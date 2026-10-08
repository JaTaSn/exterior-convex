#!/usr/bin/python3
"""appendix_tables_bruteforce.py -- brute-force every feasible cell of the two
count tables of article 2, Appendix A (tab-app-imp: |FF(n;d)|, tab-app-pro:
|FF_pr(n;d)|, constant gap d = (0, delta, ..., (r-1)delta)).

Changelog:
  2026-10-08  Claude: created (review of article 2 draft 7 found only 36 of
              the 120 r >= 2 cells per table brute-forced).  Same day:
              two-word packing for cells above 64 bits, worker pool, and
              skip-after-first-abort replaces the rate-extrapolated limit.

For each cell three numbers are compared:
  (a) the number PRINTED in the manuscript (parsed from the exported .tex),
  (b) the formula, linusson_ff_counting.ff_count (transfer matrix),
  (c) an independent brute force, described below.
A cell PASSes iff (a) == (b) == (c).

Brute-force method (iterative sumset; no Linusson recursion, no transfer
matrix, no chaining condition, no Kruskal-Katona):
  * F_n = set of f-vectors of ALL downward-closed families on [n], obtained by
    enumerating the families themselves (linusson_ff_counting.brute_fvectors,
    the same enumeration ff_count_bruteforce uses).  Proper variant: S_n =
    those with f_0 = 1 and f_1 = n.
  * Each f-vector shifted by i*delta is packed into uint64 words (one word
    if it fits in 64 bits, else two), one bit field per coordinate of the
    ambient vector, wide enough for the largest possible coordinate sum
    sum_i binom(n, j - i*delta), so word-wise integer addition IS vector
    addition (no carries between fields).
  * Sigma_1 = {sh_0(f)}, Sigma_k = {x + sh_{(k-1)delta}(f) : x in Sigma_{k-1},
    f in F_n} as a SET (numpy unique / lexsort), so the work is |Sigma_{k-1}|*|F_n|
    instead of |F_n|^k.  The answer is |Sigma_r|.
  * Memory partition (exact, not heuristic): coordinate 0 is packed in the
    HIGHEST bits, so sorted Sigma_{k-1} is grouped by its coordinates
    j < (k-1)delta, which the k-th summand does not touch; sums from distinct
    groups are therefore distinct, and the per-group distinct counts add up.

Budgets: cells are run cheapest first (predicted work = sum_k |Sigma_{k-1}| *
|F_n|, predicted from the printed table -- used ONLY for scheduling); a cell
is skipped if its predicted work exceeds PER_CELL_WORK, or aborted if it runs
past PER_CELL_SECONDS; the run stops starting new cells after TOTAL_SECONDS.
Once one cell has been aborted, every cell of larger predicted work is
skipped.  Groups are processed in parallel (multiprocessing, WORKERS).

Run:  nice -n 19 /usr/bin/python3 code/oneoff/appendix_tables_bruteforce.py
"""
import os
import re
import sys
import time
import multiprocessing as mp

import numpy as np

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, os.pardir))
import linusson_ff_counting as L  # noqa: E402

TEX = os.path.join(HERE, os.pardir, os.pardir, "article",
                   "exterior-convex_article2_latest.tex")

PER_CELL_SECONDS = 300
TOTAL_SECONDS = 45 * 60
PER_CELL_WORK = 1e11          # candidate sums; the 300 s abort is the real cap
CHUNK = 2 * 10**7             # candidate sums materialised at once, per worker
WORKERS = 8
RATE = None                   # work of the first aborted cell, if any


class Abort(Exception):
    pass


def parse_tables(path):
    """Return {'imp': {(n,delta,r): v}, 'pro': {...}} from the .tex."""
    tex = open(path).read()
    out = {}
    for key in ("imp", "pro"):
        lab = tex.index(r"\label{tab-app-%s}" % key)
        beg = tex.rindex(r"\begin{tabular}", 0, lab)
        end = tex.index(r"\end{tabular}", beg)
        body = tex[beg:end].split(r"\midrule", 1)[1]
        cells = {}
        n = None
        for line in body.split("\n"):
            line = line.strip()
            if not line.endswith(r"\\"):
                continue
            fields = [f.strip() for f in line[:-2].split("&")]
            fields = [re.sub(r"\\\(|\\\)|\\,|\s", "", f) for f in fields]
            if fields[0]:
                n = int(fields[0])
            delta = int(fields[1])
            for r, v in enumerate(fields[2:], start=1):
                cells[(n, delta, r)] = int(v)
        out[key] = cells
    return out


def layout(n, r, delta):
    """Bit fields for the ambient vector (coordinates 0..N).  Coordinates are
    split greedily into consecutive blocks of <= 64 bits, one uint64 word per
    block; inside a word the lower coordinate sits in the higher bits, so the
    lexicographic order of (word_0, word_1, ...) is the lexicographic order of
    the vectors.  Returns (word, offset, width) per coordinate."""
    from math import comb
    N = n + (r - 1) * delta
    width = []
    for j in range(N + 1):
        m = sum(comb(n, j - i * delta) for i in range(r)
                if 0 <= j - i * delta <= n)
        width.append(max(1, m.bit_length()))
    blocks, cur, used = [], [], 0
    for j in range(N + 1):
        if used + width[j] > 64:
            blocks.append(cur)
            cur, used = [], 0
        cur.append(j)
        used += width[j]
    blocks.append(cur)
    lay = [None] * (N + 1)
    for w, blk in enumerate(blocks):
        acc = 0
        for j in reversed(blk):
            lay[j] = (w, acc, width[j])
            acc += width[j]
    return lay, len(blocks)


def wunique(words):
    """Distinct rows of a multi-word array (tuple of uint64 arrays), sorted."""
    if len(words) == 1:
        return (np.unique(words[0]),)
    order = np.lexsort(words[::-1])
    ws = [w[order] for w in words]
    keep = np.ones(len(ws[0]), dtype=bool)
    if len(keep) > 1:
        d = np.zeros(len(ws[0]) - 1, dtype=bool)
        for w in ws:
            d |= w[1:] != w[:-1]
        keep[1:] = d
    return tuple(w[keep] for w in ws)


# globals inherited by forked workers
_S = None
_P = None


def _work(args):
    a, b, per, last = args
    if b - a <= per:
        U = wunique(tuple((s[a:b, None] + p[None, :]).ravel()
                          for s, p in zip(_S, _P)))
    else:   # one oversize group: sub-chunk, then merge
        subs = [wunique(tuple((s[c:min(c + per, b), None] + p[None, :]).ravel()
                              for s, p in zip(_S, _P)))
                for c in range(a, b, per)]
        U = wunique(tuple(np.concatenate([u[k] for u in subs])
                          for k in range(len(_S))))
    return len(U[0]) if last else U


def bruteforce(n, r, delta, proper, t0, workers):
    global _S, _P
    fv = L.brute_fvectors(n)
    if proper:
        fv = [f for f in fv if f[0] == 1 and f[1] == n]
    lay, W = layout(n, r, delta)

    def packed(i):
        rows = set()
        for f in fv:
            w = [0] * W
            for k in range(n + 1):
                wi, o, _ = lay[i * delta + k]
                w[wi] += f[k] << o
            rows.add(tuple(w))
        rows = sorted(rows)
        return tuple(np.array([x[k] for x in rows], dtype=np.uint64)
                     for k in range(W))

    S = wunique(packed(0))
    for i in range(1, r):
        P = packed(i)
        last = (i == r - 1)
        # group key: the coordinates j < i*delta, which summand i leaves alone
        L_ = len(S[0])
        change = np.zeros(max(L_ - 1, 0), dtype=bool)
        for wi in range(W):
            low = sum(wd for (ww, o, wd) in lay[i * delta:] if ww == wi)
            if low >= 64:
                continue
            key = S[wi] >> np.uint64(low)
            change |= key[1:] != key[:-1]
        bnd = np.flatnonzero(change) + 1
        starts = np.concatenate(([0], bnd)).tolist()
        ends = np.concatenate((bnd, [L_])).tolist()
        per = max(1, CHUNK // len(P[0]))
        tasks = []
        g, G = 0, len(starts)
        while g < G:
            b = ends[g]
            g2 = g + 1
            while g2 < G and ends[g2] - starts[g] <= per:
                b = ends[g2]
                g2 += 1
            tasks.append((starts[g], b, per, last))
            g = g2
        _S, _P = S, P
        total = 0
        pieces = []
        with mp.get_context("fork").Pool(workers) as pool:
            for res in pool.imap(_work, tasks):
                if last:
                    total += res
                else:
                    pieces.append(res)
                if time.time() - t0 > PER_CELL_SECONDS:
                    pool.terminate()
                    raise Abort("exceeded %d s" % PER_CELL_SECONDS)
        _S = _P = None
        if last:
            return total
        S = tuple(np.concatenate([u[k] for u in pieces]) for k in range(W))
        del pieces
    return len(S[0])


def main():
    global RATE
    T0 = time.time()
    tables = parse_tables(TEX)
    nfam = {n: len(L.brute_fvectors(n)) for n in range(2, 7)}
    nprop = {n: sum(1 for f in L.brute_fvectors(n) if f[0] == 1 and f[1] == n)
             for n in range(2, 7)}
    jobs = []
    for key, proper in (("imp", False), ("pro", True)):
        for (n, delta, r), printed in tables[key].items():
            size = nprop[n] if proper else nfam[n]
            work = sum(tables[key][(n, delta, k)] for k in range(1, r)) * size
            jobs.append((work, key, proper, n, delta, r, printed))
    jobs.sort()
    print("parsed %d + %d cells from %s"
          % (len(tables["imp"]), len(tables["pro"]), os.path.relpath(TEX)))
    print("|F_n| =", nfam, " |S_n| =", nprop)
    res = {}
    fails = 0
    for work, key, proper, n, delta, r, printed in jobs:
        tag = "%s n=%d delta=%d r=%d" % (key, n, delta, r)
        formula = L.ff_count(n, [i * delta for i in range(r)], proper)
        if time.time() - T0 > TOTAL_SECONDS:
            res[(key, n, delta, r)] = "skip-total"
            print("SKIP %-26s total budget exhausted (work %.2e)" % (tag, work))
            continue
        limit = PER_CELL_WORK if RATE is None else RATE
        if work >= limit:
            res[(key, n, delta, r)] = "skip-work"
            print("SKIP %-26s predicted work %.2e > %.2e" % (tag, work, limit))
            continue
        t0 = time.time()
        try:
            bf = bruteforce(n, r, delta, proper, t0, WORKERS)
        except Abort as e:
            res[(key, n, delta, r)] = "skip-abort"
            RATE = work   # skip every cell at least this expensive
            print("SKIP %-26s %s (predicted work %.2e)" % (tag, e, work))
            continue
        dt = time.time() - t0
        ok = (bf == formula == printed)
        fails += not ok
        res[(key, n, delta, r)] = "pass" if ok else "FAIL"
        print("%s %-26s printed %d formula %d brute %d  (%.1fs)"
              % ("PASS" if ok else "FAIL", tag, printed, formula, bf, dt))
        sys.stdout.flush()
    print()
    print("Coverage summary")
    for key in ("imp", "pro"):
        done = sorted(k for k, v in res.items() if k[0] == key and v == "pass"
                      or k[0] == key and v == "FAIL")
        ge2 = [k for k in done if k[3] >= 2]
        tot2 = sum(1 for k in tables[key] if k[2] >= 2)
        print("  %s: brute-forced %d of %d cells (r>=2: %d of %d)"
              % (key, len(done), len(tables[key]), len(ge2), tot2))
        for n in range(2, 7):
            for r in range(1, 6):
                ds = [d for (kk, nn, d, rr) in done if nn == n and rr == r]
                alld = sorted(d for (nn, d, rr) in tables[key]
                              if nn == n and rr == r)
                miss = [d for d in alld if d not in ds]
                print("    n=%d r=%d: delta done %s%s"
                      % (n, r, sorted(ds) or "none",
                         miss and "  NOT done %s" % miss or ""))
    print()
    print("mismatches: %d" % fails)
    print("OVERALL:", "PASS" if fails == 0 else "FAIL")
    print("elapsed %.1f s" % (time.time() - T0))


if __name__ == "__main__":
    main()
