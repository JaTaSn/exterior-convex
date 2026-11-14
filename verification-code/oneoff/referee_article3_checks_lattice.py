# referee_article3_checks_lattice.py
#
# Changelog (reverse chronological)
#   2026-11-14  Claude-Code (jts-pc): scratch directory from tempfile, and the log is written to the
#               current directory (or $REFEREE_LOG), instead of two absolute paths of the machine
#               it was written on.  No change to what is computed.
#   2026-10-20  Created by a referee subagent (Claude) for the referee report on
#               article/exterior-convex_article3_draft_4.org.  Independent recomputation of
#               the numbers in sec-lattice, sec-volume, sec-ehrhart, sec-centroid, sec-moments.
#               Written from scratch, without reading the authors' code.  Run with the Sage
#               python:  /home/jan/miniforge3/envs/sage/bin/python referee_article3_checks_lattice.py [part]
#               Log: runs/2026-10-20_article3-overnight-push/2026-10-20_referee-article3-lattice.txt
#
# Conventions: f-vectors indexed by cardinality, f = (f_0,...,f_n), f_0 = 1.
# S_n: f-vectors of complexes on [n] using every vertex (f_1 = n), via Kruskal-Katona.
# L_n: lattice points of Koz(n) = {f_0=1, f_1=n, 1 >= f_2/C(n,2) >= ... >= f_n >= 0}.

import sys, itertools
from fractions import Fraction as Fr
from math import comb
from functools import lru_cache
from collections import Counter, defaultdict


def kk_upper(a, k):
    """a^{(k)}: max number of (k+1)-faces given a faces of cardinality k (k>=1)."""
    if a == 0:
        return 0
    res = 0
    kk = k
    while a > 0 and kk >= 1:
        m = kk
        while comb(m + 1, kk) <= a:
            m += 1
        a -= comb(m, kk)
        res += comb(m, kk + 1)
        kk -= 1
    return res


def S(n):
    """list of f-vectors in S_n (tuples of length n+1)."""
    out = []
    def rec(f):
        k = len(f) - 1
        if k == n:
            out.append(tuple(f)); return
        bound = min(comb(n, k + 1), kk_upper(f[k], k))
        for v in range(bound + 1):
            rec(f + [v])
    if n == 0:
        return [(1,)]
    rec([1, n])
    return out


def L(n, t=1):
    """lattice points of t*Koz(n)."""
    out = []
    def rec(f):
        k = len(f) - 1
        if k == n:
            out.append(tuple(f)); return
        # f_{k+1}/C(n,k+1) <= f_k/C(n,k)  (for k>=1); also f_2 <= t*C(n,2)
        if k == 1:
            ub = t * comb(n, 2)
        else:
            ub = (f[k] * comb(n, k + 1)) // comb(n, k)
        for v in range(ub + 1):
            rec(f + [v])
    if n == 1:
        return [(t, t)]
    rec([t, t * n])
    return out


def count_L(n, t=1):
    """count lattice points of t Koz(n) by DP."""
    if n == 1:
        return 1
    cur = Counter({v: 1 for v in range(t * comb(n, 2) + 1)})
    for k in range(2, n):
        nxt = Counter()
        for v, c in cur.items():
            ub = (v * comb(n, k + 1)) // comb(n, k)
            for w in range(ub + 1):
                nxt[w] += c
        cur = nxt
    return sum(cur.values())


def count_S(n):
    if n == 1:
        return 1
    cur = Counter({n: 1})
    for k in range(1, n):
        nxt = Counter()
        for v, c in cur.items():
            ub = min(comb(n, k + 1), kk_upper(v, k))
            for w in range(ub + 1):
                nxt[w] += c
        cur = nxt
    return sum(cur.values())


def shift(v, d, N):
    return tuple([0] * d + list(v) + [0] * (N + 1 - d - len(v)))


def sumset(sets_shifts, n):
    N = n + max(d for _, d in sets_shifts)
    cur = {tuple([0] * (N + 1))}
    for A, d in sets_shifts:
        As = [shift(a, d, N) for a in A]
        cur = {tuple(x + y for x, y in zip(c, a)) for c in cur for a in As}
    return cur


def sumset_mult(sets_shifts, n):
    N = n + max(d for _, d in sets_shifts)
    cur = Counter({tuple([0] * (N + 1)): 1})
    for A, d in sets_shifts:
        As = [shift(a, d, N) for a in A]
        nxt = Counter()
        for c, m in cur.items():
            for a in As:
                nxt[tuple(x + y for x, y in zip(c, a))] += m
        cur = nxt
    return cur


def waterfill(x, n, ds):
    """canonical chained decomposition (paper's formula), returns parts as tuples length n+1."""
    cap = lambda s: comb(n, s) if 0 <= s <= n else 0
    r = len(ds)
    def Q(i, k):
        if i == 0:
            return 0
        return max(0, x[k] - sum(cap(k - ds[l]) for l in range(i, r)))
    parts = []
    for i in range(1, r + 1):
        p = tuple(Q(i, m + ds[i - 1]) - Q(i - 1, m + ds[i - 1]) for m in range(n + 1))
        parts.append(p)
    return parts


def mean(vs):
    vs = list(vs)
    m = len(vs)
    return tuple(Fr(sum(v[i] for v in vs), m) for i in range(len(vs[0])))


def cov(vs, idx):
    vs = list(vs); m = len(vs)
    mu = mean(vs)
    return [[Fr(sum((v[i] - mu[i]) * (v[j] - mu[j]) for v in vs), m) for j in idx] for i in idx]


log_lines = []
def log(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    log_lines.append(s)


# ---------------------------------------------------------------- normaliz helpers
import subprocess, os, re, tempfile
SCR = tempfile.mkdtemp(prefix="referee-lat-")


def koz_vertices(n, ds, c=None):
    """all sums of vertex tuples of sum_i shift^{d_i} angle(c) (full leg vector c, c_0=1)."""
    if c is None:
        c = [comb(n, k) for k in range(n + 1)]
    N = n + max(ds)
    V = [tuple(c[:j + 1]) + (0,) * (n - j) for j in range(1, n + 1)]
    pts = set()
    for tup in itertools.product(V, repeat=len(ds)):
        x = [0] * (N + 1)
        for v, d in zip(tup, ds):
            for i, a in enumerate(v):
                x[i + d] += a
        pts.add(tuple(x))
    return sorted(pts)


def normaliz(points, tag, opts=("-E",)):
    """run normaliz on the polytope conv(points), after dropping constant coordinates.
    returns dict with keys: h (h*-vector list), nv (multiplicity), lat (lattice points, if -E: from series)"""
    pts = [list(p) for p in points]
    keep = [i for i in range(len(pts[0])) if len({p[i] for p in pts}) > 1]
    P = [[p[i] for i in keep] for p in pts]
    D = len(keep)
    fn = os.path.join(SCR, tag + ".in")
    with open(fn, "w") as f:
        f.write(f"amb_space {D+1}\npolytope {len(P)}\n")
        for p in P:
            f.write(" ".join(map(str, p)) + "\n")
        f.write("HilbertSeries\nMultiplicity\nEhrhartQuasiPolynomial\n" if "-E" in opts else "Multiplicity\n")
    subprocess.run(["normaliz", "-x=4", "-c", fn], check=True, capture_output=True)
    out = open(fn[:-3] + ".out").read()
    res = {"D": D, "raw": out}
    m = re.search(r"multiplicity\s*=\s*([0-9/]+)", out)
    if m:
        res["nv"] = Fr(m.group(1))
    m = re.search(r"Hilbert series:\n([0-9 \-]+)\n", out)
    if m:
        res["h"] = [int(x) for x in m.group(1).split()]
    m = re.search(r"Hilbert polynomial:\n([0-9 \-]+)\nwith common denominator = (\d+)", out)
    if m:
        den = int(m.group(2))
        res["L"] = [Fr(int(x), den) for x in m.group(1).split()]
    m = re.search(r"(\d+) lattice points in polytope", out)
    if m:
        res["lat"] = int(m.group(1))
    m = re.search(r"(\d+) extreme rays", out); res["verts"] = int(m.group(1)) if m else None
    m = re.search(r"(\d+) support hyperplanes", out); res["facets"] = int(m.group(1)) if m else None
    return res


def staircase_NV(c, ds):
    """formula of thm-staircase; c full leg vector (c_0..c_n)."""
    n = len(c) - 1
    r = len(ds)
    N = n + ds[-1]
    D = N - 1
    from math import factorial
    tot = 0
    def rec(ts):
        nonlocal tot
        i = len(ts)  # next index t_i to choose
        if i == r:
            if ts[-1] != N:
                return
            # check t_{i-1}-d_i >= 1, t_i - d_i <= n
            for j in range(1, r + 1):
                if ts[j - 1] - ds[j - 1] < 1 or ts[j] - ds[j - 1] > n:
                    return
            mult = factorial(D)
            for j in range(1, r + 1):
                mult //= factorial(ts[j] - ts[j - 1])
            pr = 1
            for j in range(1, r + 1):
                for k in range(ts[j - 1] + 1, ts[j] + 1):
                    pr *= c[k - ds[j - 1]]
            tot += mult * pr
            return
        lo = ts[-1]
        hi = N if i == r - 1 else N
        cand = [N] if i == r else range(lo, N + 1)
        for t in cand:
            rec(ts + [t])
    # ts = [t_0=1, t_1, ..., t_r=N]
    def rec2(ts):
        nonlocal tot
        if len(ts) == r:
            rec_final = ts + [N]
            ok = rec_final[-1] >= rec_final[-2]
            if ok:
                for j in range(1, r + 1):
                    if rec_final[j - 1] - ds[j - 1] < 1 or rec_final[j] - ds[j - 1] > n:
                        ok = False; break
            if ok:
                from math import factorial
                mult = factorial(D)
                for j in range(1, r + 1):
                    mult //= factorial(rec_final[j] - rec_final[j - 1])
                pr = 1
                for j in range(1, r + 1):
                    for k in range(rec_final[j - 1] + 1, rec_final[j] + 1):
                        pr *= c[k - ds[j - 1]]
                tot += mult * pr
            return
        for t in range(ts[-1], N + 1):
            rec2(ts + [t])
    rec2([1])
    return tot


def rank2_formula(n, d):
    from math import prod
    m = n - d
    return prod(comb(n, k) for k in range(2, n + 1)) * sum(
        comb(n - 1 + d, d + g - 1) * prod(comb(n, k) for k in range(g + 1, g + d + 1)) for g in range(1, m + 1))


def interp(vals):
    """vals[t] for t=0..deg ; return coefficient list via Lagrange (exact)."""
    from sympy import interpolate, symbols, Poly, Rational
    t = symbols('t')
    p = interpolate([(i, v) for i, v in enumerate(vals)], t)
    P = Poly(p, t)
    return [Fr(int(cf.p), int(cf.q)) for cf in reversed(P.all_coeffs())]


def hstar_from_L(Lc, D):
    """h* from Ehrhart polynomial coefficients (degree D)."""
    vals = [sum(c * t ** i for i, c in enumerate(Lc)) for t in range(D + 2)]
    # sum L(t) z^t = h*(z)/(1-z)^{D+1}  => h = coeffs of (1-z)^{D+1} * sum
    h = []
    for i in range(D + 1):
        h.append(sum((-1) ** j * comb(D + 1, j) * vals[i - j] for j in range(i + 1)))
    return h


def hstar_asc(n):
    """ascent formula of thm-hstar (direct enumeration, only small n)."""
    c = [comb(n, k) for k in range(n + 1)]
    cnt = Counter()
    for r in itertools.product(*[range(c[k]) for k in range(2, n + 1)]):
        rho = [Fr(0)] + [Fr(r[k - 2], c[k]) for k in range(2, n + 1)]  # rho_1..rho_n
        a = sum(1 for k in range(n - 1) if rho[k] < rho[k + 1])
        cnt[a] += 1
    return [cnt[i] for i in range(max(cnt) + 1)]


def hstar_asc_dp(n, e0=False):
    """ascent statistic distribution via DP over (k, rho_k) -- feasible to n=8."""
    c = [comb(n, k) for k in range(n + 1)]
    # state: rho value of previous, ascents so far (polynomial dict)
    cur = {Fr(1) if e0 else Fr(0): Counter({0: 1})}
    for k in range(2, n + 1):
        nxt = defaultdict(Counter)
        for prev, poly in cur.items():
            for rk in range(c[k]):
                rho = Fr(rk, c[k])
                inc = 1 if prev < rho else 0
                for a, m in poly.items():
                    nxt[rho][a + inc] += m
        cur = nxt
    tot = Counter()
    for poly in cur.values():
        tot.update(poly)
    return [tot[i] for i in range(max(tot) + 1)]


def tp(x, n):
    return max(k for k in range(1, n + 1) if x[k] > 0)


def indeg(x, n):
    for k in range(n + 1):
        if x[k] < comb(n, k):
            return k
    return n + 1


def transfer(A, n):
    """A: list of points (S_n or L_n). returns u (dict tau->count), T(delta) function."""
    stats = Counter((tp(x, n), indeg(x, n)) for x in A)
    taus = list(range(1, n + 1))
    u = [sum(c for (t, i), c in stats.items() if t == tau) for tau in taus]
    def T(delta):
        return [[sum(c for (t, i), c in stats.items() if t == tau2 and i + delta > tau) for tau2 in taus] for tau in taus]
    return u, T


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def chain_count(u, T, deltas):
    v = [u]
    for d in deltas:
        v = matmul(v, T(d))
    return sum(v[0])


def ehrhart_transfer(u, T, ds, t):
    deltas = []
    for i, d in enumerate(ds):
        if i > 0:
            deltas.append(d - ds[i - 1])
        deltas += [0] * (t - 1)
    return chain_count(u, T, deltas)


def chain_moments(n, kind="L"):
    """forward/backward DP over the chain of values f_2..f_n.  kind 'L': lattice points of Koz(n);
    'S': f-vectors (Kruskal-Katona).  returns (count, E[f_k] list k=0..n, E[f_k^2])."""
    def succ(k, v):  # allowed values of f_{k+1} given f_k = v
        if kind == "L":
            if k == 1:
                return range(comb(n, 2) + 1)
            return range((v * comb(n, k + 1)) // comb(n, k) + 1)
        return range(min(comb(n, k + 1), kk_upper(v, k)) + 1)
    F = [None] * (n + 1)
    F[1] = Counter({n: 1})
    for k in range(1, n):
        nxt = Counter()
        for v, c in F[k].items():
            for w in succ(k, v):
                nxt[w] += c
        F[k + 1] = nxt
    B = [None] * (n + 1)
    B[n] = Counter({v: 1 for v in F[n]})
    for k in range(n - 1, 0, -1):
        b = Counter()
        for v in F[k]:
            b[v] = sum(B[k + 1].get(w, 0) for w in succ(k, v))
        B[k] = b
    tot = sum(F[n].values())
    E1 = [Fr(1), Fr(n)] + [Fr(sum(v * F[k][v] * B[k][v] for v in F[k]), tot) for k in range(2, n + 1)]
    E2 = [Fr(1), Fr(n * n)] + [Fr(sum(v * v * F[k][v] * B[k][v] for v in F[k]), tot) for k in range(2, n + 1)]
    return tot, E1, E2


def dilate_centroid(n, t):
    """exact lattice centroid (E f_k) of t*Koz(n), by forward/backward DP."""
    def succ(k, v):
        if k == 1:
            return range(t * comb(n, 2) + 1)
        return range((v * comb(n, k + 1)) // comb(n, k) + 1)
    F = [None] * (n + 1); F[1] = Counter({t * n: 1})
    for k in range(1, n):
        nxt = Counter()
        for v, c in F[k].items():
            for w in succ(k, v):
                nxt[w] += c
        F[k + 1] = nxt
    B = [None] * (n + 1); B[n] = Counter({v: 1 for v in F[n]})
    for k in range(n - 1, 0, -1):
        B[k] = Counter({v: sum(B[k + 1].get(w, 0) for w in succ(k, v)) for v in F[k]})
    tot = sum(F[n].values())
    return [Fr(sum(v * F[k][v] * B[k][v] for v in F[k]), tot) for k in range(2, n + 1)]


# ---------------------------------------------------------------- driver (the checks run for the report)
def main():
    log("|S_n| n=1..8", [count_S(n) for n in range(1, 9)])
    log("|L_n| n=1..8", [count_L(n) for n in range(1, 9)])
    log("fill n=11", count_S(11) / count_L(11))
    for n in range(3, 9):
        log("h* Koz(%d)" % n, hstar_asc_dp(n))
    log("h* with rho_1=1 convention, n=4", hstar_asc_dp(4, True))
    for n in range(3, 8):
        Lc = interp([count_L(n, t) for t in range(n)])
        log("L_Koz(%d)" % n, [str(x) for x in Lc])
    for n, ds in [(3, [0, 1]), (3, [0, 2]), (3, [0, 0]), (4, [0, 1]), (4, [0, 0]), (4, [0, 2]),
                  (4, [0, 3]), (3, [0, 1, 2]), (4, [0, 1, 2])]:
        r = normaliz(koz_vertices(n, ds), 'k%d_%s' % (n, ''.join(map(str, ds))))
        log(n, ds, 'D', r['D'], 'V', r['verts'], 'F', r['facets'], 'lat', r['lat'], 'NV', r['nv'],
            'h*', r['h'], 'L', [str(x) for x in r['L']], 'staircase NV',
            staircase_NV([comb(n, k) for k in range(n + 1)], ds))
    for n in range(2, 8):
        log("rank2 NV formula n=%d" % n, [rank2_formula(n, d) for d in range(n)])
    for n in [3, 4, 5]:
        Sn, Ln = S(n), L(n)
        for d in range(n):
            log("FF/lat", n, d, len(sumset([(Sn, 0), (Sn, d)], n)), len(sumset([(Ln, 0), (Ln, d)], n)))
    for n in range(3, 8):
        cS, cL = mean(S(n)), mean(L(n))
        log("centroid LYM", n, "S", [round(float(cS[k] / comb(n, k)), 4) for k in range(2, n + 1)],
            "L", [round(float(cL[k] / comb(n, k)), 4) for k in range(2, n + 1)])


if __name__ == "__main__":
    main()
    with open(os.environ.get("REFEREE_LOG", "2026-10-20_referee-article3-lattice.txt"), "w") as f:
        f.write("\n".join(log_lines) + "\n")
