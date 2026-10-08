#!/usr/bin/env python3
"""arxiv_anc_tables.py -- the computed tables shipped in article 2's arXiv ancillary directory.

Changelog (newest first):
  2026-10-08  Created (Claude, jts-office) for the arXiv package of article 2.  Writes, into the
              directory given as argv[1] (default ./tables):

    ff-counts.csv        |FF(n;d)| and |FF_pr(n;d)| for 1 <= n <= 8, 1 <= r <= 4, and EVERY gap
                         vector (delta_2, ..., delta_r) with 0 <= delta_i <= n+1.  A gap above n+1
                         changes nothing (the product regime of Prop. prop-threshold), so this is
                         the complete table for that range of n and r.  d is written with
                         d_1 = 0, since only the gaps matter.
    ff-constant-gap.csv  the constant-gap counts d = (0, delta, ..., (r-1) delta) for 1 <= n <= 8,
                         1 <= r <= 8, 0 <= delta <= n+1: the families of the growth section.
    joint-distribution-A_n.csv
                         the matrix A_n[tau][rho] = #{s in F_n : top(s) = tau, indeg(s) = rho},
                         1 <= n <= 8, one row per nonzero entry.

  Every count is the transfer-matrix formula u_n . T_n(delta_2) ... T_n(delta_r) . 1_n, computed by
  linusson_ff_counting.py (A_n from Linusson's recursion).  As a self-check, before writing
  anything, every row of ff-counts.csv with n <= 4 and r <= 2, or n <= 3 and r <= 3, is recomputed by direct enumeration
  of the sumset (linusson_ff_counting.ff_count_bruteforce: no recursion, no transfer matrix), and
  the script refuses to write if any disagree.
"""
import csv, itertools, os, sys
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, os.pardir))
import linusson_ff_counting as L

NMAX, RMAX, RMAX_CONST = 8, 4, 8
_A = {}


def A(n, proper):
    if (n, proper) not in _A:
        a = L.A_from_linusson(n)
        _A[(n, proper)] = L.restrict_proper(a) if proper else a
    return _A[(n, proper)]


def count(n, gaps, proper):
    a, R = A(n, proper), n + 2
    v = [sum(row) for row in a]
    for delta in gaps:
        T = L.transfer_matrix(a, delta, n)
        v = [sum(v[i] * T[i][j] for i in range(R)) for j in range(R)]
    return sum(v)


def dvec(gaps):
    d = [0]
    for g in gaps:
        d.append(d[-1] + g)
    return " ".join(map(str, d))


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else "tables"
    os.makedirs(out, exist_ok=True)

    rows = []
    for n in range(1, NMAX + 1):
        for r in range(1, RMAX + 1):
            for gaps in itertools.product(range(n + 2), repeat=r - 1):
                rows.append((n, r, dvec(gaps), count(n, gaps, False), count(n, gaps, True)))

    bad = 0
    for n, r, d, ff, ffpr in rows:
        if (n <= 4 and r <= 2) or (n <= 3 and r <= 3):
            ds = list(map(int, d.split()))
            bad += (L.ff_count_bruteforce(n, ds, False) != ff) + (L.ff_count_bruteforce(n, ds, True) != ffpr)
    checked = sum(1 for x in rows if (x[0] <= 4 and x[1] <= 2) or (x[0] <= 3 and x[1] <= 3))
    if bad:
        sys.exit(f"brute-force check FAILED: {bad} mismatches in {checked} rows")
    print(f"brute-force check: {checked} rows (n<=4 r<=2; n<=3 r<=3), both variants, 0 mismatches")

    with open(os.path.join(out, "ff-counts.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["n", "r", "d", "FF", "FF_proper"])
        w.writerows(rows)

    with open(os.path.join(out, "ff-constant-gap.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["n", "r", "delta", "FF", "FF_proper"])
        for n in range(1, NMAX + 1):
            for delta in range(n + 2):
                for r in range(1, RMAX_CONST + 1):
                    g = (delta,) * (r - 1)
                    w.writerow([n, r, delta, count(n, g, False), count(n, g, True)])

    with open(os.path.join(out, "joint-distribution-A_n.csv"), "w", newline="") as fh:
        w = csv.writer(fh)
        w.writerow(["n", "top_tau", "indeg_rho", "A_n"])
        for n in range(1, NMAX + 1):
            for t, row in enumerate(A(n, False)):          # row index t <-> tau = t - 1
                for rho, val in enumerate(row):
                    if val:
                        w.writerow([n, t - 1, rho, val])
    print(f"wrote {len(rows)} rows to {out}/ff-counts.csv, plus ff-constant-gap.csv and "
          f"joint-distribution-A_n.csv")


if __name__ == "__main__":
    main()
