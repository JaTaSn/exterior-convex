# 2026-11-09 - Claude-Code (jts-mini): written for working-notes/kupreyeva-limit-volume-ratio-2026-11-09.org,
#   after Jan asked whether Part III's open problem 3 (a Kupreyeva-type limit at rank r) is doable.
#   Plain Python 3, exact arithmetic, runs in well under a second.
"""Kupreyeva's observed limit q_n = (n+1)!/(2 (2n-1)!!) as a volume ratio.

Kupreyeva (2019, Section 6.2) fixes the truncation n, lets the number p of vertices grow, and
observes that the fraction of lattice points of the truncated Kozlov simplex that are f-vectors
tends to q_n.  In LYM coordinates mu_k = x_k / C(p, k) the simplex is the order simplex
    Delta = {1 >= mu_2 >= ... >= mu_n >= 0},          vol Delta = 1/(n-1)!,
and the Kruskal--Katona bound x_{k+1} <= x_k^{(k)} becomes, as p -> oo,
    mu_{k+1} <= mu_k^{(k+1)/k}                        (leading term of the Macaulay pseudo-power).
Candidate: q_n = vol R_n / vol Delta with R_n = {mu_2 <= 1, mu_{k+1} <= mu_k^{(k+1)/k}}.

Integrating out mu_n, mu_{n-1}, ..., mu_2 in turn: after mu_k is gone one holds C * mu_{k-1}^{E/(k-1)},
with E_{n-1} = n and E_{k-1} = E_k + k, so E_{k-1} = (n-k+1)(n+k)/2, and
    vol R_n = prod_{k=2}^{n-1} 2k / ((n-k+1)(n+k)) = 2^{n-2} (n+1)! / (2n-1)!,
whence (n-1)! vol R_n = (n+1)!/(2 (2n-1)!!).  This script checks the iterated integral, the closed
product and Kupreyeva's formula against each other, exactly, for 3 <= n <= NMAX.
"""
import sys
from fractions import Fraction as Fr
from math import factorial


def dfact(m):
    r = 1
    while m > 1:
        r, m = r * m, m - 2
    return r


def vol_iterated(n):
    E, C = n, Fr(1)                       # after integrating mu_n: mu_{n-1}^{n/(n-1)}
    for k in range(n - 1, 2, -1):         # integrate mu_k over [0, mu_{k-1}^{k/(k-1)}]
        C, E = C * Fr(k, E + k), E + k
    return C * Fr(2, E + 2)               # integrate mu_2 over [0, 1]


def vol_product(n):
    v = Fr(1)
    for k in range(2, n):
        v *= Fr(2 * k, (n - k + 1) * (n + k))
    return v


def main():
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 30
    bad = 0
    print(" n   vol R_n            q_n = (n-1)! vol R_n     Kupreyeva (n+1)!/(2(2n-1)!!)   equal")
    for n in range(3, nmax + 1):
        vi, vp = vol_iterated(n), vol_product(n)
        q = vi * factorial(n - 1)
        kup = Fr(factorial(n + 1), 2 * dfact(2 * n - 1))
        ok = vi == vp == Fr(2 ** (n - 2) * factorial(n + 1), factorial(2 * n - 1)) and q == kup
        bad += not ok
        print(f"{n:2d}   {str(vi):18s} {str(q):24s} {str(kup):30s} {ok}")
    print(f"mismatches: {bad}")


if __name__ == "__main__":
    main()
