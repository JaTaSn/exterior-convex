#!/usr/bin/env python3
"""interpolate_count_polynomials.py

Changelog (reverse chronological):
  2026-10-08  Claude: created (review-article2-draft7-2026-10-08, item 69).
              Re-derives, by exact rational interpolation (fractions.Fraction),
              every polynomial printed in article 2's
                * Example tab-delta0-polys (draft 7 "Ex 36"): |FF(n;0^r)| and
                  |FF_pr(n;0^r)| as polynomials in r, n = 1..7 (14 polys);
                * Example ex-poly-p-tables (draft 7 "Ex 52"): |FF^(p)(n;d)|
                  as polynomials in p, nine configurations, n = 2, 3;
              and compares every printed coefficient with the interpolant.
              The printed coefficients are transcribed by hand below from
              article/exterior-convex_article2_latest.org (2026-10-08); for the
              three abbreviated p-polynomials only the printed coefficients
              (two leading, three trailing) are compared.

              Procedure, per polynomial:
                1. values from the transfer-matrix formula: ff_count of
                   code/linusson_ff_counting.py in r; for p, the same product
                   built from A^(p)[tau][rho] = E^p(tau,rho-1) - E^p(tau-1,rho-1)
                   (Theorem thm-poly-p, eq. Ap);
                2. interpolate on deg+1 points, deg = the expected degree
                   (r: n+1 resp. n-1, Thm thm-delta0-degrees, interpolation
                   at r = 1..deg+1 as the paper states; p: the degree is not
                   assumed -- interpolate at p = n..n+deg+1 where deg is found
                   from a 40-point fit, as the paper states);
                3. verify the interpolant at EXTRA points not used in the fit:
                   r = 0 (constant term 1) and r = deg+2..deg+11 (ten points);
                   p = n+deg+2..n+deg+11 (ten points);
                4. compare coefficients with the transcription; check the
                   degree / leading-coefficient claims (eq:delta0-leading) and
                   the sign claims made in the text of tab-delta0-polys.
              Independent spot checks (brute-force sumset enumeration, no
              recursion, no transfer matrix): the r-polynomials at n <= 4,
              r <= 3 and n = 5, r = 2; the p-polynomials at every p with
              n <= p <= 5 (and p = 6 when r = 2), the truncated family
              F_n^(p) being the f-vectors of downward-closed families on [p]
              with no face of cardinality > n.

Run:  python3 code/oneoff/interpolate_count_polynomials.py
"""

import os
import sys
import time
from fractions import Fraction as Fr
from itertools import product
from math import comb, factorial, prod

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                os.pardir))
from linusson_ff_counting import (E, ff_count, restrict_proper,  # noqa: E402
                                  transfer_matrix, brute_fvectors)

# ---------------------------------------------------------------------------
# Transcriptions from the manuscript.  Lists are ascending in the variable.
# ---------------------------------------------------------------------------
F = Fr
EX36_IMPROPER = {
    1: [1, F(3, 2), F(1, 2)],
    2: [1, F(13, 6), F(3, 2), F(1, 3)],
    3: [1, F(37, 12), F(29, 8), F(23, 12), F(3, 8)],
    4: [1, F(131, 30), 8, F(47, 6), 4, F(4, 5)],
    5: [1, F(25, 4), F(1219, 72), F(79, 3), F(1915, 72), F(185, 12), F(125, 36)],
    6: [1, F(2929, 420), F(929, 24), F(269, 3), F(2869, 24), F(8863, 60),
        F(469, 4), F(225, 7)],
    7: [1, F(2117, 40), -F(267763, 1440), F(163871, 480), F(1452955, 1152),
        F(42091, 80), F(2873311, 2880), F(868819, 480), F(84035, 128)],
}
EX36_PROPER = {
    1: [1],
    2: [1, 1],
    3: [1, F(5, 2), F(3, 2)],
    4: [1, 4, 7, 4],
    5: [1, F(20, 3), F(79, 6), F(85, 3), F(125, 6)],
    6: [1, F(10, 3), F(315, 4), F(1, 6), F(595, 4), 225],
    7: [1, F(3187, 60), -F(3274, 3), F(170191, 48), -F(81977, 48),
        -F(91581, 80), F(84035, 16)],
}
# Ex 52: (n, d) -> {degree: coeff} for every PRINTED coefficient, and
# whether the printed polynomial is complete (unabbreviated).
EX52 = [
    (2, (0, 0), True, {3: 1, 2: -F(1, 2), 1: F(5, 2), 0: 3}),
    (2, (0, 1), True, {5: F(1, 12), 4: F(1, 12), 3: F(5, 12), 2: F(11, 12),
                       1: F(5, 2), 0: 4}),
    (2, (0, 0, 0), True, {3: 3, 2: -2, 1: 5, 0: 4}),
    (2, (0, 1, 2), True, {7: F(1, 24), 6: F(1, 36), 5: F(1, 3), 4: F(19, 36),
                          3: F(43, 24), 2: F(31, 9), 1: F(41, 6), 0: 8}),
    (3, (0, 0), True, {6: F(7, 90), 5: -F(3, 10), 4: F(29, 72), 3: F(3, 4),
                       2: -F(173, 360), 1: F(51, 20), 0: 3}),
    (3, (0, 1), True, {9: F(1, 1080), 8: 0, 7: -F(7, 720), 6: F(3, 80),
                       5: F(1, 48), 4: F(5, 48), 3: F(473, 1080),
                       2: F(103, 120), 1: F(51, 20), 0: 4}),
    (3, (0, 4), False, {12: F(1, 32400), 11: -F(1, 5400), 2: F(2321, 3600),
                        1: F(17, 5), 0: 4}),
    (3, (0, 1, 3), False, {14: F(1, 32400), 13: -F(1, 6480),
                           2: F(1563, 400), 1: F(527, 60), 0: 8}),
    (3, (0, 2, 3), False, {14: F(1, 32400), 13: -F(1, 4050),
                           2: F(14299, 3600), 1: F(527, 60), 0: 8}),
]


# ---------------------------------------------------------------------------
def interpolate(xs, ys):
    """Coefficients (ascending) of the unique poly of degree < len(xs)."""
    m = len(xs)
    coeffs = [Fr(0)] * m
    for i in range(m):
        # Lagrange basis polynomial l_i, built as ascending coefficient list
        basis = [Fr(1)]
        denom = Fr(1)
        for j in range(m):
            if j == i:
                continue
            basis = [Fr(0)] + basis                     # * x
            for k in range(len(basis) - 1):
                basis[k] -= xs[j] * basis[k + 1]        # - x_j * old
            denom *= (xs[i] - xs[j])
        for k in range(m):
            coeffs[k] += Fr(ys[i]) * basis[k] / denom
    while len(coeffs) > 1 and coeffs[-1] == 0:
        coeffs.pop()
    return coeffs


def ev(c, x):
    return sum(ci * Fr(x) ** k for k, ci in enumerate(c))


def fmt(c):
    return "[" + ", ".join(str(x) for x in c) + "]"


def ff_count_p(n, p, ds):
    """|FF^(p)(n;d)| by Theorem thm-poly-p's product."""
    A = [[E(p, tau, rho - 1) - (E(p, tau - 1, rho - 1) if tau >= 0 else 0)
          for rho in range(n + 2)] for tau in range(-1, n + 1)]
    R = n + 2
    v = [sum(row) for row in A]
    for i in range(1, len(ds)):
        T = transfer_matrix(A, ds[i] - ds[i - 1], n)
        v = [sum(v[a] * T[a][b] for a in range(R)) for b in range(R)]
    return sum(v)


def sumset_count(S, ds, n):
    N = n + max(ds) - min(ds)
    shifted = []
    for d in ds:
        shifted.append([tuple([0] * (d - ds[0]) + list(s)
                              + [0] * (N - n - (d - ds[0]))) for s in S])
    cur = {tuple([0] * (N + 1))}
    for L in shifted:
        cur = {tuple(a + b for a, b in zip(x, s)) for x in cur for s in L}
    return len(cur)


def truncated_family(p, n):
    """F_n^(p): f-vectors on [p] with f_j = 0 for j > n, cut to length n+1."""
    return sorted({tuple(f[:n + 1]) for f in brute_fvectors(p)
                   if all(x == 0 for x in f[n + 1:])})


# ---------------------------------------------------------------------------
def part_r():
    print("== Ex tab-delta0-polys: polynomials in r ==")
    bad = 0
    neg = {}
    for proper, table in ((False, EX36_IMPROPER), (True, EX36_PROPER)):
        for n in range(1, 8):
            deg = n - 1 if proper else n + 1
            fitr = list(range(1, deg + 2))
            c = interpolate(fitr, [ff_count(n, [0] * r, proper) for r in fitr])
            c += [Fr(0)] * (deg + 1 - len(c))
            extra = [r for r in range(deg + 2, deg + 12)]
            ext_ok = all(ev(c, r) == ff_count(n, [0] * r, proper)
                         for r in extra) and ev(c, 0) == 1
            lc = (Fr(prod(comb(n, j) for j in range(2, n + 1)), factorial(n - 1))
                  if proper else
                  Fr(prod(comb(n, j) for j in range(n + 1)), factorial(n + 1)))
            deg_ok = len(c) == deg + 1 and c[-1] == lc
            printed = [Fr(x) for x in table[n]]
            match = (c == printed)
            diffs = [(k, printed[k] if k < len(printed) else None, c[k])
                     for k in range(max(len(c), len(printed)))
                     if (printed[k] if k < len(printed) else None)
                     != (c[k] if k < len(c) else None)]
            neg[(proper, n)] = [k for k, x in enumerate(c) if x < 0]
            ok = ext_ok and deg_ok and match
            bad += not ok
            print("  %-8s n=%d deg=%d  fit r=1..%d, extra r=0,%d..%d: %s; "
                  "deg/lc(eq:delta0-leading): %s; printed coeffs: %s"
                  % ("proper" if proper else "improper", n, deg, deg + 1,
                     extra[0], extra[-1], "ok" if ext_ok else "FAIL",
                     "ok" if deg_ok else "FAIL",
                     "MATCH" if match else "MISMATCH %s" % diffs))
            print("      computed: %s" % fmt(c))
    print("  negative-coefficient exponents (k with c_k < 0):")
    for (proper, n), ks in sorted(neg.items()):
        if ks:
            print("    %s n=%d: r^%s" % ("proper" if proper else "improper", n,
                                         ks))
    sign_ok = (all(not neg[(pr, n)] for pr in (False, True) for n in range(1, 7))
               and neg[(False, 7)] == [2] and neg[(True, 7)] == [2, 4, 5])
    print("  text claims (all positive for n<=6; n=7 improper negative only at "
          "r^2; proper only at r^2,r^4,r^5): %s" % ("ok" if sign_ok else "FAIL"))
    p6 = interpolate(list(range(1, 7)), [ff_count(6, [0] * r, True)
                                         for r in range(1, 7)])
    print("  proper n=6 r^3 coefficient = %s (text: 1/6)" % p6[3])
    bad += (not sign_ok) + (p6[3] != Fr(1, 6))
    # independent brute-force spot checks
    print("  brute-force sumset spot checks (n<=4, r<=3; n=5, r=2):")
    cases = [(n, r) for n in range(1, 5) for r in range(1, 4)] + [(5, 2)]
    for proper in (False, True):
        for n, r in cases:
            S = brute_fvectors(n)
            if proper:
                S = [s for s in S if s[0] == 1 and s[1] == n]
            b = sumset_count(S, [0] * r, n)
            table = EX36_PROPER if proper else EX36_IMPROPER
            pv = ev([Fr(x) for x in table[n]], r)
            ok = (pv == b)
            bad += not ok
            print("    %-8s n=%d r=%d: printed poly %s, brute %d %s"
                  % ("proper" if proper else "improper", n, r, pv, b,
                     "ok" if ok else "FAIL"))
    return bad


def part_p():
    print("\n== Ex ex-poly-p-tables: polynomials in p ==")
    bad = 0
    polys = {}
    for n, ds, complete, printed in EX52:
        big = list(range(n, n + 40))
        cbig = interpolate(big, [ff_count_p(n, p, ds) for p in big])
        deg = len(cbig) - 1
        fitp = list(range(n, n + deg + 2))           # p = n..n+deg+1
        c = interpolate(fitp, [ff_count_p(n, p, ds) for p in fitp])
        extra = list(range(n + deg + 2, n + deg + 12))
        ext_ok = (c == cbig) and all(ev(c, p) == ff_count_p(n, p, ds)
                                     for p in extra)
        polys[(n, ds)] = c
        diffs = [(k, v, c[k] if k < len(c) else 0) for k, v in printed.items()
                 if (c[k] if k < len(c) else 0) != v]
        degmatch = (max(printed) == deg)
        if complete:
            full = [printed.get(k, 0) for k in range(max(printed) + 1)]
            match = (c == full) and not diffs
        else:
            match = not diffs and degmatch
        ok = ext_ok and match
        bad += not ok
        print("  n=%d d=%-9s deg %2d  fit p=%d..%d (40-pt fit agrees), extra "
              "p=%d..%d: %s; printed %s coeffs: %s"
              % (n, ds, deg, fitp[0], fitp[-1], extra[0], extra[-1],
                 "ok" if ext_ok else "FAIL",
                 "all" if complete else "%d shown" % len(printed),
                 "MATCH" if match else "MISMATCH %s" % diffs))
        print("      computed (ascending): %s" % fmt(c))
    # Rem rem-reversal-only-at-p-n values
    a, b = polys[(3, (0, 1, 3))], polys[(3, (0, 2, 3))]
    vals = [(p, ev(a, p), ev(b, p)) for p in (3, 4, 5)]
    print("  reversal pair (0,1,3) vs (0,2,3) at p=3,4,5: %s" % vals)
    want = [(3, 607, 607), (4, 6696, 6592), (5, 94402, 87165)]
    rv_ok = vals == [(p, Fr(x), Fr(y)) for p, x, y in want]
    print("  text values 607/607, 6696/6592, 94402/87165: %s"
          % ("ok" if rv_ok else "FAIL"))
    bad += not rv_ok
    # brute force spot checks
    print("  brute-force truncated-sumset spot checks:")
    for n, ds, _, _ in EX52:
        pmax = 6 if len(ds) == 2 else 5
        for p in range(n, pmax + 1):
            S = truncated_family(p, n)
            bf = sumset_count(S, list(ds), n)
            pv = ev(polys[(n, ds)], p)
            ok = (pv == bf)
            bad += not ok
            print("    n=%d d=%-9s p=%d: poly %s brute %d %s"
                  % (n, ds, p, pv, bf, "ok" if ok else "FAIL"))
    return bad


if __name__ == "__main__":
    t0 = time.time()
    bad = part_r()
    bad += part_p()
    print("\nruntime %.1f s" % (time.time() - t0))
    print("TOTAL failures: %d" % bad)
    print("OVERALL:", "PASS" if bad == 0 else "FAIL")
    sys.exit(0 if bad == 0 else 1)
