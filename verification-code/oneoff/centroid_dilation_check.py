# 2026-11-09 - Claude-Code (jts-mini) subagent: numerical check of the proof of cor-centroid-dilation
# (formerly conj-centroid-dilation) of Part III; see working-notes/centroid-dilation-corollary-2026-11-09.org.
# Purpose: check every inequality and every polynomiality claim the proof uses, exactly (fractions).
"""centroid_dilation_check.py

Notation: F_r = FF(n;0^r), the r-fold sumset of S_n (S_n listed by Kruskal-Katona);
L_r = r*Koz(n) cap Z^{n+1}, listed as integer LYM chains x_0 = r, x_1 = n r,
r >= x_2/C(n,2) >= ... >= x_n/C(n,n) >= 0 (prop-rank-one-H).  Both routes are independent of
the transfer matrices and of the chained decomposition.

Part A, for each n, r:
  A1  F_r is a subset of L_r;
  A2  |c(F_r)_k - c(L_r)_k| / r          <=  C(n,k) (1 - fill)          (the mixing lemma), all k;
  A3  |E_F[x_k x_l] - E_L[x_k x_l]| / r^2 <=  C(n,k) C(n,l) (1 - fill),  all k, l;
  A4  |Cov_F - Cov_L|_{kl} / r^2          <=  (3/2) C(n,k) C(n,l) (1 - fill)  (the note's sharper
      constant; the manuscript uses 3);
  A5  the actual distance of c(F_r)/r to c(Koz(n)) in LYM coordinates, against the bound
      (1 - fill) + (distance of c(L_r)/r);
  A6  r (1 - fill) against kappa_4 = 1/2, kappa_5 = 41/25.
Part B, the Ehrhart step, for n = 2..5 and t = 0..n+3:
  B1  L(t) = #L_t, S_k(t) = sum_{L_t} x_k and S_kl(t) = sum_{L_t} x_k x_l are polynomials of degree
      n-1, n, n+1 (fitted on the first values, checked on the rest);
  B2  leading coefficients vol, vol*c(Koz(n))_k, vol*E_Koz[x_k x_l], with vol = prod_{k>=2} C(n,k)/(n-1)!
      and the moments of the simplex from prop-second-moments(1);
  B3  the 1/t coefficients beta_k of nu_k(c(L_t)) - mu_k(c(Koz(n))), against obs-dilates.
Part C, n = 3, 4, 5: from the polynomials of Part B (which, by the degree bounds proved in the note,
  are exact for every t once fitted), |nu_k(c(L_t)) - mu_k| <= |beta_k|/t for every t >= 1, shown by
  non-negativity of all coefficients of two polynomials in s = t - 1; with 1 - fill < kappa_n / r this
  gives an explicit constant valid for every r at n = 4, 5.

Usage:  ulimit -v 8000000; timeout 1800 python3 centroid_dilation_check.py
Output: runs/2026-11-09_centroid-dilation-check.txt
"""
import sys
import time
from fractions import Fraction as Q
from math import comb, factorial

T0 = time.time()
RMAX = {3: 8, 4: 10, 5: 9, 6: 2}


# ------------------------------------------------------------------ S_n by Kruskal-Katona
def shadow(m, k):
    """minimal number of (k-1)-sets in the shadow of m k-sets"""
    if m == 0 or k == 0:
        return 0
    res, kk = 0, k
    while m > 0 and kk > 0:
        a = kk
        while comb(a + 1, kk) <= m:
            a += 1
        m -= comb(a, kk)
        res += comb(a, kk - 1)
        kk -= 1
    return res


def fvecs(n):
    out = []

    def rec(v, k):
        if k > n:
            out.append(tuple(v))
            return
        for x in range(comb(n, k) + 1):
            if shadow(x, k) <= v[k - 1]:
                rec(v + [x], k + 1)
            else:
                break

    rec([1, n], 2)
    return out


# ------------------------------------------------------------------ lattice points of t Koz(n)
def lattice_points(n, t):
    c = [comb(n, k) for k in range(n + 1)]
    out = []

    def rec(v, k):
        if k > n:
            out.append(tuple(v))
            return
        # mu_k <= mu_{k-1}:  x_k <= x_{k-1} c_k / c_{k-1}
        top = (v[k - 1] * c[k]) // c[k - 1]
        for x in range(top + 1):
            rec(v + [x], k + 1)

    if n == 1:
        return [(t, t)]
    rec([t, n * t], 2)
    return out


def sums(points, n):
    """count, first sums, second sums (all coordinates 0..n), as integers"""
    S1 = [0] * (n + 1)
    S2 = [[0] * (n + 1) for _ in range(n + 1)]
    for x in points:
        for k in range(n + 1):
            xk = x[k]
            if xk:
                S1[k] += xk
                row = S2[k]
                for l in range(k, n + 1):
                    row[l] += xk * x[l]
    for k in range(n + 1):
        for l in range(k):
            S2[k][l] = S2[l][k]
    return len(points), S1, S2


def fit_poly(xs, ys):
    m = len(xs)
    A = [[Q(x) ** j for j in range(m)] + [Q(y)] for x, y in zip(xs, ys)]
    for i in range(m):
        p = next(r for r in range(i, m) if A[r][i] != 0)
        A[i], A[p] = A[p], A[i]
        for r in range(m):
            if r != i and A[r][i] != 0:
                f = A[r][i] / A[i][i]
                A[r] = [a - f * b for a, b in zip(A[r], A[i])]
    return [A[i][m] / A[i][i] for i in range(m)]


def peval(cf, x):
    return sum(ci * Q(x) ** i for i, ci in enumerate(cf))


def pstr(cf, var="t"):
    terms = []
    for i in range(len(cf) - 1, -1, -1):
        if cf[i] != 0:
            terms.append("(%s)%s" % (cf[i], "" if i == 0 else var + ("^%d" % i if i > 1 else "")))
    return " + ".join(terms) if terms else "0"


def fd(x, p=5):
    return ("%." + str(p) + "f") % float(x)


def koz_moments(n):
    """centroid and second-moment matrix of the uniform measure on Koz(n), coordinates x_0..x_n,
    by prop-second-moments(1): E[x_i x_j] = (sum_a v_ai v_aj + s_i s_j)/((D+1)(D+2)), D = n-1."""
    V = [[comb(n, k) if k <= j else 0 for k in range(n + 1)] for j in range(1, n + 1)]
    m = len(V)
    s = [sum(v[i] for v in V) for i in range(n + 1)]
    cen = [Q(si, m) for si in s]
    E2 = [[Q(sum(v[i] * v[j] for v in V) + s[i] * s[j], m * (m + 1)) for j in range(n + 1)]
          for i in range(n + 1)]
    return cen, E2


ALL_OK = True


def check(cond, msg):
    global ALL_OK
    if not cond:
        ALL_OK = False
        print("   FAIL:", msg)


# ------------------------------------------------------------------ Part A
def part_A(n, R):
    print("=" * 100)
    print("Part A, n = %d, r = 1..%d" % (n, R))
    c = [comb(n, k) for k in range(n + 1)]
    S = fvecs(n)
    print("  |S_n| = %d" % len(S))
    mu_koz = [Q(n - k + 1, n) for k in range(n + 1)]   # LYM coordinates of c(Koz(n)) (k >= 1)
    cur = {tuple([0] * (n + 1))}
    print("  %3s %8s %8s %10s %9s | %9s %9s %9s %9s | %9s %9s %9s"
          % ("r", "|F_r|", "|L_r|", "1-fill", "r(1-fill)", "A2 ratio", "A3 ratio", "A4 ratio",
             "covL/r2tr", "FF err", "lat err", "bound"))
    for r in range(1, R + 1):
        cur = {tuple(a + b for a, b in zip(x, y)) for x in cur for y in S}
        Lr = lattice_points(n, r)
        Lset = set(Lr)
        check(cur <= Lset, "A1 F_r not inside L_r at n=%d r=%d" % (n, r))
        aF, S1F, S2F = sums(cur, n)
        aL, S1L, S2L = sums(Lr, n)
        fill = Q(aF, aL)
        one_m = 1 - fill
        cF = [Q(s, aF) for s in S1F]
        cL = [Q(s, aL) for s in S1L]
        EF = [[Q(S2F[k][l], aF) for l in range(n + 1)] for k in range(n + 1)]
        EL = [[Q(S2L[k][l], aL) for l in range(n + 1)] for k in range(n + 1)]
        covF = [[EF[k][l] - cF[k] * cF[l] for l in range(n + 1)] for k in range(n + 1)]
        covL = [[EL[k][l] - cL[k] * cL[l] for l in range(n + 1)] for k in range(n + 1)]
        # A2..A4: worst ratio lhs/rhs (must be <= 1); rhs = 0 only if fill = 1, then lhs must be 0
        worst2 = worst3 = worst4 = Q(0)
        for k in range(n + 1):
            lhs = abs(cF[k] - cL[k]) / r
            rhs = c[k] * one_m
            check(lhs <= rhs, "A2 n=%d r=%d k=%d" % (n, r, k))
            if rhs:
                worst2 = max(worst2, lhs / rhs)
            for l in range(n + 1):
                lhs3 = abs(EF[k][l] - EL[k][l]) / r ** 2
                rhs3 = c[k] * c[l] * one_m
                check(lhs3 <= rhs3, "A3 n=%d r=%d k=%d l=%d" % (n, r, k, l))
                lhs4 = abs(covF[k][l] - covL[k][l]) / r ** 2
                rhs4 = Q(3, 2) * c[k] * c[l] * one_m
                check(lhs4 <= rhs4, "A4 n=%d r=%d k=%d l=%d" % (n, r, k, l))
                if rhs3:
                    worst3 = max(worst3, lhs3 / rhs3)
                    worst4 = max(worst4, lhs4 / rhs4)
        # A5: LYM distances to c(Koz(n)), k = 2..n
        ff_err = max((abs(cF[k] / (r * c[k]) - mu_koz[k]) for k in range(2, n + 1)), default=Q(0))
        lat_err = max((abs(cL[k] / (r * c[k]) - mu_koz[k]) for k in range(2, n + 1)), default=Q(0))
        for k in range(2, n + 1):
            e_ff = abs(cF[k] / (r * c[k]) - mu_koz[k])
            e_l = abs(cL[k] / (r * c[k]) - mu_koz[k])
            check(e_ff <= one_m + e_l, "A5 n=%d r=%d k=%d" % (n, r, k))
        trcov = sum(covL[k][k] / (r * r * c[k] * c[k]) for k in range(2, n + 1))
        print("  %3d %8d %8d %10s %9s | %9s %9s %9s %9s | %9s %9s %9s"
              % (r, aF, aL, fd(one_m), fd(r * one_m, 4), fd(worst2, 4), fd(worst3, 4), fd(worst4, 4),
                 fd(trcov, 4), fd(ff_err), fd(lat_err), fd(one_m + lat_err)))
        if n == 4:
            exact = Q(2 * r, (r + 1) * (4 * r + 1))
            check(one_m == exact, "A6 n=4 closed form r=%d" % r)
            check(one_m < Q(1, 2 * r), "A6 n=4 bound r=%d" % r)
        if n == 5:
            exact = Q(r * (205 * r + 71), 125 * r ** 3 + 250 * r ** 2 + 105 * r + 6)
            check(one_m == exact, "A6 n=5 closed form r=%d" % r)
            check(one_m < Q(41, 25 * r), "A6 n=5 bound r=%d" % r)
        if r == R:
            print("  at r = %d, LYM coordinates nu_k, k = 2..n:" % r)
            print("    FF      :", " ".join(fd(cF[k] / (r * c[k]), 4) for k in range(2, n + 1)))
            print("    lattice :", " ".join(fd(cL[k] / (r * c[k]), 4) for k in range(2, n + 1)))
            print("    Koz(n)  :", " ".join(fd(mu_koz[k], 4) for k in range(2, n + 1)))
        sys.stdout.flush()
    print("  columns: A2/A3/A4 ratio = worst lhs/rhs over all k (,l) (<= 1 required); covL/r2tr = trace of")
    print("  the nu-covariance of L_r; FF err, lat err = max_k |nu_k - mu_k(c(Koz(n)))|; bound = (1-fill) + lat err.")
    print("  [%.1f s]" % (time.time() - T0))


# ------------------------------------------------------------------ Part B
OBS_DILATES = {3: [Q(-1, 9), Q(-2, 9)],
               4: [Q(-5, 48), Q(-1, 4), Q(-5, 16)],
               5: [Q(-1, 10), Q(-1, 5), Q(-3, 10), Q(-7, 20)]}


def part_B(n):
    print("=" * 100)
    T = n + 3
    print("Part B, n = %d: Ehrhart-type sums over L_t, t = 0..%d" % (n, T))
    c = [comb(n, k) for k in range(n + 1)]
    vol = Q(1, factorial(n - 1))
    for k in range(2, n + 1):
        vol *= c[k]
    cen, E2 = koz_moments(n)
    data = []
    for t in range(T + 1):
        data.append(sums(lattice_points(n, t), n))
    ts = list(range(T + 1))
    Ls = [d[0] for d in data]
    # L: degree n-1
    pL = fit_poly(ts[:n], Ls[:n])
    check(all(peval(pL, t) == Ls[t] for t in ts), "B1 L(t) n=%d" % n)
    check(pL[n - 1] == vol, "B2 lead L n=%d" % n)
    print("  L(t): degree %d, fitted on t=0..%d, checked to t=%d; leading coeff %s = vol %s"
          % (n - 1, n - 1, T, pL[n - 1], vol))
    print("    L(t) = " + pstr(pL))
    betas = []
    polys = {}
    for k in range(2, n + 1):
        Sk = [d[1][k] for d in data]
        pS = fit_poly(ts[:n + 1], Sk[:n + 1])
        check(all(peval(pS, t) == Sk[t] for t in ts), "B1 S_%d n=%d" % (k, n))
        check(pS[n] == vol * cen[k], "B2 lead S_%d n=%d" % (k, n))
        # nu_k(c(L_t)) - mu_k = (S_k(t) - cen_k t L(t)) / (C(n,k) t L(t));  numerator has degree <= n-1
        num_lead = pS[n - 1] - cen[k] * (pL[n - 2] if n >= 2 else 0)
        beta = num_lead / (vol * c[k])
        betas.append(beta)
        polys[k] = pS
        print("  S_%d(t): degree %d, leading coeff %s = vol*c_k; beta_%d = %s" % (k, n, pS[n], k, beta))
        print("    S_%d(t) = %s" % (k, pstr(pS)))
    if n in OBS_DILATES:
        check(betas == OBS_DILATES[n], "B3 obs-dilates n=%d" % n)
        print("  beta against obs-dilates:", "agree" if betas == OBS_DILATES[n] else "DISAGREE",
              [str(b) for b in betas])
    # second moments: degree n+1, fitted on t=0..n+1, checked on t=n+2..T
    bad = 0
    for k in range(2, n + 1):
        for l in range(k, n + 1):
            Skl = [d[2][k][l] for d in data]
            pS2 = fit_poly(ts[:n + 2], Skl[:n + 2])
            ok = all(peval(pS2, t) == Skl[t] for t in ts) and pS2[n + 1] == vol * E2[k][l]
            check(ok, "B1/B2 S_%d%d n=%d" % (k, l, n))
            bad += (not ok)
    print("  S_kl(t), 2<=k<=l<=n: degree n+1 = %d, fitted on t=0..%d, checked to t=%d, leading coeff"
          " vol*E_Koz[x_k x_l]: %s" % (n + 1, n + 1, T, "all agree" if bad == 0 else "%d FAIL" % bad))
    print("  [%.1f s]" % (time.time() - T0))
    return pL, polys, dict(zip(range(2, n + 1), betas)), cen


# ------------------------------------------------------------------ Part C
def shift_poly(cf):
    """coefficients of p(s + 1) from those of p(t)"""
    out = [Q(0)] * len(cf)
    for i, ci in enumerate(cf):
        for j in range(i + 1):
            out[j] += ci * comb(i, j)
    return out


def nonneg_on_t_ge_1(cf):
    """sufficient test: every coefficient of p(s+1) in s is >= 0"""
    return all(x >= 0 for x in shift_poly(cf))


def part_C(n, pL, polys, betas, cen):
    """All-t bound |nu_k(c(L_t)) - mu_k| <= |beta_k|/t, t >= 1, by coefficients.  With
    R_k(t) = S_k(t) - c_k t L(t):  nu_k(c(L_t)) - mu_k = R_k(t)/(C(n,k) t L(t)).  We show
    -R_k >= 0 and |beta_k| C(n,k) L + R_k >= 0 on t >= 1 (all coefficients in s = t-1 non-negative)."""
    print("=" * 100)
    print("Part C, n = %d: explicit bound for the lattice centroid, every t >= 1" % n)
    c = [comb(n, k) for k in range(n + 1)]
    for k in range(2, n + 1):
        pS = polys[k]
        tL = [Q(0)] + list(pL)                      # t L(t)
        R = [pS[i] - cen[k] * (tL[i] if i < len(tL) else 0) for i in range(len(pS))]
        check(R[-1] == 0, "C R_k degree n=%d k=%d" % (n, k))
        negR = [-x for x in R]
        P = [abs(betas[k]) * c[k] * (pL[i] if i < len(pL) else 0) + R[i] for i in range(len(R))]
        ok1, ok2 = nonneg_on_t_ge_1(negR), nonneg_on_t_ge_1(P)
        check(ok1 and ok2, "C n=%d k=%d" % (n, k))
        # numerical spot check of the conclusion
        for t in range(1, 40):
            lhs = abs(peval(R, t)) / (c[k] * t * peval(pL, t))
            check(lhs <= abs(betas[k]) / t, "C spot n=%d k=%d t=%d" % (n, k, t))
        print("  k=%d: R_k(t) <= 0 on t>=1: %s;  |nu_k - mu_k| <= |beta_k|/t = (%s)/t on t>=1: %s"
              % (k, ok1, abs(betas[k]), ok2))
    kap = {4: Q(1, 2), 5: Q(41, 25)}.get(n)
    if kap is not None:
        tot = kap + max(abs(b) for b in betas.values())
        print("  hence, with 1 - fill(%d;0^r) < %s/r:  |nu_k(c(FF(%d;0^r))) - mu_k| < %s/r = %s/r for every r >= 1, k"
              % (n, kap, n, tot, fd(tot, 4)))


if __name__ == "__main__":
    print("centroid_dilation_check.py, run", time.strftime("%Y-%m-%d %H:%M"))
    for n in (2, 3, 4, 5):
        res = part_B(n)
        if n >= 3:
            part_C(n, *res)
    for n in (3, 4, 5, 6):
        part_A(n, RMAX[n])
    print("=" * 100)
    print("ALL CHECKS PASSED" if ALL_OK else "SOME CHECK FAILED")
    print("total %.1f s" % (time.time() - T0))
