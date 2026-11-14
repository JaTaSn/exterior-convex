# 2026-11-09 - Claude-Code (jts-mini): for cor-centroid-dilation (Part III), after the adversarial review asked
#   that the polynomials behind part (3) be printed. Exact: lattice points of tKoz(n), n = 4, 5, t = 1..n+2,
#   L(t), S_k(t) = sum of x_k, interpolated at t = 1..n+1 (Ehrhart, positive t only), checked at t = n+2.
#   Run: sage code/oneoff/centroid_dilation_Rk_polys.py
from sage.all import QQ, PolynomialRing, binomial, factor
R = PolynomialRing(QQ, 't'); t = R.gen()

def points(n, T):
    """integer (x_2..x_n) with T >= x_2/C(n,2) >= ... >= x_n/C(n,n) >= 0"""
    C = [binomial(n, k) for k in range(n + 1)]
    out = []
    def rec(k, bound, acc):          # bound = previous mu (as a fraction)
        if k > n:
            out.append(tuple(acc)); return
        top = (bound * C[k]).floor()
        for x in range(0, top + 1):
            rec(k + 1, QQ(x) / C[k], acc + [x])
    rec(2, QQ(T), [])
    return out

for n in (4, 5):
    C = [binomial(n, k) for k in range(n + 1)]
    data = {T: points(n, T) for T in range(1, n + 3)}
    Lp = R.lagrange_polynomial([(T, len(data[T])) for T in range(1, n + 2)])
    assert Lp(n + 2) == len(data[n + 2])
    print(f"n = {n}:  L(t) = {factor(Lp)}")
    vol = Lp.leading_coefficient()
    for k in range(2, n + 1):
        Sk = R.lagrange_polynomial([(T, sum(p[k - 2] for p in data[T])) for T in range(1, n + 2)])
        assert Sk(n + 2) == sum(p[k - 2] for p in data[n + 2])
        ck = C[k] * QQ(n - k + 1) / n
        Rk = Sk - ck * t * Lp
        beta = Rk[n - 1] / (C[k] * vol)
        s = R.gen()  # t
        shifted = (-Rk)(t + 1)                    # -R_k in powers of (t-1)
        shifted2 = (abs(beta) * C[k] * Lp + Rk)(t + 1)
        ok = all(c >= 0 for c in shifted.list()) and all(c >= 0 for c in shifted2.list())
        print(f"  k={k}: S_k(t) = {factor(Sk)};  R_k(t) = {factor(Rk)};  beta_k = {beta};  "
              f"|beta_k| C(n,k) L + R_k = {factor(abs(beta) * C[k] * Lp + Rk)};  "
              f"both non-negative coefficients in t-1: {ok}")
