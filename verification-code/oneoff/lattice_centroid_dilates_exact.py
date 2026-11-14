# 2026-11-09 - Claude-Code (jts-mini): for prop-dilates (Part III; was obs-dilates), at Jan's request
#   ("Yes, compute that", round-2 report item 21.1). Exact lattice-point centroid of tKoz(n), n = 3, 4, 5,
#   as a rational function of t: L(t) and S_k(t) = sum of x_k over the lattice points, interpolated at
#   t = 1..n+1 (degrees n-1 and n, by the proof of cor-centroid-dilation), checked at t = n+2 and n+3.
#   Prints R_k = S_k - c_k t L, the exact nu_k(c(Lambda_t)) - (n-k+1)/n = R_k / (C(n,k) t L), and its
#   expansion in 1/t to order 2. Same enumeration as centroid_dilation_Rk_polys.py.
#   Run: timeout 600 sage code/oneoff/lattice_centroid_dilates_exact.py
from sage.all import QQ, PolynomialRing, binomial, factor, LaurentSeriesRing
R = PolynomialRing(QQ, 't'); t = R.gen()
S = LaurentSeriesRing(QQ, 'u'); u = S.gen()          # u = 1/t

def points(n, T):
    """integer (x_2..x_n) with T >= x_2/C(n,2) >= ... >= x_n/C(n,n) >= 0"""
    C = [binomial(n, k) for k in range(n + 1)]
    out = []
    def rec(k, bound, acc):
        if k > n:
            out.append(tuple(acc)); return
        top = (bound * C[k]).floor()
        for x in range(0, top + 1):
            rec(k + 1, QQ(x) / C[k], acc + [x])
    rec(2, QQ(T), [])
    return out

def to_u(p):          # p(t) as a series in u = 1/t, times t^deg
    d = p.degree()
    return sum(p[i] * u**(d - i) for i in range(d + 1)), d

for n in (3, 4, 5):
    C = [binomial(n, k) for k in range(n + 1)]
    data = {T: points(n, T) for T in range(1, n + 4)}
    Lp = R.lagrange_polynomial([(T, len(data[T])) for T in range(1, n + 2)])
    assert Lp.degree() == n - 1
    for T in (n + 2, n + 3):
        assert Lp(T) == len(data[T])
    print(f"n = {n}:  L(t) = {factor(Lp)}   (L(1) = {Lp(1)})")
    for k in range(2, n + 1):
        Sk = R.lagrange_polynomial([(T, sum(p[k - 2] for p in data[T])) for T in range(1, n + 2)])
        for T in (n + 2, n + 3):
            assert Sk(T) == sum(p[k - 2] for p in data[T])
        assert Sk.degree() == n
        ck = C[k] * QQ(n - k + 1) / n
        Rk = Sk - ck * t * Lp
        assert Rk.degree() <= n - 1
        num, dn = to_u(Rk); den, dd = to_u(C[k] * t * Lp)
        ser = (num / den) * u**(dd - dn)                  # nu_k - (n-k+1)/n in powers of 1/t
        ser = ser.add_bigoh(3)
        neg = all(c >= 0 for c in (-Rk)(t + 1).list())   # R_k < 0 for t >= 1 (coefficients in t-1)
        print(f"  k={k}: R_k(t) = {factor(Rk)};  nu_k - {QQ(n-k+1)/n} = {ser}  (u = 1/t);  R_k<0 for t>=1: {neg}")
