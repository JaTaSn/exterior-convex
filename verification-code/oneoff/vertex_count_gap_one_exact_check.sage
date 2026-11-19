# vertex_count_gap_one_exact_check.sage -- 2026-11-18, jts-mini (Claude-Code).
#
# Part IV, Proposition prop-gap-one: EXACT verification, written by the independent referee agent of
# 2026-11-18 from the statements (kept as that agent wrote it, apart from this header, renamed local
# cos/sin helpers, and the log path).  For 2 <= n <= NMAX (default 60):
#   * M built literally from the zero condition of Corollary cor-rank2-lc (a_i = 1/i!, and a second
#     strictly log-concave a) equals the description used in the proof;
#   * charpoly(M) vanishes at 1 + zeta + 1/zeta in Q(zeta_{n+4});
#   * M x = lambda x exactly in Q(zeta_{4(n+4)}), and both closed forms of x_j;
#   * x > 0 by 3000-bit interval arithmetic;
#   * over QQbar, lambda is the largest eigenvalue modulus (and strictly dominant; M primitive);
#   * the two-sided bound for r = 1..12.
# Last lines: geometric a (constant slope) shows strictness is needed for n >= 4.
# Run from code/:  sage oneoff/vertex_count_gap_one_exact_check.sage [NMAX] > ../runs/2026-11-18_gap-one-review/vertex_count_gap_one_exact_check.txt
import sys
def extten(a, d):
    # straight from cor-rank2-lc; 1-based indices
    n = len(a); m = n-d
    sig = {i: a[i]/a[i-1] for i in range(1, n)}   # sigma_i = a_{i+1}/a_i, i=1..n-1
    M = matrix(ZZ, n, n, 1)
    for i in range(1, n+1):
        for j in range(1, n+1):
            t = i-d
            if 1 <= t <= m and 1 <= j <= m:
                z = (j < t) or (j == t+1)
                if j >= t+2:
                    rng = range(t+1, j+d)   # [t+1, j+d-1]
                    if len(set(sig[k] for k in rng)) == 1: z = True
                M[i-1, j-1] = 0 if z else 1
            else:
                M[i-1, j-1] = 1
    return M
def proofM(n):
    return matrix(ZZ, n, n, lambda i, j: 1 if (j >= i-1 and not (j == i and 1 <= i <= n-2)) else 0)  # 0-based
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 60
for n in range(2, NMAX+1):
    a = [QQ(1)/factorial(i) for i in range(1, n+1)]     # sigma_i = 1/(i+1), strictly decreasing
    a2 = [QQ(binomial(n+3, i))/(i^2+1) for i in range(1, n+1)]
    M = extten(a, 1)
    s2 = [a2[i]/a2[i-1] for i in range(1,n)]
    if all(s2[i] > s2[i+1] for i in range(n-2)): assert extten(a2,1) == M
    assert M == proofM(n), n
    # eigenvalue exactly, in Q(zeta_{n+4})
    K.<z> = CyclotomicField(n+4)
    lam = 1 + z + z^-1
    p = M.charpoly()
    assert p(lam) == 0
    # eigenvector exactly, in Q(zeta_{4(n+4)}): w = exp(2 pi i/(4(n+4))), e^{i theta} = w^2, I = w^(n+4)
    L.<w> = CyclotomicField(4*(n+4))
    I_ = w^(n+4); e = w^2
    ccos = lambda k: (e^k + e^-k)/2
    csin = lambda k: (e^k - e^-k)/(2*I_)
    lamL = 1 + 2*ccos(2); q = 1/(2*ccos(1))
    S = {j: q^j*csin(j+2) for j in range(1, n+1)}; S[n+1] = L(0)
    x = vector(L, [S[j]-S[j+1] for j in range(1, n+1)])
    assert M.change_ring(L)*x == lamL*x
    # closed forms claimed in the proof
    for j in range(1, n): assert x[j-1] == q^(j+1)*csin(j+1)
    assert x[n-1] == q^n*csin(2)
    # positivity: rigorous, via the embedding w -> exp(2 pi i /(4(n+4))) in interval arithmetic
    C = ComplexIntervalField(3000)
    w0 = (2*C(pi)*C(0,1)/(4*(n+4))).exp()
    for xi in x:
        v = xi.polynomial()(w0)
        assert v.real() > 0 and v.imag().contains_zero(), (n, v)
    lam0 = lamL.polynomial()(w0).real()
    # independent: all eigenvalues in QQbar, exact comparison of moduli
    ev = p.roots(QQbar, multiplicities=False) if True else None
    if ev is not None:
        lamQ = 1 + 2*cos_exact if False else max([r for r in ev if r.imag() == 0], key=lambda r: r.real())
        zq = QQbar.zeta(n+4); assert lamQ == 1 + zq + 1/zq
        assert all(abs(r) <= lamQ for r in ev)
        strict = all(abs(r) < lamQ for r in ev if r != lamQ)
    else:
        # rigorous interval enclosure of all roots
        rts = p.roots(ComplexIntervalField(300), multiplicities=False)
        assert p.is_squarefree() and len(rts) == n
        big = [r for r in rts if not (abs(r) < RealIntervalField(300)(lam0.lower()))]
        strict = (len(big) == 1 and p.is_squarefree())
        assert len(big) == 1
    # bounds, r = 1..12
    one = vector(ZZ, [1]*n); xr = [xi.polynomial()(w0).real() for xi in x]
    sx = sum(xr); xmax = max(xr, key=lambda u: u.upper()); xmin = min(xr, key=lambda u: u.lower())
    for r in range(1, 13):
        V = one*(M^(r-1))*one
        RR2 = RealIntervalField(3000); eps = RR2(2)^-100; assert lam0^(r-1)*sx/xmax < RR2(V) + eps and RR2(V) - eps < lam0^(r-1)*sx/xmin
    print(n, "ok; strictly dominant:", strict, " primitive:", all(e > 0 for e in (M^(n*n)).list()))
# strictness is needed for n >= 4: geometric a
for n in range(2, 9):
    Mg = extten([QQ(2)^i for i in range(n)], 1)
    print("geometric n=%d: equals strict M: %s, rho=%s vs %s" % (n, Mg == proofM(n), max(abs(r) for r in Mg.charpoly().roots(QQbar, multiplicities=False)).n(30), (1+2*cos(2*pi/(n+4))).n(30)))
