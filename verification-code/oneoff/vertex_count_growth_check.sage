# vertex_count_growth_check.sage -- 2026-11-17, jts-mini (Claude-Code).
#
# Part IV, Proposition prop-gap-one and Remark rem-vertex-growth.  M(n; delta) is the rank-two
# extremal matrix of a strictly log-concave leg vector (closed form of Corollary cor-rank2-lc; its
# agreement with the polytopes is checked in vertex_count_transfer_check.sage).
#   (a) gap one: with theta = pi/(n+4), lambda = 1 + 2 cos(2 theta), q = 1/(2 cos theta),
#       S_j = q^j sin((j+2) theta), S_{n+1} = 0, x_j = S_j - S_{j+1}:  M x = lambda x and x > 0,
#       to 200 bits, 2 <= n <= 60; and lambda is the largest root of the exact characteristic
#       polynomial, 2 <= n <= 14.
#   (b) gap n-2: x^2 - n x + 2 divides the characteristic polynomial exactly and its larger root
#       is the spectral radius, 4 <= n <= 30 (it fails at n = 3, where gap n-2 is gap one).
#   (c) the table of spectral radii in Remark rem-vertex-growth, n <= 7.
# Run from code/:  sage oneoff/vertex_count_growth_check.sage
# Log: ../runs/2026-11-17_vertex-count-transfer/vertex_count_growth_check.txt
import os
from sage.all import ZZ, QQ, QQbar, RealField, matrix, vector, identity_matrix, PolynomialRing, pi, cos, sin
OUT = "../runs/2026-11-17_vertex-count-transfer"
os.makedirs(OUT, exist_ok=True)
LOG = open(os.path.join(OUT, "vertex_count_growth_check.txt"), "w")
def say(*a):
    s = " ".join(str(x) for x in a); print(s); LOG.write(s + "\n"); LOG.flush()

def M(n, delta):
    if delta == 0: return identity_matrix(ZZ, n)
    if delta >= n: return matrix(ZZ, n, n, lambda i, j: 1)
    m = n - delta
    def e(i, j):
        t = i - delta
        return 0 if (1 <= t <= m and 1 <= j <= m and (j < t or j == t + 1)) else 1
    return matrix(ZZ, n, n, lambda i, j: e(i + 1, j + 1))

RF = RealField(200)
say("== (a) gap one: eigenvector identity, 200 bits")
worst = RF(0)
for n in range(2, 61):
    th = RF(pi) / (n + 4); lam = 1 + 2 * cos(2 * th); q = 1 / (2 * cos(th))
    S = [None] + [q ** j * sin((j + 2) * th) for j in range(1, n + 1)] + [RF(0)]
    x = vector(RF, [S[j] - S[j + 1] for j in range(1, n + 1)])
    assert min(x) > 0, n
    res = (M(n, 1).change_ring(RF) * x - lam * x).norm() / x.norm()
    worst = max(worst, res)
say("  2 <= n <= 60: x > 0 always; largest relative residual |Mx - lambda x|/|x| =", worst.n(30))
assert worst < RF(2) ** (-150)
for n in range(2, 15):
    cp = M(n, 1).charpoly()
    rho = max(abs(z) for z in cp.roots(QQbar, multiplicities=False))
    th = RF(pi) / (n + 4)
    assert abs(RF(rho) - (1 + 2 * cos(2 * th))) < RF(10) ** (-40), n
say("  2 <= n <= 14: 1 + 2cos(2pi/(n+4)) is the largest root of the exact characteristic polynomial")

say("== (b) gap n-2: x^2 - n x + 2")
R = PolynomialRing(QQ, 'x'); xx = R.gen()
for n in range(4, 31):
    cp = R(M(n, n - 2).charpoly())
    assert cp % (xx ** 2 - n * xx + 2) == 0, n
    rho = max(abs(z) for z in cp.roots(QQbar, multiplicities=False))
    assert rho == (n + QQbar(n * n - 8).sqrt()) / 2, n
say("  4 <= n <= 30: divides, and (n + sqrt(n^2-8))/2 is the spectral radius")

say("== (c) spectral radii of M(n; delta), 2 <= n <= 7, 1 <= delta <= n-1")
for n in range(2, 8):
    row = []
    for d in range(1, n):
        cp = M(n, d).charpoly()
        rho = max(abs(z) for z in cp.roots(QQbar, multiplicities=False))
        row.append("%.4f" % float(rho))
    say("  n =", n, ":", "  ".join(row))
    for d in range(1, n):
        say("     delta =", d, " charpoly:", M(n, d).charpoly().factor())
LOG.close()
