# 2026-11-09 - Claude-Code (jts-mini): written for working-notes/centroid-section-worked-n5-2026-11-09.org
"""centroid_worked_n5.py -- every number of the worked n = 5 example of Part III's sec-centroid
and sec-moments, computed exactly (fractions), plus a validation block that reproduces the n = 3
numbers printed in the paper.

Reuses centroids_moments.py (KK listing of S_n, LYM-chain listing / DP of the lattice points of
t*Koz(n), sumsets, the simplex second-moment formula).  New here:
  * continuous moments of Koz(n; 0, d) from the staircase tiling (thm-staircase): each cell is a
    lattice translate of a product of two orthoschemes on complementary coordinate blocks, so its
    uniform measure is the law of a + b with a, b independent and uniform on two faces;
  * an exact Fourier-Motzkin membership test for Koz(5; 0, 1) = Koz(5) + shift Koz(5), giving a
    count of its lattice points independent of the sumset of L_5 (cor-additivity);
  * polynomial fits in r of the coordinate sums over FF(5; 0^r) and over r*Koz(5) cap Z^6, and
    their 1/r expansions (obs-dilates, conj-centroid-dilation).

Usage:  ulimit -v 4000000; timeout 600 python3 centroid_worked_n5.py [R]     (R = max rank, default 8)
Output: runs/2026-11-09_centroid-worked-n5.txt
"""
import os
import sys
import time
from fractions import Fraction as Q
from math import comb, factorial

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import centroids_moments as cm  # noqa: E402

R = int(sys.argv[1]) if len(sys.argv) > 1 else 8
n = 5
C = [comb(n, k) for k in range(n + 1)]          # 1 5 10 10 5 1
T0 = time.time()


# ------------------------------------------------------------------ helpers
def fd(x, p=4):
    return ("%." + str(p) + "f") % float(x)


def vec(v, p=4):
    return "(" + ", ".join(fd(x, p) for x in v) + ")"


def vq(v):
    return "(" + ", ".join(str(x) for x in v) + ")"


def stats(pts, wts=None):
    """count/total weight, centroid (list of Q), covariance (matrix of Q)."""
    W, S1, S2 = cm.moments_from_points(pts, wts)
    c = [Q(s, W) for s in S1]
    D = len(c)
    cov = [[Q(S2[i][j], W) - c[i] * c[j] for j in range(D)] for i in range(D)]
    return W, c, cov


def koz_vertices(nn, N=None, d=0):
    N = nn + d if N is None else N
    out = []
    for j in range(1, nn + 1):
        v = [0] * (N + 1)
        for k in range(j + 1):
            v[k + d] = comb(nn, k)
        out.append(v)
    return out


def simplex_moments(verts):
    m = len(verts)
    c = [Q(sum(v[i] for v in verts), m) for i in range(len(verts[0]))]
    return c, cm.simplex_second_moment(verts)


def det(M):
    M = [[Q(x) for x in row] for row in M]
    m = len(M)
    d = Q(1)
    for i in range(m):
        p = next((r for r in range(i, m) if M[r][i] != 0), None)
        if p is None:
            return Q(0)
        if p != i:
            M[i], M[p] = M[p], M[i]
            d = -d
        d *= M[i][i]
        for r in range(i + 1, m):
            f = M[r][i] / M[i][i]
            for c_ in range(i, m):
                M[r][c_] -= f * M[i][c_]
    return d


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def transpose(A):
    return [list(r) for r in zip(*A)]


def sub_cov(cov, idx, scale):
    """covariance restricted to coordinates idx, coordinate i divided by scale[i]."""
    return [[cov[i][j] / (scale[i] * scale[j]) for j in idx] for i in idx]


def trace(M):
    return sum(M[i][i] for i in range(len(M)))


def fit_poly(xs, ys):
    """coefficients c_0..c_m of the polynomial of degree m = len(xs)-1 through the points."""
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


def peval(c, x):
    return sum(ci * Q(x) ** i for i, ci in enumerate(c))


def pstr(c, var="r"):
    terms = []
    for i in range(len(c) - 1, -1, -1):
        if c[i] != 0:
            terms.append("(%s)%s" % (c[i], "" if i == 0 else var + ("^%d" % i if i > 1 else "")))
    return " + ".join(terms) if terms else "0"


def mq(M):
    return "[" + "; ".join(" ".join(str(x) for x in row) for row in M) + "]"


def print_matrix(M, labels, exact=True):
    w = max(len(str(x)) for row in M for x in row) if exact else 9
    for lab, row in zip(labels, M):
        print("    %-4s " % lab + "  ".join((str(x) if exact else fd(x, 5)).rjust(w) for x in row))


# ------------------------------------------------------------------ staircase moments
def koz_0d_moments(nn, d):
    """(NV, centroid, second-moment matrix) of the uniform measure on Koz(nn; 0, d), 0 <= d <= nn-1,
    in coordinates x_0..x_{nn+d}, from the staircase cells C_j, j = 1..nn-d (cor-rank2-volume)."""
    N = nn + d
    D = nn - 1 + d
    V = koz_vertices(nn, N)
    Vs = koz_vertices(nn, N, d)
    totw, m1, m2 = Q(0), [Q(0)] * (N + 1), [[Q(0)] * (N + 1) for _ in range(N + 1)]
    for j in range(1, nn - d + 1):
        A = V[:d + j]                  # conv(F_1..F_{d+j})
        B = Vs[j - 1:]                 # shift^d conv(F_j..F_n)
        pa = 1
        for k in range(2, d + j + 1):
            pa *= comb(nn, k)
        pb = 1
        for k in range(j + 1, nn + 1):
            pb *= comb(nn, k)
        w = comb(D, d + j - 1) * pa * pb                     # NV(C_j)
        # independent check of NV(C_j): product of the two orthoschemes' volumes
        assert Q(pa, factorial(d + j - 1)) * Q(pb, factorial(nn - j)) * factorial(D) == w
        ea, ma = simplex_moments(A)
        eb, mb = simplex_moments(B)
        for i in range(N + 1):
            m1[i] += w * (ea[i] + eb[i])
            for k in range(N + 1):
                m2[i][k] += w * (ma[i][k] + ea[i] * eb[k] + eb[i] * ea[k] + mb[i][k])
        totw += w
    c = [x / totw for x in m1]
    M = [[x / totw for x in row] for row in m2]
    return totw, c, M


def cov_from(c, M):
    return [[M[i][j] - c[i] * c[j] for j in range(len(c))] for i in range(len(c))]


# ------------------------------------------------------------------ Fourier-Motzkin
def fm_feasible(ineqs, nv):
    """ineqs: list of (coef tuple of length nv, rhs), meaning coef . a <= rhs (integers).
    Exact Fourier-Motzkin elimination; True iff a real solution exists."""
    for v in range(nv):
        pos = [q for q in ineqs if q[0][v] > 0]
        neg = [q for q in ineqs if q[0][v] < 0]
        out = [q for q in ineqs if q[0][v] == 0]
        for (pc, pr) in pos:
            for (nc, nr) in neg:
                a, b = pc[v], -nc[v]
                out.append((tuple(b * x + a * y for x, y in zip(pc, nc)), b * pr + a * nr))
        # drop duplicates
        ineqs = list(set(out))
    return all(r >= 0 for _, r in ineqs)


def in_koz5_01(x):
    """x = (x_0..x_6) in Koz(5) + shift^1 Koz(5)?  Variables (a_3, a_4, a_5); a_2 = x_2 - 5."""
    if x[0] != 1 or x[1] != 6 or x[6] < 0:
        return False
    a2 = x[2] - 5
    ineqs = [((0, 0, 0), 10 - a2),            # a_2 <= 10       (mu_2 <= 1)
             ((1, 0, 0), a2),                 # a_3 <= a_2      (mu_3 <= mu_2)
             ((-1, 2, 0), 0),                 # 2a_4 <= a_3     (mu_4 <= mu_3)
             ((0, -1, 5), 0),                 # 5a_5 <= a_4     (mu_5 <= mu_4)
             ((0, 0, -1), 0),                 # a_5 >= 0
             ((-1, 0, 0), 10 - x[3]),         # b_3 <= 10
             ((1, -1, 0), x[3] - x[4]),       # b_4 <= b_3
             ((0, 1, -2), x[4] - 2 * x[5]),   # 2b_5 <= b_4
             ((0, 0, 1), x[5] - 5 * x[6])]    # 5b_6 <= b_5
    return fm_feasible(ineqs, 3)


# ================================================================== VALIDATION (n = 3, paper numbers)
print("# Produced by code/oneoff/centroid_worked_n5.py (R = %d), %s, on %s." % (R, time.strftime("%Y-%m-%d %H:%M"), os.uname()[1]))
print("# Written for working-notes/centroid-section-worked-n5-2026-11-09.org (Part III, sec-centroid and sec-moments at n = 5).")
print("=" * 90)
print("VALIDATION: numbers printed in the paper at n = 3 (ex-centroid-n3, ex-centroid-rank2,")
print("ex-moments-n3, thm-n3-equal-shifts) and Kupreyeva's c(S_4)")
print("=" * 90)
S3 = cm.Sn_points(3)
_, c3, cov3 = stats(S3)
print("c(S_3) (x2,x3) =", vq(c3[2:]), " expect (9/5, 1/5)")
print("Cov(S_3) (x2,x3) =", mq([cov3[2][2:], cov3[3][2:]]), " expect [[34/25,6/25],[6/25,4/25]]")
ck3, mk3 = simplex_moments(koz_vertices(3))
print("c(Koz3) =", vq(ck3[2:]), " Cov(Koz3) =", mq([r[2:] for r in cov_from(ck3, mk3)[2:]]),
      " expect (2,1/3), [[1/2,1/12],[1/12,1/18]]")
_, c4, _ = stats(cm.Sn_points(4))
print("c(S_4) (x2,x3,x4) =", vq(c4[2:]), " expect (17/4, 19/16, 1/16)")
ff = cm.ff_sumset(3, (0, 0))
print("FF(3;0,0): %d points, centroid (x2,x3) = %s, expect 12, (15/4, 1/2)" % (len(ff), vq(stats(ff)[1][2:])))
ff = cm.ff_sumset(3, (0, 1))
W, cf, covf = stats(ff)
print("FF(3;0,1): %d points, centroid (x2,x3,x4) = %s, expect 22, (51/11, 2, 5/22)" % (W, vq(cf[2:])))
print("  Cov FF(3;0,1) =", mq([r[2:] for r in covf[2:]]))
print("  expect [[160/121,3/11,9/242],[3/11,18/11,3/11],[9/242,3/11,85/484]]")
nv, ck, mk = koz_0d_moments(3, 1)
print("Koz(3;0,1) by staircase: NV = %s (expect 36), centroid %s (expect (37/8, 7/3, 3/8))" % (nv, vq(ck[2:])))
print("  Cov =", mq([r[2:] for r in cov_from(ck, mk)[2:]]))
print("  expect [[47/64,7/48,1/64],[7/48,13/18,5/48],[1/64,5/48,13/192]]")
nv, ck, _ = koz_0d_moments(3, 2)
print("Koz(3;0,2) by staircase: centroid %s (expect (1,3,3,10/3,2,1/3))" % vq(ck))
ok = True
for r in range(1, 7):
    ffr = cm.ff_sumset(3, (0,) * r)
    W, cr, _ = stats(ffr)
    ok &= (W == (r + 1) * (3 * r + 2) // 2 and cr[2] == Q(3 * r * (2 * r + 1), 3 * r + 2) and cr[3] == Q(r * r, 3 * r + 2))
print("thm-n3-equal-shifts count and centroid formula, r = 1..6:", ok)
# staircase at d = 0 must give the dilate 2 Koz(n)
for nn in (3, 4, 5):
    nv, ck, mk = koz_0d_moments(nn, 0)
    c1, m1 = simplex_moments(koz_vertices(nn))
    cv1, cv2 = cov_from(c1, m1), cov_from(ck, mk)
    assert ck == [2 * x for x in c1] and all(cv2[i][j] == 4 * cv1[i][j] for i in range(nn + 1) for j in range(nn + 1))
print("staircase moments at d = 0 equal those of 2 Koz(n), n = 3, 4, 5: True")

# ================================================================== RANK ONE, n = 5
print()
print("=" * 90)
print("RANK ONE, n = 5")
print("=" * 90)
S5 = cm.Sn_points(5)
L5 = [(1,) + p for p in cm.chain_enumerate(5, cm.g_lat(5))]
cpx = cm.proper_complex_fvector_counts(5)
print("|S_5| = %d (KK listing); %d distinct f-vectors among %d proper complexes on [5] (enumerated); sets equal: %s"
      % (len(S5), len(cpx), sum(cpx.values()), set((1,) + k for k in cpx) == set(S5)))
print("|L_5| = %d; S_5 subset of L_5: %s" % (len(L5), set(S5) <= set(L5)))
V = koz_vertices(5)
print("vertices F~_j (x_0..x_5):")
for j, v in enumerate(V, 1):
    print("   F~_%d = %s" % (j, vq(v)))
vol = det([[V[j][k] - V[0][k] for k in range(2, 6)] for j in range(1, 5)]) / factorial(4)
print("vol (x_2..x_5, |det|/4!) = %s;  prop-simplex-volume: prod_{k>=1} C(5,k)/5! = %s;  NV = 4! vol = %s = prod_{k>=2} C(5,k) = %d"
      % (abs(vol), Q(5 * 10 * 10 * 5 * 1, 120), abs(vol) * 24, 10 * 10 * 5 * 1))

meas = {}
for name, pts in (("S5", S5), ("L5", L5)):
    W, c, cov = stats(pts)
    meas[name] = (W, c, cov)
ckz, mkz = simplex_moments(V)
meas["Koz5"] = (None, ckz, cov_from(ckz, mkz))

print("\ncentroids (x_0..x_5), LYM mu_1..mu_5, barycentric lambda_1..lambda_5, mean vertex index sum mu_k:")
for name in ("S5", "L5", "Koz5"):
    W, c, cov = meas[name]
    mu = [c[k] / C[k] for k in range(1, 6)]
    lam = [mu[j] - (mu[j + 1] if j + 1 < 5 else 0) for j in range(5)]
    J = sum(mu)
    EJ2 = sum((2 * k - 1) * mu[k - 1] for k in range(1, 6))
    print("  %-5s x   = %s" % (name, vq(c)))
    print("        x   ~ %s" % vec(c))
    print("        mu  = %s  ~ %s" % (vq(mu), vec(mu)))
    print("        lam = %s  ~ %s" % (vq(lam), vec(lam)))
    print("        mean index = %s ~ %s;  index variance = %s ~ %s (/n^2: %s)" % (J, fd(J), EJ2 - J * J, fd(EJ2 - J * J), fd((EJ2 - J * J) / 25)))
    print("        beta residual mu_2 + mu_3 - 1 - mu_4 = %s ~ %s" % (mu[1] + mu[2] - 1 - mu[3], fd(mu[1] + mu[2] - 1 - mu[3])))


def beta(x, r=1):
    """lem-beta at n = 5, on r*Koz(5): fixes x_0, x_1, x_4, x_5; x_k -> r C(5,k) + C(5,k) x_4/5 - x_{5-k}."""
    y = list(x)
    for k in (2, 3):
        y[k] = r * C[k] + Q(C[k] * x[4], 5) - x[5 - k]
    return tuple(y)


bS = [beta(s) for s in S5]
bL = [beta(s) for s in L5]
print("\nbeta on vertices: " + ", ".join("F~_%d -> F~_%d" % (j + 1, next(i + 1 for i, w in enumerate(V) if tuple(w) == beta(v)))
                                       for j, v in enumerate(V)))
print("beta(L_5) = L_5 (bijection, n prime): %s" % (set(bL) == set(L5)))
print("beta(S_5): %d of %d images are in S_5; all images integral and in L_5: %s"
      % (sum(1 for b in bS if b in set(S5)), len(S5), set(bS) <= set(L5)))
B = [[0, -1, 1, 0], [-1, 0, 1, 0], [0, 0, 1, 0], [0, 0, 0, 1]]     # linear part of beta on (mu_2..mu_5)
print("\ncovariance matrices in LYM coordinates (mu_2..mu_5), and beta-invariance  B Sigma B^T - Sigma:")
covmu = {}
for name in ("S5", "L5", "Koz5"):
    cov = meas[name][2]
    Sg = sub_cov(cov, range(2, 6), {i: C[i] for i in range(6)})
    covmu[name] = Sg
    print("  %s  (trace %s ~ %s; sd of mu_k: %s)" % (name, trace(Sg), fd(trace(Sg), 5),
                                                    " ".join(fd(float(Sg[i][i]) ** 0.5, 4) for i in range(4))))
    print_matrix(Sg, ["mu2", "mu3", "mu4", "mu5"])
    print("   decimal:")
    print_matrix(Sg, ["mu2", "mu3", "mu4", "mu5"], exact=False)
    Dlt = [[a - b for a, b in zip(r1, r2)] for r1, r2 in zip(matmul(matmul(B, Sg), transpose(B)), Sg)]
    print("   B Sg B^T - Sg = 0: %s;  max |entry| = %s" % (all(x == 0 for r_ in Dlt for x in r_), fd(max(abs(x) for r_ in Dlt for x in r_), 5)))
ok = all(covmu["Koz5"][k - 2][l - 2] == Q((min(k, l) - 1) * (n - max(k, l) + 1), n * n * (n + 1))
         for k in range(2, 6) for l in range(2, 6))
print("prop-second-moments(2): Cov(mu_k, mu_l) = (k-1)(n-l+1)/(n^2(n+1)) for k <= l, n = 5: %s" % ok)

# Alexander core
core = [s for s in S5 if s[4] == 0]
top = [s for s in S5 if s[4] != 0]
Sm = [1] + [len(cm.Sn_points(m)) for m in range(1, 5)]
eps = Q(len(top), len(S5))
Dn = lambda s: tuple(C[k] - s[5 - k] for k in range(6))
print("\nAlexander core: |S_5 core| = %d, |S_5 top| = %d, sum_{m<5} |S_m| = %s = %d; eps_5 = %s ~ %s"
      % (len(core), len(top), "+".join(map(str, Sm)), sum(Sm), eps, fd(eps, 4)))
print("  Alexander duality D_5 maps the core onto itself: %s" % (set(map(Dn, core)) == set(core)))
_, cc, _ = stats(core)
_, ct, _ = stats(top)
muc = [cc[k] / C[k] for k in range(6)]
mut = [ct[k] / C[k] for k in range(6)]
print("  c(core) x = %s, mu_1..5 = %s; mu_k + mu_{5-k} - 1 (k=1..4) = %s" % (vq(cc), vq(muc[1:]), vq([muc[k] + muc[5 - k] - 1 for k in range(1, 5)])))
print("  c(top)  x = %s, mu_1..5 = %s" % (vq(ct), vq(mut[1:])))
mu = [meas["S5"][1][k] / C[k] for k in range(6)]
dev = [mu[k] + mu[5 - k] - 1 for k in range(1, 5)]
print("  thm-alexander-core(3) for S_5: mu_k + mu_{5-k} - 1 = %s, all in [0, eps]: %s" % (vq(dev), all(0 <= x <= eps for x in dev)))
print("    0 <= mu_5 = %s <= mu_4 = %s <= eps = %s: %s" % (mu[5], mu[4], eps, 0 <= mu[5] <= mu[4] <= eps))
J = sum(mu[1:])
print("    mean index %s ~ %s in [%s, %s] = [2, %s]: %s" % (J, fd(J), Q(4, 2), Q(4, 2) + Q(6, 2) * eps, fd(Q(4, 2) + 3 * eps), Q(2) <= J <= 2 + 3 * eps))
print("    mixture check c(S_5) = (1-eps) c(core) + eps c(top): %s" % (meas["S5"][1] == [(1 - eps) * a + eps * b for a, b in zip(cc, ct)]))

# h* and Ehrhart
c_ = [None, 1, 10, 10, 5, 1]
hstar = [0] * 5
for z2 in range(10):
    for z3 in range(10):
        for z4 in range(5):
            rho = [Q(0), Q(z2, 10), Q(z3, 10), Q(z4, 5), Q(0)]
            hstar[sum(1 for k in range(4) if rho[k] < rho[k + 1])] += 1
Lt = [cm.chain_moments(5, cm.g_lat(5, t), first=5 * t, second=False)[0] for t in range(0, 9)]
h_from_L = [sum((-1) ** j * comb(5, j) * Lt[i - j] for j in range(i + 1)) for i in range(5)]
print("\nh* by thm-hstar (asc over 500 residue vectors) = %s, sum %d" % (hstar, sum(hstar)))
print("h* from L(t), t = 0..4 (lattice listing)        = %s" % h_from_L)
print("L_Koz(5)(t), t = 0..8 = %s" % Lt)
ep = fit_poly(range(5), Lt[:5])
paper = lambda t: Q((t + 1) * (125 * t ** 3 + 250 * t ** 2 + 105 * t + 6), 6)
print("Ehrhart polynomial (fit t = 0..4) = %s" % pstr(ep, "t"))
print("  equals paper's (t+1)(125t^3+250t^2+105t+6)/6 at t = -1..8, and fit predicts t = 5..8: %s"
      % (all(peval(ep, t) == paper(t) for t in range(-1, 9)) and all(peval(ep, t) == Lt[t] for t in range(9))))

# obs-dilates at n = 5: lattice sums over t*Koz(5)
print("\nobs-dilates, n = 5: sum of x_k over t Koz(5) cap Z^6 is a polynomial of degree 5 in t;")
latS1 = {}
TMAX = max(R, 8)
for t in range(0, TMAX + 1):
    cnt, S1, _ = cm.chain_moments(5, cm.g_lat(5, t), first=5 * t, second=False)
    latS1[t] = (cnt, S1)
Lp = fit_poly(range(5), [latS1[t][0] for t in range(5)])
corr_lat = []
for k in range(2, 6):
    pk = fit_poly(range(6), [latS1[t][1][k] for t in range(6)])
    good = all(peval(pk, t) == latS1[t][1][k] for t in range(TMAX + 1))
    lead = pk[5] / (C[k] * Lp[4])
    nxt = (pk[4] * Lp[4] - pk[5] * Lp[3]) / (C[k] * Lp[4] ** 2)
    corr_lat.append((lead, nxt))
    print("  k=%d: fit on t=0..5 reproduces t=0..%d: %s;  nu_k = %s %+s/t + O(1/t^2)" % (k, TMAX, good, lead, nxt))
print("  paper obs-dilates n = 5: (4/5 - 1/(10t), 3/5 - 1/(5t), 2/5 - 3/(10t), 1/5 - 7/(20t))")

# ================================================================== RANK r, d = 0^r
print()
print("=" * 90)
print("RANK r, d = 0^r, n = 5, r = 1..%d" % R)
print("=" * 90)
cS = meas["S5"][1]
covS = meas["S5"][2]
covK = meas["Koz5"][2]
apoly = lambda r: Q((r + 1) * (125 * r ** 3 + 45 * r ** 2 + 34 * r + 6), 6)
defpoly = lambda r: Q(r * (r + 1) * (205 * r + 71), 6)
acc = {(0,) * 6: 1}
ffsums = {}
rows = []
for r in range(1, R + 1):
    t1 = time.time()
    new = {}
    for a, m in acc.items():
        for s in S5:
            key = (a[0] + s[0], a[1] + s[1], a[2] + s[2], a[3] + s[3], a[4] + s[4], a[5] + s[5])
            new[key] = new.get(key, 0) + m
    acc = new
    pts = list(acc)
    wts = [acc[p] for p in pts]
    a_r = len(pts)
    Wm, cm_, covm = stats(pts, wts)
    _, cu, covu = stats(pts)
    Lcnt, LS1, LS2 = cm.chain_moments(5, cm.g_lat(5, r), first=5 * r)
    cl = [Q(r)] + [Q(LS1[k], Lcnt) for k in range(1, 6)]
    covl = [[0] * 6 for _ in range(6)]
    for k in range(1, 6):
        for l in range(1, 6):
            covl[k][l] = Q(LS2[k][l], Lcnt) - cl[k] * cl[l]
    ffsums[r] = (a_r, [sum(p[k] for p in pts) for k in range(6)])
    scale = {i: r * C[i] for i in range(6)}
    nu = lambda c: [c[k] / (r * C[k]) for k in range(2, 6)]
    tv = lambda cov: trace(sub_cov(cov, range(2, 6), scale))
    push_ok = (cm_ == [r * x for x in cS]) and all(covm[i][j] == r * covS[i][j] for i in range(6) for j in range(6))
    print("\nr = %d   (%.1fs)" % (r, time.time() - t1))
    print("  |FF(5;0^r)| = a(r) = %d (paper formula %s);  ordered tuples 70^r = %d" % (a_r, apoly(r), Wm))
    print("  lattice points L(r) = %d (paper formula %s);  fill = %s ~ %s" % (Lcnt, paper(r), Q(a_r, Lcnt), fd(Q(a_r, Lcnt))))
    print("  deficiency L - a = %d (paper r(r+1)(205r+71)/6 = %s)" % (Lcnt - a_r, defpoly(r)))
    print("  push-forward (multiplicity-weighted FF): centroid = r c(S_5) and Cov = r Cov(S_5) exactly: %s" % push_ok)
    for name, c in (("c(FF)", cu), ("r c(S5)", [r * x for x in cS]), ("c(lattice)", cl), ("r c(Koz5)", [r * x for x in ckz])):
        nv_ = nu(c)
        print("  %-11s x = %s" % (name, vq(c)))
        print("  %-11s nu_2..5 = %s;  beta residual nu2+nu3-1-nu4 = %s" % ("", vec(nv_), fd(nv_[0] + nv_[1] - 1 - nv_[2], 5)))
    covs = (("FF", covu), ("push-fwd", covm), ("lattice", covl), ("polytope", [[r * r * x for x in row] for row in covK]))
    print("  total nu-variance (trace, nu_2..nu_5): " + "  ".join("%s %s" % (nm, fd(tv(cv), 5)) for nm, cv in covs))
    print("  nu-variances (diagonal):")
    for nm, cv in covs:
        S_ = sub_cov(cv, range(2, 6), scale)
        print("    %-9s %s" % (nm, " ".join(fd(S_[i][i], 5) for i in range(4))))
    if r in (2, 3):
        print("  Cov in nu coordinates, FF(5;0^%d), exact:" % r)
        print_matrix(sub_cov(covu, range(2, 6), scale), ["nu2", "nu3", "nu4", "nu5"])
    rows.append((r, a_r, Lcnt))
    sys.stdout.flush()

print("\nconj-centroid-dilation data: c(FF(5;0^r))/r in nu, minus c(Koz5) = (4/5,3/5,2/5,1/5):")
for r in range(1, R + 1):
    a_r, s1 = ffsums[r]
    nu_ = [Q(s1[k], a_r * r * C[k]) for k in range(2, 6)]
    print("  r=%d  nu = %s   nu - c(Koz5) = %s" % (r, vec(nu_), vec([x - y for x, y in zip(nu_, [Q(4, 5), Q(3, 5), Q(2, 5), Q(1, 5)])])))
# polynomial fits of the FF sums
print("\nIs sum_{FF(5;0^r)} x_k a polynomial of degree <= 5 in r?  (fit on r = 1..6, test r = 7..%d)" % R)
ap = fit_poly(range(1, 6), [ffsums[r][0] for r in range(1, 6)])
print("  a(r) fit on r=1..5: %s; reproduces r <= %d: %s" % (pstr(ap), R, all(peval(ap, r) == ffsums[r][0] for r in range(1, R + 1))))
for k in range(2, 6):
    pk = fit_poly(range(1, 7), [ffsums[r][1][k] for r in range(1, 7)])
    good = all(peval(pk, r) == ffsums[r][1][k] for r in range(1, R + 1))
    lead = pk[5] / (C[k] * ap[4])
    nxt = (pk[4] * ap[4] - pk[5] * ap[3]) / (C[k] * ap[4] ** 2)
    print("  k=%d: fit reproduces r = 7..%d: %s;  sum = %s" % (k, R, good, pstr(pk)))
    if good:
        print("       => nu_k(FF) = %s %+s/r + O(1/r^2)   [lattice: %s %+s/r]" % (lead, nxt, corr_lat[k - 2][0], corr_lat[k - 2][1]))

# ================================================================== d = (0,1) and (0,4)
print()
print("=" * 90)
print("POSITIVE GAP: d = (0,1), n = 5 (N = 6); and the product regime d = (0,4)")
print("=" * 90)
N = 6
H = [sum(comb(5, k - d) for d in (0, 1) if 0 <= k - d <= 5) for k in range(N + 1)]
ffm = cm.ff_sumset(5, (0, 1), Sn=S5, multiplicity=True)
latset = set(cm.ff_sumset(5, (0, 1), Sn=L5))
t1 = time.time()
box = [(1, 6, x2, x3, x4, x5, x6) for x2 in range(5, 16) for x3 in range(0, 21) for x4 in range(0, 16)
       for x5 in range(0, 7) for x6 in range(0, 2)]
fmset = set(x for x in box if in_koz5_01(x))
print("dim F_k = H_k = %s" % H)
print("|FF(5;0,1)| = %d of 4900 pairs" % len(ffm))
print("lattice points: L_5 + shift L_5 = %d;  Fourier-Motzkin over a %d-point box = %d (%.1fs); sets equal: %s"
      % (len(latset), len(box), len(fmset), time.time() - t1, latset == fmset))
print("FF subset of lattice: %s;  fill = %s ~ %s" % (set(ffm) <= latset, Q(len(ffm), len(latset)), fd(Q(len(ffm), len(latset)))))
nvk, ck01, mk01 = koz_0d_moments(5, 1)
print("Koz(5;0,1): NV = %d (tab:volumes 102500), vol = NV/5! = %s (tab:volumes 5125/6)" % (nvk, Q(nvk, 120)))
pts = list(ffm)
_, cF, covF = stats(pts)
_, cP, covP = stats(pts, [ffm[p] for p in pts])
_, cL, covL = stats(sorted(latset))
shift1 = lambda v: [0] + list(v)
cInd = [a + b for a, b in zip(list(cS) + [0], shift1(cS))]
cKInd = [a + b for a, b in zip(list(ckz) + [0], shift1(ckz))]
covK01 = cov_from(ck01, mk01)
print("push-forward centroid = c(S5) + shift c(S5): %s" % (cP == cInd))
for name, c in (("c(FF)", cF), ("indep sum c(S5)", cInd), ("c(lattice)", cL), ("c(Koz(5;0,1))", ck01), ("indep sum c(Koz5)", cKInd)):
    print("  %-18s x = %s" % (name, vq(c)))
    print("  %-18s nu_2..6 = %s" % ("", vec([c[k] / H[k] for k in range(2, 7)])))
sc = {i: H[i] for i in range(N + 1)}
print("  total nu-variance (nu_2..nu_6): FF %s  push-fwd %s  lattice %s  polytope %s  indep-Koz %s"
      % tuple(fd(trace(sub_cov(cv, range(2, 7), sc)), 5)
              for cv in (covF, covP, covL, covK01,
                         [[(covK[i][j] if i < 6 and j < 6 else 0) + (covK[i - 1][j - 1] if i >= 1 and j >= 1 else 0)
                           for j in range(7)] for i in range(7)])))
# product regime d = (0,4)
ff4 = cm.ff_sumset(5, (0, 4), Sn=S5)
lat4 = cm.ff_sumset(5, (0, 4), Sn=L5)
sh4 = lambda v: [0] * 4 + list(v)
pad = lambda v: list(v) + [0] * 4
_, cF4, _ = stats(ff4)
_, cL4, _ = stats(lat4)
print("\nd = (0,4) (product regime): |FF| = %d, lattice = %d; c(FF) = c(S5)+shift^4 c(S5): %s; c(lattice) = sum of shifted c(L5): %s"
      % (len(ff4), len(lat4), cF4 == [a + b for a, b in zip(pad(cS), sh4(cS))],
         cL4 == [a + b for a, b in zip(pad(meas["L5"][1]), sh4(meas["L5"][1]))]))
# the n = 5 rows of tab:fill (right half) and tab:volumes, d = 0..4
print("\nn = 5 rows of tab:fill and tab:volumes, Koz(5;0,d):")
print("   d  |FF|  lattice  fill     NV (staircase)  vol = NV/D!")
for d in range(0, 5):
    ffd = cm.ff_sumset(5, (0, d), Sn=S5)
    latd = cm.ff_sumset(5, (0, d), Sn=L5)
    nvd, _, _ = koz_0d_moments(5, d)
    D = 4 + d
    print("  %2d  %4d  %6d   %.5f  %14d  %s" % (d, len(ffd), len(latd), len(ffd) / len(latd), nvd, Q(nvd, factorial(D))))
print("  paper: |FF| 627 1858 3805 4857 4900; lattice 1108 4484 14214 26119 26244; fill 0.566 0.414 0.268 0.186(0.18596) 0.187(0.18671)")
print("         NV 8000 102500 1287500 9625000 17500000; vol 1000/3 5125/6 64375/36 34375/18 15625/36")
print("\ntotal time %.1fs" % (time.time() - T0))
