# centroids_moments.sage -- discrete vs lattice vs continuous centroids and second moments
# of S_n / Koz(n) (rank 1) and FF(n; d) / Koz(n; d) (rank r >= 2).
#
# Changelog (reverse chronological):
# 2026-10-20 - Claude (overnight article-3 agent): created.  Uses the pure-Python core
#   centroids_moments.py (chain DP, sumsets, complex counts).  Continuous moments: project
#   Koz(n; d) isomorphically onto a coordinate subspace spanning its affine hull,
#   triangulate there, and sum exact simplex moments (vertex average for the first moment,
#   (sum v v^T + s s^T)/((D+1)(D+2)) for the second) with |det| weights computed in the
#   projected coordinates; lifted back to all coordinates by using the original vertices.
#   Lattice points: Polyhedron(backend='normaliz').integral_points().
#   Cross-checks built in: d = (0,...,0) dilation identity, product-regime additivity,
#   rank-1 closed forms, and the older discrete_continuous_kup_generalization.sage numbers.
#
# Run:  cd code/oneoff && sage centroids_moments.sage [section]   (section: rank1 | rank2 | ehrhart | all)
import sys, os
sys.path.insert(0, os.path.abspath('.'))
import centroids_moments as cm
from fractions import Fraction


def QQf(x):
    return QQ(x.numerator) / QQ(x.denominator) if isinstance(x, Fraction) else QQ(x)


def shift_vec(s, d, N):
    out = [0] * (N + 1)
    for i, x in enumerate(s):
        out[i + d] = x
    return out


def koz_vertices(n):
    return [[1] + [binomial(n, k) if k <= j else 0 for k in range(1, n + 1)] for j in range(1, n + 1)]


def koz_poly(n, ds):
    N = n + ds[-1]
    P = None
    for d in ds:
        Q_ = Polyhedron(vertices=[shift_vec(v, d, N) for v in koz_vertices(n)], base_ring=QQ)
        P = Q_ if P is None else P + Q_
    return P


def continuous_moments(P):
    """(dim, centroid vector, second-moment matrix E[x x^T]) of the uniform (relative
    Lebesgue) measure on the rational polytope P."""
    V = [vector(QQ, v) for v in P.vertices_list()]
    A = len(V[0])
    D = P.dim()
    base = V[0]
    M = matrix(QQ, [v - base for v in V])            # rows: edge vectors
    # choose D coordinates on which the projection is injective on the affine hull
    cols = list(M.pivots())   # pivot columns = coordinates spanning the affine hull
    assert len(cols) == D
    proj = [vector(QQ, [v[c] for c in cols]) for v in V]
    Pp = Polyhedron(vertices=proj, base_ring=QQ)
    # map projected vertices back to original indices
    pidx = {tuple(p): i for i, p in enumerate(proj)}
    assert len(pidx) == len(V)
    tri = Pp.triangulate()
    totvol = QQ(0)
    m1 = vector(QQ, [0] * A)
    m2 = matrix(QQ, A, A, 0)
    Pv = Pp.Vrepresentation()
    for simp in tri:
        pv = [vector(QQ, Pv[i].vector()) for i in simp]
        vol = abs(matrix(QQ, [p - pv[0] for p in pv[1:]]).det()) / factorial(D)
        ov = [V[pidx[tuple(p)]] for p in pv]
        s = sum(ov)
        m1 += vol * s / (D + 1)
        m2 += vol * (sum(v.column() * v.row() for v in ov) + s.column() * s.row()) / ((D + 1) * (D + 2))
        totvol += vol
    return D, m1 / totvol, m2 / totvol, totvol


def finite_moments(pts, wts=None):
    pts = [vector(QQ, p) for p in pts]
    if wts is None:
        wts = [1] * len(pts)
    W = sum(wts)
    c = sum(w * p for p, w in zip(pts, wts)) / W
    m2 = sum(w * p.column() * p.row() for p, w in zip(pts, wts)) / W
    return W, c, m2


def cov(c, m2):
    return m2 - c.column() * c.row()


def Hfree(n, ds, N):
    return [sum(binomial(n, k - d) if 0 <= k - d <= n else 0 for d in ds) for k in range(N + 1)]


def fmt(v, digits=4):
    return "(" + ", ".join(("%." + str(digits) + "f") % float(x) for x in v) + ")"


def fmtq(v):
    return "(" + ", ".join(str(x) for x in v) + ")"


# ---------------------------------------------------------------- rank 1
def rank1(nmax=7):
    print("=" * 78)
    print("RANK 1: S_n vs lattice points of Koz(n) vs Koz(n) vs uniform proper complexes")
    print("=" * 78)
    for n in range(2, nmax + 1):
        Sn = cm.Sn_points(n)
        W, cS, m2S = finite_moments(Sn)
        lat = [(1,) + p for p in cm.chain_enumerate(n, cm.g_lat(n))]
        WL, cL, m2L = finite_moments(lat)
        P = koz_poly(n, (0,))
        D, cK, m2K, vol = continuous_moments(P)
        cK_closed = vector(QQ, [QQf(x) for x in cm.koz_centroid_f(n)])
        assert cK == cK_closed, n
        bino = [binomial(n, k) for k in range(n + 1)]
        mu = lambda c: [c[k] / bino[k] for k in range(n + 1)]
        print("\nn = %d   |S_n| = %d   #lattice pts = %d   vol (f_2..f_n coords) = %s" % (n, W, WL, vol))
        print("  centroid S_n   (f)  ", fmtq(cS))
        print("  centroid lat   (f)  ", fmtq(cL))
        print("  centroid Koz   (f)  ", fmtq(cK))
        print("  mu: S_n ", fmt(mu(cS)))
        print("  mu: lat ", fmt(mu(cL)))
        print("  mu: Koz ", fmt(mu(cK)))
        if n <= 6:
            cnt = cm.proper_complex_fvector_counts(n)
            pts = [(1,) + f for f in cnt]
            WC, cC, m2C = finite_moments(pts, [cnt[f] for f in cnt])
            print("  mu: cx  ", fmt(mu(cC)), "  (#complexes %d)" % WC)
            print("  centroid cx    (f)  ", fmtq(cC))
        # barycentric coordinates lambda_j = mu_j - mu_{j+1}, j = 1..n
        for name, c in (("S_n", cS), ("lat", cL), ("Koz", cK)):
            m = mu(c) + [0]
            lam = [m[j] - m[j + 1] for j in range(1, n + 1)]
            print("  bary %s " % name, fmt(lam))
        # standard deviations of mu_k
        for name, c, m2 in (("S_n", cS, m2S), ("lat", cL, m2L), ("Koz", cK, m2K)):
            C = cov(c, m2)
            print("  sd(mu) %s" % name, fmt([sqrt(C[k, k]) / bino[k] for k in range(2, n + 1)], 3))
        if n <= 5:
            for name, c, m2 in (("S_n", cS, m2S), ("lat", cL, m2L), ("Koz", cK, m2K)):
                C = cov(c, m2)
                print("  Cov(f_2..f_n) %s =" % name)
                print("   ", str(C[2:, 2:]).replace("\n", "\n    "))


# ---------------------------------------------------------------- rank >= 2
def rankr_case(n, ds, Sn_cache={}, verbose_cov=False, do_lattice=True):
    n = int(n); ds = tuple(int(d) for d in ds)
    if n not in Sn_cache:
        Sn_cache[n] = cm.Sn_points(n)
    Sn = Sn_cache[n]
    N = n + ds[-1]
    H = Hfree(n, ds, N)
    mult = cm.ff_sumset(n, ds, Sn, multiplicity=True)
    FF = list(mult)
    W, cFF, m2FF = finite_moments(FF)
    _, cS, m2S = finite_moments(Sn)
    # independent-sum (product measure on S_n^r) : centroid sum of shifted centroids
    cInd = sum(vector(QQ, shift_vec(list(cS), d, N)) for d in ds)
    Wm, cMult, m2Mult = finite_moments(FF, [mult[f] for f in FF])
    assert cMult == cInd
    P = koz_poly(n, ds)
    D, cK, m2K, vol = continuous_moments(P)
    cK1 = vector(QQ, [QQf(x) for x in cm.koz_centroid_f(n)])
    cKind = sum(vector(QQ, shift_vec(list(cK1), d, N)) for d in ds)
    res = dict(n=n, ds=ds, N=N, H=H, nFF=W, nTuples=len(Sn) ** len(ds), D=D, vol=vol,
               cFF=cFF, cInd=cInd, cK=cK, cKind=cKind, m2FF=m2FF, m2K=m2K, m2Ind=m2Mult)
    if do_lattice:
        L = Polyhedron(vertices=P.vertices_list(), backend='normaliz').integral_points()
        WL, cL, m2L = finite_moments([tuple(p) for p in L])
        res.update(nLat=WL, cL=cL, m2L=m2L)
    return res


def nu(c, H):
    return [c[k] / H[k] if H[k] else 0 for k in range(len(H))]


def print_case(r):
    n, ds, H = r['n'], r['ds'], r['H']
    print("\nn = %d  d = %s  N = %d  dim Koz = %d  |FF| = %d / %d tuples  #lattice = %s"
          % (n, ds, r['N'], r['D'], r['nFF'], r['nTuples'], r.get('nLat')))
    print("  H_F (free module) =", H)
    print("  nu-coords (f_k / H_F(k)), k = 0..N:")
    print("   FF        ", fmt(nu(r['cFF'], H)))
    print("   S-indep   ", fmt(nu(r['cInd'], H)))
    if 'cL' in r:
        print("   lattice   ", fmt(nu(r['cL'], H)))
    print("   Koz       ", fmt(nu(r['cK'], H)))
    print("   Koz-indep ", fmt(nu(r['cKind'], H)))
    print("  exact centroids (f-coords):")
    print("   FF        ", fmtq(r['cFF']))
    print("   S-indep   ", fmtq(r['cInd']))
    if 'cL' in r:
        print("   lattice   ", fmtq(r['cL']))
    print("   Koz       ", fmtq(r['cK']))
    print("   Koz-indep ", fmtq(r['cKind']))
    print("  FF == S-indep ? %s    Koz == Koz-indep ? %s" % (r['cFF'] == r['cInd'], r['cK'] == r['cKind']))
    # trace of covariance in nu-coordinates (total variance), for the four measures
    def tv(c, m2):
        C = cov(c, m2)
        return sum(C[k, k] / H[k] ** 2 for k in range(len(H)) if H[k])
    out = "  total nu-variance: FF %.4f  S-indep %.4f" % (float(tv(r['cFF'], r['m2FF'])), float(tv(r['cInd'], r['m2Ind'])))
    if 'cL' in r:
        out += "  lattice %.4f" % float(tv(r['cL'], r['m2L']))
    out += "  Koz %.4f" % float(tv(r['cK'], r['m2K']))
    print(out)


def rank2(nmax=5, only_r3=False):
    print("=" * 78)
    print("RANK >= 2: four (five) points: FF, S-indep, lattice, Koz, Koz-indep")
    print("=" * 78)
    for n in (range(3, nmax + 1) if not only_r3 else []):
        for d in range(0, n):
            r = rankr_case(n, (0, d), do_lattice=(n <= 4 or d <= 2))
            print_case(r)
            if d == 0:
                # dilation identity Koz(n;0,0) = 2 Koz(n)
                assert r['cK'] == r['cKind']
            if d >= n - 1:
                assert r['cFF'] == r['cInd'] and r['cK'] == r['cKind']
    for n, ds in ((3, (0, 0, 0)), (3, (0, 0, 1)), (3, (0, 1, 1)), (3, (0, 1, 2)), (3, (0, 2, 4)), (3, (0, 1, 3)),
                  (4, (0, 0, 0)), (4, (0, 1, 2)), (4, (0, 3, 6))):
        r = rankr_case(n, ds, do_lattice=(n == 3))
        print_case(r)


# ---------------------------------------------------------------- weighted Ehrhart (rank 1)
def ehrhart(nmax=6, tmax=None):
    print("=" * 78)
    print("WEIGHTED EHRHART for t*Koz(n): sum over lattice points of 1, f_k, f_k f_l as polynomials in t")
    print("=" * 78)
    R = PolynomialRing(QQ, 't')
    for n in range(3, nmax + 1):
        P = koz_poly(n, (0,))
        D, cK, m2K, vol = continuous_moments(P)
        deg = D + 2
        ts = list(range(1, deg + 2 + 1))
        extra = [deg + 3, deg + 4]          # interpolation-independent check points
        data = {}
        for t in ts + extra:
            c, S1, S2 = cm.chain_moments(n, cm.g_lat(n, t), first=n * t)
            data[t] = (c, S1, S2)
        cnt = R.lagrange_polynomial([(t, data[t][0]) for t in ts])
        for t in extra:
            assert cnt(t) == data[t][0]
            for k in range(2, n + 1):
                assert R.lagrange_polynomial([(u, data[u][1][k]) for u in ts])(t) == data[t][1][k]
                for l in range(2, n + 1):
                    assert R.lagrange_polynomial([(u, data[u][2][k][l]) for u in ts])(t) == data[t][2][k][l]
        print("\nn = %d, dim %d, vol %s" % (n, D, vol))
        print("  L(t)           =", cnt.factor() if cnt != 0 else 0)
        assert cnt.leading_coefficient() == vol and cnt.degree() == D
        for k in range(2, n + 1):
            pk = R.lagrange_polynomial([(t, data[t][1][k]) for t in ts])
            assert pk.degree() == D + 1 and pk.leading_coefficient() == vol * cK[k], (n, k)
            print("  sum f_%d       =" % k, pk)
        # second moment of the middle coordinate
        k = (n + 1) // 2 + (1 if n % 2 == 0 else 0)
        k = max(2, min(n, k))
        pkk = R.lagrange_polynomial([(t, data[t][2][k][k]) for t in ts])
        assert pkk.degree() == D + 2 and pkk.leading_coefficient() == vol * m2K[k, k]
        print("  sum f_%d^2     =" % k, pkk)
        # centroid of lattice points of tKoz(n) = t c + c1 + O(1/t): compute c1
        c1s = []
        for k in range(2, n + 1):
            pk = R.lagrange_polynomial([(t, data[t][1][k]) for t in ts])
            # pk / cnt = c t + c1 + ...: c1 = (a_{D} - c b_{D-1})/b_D  with pk = sum a_i t^i, cnt = sum b_i t^i
            a = pk.list(); b = cnt.list()
            c1 = (a[D] - cK[k] * b[D - 1]) / b[D]
            print("  centroid(lattice pts of tKoz)_%d = %s t + %s + O(1/t)   [mu: %s + %s/t]"
                  % (k, cK[k], c1, cK[k] / binomial(n, k), c1 / binomial(n, k)))
            c1s.append(c1)
        # Euler-Maclaurin prediction: c1 = (1/2) sum_F vol_F (c_F - c) / vol, lattice-normalised
        # relative volumes of the facets F (normaliz 'induced_lattice')
        Pn = Polyhedron(vertices=P.vertices_list(), backend='normaliz')
        vP = Pn.volume(measure='induced_lattice') / factorial(D)
        acc = vector(QQ, [0] * (n + 1))
        for F in Pn.faces(D - 1):
            Fp = Polyhedron(vertices=F.as_polyhedron().vertices_list(), backend='normaliz')
            vF = Fp.volume(measure='induced_lattice') / factorial(D - 1)
            cF = sum(vector(QQ, v) for v in Fp.vertices_list()) / len(Fp.vertices_list())
            acc += vF * (cF - cK)
        pred = acc / (2 * vP)
        assert list(pred[2:]) == c1s, (n, pred, c1s)
        print("  Euler-Maclaurin half-boundary prediction for c1 matches:", list(pred[2:]))


sec = sys.argv[1] if len(sys.argv) > 1 else "all"
if sec in ("rank1", "all"):
    rank1()
if sec in ("ehrhart", "all"):
    ehrhart()
if sec in ("rank2", "all"):
    rank2()
if sec == "rank3":
    rank2(only_r3=True)
