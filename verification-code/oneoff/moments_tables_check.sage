# moments_tables_check.sage -- independent check of the numbers in the two moment tables of
# Part III, sec-moments (tab:concentration, tab:rank-r-variance), against the run log
# runs/2026-10-20_article3-overnight-push/2026-10-20_centroids_moments.txt.
#
# Changelog (reverse chronological):
# 2026-11-14 - Claude Opus 5.5 (jts-pc), for Jan's sweep item 7 (tables in sec-moments): created.
#   Deliberately shares no code with centroids_moments.{py,sage}:
#   * S_n from all simplicial complexes on [n] that use every vertex (n <= 5), not from the
#     Kruskal-Katona bound;
#   * FF(n; d) as a plain sumset of shifted copies of that S_n;
#   * continuous moments of Koz(n; d) by a pulling triangulation over Sage's face lattice
#     (cone from the first vertex over the facets missing it, recursively), not by
#     Polyhedron.triangulate(); simplex weights |det| in a coordinate chart chosen from the
#     LAST pivots rather than the first;
#   * product-regime and equal-shift cases also by the closed forms (Prop. prop-pushforward(2),
#     Prop. prop-second-moments(2)), as a check of the triangulation code;
#   * rank one, n <= 8: sd of the middle LYM coordinate and Var(J) by enumerating S_n (all
#     sequences under the Kruskal-Katona bound) and the lattice points of Koz(n) (all integer
#     LYM chains), against the chain DP of the log.
#
# Run:  cd code/oneoff && sage moments_tables_check.sage   (about a minute)
from itertools import combinations
from math import comb
import sys

# ------------------------------------------------------------------ S_n from complexes
def complexes_fvectors(n):
    """f-vectors (f_0..f_n), f_k = number of faces with k elements, of all simplicial
    complexes on [n] containing every vertex. Down-sets built subset by subset in order of
    size, a subset being allowed only when all its codimension-one subsets are present."""
    subs = [frozenset(c) for k in range(2, n + 1) for c in combinations(range(n), k)]
    out = set()
    def rec(i, present, f):
        if i == len(subs):
            out.add(tuple(f)); return
        s = subs[i]
        rec(i + 1, present, f)                       # exclude s
        if all((s - {x}) in present for x in s):     # include s if its boundary is there
            present.add(s); f[len(s)] += 1
            rec(i + 1, present, f)
            present.discard(s); f[len(s)] -= 1
    base = set(frozenset([v]) for v in range(n))
    rec(0, base, [1, n] + [0] * (n - 1))
    return sorted(out)

# ------------------------------------------------------------------ finite moments
def fin_cov_diag(points):
    m = len(points); A = len(points[0])
    mean = [QQ(sum(p[k] for p in points)) / m for k in range(A)]
    var = [QQ(sum(p[k] ** 2 for p in points)) / m - mean[k] ** 2 for k in range(A)]
    return mean, var

def sumset(n, ds, Sn):
    N = n + ds[-1]
    cur = {tuple([0] * (N + 1))}
    for d in ds:
        nxt = set()
        for x in cur:
            for s in Sn:
                y = list(x)
                for j, v in enumerate(s):
                    y[j + d] += v
                nxt.add(tuple(y))
        cur = nxt
    return sorted(cur)

def Hfree(n, ds):
    N = n + ds[-1]
    return [sum(comb(n, k - d) for d in ds if 0 <= k - d <= n) for k in range(N + 1)]

# ------------------------------------------------------------------ continuous moments
def koz_poly(n, ds):
    N = n + ds[-1]
    verts1 = [[1] + [comb(n, k) if k <= j else 0 for k in range(1, n + 1)] for j in range(1, n + 1)]
    P = None
    for d in ds:
        Q = Polyhedron(vertices=[[0] * d + v + [0] * (N - n - d) for v in verts1], base_ring=QQ)
        P = Q if P is None else P + Q
    return P

def pulling_simplices(P):
    """Simplices (as lists of vertex tuples) of the pulling triangulation of P."""
    memo = {}
    def rec(F):
        key = frozenset(tuple(v) for v in F.vertices_list())
        if key in memo:
            return memo[key]
        D = F.dim()
        if D == 0:
            res = [[tuple(F.vertices_list()[0])]]
        else:
            v0 = tuple(F.vertices_list()[0])
            res = []
            for G in F.faces(D - 1):
                Gp = G.as_polyhedron()
                if v0 in set(tuple(v) for v in Gp.vertices_list()):
                    continue
                for S in rec(Gp):
                    res.append([v0] + S)
        memo[key] = res
        return res
    return rec(P)

def cont_cov_diag(P):
    V = [vector(QQ, v) for v in P.vertices_list()]
    A = len(V[0]); D = P.dim()
    E = matrix(QQ, [v - V[0] for v in V[1:]])
    # chart: D coordinates, chosen as pivots of the REVERSED column order
    rev = E.matrix_from_columns(list(range(A - 1, -1, -1)))
    cols = sorted(A - 1 - c for c in rev.pivots())
    assert len(cols) == D
    tot = QQ(0); m1 = vector(QQ, [0] * A); m2 = vector(QQ, [0] * A)
    for S in pulling_simplices(P):
        S = [vector(QQ, v) for v in S]
        w = abs(matrix(QQ, [[(v - S[0])[c] for c in cols] for v in S[1:]]).det())
        s = sum(S)
        m1 += w * s / (D + 1)
        m2 += w * vector(QQ, [(sum(v[k] ** 2 for v in S) + s[k] ** 2) for k in range(A)]) / ((D + 1) * (D + 2))
        tot += w
    mean = m1 / tot
    return D, mean, [m2[k] / tot - mean[k] ** 2 for k in range(A)]

# ------------------------------------------------------------------ closed forms
def koz1_var_x(n):
    """Var(x_k) on Koz(n), k = 0..n, from Prop. prop-second-moments(2)."""
    return [QQ(0), QQ(0)] + [QQ((k - 1) * (n - k + 1)) / (n ** 2 * (n + 1)) * comb(n, k) ** 2 for k in range(2, n + 1)]

# ------------------------------------------------------------------ rank r >= 2 table
LOG = {  # total nu-variance from the 2026-10-20 log: FF, S-indep, Koz
 (3, (0, 0)): (0.2066, 0.1556, 0.1111), (3, (0, 1)): (0.3146, 0.2928, 0.1332), (3, (0, 2)): (0.4061, 0.4061, 0.1458),
 (4, (0, 0)): (0.1967, 0.1382, 0.1250), (4, (0, 1)): (0.2835, 0.2273, 0.1596), (4, (0, 2)): (0.3555, 0.3538, 0.1806),
 (4, (0, 3)): (0.4538, 0.4538, 0.1960), (5, (0, 0)): (0.1732, 0.1153, 0.1333), (5, (0, 1)): (0.2397, 0.1706, 0.1781),
 (5, (0, 2)): (0.2990, 0.2812, 0.2079), (5, (0, 3)): (0.3778, 0.3801, 0.2225), (5, (0, 4)): (0.4319, 0.4319, 0.2285),
 (3, (0, 0, 0)): (0.1739, 0.1037, 0.1111), (3, (0, 0, 1)): (0.3282, 0.2608, 0.1506), (3, (0, 1, 1)): (0.2101, 0.1556, 0.1209),
 (3, (0, 1, 2)): (0.3420, 0.3138, 0.1524), (3, (0, 2, 4)): (0.5011, 0.5011, 0.1806), (3, (0, 1, 3)): (0.4243, 0.4197, 0.1646),
 (4, (0, 0, 0)): (0.1722, 0.0921, 0.1250), (4, (0, 1, 2)): (0.3205, 0.2400, 0.1900), (4, (0, 3, 6)): (0.6312, 0.6312, 0.2670),
}

def rankr():
    print("== rank r >= 2: total nu-variance (trace of the covariance in the coordinates nu_k = x_k / dim F_k)")
    Scache = {n: complexes_fvectors(n) for n in (3, 4, 5)}
    for n, S in Scache.items():
        print("  |S_%d| from complexes = %d" % (n, len(S)))
    ok_all = True
    for (n, ds), logv in LOG.items():
        Sn = Scache[n]; H = Hfree(n, ds); N = len(H) - 1
        FF = sumset(n, ds, Sn)
        _, vFF = fin_cov_diag(FF)
        _, vS = fin_cov_diag(Sn)
        vInd = [sum((vS[k - d] if 0 <= k - d <= n else 0) for d in ds) for k in range(N + 1)]
        tv = lambda v: sum(QQ(v[k]) / H[k] ** 2 for k in range(N + 1))
        tFF, tInd = tv(vFF), tv(vInd)
        # continuous: closed form where available, pulling triangulation where feasible
        gaps = [b - a for a, b in zip(ds, ds[1:])]
        closed = None
        if all(g == 0 for g in gaps):
            # nu = x/(r C(n,k)) = mu on the dilate r Koz(n): the rank-one total, dilation-invariant
            closed = sum(QQ((k - 1) * (n - k + 1)) / (n ** 2 * (n + 1)) for k in range(2, n + 1))
        elif all(g >= n - 1 for g in gaps):
            v1 = koz1_var_x(n)
            closed = tv([sum((v1[k - d] if 0 <= k - d <= n else 0) for d in ds) for k in range(N + 1)])
        tri = None
        P = koz_poly(n, ds)
        if P.dim() <= 7:
            D, _, vK = cont_cov_diag(P)
            tri = tv(vK)
        tK = tri if tri is not None else closed
        agree = (closed is None or tri is None or closed == tri)
        match = all(abs(float(a) - b) < 6e-5 for a, b in zip((tFF, tInd, tK), logv))
        ok_all &= agree and match and tFF > tK
        print("  n=%d d=%-10s dim=%d |FF|=%5d  FF %.4f  indep %.4f  Koz %.4f  %s%s  log-match=%s  FF>Koz=%s"
              % (n, str(ds), P.dim(), len(FF), float(tFF), float(tInd), float(tK),
                 "[tri]" if tri is not None else "", "[closed%s]" % ("=tri" if (closed is not None and tri is not None and agree) else "") if closed is not None else "",
                 match, tFF > tK))
    print("  ALL OK:", ok_all)

# ------------------------------------------------------------------ rank one, n <= 8
def kk_bound(m, k):
    if m == 0:
        return 0
    tot = 0; level = k
    while m > 0 and level >= 1:
        a = level
        while comb(a + 1, level) <= m:
            a += 1
        tot += comb(a, level + 1); m -= comb(a, level); level -= 1
    return tot

def enum_chains(n, bound):
    """All (f_2..f_n) with f_1 = n and 0 <= f_{k+1} <= bound(f_k, k)."""
    out = []
    def rec(k, prev, acc):
        if k > n:
            out.append(tuple(acc)); return
        for v in range(bound(prev, k - 1) + 1):
            acc.append(v); rec(k + 1, v, acc); acc.pop()
    rec(2, n, [])
    return out

LOG1 = {  # (n, set): (sd of mu_{n/2}, Var(J)) from the 2026-10-20 log
 (4, 'S'): (0.31458, 0.771457), (4, 'L'): (0.29768, 0.799149), (6, 'S'): (0.28962, 1.150909), (6, 'L'): (0.23253, 1.815091),
 (8, 'S'): (0.23436, 1.723272), (8, 'L'): (0.19367, 3.643545)}

def rank1():
    print("== rank one, by enumeration: sd of the middle LYM coordinate mu_{n/2} and Var(J)")
    ok = True
    for n in (4, 6, 8):
        for name, bound in (('S', lambda m, k: kk_bound(m, k)), ('L', lambda m, k, n=n: (m * (n - k)) // (k + 1))):
            pts = enum_chains(n, bound)
            m = n // 2
            mu = [[QQ(p[k - 2]) / comb(n, k) for k in range(2, n + 1)] for p in pts]
            cnt = len(pts)
            mk = [x[m - 2] for x in mu]
            mean = sum(mk) / cnt; var = sum(x * x for x in mk) / cnt - mean ** 2
            sd = float(var) ** 0.5
            # J: P(J = j) = E[lambda_j], lambda_j = mu_j - mu_{j+1} (mu_1 = 1, mu_{n+1} = 0)
            Emu = [QQ(1)] + [sum(x[k] for x in mu) / cnt for k in range(n - 1)] + [QQ(0)]
            lam = [Emu[j - 1] - Emu[j] for j in range(1, n + 1)]
            EJ = sum(j * lam[j - 1] for j in range(1, n + 1)); EJ2 = sum(j * j * lam[j - 1] for j in range(1, n + 1))
            VJ = EJ2 - EJ ** 2
            lsd, lVJ = LOG1[(n, name)]
            good = abs(sd - lsd) < 6e-6 and abs(float(VJ) - lVJ) < 6e-7
            ok &= good
            print("  n=%d %s count=%d sd(mu_%d)=%.5f (log %.5f)  Var(J)=%.6f (log %.6f)  %s"
                  % (n, name, cnt, m, sd, lsd, float(VJ), lVJ, good))
    print("  ALL OK:", ok)

# ------------------------------------------------------------------ the identities of prop-pushforward(2)
def identities():
    """Outside the product regime, which identities of Prop. prop-pushforward(2) hold?
    Centroids exactly; second moments compared through the diagonal (differing diagonals mean
    differing matrices; equal diagonals are reported as such)."""
    print("== prop-pushforward(2) outside the product regime: does each identity hold? (True = holds)")
    Scache = {n: complexes_fvectors(n) for n in (3, 4, 5)}
    L1 = {}
    for n in (3, 4, 5):
        pts = [tuple(p) for p in koz_poly(n, (0,)).integral_points()]
        L1[n] = fin_cov_diag(pts)
    cnt = 0
    for (n, ds) in LOG:
        gaps = [b - a for a, b in zip(ds, ds[1:])]
        if all(g >= n - 1 for g in gaps):
            continue
        cnt += 1
        Sn = Scache[n]; N = n + ds[-1]
        sh = lambda v: [sum((v[k - d] if 0 <= k - d <= n else 0) for d in ds) for k in range(N + 1)]
        mFF, vFF = fin_cov_diag(sumset(n, ds, Sn)); mS, vS = fin_cov_diag(Sn)
        P = koz_poly(n, ds)
        _, mK, vK = cont_cov_diag(P)
        _, mK1, vK1 = cont_cov_diag(koz_poly(n, (0,)))
        row = "  n=%d d=%-10s FF centroid %-5s FF var-diag %-5s Koz centroid %-5s Koz var-diag %-5s" % (
            n, str(ds), list(mFF) == sh(mS), list(vFF) == sh(vS), list(mK) == sh(list(mK1)), list(vK) == sh(list(vK1)))
        if (n, ds) != (5, (0, 3)):        # the one case with too many lattice points to list here
            pts = [tuple(p) for p in P.integral_points()]
            mL, vL = fin_cov_diag(pts)
            row += " lattice centroid %-5s lattice var-diag %-5s (%d pts)" % (list(mL) == sh(L1[n][0]), list(vL) == sh(L1[n][1]), len(pts))
        else:
            row += " lattice: not computed"
        print(row)
    print("  cases:", cnt)

rank1()
rankr()
identities()
