# referee_article3_checks.sage
#
# Changelog (reverse chronological):
#   2026-10-20  Created (Claude, referee of article 3 draft 4). Independent
#               recomputation of the numbers in sections sec-vertices,
#               sec-facets and sec-module-kk of
#               article/exterior-convex_article3_draft_4.org, written without
#               reading the authors' scripts. Lattice/volume/Ehrhart/centroid
#               numbers are in referee_article3_checks_lattice.* (separate).
#
# Run:  sage referee_article3_checks.sage  > runs/2026-10-20_article3-overnight-push/2026-10-20_referee-article3.txt

import itertools, random
from sage.all import *

def out(*a):
    print(*a, flush=True)

# ---------------------------------------------------------------- RA polytope
def summand_vertices(a, d, N):
    n = len(a); V = []
    for j in range(1, n+1):
        v = [0]*N
        for i in range(1, j+1):
            v[d+i-1] = a[i-1]
        V.append(v)
    return V

def RA(a, dd, lam=None):
    n = len(a); N = n + dd[-1]
    if lam is None: lam = [1]*len(dd)
    P = None
    for p, d in enumerate(dd):
        Q = Polyhedron(vertices=[[lam[p]*x for x in v] for v in summand_vertices(a, d, N)], base_ring=QQ)
        P = Q if P is None else P + Q
    return P

def extremal_tensor(a, dd):
    n = len(a); N = n + dd[-1]
    P = RA(a, dd)
    Vs = set(tuple(v) for v in P.vertices_list())
    SV = [summand_vertices(a, d, N) for d in dd]
    T = {}
    for jj in itertools.product(range(1, n+1), repeat=len(dd)):
        s = [sum(SV[p][jj[p]-1][c] for p in range(len(dd))) for c in range(N)]
        T[jj] = 1 if tuple(s) in Vs else 0
    return T, P

def vdesc_pred(a, dd, jj):
    """Theorem thm-vdesc (1)-(3)."""
    n = len(a); r = len(dd)
    m = [dd[p] + jj[p] for p in range(r)]
    for p in range(r-1):
        dp, dq = dd[p], dd[p+1]
        if dp == dq and m[p] != m[p+1]: return 0
        if m[p] > m[p+1]: return 0
        if m[p] < m[p+1] and dq < m[p] and m[p+1] <= dp + n:
            rho = [QQ(a[c-dp-1])/a[c-dq-1] for c in range(m[p]+1, m[p+1]+1)]
            if len(set(rho)) == 1: return 0
    return 1

def koz_pred(n, dd, jj):
    """Corollary cor-kozlov-vertices."""
    r = len(dd); m = [dd[p]+jj[p] for p in range(r)]
    for p in range(r-1):
        if m[p] > m[p+1]: return 0
        if dd[p] == dd[p+1] and m[p] != m[p+1]: return 0
        if m[p+1] == m[p]+1 and dd[p+1] < m[p] < dd[p]+n: return 0
    return 1

def rank2_lc_pred(a, g, i, j):
    """Corollary cor-rank2-lc: returns entry (1 = vertex)."""
    n = len(a); m = n - g; t = i - g
    if g == 0: return 1 if i == j else 0
    if g >= n: return 1
    sig = [QQ(a[k])/a[k-1] for k in range(1, n)]  # sig[0] = sigma_1
    if 1 <= t <= m and 1 <= j <= m:
        if j < t: return 0
        if j == t+1: return 0
        if j >= t+2:
            vals = [sig[u-1] for u in range(t+1, j+g)]   # sigma on [t+1, j+g-1]
            if len(set(vals)) == 1: return 0
    return 1

kozvec = lambda n: [binomial(n, k) for k in range(1, n+1)]
ones = lambda n: [1]*n

def matrix_of(T, n):
    return matrix(ZZ, n, n, lambda i, j: T[(i+1, j+1)])

out("=== V1 ex-plateau ===")
for a, name in [([1,2,4,4,4], "plateau"), (kozvec(5), "kozlov5"), (ones(5), "ones5")]:
    for g in [1, 2]:
        T, P = extremal_tensor(a, [0, g])
        M = matrix_of(T, 5)
        out(name, "g=", g, "nvertices", P.n_vertices(), "sum M", sum(M.list()))
        if g == 1: out(M)
T1, _ = extremal_tensor([1,2,4,4,4], [0,2]); T2, _ = extremal_tensor(kozvec(5), [0,2])
out("g=2 plateau == kozlov:", T1 == T2)
# the explicit functional of ex-plateau
phi = [1, 1, QQ(-1)/2, 0, QQ(3)/8, -1]
a = [1,2,4,4,4]
pre1 = [sum(a[i]*phi[i] for i in range(k)) for k in range(1, 6)]
pre2 = [sum(a[i]*phi[1+i] for i in range(k)) for k in range(1, 6)]
out("phi prefix summand1", pre1, "summand2", pre2)

out("=== V2 cor-rank2-lc and thm-vdesc vs brute force ===")
fams = []
for n in range(2, 7):
    fams += [kozvec(n), ones(n), [2**k for k in range(n)]]
fams += [[1,2,4,4,4], [1,2,4,4,4,4], [1,3,3,3,1], [1,2,2,2,2], [1,2,4,8,8,8], [3,3,1], [2,3,3,2,1], [1,1,1,1/2,1/4]]
bad = 0; cnt = 0
for a in fams:
    a = [QQ(x) for x in a]; n = len(a)
    # weak LC check
    assert all(a[i]**2 >= a[i-1]*a[i+1] for i in range(1, n-1)), a
    for g in range(0, n+1):
        T, P = extremal_tensor(a, [0, g])
        for i in range(1, n+1):
            for j in range(1, n+1):
                cnt += 1
                if T[(i, j)] != rank2_lc_pred(a, g, i, j): bad += 1; out("rank2 mismatch", a, g, i, j)
                if T[(i, j)] != vdesc_pred(a, [0, g], (i, j)): bad += 1; out("vdesc2 mismatch", a, g, i, j)
out("rank-two entries checked", cnt, "mismatches", bad)

bad = 0; cnt = 0
random.seed(int(1))
for a in [kozvec(3), kozvec(4), ones(4), [1,2,4,4,4], [1,2,2,2], [3,3,1], kozvec(5)]:
    a = [QQ(x) for x in a]; n = len(a)
    for r in [3]:
        for dd in itertools.combinations_with_replacement(range(0, n+1), r-1):
            dd = [0] + list(dd)
            if len(a) == 5 and dd[-1] > 3: continue
            T, P = extremal_tensor(a, dd)
            strict = all(a[i]**2 > a[i-1]*a[i+1] for i in range(1, n-1))
            for jj, val in T.items():
                cnt += 1
                if val != vdesc_pred(a, dd, jj): bad += 1; out("vdesc mismatch", a, dd, jj)
                if strict and val != koz_pred(n, dd, jj): bad += 1; out("koz mismatch", a, dd, jj)
                # pairwise reduction
                ok = all(vdesc_pred(a, [dd[p], dd[p+1]], (jj[p], jj[p+1])) for p in range(r-1))
out("rank-three tuples checked", cnt, "mismatches", bad)

out("=== V3 ex-rank3-vertices n=4 d=(0,1,2) ===")
T, P = extremal_tensor(kozvec(4), [0, 1, 2])
mlist = sorted(tuple(jj[p] + [0,1,2][p] for p in range(3)) for jj, v in T.items() if v)
out("n vertices", P.n_vertices(), "from tensor", len(mlist), "dim", P.dim(), "facets", P.n_facets())
out("m-triples", mlist)
out("j=(2,4,3):", T[(2,4,3)], " j=(2,2,3):", T[(2,2,3)], " j=(1,1,1):", T[(1,1,1)],
    " j=(4,4,4):", T[(4,4,4)], " j=(3,2,1):", T[(3,2,1)], " j=(2,1,1):", T[(2,1,1)])
paper_list = [(1,2,3),(1,2,4),(1,2,5),(1,2,6),(1,3,3),(1,3,5),(1,3,6),(1,4,4),(1,4,6),(1,5,5),(1,5,6),(2,2,3),(2,2,4),(2,2,5),(2,2,6),(2,4,4),(2,4,6),(2,5,5),(2,5,6),(3,3,3),(3,3,5),(3,3,6),(3,5,5),(3,5,6),(4,4,4),(4,4,6),(4,5,5),(4,5,6)]
out("paper list equals computed:", sorted(paper_list) == mlist, "missing", sorted(set(mlist)-set(paper_list)), "extra", sorted(set(paper_list)-set(mlist)))

out("=== V4 rem-logconvex ===")
a = [1,2,6,24]
T, P = extremal_tensor(a, [0,1,2])
T12, _ = extremal_tensor(a, [0,1]); T23, _ = extremal_tensor(a, [0,1])  # pair (2,3): shifts 1,2 ~ (0,1)
T13, _ = extremal_tensor(a, [0,2])
out("M[4,1,1]", T[(4,1,1)], "pair12", T12[(4,1)], "pair23", T23[(1,1)], "pair13", T13[(4,1)])

out("=== V5 vertex counts of examples ===")
for n, dd in [(3, [0,1]), (3, [0,2]), (4, [0,1]), (4,[0,0]), (4,[0,2])]:
    P = RA(kozvec(n), dd)
    out("RA(koz(%d);%s): dim %d, vertices %d, facets %d" % (n, dd, P.dim(), P.n_vertices(), P.n_facets()))
P = RA(kozvec(3), [0,1])
out("Koz(3;0,1) vertex list (x2,x3,x4) with x1=3 (f_k=x_k, f1=x1+1):", sorted(tuple(v[1:]) for v in P.vertices_list()))

out("=== V6 facets ===")
def ineqs_str(P):
    return [str(h) for h in P.inequality_generator()] + [str(e) for e in P.equation_generator()]
for n, d in [(4,1), (3,1)]:
    P = RA(kozvec(n), [0, d]); out("RA(koz(%d);0,%d) H-rep:" % (n, d)); [out("  ", s) for s in ineqs_str(P)]
# ex-hrep2-n4 explicit list
x = var(' '.join('x%d' % i for i in range(1, 6)))
X = vector(QQ, [0]*5)
def H(rows, eqs, N):
    return Polyhedron(ieqs=rows, eqns=eqs, base_ring=QQ)
# rows as [b, c1..cN] meaning b + c.x >= 0
rows = [[10,0,-1,0,0,0],[10,0,2,-3,0,0],[10,0,0,1,-4,0],[-4,0,1,0,0,0],[0,0,0,2,-3,0],[0,0,0,0,1,-4],[1,0,0,0,0,-1],[0,0,0,0,0,1]]
Q = H(rows, [[-4,1,0,0,0,0]], 5)
out("ex-hrep2-n4 list == RA(koz4;0,1):", Q == RA(kozvec(4), [0,1]), " facets", Q.n_facets())
# n=3 d=1 list (in x coords x1=3, f2=x2...)
rows = [[6,0,-1,0,0],[-3,0,1,0,0],[6,0,1,-3,0],[0,0,0,1,-3],[0,0,0,0,1],[1,0,0,0,-1]]
Q = H(rows, [[-3,1,0,0,0]], 4)
out("ex-hrep2 n=3 list == RA(koz3;0,1):", Q == RA(kozvec(3), [0,1]))
# ex-hrep-r3
rows = [[3,1,-1,0,0,0],[15,0,1,-3,0,0],[6,0,0,1,-3,0],[0,0,0,0,1,-3],[-3,0,1,0,0,0],[-3,0,0,1,0,0],[4,0,0,0,-1,0],[1,0,0,0,0,-1],[0,0,0,0,0,1]]
Q = H(rows, [[-3,1,0,0,0,0]], 5)
P = RA([3,3,1], [0,1,2])
out("ex-hrep-r3 list == RA:", Q == P, " dim", P.dim(), " vertices", P.n_vertices(), " facets", P.n_facets())
for rw in rows:
    F = Polyhedron(ieqs=[], eqns=[rw], base_ring=QQ).intersection(P)
    if F.dim() != P.dim()-1: out("  row not facet:", rw)

# Theta form general builder
def theta_system(a, dd, lam):
    n = len(a); r = len(dd); N = n + dd[-1]
    A = lambda s: QQ(a[s-1]) if 1 <= s <= n else QQ(0)
    def M(p, c):  # p 1-based; roof after p
        return sum(lam[q-1]*A(c-dd[q-1]) for q in range(p+1, r+1))
    rows = []
    def link(p, c):
        j = c - dd[p-1]
        # Theta(p;c) >= Theta(p;c+1): (x_c - M(p,c))/a_j - (x_{c+1}-M(p,c+1))/a_{j+1} >= 0
        row = [0]*(N+1)
        row[0] = -M(p, c)/A(j) + M(p, c+1)/A(j+1)
        row[c] += 1/A(j); row[c+1] -= 1/A(j+1)
        return row
    for c in range(1, n): rows.append(link(1, c))
    for p in range(2, r+1):
        for c in range(dd[p-1]+2, dd[p-1]+n): rows.append(link(p, c))
        row = [0]*(N+1); row[0] = -lam[p-1]*A(1); row[dd[p-1]+1] = 1; rows.append(row)
        e = dd[p-2] + n + 1
        row = [0]*(N+1); row[0] = M(p-1, e); row[e] = -1; rows.append(row)
    row = [0]*(N+1); row[N] = 1; rows.append(row)
    eq = [0]*(N+1); eq[0] = -lam[0]*A(1); eq[1] = 1
    return rows, [eq]

random.seed(int(7))
nbad = 0; ntest = 0
for a in [kozvec(3), kozvec(4), kozvec(5), ones(4), [1,2,4,4,4], [3,3,1]]:
    n = len(a)
    for r in [2, 3]:
        for gaps in itertools.product(range(1, n), repeat=r-1):
            dd = [0]
            for g in gaps: dd.append(dd[-1]+g)
            if n + dd[-1] > 11: continue
            lam = [QQ(int(random.randint(1, 4)))/int(random.randint(1, 3)) for _ in range(r)]
            rows, eqs = theta_system(a, dd, lam)
            Q = Polyhedron(ieqs=rows, eqns=eqs, base_ring=QQ)
            P = RA(a, dd, lam)
            ntest += 1
            strict = all(QQ(a[i])**2 > a[i-1]*a[i+1] for i in range(1, n-1))
            ok = (Q == P) and (not strict or P.n_facets() == r*n)
            if not ok: nbad += 1; out("theta FAIL", a, dd, lam, Q == P, P.n_facets())
out("Theta-form tests", ntest, "failures", nbad)

out("--- cor-facets-every-d (ties, wide gaps) and cor-ones-hrep counts ---")
for n in [3, 4]:
    for dd in [[0,0],[0,0,1],[0,1,1],[0,n],[0,n+1],[0,1,n+2],[0,0,2,2],[0,2,2,2+n]]:
        P = RA(kozvec(n), dd); s = len(set(dd))
        out("koz n=%d d=%s: facets %d, ns=%d" % (n, dd, P.n_facets(), n*s))
for n in range(2, 7):
    for d in range(1, n):
        P = RA(ones(n), [0, d]); m = n - d
        pred = n + d + 2 if m >= 2 else n + d + 1
        if P.n_facets() != pred: out("ones FAIL", n, d, P.n_facets(), pred)
out("cor-ones-hrep counts checked n<=6")

out("--- rem-hdesc-hypotheses: a=(1,2,6,24) ---")
a = [1,2,6,24]
def hrep2_system(a, d):
    n = len(a); N = n + d; m = n - d
    A = lambda s: QQ(a[s-1]) if 1 <= s <= n else QQ(0)
    rows = {}
    for j in range(1, n):
        t = j - d; cj = A(t+1)/A(j+1) - A(t)/A(j)
        row = [0]*(N+1); row[0] = cj; row[j] += 1/A(j); row[j+1] -= 1/A(j+1); rows[("Ch1", j)] = row
        row = [0]*(N+1); row[d+j] += 1/A(j); row[d+j+1] -= 1/A(j+1); rows[("Ch2", j)] = row
    row = [0]*(N+1); row[0] = -A(1); row[d+1] = 1; rows["C"] = row
    row = [0]*(N+1); row[0] = A(m+1); row[n+1] = -1; rows["D"] = row
    row = [0]*(N+1); row[N] = 1; rows["F"] = row
    eq = [0]*(N+1); eq[0] = -A(1); eq[1] = 1
    return rows, [eq]
for d in [1, 2]:
    P = RA(a, [0, d])
    rows, eqs = hrep2_system(a, d)
    viol = [k for k, rw in rows.items() if any(rw[0] + sum(rw[i+1]*v[i] for i in range(len(v))) < 0 for v in P.vertices_list())]
    trows, teqs = theta_system(a, [0, d], [1, 1])
    tviol = sum(1 for rw in trows if any(rw[0] + sum(rw[i+1]*v[i] for i in range(len(v))) < 0 for v in P.vertices_list()))
    out("d=%d: hrep2 rows violated by RA vertices: %s; Theta rows violated: %d" % (d, viol, tviol))

out("--- n=3 d=(0,1): which summand-inequality directions are facets ---")
P = RA(kozvec(3), [0,1])
out([str(h) for h in P.inequality_generator()])

out("=== V7 rem-permutohedron: 2-faces of RA(koz4;0,1) ===")
P = RA(kozvec(4), [0,1])
best = 0
for F in P.faces(2):
    Fp = F.as_polyhedron()
    dirs = []
    for e in Fp.faces(1):
        vs = e.as_polyhedron().vertices_list(); w = vector(QQ, vs[1]) - vector(QQ, vs[0])
        w = w / max(abs(t) for t in w if t != 0) * (1 if [t for t in w if t != 0][0] > 0 else -1)
        if w not in dirs: dirs.append(w)
    best = max(best, len(dirs))
out("max number of pairwise non-parallel edge directions on a 2-face:", best)
# all-ones sanity: generalized permutohedron, expect <= 3
P = RA(ones(4), [0,1,2]); b1 = 0
for F in P.faces(2):
    dirs = []
    for e in F.as_polyhedron().faces(1):
        vs = e.as_polyhedron().vertices_list(); w = vector(QQ, vs[1]) - vector(QQ, vs[0])
        w = w / max(abs(t) for t in w if t != 0) * (1 if [t for t in w if t != 0][0] > 0 else -1)
        if w not in dirs: dirs.append(w)
    b1 = max(b1, len(dirs))
out("all-ones RA(1;0,1,2) max 2-face directions:", b1)

# ================================================================ module KK
out("=== V9 module Kruskal-Katona ===")
from itertools import combinations
def lexsets(n, k):
    S = [frozenset(c) for c in combinations(range(1, n+1), k)]
    # lex on E: sigma > tau iff min(sym diff) in sigma; "first" = largest; combinations() already gives
    # 12,13,14,23,... which is decreasing in this order
    return S
def upper(A, n):
    return set(S | {x} for S in A for x in range(1, n+1) if x not in S)
def omega(n, k, t):
    if k < 0 or k > n: return 0
    return len(upper(lexsets(n, k)[:t], n))
def omega_rec(n, k, t, memo={}):
    key = (n, k, t)
    if key in memo: return memo[key]
    if n == 0: v = 0
    elif k == 0: v = 0 if t == 0 else n   # t in {0,1}
    else:
        al = binomial(n-1, k-1); be = binomial(n-1, k)
        if t <= al: v = omega_rec(n-1, k-1, t)
        else: v = be + omega_rec(n-1, k, t-al)
    memo[key] = v; return v
bad = 0
for n in range(0, 8):
    for k in range(0, n+1):
        for t in range(0, binomial(n, k)+1):
            if omega(n, k, t) != omega_rec(n, k, t): bad += 1
out("lex shadow recursion vs actual, n<=7, mismatches:", bad)
def macaulay_up(a, k):
    # a^{(k)} = sum C(a_l, l+1), k-th Macaulay representation
    if a == 0: return 0
    res = 0; l = k
    while a > 0 and l >= 1:
        al = l
        while binomial(al+1, l) <= a: al += 1
        res += binomial(al, l+1); a -= binomial(al, l); l -= 1
    return res
bad = 0
for n in range(1, 9):
    for k in range(1, n+1):
        for a_ in range(0, binomial(n, k)):
            if binomial(n, k+1) - omega_rec(n, k, binomial(n, k)-a_) != macaulay_up(a_, k): bad += 1
out("thm-kk-rank1(b) identity n<=8 mismatches:", bad)
out("2^(2),3^(2),4^(2),5^(2) =", [macaulay_up(v, 2) for v in [2,3,4,5]])
out("rem-blocks: w4(2,1)=%d w4(1,3)=%d w4(1,4)=%d w4(2,4)=%d" % (omega(4,2,1), omega(4,1,3), omega(4,1,4), omega(4,2,4)))
# Prop PQ
bad = 0
for n in range(0, 10):
    for k in range(0, n+1):
        for kp in range(0, k+1):
            Ck, Ckp = binomial(n, k), binomial(n, kp)
            for x_ in range(0, Ck+1):
                for y_ in range(0, Ckp+1):
                    if x_ + y_ <= Ck and omega_rec(n, k, x_+y_) > omega_rec(n, k, x_) + omega_rec(n, kp, y_): bad += 1
                    if x_ + y_ >= Ck and omega_rec(n, k, x_) + omega_rec(n, kp, y_) < binomial(n, k+1) + omega_rec(n, kp, x_+y_-Ck): bad += 1
out("Prop PQ n<=9 violations:", bad)

# Def B and thm-module-kk / thm-ac42 against brute force achievable sets of MONOMIAL quotients
def dimF(n, ds, j): return sum(binomial(n, j-d) for d in ds)
def Bfun(n, ds, h, j):
    r = len(ds)
    if h == dimF(n, ds, j): return dimF(n, ds, j+1)
    T = lambda Nn: sum(binomial(n, j-ds[i-1]) for i in range(Nn+1, r+1))
    for Nn in range(1, r+1):
        if T(Nn) <= h < T(Nn-1):
            a_ = h - T(Nn); kN = j - ds[Nn-1]
            return sum(binomial(n, j+1-ds[i-1]) for i in range(Nn+1, r+1)) + macaulay_up(a_, kN)
    raise ValueError
def fvecs_orderideals(n):
    # f-vectors (f_0..f_n) of order ideals of 2^[n] incl. empty ideal; via all complexes (small n)
    subsets = [frozenset(c) for k in range(n+1) for c in combinations(range(1, n+1), k)]
    res = set()
    # enumerate antichains -> generate down-closures; brute force via recursion on subsets
    def rec(idx, chosen):
        pass
    # simpler: enumerate all down-closed families by brute force for n<=3 (2^8 families)
    for mask in range(1 << len(subsets)):
        fam = [subsets[i] for i in range(len(subsets)) if mask >> i & 1]
        fs = set(fam)
        if all(all(S - {x} in fs for x in S) for S in fam):
            res.add(tuple(sum(1 for S in fam if len(S) == k) for k in range(n+1)))
    return res
OI = {n: fvecs_orderideals(n) for n in range(1, 4)}
def achievable(n, ds):
    lo = min(ds); hi = max(ds) + n
    res = set()
    for combo in itertools.product(sorted(OI[n]), repeat=len(ds)):
        h = [0]*(hi - lo + 1)
        for f, d in zip(combo, ds):
            for k in range(n+1): h[d - lo + k] += f[k]
        res.add(tuple(h))
    return res, lo, hi
def Bcond(n, ds, h, lo, hi):
    hh = lambda j: h[j-lo] if lo <= j <= hi else 0
    return all(hh(j+1) <= Bfun(n, ds, hh(j), j) for j in range(lo-1, hi))
tot = 0; bad = 0
for n in [1, 2, 3]:
    for ds in [[0],[0,0],[0,1],[0,2],[0,0,0],[0,0,1],[0,1,1],[-1,0],[-2,0,1],[0,3],[0,1,2]]:
        if n == 3 and len(ds) == 3 and ds not in ([0,0,1],[0,1,2]): continue
        ach, lo, hi = achievable(n, ds)
        # candidate sequences: all with 0 <= h_j <= dim F_j
        ranges = [range(0, dimF(n, ds, j)+1) for j in range(lo, hi+1)]
        cand = 0
        for h in itertools.product(*ranges):
            cand += 1
            b = Bcond(n, ds, h, lo, hi)
            if b != (h in ach): bad += 1
        tot += cand
out("thm-ac42 (monomial achievable sets vs B-condition), sequences tested", tot, "mismatches", bad)
# ex-ac-smallest
ach, lo, hi = achievable(1, [0,0]); out("n=1,d=(0,0) achievable:", sorted(ach), "count", len(ach))
out("B(4,2) n3 d01:", Bfun(3,[0,1],4,2), " B(3,3):", Bfun(3,[0,1],3,3), " B(6,2) n4 d01:", Bfun(4,[0,1],6,2))
# Amata-Crupi printed clause vs corrected
out("printed clause n*r0+r1 at (1,2): allows h1<=", 1*2+0, "; corrected n*h0+r1 =", 1*1+0)

# cor-initial random checks
bad = 0
for n in range(1, 5):
    for ds in [[0,0],[0,0,1],[0,1,1,1],[-1,0,0],[0,0,0,2],[1,1,2]]:
        lo = min(ds); hi = max(ds)+n
        for s in range(lo, hi+1):
            r0 = ds.count(s); r1 = ds.count(s+1)
            if r0 == 0: continue
            if Bfun(n, ds, 0, s-1) != r0: bad += 1; out("B(0,s-1) fail", n, ds, s)
            for hs in range(1, r0+1):
                if hs <= dimF(n, ds, s) and Bfun(n, ds, hs, s) != n*hs + r1: bad += 1; out("B(hs,s) fail", n, ds, s, hs, Bfun(n,ds,hs,s), n*hs+r1)
out("cor-initial checks mismatches:", bad)

# L_4 \ S_4
S4 = set(f for f in fvecs_orderideals(4) if f[0] == 1 and f[1] == 4) if False else None
out("done")

# ---- appended 2026-10-20: weak-LC facet count = number of distinct normal classes (thm-theta last clause)
out("=== V8b thm-theta weak LC: facets vs distinct normal classes ===")
def normal_class(row, N):
    v = vector(QQ, row[2:])   # drop constant and e_1 coefficient (mod e_1)
    nz = [t for t in v if t != 0]
    return tuple(v / abs(nz[0]))
bad = 0
for a in [[1,2,4,4,4], [1,1,1,1], [1,2,2,2,2], [2,2,2,1], [1,3,3,3,1]]:
    n = len(a)
    for dd in [[0,1],[0,2],[0,1,2],[0,1,3],[0,2,3]]:
        if any(dd[i+1]-dd[i] > n-1 for i in range(len(dd)-1)): continue
        rows, eqs = theta_system(a, dd, [1]*len(dd))
        P = RA(a, dd)
        classes = set(normal_class(rw, n+dd[-1]) for rw in rows)
        if P.n_facets() != len(classes): bad += 1; out("  mismatch", a, dd, P.n_facets(), len(classes))
out("weak-LC facet-class checks mismatches:", bad)
# thm-beta-lattice example n=4
x = [1,4,6,1,0]; n = 4
beta2 = binomial(n,2) + binomial(n,2)*QQ(x[3])/n - x[2]
out("beta(1,4,6,1,0)_2 =", beta2)
