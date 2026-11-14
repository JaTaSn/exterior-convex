# kozlov_pairwise_hside_check.sage
#
# Changelog (reverse chronological):
#   2026-10-20  Added mode 'extra' (rank 5; n = 7).
#   2026-10-20  Created (Claude-Code, overnight article-3 push, H-side route to
#               the rank-r pairwise reduction; item E of
#               working-notes/vrep-hrep-state-of-knowledge.org).  Companion
#               note: working-notes/kozlov-pairwise-reduction-hside-2026-10-20.org.
#
# What it checks, for many (a, n, d) and EVERY index tuple j (exact arithmetic,
# brute force = Sage Polyhedron vertex list of the n^r vertex sums, ppl backend):
#
#   T0  every Theta-normal u has offset (Theta-form) = sum_q h(u, P_q)
#       (validity + support-tightness of part 1 of the facet note).
#   T1  TIGHTNESS LEMMA: u tight at x(j) [computed from argmax sets] <=> the
#       closed-form condition in terms of the ends m(q) = d(q) + j(q):
#         link (p,c):  m(p) != c,  m(q) <= c-1 (q<p),  m(q) >= c+1 (q>p)
#         C_p:         m(q) <= d(p)            (q<p)
#         D_p:         m(q) >= d(p-1)+n+1      (q>=p)
#         F:           m(r) <= N-1
#       (strict LC: equality; weak LC: formula => tight only, recorded).
#   T2  RANK CRITERION: rank(tight normals + e1) = N  <=>  brute-force vertex.
#   T3  COMPONENT FORMULA: rank = N - #(components of the tight-link graph on
#       [1,N] with no anchor, no e1, and no pair of independent co-supported
#       links).
#   T4  FINAL V-DESCRIPTION (any d, ties and wide gaps included): brute-force
#       vertex <=> for every consecutive pair p:
#         tie d(p)=d(p+1):   j(p) = j(p+1)
#         else, with O = [d(p+1)+1, d(p)+n]:
#            NOT( m(p), m(p+1) in O  and  (m(p+1) < m(p) or m(p+1) = m(p)+1) )
#       and also <=> every consecutive pair is a brute-force vertex of its own
#       rank-two subsum (the pairwise reduction itself).
#   T5  CERTIFICATE: for every vertex, phi = sum of the tight normals exposes
#       x(j) uniquely on every summand (checked by evaluating phi on all
#       summand vertices).
#
# Usage: sage kozlov_pairwise_hside_check.sage [quick|full|extra]
#   extra = r = 5 for n = 3, 4 and r = 3 for n = 7 (Kozlov and tent only).

import itertools, sys, random
from sage.all import QQ, vector, matrix, Polyhedron, binomial

MODE = sys.argv[1] if len(sys.argv) > 1 else "quick"

# ---------------------------------------------------------------- leg vectors
def kozlov(n): return [QQ(binomial(n, i)) for i in range(1, n+1)]
def tent(n):   return [QQ(i*(n+1-i)) for i in range(1, n+1)]
def pow2(n):   return [QQ(2)**(i*(n-i)) for i in range(1, n+1)]
def ones(n):   return [QQ(1)]*n
def geom(n):   return [QQ(3)**i for i in range(1, n+1)]
def logconvex(n): return [QQ(factorial(i)) for i in range(1, n+1)]
def rand_slc(n, seed):
    R = random.Random(int(seed))
    sl = sorted([QQ(R.randint(1, 60))/R.randint(1, 12) for _ in range(n-1)], reverse=True)
    # force strictness
    for i in range(1, len(sl)):
        if sl[i] >= sl[i-1]: sl[i] = sl[i-1]*QQ(9)/10
    a = [QQ(R.randint(1, 5))]
    for s in sl: a.append(a[-1]*s)
    return a
def weak_tie(n):
    # slopes strictly decreasing except one tie in the middle
    sl = [QQ(n-i) for i in range(1, n)]
    if n >= 4: sl[1] = sl[0]
    a = [QQ(1)]
    for s in sl: a.append(a[-1]*s)
    return a

def sigma_class(a):
    s = [a[i+1]/a[i] for i in range(len(a)-1)]
    if all(s[i] > s[i+1] for i in range(len(s)-1)): return "strictLC"
    if all(s[i] == s[i+1] for i in range(len(s)-1)): return "geometric"
    if all(s[i] >= s[i+1] for i in range(len(s)-1)): return "weakLC"
    if all(s[i] < s[i+1] for i in range(len(s)-1)): return "strictLConvex"
    return "other"

# ---------------------------------------------------------------- geometry
def summand_vertices(a, d, N):
    n = len(a); V = []
    for k in range(1, n+1):
        x = [QQ(0)]*N
        for i in range(1, k+1): x[d+i-1] = a[i-1]
        V.append(vector(QQ, x))
    return V

def theta_normals(a, ds, N):
    """Theta-form normals with Theta offsets, for distinct shifts, gaps in [1,n-1].
    Returns list of (name, u, beta, kind, data) with constraint u.x <= beta.
    1-based coordinates in 'data'; vectors 0-based."""
    n = len(a); r = len(ds); out = []
    def e(c, s=1):
        v = [QQ(0)]*N; v[c-1] = QQ(s); return vector(QQ, v)
    def roof(p, c):  # M(p;c), p 1-based
        return sum((a[c-ds[q]-1] for q in range(p, r) if 1 <= c-ds[q] <= n), QQ(0))
    for p in range(1, r+1):
        dp = ds[p-1]
        cs = range(dp+1, dp+n) if p == 1 else range(dp+2, dp+n)
        for c in cs:
            j = c - dp
            u = e(c+1)/a[j] - e(c)/a[j-1]
            beta = roof(p, c+1)/a[j] - roof(p, c)/a[j-1]
            out.append(("L(%d,%d)" % (p, c), u, beta, "link", (p, c)))
    for p in range(2, r+1):
        b = ds[p-1]+1
        out.append(("C%d" % p, -e(b), -a[0], "C", (p, b)))
        c = ds[p-2]+n+1
        out.append(("D%d" % p, e(c), roof(p-1, c), "D", (p, c)))
    out.append(("F", -e(N), QQ(0), "F", (N,)))
    return out

def argmax_set(u, V):
    vals = [u.dot_product(v) for v in V]; M = max(vals)
    return set(k+1 for k, x in enumerate(vals) if x == M), M

def formula_tight(kind, data, m, ds, n, N):
    r = len(ds)
    if kind == "link":
        p, c = data
        return (m[p-1] != c and all(m[q] <= c-1 for q in range(p-1))
                and all(m[q] >= c+1 for q in range(p, r)))
    if kind == "C":
        p, b = data
        return all(m[q] <= ds[p-1] for q in range(p-1))
    if kind == "D":
        p, c = data
        return all(m[q] >= c for q in range(p-1, r))
    if kind == "F":
        return m[r-1] <= N-1

def components_deficit(tight, N):
    """Combinatorial rank prediction. tight: list of (kind,data,u)."""
    anchored = set([1]); edges = {}
    for kind, data, u in tight:
        supp = [i+1 for i in range(N) if u[i] != 0]
        if len(supp) == 1: anchored.add(supp[0])
        else:
            c = supp[0]; assert supp == [c, c+1]
            edges.setdefault(c, []).append(u)
    doubled = set(c for c, L in edges.items() if matrix(QQ, L).rank() == 2)
    # components of the path graph using edges
    deficit = 0; c = 1
    while c <= N:
        start = c
        while c in edges: c += 1
        comp = range(start, c+1)
        ok = any(x in anchored for x in comp) or any(x in doubled for x in range(start, c))
        if not ok: deficit += 1
        c += 1
    return deficit

def vertex_sum(V, j):
    return sum((V[p][j[p]-1] for p in range(len(j))), vector(QQ, [0]*len(V[0][0])))

def brute_vertices(a, ds):
    n = len(a); N = n + max(ds)
    V = [summand_vertices(a, d, N) for d in ds]
    pts = {j: vertex_sum(V, j) for j in itertools.product(range(1, n+1), repeat=len(ds))}
    P = Polyhedron(vertices=[list(x) for x in set(tuple(x) for x in pts.values())],
                   base_ring=QQ, backend='ppl')
    VS = set(tuple(v) for v in P.vertices_list())
    return {j: (tuple(x) in VS) for j, x in pts.items()}, V, N

_pair_cache = {}
def pair_vertex(a, d1, d2, i, j):
    key = (tuple(a), d2-d1)
    if key not in _pair_cache:
        _pair_cache[key] = brute_vertices(a, [0, d2-d1])[0]
    return _pair_cache[key][(i, j)]

def explicit_pair_ok(n, d1, d2, i, j):
    if d1 == d2: return i == j
    m1, m2 = d1+i, d2+j
    lo, hi = d2+1, d1+n
    inO = lo <= m1 <= hi and lo <= m2 <= hi
    return not (inO and (m2 < m1 or m2 == m1+1))

# ---------------------------------------------------------------- driver
def reduced(ds, n):
    return all(1 <= ds[i+1]-ds[i] <= n-1 for i in range(len(ds)-1))

def run_config(a, ds, label, stats, log):
    n = len(a); r = len(ds)
    BV, V, N = brute_vertices(a, ds)
    cls = sigma_class(a)
    st = stats.setdefault(cls, dict(cfg=0, tuples=0, T0=0, T1eq=0, T1imp=0, T1bad=0,
                                    T2=0, T2bad=0, T3=0, T3bad=0, T4=0, T4bad=0,
                                    T4pair=0, T4pairbad=0, T5=0, T5bad=0, red=0))
    st["cfg"] += 1
    red = reduced(ds, n)
    if red:
        st["red"] += 1
        TH = theta_normals(a, ds, N)
        # T0: offsets equal summed support values
        argm = {}
        for name, u, beta, kind, data in TH:
            hs = [argmax_set(u, V[q]) for q in range(r)]
            argm[name] = hs
            if sum(h[1] for h in hs) == beta: st["T0"] += 1
            else: log.append("T0 FAIL %s %s %s %s" % (label, ds, name, beta))
        e1 = vector(QQ, [1]+[0]*(N-1))
    for j, isv in BV.items():
        st["tuples"] += 1
        m = [ds[p]+j[p] for p in range(r)]
        if red:
            tight = []
            for name, u, beta, kind, data in TH:
                t_real = all(j[q] in argm[name][q][0] for q in range(r))
                t_form = formula_tight(kind, data, m, ds, n, N)
                if t_real == t_form: st["T1eq"] += 1
                elif t_real and not t_form: st["T1imp"] += 1   # extra tightness (weak case)
                else:
                    st["T1bad"] += 1
                    log.append("T1 FAIL %s %s j=%s %s real=%s form=%s" % (label, ds, j, name, t_real, t_form))
                if t_real: tight.append((kind, data, u))
            rk = matrix(QQ, [e1]+[u for _, _, u in tight]).rank()
            if (rk == N) == isv: st["T2"] += 1
            else:
                st["T2bad"] += 1; log.append("T2 FAIL %s %s j=%s rank=%d vertex=%s" % (label, ds, j, rk, isv))
            dfc = components_deficit(tight, N)
            if rk == N - dfc: st["T3"] += 1
            else:
                st["T3bad"] += 1; log.append("T3 FAIL %s %s j=%s rank=%d deficit=%d" % (label, ds, j, rk, dfc))
            if isv:
                phi = sum((u for _, _, u in tight), vector(QQ, [0]*N))
                ok = all(argmax_set(phi, V[q])[0] == {j[q]} for q in range(r))
                if ok: st["T5"] += 1
                else:
                    st["T5bad"] += 1; log.append("T5 FAIL %s %s j=%s" % (label, ds, j))
        pred = all(explicit_pair_ok(n, ds[p], ds[p+1], j[p], j[p+1]) for p in range(r-1))
        if pred == isv: st["T4"] += 1
        else:
            st["T4bad"] += 1; log.append("T4 FAIL %s %s j=%s vertex=%s explicit=%s" % (label, ds, j, isv, pred))
        predp = all(pair_vertex(a, ds[p], ds[p+1], j[p], j[p+1]) for p in range(r-1))
        if predp == isv: st["T4pair"] += 1
        else:
            st["T4pairbad"] += 1
            if len([l for l in log if l.startswith("T4pair")]) < 20:
                log.append("T4pair FAIL %s %s j=%s vertex=%s pairwise=%s" % (label, ds, j, isv, predp))

def shift_vectors(n, r, dmax, Nmax):
    for rest in itertools.combinations_with_replacement(range(0, dmax+1), r-1):
        ds = [0] + list(rest)
        if n + ds[-1] <= Nmax: yield ds

def main():
    stats = {}; log = []
    if MODE == "quick":
        ns = [3, 4]; rs = [2, 3]; Nmax = 9
    elif MODE == "full":
        ns = [3, 4, 5, 6]; rs = [2, 3, 4]; Nmax = 12
    else:  # "extra": rank 5 and n = 7, Kozlov + tent only
        ns = [3, 4, 7]; rs = [3, 5]; Nmax = 12
    for n in ns:
        legs = [("kozlov", kozlov(n)), ("tent", tent(n)), ("pow2", pow2(n)),
                ("randSLC1", rand_slc(n, 1000+n)), ("randSLC2", rand_slc(n, 2000+n)),
                ("ones", ones(n)), ("geom3", geom(n)), ("weaktie", weak_tie(n)),
                ("factorial", logconvex(n))]
        for r in rs:
            if n**r > 1300 and MODE != "extra": continue
            if n**r > 3200: continue
            dmax = min(n+1, 6)
            for ds in shift_vectors(n, r, dmax, Nmax):
                for lab, a in legs:
                    # keep the full battery for strict LC; controls on reduced configs only
                    if sigma_class(a) != "strictLC" and not reduced(ds, n): continue
                    if MODE == "full" and n == 6 and r == 4 and lab not in ("kozlov", "tent"): continue
                    if MODE == "extra" and (lab not in ("kozlov", "tent") or (n == 7) != (r == 3)): continue
                    run_config(a, ds, "%s(n=%d)" % (lab, n), stats, log)
        print("done n=%d" % n, flush=True)
    print("\n=== summary by sigma-class ===")
    for cls, st in stats.items():
        print(cls, st)
    print("\n=== failure log (first 60 lines) ===")
    for l in log[:60]: print(l)
    print("total log lines:", len(log))

main()
