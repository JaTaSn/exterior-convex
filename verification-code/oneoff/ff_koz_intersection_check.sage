# Changelog (newest first)
# 2026-11-09  Claude-Code (jts-mini), while drafting Part V (exterior-convex_article5_draft_1.org, open problem 2):
#             exact check that FF(n;d) ∩ Koz(n;d) = FF_pr(n;d), FF = Hilbert functions of all graded
#             quotients of F (sums of shifted f-vectors of all complexes on [n], void included), FF_pr =
#             proper complexes only, Koz(n;d) = Minkowski sum of shifted Kozlov simplices, over QQ.
#             Range: 2 <= n <= 5, r in {2,3} (r = 2 at n = 5), d = (0,...) with all gaps in [0,n]; 68 cases.
#             Run: sage ff_koz_intersection_check.sage   (about a minute on jts-mini; result: 0 failures)
from itertools import combinations, product
def fvecs(n, proper):
    order = sorted([frozenset(c) for k in range(n+1) for c in combinations(range(n), k)], key=len)
    res = set()
    def rec(i, D):
        if i == len(order):
            f = [0]*(n+1)
            for s in D: f[len(s)] += 1
            if (not proper) or f[1] == n: res.add(tuple(f))
            return
        s = order[i]
        rec(i+1, D)
        if len(s) == 0 or all(frozenset(t) in D for t in combinations(sorted(s), len(s)-1)):
            rec(i+1, D | {s})
    rec(0, frozenset())
    return res
def sumset(n, d, S):
    L = d[-1]+n+1; acc = {tuple([0]*L)}
    for di in d:
        acc = {tuple(a[t] + (f[t-di] if 0 <= t-di <= n else 0) for t in range(L)) for a in acc for f in S}
    return acc
def koz(n, d):
    L = d[-1]+n+1
    P = None
    for di in d:
        V = [[0]*di + [binomial(n, t) if t <= k else 0 for t in range(n+1)] + [0]*(L-di-n-1) for k in range(1, n+1)]
        Q = Polyhedron(vertices=V, base_ring=QQ)
        P = Q if P is None else P + Q
    return P
cache = {}
cases = []
for n in range(2, 6):
    gaps = range(0, n+1)
    for r in (2, 3):
        if n == 5 and r == 3: continue
        for g in product(gaps, repeat=r-1):
            d = [0]
            for x in g: d.append(d[-1]+x)
            cases.append((n, tuple(d)))
bad = 0
for n, d in cases:
    if n not in cache: cache[n] = (fvecs(n, True), fvecs(n, False))
    Sp, Sa = cache[n]
    FFpr = sumset(n, d, Sp); FF = sumset(n, d, Sa)
    P = koz(n, d)
    inK = {x for x in FF if P.contains(vector(QQ, x))}
    ok = (inK == FFpr)
    if not ok: bad += 1
    print(n, d, len(FFpr), len(inK), ok)
print("cases", len(cases), "failures", bad)
