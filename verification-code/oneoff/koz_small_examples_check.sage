# koz_small_examples_check.sage -- 2026-11-07, Claude-Code (jts-mini).
# The explicit computation behind Part III's Examples ex-koz3-d01 and ex-koz4-d01: Koz(n;0,1) for
# n = 3, 4 as the hull of the sumset S_n + shift(S_n), with exact (SageMath) vertices, facets, lattice
# points, and whether every lattice point is an ff-vector. Run: sage code/oneoff/koz_small_examples_check.sage
# Output on 2026-11-07 (SageMath 10.9):
#   n=3 d=(0,1): dim 3, vertices 7, facets 6, lattice pts 22, ff 22, all lattice ff: True
#     facets: 3 <= x2 <= 6, 3x3 <= x2 + 6, 3x4 <= x3, 0 <= x4 <= 1   (x0 = 1, x1 = 4)
#   n=4 d=(0,1): dim 4, vertices 11, facets 8, lattice pts 214, ff 162, all lattice ff: False
#     facets: 4 <= x2 <= 10, 3x3 <= 2x2 + 10, 4x4 <= x3 + 10, 3x4 <= 2x3, 4x5 <= x4, 0 <= x5 <= 1
#   the six-inequality system for n = 3 has exactly the seven vertices of Koz(3;0,1), and the
#   eight-inequality system for n = 4 exactly the eleven vertices of Koz(4;0,1).

from itertools import combinations
def fvecs(n):
    # f-vectors (f_0..f_n) of simplicial complexes on [n] using every vertex
    V = list(range(n)); faces = [frozenset(c) for k in range(n+1) for c in combinations(V, k)]
    out = set()
    # enumerate down-closed families via antichains of maximal faces (small n only)
    from itertools import chain
    nonempty = [f for f in faces if len(f) >= 1]
    def closure(gens):
        S = set([frozenset()])
        for g in gens:
            for k in range(len(g)+1):
                for c in combinations(sorted(g), k): S.add(frozenset(c))
        return S
    for r in range(1, len(nonempty)+1):
        for gens in combinations(nonempty, r):
            if any(a < b for a in gens for b in gens if a != b): continue
            S = closure(gens)
            if sum(1 for f in S if len(f) == 1) != n: continue
            out.add(tuple(sum(1 for f in S if len(f) == k) for k in range(n+1)))
    return sorted(out)
def shift(v, d): return tuple([0]*d) + tuple(v)
def pad(v, N): return tuple(v) + tuple([0]*(N+1-len(v)))
def koz(n, d):
    S = fvecs(n); N = n + d[-1]
    pts = set()
    def rec(i, acc):
        if i == len(d): pts.add(acc); return
        for s in S:
            v = pad(shift(s, d[i]), N); rec(i+1, tuple(a+b for a, b in zip(acc, v)))
    rec(0, tuple([0]*(N+1)))
    P = Polyhedron(vertices=[list(p) for p in pts])
    return P, pts
for n, d in [(3, (0, 1)), (4, (0, 1))]:
    P, FF = koz(n, d)
    L = P.integral_points()
    print(f"n={n} d={d}: dim {P.dim()}, vertices {P.n_vertices()}, facets {P.n_facets()}, lattice pts {len(L)}, ff {len(FF)}, all lattice ff: {set(tuple(x) for x in L) == FF}")
    print("  vertices:", sorted(tuple(v)[2:] for v in P.vertex_generator()))
    for ineq in P.inequality_generator():
        print("  ", ineq)
    for e in P.equation_generator(): print("  eq", e)
# the hand-checkable system for n=3, coordinates (x2,x3,x4)
Q = Polyhedron(ieqs=[[-3,1,0,0],[6,-1,0,0],[6,1,-3,0],[0,0,1,-3],[0,0,0,1],[1,0,0,-1]])
print("system vertices:", sorted(tuple(v) for v in Q.vertex_generator()), "facets", Q.n_facets())
# the hand-checkable system for n=4, coordinates (x2,x3,x4,x5)  (added 2026-11-07, for ex-koz4-d01)
Q4 = Polyhedron(ieqs=[[-4,1,0,0,0],[10,-1,0,0,0],[10,2,-3,0,0],[10,0,1,-4,0],[0,0,2,-3,0],[0,0,0,1,-4],[0,0,0,0,1],[1,0,0,0,-1]])
print("n=4 system vertices:", sorted(tuple(v) for v in Q4.vertex_generator()), "facets", Q4.n_facets())
