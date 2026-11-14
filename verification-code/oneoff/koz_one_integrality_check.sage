# 2026-11-11 - Claude-Code (jts-mini): Jan asked whether Koz(n;d) is k-integral in the sense of Liu 2011
#   (Adv. Math. 226, Definition 1.1) for some k > 0. 1-integral w.r.t. some lattice basis <=> some integer
#   functional g has |g(u)| = 1 on every primitive edge direction u. This lists the primitive edge directions
#   of Koz(n;d) = sum_i shift^{d_i} conv(F_1..F_n), checks that the triple e_{n-1+d}, e_{n+d}, n e_{n-1+d} + e_{n+d}
#   (the obstruction in working-notes/koz-k-integrality-liu2011-2026-11-11.org) is among them, and, for small
#   ambient dimension, searches g in [-3,3]^(N+1) as a sanity check (none should exist).
#   Run: timeout 600 sage code/oneoff/koz_one_integrality_check.sage
from itertools import product
def koz(n, d):
    N = n + max(d)
    F = [[binomial(n, k) if k <= j else 0 for k in range(n + 1)] for j in range(1, n + 1)]
    P = None
    for di in d:
        Q = Polyhedron(vertices=[[0]*di + f + [0]*(N - n - di) for f in F])
        P = Q if P is None else P + Q
    return P, N
def prim(v):
    g = gcd(v); return tuple(x // g for x in v)
for n, d in [(3, (0,)), (4, (0,)), (5, (0,)), (3, (0, 1)), (3, (0, 0, 2)), (4, (0, 1, 3)), (4, (0, 2))]:
    P, N = koz(n, d)
    dirs = set()
    for e in P.faces(1):
        a, b = [vector(v) for v in e.vertices()]
        u = prim(list(b - a)); dirs.add(max(u, tuple(-x for x in u)))
    ok_triple = True
    for di in set(d):
        a = [0]*(N+1); a[n-1+di] = 1; b = [0]*(N+1); b[n+di] = 1; c = [0]*(N+1); c[n-1+di] = n; c[n+di] = 1
        ok_triple &= all(tuple(x) in dirs or tuple(-y for y in x) in dirs for x in (a, b, c))
    found = None
    if N + 1 <= 7:
        for g in product(range(-3, 4), repeat=N+1):
            if all(abs(sum(gi*ui for gi, ui in zip(g, u))) == 1 for u in dirs):
                found = g; break
    print("n=%d d=%s dim=%d edges-dirs=%d triple-present=%s  g with |g(u)|=1 in [-3,3]^%d: %s"
          % (n, d, P.dim(), len(dirs), ok_triple, N+1, found if N+1 <= 7 else "skipped"))
