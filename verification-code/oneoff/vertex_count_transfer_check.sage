# vertex_count_transfer_check.sage -- 2026-11-17, jts-mini (Claude-Code).
#
# Part IV, Corollary cor-vertex-count: for a positive weakly log-concave leg vector a and shifts
# 0 = d_1 <= ... <= d_r, the number of vertices of RA(a; d) is
#       1^T  M(a; d_2-d_1) M(a; d_3-d_2) ... M(a; d_r-d_{r-1})  1,
# where M(a; delta) is the rank-two extremal matrix (identity for delta = 0).
#
# The check is independent of the paper's formulas on both sides:
#   * the vertex count is taken from the polytope itself, the convex hull of all n^r sums of
#     summand vertices, by exact rational polyhedral computation;
#   * M(a; delta) is taken from the rank-two polytope the same way (which sums are vertices),
#     NOT from the closed form of Corollary cor-rank2-lc.
# A second pass compares the brute-force M with the closed form of cor-rank2-lc, and a third
# prints the counts and Perron roots quoted in the paper.
#
# Run from code/:   sage oneoff/vertex_count_transfer_check.sage
# Log:              ../runs/2026-11-17_vertex-count-transfer/vertex_count_transfer_check.txt

import itertools, os, sys
from sage.all import QQ, ZZ, Polyhedron, matrix, vector, binomial, identity_matrix, AA, QQbar

OUT = "../runs/2026-11-17_vertex-count-transfer"
os.makedirs(OUT, exist_ok=True)
LOG = open(os.path.join(OUT, "vertex_count_transfer_check.txt"), "w")

def say(*args):
    s = " ".join(str(x) for x in args)
    print(s); LOG.write(s + "\n"); LOG.flush()

def vert(a, d, j, N):
    """shift^d(v_j) in R^N, coordinates 1..N stored 0-based; j in 1..n."""
    v = [0] * N
    for i in range(1, j + 1):
        v[d + i - 1] = a[i - 1]
    return vector(QQ, v)

def brute_vertices(a, d):
    """Set of tuples j in [n]^r whose sum is a vertex of RA(a; d); also the number of vertices."""
    n = len(a); r = len(d); N = n + max(d)
    sums = {}
    for js in itertools.product(range(1, n + 1), repeat=r):
        s = sum(vert(a, d[p], js[p], N) for p in range(r))
        sums.setdefault(tuple(s), []).append(js)
    P = Polyhedron(vertices=list(sums.keys()), base_ring=QQ)
    V = set(tuple(v) for v in P.vertices_list())
    good = set()
    for pt, lst in sums.items():
        if pt in V:
            assert len(lst) == 1, ("vertex with two decompositions", a, d, pt, lst)
            good.add(lst[0])
    return good, len(V)

_Mcache = {}
def M_brute(a, delta):
    key = (tuple(a), delta)
    if key not in _Mcache:
        n = len(a)
        if delta == 0:
            good, _ = brute_vertices(a, (0, 0))
        else:
            good, _ = brute_vertices(a, (0, delta))
        _Mcache[key] = matrix(ZZ, n, n, lambda i, j: 1 if (i + 1, j + 1) in good else 0)
    return _Mcache[key]

def M_closed(a, delta):
    """Corollary cor-rank2-lc (weakly log-concave a): zeros of the extremal matrix."""
    n = len(a)
    if delta == 0:
        return identity_matrix(ZZ, n)
    if delta >= n:
        return matrix(ZZ, n, n, lambda i, j: 1)
    m = n - delta
    sigma = {i: QQ(a[i]) / QQ(a[i - 1]) for i in range(1, n)}   # sigma_i = a_{i+1}/a_i, 1 <= i <= n-1
    def entry(i, j):          # 1-based
        t = i - delta
        if 1 <= t <= m and 1 <= j <= m:
            if j < t or j == t + 1:
                return 0
            if j >= t + 2 and len(set(sigma[u] for u in range(t + 1, j + delta))) == 1:
                return 0
        return 1
    return matrix(ZZ, n, n, lambda i, j: entry(i + 1, j + 1))

def transfer_count(a, d, M):
    n = len(a)
    one = vector(ZZ, [1] * n)
    w = one
    for p in range(len(d) - 1, 0, -1):
        w = M(a, d[p] - d[p - 1]) * w
    return one * w

def is_wlc(a):
    return all(a[i] ** 2 >= a[i - 1] * a[i + 1] for i in range(1, len(a) - 1))

def kozlov(n): return [binomial(n, k) for k in range(1, n + 1)]
def ones(n): return [1] * n

families = {
    "kozlov": kozlov, "ones": ones,
    "geometric2": lambda n: [2 ** k for k in range(n)],
    "plateau": lambda n: ([1, 2, 4, 4, 4, 4, 4])[:n],
    "linear": lambda n: list(range(1, n + 1)),
    "concave-bump": lambda n: [k * (n + 1 - k) for k in range(1, n + 1)],
}

def shift_vectors(n, r, maxN):
    for gaps in itertools.product(range(0, n + 2), repeat=r - 1):
        d = [0]
        for g in gaps: d.append(d[-1] + g)
        if n + d[-1] <= maxN:
            yield tuple(d)

say("== Pass 1: polytope vertex count  vs  1^T prod M_brute 1  (both by exact polyhedral computation)")
ncases = 0; nfail = 0
for name, fam in families.items():
    for n in range(1, 6):
        a = fam(n)
        assert all(x > 0 for x in a) and is_wlc(a)
        for r in range(2, 5):
            if n ** r > 700: continue
            for d in shift_vectors(n, r, maxN=n + 7 if r <= 3 else n + 5):
                _, nv = brute_vertices(a, d)
                tc = transfer_count(a, d, M_brute)
                ncases += 1
                if nv != tc:
                    nfail += 1
                    say("  FAIL", name, "n =", n, "d =", d, "polytope:", nv, "transfer:", tc)
    say("  family", name, "done; cumulative cases", ncases, "failures", nfail)
say("Pass 1:", ncases, "configurations,", nfail, "failures")

say("== Pass 2: M_brute  vs  closed form of cor-rank2-lc")
n2 = 0; f2 = 0
for name, fam in families.items():
    for n in range(1, 8):
        a = fam(n)
        for delta in range(0, n + 2):
            n2 += 1
            if M_brute(a, delta) != M_closed(a, delta):
                f2 += 1
                say("  FAIL", name, n, delta); say(M_brute(a, delta)); say(M_closed(a, delta))
say("Pass 2:", n2, "matrices,", f2, "failures")

say("== Pass 3: values quoted in the paper")
a = kozlov(4)
say("M(kozlov(4); 1) =", M_brute(a, 1).rows())
say("count n=4 d=(0,1):", transfer_count(a, (0, 1), M_brute), " d=(0,1,2):", transfer_count(a, (0, 1, 2), M_brute))
say("Part I rank-two count n^2 - (m-1)(m+2)/2, m = n - d, against 1^T M 1 (Kozlov):")
for n in range(2, 8):
    for dd in range(1, n):
        m = n - dd
        lhs = sum(sum(row) for row in M_closed(kozlov(n), dd).rows())
        assert lhs == n * n - (m - 1) * (m + 2) // 2, (n, dd, lhs)
say("  holds for 2 <= n <= 7, 1 <= d <= n-1")

say("Vertex counts of Koz(n; 0, delta, 2 delta, ..., (r-1) delta), r = 1..8, and the Perron root of M(kozlov(n); delta):")
for n in range(2, 7):
    for delta in range(1, n):
        Mx = M_closed(kozlov(n), delta)
        one = vector(ZZ, [1] * n)
        seq = []; w = one
        for r in range(1, 9):
            seq.append(one * w); w = Mx * w
        cp = Mx.charpoly()
        rho = max(abs(z) for z in cp.roots(QQbar, multiplicities=False))
        say("  n =", n, "delta =", delta, " counts:", seq, " charpoly:", cp.factor(), " rho ~ %.6f" % float(rho))
say("Same for the all-ones vector:")
for n in range(2, 7):
    for delta in range(1, n):
        Mx = M_closed(ones(n), delta)
        one = vector(ZZ, [1] * n)
        seq = []; w = one
        for r in range(1, 9):
            seq.append(one * w); w = Mx * w
        cp = Mx.charpoly()
        rho = max(abs(z) for z in cp.roots(QQbar, multiplicities=False))
        say("  n =", n, "delta =", delta, " counts:", seq, " charpoly:", cp.factor(), " rho ~ %.6f" % float(rho))
LOG.close()
