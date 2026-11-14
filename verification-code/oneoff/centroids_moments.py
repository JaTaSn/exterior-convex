# centroids_moments.py -- discrete vs continuous centroids and second moments of
# S_n, Koz(n), FF(n; d) and Koz(n; d).  Pure Python (fractions), importable from Sage.
#
# Changelog (reverse chronological):
# 2026-10-20 - Claude (overnight article-3 agent): created.  Rank-1 part is an exact
#   layered-DAG ("chain") dynamic programme: S_n and the lattice points of t*Koz(n)
#   are both sets of sequences (f_1,...,f_n) with f_1 = n*t and f_{k+1} in [0, g_k(f_k)]
#   for a nondecreasing bound g_k (Kruskal-Katona pseudopower for S_n, floor of the
#   linear ratio (n-k)/(k+1) for lattice points), so counts, first and second moments
#   come from forward/backward prefix sums in O(n^2 2^n) instead of enumeration.
#   Every DP number is cross-checked against brute-force enumeration for small n
#   (see self_test()).  Also: uniform measure on proper simplicial complexes (n <= 6,
#   by enumeration), sumsets FF(n; d), and the closed forms for the order simplex.
#
# Usage:  python3 centroids_moments.py selftest | checks
from fractions import Fraction as Q
from math import comb
from functools import lru_cache
from itertools import product, combinations
import sys


# ---------------------------------------------------------------- Kruskal-Katona
def kk_cascade(m, i):
    """i-binomial representation m = C(a_i,i)+C(a_{i-1},i-1)+..., a_i > a_{i-1} > ..."""
    terms = []
    level = i
    while m > 0 and level >= 1:
        a = level
        while comb(a + 1, level) <= m:
            a += 1
        # a is the largest with C(a,level) <= m
        terms.append((a, level))
        m -= comb(a, level)
        level -= 1
    assert m == 0
    return terms


def kk_bound(m, k):
    """Max number of (k+1)-faces given m k-faces (cardinality convention, k >= 1)."""
    if m == 0:
        return 0
    return sum(comb(a, l + 1) for a, l in kk_cascade(m, k))


def g_kk(n):
    """g[k][v] = max f_{k+1} given f_k = v, k = 1..n-1, v = 0..C(n,k)."""
    return {k: [kk_bound(v, k) for v in range(comb(n, k) + 1)] for k in range(1, n)}


def g_lat(n, t=1):
    """Lattice points of t*Koz(n): f_{k+1} <= f_k (n-k)/(k+1) (mu_{k+1} <= mu_k)."""
    return {k: [(v * (n - k)) // (k + 1) for v in range(t * comb(n, k) + 1)]
            for k in range(1, n)}


# ---------------------------------------------------------------- chain DP
def chain_moments(n, g, first=None, second=True):
    """For the set of sequences (f_1..f_n) with f_1 = first (default n) and
    0 <= f_{k+1} <= g[k][f_k], return (count, S1, S2) where S1[k] = sum f_k and
    S2[k][l] = sum f_k f_l (k,l = 1..n), exact integers."""
    if first is None:
        first = n
    # forward counts F[k] : list indexed by value
    F = {1: {first: 1}}
    for k in range(1, n):
        top = g[k]
        nxt = {}
        # F_{k+1}(w) = sum_{v : g(v) >= w} F_k(v): accumulate via difference array
        maxw = max((top[v] for v in F[k]), default=0)
        diff = [0] * (maxw + 2)
        for v, c in F[k].items():
            diff[0] += c
            diff[top[v] + 1] -= c
        run = 0
        for w in range(maxw + 1):
            run += diff[w]
            if run:
                nxt[w] = run
        F[k + 1] = nxt
    # backward counts B[k][v]
    B = {n: {v: 1 for v in F[n]}}
    for k in range(n - 1, 0, -1):
        top = g[k]
        vals = F[k].keys()
        maxw = max((top[v] for v in vals), default=0)
        pref = [0] * (maxw + 2)
        for w in range(maxw + 1):
            pref[w + 1] = pref[w] + B[k + 1].get(w, 0)
        B[k] = {v: pref[top[v] + 1] for v in vals}
    count = sum(F[n][v] * B[n][v] for v in F[n])
    S1 = {k: sum(v * F[k][v] * B[k][v] for v in F[k]) for k in range(1, n + 1)}
    S2 = {k: {k: sum(v * v * F[k][v] * B[k][v] for v in F[k])} for k in range(1, n + 1)}
    for k in (range(1, n + 1) if second else []):
        W = {v: v * c for v, c in F[k].items()}
        for l in range(k + 1, n + 1):
            top = g[l - 1]
            maxw = max((top[v] for v in W), default=0)
            diff = [0] * (maxw + 2)
            for v, c in W.items():
                diff[0] += c
                diff[top[v] + 1] -= c
            run = 0
            nW = {}
            for w in range(maxw + 1):
                run += diff[w]
                if run:
                    nW[w] = run
            W = nW
            S2[k][l] = sum(w * c * B[l][w] for w, c in W.items())
            S2[l][k] = S2[k][l]
    return count, S1, S2


def chain_enumerate(n, g, first=None):
    if first is None:
        first = n
    out = []

    def rec(pre):
        if len(pre) == n:
            out.append(tuple(pre))
            return
        for w in range(g[len(pre)][pre[-1]] + 1):
            rec(pre + [w])
    rec([first])
    return out


def moments_from_points(pts, weights=None):
    """pts: list of tuples (any length D); returns (total weight, S1 list, S2 matrix)."""
    D = len(pts[0])
    if weights is None:
        weights = [1] * len(pts)
    W = sum(weights)
    S1 = [sum(w * p[i] for p, w in zip(pts, weights)) for i in range(D)]
    S2 = [[sum(w * p[i] * p[j] for p, w in zip(pts, weights)) for j in range(D)]
          for i in range(D)]
    return W, S1, S2


# ---------------------------------------------------------------- order simplex
def koz_centroid_f(n):
    """Centroid of Koz(n) in f-coordinates (f_0..f_n): proved closed form."""
    return [Q(1)] + [Q(comb(n, k) * (n - k + 1), n) for k in range(1, n + 1)]


def koz_mu_moments(n):
    """Uniform measure on the order simplex 1 = mu_1 >= mu_2 >= ... >= mu_n >= 0.
    mu_k is the (n-k+1)-th smallest of m = n-1 iid U(0,1) (k >= 2).
    E mu_k = (n-k+1)/n; for 2 <= k <= l:  Cov(mu_k, mu_l) = i(n-j)/(n^2 (n+1)) with
    i = n-l+1 <= j = n-k+1 (order-statistic covariance i(m+1-j)/((m+1)^2(m+2)))."""
    E = {k: Q(n - k + 1, n) for k in range(1, n + 1)}
    C = {}
    for k in range(1, n + 1):
        for l in range(1, n + 1):
            if k == 1 or l == 1:
                C[k, l] = Q(0)
                continue
            i, j = sorted((n - k + 1, n - l + 1))
            C[k, l] = Q(i * (n - j), n * n * (n + 1))
    return E, C


def simplex_second_moment(verts):
    """E[x x^T] for the uniform measure on the simplex conv(verts) (D+1 affinely
    independent vertices): (sum_v v v^T + (sum v)(sum v)^T)/((D+1)(D+2))."""
    D1 = len(verts)
    dim = len(verts[0])
    s = [sum(v[i] for v in verts) for i in range(dim)]
    return [[Q(sum(v[i] * v[j] for v in verts) + s[i] * s[j], D1 * (D1 + 1))
             for j in range(dim)] for i in range(dim)]


# ---------------------------------------------------------------- complexes
def proper_complex_fvector_counts(n):
    """dict f-vector (f_1..f_n) -> number of simplicial complexes on [n] containing all
    n vertices.  Level-by-level enumeration with bitmasks; fine for n <= 6."""
    faces = {k: [frozenset(c) for c in combinations(range(n), k)] for k in range(n + 1)}
    idx = {k: {f: i for i, f in enumerate(faces[k])} for k in range(n + 1)}
    # for each (k+1)-set, the bitmask of its k-subsets
    sub = {k: [sum(1 << idx[k][f - {x}] for x in f) for f in faces[k + 1]]
           for k in range(1, n)}
    counts = {}

    def rec(k, mask, fv):
        # mask: bitmask of chosen k-faces; fv: f-vector so far (f_1..f_k)
        if k == n:
            counts[fv] = counts.get(fv, 0) + 1
            return
        cand = [j for j, sm in enumerate(sub[k]) if sm & mask == sm]
        if not cand:
            t = fv + (0,) * (n - k)
            counts[t] = counts.get(t, 0) + 1
            return
        L = len(cand)
        for s in range(1 << L):
            m2 = 0
            c = 0
            ss = s
            while ss:
                b = ss & -ss
                j = b.bit_length() - 1
                m2 |= 1 << cand[j]
                c += 1
                ss ^= b
            rec(k + 1, m2, fv + (c,))
    rec(1, (1 << n) - 1, (n,))
    return counts


# ---------------------------------------------------------------- sumsets
def shift(s, d, N):
    out = [0] * (N + 1)
    for i, x in enumerate(s):
        out[i + d] = x
    return tuple(out)


def Sn_points(n):
    """S_n as tuples (f_0..f_n)."""
    return [(1,) + p for p in chain_enumerate(n, g_kk(n))]


def ff_sumset(n, ds, Sn=None, multiplicity=False):
    if Sn is None:
        Sn = Sn_points(n)
    N = n + ds[-1]
    acc = {(0,) * (N + 1): 1}
    for d in ds:
        sh = [shift(s, d, N) for s in Sn]
        new = {}
        for a, c in acc.items():
            for b in sh:
                t = tuple(x + y for x, y in zip(a, b))
                new[t] = new.get(t, 0) + c
        acc = new
    return acc if multiplicity else list(acc)


# ---------------------------------------------------------------- self test
def self_test(nmax=6):
    for n in range(1, nmax + 1):
        for name, g in (("S_n", g_kk(n)), ("lat", g_lat(n))):
            pts = chain_enumerate(n, g)
            W, S1, S2 = moments_from_points(pts)
            c, T1, T2 = chain_moments(n, g)
            assert c == W, (n, name)
            for k in range(1, n + 1):
                assert T1[k] == S1[k - 1], (n, name, k)
                for l in range(1, n + 1):
                    assert T2[k][l] == S2[k - 1][l - 1], (n, name, k, l)
        # S_n counts
    assert [chain_moments(n, g_kk(n))[0] for n in range(1, 8)] == [1, 2, 5, 16, 70, 457, 4908]
    # complexes vs S_n support
    for n in range(1, 6):
        cnt = proper_complex_fvector_counts(n)
        assert set(cnt) == set(chain_enumerate(n, g_kk(n))), n
    # order-simplex closed form vs simplex moment formula, mu-coordinates
    for n in range(2, 8):
        verts = [[1] * j + [0] * (n - j) for j in range(1, n + 1)]   # mu_1..mu_n
        M = simplex_second_moment(verts)
        E, C = koz_mu_moments(n)
        for k in range(1, n + 1):
            assert Q(sum(v[k - 1] for v in verts), n) == E[k]
            for l in range(1, n + 1):
                assert M[k - 1][l - 1] - E[k] * E[l] == C[k, l], (n, k, l)
    print("self_test passed (n <= %d)" % nmax)


def checks(nprime=19):
    """The ad-hoc verifications quoted in working-notes/centroids-and-moments-discrete-vs-continuous.org."""
    print("-- Theorem 5(c): lattice centroid identity mu_k + mu_{n-k} = 1 + mu_{n-1}")
    for n in range(3, nprime + 1):
        c, S1, _ = chain_moments(n, g_lat(n), second=False)
        mu = {k: Q(S1[k], c * comb(n, k)) for k in range(1, n + 1)}
        print("  n=%d identity holds: %s" % (n, all(mu[k] + mu[n - k] - 1 - mu[n - 1] == 0 for k in range(1, n))))
    print("-- Theorem 6: |S_n^top| = sum_{m<n} |S_m|, D_n involution of the core")
    for n in range(3, 9):
        S = Sn_points(n)
        top = [s for s in S if s[n - 1] >= 1]
        pred = 1 + sum(chain_moments(m, g_kk(m), second=False)[0] for m in range(1, n))
        core = [s for s in S if s[n - 1] == 0]
        D = lambda s: tuple(comb(n, j) - s[n - j] for j in range(n + 1))
        print("  n=%d |top|=%d predicted=%d core D-invariant=%s" % (n, len(top), pred, set(map(D, core)) == set(core)))
    print("-- Theorem 6(c) bounds, n <= 12")
    for n in range(3, 13):
        c, S1, _ = chain_moments(n, g_kk(n), second=False)
        mu = {k: Q(S1[k], c * comb(n, k)) for k in range(1, n + 1)}
        eps = Q(1 + sum(chain_moments(m, g_kk(m), second=False)[0] for m in range(1, n)), c)
        dev = [mu[k] + mu[n - k] - 1 for k in range(1, n)]
        ok = all(0 <= x <= eps for x in dev) and 0 <= mu[n] <= mu[n - 1] <= eps
        print("  n=%d eps=%.4g maxdev=%.4g mu_{n-1}=%.4g mean-(n-1)/2=%.4g bounds ok=%s"
              % (n, eps, max(dev), mu[n - 1], sum(mu.values()) - Q(n - 1, 2), ok))
    print("-- Theorem 8: FF(3;0^r) = lattice points of r Koz(3), centroid closed form")
    for r in range(1, 8):
        FF = ff_sumset(3, (0,) * r)
        lat = [(r, 3 * r, a, b) for a in range(3 * r + 1) for b in range(a // 3 + 1)]
        W, S1, _ = moments_from_points(FF)
        print("  r=%d |FF|=%d =lattice:%s centroid formula:%s" % (r, len(FF), set(FF) == set(lat),
              Q(S1[2], W) == Q(3 * r * (2 * r + 1), 3 * r + 2) and Q(S1[3], W) == Q(r * r, 3 * r + 2)))
    print("-- Conjecture 9 data: FF(n;0^r) centroid / r in nu-coordinates; deficit vs lattice")
    for n, rmax in ((4, 10), (5, 5)):
        Sn = Sn_points(n)
        acc = {tuple([0] * (n + 1))}
        for r in range(1, rmax + 1):
            acc = {tuple(a + b for a, b in zip(x, s)) for x in acc for s in Sn}
            W, S1, _ = moments_from_points(list(acc))
            L = chain_moments(n, g_lat(n, r), first=n * r)[0]
            print("  n=%d r=%d |FF|=%d lattice=%d deficit=%d nu=%s" % (n, r, len(acc), L, L - len(acc),
                  " ".join("%.4f" % (S1[k] / W / r / comb(n, k)) for k in range(2, n + 1))))


if __name__ == "__main__":
    cmd = sys.argv[1] if len(sys.argv) > 1 else "selftest"
    if cmd == "selftest":
        self_test()
    elif cmd == "checks":
        checks()
