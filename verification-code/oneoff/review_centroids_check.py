# review_centroids_check.py -- independent referee checks for
#   working-notes/centroids-and-moments-discrete-vs-continuous.org
#
# Changelog (reverse chronological):
# 2026-10-20 - Claude (adversarial-referee subagent): created.  Written from scratch,
#   NOT importing the author's centroids_moments.py.  S_n is obtained two ways: brute-force
#   enumeration of order ideals of P([n]) (n <= 5) and a Kruskal-Katona chain search
#   (n <= 8), plus a prefix-sum DP for centroids only (n <= 13).  Polytope quantities via
#   Sage (Polyhedron.centroid, integral_points, symbolic integration over the order simplex).
#
# Run:  sage -python review_centroids_check.py   (log: runs/2026-10-20_article3-overnight-push/2026-10-20_review-centroids.txt)
from fractions import Fraction as Q
from math import comb, isqrt
from itertools import combinations, product
import random, sys

def out(*a):
    print(*a); sys.stdout.flush()

# ---------------------------------------------------------------- Kruskal-Katona (own)
def kk_upper(m, k):
    """max f_{k+1} given f_k = m (k-element faces -> (k+1)-element faces)."""
    res, lev = 0, k
    while m > 0 and lev >= 1:
        a = lev
        while comb(a + 1, lev) <= m:
            a += 1
        m -= comb(a, lev)
        res += comb(a, lev + 1)
        lev -= 1
    return res

def S_by_kk(n):
    """all f-vectors (1,n,f2..fn) of proper complexes on [n], via KK."""
    res = []
    def rec(v):
        k = len(v) - 1
        if k == n:
            res.append(tuple(v)); return
        for w in range(min(kk_upper(v[-1], k), comb(n, k + 1)) + 1):
            rec(v + [w])
    rec([1, n])
    return res

def complexes_bruteforce(n):
    """all order ideals of P([n]) containing every singleton (proper complexes)."""
    subsets = sorted(range(1 << n), key=lambda s: bin(s).count('1'))
    res = []
    def rec(i, chosen):
        if i == len(subsets):
            res.append(frozenset(chosen)); return
        s = subsets[i]
        if bin(s).count('1') <= 1:
            chosen.add(s); rec(i + 1, chosen); chosen.discard(s); return
        ok = all((s & ~(1 << b)) in chosen for b in range(n) if s >> b & 1)
        if ok:
            chosen.add(s); rec(i + 1, chosen); chosen.discard(s)
        rec(i + 1, chosen)
    rec(0, set())
    return res

def fvec(cx, n):
    f = [0] * (n + 1)
    for s in cx: f[bin(s).count('1')] += 1
    return tuple(f)

def mean(pts):
    N = len(pts); d = len(pts[0])
    return tuple(Q(sum(p[i] for p in pts), N) for i in range(d))

def cov(pts):
    N = len(pts); d = len(pts[0]); m = mean(pts)
    return [[Q(sum(p[i] * p[j] for p in pts), N) - m[i] * m[j] for j in range(d)] for i in range(d)]

def mu(f, n):
    return tuple(Q(f[k], comb(n, k)) for k in range(len(f)))

def lattice_koz(n, t=1):
    """lattice points of t*Koz(n): f0=t, f1=n t, f_{k+1} <= f_k (n-k)/(k+1), f_n >= 0."""
    res = []
    def rec(v):
        k = len(v) - 1
        if k == n:
            res.append(tuple(v)); return
        for w in range(v[-1] * (n - k) // (k + 1) + 1):
            rec(v + [w])
    rec([t, n * t])
    return res

# ------------------------------------------- prefix-sum DP: centroid of a chain set
def chain_centroid(n, bound, start):
    """chain set f1=start, 0<=f_{k+1}<=bound(f_k,k); returns (count, [E f_k], k=1..n)."""
    layers = [{start: 1}]
    for k in range(1, n):
        cur = layers[-1]; mx = max(bound(v, k) for v in cur)
        diff = [0] * (mx + 2)
        for v, c in cur.items():
            diff[0] += c; diff[bound(v, k) + 1] -= c
        nxt, acc = {}, 0
        for w in range(mx + 1):
            acc += diff[w]
            if acc: nxt[w] = acc
        layers.append(nxt)
    # backward counts
    bwd = [None] * n
    bwd[n - 1] = {v: 1 for v in layers[n - 1]}
    for k in range(n - 2, -1, -1):
        nb = bwd[k + 1]; mx = max(nb) if nb else 0
        pref = [0] * (mx + 2)
        for w in range(mx + 1):
            pref[w + 1] = pref[w] + nb.get(w, 0)
        bwd[k] = {v: pref[min(bound(v, k + 1), mx) + 1] for v in layers[k]}
    tot = sum(bwd[0].values())
    E = [Q(sum(v * layers[k][v] * bwd[k][v] for v in layers[k]), tot) for k in range(n)]
    return tot, E

def isprime(n):
    return n >= 2 and all(n % p for p in range(2, isqrt(n) + 1))

# ---------------------------------------------------------------- beta
def beta(f, n):
    g = list(f)
    for k in range(2, n - 1):
        g[k] = Q(comb(n, k)) * (1 + Q(f[n - 1], n)) - f[n - k]
    return tuple(g)

def D(f, n):
    return tuple(comb(n, j) - f[n - j] for j in range(n + 1))

def sumset(A, shifts, N):
    cur = {tuple([0] * (N + 1))}
    for d in shifts:
        new = set()
        for x in cur:
            for a in A:
                y = list(x)
                for i, ai in enumerate(a): y[i + d] += ai
                new.add(tuple(y))
        cur = new
    return sorted(cur)

def fmt(v): return '(' + ', '.join(str(x) for x in v) + ')'

# ================================================================ main
if __name__ == '__main__':
    S = {}
    out('== 1. S_n: brute force vs KK; |S_n|')
    for n in range(1, 9):
        S[n] = sorted(set(S_by_kk(n)))
        line = f'n={n} |S_n|(KK)={len(S[n])}'
        if n <= 5:
            cxs = complexes_bruteforce(n)
            fs = sorted(set(fvec(c, n) for c in cxs))
            line += f'  #proper complexes={len(cxs)}  brute f-vectors match KK: {fs == S[n]}'
            if n <= 4:
                cm = mean([fvec(c, n) for c in cxs])
                line += f'  cx-centroid={fmt(cm)}'
        out(line)
    S[0] = [(1,)]

    out('\n== 2. centroids of S_n (exact), mu-coords, and Table R1 exact values')
    for n in range(3, 8):
        c = mean(S[n]); out(f'n={n} centroid(S_n)={fmt(c)}  mu={fmt(tuple(float(x) for x in mu(c,n)))}')

    out('\n== 3. Lemma 3: beta permutes vertices, involution, maps Koz(n) to itself (vertex check)')
    for n in range(3, 10):
        V = [tuple([1] + [comb(n, k) if k <= j else 0 for k in range(1, n + 1)]) for j in range(1, n + 1)]
        imgs = [beta(v, n) for v in V]
        perm = [V.index(tuple(int(x) for x in im)) + 1 if tuple(im) in [tuple(map(Q, v)) for v in V] else None for im in imgs]
        rnd = [tuple(random.randint(0, 50) for _ in range(n + 1)) for _ in range(5)]
        inv = all(beta(beta(x, n), n) == tuple(map(Q, x)) for x in rnd)
        out(f'n={n} beta: vertex j -> {perm}  involution(random pts)={inv}')

    out('\n== 4. Thm 5: lattice-point set beta-invariant iff n prime; centroid identity')
    for n in range(3, 9):
        L = lattice_koz(n); Ls = set(L)
        inv = all(tuple(beta(x, n)) in Ls for x in L)  # Q==int compare ok
        out(f'n={n} prime={isprime(n)} |L_n|={len(L)} beta(L_n)=L_n: {inv}')
    for n in range(3, 15):
        tot, E = chain_centroid(n, lambda v, k: v * (n - k) // (k + 1), n)
        m = [Q(1)] + [E[k - 1] / comb(n, k) for k in range(1, n + 1)]
        defect = max(abs(m[k] + m[n - k] - 1 - m[n - 1]) for k in range(1, n))
        out(f'n={n:2d} prime={isprime(n)!s:5} |L_n|={tot}  max_k|mu_k+mu_(n-k)-1-mu_(n-1)| = {float(defect):.3e}  identity holds={defect == 0}')
    for n in [4, 6, 8, 9, 10, 12]:
        p = min(q for q in range(2, n) if n % q == 0)
        x = tuple([comb(n, k) for k in range(n - 1)] + [1, 0])
        out(f'n={n} counterexample point x=(C(n,k)..,1,0): beta(x)_{p} = {beta(x, n)[p]} (non-integral: {beta(x,n)[p].denominator != 1})')

    out('\n== 5. Thm 6: core, link count, bounds')
    for n in range(3, 9):
        core = [s for s in S[n] if s[n - 1] == 0]; top = [s for s in S[n] if s[n - 1] > 0]
        cs = set(core)
        Dinv = all(D(s, n) in cs for s in core)
        # top: tp = n-1 or n ; check equivalence s(n-1)=0 <=> tp <= n-2
        eqv = all((s[n - 1] == 0) == (max(k for k in range(n + 1) if s[k]) <= n - 2) for s in S[n])
        # link bijection: f_{k-1}(Gamma) = f_k(Delta) - C(n-1,k)
        links = set(tuple(s[k] - comb(n - 1, k) for k in range(1, n + 1)) for s in top)
        target = set()
        for m in range(0, n):
            for g in S[m]: target.add(tuple(list(g) + [0] * (n - len(g))))
        cnt = sum(len(S[m]) for m in range(n))
        eps = Q(len(top), len(S[n]))
        c = mean(S[n]); mm = mu(c, n)
        pair = [mm[k] + mm[n - k] - 1 for k in range(1, n)]
        idx = sum(mm[1:]); lo = Q(n - 1, 2)
        ok = (min(pair) >= 0 and max(pair) <= eps and 0 <= mm[n] <= mm[n - 1] <= eps
              and lo <= idx <= lo + (n + 1) * eps / 2)
        cc = mean(core); mc = mu(cc, n)
        out(f'n={n} |core|={len(core)} D(core)⊂core:{Dinv} [s(n-1)=0 <=> tp<=n-2]:{eqv} '
            f'|top|={len(top)} sum_m<n|S_m|={cnt} link-image==target:{links == target} '
            f'eps={float(eps):.4f} maxpair={float(max(pair)):.4f} mu_(n-1)={float(mm[n-1]):.4f} '
            f'idx-(n-1)/2={float(idx-lo):.4f} bounds ok:{ok} core-centroid mu_k+mu_(n-k)=1:'
            f'{all(mc[k]+mc[n-k]==1 for k in range(1,n))}')
    for n in [10, 12]:
        tot, E = chain_centroid(n, lambda v, k: min(kk_upper(v, k), comb(n, k + 1)), n)
        m = [Q(1)] + [E[k - 1] / comb(n, k) for k in range(1, n + 1)]
        out(f'n={n} |S_n|={tot} maxpair={float(max(m[k]+m[n-k]-1 for k in range(1,n))):.3e} mu_(n-1)={float(m[n-1]):.3e}')

    out('\n== 6. second moments, n=3,4 (S_n, lattice), f-coords')
    for n in [3, 4]:
        for name, pts in [('S_n', S[n]), ('lattice', lattice_koz(n))]:
            C = cov([p[2:] for p in pts])
            out(f'n={n} {name}: Cov(f_2..f_n) = {[[str(x) for x in r] for r in C]}')

    out('\n== 7. rank >= 2 sumsets FF(n;d): counts and centroids')
    cases = [(3, (0, 0)), (3, (0, 1)), (3, (0, 2)), (4, (0, 0)), (4, (0, 1)), (4, (0, 2)),
             (4, (0, 3)), (5, (0, 0)), (5, (0, 1)), (3, (0, 0, 0)), (3, (0, 1, 2)), (3, (0, 1, 3))]
    FF = {}
    for n, d in cases:
        N = n + d[-1]
        F = sumset(S[n], d, N); FF[(n, d)] = F
        c = mean(F)
        Sind = [sum(Q(sum(s[k - di] for s in S[n] if 0 <= k - di <= n), len(S[n])) if 0 <= k - di <= n else 0
                    for di in d) for k in range(N + 1)]
        out(f'n={n} d={d} |FF|={len(F)} centroid={fmt(c)}  S-indep={fmt(Sind)}')
    C = cov([p[2:] for p in FF[(3, (0, 1))]])
    out(f'n=3 d=(0,1) Cov_FF(f2,f3,f4) = {[[str(x) for x in r] for r in C]}')

    out('\n== 8. Thm 8: FF(3;0^r) = r Koz(3) ∩ Z, count and centroid, r<=6')
    for r in range(1, 7):
        F = sumset(S[3], (0,) * r, 3)
        L = lattice_koz(3, r)
        c = mean(F)
        pred = (r, 3 * r, Q(3 * r * (2 * r + 1), 3 * r + 2), Q(r * r, 3 * r + 2))
        out(f'r={r} |FF|={len(F)} (r+1)(3r+2)/2={(r+1)*(3*r+2)//2} FF==lattice:{F == sorted(L)} centroid==pred:{c == pred}')
    out('|FF(4;0^r)| vs L_4(r) - 2r(r+1):')
    for r in range(1, 7):
        F = sumset(S[4], (0,) * r, 4); L = lattice_koz(4, r)
        Lpoly = 4 * Q(4 * r + 1, 4) * (r + 1) ** 2
        out(f'  r={r} |FF|={len(F)} |L|={len(L)} L4poly={Lpoly} L-2r(r+1)={len(L)-2*r*(r+1)} match:{len(F)==len(L)-2*r*(r+1)}')

    out('\n== 9. Euler-Maclaurin: lattice centroid of t Koz(n), t large, vs c + c1/t')
    pred = {4: [Q(3,4), Q(1,2), Q(1,4)], 5: [Q(4,5), Q(3,5), Q(2,5), Q(1,5)]}
    c1 = {4: [Q(-5,48), Q(-1,4), Q(-5,16)], 5: [Q(-1,10), Q(-1,5), Q(-3,10), Q(-7,20)]}
    for n in [4, 5]:
        for t in [20, 40, 80]:
            tot, E = chain_centroid(n, lambda v, k: v * (n - k) // (k + 1), n * t)
            m = [E[k - 1] / (t * comb(n, k)) for k in range(2, n + 1)]
            resid = [float(t * t * (m[i] - pred[n][i] - c1[n][i] / t)) for i in range(n - 1)]
            out(f'n={n} t={t} #pts={tot} t^2*(mu - c - c1/t) = {[round(x,3) for x in resid]}')
        if n == 4:
            out(f'  L_4(t) check t=1..8: {[chain_centroid(4, lambda v,k: v*(4-k)//(k+1), 4*t)[0] == 4*Q(4*t+1,4)*(t+1)**2 for t in range(1,9)]}')

    # ------------------------------------------------------------ Sage part
    try:
        from sage.all import Polyhedron, QQ, var, integrate
    except ImportError:
        out('Sage not available; skipping polytope part'); sys.exit()

    out('\n== 10. Sage: Koz(n) centroid and second moments (symbolic integration over order simplex)')
    for n in [3, 4]:
        xs = [var(f'x{k}') for k in range(2, n + 1)]
        # order simplex 1 >= x2 >= ... >= xn >= 0, integrate innermost xn first
        def I(h):
            e = h
            for i in range(len(xs) - 1, -1, -1):
                upper = xs[i - 1] if i > 0 else 1
                e = integrate(e, xs[i], 0, upper)
            return e
        vol = I(1)
        Emu = [I(x) / vol for x in xs]
        ok = all(bool(Emu[i] == QQ(n - (i + 2) + 1) / n) for i in range(len(xs)))
        okc = True
        for a in range(len(xs)):
            for b in range(a, len(xs)):
                k, l = a + 2, b + 2
                cv = I(xs[a] * xs[b]) / vol - Emu[a] * Emu[b]
                okc = okc and bool(cv == QQ((k - 1) * (n - l + 1)) / (n * n * (n + 1)))
        out(f'n={n} centroid mu_k=(n-k+1)/n: {ok}; Cov formula (k-1)(n-l+1)/(n^2(n+1)) all k<=l: {okc}')
    for n in [5, 6]:
        V = [[comb(n, k) if k <= j else 0 for k in range(1, n + 1)] for j in range(1, n + 1)]
        c = Polyhedron(vertices=V).centroid()
        out(f'n={n} Polyhedron.centroid mu = {[c[k-1]/comb(n,k) for k in range(1,n+1)]}')

    out('\n== 11. Sage: Koz(n;d) lattice points and polytope centroid')
    def koz_poly(n, d):
        N = n + d[-1]
        P = None
        for di in d:
            V = [[0] * di + [1] + [comb(n, k) if k <= j else 0 for k in range(1, n + 1)] + [0] * (N - n - di) for j in range(1, n + 1)]
            Q_ = Polyhedron(vertices=V)
            P = Q_ if P is None else P + Q_
        return P
    for n, d in [(3, (0, 0)), (3, (0, 1)), (3, (0, 2)), (4, (0, 0)), (4, (0, 1)), (4, (0, 2)), (3, (0, 1, 2)), (5, (0, 0))]:
        P = koz_poly(n, d)
        pts = [tuple(int(x) for x in p) for p in P.integral_points()]
        lat = mean(pts)
        cen = P.centroid()
        F = FF.get((n, d))
        extra = ''
        if F is not None:
            extra = f' FF⊂lattice:{set(F) <= set(pts)} |lattice\\FF|={len(set(pts)-set(F))}'
        out(f'n={n} d={d} dim={P.dim()} |lattice|={len(pts)} lattice-centroid={fmt(lat)} Koz-centroid={fmt(tuple(cen))}{extra}')
    P = koz_poly(3, (0, 1))
    out(f'n=3 d=(0,1) vertices: {sorted(tuple(v)[2:] for v in P.vertices_list())}')
