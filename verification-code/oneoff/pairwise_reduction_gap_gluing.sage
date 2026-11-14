# pairwise_reduction_gap_gluing.sage
#
# Changelog (reverse chronological):
#   2026-10-20  Added mode 'extra' (n=4, r=5; n=7, r=3).
#   2026-10-20  Created (Claude-Code, overnight article-3 push). Verifies the
#               gap-gluing proof of the consecutive pairwise reduction for
#               weakly log-concave leg vectors, in
#               working-notes/kozlov-pairwise-reduction-direct-2026-10-20.org.
#
# For each (leg vector a, sorted shift vector ds) it computes, independently:
#   T   : the brute-force extremal tensor (exact Polyhedron, ppl backend;
#         a tuple counts as extremal iff its point is a vertex AND no other
#         tuple gives the same point -- Lemma vertexdecomp(2)).
#   CONS: the conjunction of the consecutive rank-2 entries, the rank-2
#         matrices themselves computed by brute force (Polyhedron).
#   CF  : the closed form of the note (Theorem 2):
#         ties equal; m(p+1) >= m(p); and for a strict step m(p) < m(p+1)
#         with d(p+1) < m(p) and m(p+1) <= d(p)+n, the ratio
#         rho_c = a(c-d(p))/a(c-d(p+1)) is NOT constant on [m(p)+1, m(p+1)].
#   PHI : for every tuple CF predicts extremal, the explicit glued functional
#         of the note (head +1, tail -1, one gadget per gap), checked EXACTLY
#         (QQ) to expose every summand's chosen vertex -- every window, not
#         just the junction pairs the proof says suffice.
# It reports T == CONS, T == CF, PHI-all-ok. CF and PHI are only claimed for
# weakly log-concave a; log-convex / non-monotone vectors are negative
# controls (T == CONS is expected to fail for some of them).
#
# Run:  sage pairwise_reduction_gap_gluing.sage [quick|full] > log

import itertools, sys, random

def verts(a, d, N):
    n = len(a)
    return [vector(QQ, [0]*d + list(a[:k]) + [0]*(N-d-k)) for k in range(1, n+1)]

def extremal_set(a, ds):
    n = len(a); N = n + max(ds)
    Vs = [verts(a, d, N) for d in ds]
    tuples = list(itertools.product(range(1, n+1), repeat=len(ds)))
    pts = {}
    for t in tuples:
        x = sum((Vs[p][t[p]-1] for p in range(len(ds))), vector(QQ, [0]*N))
        pts.setdefault(tuple(x), []).append(t)
    P = Polyhedron(vertices=[vector(QQ, k) for k in pts], backend='ppl')
    ext = set()
    for v in P.vertices():
        ts = pts[tuple(vector(QQ, v))]
        if len(ts) == 1:
            ext.add(ts[0])
    return ext

_rank2 = {}
def rank2(a, g):
    key = (tuple(a), g)
    if key not in _rank2:
        _rank2[key] = extremal_set(a, [0, g])
    return _rank2[key]

def cons_prediction(a, ds, t):
    return all((t[p], t[p+1]) in rank2(a, ds[p+1]-ds[p]) for p in range(len(ds)-1))

def closed_form(a, ds, t):
    n = len(a)
    m = [ds[p] + t[p] for p in range(len(ds))]
    for p in range(len(ds)-1):
        if ds[p] == ds[p+1]:
            if m[p] != m[p+1]: return False
            continue
        if m[p+1] < m[p]: return False
        if m[p+1] > m[p] and ds[p+1] < m[p] and m[p+1] <= ds[p] + n:
            rho = [QQ(a[c-ds[p]-1]) / a[c-ds[p+1]-1] for c in range(m[p]+1, m[p+1]+1)]
            if len(set(rho)) == 1: return False
    return True

def window_ok(a, d, j, phi):
    n = len(a)
    f = [sum(a[i-1]*phi[d+i-1] for i in range(1, k+1)) for k in range(1, n+1)]
    return all(f[j-1] > f[k-1] for k in range(1, n+1) if k != j)

def glued_phi(a, ds, t):
    """The functional of Theorem 1's proof (Construction 3 of the note).
    Coordinates are 1-based global c = 1..N; returns a list of length N."""
    n = len(a); N = n + max(ds)
    # merge tied shifts (closed form guarantees equal m on ties)
    D, M = [], []
    for p in range(len(ds)):
        if D and D[-1] == ds[p]:
            assert M[-1] == ds[p] + t[p]
            continue
        D.append(ds[p]); M.append(ds[p] + t[p])
    phi = {}
    mus = sorted(set(M))
    for c in range(1, N+1):
        if c <= mus[0]: phi[c] = QQ(1)
        elif c > mus[-1]: phi[c] = QQ(-1)
        else: phi[c] = QQ(0)
    # junctions
    for p in range(len(D)-1):
        mu, mu2 = M[p], M[p+1]
        if mu == mu2: continue
        dp, dq = D[p], D[p+1]
        G = list(range(mu+1, mu2+1))
        if mu <= dq:                       # left private room: c = mu+1 unseen by window p+1's constraints
            for c in G: phi[c] = QQ(1)
            tot = sum(a[c-dp-1] for c in G[1:] if c <= dp+n)
            if mu+1 <= dp + n:
                phi[mu+1] = -(1 + QQ(tot)/a[mu+1-dp-1])
            else:
                phi[mu+1] = QQ(-1)
        elif mu2 > dp + n:                 # right private room: c = mu2 unseen by window p
            for c in G: phi[c] = QQ(-1)
            tot = sum(a[c-dq-1] for c in G[:-1] if c >= dq+2)
            phi[mu2] = 1 + QQ(tot)/a[mu2-dq-1]
        else:                              # both in the overlap: the bump
            rho1 = QQ(a[mu+1-dp-1]) / a[mu+1-dq-1]
            rho2 = QQ(a[mu2-dp-1]) / a[mu2-dq-1]
            assert len(G) >= 2 and rho1 > rho2, (a, ds, t)
            beta = (1 + rho1/rho2) / 2
            phi[mu+1] = -1 / QQ(a[mu+1-dq-1])
            phi[mu2] = beta / QQ(a[mu2-dq-1])
    return [phi[c] for c in range(1, N+1)]

def sigma_class(a):
    s = [QQ(a[i+1])/a[i] for i in range(len(a)-1)]
    if all(s[i] > s[i+1] for i in range(len(s)-1)): return 'strict-lc'
    if all(s[i] >= s[i+1] for i in range(len(s)-1)): return 'weak-lc'
    if all(s[i] <= s[i+1] for i in range(len(s)-1)): return 'log-convex'
    return 'non-monotone'

def run_config(a, ds, out):
    n = len(a)
    T = extremal_set(a, ds)
    tuples = list(itertools.product(range(1, n+1), repeat=len(ds)))
    cons = set(t for t in tuples if cons_prediction(a, ds, t))
    cls = sigma_class(a)
    lc = cls in ('strict-lc', 'weak-lc')
    cf = set(t for t in tuples if closed_form(a, ds, t)) if lc else None
    phiok = None
    if lc:
        phiok = True
        for t in cf:
            phi = glued_phi(a, ds, t)
            if not all(window_ok(a, ds[p], t[p], phi) for p in range(len(ds))):
                phiok = False
                out.write("  PHI FAIL %s %s %s phi=%s\n" % (a, ds, t, phi))
    line = "%-12s a=%s ds=%s |T|=%d T==CONS:%s T==CF:%s PHI:%s" % (
        cls, list(a), list(ds), len(T), T == cons,
        (T == cf) if lc else '-', phiok if lc else '-')
    out.write(line + "\n"); out.flush()
    return cls, T == cons, (T == cf) if lc else None, phiok

def kozlov(n): return [binomial(n, i) for i in range(1, n+1)]
def ones(n): return [1]*n
def tent(n): return [i*(n+1-i) for i in range(1, n+1)]
def pow2conc(n): return [2**(i*(n-i)) for i in range(1, n+1)]
def geom(n): return [3**i for i in range(n)]
def plateau(n):   # slopes 3,1,1,...,1/3 pattern: weakly log-concave with ties
    s = [QQ(3)] + [QQ(1)]*(n-3) + [QQ(1)/3] if n >= 3 else [QQ(1)]*(n-1)
    a = [QQ(1)]
    for x in s: a.append(a[-1]*x)
    return [x*lcm([y.denominator() for y in a]) for x in a]
def tiepair(n):   # strictly decreasing slopes except one tie in the middle
    s = sorted([QQ(random.randint(1, 9))/random.randint(1, 9) for _ in range(n-1)], reverse=True)
    k = (n-1)//2
    if n >= 3: s[k] = s[k-1]
    a = [QQ(1)]
    for x in s: a.append(a[-1]*x)
    L = lcm([y.denominator() for y in a]); return [x*L for x in a]
def rand_lc(n, strict=True):
    while True:
        s = sorted([QQ(random.randint(1, 12))/random.randint(1, 12) for _ in range(n-1)], reverse=True)
        if not strict or len(set(s)) == len(s): break
    a = [QQ(1)]
    for x in s: a.append(a[-1]*x)
    L = lcm([y.denominator() for y in a]); return [x*L for x in a]
def logconvex(n): return [factorial(i) for i in range(1, n+1)]
def nonmono(n): return [1, 3, 2, 5, 1, 4, 2][:n]

def shift_vectors(n, r, dmax):
    for rest in itertools.combinations_with_replacement(range(0, dmax+1), r-1):
        yield (0,) + tuple(rest)

if __name__ == '__main__' or True:
    mode = sys.argv[1] if len(sys.argv) > 1 else 'quick'
    random.seed(int(20261020))
    out = sys.stdout
    plan = []
    if mode == 'quick':
        for n in (3, 4):
            for gen in (kozlov, ones, tent, plateau, logconvex):
                for ds in shift_vectors(n, 3, n):
                    plan.append((gen(n), ds))
    elif mode == 'r2':
        for n in range(2, 9):
            for gen in (kozlov, ones, tent, pow2conc, geom, plateau, tiepair,
                        lambda k: rand_lc(k, True), lambda k: rand_lc(k, False)):
                a = gen(n)
                for g in range(0, n+1):
                    plan.append((a, (0, g)))
    elif mode == 'extra':
        for gen in (kozlov, ones, tent, plateau, tiepair):
            for ds in shift_vectors(4, 5, 4):
                plan.append((gen(4), ds))
        for gen in (kozlov, tent):
            for ds in shift_vectors(7, 3, 5):
                plan.append((gen(7), ds))
    else:
        gens = [kozlov, ones, tent, pow2conc, geom, plateau, tiepair,
                lambda k: rand_lc(k, True), lambda k: rand_lc(k, False),
                logconvex, nonmono]
        for n in (3, 4, 5):
            for gen in gens:
                a = gen(n)
                for r in (3, 4):
                    for ds in shift_vectors(n, r, n+1):
                        plan.append((a, ds))
        for gen in (kozlov, ones, tent, plateau, tiepair, lambda k: rand_lc(k, True)):
            a = gen(6)
            for ds in shift_vectors(6, 3, 7):
                plan.append((a, ds))
            for ds in shift_vectors(6, 4, 4):
                plan.append((a, ds))
    stats = {}
    for a, ds in plan:
        cls, c1, c2, c3 = run_config(a, ds, out)
        st = stats.setdefault(cls, [0, 0, 0, 0])
        st[0] += 1; st[1] += c1; st[2] += bool(c2); st[3] += bool(c3)
    out.write("\nSUMMARY  class: configs, T==CONS, T==CF, PHI ok\n")
    for k, v in stats.items():
        out.write("  %-12s %s\n" % (k, v))
