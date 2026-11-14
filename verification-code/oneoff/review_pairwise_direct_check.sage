# review_pairwise_direct_check.sage
# Changelog (reverse chronological):
#   2026-10-20  Created (referee check of kozlov-pairwise-reduction-direct-2026-10-20.org).
#               Written from scratch; does NOT import pairwise_reduction_gap_gluing.sage.
#
# For each (a, d) it computes
#   T    : brute-force extremal tensor: exact vertex enumeration (Polyhedron, QQ, ppl) of the
#          convex hull of all n^r sums sum_p shift^{d(p)} v(j(p)); T[j]=1 iff the point is a
#          vertex.  Also asserts each vertex point is produced by exactly one tuple
#          (lem-vertexdecomp(2)).
#   CONS : conjunction over consecutive p of the brute-force rank-two matrices M^{(p,p+1)}.
#   CF   : Theorem 2 of the note, implemented from its text: (i) ties => equal m, (ii) m
#          non-decreasing, (iii) no locked step.
#   PHI  : for each tuple CF accepts, the glued functional of Lemma 6 with Theorem 2's gadgets
#          (Cases A/B/C, implemented from the text), checked by evaluating phi on every vertex of
#          every summand and requiring j(p) to be the UNIQUE argmax.
#   COR  : (rank 2 only) the sigma-form Corollary of the note.
# Usage: sage review_pairwise_direct_check.sage [quick|full|extend|mutant]

import itertools, sys, random, time
from sage.all import QQ, Polyhedron, binomial, vector

def vpt(a, j, d, N):
    v = [QQ(0)]*N
    for i in range(j):
        v[d+i] = QQ(a[i])
    return v

def brute_tensor(a, ds):
    n = len(a); r = len(ds); N = n + ds[-1]
    pts = {}
    for js in itertools.product(range(1, n+1), repeat=r):
        s = [QQ(0)]*N
        for p in range(r):
            for i in range(js[p]):
                s[ds[p]+i] += QQ(a[i])
        pts.setdefault(tuple(s), []).append(js)
    P = Polyhedron(vertices=[list(k) for k in pts], base_ring=QQ, backend='ppl')
    verts = set(tuple(QQ(x) for x in v) for v in P.vertices_list())
    T = set()
    for k, lst in pts.items():
        if k in verts:
            assert len(lst) == 1, ("vertex produced twice", a, ds, lst)
            T.add(lst[0])
    return T

_r2cache = {}
def rank2(a, d1, d2):
    key = (tuple(a), d2 - d1)
    if key not in _r2cache:
        _r2cache[key] = brute_tensor(a, [0, d2 - d1])
    return _r2cache[key]

def cons(a, ds):
    n = len(a); r = len(ds)
    out = set()
    for js in itertools.product(range(1, n+1), repeat=r):
        if all((js[p], js[p+1]) in rank2(a, ds[p], ds[p+1]) for p in range(r-1)):
            out.add(js)
    return out

def A(a, k):   # a(k), 1-based
    return QQ(a[k-1])

def locked(a, dp, dq, mp, mq, n):
    if not (mp < mq and dq < mp and mq <= dp + n):
        return False
    rhos = [A(a, c-dp)/A(a, c-dq) for c in range(mp+1, mq+1)]
    return len(set(rhos)) == 1

def cf(a, ds, js):
    n = len(a); r = len(ds)
    m = [ds[p] + js[p] for p in range(r)]
    for p in range(r-1):
        if ds[p] == ds[p+1] and m[p] != m[p+1]: return False
        if m[p] > m[p+1]: return False
        if locked(a, ds[p], ds[p+1], m[p], m[p+1], n): return False
    return True

def glued_phi(a, ds, js):
    """Lemma 6 + Theorem 2 gadgets, from the note's text. Returns phi as dict coord->QQ."""
    n = len(a)
    # tie reduction: keep one summand per distinct shift
    red = []
    for p in range(len(ds)):
        if not red or red[-1][0] != ds[p]:
            red.append((ds[p], js[p]))
    d = [x[0] for x in red]; m = [x[0]+x[1] for x in red]
    N = n + ds[-1]
    mus = sorted(set(m))
    phi = {}
    for c in range(1, mus[0]+1): phi[c] = QQ(1)
    for c in range(mus[-1]+1, N+1): phi[c] = QQ(-1)
    for k in range(len(mus)-1):
        mu, mu2 = mus[k], mus[k+1]
        P = max(i for i in range(len(m)) if m[i] == mu); Q = P + 1
        assert m[Q] == mu2
        dP, dQ = d[P], d[Q]
        if mu <= dQ:                       # Case A
            for c in range(mu+2, mu2+1): phi[c] = QQ(1)
            S = sum((A(a, c-dP) for c in range(mu+2, min(mu2, dP+n)+1)), QQ(0))
            Lam = (S + 1)/A(a, mu+1-dP) if mu+1 <= dP+n else QQ(1)
            phi[mu+1] = -Lam
        elif mu2 > dP + n:                 # Case B
            for c in range(mu+1, mu2): phi[c] = QQ(-1)
            S = sum((A(a, c-dQ) for c in range(max(mu+1, dQ+2), mu2)), QQ(0))
            phi[mu2] = (S + 1)/A(a, mu2-dQ)
        else:                              # Case C
            rho = lambda c: A(a, c-dP)/A(a, c-dQ)
            assert rho(mu+1) > rho(mu2), ("Case C: rho not strictly smaller at end", a, ds, js)
            beta = (1 + rho(mu+1)/rho(mu2))/2
            for c in range(mu+1, mu2+1): phi[c] = QQ(0)
            phi[mu+1] = -1/A(a, mu+1-dQ)
            phi[mu2] = beta/A(a, mu2-dQ)
    assert sorted(phi) == list(range(1, N+1))
    return phi

def phi_ok(a, ds, js, phi):
    n = len(a)
    for p in range(len(ds)):
        f = [sum(A(a, i)*phi[ds[p]+i] for i in range(1, l+1)) for l in range(1, n+1)]
        best = max(f)
        if f[js[p]-1] != best or f.count(best) != 1:
            return False
    return True

def corollary_zero(a, g, i, j):
    n = len(a); mm = n - g; t = i - g
    sig = lambda k: A(a, k+1)/A(a, k)
    if not (1 <= g <= n-1): return None
    if not (1 <= t <= mm and 1 <= j <= mm): return False
    if j < t: return True
    if j == t + 1: return True
    if j > t + 1:
        return len(set(sig(k) for k in range(t+1, j+g))) == 1
    return False

def is_wlc(a):
    s = [QQ(a[i+1])/QQ(a[i]) for i in range(len(a)-1)]
    return all(s[i] >= s[i+1] for i in range(len(s)-1))

def from_sigma(s, a1=1):
    a = [QQ(a1)]
    for x in s: a.append(a[-1]*QQ(x))
    return a

def families(n, rng):
    F = {}
    F['kozlov'] = [binomial(n, i) for i in range(1, n+1)]
    F['ones'] = [1]*n
    F['tent'] = [i*(n+1-i) for i in range(1, n+1)]
    F['geom2'] = [2**i for i in range(n)]
    # long plateau of sigma=2 then plateau of sigma=1  (e.g. 1,2,4,4,4)
    k = (n-1+1)//2
    F['plat-2-1'] = from_sigma([2]*k + [1]*(n-1-k))
    # flat then halving: 8,8,8,4,2,...
    F['flat-drop'] = from_sigma([1]*k + [QQ(1)/2]*(n-1-k))
    # 3,3,1,1,...,1/3 style
    F['plat-3-1-1/3'] = from_sigma(([3] + [1]*(n-3) + [QQ(1)/3]) if n >= 3 else [1]*(n-1))
    # single-drop: sigma = 1,...,1,1/2,...  with drop at 1 position
    F['one-drop'] = from_sigma([1]*(n-2) + [QQ(1)/2]) if n >= 2 else [1]
    # random weakly lc with repeated values
    vals = [QQ(1)/3, QQ(1)/2, QQ(2)/3, 1, QQ(3)/2, 2, 3]
    for t in range(2):
        s = sorted([rng.choice(vals) for _ in range(n-1)], reverse=True)
        F['rand-wlc%d' % t] = from_sigma(s)
    s = sorted(rng.sample([QQ(x)/7 for x in range(1, 30)], n-1), reverse=True)
    F['rand-strict'] = from_sigma(s)
    for nm, a in F.items():
        assert all(x > 0 for x in a) and is_wlc(a), (nm, a)
    return F

def sorted_shifts(r, D):
    for rest in itertools.combinations_with_replacement(range(D+1), r-1):
        yield [0] + list(rest)

def main(mode):
    rng = random.Random(int(20261020))
    plan = []  # (n, r, Dmax, family filter)
    if mode == 'quick':
        plan = [(3, 3, 4, None)]
    elif mode == 'extend':
        plan = [(7, 2, 8, None), (8, 2, 9, None), (7, 3, 8, None), (6, 4, 6, None),
                (4, 5, 5, None), (4, 6, 4, ['kozlov', 'ones', 'plat-2-1', 'rand-wlc0'])]
    else:
        for n in range(2, 6):
            plan.append((n, 2, n+1, None))
            plan.append((n, 3, n+1, None))
            plan.append((n, 4, n+1 if n <= 4 else 4, None))
        plan.append((6, 2, 7, None))
        plan.append((6, 3, 6, None))
        plan.append((6, 4, 3, ['kozlov', 'ones', 'plat-2-1', 'flat-drop', 'rand-wlc0']))
        plan.append((5, 5, 3, ['kozlov', 'ones', 'plat-2-1', 'one-drop']))
    tot = 0; bad = 0; t0 = time.time()
    for (n, r, D, filt) in plan:
        F = families(n, rng)
        for nm, a in F.items():
            if filt and nm not in filt: continue
            for ds in sorted_shifts(r, D):
                T = brute_tensor(a, ds)
                C = cons(a, ds)
                CF = set(js for js in itertools.product(range(1, n+1), repeat=r) if cf(a, ds, js))
                ph = all(phi_ok(a, ds, js, glued_phi(a, ds, js)) for js in CF)
                cor = True
                if r == 2 and 1 <= ds[1] <= n-1:
                    for i in range(1, n+1):
                        for j in range(1, n+1):
                            z = corollary_zero(a, ds[1], i, j)
                            if z == ((i, j) in T): cor = False
                ok = (T == C) and (T == CF) and ph and cor
                tot += 1
                if not ok:
                    bad += 1
                    print("FAIL", nm, [str(x) for x in a], ds, "|T|", len(T), "T==CONS", T == C,
                          "T==CF", T == CF, "PHI", ph, "COR", cor,
                          "T-CF", sorted(T - CF)[:5], "CF-T", sorted(CF - T)[:5])
                    sys.stdout.flush()
        print("done n=%d r=%d D<=%d  configs so far %d  fails %d  (%.0fs)" % (n, r, D, tot, bad, time.time()-t0))
        sys.stdout.flush()
    # negative control: log-convex a must break T == CONS somewhere
    a = [1, 2, 6, 24]; nfail = 0; nc = 0
    for ds in sorted_shifts(3, 4):
        nc += 1
        if brute_tensor(a, ds) != cons(a, ds): nfail += 1
    print("negative control a=(1,2,6,24) r=3 D<=4: T!=CONS in %d of %d" % (nfail, nc))
    print("TOTAL weakly-log-concave configurations %d, failures %d" % (tot, bad))

def mutants():
    # Discrimination test: weakened closed forms must DISAGREE with T somewhere.
    rng = random.Random(int(7))
    def cf_no_iii(a, ds, js):
        m = [ds[p]+js[p] for p in range(len(ds))]
        return all(not (ds[p] == ds[p+1] and m[p] != m[p+1]) and m[p] <= m[p+1] for p in range(len(ds)-1))
    def cf_unitstep(a, ds, js):   # Kozlov form applied blindly to weakly lc a
        n = len(a); m = [ds[p]+js[p] for p in range(len(ds))]
        for p in range(len(ds)-1):
            if ds[p] == ds[p+1] and m[p] != m[p+1]: return False
            if m[p] > m[p+1]: return False
            if m[p+1] == m[p]+1 and ds[p+1] < m[p] < ds[p]+n: return False
        return True
    for n, r in [(4, 3), (5, 3)]:
        Fm = families(n, rng)
        for nm in ['plat-2-1', 'flat-drop', 'ones', 'kozlov']:
            a = Fm[nm]; c1 = c2 = 0; tot = 0
            for ds in sorted_shifts(r, n):
                T = brute_tensor(a, ds); tot += 1
                allj = list(itertools.product(range(1, n+1), repeat=r))
                if T != set(j for j in allj if cf_no_iii(a, ds, j)): c1 += 1
                if T != set(j for j in allj if cf_unitstep(a, ds, j)): c2 += 1
            print("mutant n=%d r=%d %-10s: no-(iii) differs in %d/%d, unit-step-form differs in %d/%d" % (n, r, nm, c1, tot, c2, tot))

if len(sys.argv) > 1 and sys.argv[1] == 'mutant':
    mutants()
else:
    main(sys.argv[1] if len(sys.argv) > 1 else 'full')
