# review_pairwise_hside_check.sage
#
# Changelog (reverse chronological):
#   2026-10-20  Created (Claude-Code, adversarial referee of
#               working-notes/kozlov-pairwise-reduction-hside-2026-10-20.org).
#               Written from the note's statements only; the author's
#               kozlov_pairwise_hside_check.sage was NOT read or reused.
#
# Usage:  sage review_pairwise_hside_check.sage MODE      MODE in {brute, comb}
#
# brute: for each leg vector a and sorted shift vector d (ties, gaps 0..n+1),
#   B1  brute-force vertex set (Sage Polyhedron over QQ, ppl, of all n^r sums)
#       vs condition (3) of the H-side theorem as read from the note;
#   B2  brute force vs the direct note's Theorem 2 (weak-LC general form,
#       with the rho-constancy test), and vs its strict-LC corollary;
#   B3  (3) vs Theorem 2 as predicates over all tuples (they must coincide
#       for strictly LC a);
#   B4  brute force vs condition (2) (pairwise rank-two vertexhood, brute);
#   on reduced configurations (distinct shifts, gaps in [1, n-1]) also
#   B5  tight set computed from scratch (h(u,R) = sum_p max_k u.v(p,k))
#       vs the tightness-lemma closed form (iff, strict LC);
#   B6  rank(tight + e1) == N  vs  brute-force vertexhood;
#   B7  phi = sum of tight normals exposes x(j) uniquely (checked against all
#       n^r candidate points, i.e. directly on R) for every vertex.
# comb: Proposition 5 as pure linear algebra, larger ranges, no polytopes:
#   for random strictly LC a, every reduced d, every tuple satisfying (3),
#   tight set from argmax, exact rank == N.

import itertools, random, sys, time
from sage.all import QQ, Polyhedron, matrix, vector, binomial, factorial

def vtx(a, n, N, d, k):
    v = [QQ(0)]*N
    for i in range(1, k+1):
        v[d+i-1] = QQ(a[i-1])
    return v

def strictLC(a):
    s = [QQ(a[i+1])/a[i] for i in range(len(a)-1)]
    return all(s[i] > s[i+1] for i in range(len(s)-1))

def weakLC(a):
    s = [QQ(a[i+1])/a[i] for i in range(len(a)-1)]
    return all(s[i] >= s[i+1] for i in range(len(s)-1))

def cond3(n, d, j):
    r = len(d)
    m = [d[p]+j[p] for p in range(r)]
    for p in range(r-1):
        if d[p] == d[p+1]:
            if j[p] != j[p+1]:
                return False
            continue
        B = d[p+1]+1; A = d[p]+n
        inO = (B <= m[p] <= A) and (B <= m[p+1] <= A)
        if inO and (m[p+1] < m[p] or m[p+1] == m[p]+1):
            return False
    return True

def thm2_direct(a, n, d, j):
    # direct note Theorem 2, weak-LC form, literal
    r = len(d)
    m = [d[p]+j[p] for p in range(r)]
    for p in range(r-1):
        if d[p] == d[p+1] and m[p] != m[p+1]:
            return False
        if m[p] > m[p+1]:
            return False
        if m[p] < m[p+1] and d[p+1] < m[p] and m[p+1] <= d[p]+n:
            rho = set(QQ(a[c-d[p]-1])/a[c-d[p+1]-1] for c in range(m[p]+1, m[p+1]+1))
            if len(rho) == 1:
                return False
    return True

def thm2_strict_cor(n, d, j):
    r = len(d)
    m = [d[p]+j[p] for p in range(r)]
    for p in range(r-1):
        if m[p] > m[p+1]: return False
        if d[p] == d[p+1] and m[p] != m[p+1]: return False
        if m[p+1] == m[p]+1 and d[p+1] < m[p] < d[p]+n: return False
    return True

def brute_vertices(a, n, d):
    r = len(d); N = n + d[-1]
    vs = {}
    for p in range(r):
        vs[p] = [vtx(a, n, N, d[p], k) for k in range(1, n+1)]
    pts = {}
    for j in itertools.product(range(1, n+1), repeat=r):
        x = [sum(vs[p][j[p]-1][c] for p in range(r)) for c in range(N)]
        pts[j] = tuple(x)
    P = Polyhedron(vertices=list(set(pts.values())), base_ring=QQ, backend='ppl')
    V = set(tuple(QQ(t) for t in v) for v in P.vertices_list())
    M = {j: (pts[j] in V) for j in pts}
    return M, pts, vs

_pair_cache = {}
def pair_matrix(a, n, g):
    key = (tuple(a), n, g)
    if key not in _pair_cache:
        M, _, _ = brute_vertices(a, n, (0, g))
        _pair_cache[key] = M
    return _pair_cache[key]

def cond2(a, n, d, j):
    for p in range(len(d)-1):
        g = d[p+1]-d[p]
        if not pair_matrix(a, n, g)[(j[p], j[p+1])]:
            return False
    return True

def theta_list(a, n, d):
    # the note's list U (reduced case), outward normals, plus labels
    r = len(d); N = n + d[-1]
    U = []
    def e(c, s=1):
        u = [QQ(0)]*N; u[c-1] = QQ(s); return u
    for p in range(r):
        for c in range(d[p]+1, d[p]+n):           # c, c+1 in W(p)
            if p == 0 or c >= d[p]+2:
                l = c - d[p]
                u = [QQ(0)]*N
                u[c] = 1/QQ(a[l]); u[c-1] = -1/QQ(a[l-1])
                U.append((('L', p, c), u))
    for p in range(1, r):
        U.append((('C', p), e(d[p]+1, -1)))
        U.append((('D', p), e(d[p-1]+n+1, 1)))
    U.append((('F',), e(N, -1)))
    return U

def closed_form_tight(lab, n, d, m):
    r = len(d); N = n + d[-1]
    if lab[0] == 'L':
        _, p, c = lab
        return m[p] != c and all(m[q] <= c-1 for q in range(p)) and all(m[q] >= c+1 for q in range(p+1, r))
    if lab[0] == 'C':
        p = lab[1]
        return all(m[q] <= d[p] for q in range(p))
    if lab[0] == 'D':
        p = lab[1]
        return all(m[q] >= d[p-1]+n+1 for q in range(p, r))
    if lab[0] == 'F':
        return m[r-1] <= N-1

def dot(u, v):
    return sum(x*y for x, y in zip(u, v))

def reduced(n, d):
    return all(1 <= d[p+1]-d[p] <= n-1 for p in range(len(d)-1))

def shift_vectors(n, r, dmax):
    for rest in itertools.combinations_with_replacement(range(0, dmax+1), r-1):
        d = (0,) + tuple(rest)
        if d[-1] + n <= 12:
            yield d

def legs(n, rng):
    L = []
    L.append(('kozlov', [binomial(n, i) for i in range(1, n+1)]))
    L.append(('tent', [i*(n+1-i) for i in range(1, n+1)]))
    L.append(('2^{i(n-i)}', [2**(i*(n-i)) for i in range(1, n+1)]))
    for t in range(2):
        # random strictly decreasing slopes
        sl = sorted(set(QQ(rng.randint(1, 40))/rng.randint(1, 12) for _ in range(4*n)), reverse=True)
        while len(sl) < n-1:
            sl = sorted(set(sl + [QQ(rng.randint(1, 40))/rng.randint(1, 12)]), reverse=True)
        sl = sorted(rng.sample(sl, n-1), reverse=True)
        a = [QQ(rng.randint(1, 5))]
        for s in sl: a.append(a[-1]*s)
        L.append(('randLC%d' % t, a))
    return L

def run_brute(log):
    rng = random.Random(int(20261020))
    stats = {}
    fails = []
    t0 = time.time()
    plan = [(n, r) for n in range(2, 7) for r in range(2, 5)]
    for (n, r) in plan:
        for name, a in legs(n, rng):
            assert strictLC(a) or n <= 2, (name, a)
            if n == 6 and r == 4 and name not in ('kozlov', 'tent'):
                continue
            dmax = min(n+1, 6 if r <= 3 else 5)
            for d in shift_vectors(n, r, dmax):
                N = n + d[-1]
                M, pts, vs = brute_vertices(a, n, d)
                red = reduced(n, d)
                if red:
                    U = theta_list(a, n, d)
                    H = [(lab, u, sum(max(dot(u, vs[p][k]) for k in range(n)) for p in range(r))) for lab, u in U]
                    e1 = [QQ(1)] + [QQ(0)]*(N-1)
                for j, isv in M.items():
                    key = (n, r)
                    st = stats.setdefault(key, [0]*9)
                    st[0] += 1
                    c3 = cond3(n, d, j); t2 = thm2_direct(a, n, d, j); t2s = thm2_strict_cor(n, d, j)
                    if c3 != isv: st[1] += 1; fails.append(('B1', name, a, d, j, isv))
                    if t2 != isv or t2s != isv: st[2] += 1; fails.append(('B2', name, a, d, j, isv, t2, t2s))
                    if c3 != t2: st[3] += 1; fails.append(('B3', name, a, d, j))
                    if cond2(a, n, d, j) != isv: st[4] += 1; fails.append(('B4', name, a, d, j))
                    if red:
                        st[5] += 1
                        m = [d[p]+j[p] for p in range(r)]
                        x = pts[j]
                        tight = []
                        for lab, u, h in H:
                            ist = (dot(u, x) == h)
                            if ist != closed_form_tight(lab, n, d, m):
                                st[6] += 1; fails.append(('B5', name, a, d, j, lab, ist))
                            if ist: tight.append(u)
                        rk = matrix(QQ, tight + [e1]).rank()
                        if (rk == N) != isv:
                            st[7] += 1; fails.append(('B6', name, a, d, j, rk))
                        if isv:
                            phi = [sum(col) for col in zip(*tight)] if tight else [QQ(0)]*N
                            best = dot(phi, x)
                            if any(dot(phi, y) >= best for jj, y in pts.items() if jj != j and y != x) or \
                               any(y == x for jj, y in pts.items() if jj != j):
                                st[8] += 1; fails.append(('B7', name, a, d, j))
        log("n=%d r=%d done, cumulative %.0fs, tuples %d, fails so far %d" % (n, r, time.time()-t0, stats.get((n, r), [0])[0], len(fails)))
    log("")
    log("per (n,r): tuples | B1 c3!=brute | B2 thm2!=brute | B3 c3!=thm2 | B4 c2!=brute | reduced tuples | B5 tight!=closed form | B6 rank-crit!=brute | B7 phi fails")
    tot = [0]*9
    for key in sorted(stats):
        log("  %s: %s" % (key, stats[key]))
        tot = [x+y for x, y in zip(tot, stats[key])]
    log("TOTAL: %s" % tot)
    log("failures listed (first 30): %d" % len(fails))
    for f in fails[:30]:
        log("  " + repr(f))

def run_comb(log):
    # Prop 5 directly: (3) on a reduced config => tight (from argmax) + e1 has rank N.
    rng = random.Random(int(7))
    t0 = time.time(); total = 0; bad = 0; tot_conf = 0
    for n in range(2, 10):
        for r in range(2, 6):
            for name, a in legs(n, rng)[::2]:   # kozlov, 2^{i(n-i)}, randLC1
                cnt = 0
                for rest in itertools.product(range(1, n), repeat=r-1):
                    d = [0]
                    for g in rest: d.append(d[-1]+g)
                    d = tuple(d); N = n + d[-1]
                    if N > 16: continue
                    tot_conf += 1
                    vs = {p: [vtx(a, n, N, d[p], k) for k in range(1, n+1)] for p in range(r)}
                    U = theta_list(a, n, d)
                    H = [(u, [max(dot(u, vs[p][k]) for k in range(n)) for p in range(r)],
                          [[dot(u, vs[p][k]) for k in range(n)] for p in range(r)]) for _, u in U]
                    e1 = [QQ(1)] + [QQ(0)]*(N-1)
                    # sample tuples satisfying (3) (all if few)
                    alltup = itertools.product(range(1, n+1), repeat=r)
                    tup = [j for j in alltup if cond3(n, d, j)] if n**r <= 4000 else None
                    if tup is None:
                        tup = []
                        while len(tup) < 1500:
                            j = tuple(rng.randint(1, n) for _ in range(r))
                            if cond3(n, d, j): tup.append(j)
                    for j in tup:
                        tight = [u for u, hm, vals in H if all(vals[p][j[p]-1] == hm[p] for p in range(r))]
                        if matrix(QQ, tight + [e1]).rank() != N:
                            bad += 1
                            log("  FAIL n=%d r=%d a=%s d=%s j=%s" % (n, r, name, d, j))
                        total += 1; cnt += 1
        log("n=%d done: tuples so far %d, configs %d, failures %d, %.0fs" % (n, total, tot_conf, bad, time.time()-t0))
    log("COMB TOTAL tuples %d configs %d failures %d" % (total, tot_conf, bad))

if True:
    mode = sys.argv[1]
    out = open(sys.argv[2], 'a') if len(sys.argv) > 2 else None
    def log(s):
        print(s); sys.stdout.flush()
        if out: out.write(s + "\n"); out.flush()
    log("=== review_pairwise_hside_check.sage mode=%s ===" % mode)
    if mode == 'brute': run_brute(log)
    elif mode == 'comb': run_comb(log)
    elif mode == 'quick':
        # smoke test
        a = [binomial(4, i) for i in range(1, 5)]
        M, pts, vs = brute_vertices(a, 4, (0, 1, 2))
        log("koz4 (0,1,2): (2,4,3)->%s (2,2,3)->%s, #vertices %d" % (M[(2,4,3)], M[(2,2,3)], sum(M.values())))
    elif mode == 'weak':
        # H-side Prop. 6 (as a sufficient condition) for weakly LC a with slope plateaus,
        # and its coincidence with the direct note's Theorem 2 (which also claims necessity)
        def prop6(a, n, d, j):
            r = len(d); m = [d[p]+j[p] for p in range(r)]
            sig = lambda i: QQ(a[i])/a[i-1]
            for p in range(r-1):
                if d[p] == d[p+1]:
                    if j[p] != j[p+1]: return False
                    continue
                if m[p] > m[p+1]: return False
                B = d[p+1]+1; A = d[p]+n
                if B <= m[p] <= A and B <= m[p+1] <= A and m[p+1] != m[p]:
                    if m[p+1] == m[p]+1: return False
                    if not any(sig(c-d[p]) != sig(c-d[p+1]) for c in range(m[p]+1, m[p+1])): return False
            return True
        vecs = []
        for sl in [[2, 2, QQ(3)/2, QQ(3)/2], [3, 2, 2, 2], [2, 2, 2, 1], [3, 3, 1, 1], [2, 2, QQ(3)/2, QQ(3)/2, 1], [4, 2, 2, 2, 1], [3, 3, 3, 2, 2]]:
            a = [QQ(1)]
            for s in sl: a.append(a[-1]*s)
            vecs.append(a)
        for a in vecs:
            n = len(a); assert weakLC(a)
            tot = b6 = bt = bc = 0
            for r in (2, 3):
                for d in shift_vectors(n, r, min(n+1, 6)):
                    M, pts, vs = brute_vertices(a, n, d)
                    for j, isv in M.items():
                        tot += 1
                        p6 = prop6(a, n, d, j); t2 = thm2_direct(a, n, d, j)
                        bt += (t2 != isv); bc += (p6 != t2)
                        b6 += (p6 and not isv)
            log("weak a=%s: tuples %d, Prop6 true but not vertex %d, Thm2!=brute %d, Prop6!=Thm2 %d" % (a, tot, b6, bt, bc))
    elif mode == 'control':
        # (i) the note's worked example phi; (ii) negative controls: the checks must be able to fail
        a = [binomial(4, i) for i in range(1, 5)]; d = (0, 1, 2); n = 4; N = 6
        M, pts, vs = brute_vertices(a, n, d)
        j = (2, 4, 3); m = [d[p]+j[p] for p in range(3)]
        U = theta_list(a, n, d)
        tight = [(lab, u) for lab, u in U if dot(u, pts[j]) == sum(max(dot(u, vs[p][k]) for k in range(n)) for p in range(3))]
        phi = [sum(c) for c in zip(*[u for _, u in tight])]
        log("worked example j=(2,4,3): tight %s" % [lab for lab, _ in tight])
        log("  phi = %s ; per-summand values %s" % (phi, [[dot(phi, vs[p][k]) for k in range(n)] for p in range(3)]))
        for name, a in [('log-convex i!', [factorial(i) for i in range(1, 5)]), ('all-ones', [1]*4), ('geometric 3^i', [3**i for i in range(1, 5)])]:
            bad1 = bad2 = tot = 0
            for d in shift_vectors(4, 3, 5):
                M, pts, vs = brute_vertices(a, 4, d)
                for j, isv in M.items():
                    tot += 1
                    bad1 += (cond3(4, d, j) != isv)
                    bad2 += (cond2(a, 4, d, j) != isv)
            log("control %s, n=4 r=3: tuples %d, c3!=brute %d, c2!=brute %d" % (name, tot, bad1, bad2))
