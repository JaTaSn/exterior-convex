# review_hdesc_check.sage
# Changelog (reverse chronological):
#   2026-10-20  Section X also tests the rank-2 Theta-form (no (Ch2;1)); Z restricted to strict LC.
#   2026-10-20  Created. Independent referee check of
#               working-notes/kozlov-hdescription-proof-2026-10-20.org (Theorems A, B,
#               Corollaries C, D, Lemma B2 peel). Written from the note's TEXT only; does NOT
#               import or copy kozlov_hdesc_verify.sage.
#
# Sections:
#   A  rank 2, Theorem A transcribed literally (Ch1 with c(j), Ch2 incl. j=1, C, D, F):
#      Q == R; Q minus (Ch2;1) == R; facet count; which listed rows are facet-defining
#      (face dimension computed from R's vertices), and (Ch2;1) is the unique non-facet row
#      under strict log-concavity.
#   B  rank r, Corollary-C system (ties merged into weights, blocks at gaps >= n, uncovered
#      coordinates = 0, Theorem-B Theta-form per block): Q == R; facets == n*s (strict LC),
#      == #distinct normal classes (weak LC); random rational weights lambda on distinct shifts.
#   P  Lemma B2 peel cascade: points of Q_Theta (vertices + random convex combinations);
#      y in lambda1*angle(a), w zero on [1,d2], w(d2+1)=lambda2 a1, w-bar in Q_Theta(d'), recurse.
#   D  Corollary D: Koz(n;d) in R^{N+1} from F~_j, vs translated system, incl. ties and gaps>=n.
#   X  non-log-concave a (factorials = log-convex, random positive): R subset Q? Q subset R?
#   Z  mutation sanity: perturbing an offset of each row by +-1/1000 must change Q (rank 2).
#
# Usage: sage review_hdesc_check.sage [quick|full]

import itertools, sys, random, time
from sage.all import QQ, Polyhedron, binomial, vector, matrix, factorial

random.seed(int(20261020))
MODE = sys.argv[1] if len(sys.argv) > 1 else 'quick'
FAIL = []

def log(*s):
    print(*s); sys.stdout.flush()

def check(cond, msg):
    if not cond:
        FAIL.append(msg); log('FAIL:', msg)
    return cond

# ---------------------------------------------------------------- leg vectors
def kozlov(n): return [QQ(binomial(n, i)) for i in range(1, n+1)]
def ones(n): return [QQ(1)]*n
def tent(n): return [QQ(i*(n+1-i)) for i in range(1, n+1)]
def geometric(n, q=3): return [QQ(q)**i for i in range(n)]
def from_slopes(a1, sig):
    a = [QQ(a1)]
    for s in sig: a.append(a[-1]*s)
    return a
def rand_strict_lc(n):
    s = sorted(set(QQ(random.randint(1, 40))/random.randint(1, 12) for _ in range(4*n)), reverse=True)
    while len(s) < n-1: s.append(s[-1]/2)
    sig = sorted(random.sample(s, n-1), reverse=True)
    return from_slopes(random.randint(1, 5), sig)
def rand_weak_lc(n):
    # non-increasing slopes with deliberate ties
    sig = []
    cur = QQ(random.randint(2, 9))/random.randint(1, 3)
    for i in range(n-1):
        if i > 0 and random.random() < 0.5: sig.append(sig[-1])
        else:
            cur = cur * QQ(random.randint(1, 4))/random.randint(4, 6) if i > 0 else cur
            sig.append(cur)
    sig = sorted(sig, reverse=True)
    return from_slopes(random.randint(1, 5), sig)
def rand_positive(n): return [QQ(random.randint(1, 12)) for _ in range(n)]
def is_lc(a, strict=False):
    s = [a[i+1]/a[i] for i in range(len(a)-1)]
    return all((s[i] > s[i+1]) if strict else (s[i] >= s[i+1]) for i in range(len(s)-1))

# ---------------------------------------------------------------- V-side
def vert(a, k, d, N, lam=1, base=0):
    """lam * shift^d v(k) in R^N (0-based list, coordinate c stored at c-1); base=1 adds deg-0 slot."""
    v = [QQ(0)]*(N+base)
    for i in range(k): v[base + d + i] = lam*a[i]
    return v
def angle_poly(a, d, N, lam=1):
    return Polyhedron(vertices=[vert(a, k, d, N, lam) for k in range(1, len(a)+1)], base_ring=QQ)
def R_poly(a, ds, lams=None):
    n = len(a); N = n + max(ds)
    lams = lams or [1]*len(ds)
    P = None
    for d, l in zip(ds, lams):
        S = angle_poly(a, d, N, l)
        P = S if P is None else P + S
    return P

# ---------------------------------------------------------------- H-side, Theorem A literal
def theoremA_rows(a, d):
    """Rows as (name, b, u) meaning b + u.x >= 0 in R^N; eqs separately. Read off the note §thmA."""
    n = len(a); N = n + d; m = n - d
    A = lambda s: a[s-1] if 1 <= s <= n else QQ(0)
    al = lambda s: a[s-1]
    def e(c, val):
        u = [QQ(0)]*N; u[c-1] = val; return u
    rows = []
    for j in range(1, n):
        t = j - d
        cj = A(t+1)/al(j+1) - A(t)/al(j)
        u = [QQ(0)]*N; u[j-1] += 1/al(j); u[j] += -1/al(j+1)
        rows.append((('Ch1', j), cj, u))         # x_j/a_j - x_{j+1}/a_{j+1} + c_j >= 0
    for j in range(1, n):
        u = [QQ(0)]*N; u[d+j-1] += 1/al(j); u[d+j] += -1/al(j+1)
        rows.append((('Ch2', j), QQ(0), u))
    rows.append((('C',), -al(1), e(d+1, 1)))
    rows.append((('D',), al(m+1), e(n+1, -1)))
    rows.append((('F',), QQ(0), e(N, 1)))
    eqs = [(-al(1), e(1, 1))]
    return rows, eqs

def poly_from(rows, eqs):
    return Polyhedron(ieqs=[[b]+list(u) for (_, b, u) in rows],
                      eqns=[[b]+list(u) for (b, u) in eqs], base_ring=QQ)

def face_dim(R, b, u):
    pts = [vector(QQ, v) for v in R.vertices_list() if b + vector(QQ, u)*vector(QQ, v) == 0]
    if not pts: return -1
    if len(pts) == 1: return 0
    M = matrix(QQ, [p - pts[0] for p in pts[1:]])
    return M.rank()

def valid_row(R, b, u):
    return all(b + vector(QQ, u)*vector(QQ, v) >= 0 for v in R.vertices_list())

# ---------------------------------------------------------------- H-side, Theorem B / Cor C
def theta_rows_block(a, ds, lams, N, cshift=0):
    """Theorem B system for one block: distinct shifts ds (absolute, first = block start),
    gaps <= n-1, weights lams; coordinates absolute in R^N. The block's own 'origin' is
    ds[0]; (E) is x(ds[0]+1) = lams[0] a(1). Returns rows, eqs."""
    n = len(a); r = len(ds)
    al = lambda s: a[s-1]
    W = lambda p: (ds[p]+1, ds[p]+n)
    def M(p, c):   # roof after window p (0-based p): sum over q>p, c in W(q)
        return sum((lams[q]*al(c-ds[q]) for q in range(p+1, r) if W(q)[0] <= c <= W(q)[1]), QQ(0))
    def ev(c, val):
        u = [QQ(0)]*N; u[c-1] = val; return u
    rows, eqs = [], []
    eqs.append((-lams[0]*al(1), ev(ds[0]+1, 1)))
    for p in range(r):
        lo = 1 if p == 0 else 2           # local link index j
        for j in range(lo, n):
            c = ds[p] + j
            # Theta(p;c) >= Theta(p;c+1): (x_c - M(p,c))/a_j - (x_{c+1} - M(p,c+1))/a_{j+1} >= 0
            u = [QQ(0)]*N; u[c-1] += 1/al(j); u[c] += -1/al(j+1)
            b = -M(p, c)/al(j) + M(p, c+1)/al(j+1)
            rows.append((('I', p+1, j), b, u))
    for p in range(1, r):
        rows.append((('C', p+1), -lams[p]*al(1), ev(ds[p]+1, 1)))
        e0 = ds[p-1] + n + 1
        rows.append((('D', p+1), M(p-1, e0), ev(e0, -1)))
    rows.append((('F',), QQ(0), ev(ds[-1]+n, 1)))
    return rows, eqs

def corC_system(a, dvec):
    n = len(a); N = n + max(dvec)
    vals = sorted(set(dvec)); mult = [dvec.count(v) for v in vals]
    blocks = [[0]]
    for i in range(1, len(vals)):
        if vals[i] - vals[i-1] <= n-1: blocks[-1].append(i)
        else: blocks.append([i])
    rows, eqs = [], []
    covered = set()
    for B in blocks:
        ds = [vals[i] for i in B]; lams = [QQ(mult[i]) for i in B]
        r_, e_ = theta_rows_block(a, ds, lams, N)
        rows += r_; eqs += e_
        for d in ds: covered |= set(range(d+1, d+n+1))
    for c in range(1, N+1):
        if c not in covered:
            u = [QQ(0)]*N; u[c-1] = 1; eqs.append((QQ(0), u))
    return rows, eqs, len(vals), len(blocks)

def normal_classes(rows, eqcoords):
    """distinct rows' normals mod the span of the equation unit vectors, up to positive scaling."""
    cls = set()
    for (_, b, u) in rows:
        v = [x if (i+1) not in eqcoords else 0 for i, x in enumerate(u)]
        nz = [x for x in v if x != 0]
        s = abs(nz[0]) if nz else 1
        cls.add(tuple(x/s for x in v))
    return len(cls)

# ---------------------------------------------------------------- Section A
def sectionA(nmax, families):
    log('== Section A: Theorem A (rank 2) transcribed literally ==')
    cnt = 0
    for n in range(2, nmax+1):
        for name, f in families:
            a = f(n)
            if not is_lc(a): continue
            strict = is_lc(a, True)
            for d in range(1, n):
                rows, eqs = theoremA_rows(a, d)
                R = R_poly(a, [0, d])
                Q = poly_from(rows, eqs)
                ok = check(Q == R, f'A: Q!=R n={n} d={d} a={name} {a}')
                rows2 = [r for r in rows if r[0] != ('Ch2', 1)]
                ok &= check(poly_from(rows2, eqs) == R, f'A: Q-(Ch2;1)!=R n={n} d={d} {name}')
                ok &= check(R.dim() == n + d - 1, f'A: dim n={n} d={d} {name}')
                tight = all(min(b + vector(QQ, u)*vector(QQ, v) for v in R.vertices_list()) == 0
                            for (_, b, u) in rows)
                ok &= check(tight, f'A: some row not tight n={n} d={d} {name}')
                nonfacet = [nm for (nm, b, u) in rows if face_dim(R, b, u) != R.dim()-1]
                if strict:
                    ok &= check(R.n_inequalities() == 2*n, f'A: facets {R.n_inequalities()} != 2n n={n} d={d} {name}')
                    ok &= check(nonfacet == [('Ch2', 1)], f'A: nonfacet rows {nonfacet} n={n} d={d} {name}')
                else:
                    ok &= check(all(nm == ('Ch2', 1) for nm in nonfacet), f'A weak: nonfacet {nonfacet} n={n} d={d} {name}')
                    ok &= check(R.n_inequalities() == normal_classes(rows2, {1}),
                                f'A weak: facets {R.n_inequalities()} vs classes n={n} d={d} {name}')
                    if name == 'ones':
                        m = n - d
                        ok &= check(R.n_inequalities() == (n+d+2 if m >= 2 else n+d+1), f'A ones count n={n} d={d}')
                cnt += 1
    log(f'   section A: {cnt} configurations')

# ---------------------------------------------------------------- Section B
def sectionB(cases):
    log('== Section B: Corollary C / Theorem B, rank r ==')
    cnt = 0
    for (name, a, dvec) in cases:
        n = len(a)
        rows, eqs, s, nb = corC_system(a, dvec)
        R = R_poly(a, dvec)
        Q = poly_from(rows, eqs)
        check(Q == R, f'B: Q!=R {name} n={n} d={dvec}')
        eqc = set(i+1 for (b, u) in eqs for i, x in enumerate(u) if x != 0)
        if is_lc(a, True):
            check(R.n_inequalities() == n*s, f'B: facets {R.n_inequalities()} != n*s={n*s} {name} d={dvec}')
        check(R.n_inequalities() == normal_classes(rows, eqc),
              f'B: facets {R.n_inequalities()} vs classes {normal_classes(rows, eqc)} {name} d={dvec}')
        cnt += 1
    log(f'   section B: {cnt} configurations')

def sectionB_weights(cases):
    log('== Section B-lambda: Theorem B with random rational weights, distinct shifts ==')
    cnt = 0
    for (name, a, ds) in cases:
        n = len(a); N = n + ds[-1]
        lams = [QQ(random.randint(1, 9))/random.randint(1, 4) for _ in ds]
        rows, eqs = theta_rows_block(a, ds, lams, N)
        R = R_poly(a, ds, lams)
        check(poly_from(rows, eqs) == R, f'Bl: Q!=R {name} d={ds} lam={lams}')
        if is_lc(a, True):
            check(R.n_inequalities() == n*len(ds), f'Bl: count {name} d={ds}')
        cnt += 1
    log(f'   section B-lambda: {cnt} configurations')

# ---------------------------------------------------------------- Section P (peel)
def in_theta(a, ds, lams, x, Nloc):
    rows, eqs = theta_rows_block(a, ds, lams, Nloc)
    xv = vector(QQ, x)
    return all(b + vector(QQ, u)*xv >= 0 for (_, b, u) in rows) and \
           all(b + vector(QQ, u)*xv == 0 for (b, u) in eqs)

def in_angle(a, lam, y):
    n = len(a)
    if any(t != 0 for t in y[n:]): return False
    mu = [y[i]/a[i] for i in range(n)]
    return mu[0] == lam and all(mu[i] >= mu[i+1] for i in range(n-1)) and mu[-1] >= 0

def peel_cascade(a, ds, lams, x):
    """ds starts at 0. Returns True iff every level of the cascade satisfies B2 (i)-(iii)."""
    n = len(a); N = n + ds[-1]
    if not in_theta(a, ds, lams, x, N): return 'input-not-in-Q'
    if len(ds) == 1:
        return in_angle(a, lams[0], x)
    al = lambda s: a[s-1]
    def M1(c):
        return sum((lams[q]*al(c-ds[q]) for q in range(1, len(ds)) if ds[q]+1 <= c <= ds[q]+n), QQ(0))
    y = [QQ(0)]*N
    for c in range(1, n+1):
        y[c-1] = al(c)*max(QQ(0), (x[c-1] - M1(c))/al(c))
    w = [x[i] - y[i] for i in range(N)]
    if not in_angle(a, lams[0], y): return False
    d2 = ds[1]
    if any(w[c-1] != 0 for c in range(1, d2+1)): return False
    if w[d2] != lams[1]*al(1): return False
    wbar = w[d2:]
    return peel_cascade(a, [d - d2 for d in ds[1:]], lams[1:], wbar)

def sectionP(cases, npts=25):
    log('== Section P: Lemma B2 peel cascade ==')
    cnt = 0; pts = 0
    for (name, a, ds, lams) in cases:
        n = len(a); N = n + ds[-1]
        rows, eqs = theta_rows_block(a, ds, lams, N)
        Q = poly_from(rows, eqs)
        V = [vector(QQ, v) for v in Q.vertices_list()]
        sample = list(V)
        for _ in range(npts):
            k = random.randint(2, 4)
            ch = random.sample(V, min(k, len(V)))
            wts = [QQ(random.randint(1, 7)) for _ in ch]
            sample.append(sum(wt*v for wt, v in zip(wts, ch))/sum(wts))
        for x in sample:
            res = peel_cascade(a, ds, lams, list(x))
            check(res is True, f'P: peel fails ({res}) {name} d={ds} lam={lams} x={list(x)}')
            pts += 1
        cnt += 1
    log(f'   section P: {cnt} configurations, {pts} points')

# ---------------------------------------------------------------- Section D (Koz(n;d) itself)
def sectionD(cases):
    log('== Section D: Corollary D, Koz(n;d) in R^{N+1} ==')
    cnt = 0
    for (n, dvec) in cases:
        N = n + max(dvec); a = kozlov(n)
        P = None
        for d in dvec:
            V = []
            for j in range(1, n+1):
                v = [QQ(0)]*(N+1); v[d] = 1
                for i in range(1, j+1): v[d+i] = binomial(n, i)
                V.append(v)
            S = Polyhedron(vertices=V, base_ring=QQ)
            P = S if P is None else P + S
        rows, eqs, s, nb = corC_system(a, dvec)
        t = [QQ(0)]*(N+1)
        for d in dvec:
            if d >= 1: t[d] += 1
        # translate: b + u.(x' - t') >= 0 with x' = x[1..N]
        tt = vector(QQ, t[1:])
        ieq = [[b - vector(QQ, u)*tt, 0] + list(u) for (_, b, u) in rows]
        eqn = [[b - vector(QQ, u)*tt, 0] + list(u) for (b, u) in eqs]
        e0 = [QQ(-dvec.count(0)), 1] + [0]*N
        Q = Polyhedron(ieqs=ieq, eqns=eqn + [e0], base_ring=QQ)
        check(Q == P, f'D: Koz(n;d) mismatch n={n} d={dvec}')
        check(P.n_inequalities() == n*s, f'D: count {P.n_inequalities()} != {n*s} n={n} d={dvec}')
        cnt += 1
    log(f'   section D: {cnt} configurations')

# ---------------------------------------------------------------- Section X (non-LC)
def sectionX(tests):
    log('== Section X: non-log-concave a ==')
    stats = {}
    for (name, a, dvec, kind) in tests:
        if kind == 'A':
            rows, eqs = theoremA_rows(a, dvec[1])
        elif kind == 'T':
            rows, eqs = theta_rows_block(a, dvec, [1]*len(dvec), len(a)+dvec[-1])
        else:
            rows, eqs, s, nb = corC_system(a, dvec)
        R = R_poly(a, dvec); Q = poly_from(rows, eqs)
        RinQ = all(Q.contains(v) for v in R.vertices_list())
        QinR = all(R.contains(v) for v in Q.vertices_list()) and Q.n_lines() == 0 and Q.n_rays() == 0
        key = (name.split(':')[0], len(dvec), kind)
        st = stats.setdefault(key, [0, 0, 0])
        st[0] += 1; st[1] += (not RinQ); st[2] += (not QinR)
        if name.startswith('fact'):
            log(f'   {name} [{kind}] a={list(a)} d={dvec}: R subset Q: {RinQ}; Q subset R: {QinR}')
        if len(dvec) == 2:
            check(QinR, f'X: rank-2 completeness fails {name} a={a} d={dvec}')
        if not QinR:
            log(f'   rank-{len(dvec)} Q not subset R: {name} a={a} d={dvec}')
    for k, v in sorted(stats.items()):
        log(f'   {k}: configs={v[0]}  R not in Q: {v[1]}  Q not in R: {v[2]}')

# ---------------------------------------------------------------- Section Z (mutations)
def sectionZ(cfgs):
    log('== Section Z: mutation sanity (rank 2, Theorem A minus (Ch2;1)) ==')
    det = tot = 0
    for (a, d) in cfgs:
        rows, eqs = theoremA_rows(a, d)
        rows = [r for r in rows if r[0] != ('Ch2', 1)]
        R = R_poly(a, [0, d])
        for i in range(len(rows)):
            for eps in (QQ(1)/1000, -QQ(1)/1000):
                rr = list(rows); nm, b, u = rr[i]; rr[i] = (nm, b + eps, u)
                tot += 1; det += (poly_from(rr, eqs) != R)
    check(det == tot, f'Z: only {det}/{tot} mutations detected')
    log(f'   section Z: {det}/{tot} mutations detected')

# ---------------------------------------------------------------- driver
def dvecs(n, r, gmax, Nmax):
    out = []
    for gaps in itertools.product(range(0, gmax+1), repeat=r-1):
        ds = [0]
        for g in gaps: ds.append(ds[-1]+g)
        if n + ds[-1] <= Nmax: out.append(ds)
    return out

if True:
    t0 = time.time()
    full = (MODE == 'full')
    nA = 9 if full else 6
    famsA = [('kozlov', kozlov), ('ones', ones), ('tent', tent), ('geom3', geometric),
             ('rstrict', rand_strict_lc), ('rweak', rand_weak_lc), ('rweak2', rand_weak_lc)]
    sectionA(nA, famsA)
    log(f'   [t={time.time()-t0:.0f}s]')

    # Section B: ranks 3-4, n <= 5, every gap pattern in [0, n+1] up to N bound, incl. ties, gaps>=n
    casesB = []
    for n in range(2, (6 if full else 5)):
        for r in (2, 3, 4):
            Nmax = 13 if full else 11
            for ds in dvecs(n, r, n+1, Nmax):
                for name, f in [('kozlov', kozlov), ('rstrict', rand_strict_lc), ('rweak', rand_weak_lc), ('ones', ones)]:
                    if r == 4 and name in ('rweak', 'ones') and random.random() < 0.6: continue
                    casesB.append((name, f(n), ds))
    sectionB(casesB)
    log(f'   [t={time.time()-t0:.0f}s]')

    casesBl = []
    for n in range(2, 6):
        for r in (2, 3, 4):
            for ds in dvecs(n, r, n-1, 13):
                if len(set(ds)) < r: continue
                for name, f in [('kozlov', kozlov), ('rweak', rand_weak_lc)]:
                    casesBl.append((name, f(n), ds))
    sectionB_weights(casesBl[::(1 if full else 3)])
    log(f'   [t={time.time()-t0:.0f}s]')

    casesP = []
    for n in range(2, 6):
        for r in (2, 3, 4):
            for ds in dvecs(n, r, n-1, 12):
                if len(set(ds)) < r: continue
                for name, f in [('kozlov', kozlov), ('rstrict', rand_strict_lc), ('rweak', rand_weak_lc)]:
                    lams = [QQ(random.randint(1, 5))/random.randint(1, 3) for _ in ds]
                    casesP.append((name, f(n), ds, lams))
    sectionP(casesP[::(1 if full else 4)], npts=(25 if full else 10))
    log(f'   [t={time.time()-t0:.0f}s]')

    casesD = [(n, ds) for n in range(2, 6) for r in (2, 3) for ds in dvecs(n, r, n+1, 11)]
    sectionD(casesD[::(1 if full else 3)])
    log(f'   [t={time.time()-t0:.0f}s]')

    testsX = []
    for n in range(3, 7):
        fa = [QQ(factorial(i)) for i in range(1, n+1)]
        for d in range(1, n):
            testsX.append((f'fact:n={n}', fa, [0, d], 'A'))
            testsX.append((f'fact:n={n}', fa, [0, d], 'T'))
    for _ in range(200 if full else 60):
        n = random.randint(3, 6); a = rand_positive(n); d = random.randint(1, n-1)
        testsX.append(('rpos2', a, [0, d], 'A'))
        testsX.append(('rpos2', a, [0, d], 'T'))
    for _ in range(150 if full else 40):
        n = random.randint(3, 5); a = rand_positive(n)
        g1 = random.randint(1, n-1); g2 = random.randint(1, n-1)
        testsX.append(('rpos3', a, [0, g1, g1+g2], 'C'))
    for _ in range(60 if full else 15):
        n = random.randint(3, 4); a = rand_positive(n)
        g = [random.randint(1, n-1) for _ in range(3)]
        testsX.append(('rpos4', a, [0, g[0], g[0]+g[1], g[0]+g[1]+g[2]], 'C'))
    sectionX(testsX)
    log(f'   [t={time.time()-t0:.0f}s]')

    # strictly log-concave only: for weakly LC a (e.g. all-ones) duplicated normal classes make
    # loosening ONE copy undetectable by design (2026-10-20 quick run: ones(5), d=2, Ch1;4 / Ch2;2).
    sectionZ([(kozlov(5), 2), (kozlov(6), 1), (kozlov(6), 4), (rand_strict_lc(5), 3), (rand_strict_lc(7), 3)])
    log(f'TOTAL FAILURES: {len(FAIL)}   time {time.time()-t0:.0f}s')
