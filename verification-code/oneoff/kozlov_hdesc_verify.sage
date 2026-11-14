# kozlov_hdesc_verify.sage
#
# Changelog (reverse chronological):
#   2026-10-20  (later) Full-mode ranges raised (rank 2 to n = 10; rank r to
#               N <= 15); S0 mutation check added.
#   2026-10-20  Created (overnight article-3 push).  Independent verification
#               record for working-notes/kozlov-hdescription-proof-2026-10-20.org.
#               Written from that note's statements, NOT reusing the 2026-09-06
#               scripts, so that a slip in either is exposed.  Sections:
#                 S0  mutation sanity check: deleting any Theta row, or
#                     tightening its offset, changes the polytope.
#                 S1  rank 2, conj-kozlov-hrep2 transcribed LITERALLY (offsets
#                     c_j, both chains incl. second-chain j=1, three extras):
#                     Q == R, facet count, the redundant member, n = 2..8,
#                     every d, several leg vectors; plus the vertex set of
#                     thm-kozlov-matrix for the Kozlov vector.
#                 S2  rank 2, conj-ones-hrep transcribed literally; Q == R and
#                     the facet counts n+d+2 / n+d+1.
#                 S3  rank r, weighted Theta-form (distinct shifts d, weights
#                     lambda > 0): Q == R, facet count == #distinct normal
#                     classes in the list (== r*n when strictly log-concave).
#                 S4  the peel cascade, at EVERY level: y in lambda_1*angle(a),
#                     w == 0 below window 2, w in the smaller Theta-system;
#                     exact rationals, vertices + random boundary points.
#                 S5  arbitrary shift vectors (ties, gaps >= n): facets == n*s.
#                 S6  the Kozlov polytope itself (degree-0 coordinate kept,
#                     translation by e_{d_p}): the translated system.
#                 S7  negative controls: non-log-concave a (which inclusion
#                     fails), and completeness for arbitrary positive a.
#               Run:  sage kozlov_hdesc_verify.sage [quick]
#
# Driver at top level (no __main__ guard -- .sage files run as sage.all).

import itertools, sys, random, time
QUICK = ('quick' in sys.argv)
random.seed(int(20261020))
T0 = time.time()

def log(s):
    print(s); sys.stdout.flush()

# ---------------------------------------------------------------- basics
def kozlov(n):  return [QQ(binomial(n, j)) for j in range(1, n+1)]
def ones(n):    return [QQ(1)]*n
def tent(n):    return [QQ(i*(n+1-i)) for i in range(1, n+1)]
def twopow(n):  return [QQ(2)**(i*(n-i)) for i in range(1, n+1)]
def geom(n):    return [QQ(3)**i for i in range(1, n+1)]          # weakly LC (slope const)
def rand_strict_lc(n):
    # a(1) random, slopes strictly decreasing random rationals
    s = sorted([QQ(random.randint(1, 60))/random.randint(1, 12) for _ in range(n-1)], reverse=True)
    s = [s[i] + QQ(n-1-i)/97 for i in range(n-1)]                 # break ties, keep decreasing
    a = [QQ(random.randint(1, 9))]
    for x in s: a.append(a[-1]*x)
    return a
def rand_positive(n):
    return [QQ(random.randint(1, 30)) for _ in range(n)]

def slopes(a): return [a[i+1]/a[i] for i in range(len(a)-1)]
def is_lc(a, strict=False):
    s = slopes(a)
    return all((s[i] > s[i+1]) if strict else (s[i] >= s[i+1]) for i in range(len(s)-1))

def simplex_verts(a, d, N, lam=1):
    n = len(a)
    return [vector(QQ, [0]*d + [lam*a[i] for i in range(k)] + [0]*(N-d-k)) for k in range(1, n+1)]

def build_R(a, ds, lams=None):
    """Minkowski sum of lam_p * shift^{d_p} angle(a) in R^N, N = n + max d."""
    n = len(a); N = n + max(ds)
    if lams is None: lams = [1]*len(ds)
    P = None
    for d, l in zip(ds, lams):
        S = Polyhedron(vertices=simplex_verts(a, d, N, l), base_ring=QQ)
        P = S if P is None else P + S
    return P

def ineq_row(coeffs, b, N):
    """Sage ieq row for  b + coeffs.x >= 0 (coeffs: dict 1-based coord -> value)."""
    return [QQ(b)] + [QQ(coeffs.get(c, 0)) for c in range(1, N+1)]

def facet_count(P):
    return len([h for h in P.Hrepresentation() if h.is_inequality()])

# ---------------------------------------------------------------- Theta system
def theta_system(a, ds, lams):
    """Weighted Theta-form for DISTINCT increasing shifts ds (ds[0]=0, gaps <= n-1).
       Returns (eqns, ieqs) as lists of (label, coeffs, b) meaning coeffs.x + b (=,>=) 0."""
    n = len(a); r = len(ds); N = n + ds[-1]
    def A(i): return a[i-1] if 1 <= i <= n else QQ(0)
    def M(p, c):                 # roof of windows strictly after p (p 1-based)
        return sum((lams[q-1]*A(c-ds[q-1]) for q in range(p+1, r+1) if 1 <= c-ds[q-1] <= n), QQ(0))
    eqns = [('E', {1: QQ(1)}, -lams[0]*a[0])]
    ieqs = []
    for p in range(1, r+1):
        d = ds[p-1]
        for j in range(1 if p == 1 else 2, n):
            c = d + j
            # (x_c - M_c)/a_j - (x_{c+1} - M_{c+1})/a_{j+1} >= 0
            ieqs.append((('I', p, j), {c: 1/a[j-1], c+1: -1/a[j]}, -M(p, c)/a[j-1] + M(p, c+1)/a[j]))
    for p in range(2, r+1):
        ieqs.append((('C', p), {ds[p-1]+1: QQ(1)}, -lams[p-1]*a[0]))
        e = ds[p-2] + n + 1
        ieqs.append((('D', p), {e: QQ(-1)}, M(p-1, e)))
    ieqs.append((('F',), {N: QQ(1)}, QQ(0)))
    return eqns, ieqs

def theta_polyhedron(a, ds, lams):
    N = len(a) + ds[-1]
    eqns, ieqs = theta_system(a, ds, lams)
    return Polyhedron(eqns=[ineq_row(c, b, N) for _, c, b in eqns],
                      ieqs=[ineq_row(c, b, N) for _, c, b in ieqs], base_ring=QQ)

def normal_class(coeffs):
    """Outward normal mod e_1, up to positive scaling: canonical tuple."""
    items = sorted((c, v) for c, v in coeffs.items() if c != 1 and v != 0)
    if not items: return None
    s = abs(items[0][1])
    return tuple((c, v/s) for c, v in items)

def satisfies(x, eqns, ieqs):
    def val(coeffs, b): return sum(v*x[c-1] for c, v in coeffs.items()) + b
    return all(val(c, b) == 0 for _, c, b in eqns) and all(val(c, b) >= 0 for _, c, b in ieqs)

def violated(x, eqns, ieqs):
    def val(coeffs, b): return sum(v*x[c-1] for c, v in coeffs.items()) + b
    return [l for l, c, b in eqns if val(c, b) != 0] + [l for l, c, b in ieqs if val(c, b) < 0]

# ---------------------------------------------------------------- S1: conj-kozlov-hrep2 literal
def conj_hrep2_system(a, d):
    n = len(a); N = n + d
    def A(s): return a[s-1] if 1 <= s <= n else QQ(0)
    eqns = [('x1', {1: QQ(1)}, -a[0])]
    ieqs = []
    for j in range(1, n):
        t = j - d
        cj = A(t+1)/a[j] - A(t)/a[j-1]
        ieqs.append((('chain1', j), {j: 1/a[j-1], j+1: -1/a[j]}, cj))      # x_j/a_j - x_{j+1}/a_{j+1} + c_j >= 0
    for j in range(1, n):
        ieqs.append((('chain2', j), {d+j: 1/a[j-1], d+j+1: -1/a[j]}, QQ(0)))
    ieqs.append((('x_{d+1}>=a1',), {d+1: QQ(1)}, -a[0]))
    ieqs.append((('x_{n+1}<=a(m+1)',), {n+1: QQ(-1)}, A(n-d+1)))
    ieqs.append((('x_N>=0',), {N: QQ(1)}, QQ(0)))
    return eqns, ieqs

def kozlov_matrix_zero(n, d, i, j):
    m = n - d; t = i - d
    return 1 <= t <= m and 1 <= j <= m and (j < t or j == t+1)

def S1():
    log("\n== S1: rank 2, conj-kozlov-hrep2 transcribed literally ==")
    bad = 0; cnt = 0
    nmax = 7 if QUICK else 10
    for n in range(2, nmax+1):
        vecs = [('kozlov', kozlov(n)), ('tent', tent(n)), ('2^{i(n-i)}', twopow(n)),
                ('randLC', rand_strict_lc(n))]
        for name, a in vecs:
            strict = is_lc(a, True)
            for d in range(1, n):
                N = n + d
                R = build_R(a, [0, d])
                eqns, ieqs = conj_hrep2_system(a, d)
                Q = Polyhedron(eqns=[ineq_row(c, b, N) for _, c, b in eqns],
                               ieqs=[ineq_row(c, b, N) for _, c, b in ieqs], base_ring=QQ)
                eq = (Q == R); fc = facet_count(R)
                # which listed inequalities are facet-defining? (face of R has dim dim R - 1)
                nonfacet = []
                for lab, c, b in ieqs:
                    H = Polyhedron(eqns=[ineq_row(c, b, N)], base_ring=QQ)
                    F = R.intersection(H)
                    if F.dim() != R.dim() - 1: nonfacet.append(lab)
                expected_nonfacet = [('chain2', 1)]
                ok = eq and fc == 2*n and nonfacet == expected_nonfacet and R.dim() == N-1
                if name == 'kozlov':
                    V = set(tuple(v) for v in R.vertices_list())
                    U = simplex_verts(a, 0, N); W = simplex_verts(a, d, N)
                    pred = set(tuple(U[i-1]+W[j-1]) for i in range(1, n+1) for j in range(1, n+1)
                               if not kozlov_matrix_zero(n, d, i, j))
                    vok = (V == pred) and len(V) == n*n - (n-d-1)*(n-d+2)//2
                    ok = ok and vok
                cnt += 1
                if not ok:
                    bad += 1
                    log("  FAIL n=%d d=%d a=%s: Q==R %s, facets %d (2n=%d), nonfacets %s, strictLC %s"
                        % (n, d, name, eq, fc, 2*n, nonfacet, strict))
        log("  n=%d done (%d configs so far, %d failures)  [%.0fs]" % (n, cnt, bad, time.time()-T0))
    log("S1 result: %d configurations, %d failures" % (cnt, bad))
    return bad == 0

# ---------------------------------------------------------------- S2: conj-ones-hrep literal
def conj_ones_system(n, d):
    N = n + d
    eqns = [('x1', {1: QQ(1)}, QQ(-1))]
    ieqs = []
    for c in range(1, d):   ieqs.append((('b1', c), {c: 1, c+1: -1}, 0))       # x1>=...>=x_d
    ieqs.append((('bump',), {d: 1, d+1: -1}, 1))                               # x_{d+1} <= x_d + 1
    ieqs.append((('cap',), {d+1: 1}, -1))                                      # x_{d+1} >= 1
    for c in range(d+1, n): ieqs.append((('ov', c), {c: 1, c+1: -1}, 0))
    ieqs.append((('tr',), {n: 1, n+1: -1}, 0))
    ieqs.append((('cap2',), {n+1: -1}, 1))
    for c in range(n+1, N): ieqs.append((('b2', c), {c: 1, c+1: -1}, 0))
    ieqs.append((('floor',), {N: 1}, 0))
    return eqns, ieqs

def S2():
    log("\n== S2: rank 2, conj-ones-hrep transcribed literally (all-ones) ==")
    bad = 0; cnt = 0
    for n in range(2, (7 if QUICK else 10)+1):
        for d in range(1, n):
            N = n + d; m = n - d
            R = build_R(ones(n), [0, d])
            eqns, ieqs = conj_ones_system(n, d)
            Q = Polyhedron(eqns=[ineq_row(c, b, N) for _, c, b in eqns],
                           ieqs=[ineq_row(c, b, N) for _, c, b in ieqs], base_ring=QQ)
            th = theta_polyhedron(ones(n), [0, d], [1, 1])
            fc = facet_count(R); want = n+d+2 if m >= 2 else n+d+1
            # count of distinct normal classes in the Theta list
            _, tie = theta_system(ones(n), [0, d], [1, 1])
            ncl = len(set(normal_class(c) for _, c, b in tie))
            ok = (Q == R) and (th == R) and fc == want and ncl == fc
            cnt += 1
            if not ok:
                bad += 1; log("  FAIL n=%d d=%d: Q==R %s, Theta==R %s, facets %d want %d, classes %d"
                              % (n, d, Q == R, th == R, fc, want, ncl))
    log("S2 result: %d configurations, %d failures" % (cnt, bad))
    return bad == 0

# ---------------------------------------------------------------- S3: weighted Theta-form, rank r
def shift_patterns(n, r, Nmax):
    for gs in itertools.product(range(1, n), repeat=r-1):
        ds = [0]
        for g in gs: ds.append(ds[-1] + g)
        if n + ds[-1] <= Nmax: yield ds

def S3():
    log("\n== S3: weighted Theta-form, rank r, distinct shifts, gaps <= n-1 ==")
    bad = 0; cnt = 0
    Nmax = 11 if QUICK else 15
    for n in range(2, 8):
        for r in range(1, 6):
            if n >= 6 and r > 3: continue
            if n == 5 and r > 4: continue
            if n == 4 and r > 4: continue
            for ds in shift_patterns(n, r, Nmax):
                vecs = [('kozlov', kozlov(n)), ('randLC', rand_strict_lc(n)), ('ones', ones(n))]
                if n <= 4: vecs.append(('geom', geom(n)))
                for name, a in vecs:
                    for lamkind in ('unit', 'rand'):
                        if lamkind == 'unit': lams = [QQ(1)]*r
                        else: lams = [QQ(random.randint(1, 5))/random.randint(1, 3) for _ in range(r)]
                        if lamkind == 'rand' and name in ('ones', 'geom') and r > 2: continue
                        R = build_R(a, ds, lams)
                        Q = theta_polyhedron(a, ds, lams)
                        _, ieqs = theta_system(a, ds, lams)
                        ncl = len(set(normal_class(c) for _, c, b in ieqs))
                        fc = facet_count(R)
                        ok = (Q == R) and fc == ncl and R.dim() == n + ds[-1] - 1
                        if is_lc(a, True): ok = ok and fc == r*n and ncl == r*n
                        cnt += 1
                        if not ok:
                            bad += 1
                            log("  FAIL n=%d ds=%s a=%s lam=%s: Q==R %s facets %d classes %d rn %d"
                                % (n, ds, name, lams, Q == R, fc, ncl, r*n))
            log("  n=%d r=%d done (%d configs, %d failures) [%.0fs]" % (n, r, cnt, bad, time.time()-T0))
    log("S3 result: %d configurations, %d failures" % (cnt, bad))
    return bad == 0

# ---------------------------------------------------------------- S4: the peel cascade
def in_scaled_simplex(y, a, lam):
    """y in lam*angle(a) (coords 1..n of y; rest must be 0)."""
    n = len(a)
    if any(v != 0 for v in y[n:]): return False
    mu = [y[i]/a[i] for i in range(n)]
    return mu[0] == lam and all(mu[i] >= mu[i+1] for i in range(n-1)) and mu[-1] >= 0

def peel(a, ds, lams, x):
    n = len(a); r = len(ds)
    def A(i): return a[i-1] if 1 <= i <= n else QQ(0)
    def M1(c): return sum((lams[q-1]*A(c-ds[q-1]) for q in range(2, r+1) if 1 <= c-ds[q-1] <= n), QQ(0))
    y = [QQ(0)]*len(x)
    for c in range(1, n+1):
        th = (x[c-1] - M1(c))/a[c-1]
        y[c-1] = a[c-1]*max(QQ(0), th)
    w = [x[i] - y[i] for i in range(len(x))]
    return y, w

def cascade_check(a, ds, lams, x):
    """Returns None if every level is fine, else a description of the failure."""
    level = 0
    while len(ds) >= 2:
        eqns, ieqs = theta_system(a, ds, lams)
        if not satisfies(x, eqns, ieqs): return "level %d: input not in Q_Theta (%s)" % (level, violated(x, eqns, ieqs))
        y, w = peel(a, ds, lams, x)
        if not in_scaled_simplex(y, a, lams[0]): return "level %d: y not in lam1*angle" % level
        d2 = ds[1]
        if any(w[c] != 0 for c in range(d2)): return "level %d: w nonzero below window 2" % level
        x = w[d2:]; ds = [d - d2 for d in ds[1:]]; lams = lams[1:]; level += 1
    if not in_scaled_simplex(x, a, lams[0]): return "base: last remainder not in lam*angle"
    return None

def S4():
    log("\n== S4: the peel cascade, every level ==")
    bad = 0; cnt = 0; pts = 0
    for n in range(2, 9):
        for r in range(2, 6):
            if n >= 5 and r > 3: continue
            if n == 4 and r > 4: continue
            for ds in shift_patterns(n, r, 12 if QUICK else 15):
                for name, a in (('kozlov', kozlov(n)), ('randLC', rand_strict_lc(n)), ('ones', ones(n))):
                    for lams in ([QQ(1)]*r, [QQ(random.randint(1, 4)) for _ in range(r)]):
                        Q = theta_polyhedron(a, ds, lams)
                        V = [vector(QQ, v) for v in Q.vertices_list()]
                        samples = list(V)
                        for _ in range(40):
                            k = random.randint(2, 4)
                            S = random.sample(V, min(k, len(V)))
                            wts = [QQ(random.randint(1, 9)) for _ in S]; tot = sum(wts)
                            samples.append(sum((wt/tot)*v for wt, v in zip(wts, S)))
                        cnt += 1
                        for x in samples:
                            pts += 1
                            res = cascade_check(a, ds, lams, list(x))
                            if res is not None:
                                bad += 1; log("  FAIL n=%d ds=%s a=%s lams=%s: %s" % (n, ds, name, lams, res)); break
        log("  n=%d done (%d configs, %d points, %d failures) [%.0fs]" % (n, cnt, pts, bad, time.time()-T0))
    log("S4 result: %d configurations, %d sample points, %d failures" % (cnt, pts, bad))
    return bad == 0

# ---------------------------------------------------------------- S5: arbitrary shift vectors
def S5():
    log("\n== S5: arbitrary shift vectors (ties, gaps >= n): facets == n*s (Kozlov) ==")
    bad = 0; cnt = 0
    for n in range(2, 6):
        for r in range(2, 5):
            for gs in itertools.product(range(0, n+2), repeat=r-1):
                ds = [0]
                for g in gs: ds.append(ds[-1] + g)
                if n + ds[-1] > (11 if QUICK else 12): continue
                if all(g in range(1, n) for g in gs): continue   # covered by S3
                s = len(set(ds))
                R = build_R(kozlov(n), ds)
                fc = facet_count(R); cnt += 1
                if fc != n*s:
                    bad += 1; log("  FAIL n=%d ds=%s: facets %d, n*s=%d" % (n, ds, fc, n*s))
    log("S5 result: %d configurations, %d failures" % (cnt, bad))
    return bad == 0

# ---------------------------------------------------------------- S6: the Kozlov polytope itself
def S6():
    log("\n== S6: Koz(n;d) in R^{N+1} (degree 0 kept) vs the translated Theta-system ==")
    bad = 0; cnt = 0
    for n in range(2, 6):
        for r in (2, 3):
            for ds in shift_patterns(n, r, 11):
                N = n + ds[-1]
                # Koz(n) vertices F_j = (1, C(n,1..j), 0...) in R^{n+1}; shifted copies in R^{N+1}
                P = None
                for d in ds:
                    vs = [vector(QQ, [0]*d + [1] + [binomial(n, i) for i in range(1, j+1)] + [0]*(N-d-j))
                          for j in range(1, n+1)]
                    S = Polyhedron(vertices=vs, base_ring=QQ)
                    P = S if P is None else P + S
                # translated system: x_0 = #{p : d_p = 0}; z = proj(x) - sum_{p: d_p>=1} e_{d_p} in Q_Theta
                eqns, ieqs = theta_system(kozlov(n), ds, [1]*r)
                tvec = [QQ(0)]*(N+1)
                for d in ds:
                    tvec[d] += 1
                rows_e = [[QQ(-1)] + [QQ(1)] + [QQ(0)]*N]                  # x_0 = 1 (only d_1 = 0)
                def shifted(c, b):
                    # coeffs.z + b with z_k = x_k - t_k  (k >= 1)  ->  coeffs.x + (b - coeffs.t)
                    bb = b - sum(v*tvec[k] for k, v in c.items())
                    return [bb, QQ(0)] + [QQ(c.get(k, 0)) for k in range(1, N+1)]
                rows_e += [shifted(c, b) for _, c, b in eqns]
                rows_i = [shifted(c, b) for _, c, b in ieqs]
                Q = Polyhedron(eqns=rows_e, ieqs=rows_i, base_ring=QQ)
                cnt += 1
                if Q != P:
                    bad += 1; log("  FAIL n=%d ds=%s" % (n, ds))
    log("S6 result: %d configurations, %d failures" % (cnt, bad))
    return bad == 0

# ---------------------------------------------------------------- S7: negative controls
def S7():
    log("\n== S7: negative controls ==")
    # (a) rank 2, arbitrary positive a: completeness Q_Theta subset R must ALWAYS hold (proof uses no LC)
    fails_sub = 0; fails_sup = 0; cnt = 0
    for n in range(3, 7):
        for trial in range(12 if QUICK else 25):
            a = rand_positive(n)
            for d in range(1, n):
                R = build_R(a, [0, d]); Q = theta_polyhedron(a, [0, d], [1, 1])
                cnt += 1
                if not Q.intersection(R) == Q: fails_sub += 1
                if not R.intersection(Q) == R: fails_sup += 1
    log("  (a) rank 2, random positive a: %d configs; Q_Theta subset R fails %d times (must be 0);"
        " R subset Q_Theta fails %d times (validity needs LC)" % (cnt, fails_sub, fails_sup))
    ok = (fails_sub == 0)
    # (b) rank >= 3, arbitrary positive a: does completeness survive? (proof uses weak LC there)
    fsub = 0; fsup = 0; cnt3 = 0; ex = None
    for n in range(3, 6):
        for trial in range(8 if QUICK else 15):
            a = rand_positive(n)
            for ds in shift_patterns(n, 3, 11):
                R = build_R(a, ds); Q = theta_polyhedron(a, ds, [1]*3)
                cnt3 += 1
                if not Q.intersection(R) == Q:
                    fsub += 1
                    if ex is None: ex = (a, ds)
                if not R.intersection(Q) == R: fsup += 1
    log("  (b) rank 3, random positive a: %d configs; Q_Theta subset R fails %d; R subset Q_Theta fails %d; first sub-failure %s"
        % (cnt3, fsub, fsup, ex))
    # (c) the log-convex witness a = (1,2,6,24)
    a = [QQ(1), QQ(2), QQ(6), QQ(24)]
    for d in (1, 2, 3):
        R = build_R(a, [0, d]); Q = theta_polyhedron(a, [0, d], [1, 1])
        log("  (c) a=(1,2,6,24), d=%d: Q==R %s, Q subset R %s, R subset Q %s" % (d, Q == R, Q.intersection(R) == Q, R.intersection(Q) == R))
    return ok


# ---------------------------------------------------------------- S0: mutation sanity check
def S0():
    log("\n== S0: mutation sanity check -- every Theta row is necessary, every offset is sharp ==")
    bad = 0; cnt = 0
    for n, ds in ((3, [0, 1, 2]), (4, [0, 1, 3]), (5, [0, 2, 3]), (5, [0, 1, 2, 4]), (6, [0, 3])):
        a = kozlov(n); N = n + ds[-1]; lams = [1]*len(ds)
        R = build_R(a, ds, lams)
        eqns, ieqs = theta_system(a, ds, lams)
        E = [ineq_row(c, b, N) for _, c, b in eqns]
        for i in range(len(ieqs)):
            others = [ineq_row(c, b, N) for k, (_, c, b) in enumerate(ieqs) if k != i]
            lab, c, b = ieqs[i]
            drop = Polyhedron(eqns=E, ieqs=others, base_ring=QQ)                       # row deleted
            tight = Polyhedron(eqns=E, ieqs=others + [ineq_row(c, b - QQ(1)/1000, N)], base_ring=QQ)  # offset tightened
            cnt += 1
            if drop == R or tight == R:
                bad += 1; log("  FAIL n=%d ds=%s row %s: drop==R %s, tightened==R %s" % (n, ds, lab, drop == R, tight == R))
    log("S0 result: %d row mutations, %d failures (a failure = a mutation the comparison did not detect)" % (cnt, bad))
    return bad == 0

results = {}
for name, f in (('S0', S0), ('S1', S1), ('S2', S2), ('S3', S3), ('S4', S4), ('S5', S5), ('S6', S6), ('S7', S7)):
    results[name] = f()
log("\nSUMMARY: %s   total time %.0fs" % (results, time.time()-T0))
