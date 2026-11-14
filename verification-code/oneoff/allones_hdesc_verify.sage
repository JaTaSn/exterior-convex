# allones_hdesc_verify.sage
#
# Changelog (reverse chronological):
#   2026-11-14  load() path made relative to this file (Claude-Code, jts-pc), so it runs
#               from the public copy too: right_angle_simplex.py is one directory up in both.
#   2026-10-20  BATTERY_FROM / EHR_MAXN env switches (resume a timed-out run;
#               cap the slow Ehrhart test T7).
#   2026-10-20  Added cross-check against the Kozlov agent's Theta-form (Thm B of
#               kozlov-hdescription-proof-2026-10-20.org) at a = all-ones.
#   2026-10-20  Added SKIP_BATTERY=1 switch, worked-example printer, rank-two
#               closed-form checks (nvol, lattice count).
#   2026-10-20  Created (Claude, overnight article-3 push). Machine check for
#               working-notes/allones-hdescription-generalized-permutohedra.org.
#
# What is checked, for every configuration in the battery below
# (a = all-ones, shift vector dd sorted, d_1 = 0; ties allowed):
#
#  (T1) COORDINATE CHANGE.  With y_k = x_k - x_{k+1} (x_{N+1} := 0) and the
#       translation by sum_{p: d_p >= 1} e_{d_p}, the image of
#       RA(1; dd) equals  P = sum_p Delta_{W_p},  W_p = [d_p+1, d_p+n].
#       (exact Polyhedron equality)
#  (T2) FULL H-DESCRIPTION.  P = { y([N]) = r,  y(J) <= f(J) for all J },
#       f(J) = #{p : W_p meets J}.  (exact equality, all 2^N subsets)
#  (T3) IRREDUNDANT H-DESCRIPTION.  The explicit list of the theorem
#       (in x-coordinates) cuts out RA(1; dd) exactly, every listed
#       inequality is a facet, and the number of facets of RA equals the
#       predicted count.  Done for connected configurations (all distinct
#       gaps <= n-1); disconnected ones checked through the product formula.
#  (T4) rank 2: the list coincides with conj-ones-hrep
#       (right_angle_ones_hrepresentation in code/right_angle_simplex.py).
#  (T5) LATTICE POINTS = SUMSET (Hall's theorem consequence).
#  (T6) VOLUME: normalised volume of RA equals Postnikov Thm 9.3 count
#       sum over G-draconian a of multinomial(N-1; a).
#  (T7) EHRHART: #(t*P cap Z^N) = Postnikov Thm 11.3 formula, t = 1..3.
#  (T8) VERTICES: vertex set of P equals { sum_p e_{argmax_{W_p} c} } over
#       acyclic choices (the acyclicity criterion), and count matches.
#
# Driver at top level.

import itertools, sys, time
from sage.all import *

import os
# sys.argv[0], not __file__: under `sage x.sage' __file__ names a file inside Sage itself.
load(os.path.join(os.path.dirname(os.path.abspath(sys.argv[0])), '..', 'right_angle_simplex.py'))

def windows(n, dd):
    return [list(range(d+1, d+n+1)) for d in dd]

def to_y(x, dd):
    """x in R^N (1-indexed as list index 0..N-1) -> y = Dx + sum e_{d_p}"""
    N = len(x)
    y = [x[k] - (x[k+1] if k+1 < N else 0) for k in range(N)]
    for d in dd:
        if d >= 1:
            y[d-1] += 1
    return y

def P_simplices(n, dd):
    N = n + max(dd)
    Q = None
    for W in windows(n, dd):
        S = Polyhedron(vertices=[[1 if k+1 == i else 0 for k in range(N)] for i in W])
        Q = S if Q is None else Q + S
    return Q

def full_hdesc(n, dd):
    N = n + max(dd); r = len(dd)
    Ws = [set(W) for W in windows(n, dd)]
    ieqs = []
    for mask in range(1, 2**N - 1):
        J = [i+1 for i in range(N) if (mask >> i) & 1]
        f = sum(1 for W in Ws if W & set(J))
        ieqs.append([f] + [-1 if (k+1) in J else 0 for k in range(N)])
    eqns = [[-r] + [1]*N]
    return Polyhedron(ieqs=ieqs, eqns=eqns)

def is_connected(n, dd):
    ds = sorted(set(dd))
    return all(ds[k+1] - ds[k] <= n-1 for k in range(len(ds)-1))

def explicit_x_hdesc(n, dd):
    """Theorem B list, x-coordinates, connected case. Rows [b, a_1..a_N]: b + a.x >= 0."""
    N = n + max(dd)
    ds = sorted(set(dd)); s = len(ds)
    mu = {d: dd.count(d) for d in ds}
    def e(k):
        v = [0]*N; v[k-1] = 1; return v
    eqns = [[-mu[0]] + e(1)]
    ieqs = []
    # (a) y_i >= 0, i.e. x_i - x_{i+1} >= -mu(i), for non-bad i
    good = set()
    for d in ds:
        good |= set(range(d+2, d+n))       # i with [i-1,i+1] inside W
    good |= {1, N}
    for i in sorted(good):
        row = e(i)[:]
        if i < N:
            row = [a - b for a, b in zip(e(i), e(i+1))]
        ieqs.append([mu.get(i, 0)] + row)
    # (b) prefixes: x_{delta_q+n+1} <= #{p : delta_q < d_p <= delta_q + n}, q = 1..s-1
    for q in range(s-1):
        b = ds[q] + n
        c = sum(1 for d in dd if ds[q] < d <= ds[q] + n)
        ieqs.append([c] + [-v for v in e(b+1)])
    # (b) suffixes: x_{delta_q+1} >= mu(delta_q), q = 2..s
    for q in range(1, s):
        ieqs.append([-mu[ds[q]]] + e(ds[q]+1))
    return eqns, ieqs

def predicted_facets(n, dd):
    """connected case"""
    ds = sorted(set(dd)); s = len(ds); N = n + max(dd)
    if n == 2:
        return 2*s
    g = sum(1 for k in range(s-1) if ds[k+1]-ds[k] == n-1)
    return N - g + 2*(s-1)

def components(n, dd):
    ds = sorted(set(dd)); comps = [[ds[0]]]
    for d in ds[1:]:
        if d - comps[-1][-1] <= n-1:
            comps[-1].append(d)
        else:
            comps.append([d])
    return comps

def predicted_facets_general(n, dd):
    tot = 0
    for C in components(n, dd):
        shifted = [d - C[0] for d in dd if d in C]
        tot += predicted_facets(n, shifted)
    return tot

def sumset_points(n, dd):
    N = n + max(dd)
    V = right_angle_simplex_vertices([1]*n)
    lists = [[tuple(pad_vector(shift_vector(v, d), N)) for v in V] for d in dd]
    pts = set()
    for choice in itertools.product(*lists):
        pts.add(tuple(sum(c[k] for c in choice) for k in range(N)))
    return pts

def draconian(n, dd):
    """G-draconian sequences for G = windows (connected), sum a = N-1."""
    N = n + max(dd); Ws = [set(W) for W in windows(n, dd)]; r = len(Ws)
    subsets = [S for k in range(1, r+1) for S in itertools.combinations(range(r), k)]
    U = {S: len(set().union(*[Ws[p] for p in S])) for S in subsets}
    out = []
    def rec(p, a):
        if p == r:
            if all(U[S] >= sum(a[q] for q in S) + 1 for S in subsets):
                out.append(tuple(a))
            return
        for v in range(0, N):
            if sum(a) + v > N - 1: break
            rec(p+1, a+[v])
    rec(0, [])
    return out, subsets, U

def postnikov_volume(n, dd):
    N = n + max(dd)
    out, _, _ = draconian(n, dd)
    return sum(multinomial(list(a)) for a in out if sum(a) == N-1)

def postnikov_ehrhart(n, dd, t):
    """#lattice points of t*P via Thm 11.3 with an extra I_0 = [N], y_0 = 0+1."""
    N = n + max(dd); Ws = [set(W) for W in windows(n, dd)]; r = len(Ws)
    subsets = [S for k in range(1, r+1) for S in itertools.combinations(range(r), k)]
    U = {S: len(set().union(*[Ws[p] for p in S])) for S in subsets}
    tot = 0
    for a in itertools.product(range(N), repeat=r):
        if sum(a) > N-1: continue
        if all(U[S] >= sum(a[q] for q in S) + 1 for S in subsets):
            tot += prod(binomial(t + a[p] - 1, a[p]) for p in range(r))
    return tot

def acyclic_vertices(n, dd):
    """sum_p e_{m_p}, m_p in W_p, digraph m_p -> j (j in W_p - m_p) acyclic."""
    N = n + max(dd); Ws = windows(n, dd)
    verts = set()
    for ms in itertools.product(*Ws):
        G = DiGraph([list(range(1, N+1)), []], multiedges=False, loops=False)
        for m, W in zip(ms, Ws):
            for j in W:
                if j != m: G.add_edge(m, j)
        if G.is_directed_acyclic():
            y = [0]*N
            for m in ms: y[m-1] += 1
            verts.add(tuple(y))
    return verts

def check(n, dd, lattice=True, vol=True, ehr=True, full=True):
    t0 = time.time()
    N = n + max(dd); r = len(dd)
    R = right_angle_minkowski_sum([1]*n, dd)
    P = P_simplices(n, dd)
    imgR = Polyhedron(vertices=[to_y(list(v), dd) for v in R.vertices_list()])
    res = {}
    res['T1'] = (imgR == P)
    if full and N <= 12:
        res['T2'] = (full_hdesc(n, dd) == P)
    pf = predicted_facets_general(n, dd)
    res['T3count'] = (R.n_facets() == pf, R.n_facets(), pf)
    if is_connected(n, dd):
        eqns, ieqs = explicit_x_hdesc(n, dd)
        Q = Polyhedron(eqns=eqns, ieqs=ieqs)
        res['T3eq'] = (Q == R)
        # every listed inequality is a facet of R: compare as sets of facet
        # inequalities modulo the equation -> use: dropping any one changes Q
        irr = True
        for k in range(len(ieqs)):
            Qk = Polyhedron(eqns=eqns, ieqs=ieqs[:k]+ieqs[k+1:])
            if Qk == R: irr = False; break
        res['T3irr'] = irr and (len(ieqs) == R.n_facets())
        if r == 2 and len(set(dd)) == 2 and 1 <= dd[1] <= n-1:
            e2, i2 = right_angle_ones_hrepresentation(n, dd[1])
            res['T4'] = (Polyhedron(eqns=e2, ieqs=i2) == Q)
            # same rows as sets?
            res['T4rows'] = (sorted(map(tuple, i2)) == sorted(map(tuple, ieqs))) if n - dd[1] >= 2 else 'm=1 (conj list has the redundant transition row)'
    if lattice:
        res['T5'] = (set(tuple(p) for p in R.integral_points()) == sumset_points(n, dd))
    if is_connected(n, dd):
        if vol:
            Rn = Polyhedron(vertices=R.vertices_list(), backend='normaliz')
            res['T6'] = (Rn.volume(measure='induced_lattice') == postnikov_volume(n, dd),
                         Rn.volume(measure='induced_lattice'))
        if ehr:
            ok = True
            for t in [1, 2, 3]:
                if len((t*P).integral_points()) != postnikov_ehrhart(n, dd, t):
                    ok = False
            res['T7'] = ok
    if n**r <= 5000:
        res['T8'] = (acyclic_vertices(n, dd) == set(tuple(v) for v in P.vertices_list()), P.n_vertices())
    return res, time.time() - t0

import os
if os.environ.get("SKIP_BATTERY") != "1":
    battery = []
    for n in range(2, 7):
        for d in range(0, n+2):
            battery.append((n, [0, d]))
    for n in range(2, 6):
        for d2 in range(0, n+1):
            for d3 in range(d2, d2+n+1):
                if d3 <= 7:
                    battery.append((n, [0, d2, d3]))
    battery += [(3, [0,1,2,3]), (4, [0,1,2,3]), (4, [0,1,3,4]), (3, [0,0,1,2]), (4, [0,2,2,5]),
                (3, [0,1,1,2,3]), (5, [0,1,3]), (6, [0,2,4]), (6, [0,1,5]), (7,[0,2])]

    allok = True
    start = int(os.environ.get("BATTERY_FROM", "0")); ehr_max = int(os.environ.get("EHR_MAXN", "9"))
    for n, dd in battery[start:]:
        big = (n + max(dd) > ehr_max) or len(dd) >= 4
        res, dt = check(n, dd, lattice=(n**len(dd) <= 4000), vol=True, ehr=not big, full=(n+max(dd) <= 11))
        flags = []
        for k, v in res.items():
            val = v[0] if isinstance(v, tuple) else v
            if isinstance(val, str): continue
            if not val: flags.append(k)
        if flags: allok = False
        print("n=%d dd=%s  %s  %s  (%.1fs)" % (n, dd, "OK" if not flags else "FAIL " + str(flags), res, dt))
        sys.stdout.flush()
    print("ALL OK" if allok else "SOME FAILURE")

# ---- worked examples for the note: print the explicit facet list in x-coordinates
def pretty(row):
    b, a = row[0], row[1:]
    terms = []
    for k, c in enumerate(a):
        if c == 1: terms.append("+x%d" % (k+1))
        elif c == -1: terms.append("-x%d" % (k+1))
        elif c != 0: terms.append("%+d*x%d" % (c, k+1))
    return " ".join(terms) + " >= %d" % (-b)

for n, dd in [(3, [0,1]), (5, [0,2]), (4, [0,1,2]), (5, [0,2,3]), (4, [0,1,1,3])]:
    eqns, ieqs = explicit_x_hdesc(n, dd)
    R = right_angle_minkowski_sum([1]*n, dd)
    Q = Polyhedron(eqns=eqns, ieqs=ieqs)
    print("EXAMPLE n=%d dd=%s: equation %s ; %d inequalities ; Q==RA: %s ; facets(RA)=%d ; vertices=%d ; lattice pts=%d"
          % (n, dd, pretty(eqns[0]).replace(">=", "="), len(ieqs), Q == R, R.n_facets(), R.n_vertices(), len(R.integral_points())))
    for row in ieqs:
        print("    ", pretty(row))

# ---- rank-two closed forms (Corollary E): nvol and lattice count
for n in range(2, 8):
    for d in range(0, n):
        R = right_angle_minkowski_sum([1]*n, [0, d])
        Rn = Polyhedron(vertices=R.vertices_list(), backend='normaliz')
        v = Rn.volume(measure='induced_lattice'); vf = sum(binomial(n+d-1, k) for k in range(d, n))
        L = len(R.integral_points()); Lf = n**2 - binomial(n-d, 2)
        print("RANK2 n=%d d=%d nvol=%s formula=%s  latt=%d formula=%d  %s" % (n, d, v, vf, L, Lf, "OK" if (v == vf and L == Lf) else "FAIL"))

# ---- cross-check against the Kozlov agent's Theorem B (weighted Theta-form,
#      working-notes/kozlov-hdescription-proof-2026-10-20.org) specialised to
#      a = all-ones, lambda = 1, distinct shifts, gaps <= n-1: same polytope,
#      and the set of distinct Theta-rows (as normalised inequalities) equals
#      the Theorem-B list of this note.
def theta_rows_allones(n, dd):
    N = n + max(dd); r = len(dd); Ws = windows(n, dd)
    def M(p, c):  # roof after p (0-based p)
        return sum(1 for q in range(p+1, r) if c in Ws[q])
    def e(k):
        v = [0]*N; v[k-1] = 1; return v
    rows = []
    for p in range(r):
        lo = 1 if p == 0 else dd[p] + 2
        for c in range(lo, dd[p] + n):
            rows.append([-(M(p, c) - M(p, c+1))] + [a - b for a, b in zip(e(c), e(c+1))])
        if p >= 1:
            rows.append([-1] + e(dd[p] + 1))
            c0 = dd[p-1] + n + 1
            rows.append([M(p-1, c0)] + [-v for v in e(c0)])
    rows.append([0] + e(N))
    return [[-1] + e(1)], rows

ok_all = True
for n in range(2, 8):
    for dd in ([[0, d] for d in range(1, n)] + [[0, a, b] for a in range(1, n) for b in range(a+1, a+n)]):
        if n + max(dd) > 12: continue
        eT, iT = theta_rows_allones(n, dd)
        eB, iB = explicit_x_hdesc(n, dd)
        same_poly = Polyhedron(eqns=eT, ieqs=iT) == Polyhedron(eqns=eB, ieqs=iB)
        same_rows = set(map(tuple, iT)) == set(map(tuple, iB))
        if not (same_poly and same_rows):
            ok_all = False; print("THETA-CROSSCHECK FAIL", n, dd, same_poly, same_rows)
print("THETA-CROSSCHECK (all-ones, ranks 2-3, n<=7, N<=12):", "OK" if ok_all else "FAIL")
