#!/home/jan/miniforge3/envs/sage/bin/python
"""review_volume_ehrhart_check.py -- independent referee checks for
working-notes/kozlov-polytope-volume-and-ehrhart.org.

Changelog (reverse chronological):
  2026-10-20  Claude (referee, overnight article-3 push): created.  Written from
              the note's TEXT only; does not import kozlov_volume_ehrhart.py.
              Uses PyNormaliz (Sage) for lattice-point counts, multiplicities and
              Hilbert series, plus plain-Python enumeration/DP.
              Sections:
                A  chained decomposition, lattice level: #lattice points of
                   RA(c; d) (normaliz) vs |sumset of shifted L(c)| vs #chained
                   lattice tuples (DP) vs #points passing the greedy water-fill.
                   Log-concave legs (Kozlov, all-ones, tent, plateau, LC tail
                   with wild c1, random LC tails) and non-log-concave legs
                   (incl. the note's (1,2,1,3,1,3)).
                R  chained decomposition, REAL points: random exact-rational
                   points of RA(c; d) (incl. points on low faces, ties),
                   greedy water-fill must return LYM-valid parts.
                H  lecture hall identification, h* three ways (normaliz;
                   s-inversion ascents with e0=0; with e0=1), NV, codegree,
                   interior points, invariant factors.
                E  Ehrhart polynomials of Koz(n) (n<=7 by independent DP count
                   of t*Koz(n)), Koz(n;0,d) (normaliz), rank-2 NV closed form,
                   linear coefficient additivity (rank 2 and 3).
              Run: ~/miniforge3/envs/sage/bin/python code/oneoff/review_volume_ehrhart_check.py [A R H E]
              from PROJ; output -> runs/2026-10-20_article3-overnight-push/2026-10-20_review-volume-ehrhart.txt.
"""
import sys, random
from fractions import Fraction as Fr
from math import comb, prod, factorial
from itertools import product as iprod
from functools import lru_cache
from PyNormaliz import Cone

random.seed(20261020)

# ---------------------------------------------------------------- basics
def kozlov(n):
    return tuple(comb(n, k) for k in range(n + 1))

def is_lc_tail(c):
    t = c[2:]
    return all(t[i] ** 2 >= t[i - 1] * t[i + 1] for i in range(1, len(t) - 1))

def vertices_angle(c):
    n = len(c) - 1
    return [tuple(c[k] if k <= j else 0 for k in range(n + 1)) for j in range(1, n + 1)]

def shift(v, d, N):
    w = [0] * (N + 1)
    for k, a in enumerate(v):
        w[k + d] = a
    return tuple(w)

def lattice_angle(c):
    """integer points of angle(c): x0=1, x1=c1, y_k=x_k/c_k nonincreasing >=0."""
    n = len(c) - 1
    out = []
    def rec(k, prev, acc):
        if k > n:
            out.append(tuple(acc)); return
        hi = (c[k] * prev[0]) // prev[1]  # x_k <= c_k * x_{k-1}/c_{k-1}
        for x in range(hi + 1):
            rec(k + 1, (x, c[k]), acc + [x])
    rec(2, (c[1], c[1]), [1, c[1]])
    return out

def ra_generators(c, d):
    n = len(c) - 1; N = n + d[-1]
    V = vertices_angle(c)
    gens = set()
    for choice in iprod(V, repeat=len(d)):
        s = [0] * (N + 1)
        for v, di in zip(choice, d):
            for k, a in enumerate(v):
                s[k + di] += a
        gens.add(tuple(s))
    return sorted(gens), N

def nonconst_coords(gens):
    return [k for k in range(len(gens[0])) if len({g[k] for g in gens}) > 1]

def normaliz_cone(c, d):
    gens, N = ra_generators(c, d)
    U = nonconst_coords(gens)
    proj = [[g[k] for k in U] for g in gens]
    return Cone(polytope=proj), U, gens

def s_of(p, c):
    j = 1
    while j + 1 < len(c) and p[j + 1] == c[j + 1]:
        j += 1
    return j

def e_of(p, c):
    j = 1
    for k in range(1, len(c)):
        if p[k] > 0:
            j = k
    return j

def chained_count(L, c, d):
    """# tuples (p_1..p_r) in L^r chained for d (consecutive condition)."""
    se = [(s_of(p, c), e_of(p, c)) for p in L]
    cnt = [1] * len(L)
    for i in range(1, len(d)):
        new = [0] * len(L)
        # new[b] = sum_a cnt[a] * [e_a + d_{i-1} <= s_b + d_i]
        # sort by e to do prefix sums
        from collections import Counter
        byE = Counter()
        for a, (sa, ea) in enumerate(se):
            byE[ea] += cnt[a]
        maxE = max(byE) if byE else 0
        pref = {}
        run = 0
        for e in range(0, len(c) + 1):
            run += byE.get(e, 0); pref[e] = run
        for b, (sb, eb) in enumerate(se):
            lim = sb + d[i] - d[i - 1]
            lim = min(lim, len(c))
            new[b] = pref[lim] if lim >= 0 else 0
        cnt = new
    return sum(cnt)

def sumset_size(L, c, d):
    n = len(c) - 1; N = n + d[-1]
    S = {tuple([0] * (N + 1))}
    for di in d:
        Ls = [shift(p, di, N) for p in L]
        S = {tuple(a + b for a, b in zip(s, q)) for s in S for q in Ls}
    return len(S), S

def greedy_fill(x, c, d):
    """water-fill: at each degree, fill summands from last to first. Return parts
    (own coordinates) or None if something is left over / a part is not LYM."""
    n = len(c) - 1; r = len(d); N = n + d[-1]
    parts = [[0] * (n + 1) for _ in range(r)]
    for k in range(N + 1):
        rem = x[k]
        for i in range(r - 1, -1, -1):
            j = k - d[i]
            if 0 <= j <= n:
                take = min(c[j], rem)
                if take < 0:
                    return None
                parts[i][j] = take; rem -= take
        if rem != 0:
            return None
    for p in parts:
        if p[0] != 1 or p[1] != c[1]:
            return None
        y = [Fr(p[k], c[k]) for k in range(n + 1)]
        if any(y[k] < y[k + 1] for k in range(n)) or y[n] < 0:
            return None
    return parts

def chained_parts(parts, c, d):
    for i in range(1, len(d)):
        if e_of(parts[i - 1], c) + d[i - 1] > s_of(parts[i], c) + d[i]:
            return False
    return True

LOG = []
def out(*a):
    s = " ".join(str(x) for x in a); print(s, flush=True); LOG.append(s)

# ---------------------------------------------------------------- A
def sectionA():
    out("== A: lattice-level chained decomposition / additivity ==")
    out("columns: c | d | LC-tail | #RA∩Z (normaliz) | |sumset| | #chained | #greedy-valid lattice pts (n/a if not enumerated) | verdict")
    fams = []
    for n in range(2, 7):
        fams.append(kozlov(n))
    fams += [(1, 1, 1, 1), (1, 1, 1, 1, 1), (1, 1, 1, 1, 1, 1),
             (1, 2, 3, 2, 1), (1, 1, 2, 3, 2, 1), (1, 3, 4, 4, 3, 1),
             (1, 2, 2, 2, 1), (1, 2, 2, 2, 2, 2), (1, 3, 3, 3, 1, 1),
             (1, 7, 1, 1, 1), (1, 9, 2, 3, 3, 2), (1, 1, 5, 4, 2),
             (1, 2, 5, 7, 4, 1)]
    nonlc = [(1, 2, 1, 3, 1, 3), (1, 2, 1, 1, 2), (1, 5, 1, 2, 5), (1, 1, 3, 1, 3), (1, 2, 1, 2, 1, 2)]
    def dvecs(n):
        ds = [(0, 0), (0, 1), (0, 2), (0, n - 2), (0, n - 1), (0, 0, 0), (0, 0, 1), (0, 1, 1),
              (0, 1, 2), (0, 1, 3), (0, 2, 3)]
        return sorted({t for t in ds if all(x >= 0 for x in t) and list(t) == sorted(t)})
    bad = 0
    for c in fams + nonlc:
        n = len(c) - 1
        L = lattice_angle(c)
        for d in dvecs(n):
            if len(d) == 3 and len(L) ** 3 > 6e6:
                continue
            if len(L) ** len(d) > 8e6:
                continue
            C, U, gens = normaliz_cone(c, d)
            npts = C.NumberLatticePoints()
            ss, S = sumset_size(L, c, d)
            ch = chained_count(L, c, d)
            # greedy on all lattice points: enumerate via normaliz if small
            gv = "n/a"
            if npts <= 60000:
                pts = C.LatticePoints()
                # rebuild full vectors: constant coords from gens[0]
                full = []
                for q in pts:
                    v = list(gens[0]);
                    for k, a in zip(U, q[:-1]):
                        v[k] = a
                    full.append(tuple(v))
                ok = 0
                for v in full:
                    pr = greedy_fill(v, c, d)
                    if pr is not None and chained_parts(pr, c, d):
                        ok += 1
                gv = ok
            lc = is_lc_tail(c)
            agree = (npts == ss == ch) and (gv == "n/a" or gv == npts)
            verdict = "OK" if agree else ("FAIL(expected, non-LC)" if not lc else "**FAIL**")
            if lc and not agree:
                bad += 1
            out(c, d, lc, npts, ss, ch, gv, verdict)
    out("A: log-concave failures:", bad)
    # random LC-tail legs
    out("-- A': random leg vectors with log-concave tail, random d (r<=3) --")
    tested = 0; bad = 0; nonlc_fail = 0; nonlc_tested = 0
    while tested + nonlc_tested < 260:
        n = random.randint(3, 5)
        c = (1,) + tuple(random.randint(1, 6) for _ in range(n))
        r = random.choice([2, 2, 3])
        gaps = [random.randint(0, n) for _ in range(r - 1)]
        d = [0]
        for g in gaps:
            d.append(d[-1] + g)
        d = tuple(d)
        L = lattice_angle(c)
        if len(L) ** r > 3e5:
            continue
        lc = is_lc_tail(c)
        C, U, gens = normaliz_cone(c, d)
        npts = C.NumberLatticePoints()
        ss, _ = sumset_size(L, c, d)
        ch = chained_count(L, c, d)
        if lc:
            tested += 1
            if not (npts == ss == ch):
                bad += 1; out("  **LC FAIL**", c, d, npts, ss, ch)
        else:
            nonlc_tested += 1
            if not (npts == ss == ch):
                nonlc_fail += 1
                if nonlc_fail <= 8:
                    out("  non-LC fail (fine):", c, d, npts, ss, ch)
    out(f"A': LC-tail cases tested {tested}, failures {bad}; non-LC cases {nonlc_tested}, of which {nonlc_fail} fail additivity or existence")

# ---------------------------------------------------------------- R
def rand_lym(n, ties=True):
    """random exact y: 1 = y1 >= y2 >= ... >= yn >= 0, with deliberate ties/0/1."""
    pool = [Fr(0), Fr(1)] + [Fr(random.randint(0, 12), 12) for _ in range(3)]
    vals = sorted([random.choice(pool) if ties and random.random() < 0.6 else Fr(random.randint(0, 997), 997)
                   for _ in range(n - 1)], reverse=True)
    return [Fr(1), Fr(1)] + vals  # y0, y1, y2..yn

def sectionR(samples=3000):
    out("== R: real-point existence via greedy water-fill on random exact points ==")
    cases = []
    for n in range(2, 7):
        cases.append(kozlov(n))
    cases += [(1, 1, 1, 1, 1), (1, 2, 3, 2, 1), (1, 2, 2, 2, 2, 2), (1, 7, 1, 1, 1), (1, 2, 5, 7, 4, 1),
              (1, 4, 1, 1, 1, 1), (1, 1, 2, 3, 3, 2)]
    nonlc = [(1, 2, 1, 3, 1, 3), (1, 2, 1, 1, 2)]
    for c in cases + nonlc:
        n = len(c) - 1
        fails = 0; tot = 0
        for _ in range(samples):
            r = random.choice([2, 3, 4])
            d = [0]
            for _ in range(r - 1):
                d.append(d[-1] + random.randint(0, n + 1))
            N = n + d[-1]
            x = [Fr(0)] * (N + 1)
            for di in d:
                y = rand_lym(n)
                for k in range(n + 1):
                    x[k + di] += c[k] * y[k]
            pr = greedy_fill(x, c, d)
            tot += 1
            if pr is None or not chained_parts(pr, c, d):
                fails += 1
                if fails <= 2:
                    out("   fail example", c, d, [str(v) for v in x])
        out(c, "LC-tail" if is_lc_tail(c) else "NON-LC", f"samples {tot}, greedy chained decomposition fails {fails}")

# ---------------------------------------------------------------- H
def asc_poly(s, e0):
    """s-Eulerian: sum over e in I^(s) of z^asc(e), asc with convention e0, s0=1."""
    D = len(s)
    h = [0] * (D + 1)
    for e in iprod(*[range(si) for si in s]):
        ee = (e0,) + e; ss = (1,) + tuple(s)
        a = sum(1 for i in range(D) if Fr(ee[i], ss[i]) < Fr(ee[i + 1], ss[i + 1]))
        h[a] += 1
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return h

def hstar_normaliz(C):
    hs = C.HilbertSeries()
    num = list(hs[0])
    return num

def smith_invariants(diag):
    # invariant factors of a diagonal integer matrix
    from math import gcd
    ds = [x for x in diag]
    # use prime-power decomposition
    from collections import defaultdict
    def fac(m):
        f = {}; p = 2
        while p * p <= m:
            while m % p == 0:
                f[p] = f.get(p, 0) + 1; m //= p
            p += 1
        if m > 1: f[m] = f.get(m, 0) + 1
        return f
    pp = defaultdict(list)
    for x in ds:
        for p, e in fac(x).items():
            pp[p].append(e)
    k = max((len(v) for v in pp.values()), default=0)
    inv = [1] * k
    for p, es in pp.items():
        es = sorted(es, reverse=True)
        for i, e in enumerate(es):
            inv[k - 1 - i] *= p ** e
    return inv

def sectionH():
    out("== H: lecture hall identification, h*, NV, codegree ==")
    for n in range(2, 8):
        c = kozlov(n)
        # projected vertices onto coords 2..n, reversed order lambda_i = x_{n+1-i}
        V = vertices_angle(c)
        proj = sorted(tuple(v[k] for k in range(n, 1, -1)) for v in V)
        s = [c[k] for k in range(n, 1, -1)]  # (c_n, ..., c_2)
        D = len(s)
        # LH vertices: 0, s_D e_D, s_D e_D + s_{D-1} e_{D-1}, ...
        lh = []
        for m in range(D + 1):
            v = [0] * D
            for i in range(D - m, D):
                v[i] = s[i]
            lh.append(tuple(v))
        same = proj == sorted(lh)
        C, U, gens = normaliz_cone(c, (0,))
        mult = C.Multiplicity()
        hst = hstar_normaliz(C)
        nv = prod(c[2:])
        line = f"n={n} s=(c_n..c_2)={tuple(s)} proj(Koz)=P^(s):{same} NV normaliz={mult} prod C(n,k),k>=2 ={nv}"
        out(line)
        if prod(s) <= 3e6:
            h0 = asc_poly(s, 0); h1 = asc_poly(s, 1)
            hrev = asc_poly(list(reversed(s)), 0)
            out(f"   h* normaliz={hst}  asc(e0=0,s)={h0}  asc(e0=0,rev s)={hrev}  asc(e0=1,s)={h1}")
        else:
            out(f"   h* normaliz={hst}")
        out(f"   deg h* = {len(hst) - 1} (claim n-2 = {n - 2}); h*_top={hst[-1]}; group ⊕Z/C(n,k): invariant factors {smith_invariants(list(c[2:]))}")
        if n <= 6:
            out(f"   IDP check: Hilbert basis all degree 1: {all(h[-1] == 1 for h in C.HilbertBasis())}")

# ---------------------------------------------------------------- E
def lattice_count_dilate(c, t):
    """#integer points of t*angle(c): x_k integers, t >= x2/c2 >= ... >= xn/cn >= 0 (x0=t, x1=t c1)."""
    n = len(c) - 1
    # DP from top: f(k, x_k) = # completions x_{k+1..n}
    @lru_cache(None)
    def f(k, x):
        if k == n:
            return 1
        hi = (c[k + 1] * x) // c[k]
        return sum(f(k + 1, z) for z in range(hi + 1))
    return sum(f(2, x) for x in range(t * c[2] + 1)) if n >= 2 else 1

def interp(vals):
    """Lagrange interpolate values at t=0..m -> coefficient list (Fractions)."""
    m = len(vals) - 1
    coeffs = [Fr(0)] * (m + 1)
    for i, yi in enumerate(vals):
        # basis poly prod_{j!=i} (t - j)/(i - j)
        basis = [Fr(1)]
        den = 1
        for j in range(m + 1):
            if j == i: continue
            basis = [Fr(0)] + basis
            for k in range(len(basis) - 1):
                basis[k] -= j * basis[k + 1]
            den *= (i - j)
        for k in range(m + 1):
            coeffs[k] += yi * basis[k] / den
    return coeffs

def ehrhart_from_h(h, D):
    # L(t) = sum_i h_i C(t + D - i, D), evaluate at t = 0..D, interpolate
    vals = [sum(hi * comb(t + D - i, D) for i, hi in enumerate(h)) for t in range(D + 1)]
    return interp(vals)

def fmt(co):
    return " + ".join(f"({x})t^{k}" for k, x in enumerate(co))

def sectionE():
    out("== E: Ehrhart polynomials, NV closed form, linear coefficient ==")
    lin1 = {}
    for n in range(2, 8):
        c = kozlov(n)
        vals = [lattice_count_dilate(c, t) for t in range(n)]
        co = interp(vals)
        lin1[n] = co[1]
        out(f"L_Koz({n})(t) by DP count = {fmt(co)}")
        out(f"   L(-1) = {sum(x * (-1) ** k for k, x in enumerate(co))}  #L_n = {vals[1]}  leading*(n-1)! = {co[-1] * factorial(n - 1)}")
    out("-- rank 2: NV closed form vs normaliz, Ehrhart via normaliz h*, linear coefficient --")
    for n in range(2, 7):
        c = kozlov(n)
        for d in range(0, n + 1):
            if n == 6 and d >= 3:
                continue
            C, U, gens = normaliz_cone(c, (0, d))
            Dm = len(U)
            mult = C.Multiplicity()
            if d <= n - 1:
                cf = prod(c[2:]) * sum(comb(n - 1 + d, d + g - 1) * prod(c[k] for k in range(g + 1, g + d + 1))
                                       for g in range(1, n - d + 1))
            else:
                cf = None
            h = hstar_normaliz(C)
            co = ehrhart_from_h(h, Dm)
            out(f"n={n} d={d} D={Dm} NV normaliz={mult} closed form={cf} {'OK' if cf in (None, mult) else '**MISMATCH**'}; vol=NV/D!={Fr(int(mult), factorial(Dm))}")
            out(f"    h*={h}; #pts={C.NumberLatticePoints()}; [t^1]L = {co[1]} (2*[t]L_Koz(n) = {2 * lin1[n]}) {'OK' if co[1] == 2 * lin1[n] else '**MISMATCH**'}; negative coeffs: {[k for k, x in enumerate(co) if x < 0]}")
            if n <= 4:
                out(f"    L(t) = {fmt(co)}")
    out("-- rank 3 linear coefficients --")
    for n in range(3, 6):
        c = kozlov(n)
        for d in [(0, 0, 1), (0, 1, 1), (0, 1, 2), (0, 1, 3), (0, 2, 4), (0, 0, 0)]:
            C, U, gens = normaliz_cone(c, d)
            if C.Multiplicity() > 5e7:
                continue
            h = hstar_normaliz(C)
            co = ehrhart_from_h(h, len(U))
            out(f"n={n} d={d} NV={C.Multiplicity()} h*={h} [t]L={co[1]} 3*[t]L_Koz={3 * lin1[n]} {'OK' if co[1] == 3 * lin1[n] else '**MISMATCH**'}")
    out("-- general leg vector (1,2,5,7,4,1): linear coeff additivity, rank 2 --")
    c = (1, 2, 5, 7, 4, 1)
    C1, U1, _ = normaliz_cone(c, (0,))
    l1 = ehrhart_from_h(hstar_normaliz(C1), len(U1))[1]
    for d in [(0, 0), (0, 1), (0, 3), (0, 6)]:
        C, U, _ = normaliz_cone(c, d)
        co = ehrhart_from_h(hstar_normaliz(C), len(U))
        out(f"c={c} d={d} [t]L={co[1]} 2*[t]L1={2 * l1} {'OK' if co[1] == 2 * l1 else '**MISMATCH**'}")

if __name__ == "__main__":
    secs = sys.argv[1:] or ["A", "R", "H", "E"]
    for s in secs:
        {"A": sectionA, "R": sectionR, "H": sectionH, "E": sectionE, "S": (lambda: None)}[s]()

# ---------------------------------------------------------------- S (appended 2026-10-20)
def staircase_nv(c, d):
    """general staircase formula of the note (gaps <= n-1 assumed)."""
    n = len(c) - 1; r = len(d); N = n + d[-1]; D = N - 1
    tot = 0
    def rec(i, ts):
        nonlocal tot
        if i == r:
            ts2 = ts + [N]
            # constraints
            for k in range(1, r + 1):
                if ts2[k - 1] - d[k - 1] < 1 or ts2[k] - d[k - 1] > n or ts2[k - 1] > ts2[k]:
                    return
            parts = [ts2[k] - ts2[k - 1] for k in range(1, r + 1)]
            mult = factorial(D)
            for p in parts:
                mult //= factorial(p)
            pr = 1
            for k in range(1, r + 1):
                for g in range(ts2[k - 1] + 1, ts2[k] + 1):
                    pr *= c[g - d[k - 1]]
            tot += mult * pr
            return
        for t in range(ts[-1], N + 1):
            rec(i + 1, ts + [t])
    rec(1, [1])
    return tot

def sectionS():
    out("== S: general staircase NV formula vs normaliz multiplicity ==")
    cases = [(kozlov(3), (0, 1, 2)), (kozlov(4), (0, 1, 2)), (kozlov(4), (0, 1, 3)), (kozlov(4), (0, 2, 4)),
             (kozlov(5), (0, 1, 2)), (kozlov(5), (0, 0, 1)), (kozlov(4), (0, 1, 2, 3)),
             ((1, 2, 5, 7, 4, 1), (0, 1, 3)), ((1, 7, 1, 1, 1), (0, 1, 2)), ((1, 2, 2, 2, 2, 2), (0, 2, 3)),
             ((1, 2, 1, 3, 1, 3), (0, 1)), ((1, 2, 1, 3, 1, 3), (0, 2)), ((1, 2, 1, 1, 2), (0, 1))]
    for c, d in cases:
        C, U, _ = normaliz_cone(c, d)
        m = C.Multiplicity(); f = staircase_nv(c, d)
        out(c, d, "LC" if is_lc_tail(c) else "NON-LC", "normaliz", m, "staircase", f, "OK" if m == f else "differs")

if __name__ == "__main__" and "S" in sys.argv[1:]:
    sectionS()
