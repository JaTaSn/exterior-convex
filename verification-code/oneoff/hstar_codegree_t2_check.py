# 2026-11-09 - Claude-Code (jts-mini) subagent, for working-notes/hstar-sketches-proofs-2026-11-09.org.
#   Checks the three statements proved there: the codegree theorem (codegree 1 iff no exposed index), never Gorenstein
#   (h*_s >= 2), and the t^2-coefficient formula; on every small d by a transfer matrix written afresh here (not imported
#   from kozlov_volume_ehrhart.py), and on the 47 stored h*-vectors. Plain python3, exact arithmetic.
#   Usage, from the project directory: python3 code/oneoff/hstar_codegree_t2_check.py > runs/2026-11-09_hstar-codegree-t2-check.txt
import ast
import itertools
import re
import sys
from fractions import Fraction as Fr
from math import comb

NMAX = 7


# ---------------------------------------------------------------- rank one: lattice points of Koz(n) and the matrices
def joint_counts(n):
    """J[tau][iota] = #{x in L_n : tp(x) = tau, indeg(x) = iota}, tau in 1..n, iota in 2..n+1; and #L_n."""
    c = [comb(n, k) for k in range(n + 1)]
    J = [[0] * (n + 2) for _ in range(n + 1)]
    total = 0

    def rec(k, prev, tp, indeg):
        # prev = x_{k-1}; tp = largest index < k with x > 0; indeg = least index < k with x < c (or None)
        nonlocal total
        if k > n:
            J[tp][indeg if indeg is not None else n + 1] += 1
            total += 1
            return
        ub = (c[k] * prev) // c[k - 1]          # x_k / c_k <= x_{k-1} / c_{k-1}
        for xk in range(ub + 1):
            rec(k + 1, xk, k if xk > 0 else tp, indeg if indeg is not None else (k if xk < c[k] else None))

    rec(2, n, 1, None)                           # x_0 = 1, x_1 = n are full
    return J, total


def matmul(A, B):
    return [[sum(A[i][k] * B[k][j] for k in range(len(B))) for j in range(len(B[0]))] for i in range(len(A))]


def vecmat(v, A):
    return [sum(v[k] * A[k][j] for k in range(len(v))) for j in range(len(A[0]))]


class Rank1:
    def __init__(self, n):
        self.n = n
        self.J, self.npts = joint_counts(n)
        # index tau = 1..n stored at 0..n-1
        self.u = [sum(self.J[t]) for t in range(1, n + 1)]
        self._T = {}

    def T(self, delta):
        """T(delta)[tau][tau'] = #{x : tp(x) = tau', indeg(x) + delta > tau}."""
        if delta not in self._T:
            n = self.n
            self._T[delta] = [[sum(self.J[tp_][i] for i in range(2, n + 2) if i + delta > tau)
                               for tp_ in range(1, n + 1)] for tau in range(1, n + 1)]
        return self._T[delta]

    def count(self, ds):
        """#lattice points of Koz(n; ds) = number of chained tuples (Cor. cor-additivity, cor-transfer)."""
        v = list(self.u)
        for a, b in zip(ds, ds[1:]):
            v = vecmat(v, self.T(b - a))
        return sum(v)


# ---------------------------------------------------------------- polynomials
def interpolate(vals):
    """Coefficients (t^0..t^m) of the polynomial of degree <= m with p(t) = vals[t], t = 0..m (Newton forward)."""
    m = len(vals) - 1
    diffs, row = [], [Fr(v) for v in vals]
    while row:
        diffs.append(row[0])
        row = [row[i + 1] - row[i] for i in range(len(row) - 1)]
    coeffs = [Fr(0)] * (m + 1)
    for k, dk in enumerate(diffs):                # dk * binom(t, k)
        poly = [Fr(1)]
        for i in range(k):                        # multiply by (t - i)
            poly = [(-i) * poly[0]] + [poly[j - 1] - i * poly[j] for j in range(1, len(poly))] + [poly[-1]]
        f = Fr(1, 1)
        for i in range(1, k + 1):
            f *= i
        for j, pj in enumerate(poly):
            coeffs[j] += dk * pj / f
    return coeffs


def peval(co, t):
    return sum(cj * Fr(t) ** j for j, cj in enumerate(co))


def binom_poly_shifted(k):
    """Coefficients in t of binom(t-1, k) = (t-1)(t-2)...(t-k)/k!."""
    poly = [Fr(1)]
    for i in range(1, k + 1):
        poly = [(-i) * poly[0]] + [poly[j - 1] - i * poly[j] for j in range(1, len(poly))] + [poly[-1]]
    f = 1
    for i in range(1, k + 1):
        f *= i
    return [p / f for p in poly]


def hstar_from_L(L, D):
    vals = [peval(L, t) for t in range(D + 1)]
    h = [sum((-1) ** j * comb(D + 1, j) * vals[i - j] for j in range(i + 1)) for i in range(D + 1)]
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return [int(x) for x in h]


def L_from_hstar(h, D):
    """L(t) = sum_i h_i binom(t + D - i, D), as coefficients."""
    co = [Fr(0)] * max(D + 1, 3)
    for i, hi in enumerate(h):
        poly = [Fr(1)]
        for j in range(1, D + 1):                 # prod_{j=1}^{D} (t + j - i) / D!
            a = j - i
            poly = [a * poly[0]] + [poly[m - 1] + a * poly[m] for m in range(1, len(poly))] + [poly[-1]]
        f = 1
        for j in range(1, D + 1):
            f *= j
        for m, pm in enumerate(poly):
            co[m] += hi * pm / f
    return co


# ---------------------------------------------------------------- the polytope
def dim(n, ds):
    U = set()
    for d in ds:
        U |= set(range(d + 2, d + n + 1))
    return len(U), sorted(U)


def repeat(ds, t):
    return [d for d in ds for _ in range(t)]


def ehrhart(R, ds):
    n = R.n
    D, _ = dim(n, ds)
    vals = [1] + [R.count(repeat(ds, t)) for t in range(1, D + 2)]   # one value more than needed, as a check
    co = interpolate(vals[:D + 1])
    assert peval(co, D + 1) == vals[D + 1], ('degree check failed', n, ds)
    assert co[D] != 0
    return D, co + [Fr(0)] * (3 - len(co))          # padded, so that [t^2] exists also for D = 1


def exposed(n, ds):
    """Indices i (0-based) with d_i not repeated from below and the next gap >= n-1 (or i last)."""
    r = len(ds)
    return [i for i in range(r)
            if not (i > 0 and ds[i - 1] == ds[i]) and (i == r - 1 or ds[i + 1] - ds[i] >= n - 1)]


# ---------------------------------------------------------------- t^2 machinery: U(t) = sum_k binom(t-1,k) N^k
def matrix_U_coeffs(R, upto=2):
    n = R.n
    T0 = R.T(0)
    I = [[int(i == j) for j in range(n)] for i in range(n)]
    Nm = [[T0[i][j] - I[i][j] for j in range(n)] for i in range(n)]
    powers = [I]
    for _ in range(n):
        powers.append(matmul(powers[-1], Nm))
    assert all(x == 0 for row in powers[n] for x in row), 'N not nilpotent'
    Us = []
    for e in range(upto + 1):
        M = [[Fr(0)] * n for _ in range(n)]
        for k in range(n):
            ck = binom_poly_shifted(k)
            coef = ck[e] if e < len(ck) else 0
            if coef:
                for i in range(n):
                    for j in range(n):
                        M[i][j] += coef * powers[k][i][j]
        Us.append(M)
    return Us


def selection(n, delta):
    return [[int(j == max(i - delta, 0)) for j in range(n)] for i in range(n)]   # 0-based: tau -> max(tau - delta, 1)


# ================================================================ main
def main():
    out = print
    out('# hstar_codegree_t2_check.py, 2026-11-09, Claude-Code (jts-mini) subagent')
    out('# python', sys.version.split()[0])
    R = {n: Rank1(n) for n in range(2, NMAX + 1)}
    out('#L_n:', {n: R[n].npts for n in R}, '(expected 2, 5, 20, 162, 1981, 60993)')
    assert [R[n].npts for n in range(2, 8)] == [2, 5, 20, 162, 1981, 60993]

    # ---------------- A. rank one: L_Koz(n), a1, a2 by interpolation and by the matrix expansion
    out('\nA. Rank one: [t]L and [t^2]L of Koz(n), by interpolation and by u U_e 1')
    a1, a2, Us = {}, {}, {}
    for n in R:
        D, co = ehrhart(R[n], [0])
        Us[n] = matrix_U_coeffs(R[n])
        uU = [vecmat(R[n].u, Us[n][e]) for e in range(3)]
        e_vals = [sum(v) for v in uU]
        assert e_vals[0] == 1 and e_vals[1] == co[1] and e_vals[2] == co[2], n
        a1[n], a2[n] = co[1], co[2]
        out(f'  n={n}: L = {[str(x) for x in co]}   a1={co[1]} a2={co[2]}  (matrix: {e_vals[1]}, {e_vals[2]})')

    # ---------------- B. the two matrix identities behind the t^2 formula
    out('\nB. T(delta) T0^{-1} = S(delta) (row selection tau -> max(tau-delta,1)) and S(a)S(b) = S(a+b)')
    for n in R:
        U0 = Us[n][0]
        for delta in range(0, n + 2):
            TS = [[sum(Fr(R[n].T(delta)[i][k]) * U0[k][j] for k in range(n)) for j in range(n)] for i in range(n)]
            assert TS == [[Fr(x) for x in row] for row in selection(n, delta)], (n, delta)
            for b in range(0, n + 2):
                assert matmul(selection(n, delta), selection(n, b)) == selection(n, delta + b)
    out('  OK for 2 <= n <= %d, 0 <= delta, b <= n+1' % NMAX)

    # ---------------- C. Q_n(delta) by the matrix formula and from rank two
    out('\nC. Q_n(delta) = u U1 T(delta) U1 1 = [t^2]L_Koz(n;0,delta) - 2 a2; Q(0) = 2 a2, Q(delta) = a1^2 for delta >= n-1')
    Qm = {}
    for n in R:
        U1 = Us[n][1]
        uU1 = vecmat(R[n].u, U1)
        U1one = [sum(U1[i][j] for j in range(n)) for i in range(n)]
        row = []
        for delta in range(0, n + 1):
            q = sum(sum(uU1[i] * R[n].T(delta)[i][j] for i in range(n)) * U1one[j] for j in range(n))
            D, co = ehrhart(R[n], [0, delta])
            assert q == co[2] - 2 * a2[n], (n, delta, q, co[2])
            row.append(q)
        Qm[n] = row
        assert row[0] == 2 * a2[n] and all(row[d] == a1[n] ** 2 for d in range(n - 1, n + 1))
        out(f'  n={n}: ' + ', '.join(f'Q({d})={q}' for d, q in enumerate(row)))
        if n >= 3 and all(q >= 0 for q in row) and a2[n] > 0:
            out(f'        all Q_{n} >= 0 and a2 > 0: [t^2]L_Koz({n};d) > 0 for every d')

    def Q(n, delta):
        return Qm[n][min(delta, n - 1)]

    # ---------------- D. all small d
    out('\nD. Every d with d_1 = 0 and gaps in [0, n]: codegree, h*_s, palindromy, t^2 formula')
    ranges = {2: 4, 3: 5, 4: 5, 5: 4, 6: 4, 7: 3}
    stats = dict(cases=0, conj_fail=[], thm_fail=[], gor=[], t2_fail=[], hs_lt2=[])
    INT = []
    for n in sorted(ranges):
        for r in range(1, ranges[n] + 1):
            for gaps in itertools.product(range(0, n + 1), repeat=r - 1):
                ds = [0]
                for g in gaps:
                    ds.append(ds[-1] + g)
                D, co = ehrhart(R[n], ds)
                h = hstar_from_L(co, D)
                s = len(h) - 1
                ints = [(-1) ** D * peval(co, -t) for t in range(1, 4)]
                codeg = next(t for t in range(1, 4) if ints[t - 1] > 0)
                assert codeg == D + 1 - s
                assert ints[codeg - 1] == h[s]
                stats['cases'] += 1
                # t^2 formula
                pred = r * a2[n] + sum(Q(n, ds[k] - ds[j]) for j in range(r) for k in range(j + 1, r))
                if pred != co[2]:
                    stats['t2_fail'].append((n, tuple(ds)))
                if co[2] < 0:
                    stats.setdefault('neg_t2', []).append((n, tuple(ds), co[2]))
                if n >= 3:
                    ex = exposed(n, ds)
                    thm = 2 if ex else 1
                    conj = 1 if (r >= 2 and ds[-2] == ds[-1]) else 2
                    if thm != codeg:
                        stats['thm_fail'].append((n, tuple(ds)))
                    if conj != codeg:
                        stats['conj_fail'].append((n, tuple(ds), codeg))
                    if h == h[::-1]:
                        stats['gor'].append((n, tuple(ds)))
                    if h[s] < 2:
                        stats['hs_lt2'].append((n, tuple(ds)))
                    INT.append((n, tuple(ds), int(ints[0]), int(ints[1]), codeg))
        out(f'  n={n}: r <= {ranges[n]} done')
    out(f"  cases: {stats['cases']}, of which {len(INT)} with n >= 3 (n=2 only for the t^2 formula)")
    out(f"  t^2 formula failures: {stats['t2_fail']}")
    out(f"  codegree theorem (exposed index) failures, n>=3: {stats['thm_fail']}")
    out(f"  h*_s < 2, n>=3: {stats['hs_lt2']}")
    out(f"  palindromic h*, n>=3: {stats['gor']}")
    cf = stats['conj_fail']
    out(f"  conj-codegree AS STATED in the paper fails in {len(cf)} cases; all have an exposed index i < r:"
        f" {all(exposed(n, list(ds)) and exposed(n, list(ds))[0] < len(ds) - 1 for n, ds, _ in cf)}")
    out('  the smallest ones: ' + ', '.join(f'({n};{",".join(map(str, ds))}) codeg {c}' for n, ds, c in
                                            sorted(cf, key=lambda x: (x[0], len(x[1]), x[1]))[:12]))
    if cf:
        # all-gaps <= n-2: conj as stated should be right there
        bad_conn = [x for x in cf if all(b - a <= x[0] - 2 for a, b in zip(x[1], x[1][1:]))]
        out(f'  of these, with every gap <= n-2: {bad_conn}')
    assert not stats['t2_fail'] and not stats['thm_fail'] and not stats['hs_lt2'] and not stats['gor']
    neg = stats.get('neg_t2', [])
    for n in sorted(set(x[0] for x in neg)):
        tot = sum(1 for x in INT if x[0] == n) if n >= 3 else None
        here = [x for x in neg if x[0] == n]
        out(f'  negative [t^2]L at n={n}: {len(here)} of the cases computed'
            + ('; with r <= 3: ' + ', '.join(f'({n};{",".join(map(str, ds))}) {v}' for _, ds, v in here if len(ds) <= 3)
               if n == 6 else ''))
    out('  (n <= 5: none, as section C predicts)')

    # ---------------- E. the construction of the proof: two interior lattice points, checked by membership tests
    out('\nE. The construction in the proof of claim (*) (note, sec. 4): two lattice points in relint Koz(n;d) when no index is exposed')
    out('   interior test: M x +- e_k in M Koz(n;d) for every free coordinate k (water-filling membership), M = 2,4,8,16')
    nchecked = 0
    for n in range(3, 7):
        for r in range(2, {3: 6, 4: 5, 5: 4, 6: 4}[n] + 1):
            for gaps in itertools.product(range(0, n + 1), repeat=r - 1):
                ds = [0]
                for g in gaps:
                    ds.append(ds[-1] + g)
                if exposed(n, ds):
                    assert construct(n, ds, 0) is None
                    continue
                pts = [construct(n, ds, w) for w in (0, 1)]
                assert pts[0] != pts[1]
                for x in pts:
                    assert member(n, ds, x), (n, ds, x)
                    assert interior(n, ds, x), (n, ds, x)
                nchecked += 1
    out(f'  {nchecked} non-exposed d checked (n=3..6), both points interior and distinct in every case')
    # sketch 1: two interior lattice points of 2 Koz(n;d), by varying one summand
    n2 = 0
    for n in range(3, 7):
        for r in range(1, 4):
            for gaps in itertools.product(range(0, n + 1), repeat=r - 1):
                ds = [0]
                for g in gaps:
                    ds.append(ds[-1] + g)
                pts = [sum_of_twoK(n, ds, w) for w in (0, 1)]
                assert pts[0] != pts[1]
                for x in pts:
                    assert interior(n, repeat(ds, 2), x), (n, ds, x)
                n2 += 1
    out(f'  sketch 1 points: {n2} cases (n=3..6, r<=3), two distinct interior lattice points of 2Koz(n;d) each')

    # ---------------- F. stored data
    out('\nF. The 47 stored h*-vectors (V section D and R), against this implementation and the three statements')
    stored = read_stored()
    out(f'  read {len(stored)} cases, {sum(1 for c in stored.values() if c["src"] == "V")} from V')
    for (n, ds), cse in sorted(stored.items(), key=lambda kv: (len(kv[0][1]), kv[0][0], kv[0][1])):
        h, D = cse['h'], cse['D']
        D2, co = ehrhart(R[n], list(ds))
        assert D2 == D, (n, ds)
        mine = hstar_from_L(co, D)
        Ls = L_from_hstar(h, D)
        s = len(h) - 1
        codeg = D + 1 - s
        r = len(ds)
        pred = r * a2[n] + sum(Q(n, ds[k] - ds[j]) for j in range(r) for k in range(j + 1, r))
        flags = [f'h*=mine:{mine == h}', f't2={Ls[2]}', f'formula:{pred == Ls[2]}']
        if 'L' in cse:
            Lst = cse['L'] + [Fr(0)] * (len(Ls) - len(cse['L']))
            flags.append(f'storedL=L(h*):{Lst == Ls}')
            assert Lst == Ls, (n, ds)
        if 'int' in cse:
            i1, i2 = [(-1) ** D * peval(Ls, -t) for t in (1, 2)]
            flags.append(f'int(P),int(2P)={int(i1)},{int(i2)} stored:{[i1, i2] == cse["int"][:2]}')
            assert [i1, i2] == cse['int'][:2]
        if n >= 3:
            ex = exposed(n, list(ds))
            flags += [f'codeg={codeg}', f'thm:{(2 if ex else 1) == codeg}', f'h*_s={h[s]}', f'pal:{h == h[::-1]}']
            assert (2 if ex else 1) == codeg and h[s] >= 2 and h != h[::-1]
        assert mine == h and pred == Ls[2], (n, ds)
        out(f'  ({n};{",".join(map(str, ds))}) [{cse["src"]}] D={D} ' + ' '.join(flags))
    out('  all stored cases agree')

    out('\nINT lines (for the Sage cross-check): n d #int(P) #int(2P) codegree')
    for n, ds, i1, i2, cg in INT:
        if n <= 4 and len(ds) <= 3 and ds[-1] <= 4:
            out(f'INT {n} {",".join(map(str, ds))} {i1} {i2} {cg}')


# ---------------------------------------------------------------- membership and interior, by water-filling (thm-chained)
def member(n, ds, x):
    """x (sequence of rationals, length N+1) in Koz(n; ds)? Water-filling parts, each checked to lie in Koz(n)."""
    c = [comb(n, k) for k in range(n + 1)]
    N = n + ds[-1]
    if len(x) != N + 1 or any(v < 0 for v in x):
        return False
    r = len(ds)

    def cap(k, l):
        m = k - ds[l]
        return c[m] if 0 <= m <= n else 0

    def Qf(i, k):                                   # i = number of summands from below, 0..r
        if i == 0:
            return Fr(0)
        return max(Fr(0), Fr(x[k]) - sum(cap(k, l) for l in range(i, r)))

    tot = [Fr(0)] * (N + 1)
    for i in range(1, r + 1):
        d = ds[i - 1]
        p = [Qf(i, m + d) - Qf(i - 1, m + d) for m in range(n + 1)]
        if p[0] != 1 or p[1] != n:
            return False
        mu = [p[k] / c[k] for k in range(n + 1)]
        if not all(mu[k] >= mu[k + 1] for k in range(1, n)) or mu[n] < 0:
            return False
        for m in range(n + 1):
            tot[m + d] += p[m]
    return tot == [Fr(v) for v in x]


def interior(n, ds, x):
    _, U = dim(n, ds)
    for M in (2, 4, 8, 16):
        dsM = repeat(ds, M)
        ok = True
        for k in U:
            for sgn in (1, -1):
                y = [M * Fr(v) for v in x]
                y[k] += sgn
                if not member(n, dsM, y):
                    ok = False
                    break
            if not ok:
                break
        if ok:
            return True
    return False


# ---------------------------------------------------------------- the constructions of the proofs
def interior_trunc(n, j):
    """Own coordinates (x_0..x_n) of a lattice point of Koz(n) whose truncation to degrees <= j (2 <= j <= n-1) is
    interior to the truncated simplex: x_j = 1, x_k = floor(c_k x_{k+1}/c_{k+1}) + 1 downward, zeros above j."""
    c = [comb(n, k) for k in range(n + 1)]
    x = [0] * (n + 1)
    x[0], x[1], x[j] = 1, n, 1
    for k in range(j - 1, 1, -1):
        x[k] = (c[k] * x[k + 1]) // c[k + 1] + 1
    return x


def interior_2K(n, which):
    """Interior lattice point of 2 Koz(n) (Prop. prop-hstar-props): x_n = 1, x_k = floor(c_k x_{k+1}/c_{k+1}) + 1;
    which = 1 raises x_2 by one."""
    c = [comb(n, k) for k in range(n + 1)]
    x = [0] * (n + 1)
    x[0], x[1], x[n] = 2, 2 * n, 1
    for k in range(n - 1, 1, -1):
        x[k] = (c[k] * x[k + 1]) // c[k + 1] + 1
    x[2] += which
    return x


def construct(n, ds, which):
    N = n + ds[-1]
    x = [0] * (N + 1)
    s, T = len(ds), None
    first = True
    while s > 0:
        top = ds[s - 1]
        if T is None or T - top >= n:                          # case 2: top summand untruncated
            m = sum(1 for d in ds[:s] if d == top)
            if m < 2:
                return None                                    # an exposed index
            a = interior_2K(n, which if first else 0)
            a[0] += m - 2                                      # + (m-2) * F_1 = (m-2)(1, n, 0, ..., 0)
            a[1] += (m - 2) * n
            for k in range(n + 1):
                x[top + k] += a[k]
            s -= m
            T = top + 1
        else:                                                  # case 1: every summand with T - d <= n-1 truncated
            A = [i for i in range(s) if T - ds[i] <= n - 1]
            for i in A:
                y = interior_trunc(n, T - ds[i])
                for k in range(n + 1):
                    x[ds[i] + k] += y[k]
            k0 = min(A)
            s, T = k0, ds[k0] + 1
        first = False
    return x


def sum_of_twoK(n, ds, which):
    """Sketch 1: sum over i of shift^{d_i} q, with q interior in 2Koz(n), the last summand's q varied."""
    N = n + ds[-1]
    x = [0] * (N + 1)
    for i, d in enumerate(ds):
        q = interior_2K(n, which if i == len(ds) - 1 else 0)
        for k in range(n + 1):
            x[d + k] += q[k]
    return x


# ---------------------------------------------------------------- stored data (parsers as in hstar_realrooted_check.py)
def read_stored():
    Rdir = 'runs/2026-10-20_article3-overnight-push/'
    txt = open(Rdir + '2026-10-20_kozlov_volume_ehrhart.txt').read()
    Dsec = txt.split('D. Ehrhart polynomials')[1].split('E. Discrete volume')[0]
    cases = {}
    pat = (r'n=(\d+) d=(\[[^\]]*\])\s+D=\s*(\d+) NV=(\d+)\s+h\*=(\[[^\]]*\])\s*\n\s*L\(t\) coeffs: (\[[^\]]*\])'
           r'[^\n]*\n[^\n]*interior\(t=1,2,3\)=(\[[^\]]*\])')
    for m in re.finditer(pat, Dsec):
        n = int(m[1])
        ds = tuple(ast.literal_eval(m[2]))
        L = [Fr(s) for s in ast.literal_eval(m[6])]
        ints = [Fr(int(a), int(b)) for a, b in re.findall(r'Fraction\((-?\d+), (\d+)\)', m[7])]
        cases[(n, ds)] = dict(D=int(m[3]), h=ast.literal_eval(m[5]), L=L, int=ints, src='V')
    rev = open(Rdir + '2026-10-20_review-volume-ehrhart.txt').read()
    for m in re.finditer(r'n=(\d+) d=\(([^)]*)\) NV=(\d+) h\*=(\[[^\]]*\])', rev):
        n = int(m[1])
        ds = tuple(int(x) for x in m[2].split(','))
        h = ast.literal_eval(m[4])
        if (n, ds) in cases:
            assert cases[(n, ds)]['h'] == h, (n, ds)
        else:
            cases[(n, ds)] = dict(D=dim(n, ds)[0], h=h, src='R')
    assert len(cases) == 47, len(cases)
    return cases


if __name__ == '__main__':
    main()
