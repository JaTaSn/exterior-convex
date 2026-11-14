#!/usr/bin/env python3
"""kozlov_volume_ehrhart.py -- volume, discrete volume and Ehrhart theory of the
Kozlov simplex Koz(n) and the Kozlov polytope Koz(n; d).

Changelog (reverse chronological):
  2026-10-20  Claude (overnight article-3 push): created.  Reproduces every
              number in working-notes/kozlov-polytope-volume-and-ehrhart.org.
              Sections:
                A  Koz(n): normalised volume, lattice points L_n, |S_n|,
                   h*-vector three ways (normaliz; fundamental-parallelepiped
                   ascent formula; Savage-Schuster s-Eulerian formula),
                   group Z^{n-1}/Lambda, interior points, IDP (normaliz).
                B  The staircase volume formula NV(Koz(n;d)) against normaliz
                   multiplicities, rank 2 all d, rank 3/4 samples, and general
                   leg vectors (log-concave: must hold; non-log-concave: test).
                C  Lattice-point additivity and the chained decomposition:
                   #lattice points (normaliz) = |L_n + shift L_n + ...| (direct
                   sumset) = #chained L_n-tuples (transfer matrix).
                D  Ehrhart polynomials of Koz(n;d) via the transfer matrix
                   (t*Koz(n;d) = Koz(n; d repeated t times)), checked against
                   normaliz where feasible; h*-vectors, palindromy, interior
                   points, IDP.
                E  Discrete volume: |FF(n;d)| vs lattice points vs NV; fill
                   rates; the zero-shift and constant-gap limits (Perron roots).
              Run:  python3 code/oneoff/kozlov_volume_ehrhart.py [sections]
              from the project directory; output recorded in
              runs/2026-10-20_article3-overnight-push/2026-10-20_kozlov_volume_ehrhart.txt.  Needs the normaliz
              binary on PATH.  Imports code/linusson_ff_counting.py for |FF|.
"""

import os
import sys
import subprocess
import tempfile
from fractions import Fraction
from functools import lru_cache
from itertools import product as iproduct
from math import comb, factorial, prod, gcd

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(HERE, '..'))
import linusson_ff_counting as LFF  # noqa: E402

NORMALIZ = 'normaliz'


# ---------------------------------------------------------------------------
# basic objects
# ---------------------------------------------------------------------------

def kozvec(n):
    """c = (C(n,0), ..., C(n,n)); vertex j of Koz(n) is (c_0..c_j, 0..0)."""
    return [comb(n, k) for k in range(n + 1)]


def vertices_RA(c):
    """Vertices F_j = (c_0, ..., c_j, 0, ..., 0), j = 1..n, of the right-angle
    simplex with full coordinate vector c (c_0, c_1 constant coordinates)."""
    n = len(c) - 1
    return [tuple(c[k] if k <= j else 0 for k in range(n + 1))
            for j in range(1, n + 1)]


def shift(v, d, N):
    w = [0] * (N + 1)
    for k, y in enumerate(v):
        w[k + d] += y
    return tuple(w)


def minkowski_vertex_sums(c, ds):
    n = len(c) - 1
    N = n + ds[-1]
    V = vertices_RA(c)
    pts = set()
    for choice in iproduct(V, repeat=len(ds)):
        s = [0] * (N + 1)
        for v, d in zip(choice, ds):
            for k, y in enumerate(v):
                s[k + d] += y
        pts.add(tuple(s))
    return sorted(pts)


def dimension(n, ds):
    U = set()
    for d in ds:
        U |= set(range(d + 2, d + n + 1))
    return len(U)


def lattice_points_RA(c):
    """All integer points of conv(F_1..F_n): (c0, c1, x2..xn) with
    1 >= x2/c2 >= ... >= xn/cn >= 0."""
    n = len(c) - 1
    out = []

    def rec(k, prefix, ratio):          # ratio = x_{k-1}/c_{k-1} (Fraction)
        if k > n:
            out.append(tuple(prefix))
            return
        hi = (ratio * c[k]).__floor__()
        for x in range(hi + 1):
            rec(k + 1, prefix + [x], Fraction(x, c[k]))
    rec(2, [c[0], c[1]], Fraction(1))
    return out


# --- Kruskal-Katona (cardinality indexing: f_k = # k-subsets) --------------

def kk_upper(m, k):
    """Max #(k+1)-sets on a family of m k-sets (k >= 1): sum C(a_i, i+1)
    over the k-binomial expansion m = C(a_k,k) + C(a_{k-1},k-1) + ..."""
    total = 0
    i = k
    while m > 0 and i >= 1:
        a = i
        while comb(a + 1, i) <= m:
            a += 1
        total += comb(a, i + 1)
        m -= comb(a, i)
        i -= 1
    return total


def is_fvector(f):
    """f = (f_0, ..., f_n), f_0 = 1, f_k = # faces of cardinality k."""
    for k in range(1, len(f) - 1):
        if f[k + 1] > kk_upper(f[k], k):
            return False
    return True


def S_n(n):
    return [x for x in lattice_points_RA(kozvec(n)) if is_fvector(x)]


# --- top / indeg and the transfer matrix ------------------------------------

def tp(x):
    return max(j for j, y in enumerate(x) if y > 0)


def indeg(x, c):
    for j in range(len(c)):
        if x[j] < c[j]:
            return j
    return len(c)          # = n+1, x is the top vertex


def joint(points, c):
    """A[tau][iota] = #{x : tp(x) = tau, indeg(x) = iota}, tau, iota in 0..n+1."""
    n = len(c) - 1
    A = [[0] * (n + 2) for _ in range(n + 2)]
    for x in points:
        A[tp(x)][indeg(x, c)] += 1
    return A


def transfer(A, delta):
    """T[tau][tau'] = #{x : tp(x) = tau', indeg(x) + delta > tau}."""
    R = len(A)
    return [[sum(A[t2][i] for i in range(R) if i + delta > t) for t2 in range(R)]
            for t in range(R)]


def chained_count(A, ds):
    """#chained tuples (x_1..x_r), chaining tp(x_{i-1}) < indeg(x_i) + delta_i."""
    R = len(A)
    v = [sum(row) for row in A]
    for i in range(1, len(ds)):
        T = transfer(A, ds[i] - ds[i - 1])
        v = [sum(v[a] * T[a][b] for a in range(R)) for b in range(R)]
    return sum(v)


def sumset_count(points, ds):
    """|points + shift^{d_2} points + ...| by direct enumeration."""
    n = len(points[0]) - 1
    N = n + ds[-1]
    cur = {shift(p, ds[0], N) for p in points}
    for d in ds[1:]:
        sh = [shift(p, d, N) for p in points]
        cur = {tuple(a + b for a, b in zip(x, y)) for x in cur for y in sh}
    return len(cur)


def repeat_shifts(ds, t):
    return [d for d in ds for _ in range(t)]


def ehrhart_values_transfer(A, ds, tmax):
    """L(t) = #lattice points of t*Koz(n;d) = #chained tuples for d^(t)."""
    return [1] + [chained_count(A, repeat_shifts(ds, t)) for t in range(1, tmax + 1)]


# ---------------------------------------------------------------------------
# h*-vectors and polynomials
# ---------------------------------------------------------------------------

def hstar_from_values(L, D):
    """h*_0..h*_D from L(0..D): sum_t L(t) z^t = h*(z)/(1-z)^{D+1}."""
    h = []
    for i in range(D + 1):
        h.append(sum((-1) ** j * comb(D + 1, j) * L[i - j] for j in range(i + 1)))
    while len(h) > 1 and h[-1] == 0:
        h.pop()
    return [int(x) if Fraction(x).denominator == 1 else x for x in h]


def ehrhart_from_hstar(h, D, t):
    return sum(hi * comb(t + D - i, D) for i, hi in enumerate(h))


def interp_poly(L):
    """Coefficients (Fractions, low->high) of the polynomial through (t, L[t])."""
    m = len(L)
    # Newton forward differences
    diffs = [list(map(Fraction, L))]
    for _ in range(1, m):
        prev = diffs[-1]
        diffs.append([prev[i + 1] - prev[i] for i in range(len(prev) - 1)])
    coeffs = [Fraction(0)] * m
    # sum_k Delta^k L(0) * C(t,k)
    for k in range(m):
        a = diffs[k][0]
        # C(t,k) = t(t-1)...(t-k+1)/k!
        poly = [Fraction(1)]
        for j in range(k):
            poly = [Fraction(0)] + poly
            for i in range(len(poly) - 1):
                poly[i] -= j * poly[i + 1]
        for i, pc in enumerate(poly):
            coeffs[i] += a * pc / factorial(k)
    while len(coeffs) > 1 and coeffs[-1] == 0:
        coeffs.pop()
    return coeffs


def eval_poly(co, t):
    return sum(c * t ** i for i, c in enumerate(co))


# --- Koz(n) h* by the fundamental parallelepiped -----------------------------

def hstar_parallelepiped(n):
    """h*_i = #{(r_2..r_n), 0 <= r_k < C(n,k) : asc = i}, where with
    rho_1 = 0, rho_k = r_k/C(n,k), asc = #{k in 1..n-1 : rho_k < rho_{k+1}}
    (derivation in the note, section ehrhart-simplex).  DP over k with the
    state rho_k; exact rationals."""
    c = kozvec(n)
    # dist: dict rho -> polynomial (list) in z counting ascents so far
    dist = {Fraction(0): [1]}
    for k in range(2, n + 1):
        new = {}
        states = sorted(dist)
        for r in range(c[k]):
            rho = Fraction(r, c[k])
            acc = None
            for s in states:
                pol = dist[s]
                shiftz = 1 if s < rho else 0
                cur = new.setdefault(rho, [])
                need = len(pol) + shiftz
                if len(cur) < need:
                    cur.extend([0] * (need - len(cur)))
                for i, a in enumerate(pol):
                    cur[i + shiftz] += a
        dist = new
    tot = []
    for pol in dist.values():
        if len(tot) < len(pol):
            tot.extend([0] * (len(pol) - len(tot)))
        for i, a in enumerate(pol):
            tot[i] += a
    while len(tot) > 1 and tot[-1] == 0:
        tot.pop()
    return tot


def s_eulerian(s, e0=0):
    """Savage-Schuster: sum over e in I^(s) (0 <= e_i < s_i) of z^asc(e),
    asc(e) = #{0 <= i < d : e_i/s_i < e_{i+1}/s_{i+1}}, e_0 = e0, s_0 = 1.
    Brute force (small s only)."""
    d = len(s)
    tot = [0] * (d + 1)
    for e in iproduct(*[range(si) for si in s]):
        ratios = [Fraction(e0, 1)] + [Fraction(ei, si) for ei, si in zip(e, s)]
        a = sum(1 for i in range(d) if ratios[i] < ratios[i + 1])
        tot[a] += 1
    while len(tot) > 1 and tot[-1] == 0:
        tot.pop()
    return tot


def invariant_factors(mods):
    """Invariant factors of (+) Z/m_i (m_i >= 1), as sorted list (>1 only)."""
    from collections import defaultdict
    primes = set()
    for m in mods:
        x, p = m, 2
        while p * p <= x:
            while x % p == 0:
                primes.add(p)
                x //= p
            p += 1
        if x > 1:
            primes.add(x)
    L = len(mods)
    fac = [1] * L
    for p in primes:
        vals = []
        for m in mods:
            v = 0
            while m % p == 0:
                m //= p
                v += 1
            vals.append(v)
        vals.sort()
        for i in range(L):
            fac[i] *= p ** vals[i]
    return [f for f in fac if f > 1]


# ---------------------------------------------------------------------------
# normaliz
# ---------------------------------------------------------------------------

def run_normaliz(points, goals, timeout=600):
    """points: list of integer tuples in Z^{N+1}.  Returns dict with keys
    multiplicity, rank, hilbert_poly (Fractions), deg1_HB (bool), n_lattice,
    n_hb (Hilbert basis size), raw."""
    dim = len(points[0])
    with tempfile.TemporaryDirectory() as td:
        fn = os.path.join(td, 'p.in')
        with open(fn, 'w') as f:
            f.write('amb_space %d\npolytope %d\n' % (dim + 1, len(points)))
            for p in points:
                f.write(' '.join(map(str, p)) + '\n')
            for g in goals:
                f.write(g + '\n')
        subprocess.run([NORMALIZ, '-c', '-x=4', fn], stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL, timeout=timeout, check=True)
        txt = open(os.path.join(td, 'p.out')).read()
    res = {'raw': txt}
    lines = txt.splitlines()
    for i, ln in enumerate(lines):
        s = ln.strip()
        if s.startswith('multiplicity ='):
            res['multiplicity'] = Fraction(s.split('=')[1].strip())
        elif s.startswith('rank ='):
            res['rank'] = int(s.split('=')[1].split()[0])
        elif s.startswith('Hilbert polynomial:') or s.startswith('Ehrhart polynomial:'):
            co = [Fraction(x) for x in lines[i + 1].split()]
            den = int(lines[i + 2].split('=')[1])
            res['hilbert_poly'] = [x / den for x in co]
        elif 'Hilbert basis elements are of degree 1' in s:
            res['deg1_HB'] = True
        elif s.endswith('Hilbert basis elements') and s.split()[0].isdigit():
            res['n_hb'] = int(s.split()[0])
        elif 'lattice points in polytope' in s and s.split()[0].isdigit():
            res['n_lattice'] = int(s.split()[0])
    if 'n_hb' in res and 'n_lattice' in res:
        res.setdefault('deg1_HB', res['n_hb'] == res['n_lattice'])
    return res


# ---------------------------------------------------------------------------
# the staircase volume formula
# ---------------------------------------------------------------------------

def nv_staircase(c, ds):
    """Normalised (lattice) volume of RA(c; ds) by the staircase cells:
    sum over 1 = t_0 <= t_1 <= ... <= t_r = d_r + n with
    t_{i-1} - d_i >= 1, t_i - d_i <= n, of
    multinomial(D; t_i - t_{i-1}) * prod_i prod_{k in (t_{i-1}, t_i]} c_{k - d_i}.
    Valid (proved) when every gap is <= n-1 and (c_2..c_n) is log-concave;
    for a gap >= n-1 the polytope is a product and we multiply blocks."""
    n = len(c) - 1
    r = len(ds)
    # split into product blocks at gaps >= n-1
    blocks, cur = [], [ds[0]]
    for a, b in zip(ds, ds[1:]):
        if b - a >= n - 1:
            blocks.append(cur)
            cur = [b]
        else:
            cur.append(b)
    blocks.append(cur)
    if len(blocks) > 1:
        dims = [dimension(n, [x - bl[0] for x in bl]) for bl in blocks]
        D = sum(dims)
        mult = factorial(D)
        for dd in dims:
            mult //= factorial(dd)
        return mult * prod(nv_staircase(c, [x - bl[0] for x in bl]) for bl in blocks)
    D = dimension(n, ds)
    total = 0

    def rec(i, tprev, acc_mult, acc_prod, used):
        # choose t_i (i = 1..r); block i = (t_{i-1}, t_i] belongs to summand i
        nonlocal total
        di = ds[i - 1]
        if i == r:
            choices = [ds[-1] + n]
        else:
            choices = range(max(tprev, ds[i] + 1), di + n + 1)
        for ti in choices:
            if ti < tprev or ti - di > n or tprev - di < 1:
                continue
            l = ti - tprev
            p = prod(c[k - di] for k in range(tprev + 1, ti + 1))
            m2 = acc_mult * comb(used + l, l)
            if i == r:
                total += m2 * acc_prod * p
            else:
                rec(i + 1, ti, m2, acc_prod * p, used + l)
    rec(1, 1, 1, 1, 0)
    assert r == 1 or True
    return total


def nv_rank2_closed(n, d):
    """Rank-2 closed form, 0 <= d <= n-1, m = n-d:
    NV = sum_{g=1}^{m} C(n-1+d, d+g-1) * prod_{k=2}^{d+g} C(n,k) * prod_{k=g+1}^{n} C(n,k)."""
    m = n - d
    D = n - 1 + d
    return sum(comb(D, d + g - 1) * prod(comb(n, k) for k in range(2, d + g + 1))
               * prod(comb(n, k) for k in range(g + 1, n + 1)) for g in range(1, m + 1))


# ---------------------------------------------------------------------------
# sections
# ---------------------------------------------------------------------------

def section_A(nmax_nmz=7, nmax_formula=12):
    print('=' * 78)
    print('A. The Kozlov simplex Koz(n)')
    print('=' * 78)
    print('n | NV=prod_{k>=2}C(n,k) | Euclid vol | #L_n | |S_n| | |S_n|/#L_n | group Z^{n-1}/Lambda (invariant factors)')
    for n in range(2, 10):
        c = kozvec(n)
        NV = prod(c[2:])
        Ln = lattice_points_RA(c) if n <= 8 else None
        Sn = LFF.ff_count(n, [0], True)
        inv = invariant_factors(c[2:])
        print('%d | %d | %s | %s | %d | %s | %s' % (
            n, NV, Fraction(NV, factorial(n - 1)),
            len(Ln) if Ln else '-', Sn,
            (Fraction(Sn, len(Ln)) if Ln else '-'), inv))
    print()
    print('Check |S_n| by Kruskal-Katona filter of L_n vs Linusson count:')
    for n in range(2, 8):
        print('  n=%d  KK-filter %d  Linusson %d' % (n, len(S_n(n)), LFF.ff_count(n, [0], True)))
    print()
    print('h*-vectors of Koz(n): (a) normaliz, (b) parallelepiped ascent DP, (c) s-Eulerian (Savage-Schuster, s=(C(n,2..n)), e0=0)')
    for n in range(2, nmax_formula + 1):
        hb = hstar_parallelepiped(n)
        line = 'n=%2d  DP: %s  sum=%d  deg=%d' % (n, hb, sum(hb), len(hb) - 1)
        assert sum(hb) == prod(kozvec(n)[2:])
        if n <= 6:
            hc = s_eulerian(kozvec(n)[2:])
            hc2 = s_eulerian(list(reversed(kozvec(n)[2:])))
            line += '  SS(s)=%s SS(rev s)=%s' % (hc, hc2)
            assert hc == hb and hc2 == hb
        if n <= nmax_nmz:
            r = run_normaliz(vertices_RA(kozvec(n)), ['EhrhartSeries', 'HilbertBasis'] if n <= 6 else ['EhrhartSeries'])
            D = n - 1
            L = [eval_poly(r['hilbert_poly'], t) for t in range(D + 1)]
            hn = hstar_from_values(L, D)
            line += '  nmz=%s' % hn
            assert hn == hb, (hn, hb)
            if 'deg1_HB' in r:
                line += '  IDP(nmz)=%s' % r['deg1_HB']
        print(line)
        pal = hb == list(reversed(hb))
        # unimodal / log-concave
        lc = all(hb[i] ** 2 >= hb[i - 1] * hb[i + 1] for i in range(1, len(hb) - 1))
        print('       palindromic=%s  log-concave=%s  h*_1=%s (=#L_n - n)' % (pal, lc, hb[1] if len(hb) > 1 else 0))
    print()
    print('Ehrhart polynomials L_{Koz(n)}(t) (transfer-matrix values, interpolated):')
    for n in range(2, 8):
        c = kozvec(n)
        A = joint(lattice_points_RA(c), c)
        L = ehrhart_values_transfer(A, [0], n + 1)
        co = interp_poly(L[:n])
        assert all(eval_poly(co, t) == L[t] for t in range(len(L)))
        # cross-check with h*
        hb = hstar_parallelepiped(n)
        assert all(ehrhart_from_hstar(hb, n - 1, t) == L[t] for t in range(len(L)))
        print('  n=%d  L(t) = %s   [L(0..%d) = %s]' % (n, ' + '.join('%s t^%d' % (x, i) for i, x in enumerate(co)), n + 1, L))
        # interior points by reciprocity
        Dm = n - 1
        inter = [(-1) ** Dm * eval_poly(co, -t) for t in range(1, 5)]
        print('        interior points of t*Koz(n), t=1..4: %s' % inter)
    print()


def section_B():
    print('=' * 78)
    print('B. Staircase volume formula vs normaliz multiplicity')
    print('=' * 78)
    print('Rank 2, Koz(n;0,d): D, NV(normaliz), NV(staircase), NV(rank-2 closed form), Euclid vol = NV/D!')
    for n in range(2, 8):
        for d in range(0, n + 2):
            c = kozvec(n)
            pts = minkowski_vertex_sums(c, [0, d])
            r = run_normaliz(pts, ['Multiplicity'])
            D = r['rank'] - 1
            assert D == dimension(n, [0, d])
            nvs = nv_staircase(c, [0, d])
            closed = nv_rank2_closed(n, d) if d <= n - 1 else None
            ok = (r['multiplicity'] == nvs) and (closed is None or closed == nvs)
            print('  n=%d d=%d  D=%2d  NV_nmz=%s  NV_stair=%d  closed=%s  vol=%s  %s' % (
                n, d, D, r['multiplicity'], nvs, closed, Fraction(nvs, factorial(D)),
                'OK' if ok else 'MISMATCH'))
            assert ok
    print()
    print('Rank 3 and 4 samples:')
    samples = []
    for n in (3, 4, 5):
        for ds in ([0, 0, 0], [0, 0, 1], [0, 1, 1], [0, 1, 2], [0, 1, 3], [0, 2, 3],
                   [0, 2, 4], [0, 1, 4], [0, 3, 4], [0, 0, 2], [0, 2, 2]):
            samples.append((n, ds))
    samples += [(4, [0, 1, 2, 3]), (4, [0, 0, 1, 2]), (3, [0, 1, 2, 3]), (4, [0, 2, 3, 5]),
                (6, [0, 1, 2]), (6, [0, 2, 3])]
    for n, ds in samples:
        c = kozvec(n)
        r = run_normaliz(minkowski_vertex_sums(c, ds), ['Multiplicity'])
        nvs = nv_staircase(c, ds)
        ok = r['multiplicity'] == nvs
        print('  n=%d d=%s  D=%d  NV_nmz=%s  NV_stair=%d  %s' % (n, ds, r['rank'] - 1,
                                                             r['multiplicity'], nvs, 'OK' if ok else 'MISMATCH'))
        assert ok
    print()
    print('General leg vectors c = (1, c_1, c_2..c_n):')
    tests = [
        ((1, 3, 3, 1), 'binomial n=3'),
        ((1, 2, 5, 7, 4, 1), 'log-concave'),
        ((1, 1, 2, 3, 3, 2), 'log-concave'),
        ((1, 4, 1, 1, 1, 1), 'constant (log-concave)'),
        ((1, 2, 1, 1, 2), 'NOT log-concave: (c2,c3,c4)=(1,1,2)'),
        ((1, 2, 1, 3, 1, 3), 'NOT log-concave'),
        ((1, 5, 1, 2, 5), 'NOT log-concave (log-convex)'),
    ]
    for c, label in tests:
        n = len(c) - 1
        for ds in ([0, 1], [0, 2], [0, 1, 2], [0, 0, 1]):
            if ds[-1] > n:
                continue
            r = run_normaliz(minkowski_vertex_sums(list(c), ds), ['Multiplicity'])
            nvs = nv_staircase(list(c), ds)
            print('  c=%s (%s) d=%s  NV_nmz=%s  NV_stair=%d  %s' % (
                c, label, ds, r['multiplicity'], nvs, 'OK' if r['multiplicity'] == nvs else 'DIFFERS'))
    print()


def section_C():
    print('=' * 78)
    print('C. Lattice-point additivity and the chained decomposition')
    print('   #lattice pts (normaliz) = |L_n + shift L_n + ...| (sumset) = #chained L_n-tuples')
    print('=' * 78)
    cases = []
    for n in range(2, 7):
        for d in range(0, n + 1):
            cases.append((n, [0, d]))
    for n in (3, 4, 5):
        for ds in ([0, 0, 0], [0, 0, 1], [0, 1, 1], [0, 1, 2], [0, 1, 3], [0, 2, 3], [0, 2, 4]):
            cases.append((n, ds))
    cases += [(4, [0, 1, 2, 3]), (3, [0, 0, 1, 2]), (4, [0, 0, 1, 1])]
    for n, ds in cases:
        c = kozvec(n)
        Ln = lattice_points_RA(c)
        A = joint(Ln, c)
        ch = chained_count(A, ds)
        big = (n == 6 and len(ds) == 2 and ds[1] <= 1) or n <= 5
        ss = sumset_count(Ln, ds) if (n <= 5 or (n == 6 and len(ds) == 2)) and not (n == 5 and len(ds) == 3 and ds[-1] >= 3) else None
        r = run_normaliz(minkowski_vertex_sums(c, ds), ['NumberLatticePoints'])
        nl = r.get('n_lattice')
        ok = (nl == ch) and (ss is None or ss == ch)
        print('  n=%d d=%-12s  #lattice(nmz)=%-8s  sumset=%-8s  chained=%-8d %s' % (
            n, ds, nl, ss, ch, 'OK' if ok else 'MISMATCH'))
        assert ok
    print()
    print('Non-log-concave leg vector: does additivity fail?')
    for c in ((1, 2, 1, 1, 2), (1, 2, 1, 3, 1, 3), (1, 5, 1, 2, 5)):
        c = list(c)
        Lc = lattice_points_RA(c)
        A = joint(Lc, c)
        for ds in ([0, 1], [0, 2], [0, 0, 1]):
            if ds[-1] > len(c) - 1:
                continue
            r = run_normaliz(minkowski_vertex_sums(c, ds), ['NumberLatticePoints'])
            print('  c=%s d=%s  #lattice=%s  sumset=%d  chained=%d' % (
                c, ds, r.get('n_lattice'), sumset_count(Lc, ds), chained_count(A, ds)))
    print()


def section_D(maxnv=3 * 10 ** 7):
    print('=' * 78)
    print('D. Ehrhart polynomials and h*-vectors of Koz(n;d)')
    print('   (transfer-matrix values; normaliz check when NV <= %d)' % maxnv)
    print('=' * 78)
    cases = []
    for n in range(2, 7):
        for d in range(0, n + 1):
            cases.append((n, [0, d]))
    cases += [(7, [0, 1]), (7, [0, 2])]
    for n in (3, 4):
        for ds in ([0, 0, 1], [0, 1, 1], [0, 1, 2], [0, 1, 3], [0, 2, 3], [0, 2, 4]):
            cases.append((n, ds))
    cases += [(5, [0, 1, 2]), (5, [0, 2, 4]), (3, [0, 1, 2, 3])]
    for n, ds in cases:
        c = kozvec(n)
        A = joint(lattice_points_RA(c), c)
        D = dimension(n, ds)
        L = ehrhart_values_transfer(A, ds, D + 1)
        h = hstar_from_values(L, D)
        co = interp_poly(L[:D + 1])
        assert eval_poly(co, D + 1) == L[D + 1]          # degree <= D consistency
        nv = nv_staircase(c, ds)
        assert sum(h) == nv, (n, ds, sum(h), nv)
        assert co[-1] * factorial(D) == nv
        chk = ''
        if nv <= maxnv:
            r = run_normaliz(minkowski_vertex_sums(c, ds), ['EhrhartSeries', 'HilbertBasis'] if nv <= 10 ** 6 else ['EhrhartSeries'])
            Ln = [eval_poly(r['hilbert_poly'], t) for t in range(D + 2)]
            chk = 'nmz:%s' % ('OK' if Ln == L else 'MISMATCH')
            assert Ln == L
            if 'deg1_HB' in r:
                chk += ' IDP:%s' % r['deg1_HB']
        pal = h == list(reversed(h))
        nonneg = all(x >= 0 for x in h)
        uni = all(h[i] <= h[i + 1] for i in range(h.index(max(h)))) and \
            all(h[i] >= h[i + 1] for i in range(h.index(max(h)), len(h) - 1))
        lc = all(h[i] ** 2 >= h[i - 1] * h[i + 1] for i in range(1, len(h) - 1))
        inter = [(-1) ** D * eval_poly(co, -t) for t in range(1, 4)]
        codeg = next((t for t in range(1, D + 3) if (-1) ** D * eval_poly(co, -t) > 0), None)
        print('  n=%d d=%-10s D=%2d NV=%-12d h*=%s' % (n, ds, D, nv, h))
        negc = [i for i, x in enumerate(co) if x < 0]
        print('        L(t) coeffs: %s%s' % ([str(x) for x in co], '  NEGATIVE at %s' % negc if negc else ''))
        print('        deg h*=%d codegree=%s palin=%s unimodal=%s logconc=%s  interior(t=1,2,3)=%s %s' % (
            len(h) - 1, codeg, pal, uni, lc, inter, chk))
    print()


def perron(M, iters=4000):
    """Spectral radius of a nonnegative matrix by power iteration (float)."""
    R = len(M)
    v = [1.0] * R
    lam = 0.0
    for _ in range(iters):
        w = [sum(v[a] * M[a][b] for a in range(R)) for b in range(R)]
        s = sum(w)
        if s == 0:
            return 0.0
        lam = s / sum(v)
        v = [x / s for x in w]
    return lam


def section_E():
    print('=' * 78)
    print('E. Discrete volume: |FF| vs #lattice points vs NV/D!')
    print('=' * 78)
    print('Rank 1: n, |S_n|, #L_n, NV, vol=NV/(n-1)!, fill=|S_n|/#L_n')
    for n in range(2, 9):
        c = kozvec(n)
        Ln = len(lattice_points_RA(c))
        Sn = LFF.ff_count(n, [0], True)
        NV = prod(c[2:])
        print('  n=%d  |S|=%-6d #L=%-8d NV=%-12d vol=%-14s fill=%.6f' % (
            n, Sn, Ln, NV, Fraction(NV, factorial(n - 1)), Sn / Ln))
    print()
    print('Rank 2, Koz(n;0,d): |FF|, #lattice, Euclid vol, fill = |FF|/#lattice')
    for n in range(2, 8):
        c = kozvec(n)
        Lp = lattice_points_RA(c)
        A = joint(Lp, c)
        for d in range(0, n + 1):
            ff = LFF.ff_count(n, [0, d], True)
            nl = chained_count(A, [0, d])
            D = dimension(n, [0, d])
            nv = nv_staircase(c, [0, d])
            print('  n=%d d=%d  D=%2d  |FF|=%-10d #lat=%-10d vol=%-22s fill=%.6f' % (
                n, d, D, ff, nl, Fraction(nv, factorial(D)), ff / nl))
    print()
    print('Rank 3 samples:')
    for n in (3, 4, 5, 6):
        c = kozvec(n)
        A = joint(lattice_points_RA(c), c)
        for ds in ([0, 0, 0], [0, 1, 2], [0, 2, 4], [0, 1, 3], [0, n - 1, 2 * n - 2]):
            ff = LFF.ff_count(n, ds, True)
            nl = chained_count(A, ds)
            print('  n=%d d=%-14s |FF|=%-12d #lat=%-12d fill=%.6f' % (n, ds, ff, nl, ff / nl))
    print()
    print('Zero shifts, rank r -> infinity: a(r)=|FF(n;0^r)|, e(r)=#lat(r Koz(n)), ratio')
    for n in (4, 5, 6):
        c = kozvec(n)
        A = joint(lattice_points_RA(c), c)
        As = joint(S_n(n), c)
        row = []
        for r in (1, 2, 3, 5, 10, 20, 40, 80):
            a = chained_count(As, [0] * r)
            e = chained_count(A, [0] * r)
            if r <= 3:
                assert a == LFF.ff_count(n, [0] * r, True)
            row.append('r=%d:%.4f' % (r, a / e))
        print('  n=%d  %s' % (n, '  '.join(row)))
    print()
    print('Constant gap delta, rank r -> infinity: Perron roots lambda_FF(delta), lambda_L(delta);')
    print('fill rate ~ C*(lambda_FF/lambda_L)^r')
    for n in (3, 4, 5, 6):
        c = kozvec(n)
        A = joint(lattice_points_RA(c), c)
        As = joint(S_n(n), c)
        for delta in range(1, n):
            lf = perron(transfer(As, delta))
            ll = perron(transfer(A, delta))
            print('  n=%d delta=%d  lambda_FF=%.6f  lambda_L=%.6f  ratio=%.6f   (|S_n|=%d, #L_n=%d)' % (
                n, delta, lf, ll, lf / ll, len(S_n(n)), sum(map(sum, A))))
    print()


def canonical_decomposition(x, c, ds):
    """Article 2's water-filling inverse Phi_d (lem-explicit-inverse), applied
    to an arbitrary lattice point x of RA(c; ds): returns the r components."""
    n = len(c) - 1
    r = len(ds)
    N = n + ds[-1]

    def cc(j):
        return c[j] if 0 <= j <= n else 0

    def Q(i, j):
        return max(0, x[j] - sum(cc(j - ds[k]) for k in range(i, r)))
    comps = []
    for i in range(1, r + 1):
        comps.append(tuple(Q(i, m + ds[i - 1]) - Q(i - 1, m + ds[i - 1]) for m in range(n + 1)))
    return comps


def is_chained(comps, c, ds):
    for i in range(1, len(ds)):
        if not tp(comps[i - 1]) < indeg(comps[i], c) + ds[i] - ds[i - 1]:
            return False
    return True


def section_X():
    print('=' * 78)
    print('X. Worked examples')
    print('=' * 78)
    for n, ds in ((3, [0]), (4, [0]), (3, [0, 1]), (3, [0, 2]), (4, [0, 1]), (4, [0, 0]), (4, [0, 2])):
        c = kozvec(n)
        D = dimension(n, ds)
        A = joint(lattice_points_RA(c), c)
        L = ehrhart_values_transfer(A, ds, D + 1)
        co = interp_poly(L[:D + 1])
        h = hstar_from_values(L, D)
        print('Koz(%d; %s): D=%d  NV=%d  vol=%s' % (n, ds, D, nv_staircase(c, ds), Fraction(nv_staircase(c, ds), factorial(D))))
        print('   vertices (%d): %s' % (len(set(minkowski_vertex_sums(c, ds))) if len(ds) == 1 else -1,
                                       vertices_RA(c) if len(ds) == 1 else ''))
        print('   L(t) = %s' % ' + '.join('(%s)t^%d' % (x, i) for i, x in enumerate(co)))
        print('   L(0..%d) = %s   h* = %s' % (D + 1, L, h))
        neg = [i for i, x in enumerate(co) if x < 0]
        print('   negative Ehrhart coefficients at degrees: %s' % neg)
        Lp = lattice_points_RA(c)
        Sset = set(S_n(n))
        if len(ds) == 1:
            bad = [x for x in Lp if x not in Sset]
            print('   lattice points that are not f-vectors (%d): %s' % (len(bad), bad))
        else:
            N = n + ds[-1]
            pts = set()
            sh = [[shift(p, d, N) for p in Lp] for d in ds]
            cur = set(sh[0])
            for layer in sh[1:]:
                cur = {tuple(a + b for a, b in zip(u, v)) for u in cur for v in layer}
            nonff, kinds = [], {}
            for x in sorted(cur):
                comps = canonical_decomposition(x, c, ds)
                assert is_chained(comps, c, ds)
                assert all(comp in set(Lp) for comp in comps)
                back = [0] * (N + 1)
                for comp, d in zip(comps, ds):
                    for k, y in enumerate(comp):
                        back[k + d] += y
                assert tuple(back) == x
                okf = tuple(comp in Sset for comp in comps)
                kinds[okf] = kinds.get(okf, 0) + 1
            print('   #lattice=%d  canonical parts all chained and in L_n: OK' % len(cur))
            print('   classification by (part_i is an f-vector?): %s' % kinds)
            print('   |FF| = %d  (=count of (True,..,True): %s)' % (LFF.ff_count(n, ds, True),
                  kinds.get(tuple([True] * len(ds)), 0) == LFF.ff_count(n, ds, True)))
        print()
    # full lattice-point listing of Koz(3;0,1) with canonical decomposition
    n, ds = 3, [0, 1]
    c = kozvec(n)
    Lp = lattice_points_RA(c)
    N = n + 1
    cur = sorted({tuple(a + b for a, b in zip(shift(p, 0, N), shift(q, 1, N))) for p in Lp for q in Lp})
    print('Koz(3;0,1): all %d lattice points with canonical decomposition (x = s1 + shift s2):' % len(cur))
    for x in cur:
        s1, s2 = canonical_decomposition(x, c, ds)
        print('   %s = %s + shift%s' % (x, s1, s2))
    print()
    # staircase cells of Koz(4;0,1)
    n, d = 4, 1
    c = kozvec(n)
    print('Staircase cells of Koz(4;0,1): C_g = conv(F_1..F_{d+g}) + shift conv(F_g..F_n), g = 1..n-d')
    for g in range(1, n - d + 1):
        a = prod(c[k] for k in range(2, d + g + 1))
        b = prod(c[k] for k in range(g + 1, n + 1))
        D = n - 1 + d
        print('   g=%d: blocks %s | %s, NV = C(%d,%d)*%d*%d = %d, vol = %s' % (
            g, list(range(2, d + g + 1)), list(range(d + g + 1, n + d + 1)), D, d + g - 1, a, b,
            comb(D, d + g - 1) * a * b, Fraction(comb(D, d + g - 1) * a * b, factorial(D))))
    print()


if __name__ == '__main__':
    secs = sys.argv[1:] or ['A', 'B', 'C', 'D', 'E', 'X']
    for s in secs:
        {'A': section_A, 'B': section_B, 'C': section_C, 'D': section_D, 'E': section_E, 'X': section_X}[s]()
