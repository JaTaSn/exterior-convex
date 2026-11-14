#!/usr/bin/env sage-python
"""staircase_lattice_paths.py -- staircase indices as lattice paths in a band (Part III, thm-staircase).
2026-11-09  Claude-Code (jts-mini) subagent.  Purpose: check the lattice-path reading of the
            staircase indices and the d = 0^r identification with the staircase triangulation,
            before they go into the manuscript (working-notes/staircase-lattice-paths-2026-11-09.org).

Run (bounded):
    cd PROJ && ulimit -v 8000000 && timeout 3000 sage code/oneoff/staircase_lattice_paths.py \
        | tee runs/2026-11-09_staircase-lattice-paths.txt

(A) For n <= 7, r <= 4 and every d with d_1 = 0 and all gaps in [0, n-1]: the staircase indices,
    enumerated from the paper's definition
        1 = t_0 <= t_1 <= ... <= t_r = N = n + d_r,  t_{i-1} - d_i >= 1,  t_i - d_i <= n,
    are in bijection with the monotone E/N lattice paths from (1, row 1) to (N, row r) that
      (A1) visit only the dots {(x, i) : d_i + 1 <= x <= d_i + n};
      (A2) every east step into column k in row i has k - d_i in [2, n] ("assignment" reading);
      (A3) stay (geometrically) between the boundary paths L = E^{n-1} N E^{d2} N ... N E^{dr}
           (lower) and U = E^{d2} N E^{d3} ... N E^{dr} N E^{n-1} (upper), d_i = gaps;
    via t_j = column of the j-th north step.  Counts against C(n+r-2, r-1) at d = 0^r, against
    n - d_2 at r = 2, and against a determinant (tested, attribution not checked).
(B) At d = 0^r, n <= 5, r <= 4: the staircase triangulation of Delta^{r-1} x Delta^{n-1} as
    defined in Ceballos-Padrol-Sarmiento 2015, Example 2.2 (monotone square paths in the r x n
    grid) is checked to be a triangulation (unimodular, right count, proper intersections); the
    Cayley trick (Santos 2005, Thm 1.4: slice at lambda = (1/r,...,1/r)) is checked on it; and the
    resulting mixed cells, mapped by e_j -> F_j, are compared with the paper's cells C_t.  The
    tiling of r*angle(c) by the C_t is checked for Kozlov, all-ones and non-log-concave c.
(C) Worked examples Koz(3;0,0,0), Koz(3;0,1), Koz(3;0,1,2): cells, blocks, NV by the formula of
    thm-staircase and by Sage, and the sum against NV of the polytope; vertices of the cells of
    3 Koz(3) in (x_2, x_3) for the figure.
"""
import sys
import time
from itertools import combinations, combinations_with_replacement, product
from math import comb

from sage.all import Polyhedron, QQ, factorial, binomial, matrix, ZZ


def say(*a):
    print(*a)
    sys.stdout.flush()


# ----------------------------------------------------------------------------------------------
# (A) combinatorics
# ----------------------------------------------------------------------------------------------

def shift_vectors(n, r):
    """sorted d with d_1 = 0 and every gap in [0, n-1]"""
    for gaps in product(range(n), repeat=r - 1):
        d = [0]
        for g in gaps:
            d.append(d[-1] + g)
        yield tuple(d)


def staircase_indices(n, d):
    """from the definition in the paper; d[i-1] is d_i"""
    r = len(d)
    N = n + d[-1]
    out = []
    for mid in combinations_with_replacement(range(1, N + 1), r - 1):
        t = (1,) + mid + (N,)
        if all(t[i - 1] - d[i - 1] >= 1 and t[i] - d[i - 1] <= n for i in range(1, r + 1)):
            out.append(t)
    return out


def all_words(n, d):
    r = len(d)
    N = n + d[-1]
    L = N - 1 + r - 1
    for npos in combinations(range(L), r - 1):
        w = ["E"] * L
        for p in npos:
            w[p] = "N"
        yield tuple(w)


def walk(w):
    x, row = 1, 1
    pts = [(x, row)]
    for s in w:
        if s == "E":
            x += 1
        else:
            row += 1
        pts.append((x, row))
    return pts


def north_cols(w):
    x, cols = 1, []
    for s in w:
        if s == "E":
            x += 1
        else:
            cols.append(x)
    return cols


def ok_dots(w, n, d):
    return all(d[row - 1] + 1 <= x <= d[row - 1] + n for (x, row) in walk(w))


def ok_assignment(w, n, d):
    x, row = 1, 1
    for s in w:
        if s == "E":
            x += 1
            if not (2 <= x - d[row - 1] <= n):
                return False
        else:
            row += 1
    return True


def word_U(n, d):
    w = []
    for j in range(1, len(d)):
        w += ["E"] * (d[j] - d[j - 1]) + ["N"]
    return tuple(w + ["E"] * (n - 1))


def word_L(n, d):
    w = ["E"] * (n - 1)
    for j in range(1, len(d)):
        w += ["N"] + ["E"] * (d[j] - d[j - 1])
    return tuple(w)


def height_range(w):
    """column x -> (min row, max row) of the path at that column"""
    hr = {}
    for (x, row) in walk(w):
        lo, hi = hr.get(x, (row, row))
        hr[x] = (min(lo, row), max(hi, row))
    return hr


def ok_between(w, U, L):
    """geometric: every vertex (x,y) of w has  min-height of L at x <= y <= max-height of U at x"""
    hu, hl = height_range(U), height_range(L)
    return all(hl[x][0] <= y <= hu[x][1] for (x, y) in walk(w))


def index_of(w, N):
    return (1,) + tuple(north_cols(w)) + (N,)


def det_count(n, d):
    """closed count: #{t_1<=...<=t_m : a_j<=t_j<=b_j}, m = r-1, a_j = d_{j+1}+1, b_j = d_j+n, as
    det[ C(b_i - a_j + 1, j - i + 1) ] = det[ C(n + d_i - d_{j+1}, j - i + 1) ]_{i,j=1..r-1}, with
    C(x, k) = 0 for k < 0.  (A first attempt, transforming to strictly increasing s_j = t_j + j and
    using the same determinant, was wrong: 4 against 3 at n = 2, d = 0^3.  This form was then found
    by testing; attribution to Kreweras/Steck/Gessel-Viennot NOT checked against a source.)"""
    m = len(d) - 1
    if m == 0:
        return 1

    def bn(x, k):
        if k < 0 or x < 0:
            return 0
        return binomial(x, k)
    # d[i] is d_{i+1}; row i (0-based) <-> b_{i+1} = d[i] + n, column j <-> a_{j+1} = d[j+1] + 1
    M = matrix(ZZ, m, m, lambda i, j: bn(n + d[i] - d[j + 1], j - i + 1))
    return M.det()


def part_A():
    say("=" * 100)
    say("(A) staircase indices <-> band lattice paths; n <= 7, r <= 4, all gaps in [0, n-1]")
    say("=" * 100)
    total_cases = 0
    for n in range(2, 8):
        for r in range(1, 5):
            ncases, maxcount = 0, 0
            for d in shift_vectors(n, r):
                N = n + d[-1]
                S = staircase_indices(n, d)
                Sset = set(S)
                assert len(S) == len(Sset)
                U, L = word_U(n, d), word_L(n, d)
                assert U.count("E") == N - 1 and L.count("E") == N - 1
                assert U.count("N") == r - 1 and L.count("N") == r - 1
                tU, tL = index_of(U, N), index_of(L, N)
                assert tU == (1,) + tuple(dj + 1 for dj in d[1:]) + (N,), (n, d, tU)
                assert tL == (1,) + tuple(dj + n for dj in d[:-1]) + (N,), (n, d, tL)
                assert tU in Sset and tL in Sset, (n, d)
                A1, A2, A3 = [], [], []
                for w in all_words(n, d):
                    a1, a2, a3 = ok_dots(w, n, d), ok_assignment(w, n, d), ok_between(w, U, L)
                    if a1:
                        A1.append(index_of(w, N))
                    if a2:
                        A2.append(index_of(w, N))
                    if a3:
                        A3.append(index_of(w, N))
                for name, A in (("dots", A1), ("assignment", A2), ("between U and L", A3)):
                    assert len(A) == len(set(A)), (n, d, name, "not injective")
                    assert set(A) == Sset, (n, d, name, sorted(set(A) ^ Sset))
                # every staircase index is componentwise between U and L
                assert all(tU[j] <= t[j] <= tL[j] for t in S for j in range(r + 1))
                cnt = len(S)
                if all(x == 0 for x in d):
                    assert cnt == comb(n + r - 2, r - 1), (n, d, cnt)
                if r == 2:
                    assert cnt == n - d[1], (n, d, cnt)
                assert det_count(n, d) == cnt, (n, d, cnt, det_count(n, d))
                ncases += 1
                maxcount = max(maxcount, cnt)
            total_cases += ncases
            say(f"  n={n} r={r}: {ncases:4d} shift vectors, bijection (A1)=(A2)=(A3)=staircase "
                f"indices OK; counts OK (max {maxcount})")
    # the determinant also for r = 5 (counts only; paths not enumerated)
    k5 = 0
    for n in range(2, 6):
        for d in shift_vectors(n, 5):
            assert det_count(n, d) == len(staircase_indices(n, d)), (n, d)
            k5 += 1
    say(f"  determinant count also checked at r = 5, n <= 5: {k5} shift vectors OK")
    say(f"  total {total_cases} (n, d) cases.  Path: N-1 east and r-1 north steps; t_j = column "
        f"of j-th north step.")
    # a few counts for the record
    say("  sample counts (n; d) -> #cells:")
    for n, d in [(3, (0,)), (3, (0, 0)), (3, (0, 1)), (3, (0, 2)), (3, (0, 0, 0)), (3, (0, 0, 1)),
                 (3, (0, 1, 1)), (3, (0, 1, 2)), (3, (0, 2, 4)), (4, (0, 1)), (4, (0, 0, 0)),
                 (4, (0, 1, 2)), (4, (0, 1, 2, 3)), (5, (0, 0, 0, 0)), (5, (0, 1, 2, 3))]:
        say(f"    Koz({n};{','.join(map(str, d))}): {len(staircase_indices(n, d))}"
            f"   [C(n+r-2,r-1) = {comb(n + len(d) - 2, len(d) - 1)}]")


# ----------------------------------------------------------------------------------------------
# polytopes
# ----------------------------------------------------------------------------------------------

def Ft(c, j):
    n = len(c) - 1
    return [QQ(c[k]) if k <= j else QQ(0) for k in range(n + 1)]


def shifted(v, s, N):
    w = [QQ(0)] * s + list(v)
    return w + [QQ(0)] * (N + 1 - len(w))


def face(c, a, b, s, N):
    return Polyhedron(vertices=[shifted(Ft(c, j), s, N) for j in range(a, b + 1)], base_ring=QQ)


def msum(polys):
    P = polys[0]
    for Q in polys[1:]:
        P = P + Q
    return P


def cell(c, d, t):
    n = len(c) - 1
    N = n + d[-1]
    return msum([face(c, t[i - 1] - d[i - 1], t[i] - d[i - 1], d[i - 1], N)
                 for i in range(1, len(d) + 1)])


def RA(c, d):
    n = len(c) - 1
    N = n + d[-1]
    return msum([face(c, 1, n, di, N) for di in d])


def NV(P, N):
    """normalised volume: coordinates x_0, x_1 are constant; project to x_2..x_N (D = N-1)"""
    Q = Polyhedron(vertices=[list(v)[2:] for v in P.vertices_list()], base_ring=QQ)
    assert Q.dim() == N - 1, (Q.dim(), N - 1)
    return factorial(N - 1) * Q.volume()


def nv_formula(c, d, t):
    n = len(c) - 1
    N = n + d[-1]
    D = N - 1
    mult = factorial(D)
    prod_ = 1
    for i in range(1, len(d) + 1):
        mult //= factorial(t[i] - t[i - 1])
        for k in range(t[i - 1] + 1, t[i] + 1):
            prod_ *= c[k - d[i - 1]]
    return mult * prod_


def kozvec(n):
    return [binomial(n, k) for k in range(n + 1)]


def check_tiling(c, d, label, pairwise=True):
    n = len(c) - 1
    N = n + d[-1]
    D = N - 1
    S = staircase_indices(n, d)
    cells = [cell(c, d, t) for t in S]
    P = RA(c, d)
    nvP = NV(P, N)
    nvs = [NV(C, N) for C in cells]
    form = [nv_formula(c, d, t) for t in S]
    assert nvs == form, (label, nvs, form)
    inside = all(P.contains(v) for C in cells for v in C.vertices_list())
    disjoint = True
    if pairwise:
        for i in range(len(cells)):
            for j in range(i + 1, len(cells)):
                if (cells[i] & cells[j]).dim() >= D:
                    disjoint = False
    return len(S), sum(nvs), nvP, inside, disjoint


# ----------------------------------------------------------------------------------------------
# (B) d = 0^r: staircase triangulation and the Cayley trick
# ----------------------------------------------------------------------------------------------

def grid_staircases(m, n):
    """CPS15 Ex. 2.2: monotone paths of squares (i, j) in the m x n grid from (1,1) to (m,n)"""
    out = []

    def rec(path):
        i, j = path[-1]
        if (i, j) == (m, n):
            out.append(tuple(path))
            return
        if i < m:
            rec(path + [(i + 1, j)])
        if j < n:
            rec(path + [(i, j + 1)])
    rec([(1, 1)])
    return out


def e(k, dim):
    v = [QQ(0)] * dim
    v[k - 1] = QQ(1)
    return v


def part_B():
    say("=" * 100)
    say("(B) d = 0^r: staircase triangulation of Delta^{r-1} x Delta^{n-1} (CPS15 Ex. 2.2), Cayley")
    say("    trick (Santos05 Thm 1.4 / CPS15 Sec. 2), and the paper's cells C_t")
    say("=" * 100)
    for n in range(2, 6):
        for r in range(1, 5):
            t0 = time.time()
            m = r
            paths = grid_staircases(m, n)
            assert len(paths) == comb(n + r - 2, r - 1)
            Dprod = m + n - 2
            # (B1) it is a triangulation of the product (projected: drop the last coordinate of each
            # block, a lattice isomorphism on the affine hull)
            def proj(i, j):
                return e(i, m)[:m - 1] + e(j, n)[:n - 1]
            simp = [Polyhedron(vertices=[proj(i, j) for (i, j) in p], base_ring=QQ) for p in paths]
            prod_poly = Polyhedron(vertices=[proj(i, j) for i in range(1, m + 1)
                                             for j in range(1, n + 1)], base_ring=QQ)
            if Dprod > 0:
                assert all(s.dim() == Dprod for s in simp)
                assert all(factorial(Dprod) * s.volume() == 1 for s in simp), "not unimodular"
                assert factorial(Dprod) * prod_poly.volume() == len(paths)
                for a in range(len(simp)):
                    for b in range(a + 1, len(simp)):
                        assert (simp[a] & simp[b]).dim() < Dprod
            # (B2) Cayley trick on these simplices: slice lambda = (1/r,...,1/r) of the simplex is
            # (1/r) * sum_i conv{e_j : (i,j) in path}
            for p in paths:
                full = Polyhedron(vertices=[e(i, m) + e(j, n) for (i, j) in p], base_ring=QQ)
                sl = full & Polyhedron(eqns=[[-QQ(1) / m] + e(i, m) + [QQ(0)] * n
                                             for i in range(1, m + 1)], base_ring=QQ)
                sl_proj = Polyhedron(vertices=[list(v)[m:] for v in sl.vertices_list()], base_ring=QQ)
                mixed = msum([Polyhedron(vertices=[e(j, n) for (ii, j) in p if ii == i], base_ring=QQ)
                              for i in range(1, m + 1)])
                assert sl_proj == mixed.dilation(QQ(1) / m), (n, r, p)
            # (B3) map e_j -> F_j(c) and compare with the paper's cells at d = 0^r
            d = (0,) * r
            for cname, c in (("Kozlov", kozvec(n)), ("ones", [1] * (n + 1))):
                images = set()
                for p in paths:
                    Pm = msum([Polyhedron(vertices=[Ft(c, j) for (ii, j) in p if ii == i], base_ring=QQ)
                               for i in range(1, m + 1)])
                    images.add(frozenset(tuple(v) for v in Pm.vertices_list()))
                ours = set(frozenset(tuple(v) for v in cell(c, d, t).vertices_list())
                           for t in staircase_indices(n, d))
                assert images == ours, (n, r, cname)
                # the staircase index of a grid path: t_i = largest j in column i
                for p in paths:
                    t = (1,) + tuple(max(j for (ii, j) in p if ii == i) for i in range(1, m)) + (n,)
                    Pm = msum([Polyhedron(vertices=[Ft(c, j) for (ii, j) in p if ii == i], base_ring=QQ)
                               for i in range(1, m + 1)])
                    assert Pm == cell(c, d, t)
            # (B4) tiling at 0^r, any c
            res = []
            cs = [("Kozlov", kozvec(n)), ("ones", [1] * (n + 1))]
            if n == 4:
                cs.append(("non-log-concave (1,4,3,1,3)", [1, 4, 3, 1, 3]))
            if n == 5:
                cs.append(("non-log-concave (1,2,1,3,1,3)", [1, 2, 1, 3, 1, 3]))
            for cname, c in cs:
                k, s, nvP, inside, disj = check_tiling(c, (0,) * r, cname)
                assert k == comb(n + r - 2, r - 1)
                prodc = 1
                for kk in range(2, n + 1):
                    prodc *= c[kk]
                assert nvP == r ** (n - 1) * prodc
                assert s == nvP and inside and disj, (n, r, cname, s, nvP, inside, disj)
                res.append(f"{cname}: {k} cells, sum NV {s} = NV(r*angle) {nvP}")
            say(f"  n={n} r={r}: {len(paths)} staircases = C({n + r - 2},{r - 1}); triangulation OK; "
                f"Cayley slice OK; images = C_t OK; tiling: " + "; ".join(res)
                + f"  [{time.time() - t0:.1f}s]")
    # contrast: the paper's counterexample at d = (0,1)
    c = [1, 2, 1, 3, 1, 3]
    S = staircase_indices(5, (0, 1))
    f = sum(nv_formula(c, (0, 1), t) for t in S)
    say(f"  contrast, c=(1,2,1,3,1,3), d=(0,1): formula {f}, true NV {NV(RA(c, (0, 1)), 6)} "
        f"(paper: 540 against 1500)")
    k, s, nvP, inside, disj = check_tiling(c, (0, 0), "nlc d=00")
    say(f"  same c at d=(0,0): {k} cells, sum {s}, NV(2*angle) {nvP}, disjoint {disj}")


# ----------------------------------------------------------------------------------------------
# (C) worked examples
# ----------------------------------------------------------------------------------------------

def blocks(t):
    return [list(range(t[i - 1] + 1, t[i] + 1)) for i in range(1, len(t))]


def part_C():
    say("=" * 100)
    say("(C) worked examples (Kozlov c)")
    say("=" * 100)
    for n, d in [(3, (0, 0, 0)), (3, (0, 1)), (3, (0, 1, 2)), (4, (0, 1)), (3, (0, 0)), (3, (0, 0, 1))]:
        c = kozvec(n)
        N = n + d[-1]
        S = staircase_indices(n, d)
        say(f"  Koz({n};{','.join(map(str, d))}): N={N}, D={N - 1}, {len(S)} cells; band rows "
            + ", ".join(f"[{di + 1},{di + n}]" for di in d))
        tot = 0
        for t in S:
            C = cell(c, d, t)
            nv = NV(C, N)
            assert nv == nv_formula(c, d, t)
            tot += nv
            al = [t[i - 1] - d[i - 1] for i in range(1, len(d) + 1)]
            be = [t[i] - d[i - 1] for i in range(1, len(d) + 1)]
            mult = factorial(N - 1)
            for i in range(1, len(d) + 1):
                mult //= factorial(t[i] - t[i - 1])
            legs = [[c[k - d[i - 1]] for k in range(t[i - 1] + 1, t[i] + 1)] for i in range(1, len(d) + 1)]
            say(f"    t={t}: own vertex ranges {list(zip(al, be))}, blocks "
                + "|".join("{" + ",".join(map(str, b)) + "}" if b else "{}" for b in blocks(t))
                + f", multinomial {mult}, legs {legs}, NV {nv}")
        nvP = NV(RA(c, d), N)
        say(f"    sum {tot}; NV(Koz) by Sage {nvP}; {'OK' if tot == nvP else 'MISMATCH'}")
        assert tot == nvP
    # coordinates for the figure: cells of 3 Koz(3) in (x_2, x_3)
    say("  cells of 3Koz(3) = Koz(3;0,0,0) in (x_2, x_3), vertices in cyclic order:")
    c = kozvec(3)
    for t in staircase_indices(3, (0, 0, 0)):
        C = cell(c, (0, 0, 0), t)
        Q = Polyhedron(vertices=[list(v)[2:] for v in C.vertices_list()], base_ring=QQ)
        # cyclic order around the centroid
        import math
        cx = sum(v[0] for v in Q.vertices_list()) / len(Q.vertices_list())
        cy = sum(v[1] for v in Q.vertices_list()) / len(Q.vertices_list())
        vs = sorted(Q.vertices_list(), key=lambda v: math.atan2(float(v[1] - cy), float(v[0] - cx)))
        say(f"    t={t}: " + " -- ".join(f"({v[0]},{v[1]})" for v in vs)
            + f"   area {Q.volume()}, NV {2 * Q.volume()}")


# no __main__ guard: `sage file.py` runs the file with __name__ == "sage.all"
T = time.time()
part_A()
part_C()
part_B()
say(f"done in {time.time() - T:.0f}s")
