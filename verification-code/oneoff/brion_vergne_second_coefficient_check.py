# 2026-11-11 - Claude-Code (jts-mini): check of the Euler-Maclaurin sentence in "Lattice points of dilates"
#   (Part III), after Jan read Brion-Vergne 1997 and could not find its exact formulation there.
#   Claim: for a lattice polytope P of dimension D and a homogeneous polynomial h of degree k,
#     sum_{x in tP ∩ Z^d} h(x) = t^(D+k) ∫_P h + t^(D+k-1) (1/2) sum_F ∫_F h dσ_F + O(t^(D+k-2)),
#   σ_F the lattice-normalised measure on the facet F. Checked
#   (a) on non-unimodular lattice simplices in dimensions 2 and 3, and a non-simple square pyramid,
#       against exact lattice-point sums interpolated in t;
#   (b) on K = the projection of Koz(n) to (x_2..x_n), n = 3, 4, 5: the first-order centroid
#       corrections it predicts against those of prop-dilates (runs/2026-11-09_lattice-centroid-dilates-exact.txt).
#   (c) the non-homogeneous counterexample: leading coefficient is not ∫_P h for h = 1 + x on [0,1].
#   Run: timeout 600 sage code/oneoff/brion_vergne_second_coefficient_check.py
import itertools
from functools import reduce
from math import gcd
import sympy as sp

def in_simplex(V, x):
    d = len(x)
    M = sp.Matrix.hstack(*[sp.Matrix(V[i]) - sp.Matrix(V[0]) for i in range(1, d + 1)])
    lam = M.LUsolve(sp.Matrix(x) - sp.Matrix(V[0]))
    return all(l >= 0 for l in lam) and sum(lam) <= 1

def lattice_points(simplices, t):
    """lattice points of t * (union of the full-dimensional simplices)"""
    d = len(simplices[0][0]); out = set()
    for V in simplices:
        Vt = [tuple(t * c for c in v) for v in V]
        if t == 0:
            out.add(tuple([0] * d)); continue
        box = [range(min(v[i] for v in Vt), max(v[i] for v in Vt) + 1) for i in range(d)]
        out |= {x for x in itertools.product(*box) if in_simplex(Vt, x)}
    return out

def gcd_minors(E):
    """covolume of the lattice spanned by the rows of E inside its saturation"""
    E = sp.Matrix(E)
    return reduce(gcd, [int(abs(E[:, list(c)].det())) for c in itertools.combinations(range(E.cols), E.rows)])

def simplex_integral(V, h, xs):
    """∫ of h over conv(V), lattice-normalised on its affine span"""
    m = len(V) - 1; s = sp.symbols('s0:%d' % m)
    E = [[V[j + 1][i] - V[0][i] for i in range(len(xs))] for j in range(m)]
    pt = [V[0][i] + sum(s[j] * E[j][i] for j in range(m)) for i in range(len(xs))]
    f = h.subs(dict(zip(xs, pt)), simultaneous=True)
    for j in reversed(range(m)):
        f = sp.integrate(f, (s[j], 0, 1 - sum(s[:j])))
    return sp.nsimplify(f * gcd_minors(E))

t = sp.symbols('t')

def check(name, simplices, facets, h, xs):
    D = len(xs); k = sp.Poly(h, *xs).total_degree()
    top = sum(simplex_integral(V, h, xs) for V in simplices)
    nxt = sp.Rational(1, 2) * sum(simplex_integral(F, h, xs) for F in facets)
    ts = list(range(0, D + k + 3))          # one more point than the degree needs, as a check
    vals = [sum(h.subs(dict(zip(xs, p))) for p in lattice_points(simplices, tt)) for tt in ts]
    poly = sp.expand(sp.interpolate(list(zip(ts[:-1], vals[:-1])), t))
    assert poly.subs(t, ts[-1]) == vals[-1], "not a polynomial of degree <= D+k"
    c = sp.Poly(poly, t).all_coeffs()
    ok = (c[0] == top and c[1] == nxt)
    print("%-34s h = %-12s sum = %s" % (name, h, poly))
    print("%-34s t^%d: %s vs ∫_P h = %s;  t^%d: %s vs ½Σ∫_F h = %s   %s"
          % ("", D + k, c[0], top, D + k - 1, c[1], nxt, "OK" if ok else "MISMATCH"))
    return ok

x, y, z = sp.symbols('x y z')
allok = True
print("(a) lattice polytopes, homogeneous weights")
T2 = [(0, 0), (4, 0), (0, 2)]                     # hypotenuse of lattice length 2
for h in [x, x * y, x**2 - 3 * y**2]:
    allok &= check("triangle (0,0),(4,0),(0,2)", [T2], list(itertools.combinations(T2, 2)), h, (x, y))
T3 = [(0, 0, 0), (2, 0, 0), (0, 3, 0), (1, 1, 4)]  # no facet unimodular to the lattice in its span
for h in [z, x * y + z**2]:
    allok &= check("simplex (0,0,0),(2,0,0),(0,3,0),(1,1,4)", [T3], list(itertools.combinations(T3, 3)), h, (x, y, z))
S1 = [(0, 0, 0), (2, 0, 0), (2, 2, 0), (1, 1, 3)]; S2 = [(0, 0, 0), (0, 2, 0), (2, 2, 0), (1, 1, 3)]
pyr_facets = [S1[:3], S2[:3],                      # the base square, in two halves
              [(0, 0, 0), (2, 0, 0), (1, 1, 3)], [(2, 0, 0), (2, 2, 0), (1, 1, 3)],
              [(2, 2, 0), (0, 2, 0), (1, 1, 3)], [(0, 2, 0), (0, 0, 0), (1, 1, 3)]]
for h in [z, x * z + y**2]:
    allok &= check("square pyramid (apex not simple)", [S1, S2], pyr_facets, h, (x, y, z))

print("\n(b) Koz(n): predicted first-order centroid corrections vs prop-dilates")
# K = {1 >= x_2/C(n,2) >= ... >= x_n/C(n,n) >= 0}, vertices v_j (j = 1..n): x_k = C(n,k) for k <= j, else 0.
# Lattice points of tKoz(n) <-> those of tK (x_0 = t, x_1 = nt), so the measures agree.
expected = {3: {2: sp.Rational(-1, 9), 3: sp.Rational(-2, 9)},
            4: {2: sp.Rational(-5, 48), 3: sp.Rational(-1, 4), 4: sp.Rational(-5, 16)},
            5: {2: sp.Rational(-1, 10), 3: sp.Rational(-1, 5), 4: sp.Rational(-3, 10), 5: sp.Rational(-7, 20)}}
for n in (3, 4, 5):
    X = sp.symbols('x2:%d' % (n + 1))
    V = [tuple(sp.binomial(n, k) if k <= j else 0 for k in range(2, n + 1)) for j in range(1, n + 1)]
    F = list(itertools.combinations(V, n - 1))
    vol = simplex_integral(V, sp.Integer(1), X); W = sp.Rational(1, 2) * sum(simplex_integral(f, sp.Integer(1), X) for f in F)
    for i, k in enumerate(range(2, n + 1)):
        I = simplex_integral(V, X[i], X); B = sp.Rational(1, 2) * sum(simplex_integral(f, X[i], X) for f in F)
        # mean of x_k over tK ∩ Z^(n-1) = (I t^n + B t^(n-1) + ...)/(vol t^(n-1) + W t^(n-2) + ...)
        pred = (B / vol - I * W / vol**2) / sp.binomial(n, k)    # coefficient of 1/t in nu_k
        ok = pred == expected[n][k]; allok &= ok
        print("  n=%d k=%d: predicted %s, prop-dilates %s   %s" % (n, k, pred, expected[n][k], "OK" if ok else "MISMATCH"))

print("\n(c) non-homogeneous weight h = 1 + x on [0,1]:")
m = sp.symbols('m')
print("  sum_{x=0..t} (1+x) =", sp.expand(sp.summation(1 + m, (m, 0, t))), "; ∫_0^1 (1+x) dx = 3/2: leading coefficient is ∫ of the top-degree part only")
print("\nALL OK" if allok else "\nSOME MISMATCH")
