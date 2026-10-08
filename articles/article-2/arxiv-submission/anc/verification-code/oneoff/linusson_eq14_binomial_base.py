"""Reproduce Linusson's equation (14) exactly, and test whether our own p-polynomials
become positive in the binomial base he uses for it.

Linusson writes F^p(n) in the base C(p+2,j) rather than in powers of p, saying it is "to make
comparisons easier" with his equation (4) for M-sequences.  Article 2's ex-poly-p-tables prints
our |FF^(p)(n;d)| in the MONOMIAL base and remarks that the coefficients are not positive.
Two questions follow, and this script answers both:

  1. Is our E/F implementation right at the level of the POLYNOMIALS, not just the table
     entries?  rem-transcription records an entry-by-entry check against his Tables 5 and 6;
     this is a stronger check, since it also exercises the interpolation.
  2. Is the non-positivity an artefact of the monomial base?

Answers, 2026-10-04 on jts-yoga:

  1. YES.  All of equation (14) is reproduced exactly, including the signs:
         F^p(0) = 2
         F^p(1) = C(p+2,1)
         F^p(2) = C(p+2,3) - C(p+2,2) + 2 C(p+2,1) - 1
         F^p(3) = 4 C(p+2,6) + C(p+2,4) + C(p+2,1)
         F^p(4) = 120 C(p+2,10) + 188 C(p+2,9) + 95 C(p+2,8) + 18 C(p+2,7)
                      + 5 C(p+2,6) + C(p+2,4) + C(p+2,1)
     Checked against the printed page, not against OCR, which mangles it.

  2. NO.  Eight of the nine configurations of ex-poly-p-tables still have negative
     coefficients in the binomial base; the one exception, n=3 with d=(0,4), is the saturating
     gap where the summands have already come apart.

  AND THE POINT WORTH KEEPING: Linusson's OWN F^p(2) is not positive in his own base either.
  So non-positivity in p is not something our generalization introduces, and ex-poly-p-tables'
  remark should not be read as a contrast with him.

One convention the module does not carry: E^p(n,k) = 0 for n <= -2, which is what makes
A[-1][0] = 1 in def-A.  linusson_ff_counting.E raises instead, so Esafe wraps it.
"""

import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir))
from sympy import symbols, Poly, expand, nsimplify, interpolate, prod, Integer
from math import factorial
import linusson_ff_counting as L
p = symbols('p')

def Esafe(pp, nn, kk):
    # E^p(n,k) = 0 for n <= -2: no complex sits below the void family.  This is the
    # convention that makes A[-1][0] = 1 in def-A; the module guards it as out-of-domain.
    return 0 if nn < -1 else L.E(pp, nn, kk)

def A_p(n, pp):
    """A^(p)[tau][rho] = E^p(tau,rho-1) - E^p(tau-1,rho-1), tau=-1..n, rho=0..n+1"""
    idx = lambda t: t+1
    M = [[0]*(n+2) for _ in range(n+2)]
    for tau in range(-1, n+1):
        for rho in range(0, n+2):
            M[idx(tau)][rho] = Esafe(pp, tau, rho-1) - Esafe(pp, tau-1, rho-1)
    return M

def count(n, ds, pp):
    A = A_p(n, pp)
    u = [sum(row) for row in A]
    vec = u[:]
    for i in range(1, len(ds)):
        delta = ds[i]-ds[i-1]
        T = [[sum(A[tp][rho] for rho in range(0, n+2) if rho > (tau-1)-delta)
              for tp in range(n+2)] for tau in range(n+2)]
        vec = [sum(vec[a]*T[a][b] for a in range(n+2)) for b in range(n+2)]
    return sum(vec)

def binom_poly(j, shift=2):
    return expand(prod([(p+shift-i) for i in range(j)])/Integer(factorial(j)))

def to_base(poly, shift=2):
    d = Poly(poly, p).degree(); rem = expand(poly); out=[]
    for j in range(d, -1, -1):
        bj = binom_poly(j, shift)
        c = nsimplify(Poly(rem,p).coeff_monomial(p**j)/Poly(bj,p).coeff_monomial(p**j)) if j>0 else nsimplify(rem)
        out.append((j,c)); rem = expand(rem - c*bj)
    return out

print("Linusson's equation (14), recomputed from his recursion, in base C(p+2,j):")
for n in range(0, 5):
    deg = n*(n+1)//2 + 1
    pts = list(range(0, deg+3))
    poly = expand(interpolate(list(zip(pts, [L.F(pp, n) for pp in pts])), p))
    terms = [(j, c) for j, c in to_base(poly) if c != 0]   # to_base returns high -> low
    out = []
    for i, (j, c) in enumerate(terms):
        sign = "" if i == 0 else (" + " if c > 0 else " - ")
        mag = abs(c)
        body = f"C(p+2,{j})" if mag == 1 and j > 0 else (f"{mag}" if j == 0 else f"{mag} C(p+2,{j})")
        out.append(sign + ("-" if i == 0 and c < 0 else "") + body)
    print(f"  F^p({n}) = " + "".join(out))
print()

cfgs = [(2,(0,0)), (2,(0,1)), (2,(0,0,0)), (2,(0,1,2)),
        (3,(0,0)), (3,(0,1)), (3,(0,4)), (3,(0,1,3)), (3,(0,2,3))]
print(f"{'n':>2} {'d':<10} {'deg':>3}  coefficients in base C(p+2,j), high->low")
for n, ds in cfgs:
    r = len(ds)
    deg = r*(n*(n+1)//2) - sum((max(0,n-(ds[i]-ds[i-1]))*(max(0,n-(ds[i]-ds[i-1]))+1))//2 for i in range(1,r))
    pts = list(range(n, n+deg+4))
    poly = expand(interpolate(list(zip(pts,[count(n,ds,pp) for pp in pts])), p))
    cs = [c for j,c in to_base(poly)]
    allpos = all(c >= 0 for c in cs)
    print(f"{n:>2} {str(ds):<10} {Poly(poly,p).degree():>3}  {cs}   {'ALL >= 0' if allpos else 'has negatives'}")
