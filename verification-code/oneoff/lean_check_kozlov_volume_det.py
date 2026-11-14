# Changelog (newest first)
# 2026-10-21  Copied from a Lean agent's scratch check into code/oneoff by the coordinator: det of vertex differences of Koz(n) = prod C(n,k), n<=7, sanity check for Lattice/Volume.lean.

from itertools import combinations
from math import comb, prod
from fractions import Fraction
def fvec(n,j):  # f-vector of complete j-skeleton by actual enumeration, degree-0 inclusive
    f=[0]*(n+1)
    for k in range(n+1):
        if k<=j: f[k]=sum(1 for _ in combinations(range(n),k))
    return f
def det(M):
    M=[[Fraction(x) for x in r] for r in M]; m=len(M); d=Fraction(1)
    for c in range(m):
        p=next((r for r in range(c,m) if M[r][c]!=0),None)
        if p is None: return 0
        if p!=c: M[c],M[p]=M[p],M[c]; d=-d
        d*=M[c][c]
        for r in range(c+1,m):
            t=M[r][c]/M[c][c]; M[r]=[a-t*b for a,b in zip(M[r],M[c])]
    return d
for n in range(1,8):
    V=[fvec(n,j) for j in range(1,n+1)]
    assert all(v[0]==1 and v[1]==n for v in V)
    D=[[V[j][k]-V[0][k] for j in range(1,n)] for k in range(2,n+1)]
    print(n, abs(det(D)) if n>1 else 1, prod(comb(n,k) for k in range(2,n+1)))
