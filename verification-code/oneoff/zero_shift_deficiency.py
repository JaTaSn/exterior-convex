#!/usr/bin/env python3
"""zero_shift_deficiency.py -- the values behind Corollary cor-deficiency of article 3.

Changelog (reverse chronological):
  2026-11-05  Claude (jts-tinycalc): created, at Jan's request, to turn the n = 4 "deficiency"
              observation (L_Koz(4)(r) - |FF(4;0^r)| = 2r(r+1), previously verified for r <= 10 by the
              transfer matrices) into a proof, and to settle n = 5.

What it computes, for n and r = 1..R:
  a(r) = |FF(n;0^r)|, the r-fold sumset of S_n, with S_n (f-vectors (1,n,x_2,...,x_n) of complexes
         on [n] using every vertex) listed by the Kruskal-Katona theorem;
  L(r) = lattice points of r*Koz(n), counted as integer LYM chains
         r >= x_2/C(n,2) >= ... >= x_n/C(n,n) >= 0 (prop-rank-one-H, dilated).
Both routes are independent of the transfer matrices T_0, T'_n(0) of the paper.  The proof in the
paper uses: both are polynomials of degree <= n-1 in r for r >= 1 with equal leading coefficients
(cor-zero-shift), so at n = 4, 5 four values of the difference, and n values of each, decide them.

Output 2026-11-05 (also checked at n = 4 by brute-force enumeration of all complexes on [4]):
  n=4: a = 16, 69, 184, 385, 696;  L = 20, 81, 208, 425, 756;  L-a = 4, 12, 24, 40, 60
  n=5: a = 70, 627, 2592, 7385, 16926;  L = 162, 1108, 3964, 10355, 22406;  L-a = 92, 481, 1372, 2970, 5480
Usage: python3 zero_shift_deficiency.py n R
"""
import sys
from math import comb
from itertools import product
from fractions import Fraction
def shadow(m,k):
    # minimal number of (k-1)-sets in the shadow of m k-sets (Kruskal-Katona)
    if m==0 or k==0: return 0
    res=0; kk=k
    while m>0 and kk>0:
        a=kk
        while comb(a+1,kk)<=m: a+=1
        m-=comb(a,kk); res+=comb(a,kk-1); kk-=1
    return res
def fvecs(n):
    out=[]
    def rec(v,k):
        if k>n: out.append(tuple(v)); return
        for x in range(comb(n,k)+1):
            if shadow(x,k)<=v[k-1]: rec(v+[x],k+1)
            else: break  # shadow is monotone in x
    rec([1,n],2); return out
n=int(sys.argv[1]); R=int(sys.argv[2])
S=fvecs(n); print("|S_n|",len(S))
s=[comb(n,k) for k in range(n+1)]
def L(r):
    cnt=0
    def rec(k,prev):  # prev = x_{k-1}/s_{k-1} as Fraction, chain r>=x2/s2>=...>=xn/sn>=0
        nonlocal cnt
        if k>n: cnt+=1; return
        for x in range(s[k]*r+1):
            if Fraction(x,s[k])<=prev: rec(k+1,Fraction(x,s[k]))
            else: break
    rec(2,Fraction(r)); return cnt
cur={tuple([0]*(n+1))}
for r in range(1,R+1):
    cur={tuple(a+b for a,b in zip(x,y)) for x in cur for y in S}
    l=L(r); print(r,len(cur),l,l-len(cur),flush=True)
