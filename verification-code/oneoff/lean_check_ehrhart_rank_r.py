# Changelog (newest first)
# 2026-10-21  Copied from a Lean agent's scratch check into code/oneoff by the coordinator: brute-force dilate lattice counts vs the rank-r transfer-matrix display, sanity check for Lattice/EhrhartRankR.lean.

import itertools, sympy as sp
from math import comb
def L(n):
    pts=[]
    rng=[range(comb(n,k)+1) for k in range(2,n+1)]
    for tail in itertools.product(*rng):
        x=(1,n)+tail
        ok=all(x[k]*comb(n,k-1)<=x[k-1]*comb(n,k) for k in range(1,n+1))
        if ok: pts.append(x)
    return pts
def top(x): return max(k for k in range(len(x)) if x[k]>0)
def indeg(x,n):
    for k in range(n+1):
        if x[k]<comb(n,k): return k
    return n+1
def mats(n):
    P=L(n)
    u=sp.Matrix([[sum(1 for x in P if top(x)==t) for t in range(1,n+1)]])
    def T(d): return sp.Matrix(n,n,lambda a,b: sum(1 for x in P if top(x)==b+1 and indeg(x,n)+d>a+1))
    return P,u,T
def brute(n,d,t):
    P=L(n); N=max(d)+n
    S={tuple([0]*(N+1))}
    for di in d:
        for _ in range(t):
            S={tuple(s[i]+(x[i-di] if 0<=i-di<=n else 0) for i in range(N+1)) for s in S for x in P}
    return len(S)
tt=sp.symbols('t')
for n,d in [(4,(0,1)),(3,(0,2)),(3,(0,1)),(3,(0,1,2)),(3,(0,1,3))]:
    P,u,T=mats(n); T0=T(0); one=sp.ones(n,1)
    gs=[d[i+1]-d[i] for i in range(len(d)-1)]
    def disp(t):
        M=u*T0**(t-1)
        for g in gs: M=M*T(g)*T0**(t-1)
        return (M*one)[0]
    vals=[disp(t) for t in range(1,5)]
    br=[brute(n,d,t) for t in range(1,4 if n==4 else 5)]
    # polynomial
    Nm=T0-sp.eye(n)
    Mt=sum((sp.binomial(tt-1,j)*Nm**j for j in range(n)),sp.zeros(n,n))
    Pt=u*Mt
    for g in gs: Pt=Pt*T(g)*Mt
    Pt=sp.expand((Pt*one)[0])
    w=T0.inv()*one
    print(n,d,vals,br,Pt, 'P0',Pt.subs(tt,0), [list(T(g)*w) for g in gs])
