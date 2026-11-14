# Changelog (newest first)
# 2026-10-21  Copied from a Lean agent's scratch check into code/oneoff by the coordinator: the concatenated run-wise Theta system equals RA(a;d) (469 cases), sanity check for Facets/EveryD.lean.

# Sanity check for Facets/EveryD.lean: RA(a; d) == concatenated run system (global coords).
import itertools
from sage.all import *
def rav(a,N,e,k):
    return [a[c-e] if (e < c <= e+k) else 0 for c in range(1,N+1)]
def RA(a,n,N,d):
    P = None
    for dp in d:
        S = Polyhedron(vertices=[rav(a,N,dp,k) for k in range(1,n+1)], base_ring=QQ)
        P = S if P is None else P + S
    return P
def Aw(a,n,e,c): return a[c-e] if (e < c <= e+n) else 0
def roof(a,n,e,lam,r,p,c): return sum(lam[q]*Aw(a,n,e[q],c) for q in range(r) if q>p)
def rows(a,n,N,e,lam):
    # QRows: (E),(I;0),(I;p),(C),(D),(F) in global coords co(x,c)=x[c-1]
    r=len(e); ie=[]; eq=[]
    def v(c): 
        z=[0]*(N+1)
        if 1<=c<=N: z[c]=1
        return vector(QQ,z)
    def const(t): z=[0]*(N+1); z[0]=t; return vector(QQ,z)
    eq.append(v(e[0]+1)-const(lam[0]*a[1]))
    for p in range(r):
        for j in range(1 if p==0 else 2, n):
            c=e[p]+j
            # (x(c+1)-M(c+1))a_j <= (x(c)-M(c)) a_{j+1}
            ie.append((v(c)-const(roof(a,n,e,lam,r,p,c)))*a[j+1] - (v(c+1)-const(roof(a,n,e,lam,r,p,c+1)))*a[j])
    for p in range(r-1):
        ie.append(v(e[p+1]+1)-const(lam[p+1]*a[1]))
        c=e[p]+n+1
        ie.append(const(roof(a,n,e,lam,r,p,c))-v(c))
    ie.append(v(e[r-1]+n))
    return ie,eq
def system(a,n,N,d):
    vals=sorted(set(d)); lam=[d.count(v) for v in vals]
    runs=[[0]]
    for i in range(1,len(vals)):
        if vals[i] < vals[i-1]+n: runs[-1].append(i)
        else: runs.append([i])
    IE=[];EQ=[]
    for R in runs:
        ie,eq=rows(a,n,N,[vals[i] for i in R],[lam[i] for i in R]); IE+=ie; EQ+=eq
    for c in range(1,N+1):
        if not any(dp < c <= dp+n for dp in d):
            z=[0]*(N+1); z[c]=1; EQ.append(vector(QQ,z))
    return Polyhedron(ieqs=IE, eqns=EQ, base_ring=QQ), len(runs)
tested=0; bad=0
legs = {}
for n in [2,3,4]:
    legs[n] = [[0]+[binomial(n,s) for s in range(1,n+1)], [0]+[1]*n]
legs[3].append([0,3,3,1]); legs[3].append([0,2,3,2]); legs[4].append([0,5,7,6,2])
for n in [2,3,4]:
  for a in legs[n]:
    for r in [1,2,3]:
      for tail in itertools.product(range(0,n+3), repeat=r-1):
        d=[0]; 
        for g in tail: d.append(d[-1]+g)
        N=d[-1]+n+ (1 if tail and tail[-1]==1 else 0)  # also try slack ambient sometimes
        for NN in sorted(set([d[-1]+n, N])):
          P=RA(a,n,NN,d); Q,k=system(a,n,NN,d); tested+=1
          if P!=Q: bad+=1; print("MISMATCH",n,a,d,NN)
print("tested",tested,"bad",bad)
