# Changelog (newest first)
# 2026-10-21  Copied from a Lean agent's scratch check into code/oneoff by the coordinator: cor-rank2-lc vs exact Sage vertex test, 36581 entries, sanity check for Vertices/RankTwoCorollary.lean.

import itertools, random
random.seed(int(1))
vals=[QQ(3),QQ(2),QQ(3)/2,QQ(1),QQ(1)/2,QQ(1)/3]
def vert(a,n,N,d,k):
    v=[0]*N
    for c in range(1,k+1): v[d+c-1]=a[c]
    return vector(QQ,v)
def predicted_zero(a,n,g,i,j):
    if g==0: return i!=j
    if g>=n: return False
    m=n-g; t=i-g
    sig=lambda u: a[u+1]/a[u]
    if not(1<=t<=m and 1<=j<=m): return False
    if j<t or j==t+1: return True
    if j>=t+2:
        return len(set(sig(u) for u in range(t+1,j+g)))==1
    return False
bad=0; tests=0; plateau_hits=0
for n in range(2,8):
    seqs=set()
    for _ in range(40):
        s=sorted([random.choice(vals) for _ in range(n-1)],reverse=True)
        seqs.add(tuple(s))
    seqs.add(tuple([QQ(1)]*(n-1)))
    for s in seqs:
        a=[None,QQ(1)]
        for x in s: a.append(a[-1]*x)
        for g in range(0,n+2):
            N=n+g
            V=[vert(a,n,N,0,i) for i in range(1,n+1)]
            U=[vert(a,n,N,g,j) for j in range(1,n+1)]
            P=Polyhedron(vertices=[v+u for v in V for u in U],base_ring=QQ)
            Vs=set(tuple(v) for v in P.vertices_list())
            for i in range(1,n+1):
                for j in range(1,n+1):
                    tests+=1
                    isv = tuple(V[i-1]+U[j-1]) in Vs
                    pz=predicted_zero(a,n,g,i,j)
                    if g>=1 and g<n and pz and j>=i-g+2: plateau_hits+=1
                    if isv == pz:
                        bad+=1; print("MISMATCH",n,g,a[1:],i,j,isv,pz)
print("tests",tests,"bad",bad,"plateau-zero entries",plateau_hits)
# vertex count = #admissible distinct check for rank 2
