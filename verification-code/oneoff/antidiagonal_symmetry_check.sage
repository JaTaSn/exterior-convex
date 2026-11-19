# antidiagonal_symmetry_check.sage -- 2026-11-18, jts-mini (Claude-Code).
#
# Part IV, Remark rem-antidiagonal.  Everything is read off the polytopes (exact rational convex
# hulls of all sums of summand vertices), not from the closed form of Corollary cor-rank2-lc.
#   Part 1 (rank two): the extremal matrix of (1,3,6,12,12) at d = 1 is the antidiagonal reflection
#     of that of (1,2,4,4,4) (Example ex-plateau); three more leg vectors, d = 1, 2.
#   Part 2 (ranks 3 and 4, n <= 5, gaps <= n, d_r <= 6, ties included): the reflection
#     (j_1..j_r) -> (n+1-j_r..n+1-j_1) carries the extremal tensor of d to that of the shift vector
#     with the gaps reversed; and whether the vertex counts of the two agree.
# Run from code/:  sage oneoff/antidiagonal_symmetry_check.sage > ../runs/2026-11-18_antidiagonal-symmetry/antidiagonal_symmetry_check.txt
# (about a quarter of an hour).
print("== Part 1: rank two")
import itertools
def vert(a,d,j,N):
    v=[0]*N
    for i in range(1,j+1): v[d+i-1]=a[i-1]
    return vector(QQ,v)
def M(a,d):
    n=len(a);N=n+d;sums={}
    for i,j in itertools.product(range(1,n+1),repeat=2):
        sums.setdefault(tuple(vert(a,0,i,N)+vert(a,d,j,N)),[]).append((i,j))
    V=set(tuple(v) for v in Polyhedron(vertices=list(sums)).vertices_list())
    good={l[0] for p,l in sums.items() if p in V and len(l)==1}
    return matrix(ZZ,n,n,lambda i,j:1 if (i+1,j+1) in good else 0)
def refl(A):
    n=A.nrows(); return matrix(ZZ,n,n,lambda i,j:A[n-1-j,n-1-i])
A=M([1,2,4,4,4],1); B=M([1,3,6,12,12],1)
print(A,"\n"); print(B,"\n"); print("B == antidiagonal reflection of A:", B==refl(A))
for a in ([1,3,6,12,12,12],[1,3,6,12,12,12,6],[1,2,4,8,8,8]):
    for d in (1,2):
        X=M(a,d); print(a,"d=",d,"antidiag-symmetric:",X==refl(X))
print("== Part 2: ranks 3 and 4")
def vert(a,d,j,N):
    v=[0]*N
    for i in range(1,j+1): v[d+i-1]=a[i-1]
    return vector(QQ,v)
def good(a,d):
    n=len(a);r=len(d);N=n+max(d);sums={}
    for js in itertools.product(range(1,n+1),repeat=r):
        sums.setdefault(tuple(sum(vert(a,d[p],js[p],N) for p in range(r))),[]).append(js)
    V=set(tuple(v) for v in Polyhedron(vertices=list(sums)).vertices_list())
    return {l[0] for p,l in sums.items() if p in V and len(l)==1}
def rev(d): return tuple(d[-1]-x for x in reversed(d))
def reflT(G,n): return {tuple(n+1-j for j in reversed(js)) for js in G}
fams={"kozlov":lambda n:[binomial(n,k) for k in range(1,n+1)],"ones":lambda n:[1]*n,
      "geometric":lambda n:[2^k for k in range(n)],"plateau":lambda n:[1,2,4,4,4][:n]}
for name,f in fams.items():
    tot=0;ok=0;okc=0;bad=[]
    for n in range(2,6):
        a=f(n)
        for r in (3,4):
            if n^r>700: continue
            for gaps in itertools.product(range(0,n+1),repeat=r-1):
                d=tuple([0]+list(itertools.accumulate(gaps)))
                if d[-1]>6: continue
                G=good(a,d);H=good(a,rev(d));tot+=1
                if reflT(G,n)==H: ok+=1
                elif len(bad)<3: bad.append((n,d))
                if len(G)==len(H): okc+=1
    print(name,": configs",tot," tensor(d) reflected == tensor(reversed gaps):",ok," counts equal:",okc," first failures:",bad)
