# gap_one_path_graph.sage -- 2026-11-18, jts-mini (Claude-Code).  At Jan's request: is
# eq:rho-gap-one (Part IV, Proposition prop-gap-one) a known result of spectral graph theory?
#
#  (1) M = M(kozvec(12); 1), read off the polytope.  It is antidiagonal-symmetric, J M^T J = M.
#  (2) Can it be made symmetric by a similarity?  By a permutation: no (P M P^T is symmetric iff M is).
#      By any similarity: only if M is diagonalisable, and for n >= 6 it is not (Jordan blocks at -1).
#      M J (columns reversed) IS symmetric, but that is not a similarity and its spectrum differs.
#  (3) What is true: with P = path on n+3 vertices and A its adjacency matrix, let B = A^2 - I
#      restricted to the vertices 0, 2, 4, ...  (a path on h = ceil((n+3)/2) vertices with a loop at
#      every vertex except the first, and except the last when n is even).  Then
#            charpoly(M) * (x+1)^max(0,h-n) = (x+1)^max(0,n-h) * charpoly(B),      2 <= n <= 40,
#      so the spectral radius of M is  lambda_max(P_{n+3})^2 - 1 = 4 cos^2(pi/(n+4)) - 1.
#  Plots: the looped path B and the graph of M J, for n = 12.
# Run from code/:  sage oneoff/gap_one_path_graph.sage
import itertools, os
OUT="../runs/2026-11-18_gap-one-review"; os.makedirs(OUT,exist_ok=True)
LOG=open(OUT+"/gap_one_path_graph.txt","w")
def say(*a):
    s=" ".join(str(x) for x in a); print(s); LOG.write(s+"\n"); LOG.flush()
def vert(a,d,j,N):
    v=[0]*N
    for i in range(1,j+1): v[d+i-1]=a[i-1]
    return vector(QQ,v)
def Mbrute(a,d):
    n=len(a);N=n+d;sums={}
    for i,j in itertools.product(range(1,n+1),repeat=2):
        sums.setdefault(tuple(vert(a,0,i,N)+vert(a,d,j,N)),[]).append((i,j))
    V=set(tuple(v) for v in Polyhedron(vertices=list(sums)).vertices_list())
    good={l[0] for p,l in sums.items() if p in V and len(l)==1}
    return matrix(ZZ,n,n,lambda i,j:1 if (i+1,j+1) in good else 0)
def Mform(n): return matrix(ZZ,n,n,lambda i,j: 1 if (j>=i-1 and not (j==i and 1<=i<=n-2)) else 0)
def halfpath(n):
    A=graphs.PathGraph(n+3).adjacency_matrix(); B=A*A-identity_matrix(n+3)
    ev=[v for v in range(n+3) if v%2==0]
    return B.matrix_from_rows_and_columns(ev,ev)
n=12
M=Mbrute([binomial(n,k) for k in range(1,n+1)],1)
assert M==Mform(n)
J=matrix(ZZ,n,n,lambda i,j:1 if i+j==n-1 else 0)
say("(1) M(kozvec(12);1) from the polytope:"); say(M)
say("    J M^T J == M:",J*M.transpose()*J==M,"  M symmetric:",M.is_symmetric(),"  M J symmetric:",(M*J).is_symmetric())
say("(2) diagonalisable over QQbar, n = 2..10:",[(k,Mform(k).change_ring(QQ).is_diagonalizable(QQbar)) for k in range(2,11)])
say("    eigenvalue -1 of M(12): algebraic multiplicity %d, geometric %d"%(M.change_ring(QQ).charpoly().valuation(polygen(QQ)+1),(M+1).right_nullity()))
rho=max(abs(z) for z in M.charpoly().roots(QQbar,multiplicities=False))
rhoJ=max(abs(z) for z in (M*J).charpoly().roots(QQbar,multiplicities=False))
say("    spectral radius of M: %.6f   of M J: %.6f   1+2cos(2pi/16) = %.6f"%(rho,rhoJ,1+2*cos(2*pi/16).n()))
R.<x>=QQ[]
ok=True
for k in range(2,41):
    B=halfpath(k); h=B.nrows()
    ok=ok and R(Mform(k).charpoly())*(x+1)^max(0,h-k)==(x+1)^max(0,k-h)*R(B.charpoly())
say("(3) charpoly identity with the looped half path, 2 <= n <= 40:",ok)
B=halfpath(n); say("    B for n = 12:"); say(B)
say("    charpoly(M) =",M.charpoly().factor()); say("    charpoly(B) =",B.charpoly().factor())
lamP=max(graphs.PathGraph(n+3).adjacency_matrix().charpoly().roots(QQbar,multiplicities=False))
say("    lambda_max(P_15)^2 - 1 == spectral radius of M:",lamP^2-1==rho)
G=Graph(B,format='adjacency_matrix',loops=True)
G.plot(pos={i:(i,0) for i in range(B.nrows())},vertex_size=300,loop_size=0.25,figsize=(10,2.2),title="B = (A(P_15)^2 - I) on even vertices: spectrum of M(a;1), n = 12, apart from -1").save(OUT+"/gap_one_looped_path_n12.png",dpi=130)
H=Graph(M*J,format='adjacency_matrix',loops=True); H.relabel(lambda v:v+1)
H.plot(layout='circular',vertex_size=300,loop_size=0.08,figsize=(7,7),title="graph of M J (columns reversed), n = 12: symmetric, but NOT similar to M").save(OUT+"/gap_one_MJ_graph_n12.png",dpi=110)
D=DiGraph(M,format='adjacency_matrix',loops=True); D.relabel(lambda v:v+1)
D.plot(layout='circular',vertex_size=300,loop_size=0.08,figsize=(7,7),title="digraph of M(a;1), n = 12").save(OUT+"/gap_one_M_digraph_n12.png",dpi=110)
LOG.close()
