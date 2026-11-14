# review_volume_ehrhart_barvinok.sage
# Changelog (reverse chronological):
#   2026-10-20  Claude (referee): created. Emits an iscc (barvinok) script computing the Ehrhart
#               polynomial of Koz(n;0,d) from its Sage H-representation (projected to the
#               non-constant coordinates). Usage: sage review_volume_ehrhart_barvinok.sage n d > k.iscc; iscc < k.iscc
import sys
from math import comb
from itertools import product
n=int(sys.argv[1]); d=int(sys.argv[2])
c=[comb(n,k) for k in range(n+1)]; N=n+d
V=[tuple(c[k] if k<=j else 0 for k in range(n+1)) for j in range(1,n+1)]
def sh(v,s): w=[0]*(N+1); 
def shf(v,s):
    w=[0]*(N+1)
    for k,a in enumerate(v): w[k+s]=a
    return w
gens=[ [a+b for a,b in zip(shf(u,0),shf(v,d))] for u in V for v in V]
U=[k for k in range(N+1) if len({g[k] for g in gens})>1]
P=Polyhedron(vertices=[[g[k] for k in U] for g in gens])
D=len(U)
def lin(a,b):
    terms=[f"{ai}*x{i}" for i,ai in enumerate(a) if ai!=0]+([f"{b}*t"] if b!=0 else [])
    return " + ".join(terms).replace("+ -","- ") or "0"
cons=[]
for ineq in P.inequalities_list():
    b=ineq[0]; a=ineq[1:]   # b + a.x >= 0  -> scaled: b*t + a.x >= 0
    cons.append(lin(a,b)+" >= 0")
for eq in P.equations_list():
    cons.append(lin(eq[1:],eq[0])+" = 0")
xs=",".join(f"x{i}" for i in range(D))
print(f"P := [t] -> {{ [{xs}] : t >= 0 and " + " and ".join(cons) + " };")
print("card P;")
