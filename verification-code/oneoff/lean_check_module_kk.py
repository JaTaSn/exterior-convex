# Changelog (newest first)
# 2026-10-21  Copied from a Lean agent's scratch check into code/oneoff by the coordinator: (F2)/(F4) lex shadows, KK, greedy split vs brute force, sanity check for ModuleKK/Greedy.lean and LexShadow.lean.

import itertools, functools
from math import comb
@functools.lru_cache(None)
def sig(n,k,t):
    if n==0: return 0
    if k==0: return 0 if t==0 else 1+sig(n-1,0,t)
    if t<=comb(n-1,k-1): return sig(n-1,k-1,t)
    return comb(n-1,k)+sig(n-1,k,t-comb(n-1,k-1))
def lexkey(S,n): # lex: min of symmdiff in S => S first. Sorted tuple ascending compare works
    return tuple(sorted(S))
def up(F,n):
    return {frozenset(S|{x}) for S in F for x in range(n) if x not in S}
def lexsets(n,k): return sorted([frozenset(c) for c in itertools.combinations(range(n),k)], key=lambda S:tuple(sorted(S)))
bad=0
for n in range(0,9):
  for k in range(0,n+2):
    L=lexsets(n,k); L1=lexsets(n,k+1)
    for t in range(len(L)+1):
      sh=up(L[:t],n)
      if len(sh)!=sig(n,k,t) or sh!=set(L1[:len(sh)]): bad+=1
print("F2/F4 bad",bad)
# KK brute
bad=0
for n in range(0,6):
  for k in range(0,n+1):
    L=lexsets(n,k)
    for r in range(len(L)+1):
      for F in itertools.combinations(L,r):
        if len(up(F,n))<sig(n,k,r): bad+=1
print("KK bad",bad)
# greedy, integer degrees antitone
def cap(n,k): return comb(n,k) if k>=0 else 0
def cost(n,k,t): return sig(n,k,t) if k>=0 else 0
bad=0
for n in range(0,6):
  for r in range(1,4):
    for ks in itertools.product(range(-1,n+2),repeat=r):
      if list(ks)!=sorted(ks,reverse=True): continue
      C=[cap(n,k) for k in ks]
      for T in range(sum(C)+1):
        g=[];R=T
        for c in C: m=min(R,c); g.append(m); R-=m
        gc=sum(cost(n,k,x) for k,x in zip(ks,g))
        for v in itertools.product(*[range(c+1) for c in C]):
          if sum(v)==T and sum(cost(n,k,x) for k,x in zip(ks,v))<gc: bad+=1
print("greedy bad",bad)
