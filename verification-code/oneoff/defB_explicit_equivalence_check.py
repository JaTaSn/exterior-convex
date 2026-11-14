# 2026-11-09 - Claude-Code (jts-mini): Jan approved (review item 12) the explicit form of def-B in Part III,
#   l(h,j) = min{l : T_l(j) <= h}, B = T_l(j+1) + a^{(k_l)}; this checks it against the draft-5 definition.
#   Plain Python 3, exact; n <= 6, r <= 3, degrees -2..3 (ties and negative degrees, as sec-module-kk allows).
from math import comb
from itertools import combinations_with_replacement
def C(n,k): return comb(n,k) if 0<=k<=n else 0
def macaulay_up(a,k):
    # a^{(k)} = sum binom(a_l, l+1) over the k-th Macaulay representation a = sum binom(a_l, l)
    if a==0 or k<=0: return 0
    out=0; l=k
    while a>0 and l>=1:
        m=l
        while C(m+1,l)<=a: m+=1
        a-=C(m,l); out+=C(m,l+1); l-=1
    return out
def T(n,d,l,j): return sum(C(n,j-di) for di in d[l:])        # sum over i = l+1..r (0-based slice)
def B_printed(n,d,h,j):
    r=len(d); dimF=T(n,d,0,j)
    if h==dimF: return T(n,d,0,j+1)
    for l in range(1,r+1):
        if T(n,d,l,j)<=h<T(n,d,l-1,j):
            a=h-T(n,d,l,j); k=j-d[l-1]
            assert 0<=a<C(n,k)
            return T(n,d,l,j+1)+macaulay_up(a,k)
    raise ValueError
def B_proposed(n,d,h,j):
    r=len(d); l=min(l for l in range(r+1) if T(n,d,l,j)<=h); a=h-T(n,d,l,j)
    return T(n,d,l,j+1)+(macaulay_up(a,j-d[l-1]) if l>=1 else 0)
cnt=0
for n in range(1,7):
  for r in range(1,4):
    for d in combinations_with_replacement(range(-2,4),r):
      for j in range(min(d)-2,max(d)+n+2):
        for h in range(T(n,d,0,j)+1):
          assert B_printed(n,d,h,j)==B_proposed(n,d,h,j),(n,d,h,j); cnt+=1
print("agree on",cnt,"cases (n<=6, r<=3, degrees in [-2,3], ties included)")
