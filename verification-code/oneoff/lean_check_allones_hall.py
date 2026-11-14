# Changelog (newest first)
# 2026-10-21  Copied from a Lean agent's scratch check into code/oneoff by the coordinator: Hall form of the all-ones Corollary C and the Theorem A inequality, random cases, sanity check for AllOnes/Hall.lean.

import itertools, random
from fractions import Fraction
random.seed(1)
def subsets(N):
    for m in range(1<<N): yield [i for i in range(N) if m>>i&1]
bad=0; tests=0
for trial in range(3000):
    N=random.randint(1,5); r=random.randint(0,4)
    W=[frozenset(i for i in range(N) if random.random()<0.5) for _ in range(r)]
    sums=set()
    for ch in itertools.product(*[sorted(w) for w in W]):
        y=[0]*N
        for i in ch: y[i]+=1
        sums.add(tuple(y))
    for y in itertools.product(range(r+2),repeat=N):
        if sum(y)!=r: continue
        cond=all(sum(y[i] for i in J)<= sum(1 for w in W if w & set(J)) for J in subsets(N))
        tests+=1
        if cond != (y in sums): bad+=1; print("BAD",N,W,y)
    # intervals with ties, Abel inequality on Q points: random rational c and vertices check via LP-free: test random points of Q? use sumset points & convex combos
print("tests",tests,"bad",bad)
# Abel inequality: check c.y <= sum max on integer points of Q (= sumset) and on random rational points of Q found by rejection
bad2=0
for trial in range(2000):
    N=random.randint(1,4); r=random.randint(1,3)
    W=[frozenset(random.sample(range(N),random.randint(1,N))) for _ in range(r)]
    c=[random.randint(-3,3) for _ in range(N)]
    rhs=sum(max(c[i] for i in w) for w in W)
    for _ in range(50):
        y=[Fraction(random.randint(-2*r,4*r),4) for _ in range(N-1)]; y.append(r-sum(y))
        if all(sum(y[i] for i in J)<= sum(1 for w in W if w & set(J)) for J in subsets(N)):
            if sum(a*b for a,b in zip(c,y))>rhs: bad2+=1
print("abel bad",bad2)
