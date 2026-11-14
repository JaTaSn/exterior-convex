# Changelog (newest first)
# 2026-10-18 09:58  Claude-Code (jts-pc): created. Classifies every [0,1]-sequence for
#                   n=1, r=2, f=(0,0) under four readings of Amata-Crupi Theorem 4.2(b)
#                   (literal, charitable, repaired, and charitable-applied-to-H_M) against
#                   ground truth. Backs working-notes/amata-crupi-thm42-b-worked-n1-r2.org.
"""Amata-Crupi, 'A generalization of Kruskal-Katona's theorem' (2020), Theorem 4.2(b),
evaluated clause by clause on the smallest tied example.  Pure Python, no dependencies."""
from itertools import product


def C(m, k):
    """Binomial with the paper's convention: 0 if m < k or k < 0."""
    if k < 0 or m < k:
        return 0
    out = 1
    for t in range(k):
        out = out * (m - t) // (t + 1)
    return out


def macaulay_upper(a, i):
    """a^(i) of the paper (Section 3); 0^(i) = 0.  Needs i >= 1 when a > 0."""
    if a == 0:
        return 0
    assert i >= 1, "Macaulay expansion undefined in degree <= 0"
    out, k = 0, i
    while a > 0:
        m = k
        while C(m + 1, k) <= a:
            m += 1
        out += C(m, k + 1)
        a -= C(m, k)
        k -= 1
    return out


n, f = 1, (0, 0)
r = len(f)
lo, hi = f[0], f[-1] + n                      # the HsF/M-degrees [f1, fr+n] = [0, 1]
dimF = {d: sum(C(n, d - fj) for fj in f) for d in range(lo, hi + 1)}


def tail(d, N):
    """sum_{j=N+1}^{r} C(n, d - f_j), with j 1-indexed."""
    return sum(C(n, d - f[j - 1]) for j in range(N + 1, r + 1))


def b_holds(h, reading):
    H = dict(zip(range(lo, hi + 1), h))
    nz = [k for k in H if H[k] != 0]
    if not nz:
        return None                            # s = min of the empty set: theorem silent
    s = nz[0]
    r0 = sum(1 for fj in f if fj == s)
    r1 = sum(1 for fj in f if fj == s + 1)
    if not H[s] <= r0:
        return False
    bound = n * H[s] + r1 if reading == "repaired" else n * r0 + r1
    if s + 1 <= hi and not H[s + 1] <= bound:
        return False
    for i in range(s + 1, hi + 1):
        if reading == "literal":
            Ns, amin = range(1, r + 1), 1      # 0 < N <= r, a positive
        else:
            Ns, amin = range(0, r + 1), 0      # 0 <= N <= r, a >= 0
        reps = []
        for N in Ns:
            a = H[i] - tail(i, N)
            if N == 0:
                if a == 0:
                    reps.append((N, a))
            elif amin <= a < C(n, i - f[N - 1]):
                reps.append((N, a))
        if not reps:
            return False
        assert len(reps) == 1, (h, i, reps)   # N is unique whenever it exists
        N, a = reps[0]
        nxt = H.get(i + 1, 0)                  # h_{fr+n+1} = 0: the clause is vacuous at the top
        growth = tail(i + 1, N) + (macaulay_upper(a, i - f[N - 1]) if N > 0 else 0)
        if not nxt <= growth:
            return False
    return True


# Ground truth.  Quotients E/I for n=1: I = 0, (e1), E give (1,1), (1,0), (0,0).  By the
# initial-module reduction every H_{F/M} is that of a monomial M = I1 g1 + I2 g2, so the
# achievable H_{F/M} are the pairwise sums.
quot = [(1, 1), (1, 0), (0, 0)]
truth_FM = {tuple(x + y for x, y in zip(u, v)) for u in quot for v in quot}
truth_M = {tuple(dimF[d] - h[d - lo] for d in range(lo, hi + 1)) for h in truth_FM}

if __name__ == "__main__":
    print(f"n={n}, f={f}, dim F_d = {[dimF[d] for d in range(lo, hi + 1)]}")
    hdr = "h        H(F/M)?  literal  charitable  repaired   H(M)?  charitable-on-H_M"
    print(hdr)
    for h in product(*(range(dimF[d] + 1) for d in range(lo, hi + 1))):
        cells = [h in truth_FM] + [b_holds(h, k) for k in ("literal", "charitable", "repaired")]
        cells += [h in truth_M, b_holds(h, "charitable")]
        print(f"{str(h):8} " + "  ".join(f"{str(c):9}" for c in cells))
