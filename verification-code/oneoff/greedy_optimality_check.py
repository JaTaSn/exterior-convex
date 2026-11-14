# Changelog (newest first)
# 2026-10-20  Claude-Code (jts-pc, overnight article-3 push): created. Computational backing for
#             working-notes/module-kruskal-katona-greedy-proof-2026-10-20.org:
#             (1) the lex-shadow recursion and "shadow of a lex segment is a lex segment" (rank 1);
#             (2) the two-component inequalities P and Q on lex shadow sizes sigma_n(k,t);
#             (3) a *proof replay*: every case of the inductive proof of P(n), Q(n) is re-run with
#                 its hypotheses (range conditions, degree order) asserted for each invoked
#                 instance of P(n-1), Q(n-1), and the chain of inequalities re-evaluated;
#             (4) kappa_n(a,k) = a^(k) (Macaulay/Kruskal-Katona operator);
#             (5) module brute force: min shadow over ALL monomial subsets of Mon_j(F) equals the
#                 shadow of the lex_F segment, the latter is a lex_F segment, and
#                 dim F_{j+1} - min = B(h,j) as in def-B;
#             (6) split optimisation for larger n (all splits, rank-1 minima);
#             (7) non-monomial subspaces over GF(2) (exhaustive) and GF(3) (random);
#             (8) the full repaired Theorem 4.2: B-condition vs ground-truth sumset.
#             Pure Python 3, no dependencies.  Run:  python3 greedy_optimality_check.py
"""Greedy optimality / module Kruskal-Katona for F = (+)_i E g_i over the exterior algebra."""
import sys
import random
import time
from functools import lru_cache
from itertools import combinations, product
from math import comb

LOG = []


def out(*a):
    s = " ".join(str(x) for x in a)
    print(s, flush=True)
    LOG.append(s)


def C(m, k):
    return comb(m, k) if 0 <= k <= m else 0


# ---------------------------------------------------------------- rank 1 -------------------------
@lru_cache(None)
def sig(n, k, t):
    """sigma_n(k,t): shadow size of the first t k-subsets of [n] in lex, via the recursion
    (R1) k>=1, t<=C(n-1,k-1): sig(n-1,k-1,t);  (R2) t>C(n-1,k-1): C(n-1,k)+sig(n-1,k,t-C(n-1,k-1))."""
    assert k >= 0 and 0 <= t <= C(n, k), (n, k, t)
    if t == 0 or n == 0:
        return 0
    a = C(n - 1, k - 1)
    if k >= 1 and t <= a:
        return sig(n - 1, k - 1, t)
    return C(n - 1, k) + sig(n - 1, k, t - a)


def lexlist(n, k):
    """k-subsets of [n] in decreasing lex_E order (e_1 > ... > e_n; tuple order = lex)."""
    return sorted(combinations(range(1, n + 1), k))


def ushadow(fam, n):
    return {tuple(sorted(S + (x,))) for S in fam for x in range(1, n + 1) if x not in S}


def kappa(n, k, a):
    """max quotient growth from a quotient of size a in exterior degree k (rank 1)."""
    return C(n, k + 1) - sig(n, k, C(n, k) - a)


def macaulay_upper(a, i):
    """a^(i) of Aramova-Herzog-Hibi / Amata-Crupi (i>=1), 0^(i)=0."""
    if a == 0:
        return 0
    res, j = 0, i
    while a > 0 and j >= 1:
        m = j
        while C(m + 1, j) <= a:
            m += 1
        res += C(m, j + 1)
        a -= C(m, j)
        j -= 1
    assert a == 0
    return res


def check_rank1(nmax=9):
    t0 = time.time()
    cnt = 0
    for n in range(0, nmax + 1):
        for k in range(0, n + 1):
            L = lexlist(n, k)
            L1 = lexlist(n, k + 1)
            for t in range(len(L) + 1):
                sh = ushadow(L[:t], n)
                assert len(sh) == sig(n, k, t), (n, k, t)
                assert set(L1[:len(sh)]) == sh, ("lex shadow not lex", n, k, t)
                if t < len(L):  # increment bound F3
                    assert sig(n, k, t + 1) - sig(n, k, t) <= n - k
                cnt += 1
            assert sig(n, k, C(n, k)) == C(n, k + 1)
            for a in range(C(n, k) + 1):
                if k >= 1 and a < C(n, k):
                    assert kappa(n, k, a) == macaulay_upper(a, k), (n, k, a)
    out(f"[1] rank-1: recursion = direct lex shadow, shadow(lex) is lex, increment <= n-k, "
        f"sigma(full)=C(n,k+1), kappa=a^(k): {cnt} cases, n<={nmax}, OK ({time.time()-t0:.1f}s)")


def P_holds(n, k, kp, x, y):
    return sig(n, k, x + y) <= sig(n, k, x) + sig(n, kp, y)


def Q_holds(n, k, kp, x, y):
    return sig(n, k, x) + sig(n, kp, y) >= C(n, k + 1) + sig(n, kp, x + y - C(n, k))


def check_PQ(nmax=13):
    t0 = time.time()
    np_ = nq = 0
    tight_P = tight_Q = 0
    for n in range(0, nmax + 1):
        for k in range(0, n + 2):
            for kp in range(0, k + 1):
                Ck, Ckp = C(n, k), C(n, kp)
                for x in range(Ck + 1):
                    for y in range(Ckp + 1):
                        if x + y <= Ck:
                            assert P_holds(n, k, kp, x, y), ("P", n, k, kp, x, y)
                            np_ += 1
                        if x + y >= Ck:
                            assert Q_holds(n, k, kp, x, y), ("Q", n, k, kp, x, y)
                            nq += 1
    out(f"[2] P and Q hold for all n<={nmax}, all k>=k'>=0 (k<=n+1), all sizes: "
        f"{np_} P-instances, {nq} Q-instances ({time.time()-t0:.1f}s)")


# ---------------------------------------------------------------- proof replay -------------------
class Replay:
    """Re-runs the case analysis of the inductive proof.  Each call P_ih / Q_ih asserts the
    hypotheses of the invoked instance at level n-1 and returns the inequality it provides."""

    def __init__(self, n):
        self.n1 = n - 1
        self.used = {}

    def _ok_P(self, k, kp, x, y):
        m = self.n1
        assert k >= kp >= 0, ("P-ih degree order", k, kp)
        assert x >= 0 and y >= 0 and x + y <= C(m, k) and y <= C(m, kp), ("P-ih range", m, k, kp, x, y)
        assert P_holds(m, k, kp, x, y)

    def _ok_Q(self, k, kp, x, y):
        m = self.n1
        assert k >= kp >= 0, ("Q-ih degree order", k, kp)
        assert 0 <= x <= C(m, k) and 0 <= y <= C(m, kp) and x + y >= C(m, k), ("Q-ih range", m, k, kp, x, y)
        assert Q_holds(m, k, kp, x, y)

    def P_ih(self, k, kp, x, y, tag):
        self._ok_P(k, kp, x, y)
        self.used[tag] = self.used.get(tag, 0) + 1

    def Q_ih(self, k, kp, x, y, tag):
        self._ok_Q(k, kp, x, y)
        self.used[tag] = self.used.get(tag, 0) + 1


def replay_P(n, k, kp, x, y, R, cases):
    """P(n): sig_n(k,x+y) <= sig_n(k,x) + sig_n(kp,y), with k>=kp>=1, y>=1, n>=1."""
    s = lambda kk, t: sig(n - 1, kk, t)
    S = lambda kk, t: sig(n, kk, t)
    a, b, ap, bp = C(n - 1, k - 1), C(n - 1, k), C(n - 1, kp - 1), C(n - 1, kp)
    # recursion facts used
    assert s(k - 1, a) == b and s(kp - 1, ap) == bp
    if x + y <= a:
        assert S(k, x + y) == s(k - 1, x + y) and S(k, x) == s(k - 1, x)
        if y <= ap:
            cases.add("P.A1"); assert S(kp, y) == s(kp - 1, y)
            R.P_ih(k - 1, kp - 1, x, y, "P.A1")
            assert s(k - 1, x + y) <= s(k - 1, x) + s(kp - 1, y)
        else:
            cases.add("P.A2"); assert k > kp
            y2 = y - ap; assert S(kp, y) == bp + s(kp, y2)
            R.P_ih(k - 1, kp - 1, x + y2, ap, "P.A2")
            R.P_ih(k - 1, kp, x, y2, "P.A2")
            assert s(k - 1, x + y) <= s(k - 1, x + y2) + bp <= s(k - 1, x) + s(kp, y2) + bp
    elif x >= a:
        x0 = x - a
        assert S(k, x) == b + s(k, x0) and S(k, x + y) == b + s(k, x0 + y)
        if y <= ap:
            cases.add("P.B1"); assert S(kp, y) == s(kp - 1, y)
            R.P_ih(k, kp - 1, x0, y, "P.B1")
        else:
            cases.add("P.B2"); y2 = y - ap; assert S(kp, y) == bp + s(kp, y2)
            R.P_ih(k, kp - 1, x0 + y2, ap, "P.B2")
            R.P_ih(k, kp, x0, y2, "P.B2")
            assert s(k, x0 + y) <= s(k, x0 + y2) + bp <= s(k, x0) + s(kp, y2) + bp
    else:
        z = x + y - a
        assert S(k, x + y) == b + s(k, z) and S(k, x) == s(k - 1, x)
        if y <= ap:
            cases.add("P.C1"); assert S(kp, y) == s(kp - 1, y)
            R.Q_ih(k - 1, kp - 1, x, y, "P.C1")
            R.P_ih(k, kp - 1, 0, z, "P.C1")
            assert b + s(k, z) <= b + s(kp - 1, z) <= s(k - 1, x) + s(kp - 1, y)
        else:
            y2 = y - ap; w0 = x + ap - a; assert S(kp, y) == bp + s(kp, y2)
            if w0 >= 0:
                cases.add("P.C2a")
                R.Q_ih(k - 1, kp - 1, x, ap, "P.C2a")
                R.P_ih(k, kp, w0, y2, "P.C2a")
                R.P_ih(k, kp - 1, 0, w0, "P.C2a")
                assert z == w0 + y2
                assert b + s(k, z) <= b + s(k, w0) + s(kp, y2) <= b + s(kp - 1, w0) + s(kp, y2) \
                    <= s(k - 1, x) + bp + s(kp, y2)
            else:
                cases.add("P.C2b"); assert k > kp
                R.P_ih(k - 1, kp - 1, x, ap, "P.C2b")
                R.Q_ih(k - 1, kp, x + ap, y2, "P.C2b")
                R.P_ih(k, kp, 0, z, "P.C2b")
                assert b + s(k, z) <= b + s(kp, z) <= s(k - 1, x + ap) + s(kp, y2) \
                    <= s(k - 1, x) + bp + s(kp, y2)
    assert S(k, x + y) <= S(k, x) + S(kp, y)


def replay_Q(n, k, kp, x, y, R, cases):
    """Q(n): sig_n(k,x)+sig_n(kp,y) >= C(n,k+1)+sig_n(kp,w), w=x+y-C(n,k); k>=kp>=1, y>=1."""
    s = lambda kk, t: sig(n - 1, kk, t)
    S = lambda kk, t: sig(n, kk, t)
    a, b, ap, bp = C(n - 1, k - 1), C(n - 1, k), C(n - 1, kp - 1), C(n - 1, kp)
    c = C(n - 1, k + 1)
    assert s(k, b) == c and C(n, k + 1) == b + c and s(kp - 1, ap) == bp
    w = x + y - a - b
    assert 0 <= w <= y
    target_rhs = b + c + S(kp, w)
    if x >= a:
        x0 = x - a; assert S(k, x) == b + s(k, x0)
        if y <= ap:
            cases.add("Q.A'1"); assert S(kp, y) == s(kp - 1, y) and S(kp, w) == s(kp - 1, w)
            R.Q_ih(k, kp - 1, x0, y, "Q.A'1")
            assert x0 + y - b == w
        elif w >= ap:
            cases.add("Q.A'2")
            assert S(kp, y) == bp + s(kp, y - ap) and S(kp, w) == bp + s(kp, w - ap)
            R.Q_ih(k, kp, x0, y - ap, "Q.A'2")
            assert x0 + (y - ap) - b == w - ap
        else:
            cases.add("Q.A'3"); u = y - ap
            assert S(kp, y) == bp + s(kp, u) and S(kp, w) == s(kp - 1, w)
            R.P_ih(k, kp, x0, u, "Q.A'3")
            R.Q_ih(k, kp - 1, x0 + u, ap, "Q.A'3")
            assert x0 + u + ap - b == w
            assert s(k, x0) + s(kp, u) + bp >= s(k, x0 + u) + bp >= c + s(kp - 1, w)
    else:
        assert S(k, x) == s(k - 1, x)
        if y <= ap:
            cases.add("Q.B'1"); assert S(kp, y) == s(kp - 1, y) and S(kp, w) == s(kp - 1, w)
            R.Q_ih(k - 1, kp - 1, x, y, "Q.B'1")
            R.Q_ih(k, kp - 1, 0, w + b, "Q.B'1")
            assert x + y - a == w + b
            assert s(k - 1, x) + s(kp - 1, y) >= b + s(kp - 1, w + b) >= b + c + s(kp - 1, w)
        elif w >= ap:
            cases.add("Q.B'2"); assert k > kp
            assert S(kp, y) == bp + s(kp, y - ap) and S(kp, w) == bp + s(kp, w - ap)
            R.Q_ih(k - 1, kp, x, y - ap, "Q.B'2")
            R.Q_ih(k, kp, 0, w - ap + b, "Q.B'2")
            assert s(k - 1, x) + s(kp, y - ap) >= b + s(kp, w - ap + b) >= b + c + s(kp, w - ap)
        else:
            u = y - ap
            assert S(kp, y) == bp + s(kp, u) and S(kp, w) == s(kp - 1, w)
            if k == kp:
                cases.add("Q.B'3(k=k')")
                R.Q_ih(k, k - 1, u, x, "Q.B'3(k=k')")
                assert x + u - b == w
            elif x + u >= a:
                cases.add("Q.B'3a"); q = x + u - a
                R.Q_ih(k - 1, kp, x, u, "Q.B'3a")
                R.P_ih(k, kp, 0, q, "Q.B'3a")
                R.Q_ih(k, kp - 1, q, ap, "Q.B'3a")
                assert q + ap - b == w
                assert s(k - 1, x) + s(kp, u) + bp >= b + s(kp, q) + bp >= b + s(k, q) + bp \
                    >= b + c + s(kp - 1, w)
            else:
                cases.add("Q.B'3b")
                R.P_ih(k - 1, kp, x, u, "Q.B'3b")
                R.Q_ih(k - 1, kp - 1, x + u, ap, "Q.B'3b")
                R.Q_ih(k, kp - 1, 0, w + b, "Q.B'3b")
                assert x + u + ap - a == w + b
                assert s(k - 1, x) + s(kp, u) + bp >= s(k - 1, x + u) + bp >= b + s(kp - 1, w + b) \
                    >= b + c + s(kp - 1, w)
    assert S(k, x) + S(kp, y) >= target_rhs


def check_replay(nmax=11):
    t0 = time.time()
    cases = set()
    tot = 0
    for n in range(1, nmax + 1):
        R = Replay(n)
        for k in range(1, n + 2):
            for kp in range(1, k + 1):
                Ck, Ckp = C(n, k), C(n, kp)
                for x in range(Ck + 1):
                    for y in range(1, Ckp + 1):
                        if x + y <= Ck:
                            replay_P(n, k, kp, x, y, R, cases); tot += 1
                        if x + y >= Ck:
                            replay_Q(n, k, kp, x, y, R, cases); tot += 1
        # k' = 0 direct cases (any k>=0): P via increment bound, Q via increment bound
        for k in range(0, n + 1):
            for x in range(C(n, k)):
                assert sig(n, k, x + 1) <= sig(n, k, x) + (n - k) <= sig(n, k, x) + sig(n, 0, 1)
            if C(n, k) >= 1:
                assert sig(n, k, C(n, k) - 1) + n >= C(n, k + 1)
    out(f"[3] proof replay of the induction P(n-1),Q(n-1) => P(n),Q(n), n=1..{nmax}: {tot} instances, "
        f"every invoked IH instance within its hypotheses; cases exercised: {sorted(cases)} "
        f"({time.time()-t0:.1f}s)")
    allcases = {"P.A1", "P.A2", "P.B1", "P.B2", "P.C1", "P.C2a", "P.C2b", "Q.A'1", "Q.A'2", "Q.A'3",
                "Q.B'1", "Q.B'2", "Q.B'3(k=k')", "Q.B'3a", "Q.B'3b"}
    out(f"    cases never exercised: {sorted(allcases - cases) or 'none'}")


# ---------------------------------------------------------------- module level -------------------
def module_monomials(n, d, j):
    """Mon_j(F) in DECREASING lex_F order: u g_i > v g_l iff i<l, or i=l and u >lex v."""
    mons = []
    for i, di in enumerate(d):
        k = j - di
        if 0 <= k <= n:
            for u in lexlist(n, k):
                mons.append((i, u))
    return mons


def B_def(n, d, j, h):
    """def-B of the article-3 stub (Prop 4.1 repaired): fill the quotient from the last generator."""
    r = len(d)
    caps = [C(n, j - di) for di in d]
    assert 0 <= h <= sum(caps)
    val, i = h, r - 1
    while i >= 0 and val >= caps[i]:
        val -= caps[i]; i -= 1
    if i < 0:  # N = 0
        return sum(C(n, j + 1 - dl) for dl in d)
    # N = i (0-based), a = val, 0 <= a < caps[i]
    kN = j - d[i]
    term = macaulay_upper(val, kN) if kN >= 1 else 0  # kN = 0 forces a = 0
    return sum(C(n, j + 1 - d[l]) for l in range(i + 1, r)) + term


def is_lexF_segment(S, mons_sorted):
    """S a set of monomials; segment iff it is an initial part of the decreasing list."""
    m = len(S)
    return set(mons_sorted[:m]) == set(S)


def check_module_bruteforce(configs, maxdim=18):
    t0 = time.time()
    ncase = 0
    nsets = 0
    for (n, d) in configs:
        jlo, jhi = min(d) - 1, max(d) + n
        for j in range(jlo, jhi + 1):
            mons = module_monomials(n, d, j)
            mons1 = module_monomials(n, d, j + 1)
            idx1 = {m: p for p, m in enumerate(mons1)}
            D = len(mons)
            if D > maxdim:
                continue
            shmask = []
            for (i, u) in mons:
                msk = 0
                for x in range(1, n + 1):
                    if x not in u:
                        msk |= 1 << idx1[(i, tuple(sorted(u + (x,))))]
                shmask.append(msk)
            best = [10 ** 9] * (D + 1)
            sh = [0] * (1 << D)
            for mask in range(1, 1 << D):
                low = mask & -mask
                p = low.bit_length() - 1
                sh[mask] = sh[mask ^ low] | shmask[p]
                c = mask.bit_count()
                v = sh[mask].bit_count()
                if v < best[c]:
                    best[c] = v
            best[0] = 0
            nsets += 1 << D
            dimF1 = len(mons1)
            for t in range(D + 1):
                L = mons[:t]
                shL = set()
                for (i, u) in L:
                    for x in range(1, n + 1):
                        if x not in u:
                            shL.add((i, tuple(sorted(u + (x,)))))
                assert len(shL) == best[t], ("lex not optimal", n, d, j, t, len(shL), best[t])
                assert is_lexF_segment(shL, mons1), ("shadow of lex_F not lex_F", n, d, j, t)
                h = D - t
                assert dimF1 - best[t] == B_def(n, d, j, h), ("B mismatch", n, d, j, h)
                ncase += 1
    out(f"[5] module brute force over ALL monomial subsets of Mon_j(F): {len(configs)} configurations, "
        f"{ncase} (j,size) cases, {nsets} subsets; min shadow = shadow of lex_F segment, "
        f"shadow(lex_F) is lex_F, dim F_(j+1) - min = B(h,j): OK ({time.time()-t0:.1f}s)")


@lru_cache(None)
def rank1_min_shadow_brute(n, k):
    """exact min upper shadow over all families of k-subsets of [n], per size (brute force)."""
    L = lexlist(n, k)
    L1 = lexlist(n, k + 1)
    idx = {S: p for p, S in enumerate(L1)}
    D = len(L)
    shm = []
    for S in L:
        m = 0
        for x in range(1, n + 1):
            if x not in S:
                m |= 1 << idx[tuple(sorted(S + (x,)))]
        shm.append(m)
    best = [10 ** 9] * (D + 1); best[0] = 0
    sh = [0] * (1 << D)
    for mask in range(1, 1 << D):
        low = mask & -mask
        sh[mask] = sh[mask ^ low] | shm[low.bit_length() - 1]
        c = mask.bit_count(); v = sh[mask].bit_count()
        if v < best[c]:
            best[c] = v
    return tuple(best)


def check_splits(nmax_brute=6, nmax_lex=9, rmax=4):
    """All splits (t_1..t_r) of t, cost sum of rank-1 minima; greedy (fill g_1 first) optimal."""
    t0 = time.time()
    # rank-1 KK itself, brute force
    for n in range(0, nmax_brute + 1):
        for k in range(0, n + 1):
            if C(n, k) <= 20:
                best = rank1_min_shadow_brute(n, k)
                assert list(best) == [sig(n, k, t) for t in range(C(n, k) + 1)], (n, k)
    out(f"[6a] rank-1 Kruskal-Katona (lex minimises upper shadow) brute-force confirmed, n<={nmax_brute}")
    ncfg = 0
    for n in range(1, nmax_lex + 1):
        for r in range(1, rmax + 1):
            for ks in combinations_with_replacement_desc(range(-1, n + 1), r):
                caps = [C(n, k) if k >= 0 else 0 for k in ks]
                cost = [[sig(n, k, t) for t in range(cp + 1)] if k >= 0 else [0] for k, cp in zip(ks, caps)]
                # DP min over splits
                tot = sum(caps)
                INF = 10 ** 9
                dp = [0] + [INF] * tot
                for cp, cs in zip(caps, cost):
                    nd = [INF] * (tot + 1)
                    for s0 in range(tot + 1):
                        if dp[s0] < INF:
                            for t in range(cp + 1):
                                if s0 + t <= tot:
                                    v = dp[s0] + cs[t]
                                    if v < nd[s0 + t]:
                                        nd[s0 + t] = v
                    dp = nd
                for t in range(tot + 1):
                    rem, g = t, 0
                    for cp, cs in zip(caps, cost):
                        x = min(rem, cp); g += cs[x]; rem -= x
                    assert g == dp[t], ("greedy not optimal", n, ks, t, g, dp[t])
                ncfg += 1
    out(f"[6b] split optimisation: greedy (largest exterior degree = smallest d first) attains the "
        f"minimum over ALL splits, n<={nmax_lex}, r<={rmax}, all non-increasing degree vectors in "
        f"[-1,n]^r: {ncfg} configurations ({time.time()-t0:.1f}s)")


def combinations_with_replacement_desc(rng, r):
    from itertools import combinations_with_replacement
    for c in combinations_with_replacement(sorted(rng, reverse=True), r):
        yield c  # non-increasing


# ---------------------------------------------------------------- non-monomial -------------------
def ext_mult(x, u):
    """e_x * e_u = sign * e_{u+x}, or None."""
    if x in u:
        return None
    sgn = (-1) ** sum(1 for y in u if y < x)
    return sgn, tuple(sorted(u + (x,)))


def rank_mod(rows, p):
    rows = [r[:] for r in rows]
    rk = 0
    ncol = len(rows[0]) if rows else 0
    for col in range(ncol):
        piv = None
        for i in range(rk, len(rows)):
            if rows[i][col] % p:
                piv = i; break
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][col], p - 2, p)
        rows[rk] = [(v * inv) % p for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col] % p:
                f = rows[i][col]
                rows[i] = [(vi - f * vr) % p for vi, vr in zip(rows[i], rows[rk])]
        rk += 1
    return rk


def shadow_dim(basis, mons, mons1, n, p):
    idx1 = {m: q for q, m in enumerate(mons1)}
    rows = []
    for v in basis:
        for x in range(1, n + 1):
            row = [0] * len(mons1)
            for coef, (i, u) in zip(v, mons):
                if coef % p:
                    r_ = ext_mult(x, u)
                    if r_:
                        sgn, w = r_
                        row[idx1[(i, w)]] = (row[idx1[(i, w)]] + sgn * coef) % p
            rows.append(row)
    if not rows or not mons1:
        return 0
    return rank_mod(rows, p)


def all_subspaces_gf2(m):
    """all subspaces of GF(2)^m as RREF bases."""
    for r in range(m + 1):
        for piv in combinations(range(m), r):
            free = [(i, c) for i in range(r) for c in range(piv[i] + 1, m) if c not in piv]
            for bits in product((0, 1), repeat=len(free)):
                B = [[0] * m for _ in range(r)]
                for i in range(r):
                    B[i][piv[i]] = 1
                for (i, c), bt in zip(free, bits):
                    B[i][c] = bt
                yield B


def check_nonmonomial(configs_exh, configs_rand, nrand=300, seed=20261020):
    t0 = time.time()
    tot = 0
    for (n, d) in configs_exh:
        for j in range(min(d) - 1, max(d) + n + 1):
            mons = module_monomials(n, d, j)
            mons1 = module_monomials(n, d, j + 1)
            D = len(mons)
            if D == 0 or D > 6:
                continue
            for Bs in all_subspaces_gf2(D):
                t = len(Bs)
                lexsh = len(ushadow_mod(mons[:t], n))
                assert shadow_dim(Bs, mons, mons1, n, 2) >= lexsh, (n, d, j, Bs)
                tot += 1
    out(f"[7a] GF(2), ALL subspaces V of F_j (dim F_j <= 6): dim E_1 V >= |Shad(lex_F)|, "
        f"{tot} subspaces, {len(configs_exh)} configurations: OK")
    rnd = random.Random(seed)
    tot2 = 0
    for (n, d) in configs_rand:
        for j in range(min(d) - 1, max(d) + n + 1):
            mons = module_monomials(n, d, j)
            mons1 = module_monomials(n, d, j + 1)
            D = len(mons)
            if D == 0:
                continue
            for _ in range(nrand):
                t = rnd.randint(1, D)
                # sparse-ish random vectors to make degenerate cases likely
                Bs = []
                while len(Bs) < t:
                    v = [rnd.choice([0, 0, 1, 2]) for _ in range(D)]
                    if rank_mod(Bs + [v], 3) == len(Bs) + 1:
                        Bs.append(v)
                lexsh = len(ushadow_mod(mons[:t], n))
                assert shadow_dim(Bs, mons, mons1, n, 3) >= lexsh
                tot2 += 1
    out(f"[7b] GF(3), random subspaces (signs live): {tot2} subspaces over {len(configs_rand)} "
        f"configurations: dim E_1 V >= |Shad(lex_F)|: OK ({time.time()-t0:.1f}s)")


def ushadow_mod(L, n):
    return {(i, tuple(sorted(u + (x,)))) for (i, u) in L for x in range(1, n + 1) if x not in u}


# ---------------------------------------------------------------- full theorem -------------------
def fvectors(n):
    """Hilbert sequences (h_0..h_n) of E/I, I monomial (incl. I=E): f-vectors of down-closed families."""
    subsets = [frozenset(c) for k in range(n + 1) for c in combinations(range(n), k)]
    res = set()
    # enumerate antichains-generated down-sets by brute force over all subsets of the boolean lattice
    # is 2^(2^n); fine for n<=4 (65536)
    N = len(subsets)
    for mask in range(1 << N):
        fam = [subsets[i] for i in range(N) if mask >> i & 1]
        S = set(fam)
        if all((A - {x}) in S for A in fam for x in A):
            v = [0] * (n + 1)
            for A in fam:
                v[len(A)] += 1
            res.add(tuple(v))
    return res


def check_full_theorem(configs):
    t0 = time.time()
    fv = {}
    report = []
    for (n, d) in configs:
        if n not in fv:
            fv[n] = fvectors(n)
        lo, hi = d[0], d[-1] + n
        L = hi - lo + 1
        truth = {tuple([0] * L)}
        for di in d:
            new = set()
            for s in truth:
                for v in fv[n]:
                    w = list(s)
                    for e, val in enumerate(v):
                        w[di - lo + e] += val
                    new.add(tuple(w))
            truth = new
        dims = [sum(C(n, j - di) for di in d) for j in range(lo, hi + 1)]
        cand = 0
        fp = fn = 0
        for H in product(*[range(D + 1) for D in dims]):
            cand += 1
            ok = True
            prev = 0
            for idx in range(L):
                j = lo + idx - 1  # condition h_{j+1} <= B(h_j, j)
                if H[idx] > B_def(n, d, j, prev):
                    ok = False; break
                prev = H[idx]
            if ok and H not in truth:
                fp += 1
            if (not ok) and H in truth:
                fn += 1
        report.append((n, d, len(truth), cand, fp, fn))
        assert fp == 0 and fn == 0, (n, d, fp, fn)
    out(f"[8] repaired Theorem 4.2 (h_(j+1) <= B(h_j,j) for j in [d_1-1, d_r+n-1], h_(d_1-1)=0) vs "
        f"ground-truth sumset of f-vectors: {len(configs)} configurations, 0 false positives, "
        f"0 false negatives ({time.time()-t0:.1f}s)")
    for row in report:
        out("    n=%d d=%s achievable=%d candidates=%d fp=%d fn=%d" % row)


# ---------------------------------------------------------------- repaired clause ----------------
def check_initial_clause(nmax=5):
    cnt = 0
    for n in range(1, nmax + 1):
        for r in range(1, 4):
            for d in product(range(-2, 4), repeat=r):
                d = tuple(sorted(d))
                for s in range(d[0], d[-1] + n + 1):
                    r0 = sum(1 for x in d if x == s)
                    r1 = sum(1 for x in d if x == s + 1)
                    assert B_def(n, d, s - 1, 0) == r0
                    for hs in range(1, r0 + 1):
                        assert B_def(n, d, s, hs) == n * hs + r1, (n, d, s, hs)
                        cnt += 1
    out(f"[4b] B(0,s-1) = r~_0 and B(h_s,s) = n h_s + r~_1 for 1<=h_s<=r~_0: {cnt} cases "
        f"(n<={nmax}, r<=3, d in [-2,3]^r): OK")


def main():
    out("greedy_optimality_check.py  run", time.strftime("%Y-%m-%d %H:%M"))
    check_rank1(9)
    check_PQ(13)
    check_replay(11)
    check_initial_clause(5)
    # module configurations: n<=4, r<=3, all sorted d with d_1=0 and gaps up to 4 (ties included),
    # plus explicitly negative-degree ones (translation-equivalent, included as a sanity check)
    cfg_b = []
    for n in range(1, 5):
        for r in range(1, 4):
            for d in product(range(0, 5), repeat=r):
                if d[0] == 0 and list(d) == sorted(d):
                    cfg_b.append((n, tuple(d)))
        for d in [(-2, -1, 1), (-1, -1), (-2, 0, 0), (-3, -3, -2)]:
            cfg_b.append((n, d))
    check_module_bruteforce(cfg_b, maxdim=18)
    check_splits(6, 9, 4)
    exh = [(1, (0, 0)), (1, (0, 0, 0)), (1, (0, 1)), (2, (0, 0)), (2, (0, 1)), (2, (-1, 0)),
           (2, (0, 0, 1)), (3, (0, 0)), (3, (0, 1)), (3, (0, 2)), (2, (0, 0, 0))]
    rnd = [(3, (0, 0)), (3, (0, 0, 1)), (3, (-1, 0, 2)), (4, (0, 0)), (4, (0, 1)), (4, (0, 1, 1))]
    check_nonmonomial(exh, rnd, nrand=150)
    full = [(1, (0, 0)), (1, (0, 0, 0)), (1, (0, 1)), (2, (0, 0)), (2, (0, 1)), (2, (-2, 1)),
            (2, (0, 0, 0)), (2, (0, 0, 1)), (3, (0, 0)), (3, (1, 1)), (3, (0, 1)), (3, (0, 2)),
            (3, (0, 3)), (3, (0, 0, 0)), (3, (0, 0, 1)), (3, (-1, -1, 1)), (4, (0, 0)), (4, (0, 1)),
            (4, (0, 2)), (4, (-1, 0))]
    check_full_theorem(full)
    out("ALL CHECKS PASSED")
    if len(sys.argv) > 1:
        with open(sys.argv[1], "w") as fh:
            fh.write("\n".join(LOG) + "\n")


if __name__ == "__main__":
    main()
