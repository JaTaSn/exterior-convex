#!/usr/bin/env python3
# Changelog (newest first)
# 2026-10-20  Claude-Code (jts-pc, overnight article-3 push, adversarial referee): created.
#             Independent re-implementation (does NOT import or copy greedy_optimality_check.py)
#             of the checks needed to referee
#             working-notes/module-kruskal-katona-greedy-proof-2026-10-20.org.
#             Everything is computed from ACTUAL lex segments of sets, never from the recursion.
#             Usage: python3 review_module_kk_check.py > ../../runs/2026-10-20_article3-overnight-push/2026-10-20_review-module-kk.txt
"""
[R1] rank 1, n<=8: actual lex-initial segments; upper shadow is lex-initial (F4); recursion
     (R1)/(R2) agrees with actual sizes (F2); increment <= n-k (F3); full layer (F1);
     C(n,k+1) - sigma(k, C(n,k)-a) == a^{(k)} (own Macaulay operator).
[R2] P and Q of Prop. 3 for ACTUAL lex-shadow sizes, n<=8, all 0<=k'<=k<=n+1.
[R3] rank-1 Kruskal-Katona by exhaustion over all families, n<=6 (bitmask).
[R4] note's sec. 3.4 counterexample, n=4.
[R5] module: all monomial subsets of Mon_j(F), n<=4, r<=3, ties/negative degrees:
     min shadow == shadow of lex_F segment; shadow of lex_F segment is lex_F segment;
     dim F_{j+1} - min == B(h,j) (own implementation of stub def-B).
[R6] over GF(2) (n<=3, r<=2) and GF(3) (small dim): ALL subspaces V of F_j, with genuine
     exterior signs: min dim E_1 V == min monomial shadow (Lemma 1 loses nothing).
[R7] Theorem 8: {h : h_{j+1} <= B(h_j,j)} == achievable set (sums of shifted f-vectors of all
     simplicial complexes incl. void), various configurations.
[R8] Corollary 9.
[R9] Prop. 4 directly: greedy vs all splits, actual sigma, n<=7, r<=3, degrees in [-2,n+1].
"""
import itertools, sys, time
from math import comb

def C(n, k):
    return comb(n, k) if 0 <= k <= n else 0

# ---------------- rank 1 -----------------
def lex_ksets(n, k):
    # paper: e_s >lex e_t iff first differing index smaller in s; combinations() yields
    # sorted tuples in increasing tuple order == decreasing lex_E order. (e1e2 > e1e3 > e2e3)
    if k < 0 or k > n:
        return []
    return [frozenset(c) for c in itertools.combinations(range(1, n + 1), k)]

def up(fam, n):
    out = set()
    for S in fam:
        for x in range(1, n + 1):
            if x not in S:
                out.add(S | {x})
    return out

SIG = {}
def sigma_actual(n, k, t):
    key = (n, k, t)
    if key not in SIG:
        L = lex_ksets(n, k)
        assert 0 <= t <= len(L), key
        SIG[key] = len(up(L[:t], n))
    return SIG[key]

def macaulay_up(a, k):
    # a^{(k)}: a = C(a_k,k)+C(a_{k-1},k-1)+...+C(a_l,l), a_k>...>a_l>=l>=1; sum C(a_i,i+1)
    if a == 0:
        return 0
    assert k >= 1
    res, i = 0, k
    while a > 0 and i >= 1:
        m = i
        while comb(m + 1, i) <= a:
            m += 1
        a -= comb(m, i)
        res += comb(m, i + 1)
        i -= 1
    assert a == 0
    return res

def R1(out):
    cnt = 0
    for n in range(0, 9):
        for k in range(0, n + 1):
            L = lex_ksets(n, k); Lk1 = lex_ksets(n, k + 1)
            for t in range(len(L) + 1):
                sh = up(L[:t], n)
                s = len(sh)
                assert sh == set(Lk1[:s]), ("F4 fails", n, k, t)
                if t < len(L):
                    assert sigma_actual(n, k, t + 1) - s <= n - k
                if n >= 1:
                    al, be = C(n - 1, k - 1), C(n - 1, k)
                    if k >= 1 and t <= al:
                        assert s == sigma_actual(n - 1, k - 1, t), ("R1", n, k, t)
                    if t >= al and (k >= 1 or t >= 1):
                        assert s == be + sigma_actual(n - 1, k, t - al), ("R2", n, k, t)
                cnt += 1
            assert sigma_actual(n, k, len(L)) == C(n, k + 1)
            if k >= 1:
                for a in range(0, C(n, k)):
                    assert C(n, k + 1) - sigma_actual(n, k, C(n, k) - a) == macaulay_up(a, k), (n, k, a)
    out(f"[R1] rank 1 n<=8: F1,F2(R1/R2),F3,F4 and kappa=a^(k) on actual lex segments: {cnt} (n,k,t) OK")

def R2(out):
    nP = nQ = 0
    for n in range(0, 9):
        for k in range(0, n + 2):
            for kp in range(0, k + 1):
                Ck, Ckp = C(n, k), C(n, kp)
                s = lambda kk, t: sigma_actual(n, kk, t) if 0 <= kk <= n else 0
                for x in range(Ck + 1):
                    for y in range(Ckp + 1):
                        if x + y <= Ck:
                            assert s(k, x + y) <= s(k, x) + s(kp, y), ("P", n, k, kp, x, y)
                            nP += 1
                        if x + y >= Ck:
                            assert s(k, x) + s(kp, y) >= C(n, k + 1) + s(kp, x + y - Ck), ("Q", n, k, kp, x, y)
                            nQ += 1
    out(f"[R2] P and Q with ACTUAL lex shadows, n<=8, 0<=k'<=k<=n+1: {nP} P-, {nQ} Q-instances OK")

def R3(out):
    for n in range(0, 7):
        for k in range(0, n + 1):
            L = lex_ksets(n, k); U = lex_ksets(n, k + 1)
            idx = {S: i for i, S in enumerate(U)}
            masks = [sum(1 << idx[T] for T in up([S], n)) for S in L]
            m = len(L)
            best = [10**9] * (m + 1)
            # enumerate all families by Gray-code-free simple loop (2^20 max at n=6,k=3)
            sh = [0] * (1 << m)
            for f in range(1, 1 << m):
                low = f & -f; b = low.bit_length() - 1
                sh[f] = sh[f ^ low] | masks[b]
                c = bin(f).count("1"); v = bin(sh[f]).count("1")
                if v < best[c]:
                    best[c] = v
            best[0] = 0
            for t in range(m + 1):
                assert best[t] == sigma_actual(n, k, t), ("KK", n, k, t, best[t])
    out("[R3] rank-1 Kruskal-Katona (lex-initial minimises upper shadow), all families, n<=6: OK")

def R4(out):
    a = sigma_actual(4, 2, 1) + sigma_actual(4, 1, 3)
    b = sigma_actual(4, 2, 0) + sigma_actual(4, 1, 4)
    g = sigma_actual(4, 2, 4) + sigma_actual(4, 1, 0)
    assert (a, b, g) == (8, 6, 4)
    out(f"[R4] note 3.4 counterexample n=4: one-monomial move costs {a} > {b} (start); greedy {g}: confirmed")

# ---------------- module -----------------
def mons(n, d, j):
    # lex_F order: generator index first (g_1 first), then lex_E
    return [(i, S) for i in range(len(d)) for S in lex_ksets(n, j - d[i])]

def dimF(n, d, j):
    return sum(C(n, j - di) for di in d)

def B(n, d, h, j):
    # stub def-B, implemented from its text
    r = len(d)
    T = lambda N: sum(C(n, j - d[i - 1]) for i in range(N + 1, r + 1))
    assert 0 <= h <= T(0)
    if h == T(0):
        return dimF(n, d, j + 1)
    Ns = [N for N in range(1, r + 1) if T(N) <= h < T(N - 1)]
    assert len(Ns) == 1
    N = Ns[0]; a = h - T(N); kN = j - d[N - 1]
    tail = sum(C(n, j + 1 - d[i - 1]) for i in range(N + 1, r + 1))
    return tail + (macaulay_up(a, kN) if a > 0 else 0)

def mod_shadow_masks(n, d, j):
    M0 = mons(n, d, j); M1 = mons(n, d, j + 1)
    idx = {m: p for p, m in enumerate(M1)}
    masks = []
    for (i, S) in M0:
        mk = 0
        for x in range(1, n + 1):
            if x not in S:
                mk |= 1 << idx[(i, S | {x})]
        masks.append(mk)
    return M0, M1, masks

def is_initial(mask, length):
    return mask == (1 << bin(mask).count("1")) - 1

def R5_configs():
    cf = []
    for n in range(1, 5):
        for r in range(1, 4):
            for d in itertools.combinations_with_replacement(range(-1, 4), r):
                if d[0] not in (-1, 0):
                    continue
                cf.append((n, d))
    return cf

def R5(out):
    ncf = nsub = ncase = 0
    for n, d in R5_configs():
        jlo, jhi = d[0] - 2, d[-1] + n + 1
        tot = sum(1 << dimF(n, d, j) for j in range(jlo, jhi + 1))
        if tot > 2_000_000:
            continue
        ncf += 1
        for j in range(jlo, jhi + 1):
            M0, M1, masks = mod_shadow_masks(n, d, j)
            m = len(M0)
            best = [10**9] * (m + 1); best[0] = 0
            sh = [0] * (1 << m)
            for f in range(1, 1 << m):
                low = f & -f; b = low.bit_length() - 1
                sh[f] = sh[f ^ low] | masks[b]
                c = bin(f).count("1"); v = bin(sh[f]).count("1")
                if v < best[c]:
                    best[c] = v
            nsub += 1 << m
            for t in range(m + 1):
                lexmask = (1 << t) - 1
                s = sh[lexmask] if t > 0 else 0
                assert is_initial(s, len(M1)), ("Lemma5", n, d, j, t)
                assert bin(s).count("1") == best[t], ("Thm6 min", n, d, j, t)
                assert dimF(n, d, j + 1) - best[t] == B(n, d, m - t, j), ("Thm6 = B", n, d, j, t, best[t], B(n, d, m - t, j))
                ncase += 1
    out(f"[R5] module, ALL monomial subsets: {ncf} configs (n<=4, r<=3, d_1 in {{-1,0}}, sorted d in [-1,3]^r, ties), "
        f"j in [d_1-2, d_r+n+1], {ncase} (j,t) cases, {nsub} subsets: min shadow = lex_F shadow, "
        f"lex_F shadow is lex_F segment, dimF_(j+1)-min = B(h,j): OK")

# ---- arbitrary subspaces over GF(p), genuine exterior signs ----
def ext_mult(x, S):
    # e_x * e_S = sign * e_{S u x}; sign = (-1)^{#{s in S : s < x}}
    if x in S:
        return 0, None
    return (-1) ** sum(1 for s in S if s < x), S | {x}

def rank_mod_p(rows, p):
    rows = [r[:] for r in rows if any(r)]
    rk, col = 0, 0
    ncols = len(rows[0]) if rows else 0
    for col in range(ncols):
        piv = next((i for i in range(rk, len(rows)) if rows[i][col] % p), None)
        if piv is None:
            continue
        rows[rk], rows[piv] = rows[piv], rows[rk]
        inv = pow(rows[rk][col], p - 2, p)
        rows[rk] = [(v * inv) % p for v in rows[rk]]
        for i in range(len(rows)):
            if i != rk and rows[i][col] % p:
                f = rows[i][col]
                rows[i] = [(a - f * b) % p for a, b in zip(rows[i], rows[rk])]
        rk += 1
    return rk

def all_rref(m, t, p):
    # all t x m RREF matrices over GF(p) (each t-dim subspace exactly once)
    for piv in itertools.combinations(range(m), t):
        free = [(r, c) for r in range(t) for c in range(m) if c > piv[r] and c not in piv]
        for vals in itertools.product(range(p), repeat=len(free)):
            M = [[0] * m for _ in range(t)]
            for r in range(t):
                M[r][piv[r]] = 1
            for (r, c), v in zip(free, vals):
                M[r][c] = v
            yield M

def R6(out):
    tot = 0; lines = []
    cfgs = []
    for n in range(1, 4):
        for d in [(0,), (0, 0), (0, 1), (0, 2), (-1, 0), (0, 3)]:
            cfgs.append((2, n, d))
    cfgs += [(3, 2, (0, 0)), (3, 2, (0, 1)), (3, 3, (0,)), (3, 3, (0, 1)), (3, 2, (0, 0, 1)), (3, 3, (0, 0))]
    for p, n, d in cfgs:
        for j in range(d[0], d[-1] + n):
            M0 = mons(n, d, j); M1 = mons(n, d, j + 1)
            m = len(M0)
            if m == 0 or len(M1) == 0:
                continue
            if (p == 2 and m > 6) or (p == 3 and m > 5):
                continue
            idx = {mm: q for q, mm in enumerate(M1)}
            # matrix of e_x : F_j -> F_{j+1} for each x
            ops = []
            for x in range(1, n + 1):
                op = []
                for (i, S) in M0:
                    sg, T = ext_mult(x, S)
                    col = [0] * len(M1)
                    if T is not None:
                        col[idx[(i, T)]] = sg % p
                    op.append(col)
                ops.append(op)
            _, _, masks = mod_shadow_masks(n, d, j)
            for t in range(0, m + 1):
                best_mon = min(bin(eval_or(masks, c)).count("1") for c in itertools.combinations(range(m), t)) if t else 0
                best_sub = 10**9; cnt = 0
                for V in all_rref(m, t, p):
                    rows = []
                    for v in V:
                        for op in ops:
                            w = [0] * len(M1)
                            for q, coef in enumerate(v):
                                if coef:
                                    for c2 in range(len(M1)):
                                        w[c2] = (w[c2] + coef * op[q][c2]) % p
                            rows.append(w)
                    rk = rank_mod_p(rows, p) if rows else 0
                    best_sub = min(best_sub, rk); cnt += 1
                if t == 0:
                    best_sub = 0
                assert best_sub == best_mon, ("Lemma1", p, n, d, j, t, best_sub, best_mon)
                tot += cnt
    out(f"[R6] ALL subspaces over GF(2) (dim F_j<=6) and GF(3) (dim F_j<=5), genuine exterior signs, "
        f"{len(cfgs)} configs, {tot} subspaces: min dim E_1V over subspaces = min over monomial subsets: OK")

def eval_or(masks, c):
    s = 0
    for i in c:
        s |= masks[i]
    return s

# ---- Theorem 8 ----
def complexes_fvectors(n):
    # all simplicial complexes (down-closed families) on [n], incl. void (empty family) and {emptyset}
    sets = [frozenset(c) for k in range(n + 1) for c in itertools.combinations(range(1, n + 1), k)]
    # enumerate down-sets via antichains of maximal faces: brute force over families for n<=4 (2^16)
    res = set()
    allS = sets
    pos = {S: i for i, S in enumerate(allS)}
    for f in range(1 << len(allS)):
        fam = [allS[i] for i in range(len(allS)) if f >> i & 1]
        ok = True
        for S in fam:
            for x in S:
                if not (f >> pos[S - {x}] & 1):
                    ok = False; break
            if not ok:
                break
        if ok:
            fv = [0] * (n + 1)
            for S in fam:
                fv[len(S)] += 1
            res.add(tuple(fv))
    return res

def R7(out, fv):
    lines = []
    cfgs = [(1, (0, 0)), (1, (0, 0, 0)), (1, (0, 1)), (1, (-3, 0, 0)), (2, (0, 0)), (2, (0, 1)), (2, (-2, 1)),
            (2, (0, 0, 0)), (2, (0, 0, 1)), (2, (0, 1, 1)), (2, (-1, 0, 2)), (3, (0, 0)), (3, (0, 1)), (3, (0, 3)),
            (3, (0, 4)), (3, (0, 0, 0)), (3, (0, 0, 1)), (3, (0, 1, 1)), (3, (-1, -1, 1)), (3, (0, 2, 2)),
            (4, (0, 0)), (4, (0, 1)), (4, (-1, 1)), (4, (0, 3)), (4, (0, 0, 0)), (4, (0, 0, 1)), (4, (0, 1, 2))]
    for n, d in cfgs:
        lo, hi = d[0], d[-1] + n
        L = hi - lo + 1
        ach = {tuple([0] * L)}
        for di in d:
            new = set()
            for h in ach:
                for f in fv[n]:
                    hh = list(h)
                    for k, v in enumerate(f):
                        hh[di + k - lo] += v
                    new.add(tuple(hh))
            ach = new
        # B-condition sequences
        cand = set()
        def rec(j, prev, acc):
            if j > hi:
                cand.add(tuple(acc)); return
            ub = B(n, d, prev, j - 1)
            for v in range(0, ub + 1):
                rec(j + 1, v, acc + [v])
        rec(lo, 0, [])
        fp = len(cand - ach); fn = len(ach - cand)
        lines.append(f"    n={n} d={d} achievable={len(ach)} B-sequences={len(cand)} fp={fp} fn={fn}")
        assert fp == 0 and fn == 0, (n, d)
    out(f"[R7] Theorem 8 (b) <=> achievable by monomial M (f-vector sumset, own enumeration of complexes): "
        f"{len(cfgs)} configs, 0 fp / 0 fn")
    for l in lines:
        out(l)

def R8(out):
    cnt = 0
    for n in range(1, 6):
        for r in range(1, 4):
            for d in itertools.combinations_with_replacement(range(-2, 4), r):
                for s in range(d[0], d[-1] + n + 1):
                    if s - 1 >= d[0] - 1:
                        r0 = sum(1 for x in d if x == s); r1 = sum(1 for x in d if x == s + 1)
                        if dimF(n, d, s - 1) >= 0:
                            assert B(n, d, 0, s - 1) == r0, (n, d, s)
                        for hs in range(1, r0 + 1):
                            if hs <= dimF(n, d, s):
                                assert B(n, d, hs, s) == n * hs + r1, (n, d, s, hs)
                        cnt += 1
    out(f"[R8] Corollary 9 (B(0,s-1)=r0, B(h_s,s)=n h_s + r1), n<=5, r<=3, d in [-2,3]^r, all s: {cnt} OK")

def R9(out):
    cnt = 0
    for n in range(0, 8):
        for r in range(1, 4):
            for ks in itertools.combinations_with_replacement(range(-2, n + 2), r):
                ks = tuple(sorted(ks, reverse=True))
                caps = [C(n, k) for k in ks]
                cost = lambda i, t: sigma_actual(n, ks[i], t) if 0 <= ks[i] <= n else 0
                for T in range(sum(caps) + 1):
                    g = []; rem = T
                    for c in caps:
                        g.append(min(rem, c)); rem -= g[-1]
                    gc = sum(cost(i, g[i]) for i in range(r))
                    best = min(sum(cost(i, t[i]) for i in range(r))
                               for t in itertools.product(*[range(c + 1) for c in caps]) if sum(t) == T)
                    assert gc == best, (n, ks, T)
                    cnt += 1
    out(f"[R9] Prop 4: greedy (largest exterior degree first) = min over all splits, actual sigma, "
        f"n<=7, r<=3, exterior degrees in [-2,n+1]: {cnt} (config,T) OK")

def main():
    lines = []
    def out(s):
        print(s); sys.stdout.flush()
    out(f"review_module_kk_check.py  run {time.strftime('%Y-%m-%d %H:%M')}")
    for f in (R1, R2, R3, R4, R5, R6, R8, R9):
        t0 = time.time(); f(out); out(f"    ({time.time()-t0:.1f}s)")
    t0 = time.time()
    fv = {n: complexes_fvectors(n) for n in range(1, 5)}
    out(f"    f-vector sets: " + ", ".join(f"n={n}: {len(fv[n])}" for n in fv))
    R7(out, fv); out(f"    ({time.time()-t0:.1f}s)")
    out("ALL CHECKS PASSED")

if __name__ == "__main__":
    main()
