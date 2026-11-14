# 2026-11-09 - Claude-Code (jts-mini) subagent: Kupreyeva's limit at rank one and rank r, exactly.
#   Counts ff-vectors and lattice points of the truncated Kozlov polytope Koz^(p)(n;d) (p vertices, every
#   summand truncated at its own degree n) for growing p, and compares with the predicted limits.
#   Note: working-notes/kupreyeva-limit-proof-2026-11-09.org.  Plain Python 3, exact integers/Fractions.
"""Kupreyeva-type limits, exact counts.

Setting (truncation n fixed, p vertices, p -> oo).  c^(p) = (C(p,0),...,C(p,n)) is a full leg vector,
log-concave, so Theorem thm-chained of Part III applies to RA(c^(p); d):
  * lattice points of RA(c^(p); d)  <->  chained tuples of lattice points of angle(c^(p))   (cor-additivity)
  * ff-vectors FF^(p)(n; d) = sum_i shift^{d_i} S_n^(p)  <->  chained tuples of truncated f-vectors
    (Part II, Theorem thm-asymptotics-p-proper, formula eq:proper-p-product; also Lemma T of the note).
Both are sums over "types" (tp_i, indeg_i) of products of class counts M_X[tau][iota], X = L or S.

Independent routes used here:
  S side : (a) Linusson's recursion for E^p(m,k) [Linusson 1999, Thm 5.2]; (b) direct sums of Macaulay
           pseudo-powers (Kruskal--Katona), n <= 4; (c) brute force sumsets, small p.
  L side : (a) floor sums of the LYM chain; (b) brute force enumeration, small p.
Limits: the type formula of the note (sum over degree-maximising types), the group closed form, the
heuristic product prod q(n, delta_i), and q_n^r.
"""
import sys
import time
from fractions import Fraction as Fr
from itertools import product
from math import comb, factorial


# ----------------------------------------------------------------------------------------------
# arithmetic helpers
# ----------------------------------------------------------------------------------------------
def floor_sum(n, m, a, b):
    """sum_{i=0}^{n-1} floor((a*i+b)/m) for n >= 0, m >= 1, a, b >= 0 (AtCoder Library algorithm)."""
    ans = 0
    while True:
        if a >= m:
            ans += n * (n - 1) // 2 * (a // m)
            a %= m
        if b >= m:
            ans += n * (b // m)
            b %= m
        y_max = a * n + b
        if y_max < m:
            break
        n, b = y_max // m, y_max % m
        m, a = a, m
    return ans


def top_binom(x, k):
    """largest a with C(a,k) <= x (x >= 1, k >= 1)."""
    lo, hi = k, k
    while comb(hi, k) <= x:
        hi *= 2
    while hi - lo > 1:          # invariant C(lo,k) <= x < C(hi,k)
        mid = (lo + hi) // 2
        if comb(mid, k) <= x:
            lo = mid
        else:
            hi = mid
    return lo


def pp(x, k):
    """Macaulay pseudo-power x^{(k)}: x = sum_j C(a_j, j) (k-cascade) -> sum_j C(a_j, j+1)."""
    res = 0
    while x > 0 and k >= 1:
        a = top_binom(x, k)
        res += comb(a, k + 1)
        x -= comb(a, k)
        k -= 1
    return res


class PrefixPP:
    """A(k, m) = sum_{x=0}^{m-1} x^{(k)}, by the cascade recursion; Afull[k][a] = A(k, C(a,k))."""

    def __init__(self, kmax, amax):
        self.Afull = {1: [comb(a, 3) for a in range(amax + 2)]}    # A(1, C(a,1)) = C(a,3)
        for k in range(2, kmax + 1):
            arr = [0] * (amax + 2)
            # blocks [C(b,k), C(b+1,k)) for b = k-1, ..., a-1; arr[a] = A(k, C(a,k))
            for a in range(amax + 1):
                b = a
                arr[a + 1] = arr[a] + (comb(b, k - 1) * comb(b, k + 1) + self.Afull[k - 1][b]
                                       if b >= k - 1 else 0)
            self.Afull[k] = arr

    def A(self, k, m):
        if m <= 0:
            return 0
        if k == 1:
            return comb(m, 3)
        a = top_binom(m, k)
        rest = m - comb(a, k)
        return self.Afull[k][a] + rest * comb(a, k + 1) + self.A(k - 1, rest)


# ----------------------------------------------------------------------------------------------
# S side, route (a): Linusson's recursion
# ----------------------------------------------------------------------------------------------
def linusson_E(P, n):
    """dict E[(m,k)] = E^P(m,k) for -1 <= k <= m <= n (needs P >= n)."""
    E = {(-1, -1): 1, (0, -1): 1, (0, 0): 1}              # p' = 0
    for q in range(1, P + 1):
        new = {}
        for m in range(-1, min(n, q) + 1):
            for k in range(-1, m + 1):
                if k == -1 or k == m:
                    v = 1
                elif m == q:
                    v = new[(q - 1, k)]
                else:
                    v = sum(E[(m, i)] * E[(i - 1, k - 1)] for i in range(k, m + 1))
                new[(m, k)] = v
        E = new
    return E


def GS_linusson(E, a, b):
    """#{s in S_n^(p): fl(s) >= a, tp(s) <= b}, 1 <= a."""
    if b < a:
        return 0
    return sum(E[(b, k)] for k in range(a, b + 1))


# ----------------------------------------------------------------------------------------------
# S side, route (b): direct Kruskal--Katona sums;  L side: floor sums
# ----------------------------------------------------------------------------------------------
def GS_direct(p, a, b, PP):
    """same count, from x_{k+1} <= x_k^{(k)} on the free block a+1..b (block length <= 3)."""
    if b < a:
        return 0
    ln, k = b - a, a + 1
    C = comb(p, k)
    if ln == 0:
        return 1
    if ln == 1:
        return C + 1
    if ln == 2:
        return PP.A(k, C + 1) + C + 1
    if ln == 3:
        tot = 0
        for x in range(C + 1):
            y = pp(x, k)
            tot += PP.A(k + 1, y + 1) + y + 1
        return tot
    raise ValueError("block too long for the direct route")


def GL(p, a, b):
    """#{lattice points x of angle(c^(p)): fl >= a, tp <= b}: integer chains on a+1..b with
    0 <= x_{a+1} <= C(p,a+1), (j+1) x_{j+1} <= (p-j) x_j.  Block length <= 4."""
    if b < a:
        return 0
    ln, k = b - a, a + 1
    C = comb(p, k)
    if ln == 0:
        return 1
    if ln == 1:
        return C + 1
    if ln == 2:      # sum_{x=0}^{C} (floor((p-k)x/(k+1)) + 1)
        return floor_sum(C + 1, k + 1, p - k, 0) + C + 1
    if ln == 3:
        tot = 0
        for x in range(C + 1):
            Y = (p - k) * x // (k + 1)
            tot += floor_sum(Y + 1, k + 2, p - k - 1, 0) + Y + 1
        return tot
    if ln == 4:
        C2 = comb(p, k + 1)
        pref = [0] * (C2 + 2)          # pref[y+1] = sum_{y' <= y} W(y')
        for y in range(C2 + 1):
            Z = (p - k - 1) * y // (k + 2)
            pref[y + 1] = pref[y] + floor_sum(Z + 1, k + 3, p - k - 2, 0) + Z + 1
        tot = 0
        for x in range(C + 1):
            tot += pref[(p - k) * x // (k + 1) + 1]
        return tot
    raise ValueError("block too long")


def class_counts(G, n):
    """M[(tau, iota)] = #{tp = tau, indeg = iota}, 1 <= tau <= n, 2 <= iota <= tau+1, from
    G(a,b) = #{fl >= a, tp <= b} by inclusion-exclusion (fl = iota-1)."""
    memo = {}

    def Gm(a, b):
        if (a, b) not in memo:
            memo[(a, b)] = G(a, b)
        return memo[(a, b)]
    M = {}
    for tau in range(1, n + 1):
        for iota in range(2, tau + 2):
            a = iota - 1
            M[(tau, iota)] = Gm(a, tau) - Gm(a + 1, tau) - Gm(a, tau - 1) + Gm(a + 1, tau - 1)
    return M


def chained_count(M, n, d):
    """number of chained tuples: tp_{i-1} < indeg_i + delta_i."""
    v = {tau: sum(M[(tau, io)] for io in range(2, tau + 2)) for tau in range(1, n + 1)}
    for i in range(1, len(d)):
        delta = d[i] - d[i - 1]
        w = {}
        for t2 in range(1, n + 1):
            w[t2] = sum(v[t1] * sum(M[(t2, io)] for io in range(2, t2 + 2) if io + delta > t1)
                        for t1 in range(1, n + 1))
        v = w
    return sum(v.values())


# ----------------------------------------------------------------------------------------------
# brute force (small p)
# ----------------------------------------------------------------------------------------------
def lattice_points(p, n):
    pts = []

    def rec(prefix, k):
        if k > n:
            pts.append(tuple(prefix))
            return
        hi = comb(p, 2) if k == 2 else (p - k + 1) * prefix[-1] // k
        for x in range(hi + 1):
            rec(prefix + [x], k + 1)
    rec([1, p], 2)
    return pts


def is_fvec(v):
    return all(v[k + 1] <= pp(v[k], k) for k in range(1, len(v) - 1))


def sumset(pts, d, n):
    N = n + d[-1]
    cur = {tuple([0] * (N + 1))}
    for di in d:
        nxt = set()
        for s in cur:
            for q in pts:
                t = list(s)
                for m, val in enumerate(q):
                    t[m + di] += val
                nxt.add(tuple(t))
        cur = nxt
    return cur


# ----------------------------------------------------------------------------------------------
# limits
# ----------------------------------------------------------------------------------------------
def rho(a, b):
    """vol{1 >= mu_a >= 0, 0 <= mu_{k+1} <= mu_k^{(k+1)/k} (a <= k < b)}; 1 for an empty block."""
    if b < a:
        return Fr(1)
    v = Fr(1)
    for k in range(a, b):
        v *= Fr(2 * k, (b - k + 1) * (b + k))
    return v


def q_n(n):
    return rho(2, n) * factorial(n - 1)


def q_nd(n, delta):
    """q(n, delta): delta! * rho(n-delta+1, n), delta capped at n-1."""
    delta = min(delta, n - 1)
    return rho(n - delta + 1, n) * factorial(delta)


def limit_types(n, d):
    """sum over degree-maximising chained types of w * prod c_S / same with c_L."""
    classes = [(tau, io) for tau in range(1, n + 1) for io in range(2, tau + 2)]
    best, numS, numL = -1, Fr(0), Fr(0)
    for t in product(classes, repeat=len(d)):
        ok = all(t[i - 1][0] < t[i][1] + d[i] - d[i - 1] for i in range(1, len(d)))
        if not ok:
            continue
        deg = sum(sum(range(io, tau + 1)) for tau, io in t)
        w, cS, cL = Fr(1), Fr(1), Fr(1)
        for tau, io in t:
            for k in range(io, tau + 1):
                w /= factorial(k)
            cS *= rho(io, tau)
            cL /= factorial(tau - io + 1)
        if deg > best:
            best, numS, numL = deg, Fr(0), Fr(0)
        if deg == best:
            numS += w * cS
            numL += w * cL
    return numS / numL, best


def Phi(a, n, m):
    """sum over a-1 = t_0 <= t_1 <= ... <= t_m = n of prod rho(t_{l-1}+1, t_l)."""
    tot = Fr(0)

    def rec(prev, l, acc):
        nonlocal tot
        if l == m:
            if prev == n:
                tot += acc
            return
        hi = n if l < m - 1 else n
        lo = prev if l < m - 1 else n
        for t in range(lo, hi + 1):
            rec(t, l + 1, acc * rho(prev + 1, t))
    rec(a - 1, 0, Fr(1))
    return tot


def limit_groups(n, d):
    groups = []                      # (shift, size)
    for x in d:
        if groups and groups[-1][0] == x:
            groups[-1][1] += 1
        else:
            groups.append([x, 1])
    lim = Fr(1)
    for j, (D, m) in enumerate(groups):
        a = 2 if j == 0 else max(2, n - (D - groups[j - 1][0]) + 1)
        L = n - a + 1
        lim *= Phi(a, n, m) * factorial(L) / Fr(m) ** L
    return lim


def linusson_lc(m, k):
    """Linusson's formula (13): leading coefficient of E^p(m,k) in p."""
    N = comb(m + 1, 2)
    num = 1
    for i in range(k, m - 1):
        num *= comb(N - comb(i + 1, 2) - 1, i)
    return Fr(num, factorial(N - comb(k + 1, 2)))


# ----------------------------------------------------------------------------------------------
def fmt(x):
    return f"{float(x):.6f}"


def main():
    t0 = time.time()
    out = print
    out("Kupreyeva-type limits: exact counts (code/oneoff/kupreyeva_limit_rank_r.py, 2026-11-09)")
    out("=" * 100)

    # ---- 0. unit checks -------------------------------------------------------------------
    out("\n[0] unit checks")
    bad = 0
    for nn in range(0, 30):
        for m in range(1, 8):
            for a in range(0, 9):
                for b in range(0, 9):
                    bad += floor_sum(nn, m, a, b) != sum((a * i + b) // m for i in range(nn))
    out(f"  floor_sum vs brute force (n<30, m<8, a,b<9): mismatches {bad}")
    PPt = PrefixPP(5, 40)
    bad = 0
    for k in range(1, 5):
        acc = 0
        for m in range(0, 600):
            bad += PPt.A(k, m) != acc
            acc += pp(m, k)
    out(f"  prefix sums of pseudo-powers vs running sums (k<=4, m<600): mismatches {bad}")
    out(f"  examples: 20^(4) = {pp(20, 4)} (Kupreyeva Ex. 3.4 says 7); 5^(2) = {pp(5, 2)} (Part III says 2)")
    bad = 0
    for P in range(3, 25):
        E = linusson_E(P, 3)
        F2 = sum(E[(2, k)] for k in range(-1, 3))
        F3 = sum(E[(3, k)] for k in range(-1, 4))
        bad += F2 != comb(P + 2, 3) - comb(P + 2, 2) + 2 * comb(P + 2, 1) - 1
        bad += F3 != 4 * comb(P + 2, 6) + comb(P + 2, 4) + comb(P + 2, 1)
    out(f"  Linusson recursion vs his closed forms F^p(2), F^p(3), 3<=p<25: mismatches {bad}")

    # ---- 1. S side two routes; brute force sumsets vs chained counts --------------------------
    out("\n[1] cross-checks of the class counts")
    bad = 0
    for n in (3, 4):
        for P in ([n, n + 1, n + 2, 7, 10, 15, 25] if n == 3 else [n, n + 1, 6, 8, 12]):
            PPx = PrefixPP(n + 1, P + 2)
            E = linusson_E(P, n)
            for a in range(1, n + 1):
                for b in range(a, n + 1):
                    if GS_linusson(E, a, b) != GS_direct(P, a, b, PPx):
                        bad += 1
                        out(f"   MISMATCH S n={n} p={P} block ({a},{b})")
    out(f"  S class counts, Linusson recursion vs direct Kruskal--Katona sums (n=3,4): mismatches {bad}")
    bad = 0
    tests = [(3, P, d) for P in (3, 4, 5, 6, 7) for d in [(0,), (0, 0), (0, 1), (0, 2), (0, 3), (0, 0, 1), (0, 1, 2)]]
    tests += [(4, P, d) for P in (4, 5) for d in [(0,), (0, 0), (0, 1), (0, 2), (0, 3)]]
    tests += [(4, 6, d) for d in [(0,), (0, 1), (0, 3)]]
    for n, P, d in tests:
        L = lattice_points(P, n)
        S = [v for v in L if is_fvec(v)]
        E = linusson_E(P, n)
        ML = class_counts(lambda a, b: GL(P, a, b), n)
        MS = class_counts(lambda a, b: GS_linusson(E, a, b), n)
        nL, nS = len(sumset(L, d, n)), len(sumset(S, d, n))
        cL, cS = chained_count(ML, n, d), chained_count(MS, n, d)
        ok = (nL == cL and nS == cS)
        bad += not ok
        if not ok or P == n:
            out(f"   n={n} p={P} d={d}: lattice {nL} (sumset) {cL} (chained)   ff {nS} (sumset) {cS} (chained)  {'ok' if ok else 'MISMATCH'}")
    out(f"  brute-force sumsets vs chained-type counts, {len(tests)} cases: mismatches {bad}")
    out("  (at p = n these are Part III's numbers: Koz(4): 20/16; Koz(4;0,0): 81/69; (0,1): 214/162;")
    out("   (0,2): 386/246; (0,3): 400/256.)")

    # ---- 2. identities -----------------------------------------------------------------------
    out("\n[2] identities for the limits")
    bad = 0
    for n in range(2, 31):
        kup = Fr(factorial(n + 1), 2 * __import__('math').prod(range(1, 2 * n, 2)))
        bad += q_n(n) != kup
        bad += linusson_lc(n, 1) * factorial(n - 1) * __import__('math').prod(factorial(k) for k in range(2, n + 1)) != kup
        for kap in range(1, n):
            delta = n - kap
            lhs = linusson_lc(n, kap) * factorial(delta) * __import__('math').prod(factorial(k) for k in range(kap + 1, n + 1))
            bad += lhs != q_nd(n, delta)
            closed = Fr(2 ** (delta - 1) * factorial(n - 1) * factorial(2 * n - delta),
                        factorial(n - delta) * factorial(2 * n - 1))
            bad += closed != q_nd(n, delta)
    out("  for 2 <= n <= 30, 1 <= delta <= n-1:  q_n = (n-1)! vol R_n = (n+1)!/(2(2n-1)!!)")
    out("    = L(n,1) (n-1)! prod_{k=2}^n k!   [Linusson's leading coefficient],")
    out("  q(n,delta) = delta! rho(n-delta+1,n) = L(n,n-delta) delta! prod_{k>n-delta} k!")
    out(f"             = 2^(delta-1) (n-1)! (2n-delta)! / ((n-delta)! (2n-1)!) :  mismatches {bad}")

    # ---- 3. rank one -------------------------------------------------------------------------
    out("\n[3] rank one: fraction |S_n^(p)| / #lattice points of angle(c^(p)), against q_n")
    plist = {3: [3, 5, 10, 30, 100, 300, 1000, 3000, 10000, 30000],
             4: [4, 5, 10, 20, 50, 100, 200, 500, 1000, 2000],
             5: [5, 6, 10, 20, 40, 80, 120]}
    if len(sys.argv) > 1 and sys.argv[1] == "quick":
        plist = {3: [3, 10, 100], 4: [4, 10, 50], 5: [5, 10]}
    cache = {}
    for n in (3, 4, 5):
        out(f"  n = {n}, q_n = {q_n(n)} = {fmt(q_n(n))}")
        out(f"   {'p':>6} {'#S':>28} {'#L':>28} {'fraction':>10} {'p*(frac-q_n)':>14}")
        for P in plist[n]:
            E = linusson_E(P, n)
            ML = class_counts(lambda a, b: GL(P, a, b), n)
            MS = class_counts(lambda a, b: GS_linusson(E, a, b), n)
            cache[(n, P)] = (ML, MS)
            cL, cS = chained_count(ML, n, (0,)), chained_count(MS, n, (0,))
            f = Fr(cS, cL)
            out(f"   {P:>6} {cS:>28} {cL:>28} {fmt(f):>10} {float(P * (f - q_n(n))):>14.4f}")

    # ---- 4. rank r ---------------------------------------------------------------------------
    out("\n[4] rank r: fraction |FF^(p)(n;d)| / #lattice points of RA(c^(p);d)")
    out("    limit = type formula (sum over degree-maximising chained types); 'groups' = closed form;")
    out("    'prod q' = heuristic prod_i q(n, delta_i) with delta_1 = n-1; q_n^r as in the current Part III.")
    shifts = {3: [(0, 0), (0, 1), (0, 2), (0, 0, 0), (0, 0, 1), (0, 1, 1), (0, 1, 2), (0, 0, 0, 0)],
              4: [(0, 0), (0, 1), (0, 2), (0, 3), (0, 0, 0), (0, 1, 2), (0, 0, 2)]}
    for n in (3, 4):
        for d in shifts[n]:
            lim, deg = limit_types(n, d)
            limg = limit_groups(n, d)
            heur = q_n(n)
            for i in range(1, len(d)):
                heur *= q_nd(n, d[i] - d[i - 1]) if d[i] > d[i - 1] else Fr(0)
            heur_s = fmt(heur) if all(d[i] > d[i - 1] for i in range(1, len(d))) else "n/a"
            out(f"  n={n} d={d}: limit {lim} = {fmt(lim)} (groups: {'same' if limg == lim else 'DIFFERENT ' + str(limg)}),"
                f" prod q = {heur_s}, q_n^r = {fmt(q_n(n) ** len(d))}; degree {deg}")
            out(f"   {'p':>6} {'fraction':>10} {'frac-limit':>12} {'p*(frac-limit)':>15}")
            for P in plist[n]:
                ML, MS = cache[(n, P)]
                f = Fr(chained_count(MS, n, d), chained_count(ML, n, d))
                out(f"   {P:>6} {fmt(f):>10} {float(f - lim):>12.6f} {float(P * (f - lim)):>15.4f}")
    # ---- 5. equal shifts: Minkowski sum R_n + ... + R_n as a sawtooth region -------------------
    out("\n[5] equal shifts d = 0^r: volume of the sawtooth region {r >= nu_2, 0 <= nu_{k+1} <= G_k(nu_k)},")
    out("    G_k(v) = floor(v) + frac(v)^((k+1)/k), by nested numerical quadrature (numpy, trapezoid),")
    out("    against Phi(2,n;r) = sum over staircases of prod rho (exact).  The note shows the sawtooth")
    out("    region is the Minkowski sum R_n + ... + R_n and also the limit region of the ff-vectors.")
    try:
        import numpy as np
        for n, r in [(3, 2), (3, 3), (4, 2), (4, 3), (5, 2), (5, 3)]:
            M = 400000
            grid = np.linspace(0.0, float(r), M * r + 1)

            def G(k, v):
                fl = np.floor(v)
                fl = np.minimum(fl, r - 1)          # v = r belongs to the top tooth
                return fl + (v - fl) ** ((k + 1) / k)
            F = np.ones_like(grid)                  # F_n = 1
            for k in range(n - 1, 1, -1):           # F_k(v) = int_0^{G_k(v)} F_{k+1}
                cum = np.concatenate(([0.0], np.cumsum((F[1:] + F[:-1]) / 2 * np.diff(grid))))
                F = np.interp(G(k, grid), grid, cum)
            vol = float(np.sum((F[1:] + F[:-1]) / 2 * np.diff(grid)))
            exact = Phi(2, n, r)
            out(f"  n={n} r={r}: quadrature {vol:.7f}   Phi = {exact} = {float(exact):.7f}   diff {vol - float(exact):.1e}")
    except ImportError:
        out("  numpy not available; skipped")

    out(f"\nelapsed {time.time() - t0:.1f} s")


if __name__ == "__main__":
    main()
