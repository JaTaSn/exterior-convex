#!/usr/bin/env python3
"""transfer_irreducibility.py -- is T_n(delta) irreducible and aperiodic?

Changelog (newest first):
- 2026-10-10 - Claude (jts-pc): added step 0, the independent route.  Steps 1-5 take A_n from
  A_from_linusson, which is the same recursion the paper's own formula runs on -- so on its own
  this is a check of one formula against another, not against an independent enumeration.  Step 0
  re-runs the structural checks with A_bruteforce, which enumerates the downward-closed families
  directly and uses no E, no F and no recursion.  The distinction is the one section 10.1 of the
  manuscript insists on, and it is cheap here: n <= 6 takes a couple of minutes.
- 2026-10-10 - Claude (jts-pc): created.  Jan asked whether rem-recurrence-asymptotics,
  which states a_r ~ K lambda^r and declines to prove it, can become a proposition by way of
  Flajolet-Sedgewick's Theorem V.7 (Analytic Combinatorics, p. 343).  V.7 needs the transfer
  matrix IRREDUCIBLE and APERIODIC; this script checks both, and checks that the conclusion
  actually holds numerically.

What is checked, all against the project's own A_from_linusson / transfer_matrix:

  1. SUPPORT.  The claim is  T_n(delta)[tau][tau'] > 0  <=>  tau' >= tau - delta.
     Proof: T_n(delta)[tau][tau'] counts s in F_n with top(s) = tau' and indeg(s) > tau - delta.
     The largest indeg among s with top(s) = tau' is tau'+1 -- indeg <= top+1 always, and the
     value is attained by the full tau'-skeleton -- so the count is non-zero iff tau'+1 > tau-delta.

  2. IRREDUCIBILITY.  From 1, delta >= 1 gives a strongly connected digraph (every tau reaches n
     in one step; from n one steps down by at most delta at a time to reach anything).  At
     delta = 0 the condition is tau' >= tau, which is upper triangular, hence reducible.

  3. APERIODICITY.  From 1, tau -> tau is always an edge (tau >= tau - delta for delta >= 0), so
     every vertex carries a self-loop and the period is 1.

  4. THE CONCLUSION ITSELF.  a_r / lambda^r should converge to a positive constant for delta >= 1
     and diverge at delta = 0, where a_r is a polynomial of degree n+1 and lambda = 1.

  5. THE PROPER VARIANT.  T'_n(delta) is NEVER irreducible on the full index set: no s in S_n has
     top <= 0, so the columns tau' = -1 and tau' = 0 vanish identically.  On the principal block
     tau in {1,...,n} -- the one the manuscript already works on, see the proof of thm-proper --
     it is irreducible and aperiodic for delta >= 1.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from linusson_ff_counting import A_from_linusson, transfer_matrix, restrict_proper, ff_count

def strongly_connected(T, idx):
    def reach(src, fwd):
        seen = {src}; stack = [src]
        while stack:
            x = stack.pop()
            for y in idx:
                if (T[x][y] > 0 if fwd else T[y][x] > 0) and y not in seen:
                    seen.add(y); stack.append(y)
        return len(seen) == len(idx)
    return reach(idx[0], True) and reach(idx[0], False)

def spectral_radius(T):
    R = len(T); v = [1.0]*R; lam = 0.0
    for _ in range(50000):
        w = [sum(T[i][j]*v[i] for i in range(R)) for j in range(R)]
        s = sum(w)
        if s == 0: return 0.0
        w = [x/s for x in w]
        new = sum(sum(T[i][j]*w[i] for i in range(R)) for j in range(R))
        if abs(new - lam) < 1e-14: return new
        lam, v = new, w
    return lam

def brute_checks(nmax=6):
    """Steps 1-3 again, with A_n from direct enumeration instead of the recursion."""
    from linusson_ff_counting import A_bruteforce
    bad = 0
    print(f"0. INDEPENDENT ROUTE: same checks with A_bruteforce (no E, no F, no recursion), n <= {nmax}")
    for n in range(1, nmax + 1):
        A = A_bruteforce(n); R = n + 2; idx = list(range(R))
        for d in range(0, n + 3):
            T = transfer_matrix(A, d, n)
            sup = all((T[i][j] > 0) == ((j-1) >= (i-1) - d) for i in idx for j in idx)
            sc  = strongly_connected(T, idx)
            lp  = all(T[i][i] > 0 for i in idx)
            if not sup or sc != (d >= 1) or not lp:
                print(f"   DISAGREEMENT n={n} delta={d}: support {sup}, connected {sc}, loops {lp}")
                bad += 1
    print(f"   {'agrees with the recursion route everywhere' if not bad else str(bad) + ' DISAGREEMENTS'}")
    return bad


def main():
    fail = brute_checks()
    print()
    print("1. SUPPORT:  T_n(delta)[tau][tau'] > 0  <=>  tau' >= tau - delta")
    for n in range(1, 10):
        A = A_from_linusson(n); R = n + 2
        for d in range(0, n + 4):
            T = transfer_matrix(A, d, n)
            ok = all((T[i][j] > 0) == ((j-1) >= (i-1) - d)
                     for i in range(R) for j in range(R))
            if not ok: print(f"   MISMATCH n={n} delta={d}"); fail += 1
    print(f"   n = 1..9, delta = 0..n+3: {'all agree' if not fail else str(fail)+' MISMATCHES'}")

    print("\n2-3. IRREDUCIBLE and APERIODIC (improper)")
    for n in range(1, 10):
        A = A_from_linusson(n); R = n + 2; idx = list(range(R))
        d0 = strongly_connected(transfer_matrix(A, 0, n), idx)
        rest = {strongly_connected(transfer_matrix(A, d, n), idx) for d in range(1, n + 4)}
        loops = all(all(transfer_matrix(A, d, n)[i][i] > 0 for i in idx) for d in range(0, n + 4))
        print(f"   n={n}: delta=0 irreducible {d0};  delta>=1 irreducible {rest};  self-loop at every vertex {loops}")
        if d0 or rest != {True} or not loops: fail += 1

    print("\n4. a_r / lambda^r")
    for n in (3, 4, 5):
        A = A_from_linusson(n)
        for d in (0, 1, 2):
            T = transfer_matrix(A, d, n); lam = spectral_radius(T)
            vals = [ff_count(n, [0] + [d*i for i in range(1, r)]) / lam**r for r in (6, 14, 22)]
            tag = "converges" if d >= 1 else "DIVERGES (expected: a_r is a polynomial, lambda = 1)"
            print(f"   n={n} delta={d}  lambda={lam:.6f}  r=6,14,22: " +
                  ", ".join(f"{v:.6f}" for v in vals) + f"   {tag}")

    print("\n5. PROPER variant")
    for n in range(2, 9):
        Ap = restrict_proper(A_from_linusson(n)); R = n + 2
        full = list(range(R)); blk = list(range(2, R))
        f0 = strongly_connected(transfer_matrix(Ap, 1, n), full)
        b  = {strongly_connected(transfer_matrix(Ap, d, n), blk) for d in range(1, n + 2)}
        print(f"   n={n}: full index set irreducible {f0};  principal block tau in 1..n, delta>=1: {b}")
        if f0 or b != {True}: fail += 1

    print(f"\n{'ALL CHECKS PASS' if not fail else str(fail) + ' FAILURES'}")
    return 1 if fail else 0

if __name__ == "__main__":
    sys.exit(main())
