#!/usr/bin/env python3
"""rem_digit_characterisation_check.py

Changelog (reverse chronological):
  2026-10-08  Claude: created (review-article2-draft7-2026-10-08, item 68).
              Independent exhaustive check of the digit characterisation of
              Remark rem-delta0-structure (article 2, "Rem 33" in draft 7),
              equations eq:delta0-digits, eq:delta0-characterisation and
              eq:delta0-clamp-digits.  The remark claims:
                (a) for d = (0,...,0) (r components, improper variant, all
                    components in F_n), x lies in FF(n;0^r) iff the digit
                    sequence q (x(j) = q_j binom(n,j) + f_j, 0 <= f_j <
                    binom(n,j)) is non-increasing AND every clamp
                      s_i(j) = min(binom(n,j), max(0, x(j) - (r-i) binom(n,j)))
                    i = 1..r, is an f-vector (lies in F_n);
                (b) checked exhaustively against brute-force enumeration of
                    the sumset for n <= 4, r <= 3, "twelve cases";
                (c) over the same range monotonicity alone admits strictly
                    more vectors, e.g. 93 against |FF(3;0,0)| = 43;
                (d) smallest witness of insufficiency: n = 2, r = 1,
                    x = (0,1,0).
              Method.  The sumset FF(n;0^r) is enumerated by brute force:
              F_n = all f-vectors of downward-closed families on [n]
              (including the void family and {emptyset}), enumerated
              directly from set families (no Kruskal-Katona, no Linusson
              recursion, no transfer matrix; the enumeration is the
              independent brute_fvectors of code/linusson_ff_counting.py,
              re-implemented here so the script is standalone), and the
              r-fold sums are formed iteratively.  The characterisation is
              then evaluated on every integer vector of the box
              0 <= x(j) <= r binom(n,j) and the two sets compared.  The
              transfer-matrix count ff_count is NOT used except as an extra
              cross-check of the sumset sizes, printed separately.
              Ranges: n = 1..4 crossed with r = 1..3 (12 cases, the reading
              of "twelve cases" that matches n <= 4, r <= 3 with n, r >= 1);
              r = 0 is trivial and not counted.

Run:  python3 code/oneoff/rem_digit_characterisation_check.py
"""

import os
import sys
import time
from itertools import combinations, product
from math import comb


def fvectors(n):
    """f-vectors (f_0..f_n) of all downward-closed families on [n],
    including the void family (all zeros) and {emptyset} = (1,0,...,0)."""
    subs = [frozenset(c) for k in range(1, n + 1)
            for c in combinations(range(n), k)]
    out = set()

    def rec(i, chosen):
        if i == len(subs):
            f = [0] * (n + 1)
            f[0] = 1
            for s in chosen:
                f[len(s)] += 1
            out.add(tuple(f))
            return
        rec(i + 1, chosen)
        s = subs[i]
        if all(frozenset(t) in chosen
               for t in combinations(s, len(s) - 1) if t):
            rec(i + 1, chosen | {s})

    rec(0, frozenset())
    out.add(tuple([0] * (n + 1)))
    return frozenset(out)


def sumset(Fn, r):
    """{s_1 + ... + s_r : s_i in Fn} (all shifts zero)."""
    cur = {tuple([0] * len(next(iter(Fn))))}
    for _ in range(r):
        cur = {tuple(a + b for a, b in zip(x, s)) for x in cur for s in Fn}
    return cur


def digits(x, n):
    q, f = [], []
    for j in range(n + 1):
        c = comb(n, j)
        q.append(x[j] // c)
        f.append(x[j] % c)
    return q, f


def monotone(q):
    return all(q[j] >= q[j + 1] for j in range(len(q) - 1))


def clamps(x, n, r):
    return [tuple(min(comb(n, j), max(0, x[j] - (r - i) * comb(n, j)))
                  for j in range(n + 1)) for i in range(1, r + 1)]


def main():
    sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)),
                                    os.pardir))
    try:
        from linusson_ff_counting import ff_count
    except Exception:            # pragma: no cover
        ff_count = None
    t0 = time.time()
    allok = True
    print("n r | |box| | |FF(n;0^r)| brute | ff_count | char. (mono+clamps) "
          "| equal? | mono only | mono > FF? | clamp-identity/digit-form ok")
    for n in range(1, 5):
        Fn = fvectors(n)
        for r in range(1, 4):
            S = sumset(Fn, r)
            box = list(product(*[range(r * comb(n, j) + 1)
                                 for j in range(n + 1)]))
            char, mono = set(), 0
            ident_ok = True
            for x in box:
                q, f = digits(x, n)
                if not monotone(q):
                    continue
                mono += 1
                cl = clamps(x, n, r)
                # sanity: clamps sum to x, and match eq:delta0-clamp-digits
                if tuple(map(sum, zip(*cl))) != x:
                    ident_ok = False
                for i, s in enumerate(cl, start=1):
                    for j in range(n + 1):
                        want = (comb(n, j) if q[j] > r - i else
                                f[j] if q[j] == r - i else 0)
                        if s[j] != want:
                            ident_ok = False
                if all(s in Fn for s in cl):
                    char.add(x)
            assert S <= set(box)
            eq = (char == S)
            tm = ff_count(n, [0] * r) if ff_count else None
            tm_ok = (tm is None or tm == len(S))
            strict = mono > len(S)
            allok &= eq and ident_ok and tm_ok
            print("%d %d | %6d | %6d | %6s | %6d | %s | %6d | %s | %s"
                  % (n, r, len(box), len(S), tm, len(char),
                     "yes" if eq else "NO", mono, strict, ident_ok))
            if not eq:
                print("   in FF not char:", sorted(S - char)[:5])
                print("   char not in FF:", sorted(char - S)[:5])
    # (d) the witness
    x = (0, 1, 0)
    q, _ = digits(x, 2)
    S21 = sumset(fvectors(2), 1)
    wit = monotone(q) and x not in S21
    print("\nwitness n=2, r=1, x=(0,1,0): digits %s, monotone %s, in FF %s"
          % (q, monotone(q), x in S21))
    # smallest witness: least n, then r, then x, among (n, r) in range
    for n in range(1, 5):
        Fn = fvectors(n)
        found = None
        for r in range(1, 4):
            S = sumset(Fn, r)
            for x in product(*[range(r * comb(n, j) + 1) for j in range(n + 1)]):
                if monotone(digits(x, n)[0]) and x not in S:
                    found = (r, x)
                    break
            if found:
                break
        print("n=%d: first monotone non-member (least r, lex-least x): %s"
              % (n, found))
    # (c) the quoted pair
    S32 = sumset(fvectors(3), 2)
    mono32 = sum(1 for x in product(*[range(2 * comb(3, j) + 1)
                                      for j in range(4)])
                 if monotone(digits(x, 3)[0]))
    print("\nn=3, r=2: monotone-only count %d (claimed 93), |FF(3;0,0)| = %d "
          "(claimed 43)" % (mono32, len(S32)))
    ok_c = (mono32 == 93 and len(S32) == 43)
    allok &= wit and ok_c
    print("\nruntime %.1f s" % (time.time() - t0))
    print("SUMMARY: characterisation equals brute-force sumset in all 12 "
          "cases (n=1..4, r=1..3): %s" % ("PASS" if allok else "FAIL"))
    print("OVERALL:", "PASS" if allok else "FAIL")
    return 0 if allok else 1


if __name__ == "__main__":
    sys.exit(main())
