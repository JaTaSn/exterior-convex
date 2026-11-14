# 2026-11-10 - Claude-Code (jts-mini), Part III round 4 (Fable review, Part 2, Organisation 6).
# Checks Lemma lem-interior-points of exterior-convex_article3_latest.org as restated in round 4:
#   y_j = 1, y_k = floor(c_k y_{k+1} / c_{k+1}) + 1 for k = j-1..2, y_k = 0 for k > j, c_k = binom(n,k).
#   (1) j <= n-1: (1, n, y_2..y_n) lies in Koz(n), and 1 > mu_2 > ... > mu_j > 0 (relative interior of
#       the projection to x_0..x_j).
#   (2) j = n, every m >= 2: (m, mn, y_2..y_n) and the same with y_2 + 1 satisfy
#       m > mu_2 > ... > mu_n > 0 (relative interior of m Koz(n)).
# Also checks that the point of (2) equals q + (m-2) F_1 for the m = 2 point q, the form in which the
# earlier proof built it, so the earlier membership checks cover the same points.
# Exact rational arithmetic. Run: python3 code/oneoff/interior_points_direct_check.py
from fractions import Fraction as Fr
from math import comb

def ys(n, j):
    c = [comb(n, k) for k in range(n + 1)]
    y = [0] * (n + 1)
    y[j] = 1
    for k in range(j - 1, 1, -1):
        y[k] = (c[k] * y[k + 1]) // c[k + 1] + 1
    return c, y

def strict_chain(top, mus):
    seq = [top] + mus + [Fr(0)]
    return all(a > b for a, b in zip(seq, seq[1:]))

cases = 0
for n in range(3, 31):
    for j in range(2, n):                      # part (1)
        c, y = ys(n, j)
        mu = [Fr(y[k], c[k]) for k in range(2, n + 1)]
        assert all(a >= b for a, b in zip([Fr(1)] + mu, mu + [Fr(0)])), (n, j)      # in Koz(n)
        assert strict_chain(Fr(1), mu[: j - 1]), (n, j)                             # interior of projection
        cases += 1
    c, y = ys(n, n)                            # part (2)
    for m in range(2, 9):
        for bump in (0, 1):
            z = y[:]; z[2] += bump
            mu = [Fr(z[k], c[k]) for k in range(2, n + 1)]
            assert strict_chain(Fr(m), mu[:-1] + [mu[-1]]), (n, m, bump)
            cases += 1
        q = [2, 2 * n] + y[2:]
        assert [m, m * n] + y[2:] == [q[0] + (m - 2), q[1] + (m - 2) * n] + q[2:]
print(f"lem-interior-points: all {cases} cases pass (3 <= n <= 30; part (2) for 2 <= m <= 8, both points)")
