# moments_tables.py -- the rank-one tables of Part III, sec-moments (tab:concentration,
# tab:barycentric-index, tab:profile-n24), typeset from the output of profile_large_n.py.
#
# Changelog (reverse chronological):
# 2026-11-14 - Claude Opus 5.5 (jts-pc), for Jan's sweep item 7 ("Can some tables be added to
#   sec-moments, in particular to illustrate obs-concentration? Strong suggestion."): created.
#   Reads a profile_large_n.py output (S = f-vectors S_n, L = lattice points of Koz(n); per n the
#   count, the barycentric mean and variance of J, the LYM centroid mu_k and the standard
#   deviations sd(mu_k), k = 1..n) and prints three LaTeX tables. The Koz(n) columns are the closed
#   forms of Prop. prop-centroid-simplex and prop-second-moments: mu_k = (n-k+1)/n,
#   Var(mu_k) = (k-1)(n-k+1)/(n^2(n+1)), Var(J) = (n^2-1)/12. Numbers are rounded, not truncated.
#
# Usage:  python3 moments_tables.py <profile_large_n output> [<second output to compare>]
import sys, re
from math import sqrt


def parse(path):
    d = {}
    cur = None
    for line in open(path):
        m = re.match(r'^([SL]) (\d+) count (\d+) baryMean ([\d.]+) baryVar ([\d.]+)', line)
        if m:
            cur = (m.group(1), int(m.group(2)))
            d[cur] = dict(count=int(m.group(3)), bmean=float(m.group(4)), bvar=float(m.group(5)))
            continue
        m = re.match(r'^  (mu|sd) (.*)$', line)
        if m and cur:
            d[cur][m.group(1)] = [float(x) for x in m.group(2).split()]
    return d


def koz_sd(n, k):
    return sqrt((k - 1) * (n - k + 1) / (n * n * (n + 1)))


def main():
    D = parse(sys.argv[1])
    if len(sys.argv) > 2:
        E = parse(sys.argv[2])
        same = all(D[key] == E[key] for key in D if key in E)
        print("% compared with", sys.argv[2], ": identical on", len([k for k in D if k in E]), "entries:", same)
    evens = [n for n in range(4, 27, 2) if ('S', n) in D]

    print("% tab:concentration -- sd of the middle LYM coordinate mu_{n/2}")
    for n in evens:
        m = n // 2
        s, l, k = D[('S', n)]['sd'][m - 1], D[('L', n)]['sd'][m - 1], koz_sd(n, m)
        print("%d & %.4f & %.3f & %.4f & %.3f & %.4f & %.3f\\\\" % (n, s, n * s, l, sqrt(n) * l, k, sqrt(n) * k))
    # where the S_n and Koz(n) curves cross, in the middle coordinate ceil(n/2)
    for n in range(10, 20):
        m = (n + 1) // 2
        if ('S', n) in D:
            print("%% n=%d m=%d sd_S=%.5f sd_Koz=%.5f %s" % (n, m, D[('S', n)]['sd'][m - 1], koz_sd(n, m),
                  "S>Koz" if D[('S', n)]['sd'][m - 1] > koz_sd(n, m) else "S<Koz"))

    print("% tab:barycentric-index -- Var(J)/n^2, transposed: one column per n")
    print("n & " + " & ".join(str(n) for n in evens) + "\\\\")
    for name, f in (("S_n", lambda n: D[('S', n)]['bvar'] / n ** 2), ("lattice", lambda n: D[('L', n)]['bvar'] / n ** 2),
                    ("simplex", lambda n: (n * n - 1) / 12 / n ** 2)):
        print(name + " & " + " & ".join("%.3f" % f(n) for n in evens) + "\\\\")
    for n in evens:
        print("%% n=%d mean J: S %.4f (n-1)/2=%.1f  L %.4f  simplex %.1f" % (n, D[('S', n)]['bmean'], (n - 1) / 2,
                                                                            D[('L', n)]['bmean'], (n + 1) / 2))

    n = 24
    print("% tab:profile-n24 -- the LYM profile at n = 24: mean and sd of mu_k")
    for k in range(2, n + 1, 2):
        S, L = D[('S', n)], D[('L', n)]
        print("%d & %.3f & %.3f & %.3f & %.3f & %.3f & %.3f\\\\" % (k, S['mu'][k - 1], S['sd'][k - 1], L['mu'][k - 1],
                                                                     L['sd'][k - 1], (n - k + 1) / n, koz_sd(n, k)))


if __name__ == '__main__':
    main()
