# beta_identity_exact.py -- exact test of the lattice-point centroid identity
# mu_k + mu_{n-k} = 1 + mu_{n-1} (Part III, thm-beta-lattice, obs-beta-composite) for given n.
#
# Changelog (reverse chronological):
# 2026-11-14 - Claude Opus 5.5 (jts-pc): created. The 5-decimal LYM centroids of the lattice points
#   of Koz(n) in the 2026-10-20 log satisfy the identity to print precision at n = 25, the only
#   composite n <= 26 that does; this decides it exactly with the chain DP of centroids_moments.py
#   (first moments only, exact fractions).
#
# Usage:  python3 beta_identity_exact.py 15 21 25
import sys, time
from fractions import Fraction as Q
from math import comb
from centroids_moments import chain_moments, g_lat

for n in map(int, sys.argv[1:]):
    t = time.time()
    c, S1, _ = chain_moments(n, g_lat(n), second=False)
    mu = {k: Q(S1[k], c * comb(n, k)) for k in range(1, n + 1)}
    dev = {k: mu[k] + mu[n - k] - 1 - mu[n - 1] for k in range(1, n)}
    nz = {k: v for k, v in dev.items() if v != 0}
    worst = max(nz.items(), key=lambda kv: abs(kv[1])) if nz else None
    print("n=%d  count=%d  identity holds exactly: %s" % (n, c, not nz))
    if worst:
        print("   largest deviation at k=%d: %.3e  (= %s)" % (worst[0], float(worst[1]),
              str(worst[1]) if len(str(worst[1])) < 80 else "a fraction of %d digits" % len(str(worst[1]))))
    print("   time %.1f s" % (time.time() - t), flush=True)
