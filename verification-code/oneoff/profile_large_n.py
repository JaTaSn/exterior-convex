# profile_large_n.py -- mu-profile of centroid(S_n) and of lattice points of Koz(n), large n
# Changelog (reverse chronological):
# 2026-11-14 - Claude-Code (jts-pc): path made relative to this file, so the script runs from the
#   public copy (exterior-convex repo, verification-code/oneoff/) as well as from the working home.
# 2026-10-20 - Claude (overnight article-3 agent): created; first moments + diagonal second
#   moments only, via centroids_moments.chain_moments(second=False).
import os, sys, time
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from centroids_moments import *
nmax = int(sys.argv[1])
for n in range(3, nmax + 1):
    t = time.time()
    for name, g in (("S", g_kk(n)), ("L", g_lat(n))):
        c, S1, S2 = chain_moments(n, g, second=False)
        mu = [Q(S1[k], c * comb(n, k)) for k in range(1, n + 1)]
        sd = [float(Q(S2[k][k], c * comb(n, k) ** 2) - mu[k - 1] ** 2) ** .5 for k in range(1, n + 1)]
        lam_mean = float(sum(mu))
        lam_m2 = float(sum((2 * k - 1) * mu[k - 1] for k in range(1, n + 1)))  # E[j^2] = sum (2k-1) mu_k
        print(name, n, "count", c, "baryMean %.6f baryVar %.6f" % (lam_mean, lam_m2 - lam_mean ** 2))
        print("  mu", " ".join("%.5f" % float(x) for x in mu))
        print("  sd", " ".join("%.5f" % x for x in sd))
    print("  time %.1f" % (time.time() - t), flush=True)
