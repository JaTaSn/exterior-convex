#!/usr/bin/env python3
"""fig_mu_rank_r.py -- higher-rank companion to fig-mu-projection (Part III, Figs. fig:mu and fig:mu-rank-r).

Changelog:
  2026-11-10  Renamed from fig_mu_rank_r_draft.py, outputs from fig-mu-rank-r-DRAFT-n<n>: Jan put the
              n = 6 version in the paper (Figure fig:mu-rank-r, Section sec-centroid). n = 5 is unused.
  2026-11-10  Dot area scaled by 1/r^2 with the grid; output name carries n.
  2026-11-10  Created, Claude-Code (jts-mini), Part III round 5. Jan: "I really like fig-mu, could some
              higher-rank case be depicted similarly?"  Not in the paper; a proposal for Jan to look at.

What it draws: FF(n; 0^r) = S_n + ... + S_n (r equal shifts), projected to
    nu_2 = x_2 / (r C(n,2)),   nu_3 = x_3 / (r C(n,3)),
the rank-r analogue (eq:nu) of fig-mu's mu_2, mu_3. Koz(n; 0^r) = r Koz(n) projects onto the same
triangle 1 >= nu_2 >= nu_3 >= 0. Same visual vocabulary as ff_pictures.py's fig_mu:
  * filled blue dot at (x_2, x_3) of an ff-vector, area ~ fibre (number of distinct ff-vectors there);
  * hollow red ring: lattice point of the projected triangle hit by no ff-vector (every lattice
    point (x_2, x_3) of r * triangle lifts to a lattice point of r Koz(n), by zeros above degree 3);
  * dashed: the limit boundary nu_3 = G(r nu_2)/r with G(v) = floor(v) + (v - floor v)^{3/2},
    the upper edge of the r-fold Minkowski sum of the region under mu_3 = mu_2^{3/2}
    (the n = 3 case of Z in the proof of thm-kupreyeva-rank-r(2), Appendix B);
  * star: centroid of the finite set FF(n; 0^r); diamond: centroid of Koz(n; 0^r), which in nu
    coordinates is that of Koz(n), ((n-1)/n, (n-2)/n), for every r.
By thm-centroid-dilation the star tends to the diamond as r grows, and by cor-zero-shift the
fill rate tends to 1, so the hollow region should shrink.

FF is computed exactly: vectors are encoded in mixed radix (no carries, since every coordinate of
an r-fold sum stays below its radix), so encoded sums are sums of codes and numpy.unique dedupes.

Run: python3 code/oneoff/fig_mu_rank_r.py [n]   (default n = 6; about a minute)
Writes artefacts/ff-pictures/fig-mu-rank-r-n<n>.{pdf,png} and prints the counts.
"""
import os
import sys
from math import comb

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon

HERE = os.path.dirname(os.path.abspath(__file__))
PROJ = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(PROJ, "artefacts", "ff-pictures")

plt.rcParams.update({
    "text.usetex": True, "font.family": "serif", "font.size": 9,
    "axes.labelsize": 9, "axes.titlesize": 9, "legend.fontsize": 8,
    "xtick.labelsize": 8, "ytick.labelsize": 8,
    "text.latex.preamble": r"\usepackage{amsmath,amssymb}"
                           r"\newcommand{\Koz}{\operatorname{Koz}}\newcommand{\FF}{\operatorname{FF}}",
    "axes.linewidth": 0.6, "savefig.bbox": "tight", "savefig.pad_inches": 0.03,
})
C_ACH, C_NON, C_POLY, C_EDGE = "#1f4e8c", "#c0392b", "#e6e9ef", "#3a3f4b"


def upper_shadow_bound(m, k):
    """Kruskal-Katona: the pseudo-power m^(k) (same routine as ff_pictures.py)."""
    s = 0
    while m > 0 and k >= 1:
        a = k
        while comb(a + 1, k) <= m:
            a += 1
        s += comb(a, k + 1)
        m -= comb(a, k)
        k -= 1
    return s


def S_KK(n):
    out = []

    def rec(v, k):
        if k == n:
            out.append(tuple(v))
            return
        ub = comb(n, 2) if k == 1 else upper_shadow_bound(v[-1], k)
        for x in range(ub + 1):
            rec(v + [x], k + 1)
    rec([1, n], 1)
    return out


def ff_equal_shifts(n, rmax):
    """[(r, array of distinct ff-vectors of FF(n; 0^r))] for r = 1..rmax, exact."""
    S = np.array(S_KK(n), dtype=np.int64)
    radix = np.array([rmax * comb(n, k) + 1 for k in range(n + 1)], dtype=np.int64)
    place = np.concatenate([[1], np.cumprod(radix[:-1])])
    assert float(np.prod(radix.astype(float))) < 2.0 ** 62
    codeS = S @ place
    cur = np.unique(codeS)
    res = []
    for r in range(1, rmax + 1):
        if r > 1:
            parts = [np.unique(cur[i:i + 4000, None] + codeS[None, :])
                     for i in range(0, len(cur), 4000)]
            cur = np.unique(np.concatenate(parts))
        vec = (cur[:, None] // place[None, :]) % radix[None, :]
        res.append((r, vec))
    return S, res


def G(v):
    f = np.floor(v)
    return f + (v - f) ** 1.5


def main(n=6, rs=(1, 2, 3)):
    S, data = ff_equal_shifts(n, max(rs))
    c2, c3 = comb(n, 2), comb(n, 3)
    fig, axs = plt.subplots(1, len(rs), figsize=(5.8, 2.25), sharey=True)
    for ax, (r, F) in zip(axs, [d for d in data if d[0] in rs]):
        mult = {}
        for a, b in zip(F[:, 2], F[:, 3]):
            mult[(int(a), int(b))] = mult.get((int(a), int(b)), 0) + 1
        R2, R3 = r * c2, r * c3
        lat = [(a, b) for a in range(R2 + 1) for b in range(R3 + 1) if b * c2 <= a * c3]
        assert set(mult) <= set(lat)
        miss = [p for p in lat if p not in mult]
        ax.add_patch(Polygon([(0, 0), (1, 0), (1, 1)], closed=True, fc=C_POLY, ec=C_EDGE,
                             lw=0.7, zorder=0))
        mx = max(mult.values())
        pts = sorted(mult)
        sc = 1.0 / r ** 2          # the grid spacing shrinks like 1/r, so dot area like 1/r^2
        sizes = [sc * (3 + 40 * (mult[p] / mx) ** 0.7) for p in pts]
        if miss:
            ax.scatter([a / R2 for a, b in miss], [b / R3 for a, b in miss],
                       s=(2.5 if c2 * c3 > 150 else 7) * max(sc, 0.3), facecolors="white",
                       edgecolors=C_NON, linewidths=0.4, zorder=2)
        ax.scatter([a / R2 for a, b in pts], [b / R3 for a, b in pts], s=sizes, c=C_ACH,
                   alpha=0.75, linewidths=0, zorder=3)
        xs = np.linspace(0, 1, 600)
        ax.plot(xs, G(r * xs) / r, color="0.15", lw=0.8, ls="--", zorder=5)
        g2 = F[:, 2].mean() / R2
        g3 = F[:, 3].mean() / R3
        ax.scatter([g2], [g3], marker="*", s=70, c="black", zorder=6, linewidths=0)
        ax.scatter([(n - 1) / n], [(n - 2) / n], marker="D", s=22, facecolors="white",
                   edgecolors="black", linewidths=0.8, zorder=6)
        ax.set_xlim(-0.03, 1.03); ax.set_ylim(-0.03, 1.03); ax.set_aspect("equal")
        ax.set_xticks([0, 0.5, 1]); ax.set_yticks([0, 0.5, 1])
        ax.set_xticklabels(["0", r"$\frac12$", "1"]); ax.set_yticklabels(["0", r"$\frac12$", "1"])
        for s in ("top", "right"):
            ax.spines[s].set_visible(False)
        ax.set_xlabel(r"$\nu_2=x_2/(%d\binom{%d}{2})$" % (r, n) if r > 1
                      else r"$\nu_2=x_2/\binom{%d}{2}$" % n, labelpad=1)
        ax.set_title(r"$r=%d$: $|\FF(%d;0^{%d})|=%d$" % (r, n, r, len(F)), pad=3)
        print("n=%d r=%d: |FF|=%d; %d distinct (x2,x3) among %d lattice points (%d missed); "
              "max fibre %d; centroid FF (nu2,nu3)=(%.4f,%.4f); Koz (%.4f,%.4f)"
              % (n, r, len(F), len(mult), len(lat), len(miss), mx, g2, g3,
                 (n - 1) / n, (n - 2) / n))
    axs[0].set_ylabel(r"$\nu_3=x_3/(r\binom{%d}{3})$" % n)
    h = [plt.Line2D([], [], ls="", marker="o", ms=4, mfc=C_ACH, mec=C_ACH, alpha=0.75,
                    label=r"$(x_2,x_3)$ of an ff-vector (size $\sim$ fibre)"),
         plt.Line2D([], [], ls="", marker="o", ms=3.5, mfc="white", mec=C_NON,
                    label=r"lattice point not hit"),
         plt.Line2D([], [], color="0.35", ls="--", lw=0.7,
                    label=r"$r\nu_3=G(r\nu_2)$"),
         plt.Line2D([], [], ls="", marker="*", ms=7, mfc="black", mec="black",
                    label=r"centroid of $\FF(%d;0^r)$" % n),
         plt.Line2D([], [], ls="", marker="D", ms=4, mfc="white", mec="black",
                    label=r"centroid of $\Koz(%d;0^r)$" % n)]
    fig.legend(handles=h, loc="lower center", ncol=3, frameon=False,
               bbox_to_anchor=(0.5, -0.17), columnspacing=1.2, handletextpad=0.3)
    name = "fig-mu-rank-r-n%d" % n
    fig.savefig(os.path.join(OUT, name + ".pdf"))
    fig.savefig(os.path.join(OUT, name + ".png"), dpi=220)
    print("wrote", name)


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 6)
