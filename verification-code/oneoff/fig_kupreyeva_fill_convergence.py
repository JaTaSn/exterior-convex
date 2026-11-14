# 2026-11-13 - Claude-Code (jts-mini), at Jan's request (Part III sweep, item 7: "could there be a plot
#   of the fill-rates approaching their asymptotic limits accompanying ex-kupreyeva-values?").
#   Figure fig:kupreyeva-fill of Part III: fill^(p)(n;d) against p, and p*(fill - lim), for n = 3, 4 and
#   five shift vectors, with the limits of thm-kupreyeva-rank-r.  The counts are exact, computed with the
#   functions of kupreyeva_limit_rank_r.py (same directory; its own cross-checks are in
#   runs/2026-11-09_kupreyeva-limit-rank-r.txt).  Also checks the sentence of ex-kupreyeva-values that at
#   n = 4, d = (0,1,1) the approach is from above.
#   Run:  timeout 900 python3 code/oneoff/fig_kupreyeva_fill_convergence.py
#   Output: artefacts/ff-pictures/fig-kupreyeva-fill.{pdf,png}; the numbers on stdout (saved as
#   runs/2026-11-13_kupreyeva-fill-convergence.txt).
import os
import sys
import time
from fractions import Fraction as Fr

import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from kupreyeva_limit_rank_r import (linusson_E, class_counts, GL, GS_linusson,   # noqa: E402
                                    chained_count, limit_types, limit_groups)

OUT = os.path.normpath(os.path.join(HERE, "..", "..", "artefacts", "ff-pictures"))

SHIFTS = [(0,), (0, 0), (0, 1), (0, 2), (0, 0, 0)]       # colour follows the shift vector
COLOURS = ["#2a78d6", "#eb6834", "#1baf7a", "#eda100", "#e87ba4"]   # validated, light surface
PMAX = {3: 10000, 4: 2000}
NPTS = 34


def pgrid(n):
    g = np.unique(np.round(np.logspace(np.log10(n), np.log10(PMAX[n]), NPTS)).astype(int))
    return [int(p) for p in g]


def counts(n, P):
    E = linusson_E(P, n)
    ML = class_counts(lambda a, b: GL(P, a, b), n)
    MS = class_counts(lambda a, b: GS_linusson(E, a, b), n)
    return ML, MS


def main():
    t0 = time.time()
    print("Fill rates fill^(p)(n;d) = |FF^(p)(n;d)| / #(Koz^(p)(n;d) cap Z^(N+1)), exact, and the limits of")
    print("thm-kupreyeva-rank-r (type formula; 'groups' closed form must agree).")
    data = {}
    lims = {}
    for n in (3, 4):
        for d in SHIFTS:
            lim, _ = limit_types(n, d)
            assert limit_groups(n, d) == lim, (n, d)
            lims[(n, d)] = lim
        rows = {d: [] for d in SHIFTS}
        for P in pgrid(n):
            ML, MS = counts(n, P)
            for d in SHIFTS:
                f = Fr(chained_count(MS, n, d), chained_count(ML, n, d))
                rows[d].append((P, f))
        data[n] = rows
        for d in SHIFTS:
            lim = lims[(n, d)]
            print(f"\n n={n} d={d}: limit {lim} = {float(lim):.6f}")
            print(f"   {'p':>6} {'fill':>10} {'p*(fill-lim)':>13}")
            for P, f in rows[d]:
                print(f"   {P:>6} {float(f):>10.6f} {float(P * (f - lim)):>13.4f}")

    # the "from above" sentence of ex-kupreyeva-values
    n, d = 4, (0, 1, 1)
    lim, _ = limit_types(n, d)
    print(f"\n check: n={n} d={d}, limit {lim} = {float(lim):.6f}; sign of fill - limit")
    for P in (5, 10, 20, 50, 100, 200, 500, 1000, 2000):
        ML, MS = counts(n, P)
        f = Fr(chained_count(MS, n, d), chained_count(ML, n, d))
        print(f"   p={P:>5}  fill {float(f):.6f}  fill-lim {float(f - lim):+.6f}  p*(fill-lim) {float(P * (f - lim)):+.4f}")

    # ---- the figure ------------------------------------------------------------------------------
    plt.rcParams.update({
        "text.usetex": True, "text.latex.preamble": r"\usepackage{amsmath}",
        "font.family": "serif", "font.size": 9,
        "axes.labelsize": 9, "axes.titlesize": 9, "legend.fontsize": 8,
        "xtick.labelsize": 8, "ytick.labelsize": 8,
        "axes.linewidth": 0.6, "savefig.bbox": "tight", "savefig.pad_inches": 0.03,
    })
    fig, axs = plt.subplots(2, 2, figsize=(5.8, 4.1), sharex="col",
                            gridspec_kw={"height_ratios": [1.35, 1], "hspace": 0.08, "wspace": 0.22})
    for col, n in enumerate((3, 4)):
        top, bot = axs[0, col], axs[1, col]
        seen = set()
        for d, colour in zip(SHIFTS, COLOURS):
            ps = [P for P, _ in data[n][d]]
            fs = [float(f) for _, f in data[n][d]]
            lim = lims[(n, d)]
            label = r"$\boldsymbol d=(" + ",".join(map(str, d)) + ")$"
            top.plot(ps, fs, color=colour, lw=1.3, label=label, zorder=3)
            bot.plot(ps, [P * float(f - lim) for P, f in data[n][d]], color=colour, lw=1.3, zorder=3)
            if lim not in seen:
                seen.add(lim)
                top.axhline(float(lim), color="0.45", lw=0.6, ls=(0, (3, 2)), zorder=1)
                top.annotate(rf"${lim.numerator}/{lim.denominator}$", xy=(1.0, float(lim)),
                             xycoords=("axes fraction", "data"), xytext=(3, 0),
                             textcoords="offset points", va="center", ha="left", fontsize=7,
                             color="0.25")
        top.set_xscale("log")
        bot.set_xscale("log")
        top.set_title(rf"$n={n}$")
        top.set_ylim(0.15 if n == 4 else 0.4, 1.02)
        bot.axhline(0, color="0.6", lw=0.5, zorder=1)
        bot.set_xlabel(r"$p$")
        for ax in (top, bot):
            ax.grid(True, which="major", color="0.9", lw=0.5)
            ax.set_axisbelow(True)
            ax.spines["top"].set_visible(False)
            ax.spines["right"].set_visible(False)
        top.tick_params(labelbottom=False)
        if col == 0:
            top.set_ylabel(r"$\operatorname{fill}^{(p)}(n;\boldsymbol d)$")
            bot.set_ylabel(r"$p\,(\operatorname{fill}^{(p)}-\lim)$")
    handles, labels = axs[0, 0].get_legend_handles_labels()
    fig.legend(handles, labels, loc="lower center", ncol=5, frameon=False,
               bbox_to_anchor=(0.5, -0.045), handlelength=1.6, columnspacing=1.2)
    os.makedirs(OUT, exist_ok=True)
    name = "fig-kupreyeva-fill"
    fig.savefig(os.path.join(OUT, name + ".pdf"))
    fig.savefig(os.path.join(OUT, name + ".png"), dpi=220)
    print(f"\nwrote {os.path.join(OUT, name)}.pdf/.png")
    print(f"elapsed {time.time() - t0:.1f} s")


if __name__ == "__main__":
    main()
