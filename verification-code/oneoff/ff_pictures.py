#!/usr/bin/env sage-python
"""ff_pictures.py -- publication figures of ff-vectors inside Kozlov polytopes.

Changelog (reverse chronological):
  2026-11-14  fig-koz3-d02-product drawn on a larger canvas, (4.4, 2.8) in. instead of (3.6, 2.3),
              same font sizes (Jan, Part III sweep of 2026-11-14, item 5: its title font was too
              big and the figure slightly too large beside fig-koz3-d01).  The article now
              includes every figure at the scale it was drawn at, relative to fig-koz3-d01, so
              the fonts agree; the bigger canvas keeps the drawing from shrinking with them.
              Also: figure functions can be named on the command line to run only those
              (`sage code/oneoff/ff_pictures.py fig_koz3_02`), leaving counts.txt untouched.
              Claude-Code (jts-pc).
  2026-10-29  Axis labels and annotations in x, not f (Jan: a coordinate of R^{N+1} written f_k
              suggests an f-vector; the paper now names the coordinates x_0,...,x_N).  Claude-Code-
              de276a21 (jts-pc).
  2026-10-20  Created (article 3 overnight push).  Generates every figure in
              artefacts/ff-pictures/ (PDF for inclusion + PNG preview) and
              prints the counts quoted in artefacts/ff-pictures/README.org.

Run with Sage's Python (needs Sage for Polyhedron.integral_points; matplotlib
and scipy come with Sage):

    cd PROJ && sage code/oneoff/ff_pictures.py

Point sets are computed from scratch:
  * S_n by the Kruskal--Katona criterion  f_{k+1} <= f_k^{<k>}  starting from
    (f_0, f_1) = (1, n); cross-checked against a brute-force enumeration of
    all simplicial complexes on [n] for n <= 5 (assert).
  * FF(n; d) as the sumset  S_n + shift^{d_2} S_n + ... ;
  * lattice points of Koz(n; d) = conv FF(n; d) by Sage's
    Polyhedron.integral_points();  "non-achievable" = lattice points not in FF.
  * rank-1 lattice-point counts of Koz(n) for the fraction plot from the
    H-description  1 >= mu_2 >= ... >= mu_n >= 0,  mu_k = f_k / C(n,k).
Style: one palette for all figures -- achievable = filled blue disc,
non-achievable lattice point = hollow red ring, polytope = light grey with a
dark outline, centroids = black star (discrete) / white diamond (continuous).
"""
import os
import sys
from itertools import combinations, product
from fractions import Fraction
from functools import lru_cache

from sage.all import Polyhedron, binomial as sbinom

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from matplotlib.patches import Polygon
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import numpy as np

# sage sets __file__ oddly; use argv[0] (the script path) instead
HERE = os.path.dirname(os.path.abspath(sys.argv[0]))
PROJ = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(PROJ, "artefacts", "ff-pictures")
os.makedirs(OUT, exist_ok=True)

# ---------------------------------------------------------------- style
plt.rcParams.update({
    "text.usetex": True,
    "font.family": "serif",
    "font.size": 9,
    "axes.labelsize": 9,
    "axes.titlesize": 9,
    "legend.fontsize": 8,
    "xtick.labelsize": 8,
    "ytick.labelsize": 8,
    "text.latex.preamble": r"\usepackage{amsmath,amssymb}"
                           r"\newcommand{\Koz}{\operatorname{Koz}}",
    "axes.linewidth": 0.6,
    "savefig.bbox": "tight",
    "savefig.pad_inches": 0.03,
})
C_ACH = "#1f4e8c"      # achievable: filled
C_NON = "#c0392b"      # non-achievable lattice point: hollow ring
C_POLY = "#e6e9ef"     # polytope fill
C_EDGE = "#3a3f4b"     # polytope outline
MS = 22                # scatter marker area (pt^2) in 2D panels

COUNTS = []            # lines for the README / stdout


def note(s):
    COUNTS.append(s)
    print(s)


def binom(a, b):
    return int(sbinom(a, b))


# ---------------------------------------------------------------- S_n
def upper_shadow_bound(m, k):
    """KK: max number of (k+1)-sets whose k-shadow fits into m k-sets."""
    s = 0
    while m > 0 and k >= 1:
        a = k
        while binom(a + 1, k) <= m:
            a += 1
        s += binom(a, k + 1)
        m -= binom(a, k)
        k -= 1
    return s


def S_KK(n):
    out = []

    def rec(v, k):
        if k == n:
            out.append(tuple(v))
            return
        ub = binom(n, 2) if k == 1 else upper_shadow_bound(v[-1], k)
        for x in range(ub + 1):
            rec(v + [x], k + 1)
    if n == 0:
        return [(1,)]
    rec([1, n], 1)
    return out


def S_brute(n):
    """All proper complexes on [n], layer by layer; returns the f-vector set."""
    layers1 = [tuple([i]) for i in range(n)]
    res = set()

    def rec(fvec, prev_layer, k):
        # prev_layer: set of k-subsets present; choose any subset of the
        # (k+1)-sets all of whose facets lie in prev_layer
        if k == n:
            res.add(tuple(fvec))
            return
        cand = [c for c in combinations(range(n), k + 1)
                if all(tuple(x for x in c if x != y) in prev_layer for y in c)]
        for mask in range(2 ** len(cand)):
            chosen = {cand[j] for j in range(len(cand)) if (mask >> j) & 1}
            if not chosen:
                res.add(tuple(fvec + [0] * (n - k)))
                continue
            rec(fvec + [len(chosen)], chosen, k + 1)
    rec([1, n], set(layers1), 1)
    return res


for n in range(1, 6):
    assert set(S_KK(n)) == S_brute(n), n
note("check: S_n by Kruskal-Katona == brute force for n = 1..5; |S_n| = "
     + ", ".join(str(len(S_KK(n))) for n in range(1, 8)) + " (n = 1..7)")


def FF(n, d):
    S = S_KK(n)
    N = n + d[-1]
    pts = {tuple([0] * (N + 1))}
    for di in d:
        pts = {tuple(p[i] + (s[i - di] if 0 <= i - di <= n else 0)
                     for i in range(N + 1)) for p in pts for s in S}
    return pts


def koz_data(n, d):
    """(free coordinate indices, achievable pts, nonachievable pts, Polyhedron)
    all in the free coordinates."""
    F = FF(n, d)
    P = Polyhedron(vertices=[list(p) for p in F])
    L = {tuple(int(x) for x in p) for p in P.integral_points()}
    free = sorted({di + k for di in d for k in range(2, n + 1)})
    N = n + d[-1]
    fixed = [i for i in range(N + 1) if i not in free]
    for i in fixed:
        assert len({p[i] for p in L}) == 1
    assert F <= L
    proj = lambda p: tuple(p[i] for i in free)
    A = sorted(proj(p) for p in F)
    B = sorted(proj(p) for p in L - F)
    Q = Polyhedron(vertices=[list(proj(p)) for p in F])
    assert Q.dim() == len(free)
    fix = {i: next(iter(L))[i] for i in fixed}
    return free, A, B, Q, fix


def dstr(d):
    return ",".join(str(x) for x in d)


# ---------------------------------------------------------------- helpers
def poly2d(ax, Q):
    vs = [tuple(float(x) for x in v) for v in Q.vertices_list()]
    c = np.mean(vs, axis=0)
    vs.sort(key=lambda v: np.arctan2(v[1] - c[1], v[0] - c[0]))
    ax.add_patch(Polygon(vs, closed=True, fc=C_POLY, ec=C_EDGE, lw=0.8,
                         zorder=1))


def dots2d(ax, A, B, i=0, j=1, ms=MS):
    if A:
        ax.scatter([p[i] for p in A], [p[j] for p in A], s=ms, c=C_ACH,
                   edgecolors=C_ACH, linewidths=0.6, zorder=3)
    if B:
        ax.scatter([p[i] for p in B], [p[j] for p in B], s=ms * 1.15,
                   facecolors="white", edgecolors=C_NON, linewidths=1.1,
                   zorder=4)


def int_ticks(ax, xmax, ymax, xstep=1, ystep=1):
    ax.set_xticks(range(0, xmax + 1, xstep))
    ax.set_yticks(range(0, ymax + 1, ystep))
    ax.set_xlim(-0.6, xmax + 0.6)
    ax.set_ylim(-0.6, ymax + 0.6)
    ax.set_aspect("equal")
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)


def legend_handles(non=True):
    h = [plt.Line2D([], [], ls="", marker="o", ms=4.5, mfc=C_ACH, mec=C_ACH,
                    label="ff-vector (achievable)")]
    if non:
        h.append(plt.Line2D([], [], ls="", marker="o", ms=4.8, mfc="white",
                            mec=C_NON, mew=1.1,
                            label="lattice point, not achievable"))
    return h


def save(fig, name):
    fig.savefig(os.path.join(OUT, name + ".pdf"))
    fig.savefig(os.path.join(OUT, name + ".png"), dpi=220)
    plt.close(fig)
    print("wrote", name)


def facets3d(Q):
    """List of vertex-polygons (ordered) of a 3-polytope."""
    polys = []
    for f in Q.faces(2):
        vs = np.array([[float(x) for x in v] for v in f.vertices()])
        c = vs.mean(axis=0)
        nrm = np.array([float(x) for x in f.ambient_Hrepresentation()[0].A()])
        u = vs[0] - c
        u /= np.linalg.norm(u)
        w = np.cross(nrm, u)
        w /= np.linalg.norm(w)
        ang = [np.arctan2((v - c) @ w, (v - c) @ u) for v in vs]
        polys.append(vs[np.argsort(ang)])
    return polys


def draw3d(ax, Q, A, B, labels, elev=22, azim=-58, ms=16):
    pc = Poly3DCollection(facets3d(Q), facecolors=C_POLY, edgecolors=C_EDGE,
                          linewidths=0.6, alpha=0.35)
    ax.add_collection3d(pc)
    if A:
        a = np.array(A, dtype=float)
        ax.scatter(a[:, 0], a[:, 1], a[:, 2], s=ms, c=C_ACH, depthshade=False)
    if B:
        b = np.array(B, dtype=float)
        ax.scatter(b[:, 0], b[:, 1], b[:, 2], s=ms * 1.2, facecolors="white",
                   edgecolors=C_NON, linewidths=1.0, depthshade=False)
    ax.set_xlabel(labels[0], labelpad=-6)
    ax.set_ylabel(labels[1], labelpad=-6)
    ax.set_zlabel(labels[2], labelpad=-7)
    ax.view_init(elev=elev, azim=azim)
    ax.tick_params(pad=-3, labelsize=7)
    for axis in (ax.xaxis, ax.yaxis, ax.zaxis):
        axis.pane.set_facecolor((1, 1, 1, 0))
        axis.pane.set_edgecolor((0.85, 0.85, 0.85, 1))
        axis._axinfo["grid"]["color"] = (0.9, 0.9, 0.9, 1)
        axis._axinfo["grid"]["linewidth"] = 0.4


def flab(k):
    return r"$x_{%d}$" % k


# ================================================================ Fig 1
def fig_koz3():
    fig, axs = plt.subplots(1, 3, figsize=(5.6, 1.85),
                            gridspec_kw={"width_ratios": [3.6, 6.6, 9.6]})
    for ax, r in zip(axs, (1, 2, 3)):
        d = [0] * r
        free, A, B, Q, fix = koz_data(3, d)
        poly2d(ax, Q)
        dots2d(ax, A, B, ms=14)
        int_ticks(ax, 3 * r, r, xstep=3 if r > 1 else 1)
        ax.set_xlabel(flab(2), labelpad=1)
        if r == 1:
            ax.set_ylabel(flab(3))
        title = (r"$\Koz(3)$" if r == 1 else
                 r"$\Koz(3;%s)$" % dstr(d))
        ax.set_title(title + r":\ \ $%d/%d$" % (len(A), len(A) + len(B)),
                     pad=3, fontsize=8.5)
        note("fig-koz3-dilates: Koz(3;%s): %d achievable of %d lattice points"
             % (dstr(d), len(A), len(A) + len(B)))
    save(fig, "fig-koz3-dilates")


# ================================================================ Fig 2
def fig_koz4():
    free, A, B, Q, fix = koz_data(4, [0])
    note("fig-koz4: Koz(4): coords %s; %d achievable of %d lattice points; "
         "non-achievable %s" % (free, len(A), len(A) + len(B), B))
    fig = plt.figure(figsize=(5.6, 2.5))
    ax = fig.add_subplot(1, 2, 1, projection="3d")
    draw3d(ax, Q, A, B, [flab(2), flab(3), flab(4)], elev=24, azim=-118)
    ax.set_box_aspect((1.25, 1.0, 0.75), zoom=0.95)
    ax.set_xticks(range(0, 7, 2)); ax.set_yticks(range(0, 5, 2))
    ax.set_zticks([0, 1])
    ax2 = fig.add_subplot(1, 2, 2)
    # projection to (f2, f3): the slice f4 = 0 is the whole projection
    Q2 = Polyhedron(vertices=[[v[0], v[1]] for v in Q.vertices_list()])
    poly2d(ax2, Q2)
    A0 = [p for p in A if p[2] == 0]
    A1 = [p for p in A if p[2] == 1]
    dots2d(ax2, A0, B)
    ax2.scatter([p[0] for p in A1], [p[1] for p in A1], s=110,
                facecolors="none", edgecolors=C_ACH, linewidths=0.8, zorder=2)
    ax2.annotate(r"also $x_4 = 1$", xy=(6, 4), xytext=(3.2, 4.25),
                 fontsize=7.5, arrowprops=dict(arrowstyle="-", lw=0.5),
                 va="center")
    int_ticks(ax2, 6, 4)
    ax2.set_xlabel(flab(2)); ax2.set_ylabel(flab(3))
    ax2.set_title(r"projection to $(x_2,x_3)$ = slice $x_4=0$", pad=3)
    fig.legend(handles=legend_handles(), loc="lower center", ncol=2,
               frameon=False, bbox_to_anchor=(0.5, -0.06))
    fig.subplots_adjust(wspace=0.15)
    save(fig, "fig-koz4")


# ================================================================ Fig 3
def fig_slices(n, d, name, slice_axis_label):
    """3-dim Koz(n;d): slices by the last free coordinate."""
    free, A, B, Q, fix = koz_data(n, d)
    zs = sorted({p[2] for p in A + B})
    note("%s: Koz(%d;%s): coords %s; %d achievable of %d lattice points; "
         "non-achievable %s" % (name, n, dstr(d), free, len(A),
                                len(A) + len(B), B))
    xmax = max(p[0] for p in A + B)
    ymax = max(p[1] for p in A + B)
    xmin = min(p[0] for p in A + B)
    ymin = min(p[1] for p in A + B)
    widths = []
    for z in zs:
        sl = Q.intersection(Polyhedron(eqns=[[-z, 0, 0, 1]]))
        widths.append(1)
    fig, axs = plt.subplots(1, len(zs), figsize=(5.6, 1.75), sharey=True,
                            squeeze=False)
    axs = axs[0]
    for ax, z in zip(axs, zs):
        sl = Q.intersection(Polyhedron(eqns=[[-z, 0, 0, 1]]))
        vs = [[v[0], v[1]] for v in sl.vertices_list()]
        S2 = Polyhedron(vertices=vs)
        if S2.dim() == 2:
            poly2d(ax, S2)
        elif S2.dim() == 1:
            v = np.array(S2.vertices_list(), dtype=float)
            ax.plot(v[:, 0], v[:, 1], color=C_EDGE, lw=0.8, zorder=1)
        Az = [p for p in A if p[2] == z]
        Bz = [p for p in B if p[2] == z]
        dots2d(ax, Az, Bz, ms=12)
        ax.set_xlim(xmin - 0.6, xmax + 0.6)
        ax.set_ylim(ymin - 0.6, ymax + 0.6)
        ax.set_aspect("equal")
        ax.set_xticks(range(xmin, xmax + 1, 2 if xmax - xmin > 6 else 1))
        ax.set_yticks(range(ymin, ymax + 1, 2 if ymax - ymin > 6 else 1))
        for s in ("top", "right"):
            ax.spines[s].set_visible(False)
        ax.set_xlabel(flab(free[0]), labelpad=1)
        ax.set_title(r"%s$\,=%d$:\ \ $%d/%d$" % (slice_axis_label, z, len(Az),
                                              len(Az) + len(Bz)), pad=3)
    axs[0].set_ylabel(flab(free[1]))
    fig.legend(handles=legend_handles(bool(B)), loc="lower center", ncol=2,
               frameon=False, bbox_to_anchor=(0.5, -0.13))
    save(fig, name)
    return free, A, B, Q


# ================================================================ Fig 4
def fig_koz3_01():
    free, A, B, Q, fix = koz_data(3, [0, 1])
    note("fig-koz3-d01: Koz(3;0,1): coords %s, fixed %s; %d achievable of %d "
         "lattice points; %d vertices" % (free, fix, len(A), len(A) + len(B),
                                        Q.n_vertices()))
    fig = plt.figure(figsize=(5.6, 2.3))
    ax = fig.add_axes([-0.04, 0.02, 0.52, 0.98], projection="3d")
    draw3d(ax, Q, A, B, [flab(2), flab(3), flab(4)], elev=24, azim=-118)
    ax.set_box_aspect((0.9, 1.1, 0.6), zoom=0.95)
    ax.set_xticks(range(3, 7)); ax.set_yticks(range(0, 5))
    ax.set_zticks([0, 1])
    fig.text(0.22, 0.97, r"$\Koz(3;0,1)$\ \ ($x_0=1$, $x_1=4$)",
             ha="center", va="top")
    # right: slices f4 = 0, 1
    gs = fig.add_gridspec(1, 4, left=0.56, right=0.99, wspace=0.35,
                          bottom=0.14, top=0.88)
    for k, z in enumerate((0, 1)):
        a2 = fig.add_subplot(gs[0, 2 * k:2 * k + 2])
        sl = Q.intersection(Polyhedron(eqns=[[-z, 0, 0, 1]]))
        S2 = Polyhedron(vertices=[[v[0], v[1]] for v in sl.vertices_list()])
        poly2d(a2, S2)
        Az = [p for p in A if p[2] == z]
        dots2d(a2, Az, [p for p in B if p[2] == z], ms=12)
        a2.set_xlim(2.4, 6.6); a2.set_ylim(-0.6, 4.6)
        a2.set_xticks(range(3, 7)); a2.set_yticks(range(0, 5))
        a2.set_aspect("equal")
        for s in ("top", "right"):
            a2.spines[s].set_visible(False)
        a2.set_xlabel(flab(2), labelpad=1)
        if k == 0:
            a2.set_ylabel(flab(3))
        a2.set_title(r"$x_4=%d$: $%d$ points" % (z, len(Az)), pad=3)
    save(fig, "fig-koz3-d01")


# ================================================================ Fig 5
def fig_koz3_02():
    """Koz(3;0,2) = Koz(3) x Koz(3) (product regime, coordinates
    (f2,f3 | f4,f5) with f2,f3 shifted by the second summand's (1,3))."""
    free, A, B, Q, fix = koz_data(3, [0, 2])
    note("fig-koz3-d02: Koz(3;0,2): coords %s; %d achievable of %d lattice "
         "points; product of two triangles (%d vertices)"
         % (free, len(A), len(A) + len(B), Q.n_vertices()))
    tri = [(0, 0), (3, 0), (3, 1)]
    S3 = [(0, 0), (1, 0), (2, 0), (3, 0), (3, 1)]
    fig, ax = plt.subplots(figsize=(4.4, 2.8))   # was (3.6, 2.3); see changelog 2026-11-14
    # outer triangle: (f2 - 1, f3 - 3) in [first factor], scaled by 5
    sc = 4.2
    big = [(x * sc, y * sc * 2.2) for x, y in tri]
    ax.add_patch(Polygon(big, closed=True, fc="none", ec=C_EDGE, lw=0.7,
                         ls="--", zorder=0))
    small_scale = 0.62
    for (a, b) in S3:
        ox, oy = a * sc, b * sc * 2.2
        sm = [(ox + small_scale * (x - 1.5), oy + small_scale * 2.2 *
               (y - 0.5)) for x, y in tri]
        ax.add_patch(Polygon(sm, closed=True, fc=C_POLY, ec=C_EDGE, lw=0.6,
                             zorder=1))
        ax.scatter([ox + small_scale * (x - 1.5) for x, y in S3],
                   [oy + small_scale * 2.2 * (y - 0.5) for x, y in S3],
                   s=6, c=C_ACH, zorder=3)
    ax.set_xticks([a * sc for a in range(4)])
    ax.set_xticklabels([str(1 + a) for a in range(4)])
    ax.set_yticks([0, sc * 2.2])
    ax.set_yticklabels(["3", "4"])
    ax.set_xlabel(r"$x_2$")
    ax.set_ylabel(r"$x_3$")
    # key for the inner coordinates, drawn once, enlarged
    kx, ky, ks = 0.2 * sc, sc * 2.2 * 0.62, 0.62
    key = [(kx + ks * x, ky + ks * 2.2 * y) for x, y in tri]
    ax.add_patch(Polygon(key, closed=True, fc=C_POLY, ec=C_EDGE, lw=0.6))
    ax.scatter([kx + ks * x for x, y in S3], [ky + ks * 2.2 * y for x, y in S3],
               s=6, c=C_ACH, zorder=3)
    o = 0.35
    ax.annotate("", xy=(kx + ks * 3.6, ky - o), xytext=(kx - o, ky - o),
                arrowprops=dict(arrowstyle="->", lw=0.5))
    ax.annotate("", xy=(kx - o, ky + ks * 2.2 * 1.6), xytext=(kx - o, ky - o),
                arrowprops=dict(arrowstyle="->", lw=0.5))
    ax.text(kx + ks * 3.7, ky - o, r"$x_4$", va="center", fontsize=8)
    ax.text(kx - o, ky + ks * 2.2 * 1.7, r"$x_5$", ha="center", fontsize=8)
    ax.text(kx + ks * 1.5, ky - 0.8, r"inner $\Koz(3)$", ha="center",
            va="top", fontsize=7.5)
    ax.set_xlim(-2.0, 3 * sc + 2.0)
    ax.set_ylim(-1.6, sc * 2.2 + 1.6)
    ax.set_aspect("equal")
    for s in ("top", "right"):
        ax.spines[s].set_visible(False)
    ax.set_title(r"$\Koz(3;0,2)\cong\Koz(3)\times\Koz(3)$: $%d/%d$"
                 % (len(A), len(A) + len(B)), pad=3)
    save(fig, "fig-koz3-d02-product")


# ================================================================ Fig 6
def fig_n2():
    cases = [[0, 0], [0, 1], [0, 0, 1], [0, 1, 2]]
    fig = plt.figure(figsize=(5.6, 1.9))
    xs = [0.0, 0.20, 0.42, 0.68]
    ws = [0.12, 0.15, 0.20, 0.30]
    for k, d in enumerate(cases):
        free, A, B, Q, fix = koz_data(2, d)
        note("fig-koz2: Koz(2;%s): coords %s, fixed %s; %d achievable of %d "
             "lattice points" % (dstr(d), free, fix, len(A), len(A) + len(B)))
        if len(free) == 3:
            ax = fig.add_axes([xs[k], 0.02, ws[k], 0.9], projection="3d")
            draw3d(ax, Q, A, B, [flab(i) for i in free], elev=20, azim=-55,
                   ms=14)
            ax.set_box_aspect((1, 1, 1))
            for setter, i in ((ax.set_xticks, 0), (ax.set_yticks, 1),
                              (ax.set_zticks, 2)):
                vals = sorted({p[i] for p in A})
                setter(vals)
        elif len(free) == 2:
            ax = fig.add_axes([xs[k], 0.18, ws[k], 0.62])
            poly2d(ax, Q)
            dots2d(ax, A, B, ms=14)
            x0, x1 = min(p[0] for p in A), max(p[0] for p in A)
            y0, y1 = min(p[1] for p in A), max(p[1] for p in A)
            ax.set_xlim(x0 - 0.5, x1 + 0.5); ax.set_ylim(y0 - 0.5, y1 + 0.5)
            ax.set_xticks(range(x0, x1 + 1)); ax.set_yticks(range(y0, y1 + 1))
            ax.set_aspect("equal")
            for s in ("top", "right"):
                ax.spines[s].set_visible(False)
            ax.set_xlabel(flab(free[0]), labelpad=1)
            ax.set_ylabel(flab(free[1]), labelpad=1)
        else:  # dim 1
            ax = fig.add_axes([xs[k], 0.40, ws[k], 0.2])
            v = [p[0] for p in A]
            ax.plot([min(v), max(v)], [0, 0], color=C_EDGE, lw=0.8)
            dots2d(ax, [(x, 0) for x in v], [], ms=14)
            ax.set_yticks([]); ax.set_xticks(v)
            ax.set_xlim(min(v) - 0.5, max(v) + 0.5)
            for s in ("top", "right", "left"):
                ax.spines[s].set_visible(False)
            ax.set_xlabel(flab(free[0]), labelpad=1)
        ttl = r"$\Koz(2;%s)$" % dstr(d)
        fig.text(xs[k] + ws[k] / 2, 0.97, ttl + r"\ \ $%d/%d$"
                 % (len(A), len(A) + len(B)), ha="center", va="top")
    save(fig, "fig-koz2-small-rank")


# ================================================================ Fig 7
def fig_mu(ns=(5, 6, 7)):
    fig, axs = plt.subplots(1, len(ns), figsize=(5.8, 2.25), sharey=True)
    for ax, n in zip(axs, ns):
        S = S_KK(n)
        c2, c3 = binom(n, 2), binom(n, 3)
        mult = {}
        for s in S:
            mult[(s[2], s[3])] = mult.get((s[2], s[3]), 0) + 1
        lat = [(a, b) for a in range(c2 + 1) for b in range(c3 + 1)
               if b * c2 <= a * c3]
        miss = [p for p in lat if p not in mult]
        ax.add_patch(Polygon([(0, 0), (1, 0), (1, 1)], closed=True,
                             fc=C_POLY, ec=C_EDGE, lw=0.7, zorder=0))
        mx = max(mult.values())
        pts = sorted(mult)
        sizes = [3 + 40 * (mult[p] / mx) ** 0.7 for p in pts]
        if miss:
            ax.scatter([a / c2 for a, b in miss], [b / c3 for a, b in miss],
                       s=2.5 if n > 5 else 7, facecolors="white",
                       edgecolors=C_NON, linewidths=0.4, zorder=2)
        ax.scatter([a / c2 for a, b in pts], [b / c3 for a, b in pts],
                   s=sizes, c=C_ACH, alpha=0.75, linewidths=0, zorder=3)
        # Kruskal--Katona boundary and its continuous limit mu3 = mu2^{3/2}
        xs = np.linspace(0, 1, 200)
        ax.plot(xs, xs ** 1.5, color="0.35", lw=0.7, ls="--", zorder=4)
        # discrete centroid of S_n and centroid of Koz(n), in (mu2, mu3)
        g2 = np.mean([s[2] for s in S]) / c2
        g3 = np.mean([s[3] for s in S]) / c3
        ax.scatter([g2], [g3], marker="*", s=70, c="black", zorder=6,
                   linewidths=0)
        ax.scatter([(n - 1) / n], [(n - 2) / n], marker="D", s=22,
                   facecolors="white", edgecolors="black", linewidths=0.8,
                   zorder=6)
        ax.set_xlim(-0.03, 1.03); ax.set_ylim(-0.03, 1.03)
        ax.set_aspect("equal")
        ax.set_xticks([0, 0.5, 1]); ax.set_yticks([0, 0.5, 1])
        ax.set_xticklabels(["0", r"$\frac12$", "1"])
        ax.set_yticklabels(["0", r"$\frac12$", "1"])
        for s in ("top", "right"):
            ax.spines[s].set_visible(False)
        ax.set_xlabel(r"$\mu_2=x_2/\binom{%d}{2}$" % n, labelpad=1)
        ax.set_title(r"$n=%d$: $|S_{%d}|=%d$" % (n, n, len(S)), pad=3)
        note("fig-mu-projection: n=%d: |S_n|=%d; %d distinct (f2,f3) images of "
             "S_n among %d lattice points of the projected triangle (%d missed);"
             " max fibre %d; discrete centroid (mu2,mu3)=(%.4f,%.4f), Koz(n) "
             "centroid (%.4f,%.4f)" % (n, len(S), len(mult), len(lat),
                                      len(miss), mx, g2, g3, (n - 1) / n,
                                      (n - 2) / n))
    axs[0].set_ylabel(r"$\mu_3=x_3/\binom{n}{3}$")
    h = [plt.Line2D([], [], ls="", marker="o", ms=4, mfc=C_ACH, mec=C_ACH,
                    alpha=0.75, label=r"$(x_2,x_3)$ of an $f$-vector (size $\sim$ fibre)"),
         plt.Line2D([], [], ls="", marker="o", ms=3.5, mfc="white", mec=C_NON,
                    label=r"lattice point not hit"),
         plt.Line2D([], [], color="0.35", ls="--", lw=0.7,
                    label=r"$\mu_3=\mu_2^{3/2}$"),
         plt.Line2D([], [], ls="", marker="*", ms=7, mfc="black", mec="black",
                    label=r"centroid of $S_n$"),
         plt.Line2D([], [], ls="", marker="D", ms=4, mfc="white", mec="black",
                    label=r"centroid of $\Koz(n)$")]
    fig.legend(handles=h, loc="lower center", ncol=3, frameon=False,
               bbox_to_anchor=(0.5, -0.17), columnspacing=1.2,
               handletextpad=0.3)
    save(fig, "fig-mu-projection")


# ================================================================ Fig 8
def count_S(n):
    @lru_cache(None)
    def c(k, x):  # number of completions given f_k = x
        if k == n:
            return 1
        return sum(c(k + 1, y) for y in range(upper_shadow_bound(x, k) + 1))
    return c(1, n) if n >= 1 else 1


def count_L(n):
    @lru_cache(None)
    def c(k, x):  # lattice chains x/C(n,k) >= y/C(n,k+1) >= ... >= 0
        if k == n:
            return 1
        ub = (x * binom(n, k + 1)) // binom(n, k)
        return sum(c(k + 1, y) for y in range(ub + 1))
    return c(1, n)


def fig_fraction(nmax=11):
    ns = list(range(1, nmax + 1))
    S = [count_S(n) for n in ns]
    L = [count_L(n) for n in ns]
    for n in range(1, 8):
        assert S[n - 1] == len(S_KK(n))
    for n in (3, 4, 5, 6):   # DP count == Sage integral_points of conv(V)
        V = [[binom(n, k) if k <= j else 0 for k in range(2, n + 1)]
             for j in range(1, n + 1)]
        assert L[n - 1] == len(Polyhedron(vertices=V).integral_points()), n
    note("fig-fraction: n, |S_n|, #lattice points of Koz(n), ratio:")
    for n, s, l in zip(ns, S, L):
        note("   %2d %22d %24d   %.6g" % (n, s, l, s / l))
    fig, (a1, a2) = plt.subplots(1, 2, figsize=(5.6, 2.1))
    a1.semilogy(ns, L, "o", mfc="white", mec=C_NON, mew=1.0, ms=4,
                label=r"lattice points of $\Koz(n)$")
    a1.semilogy(ns, S, "o", c=C_ACH, ms=3.5, label=r"$|S_n|$")
    a1.set_xlabel(r"$n$"); a1.set_xticks(ns)
    a1.legend(frameon=False, loc="upper left")
    a2.semilogy(ns, [s / l for s, l in zip(S, L)], "o-", c=C_ACH, ms=3.5,
                lw=0.6)
    a2.set_xlabel(r"$n$"); a2.set_xticks(ns)
    a2.set_ylabel(r"$|S_n|\,/\,\#(\Koz(n)\cap\mathbb{Z}^{n+1})$")
    for a in (a1, a2):
        for s in ("top", "right"):
            a.spines[s].set_visible(False)
    fig.subplots_adjust(wspace=0.4)
    save(fig, "fig-fraction-achievable")


ONLY = sys.argv[1:]    # names of figure functions to run; empty = all

if ONLY:  # e.g. `sage code/oneoff/ff_pictures.py fig_koz3_02`; counts.txt is left alone
    for name in ONLY:
        globals()[name]()
elif True:  # sage runs scripts with __name__ != "__main__"
    fig_koz3()
    fig_koz4()
    fig_slices(4, [0, 0], "fig-koz4-d00-slices", r"$x_4$")
    fig_koz3_01()
    fig_koz3_02()
    fig_n2()
    fig_mu()
    fig_fraction()
    with open(os.path.join(OUT, "counts.txt"), "w") as fh:
        fh.write("# generated by code/oneoff/ff_pictures.py\n")
        fh.write("\n".join(COUNTS) + "\n")
