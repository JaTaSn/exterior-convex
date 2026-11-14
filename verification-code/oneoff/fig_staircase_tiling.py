#!/usr/bin/env sage-python
"""fig_staircase_tiling.py -- the staircase tiling of Koz(3;0,1) (Part III, Theorem thm-staircase).
Changelog (reverse chronological):
  2026-11-09  Created, Claude-Code (jts-mini), at Jan's request ("would it be possible to draw a
              picture of the tiling?", review of Part III draft 5, item 16). Writes
              artefacts/ff-pictures/fig-koz3-d01-tiling.{pdf,png}.

Run with Sage's Python (Polyhedron for the faces and the checks):
    cd PROJ && sage code/oneoff/fig_staircase_tiling.py

The cells are computed from the definition in the paper, not typed in: for n = 3, d = (0,1) the
staircase indices are t = (1, 1+j, 4), j = 1, 2 (Corollary cor-rank2-volume), and
    C_t = sum_i shift^{d_i} conv{F_alpha_i, ..., F_beta_i},  alpha_i = t_{i-1}-d_i, beta_i = t_i-d_i,
with F_j = (1, 3, ..., 0) the vertices of Koz(3) in degree-0-inclusive coordinates. Asserted: the
cells have NV 27 and 9, their union is Koz(3;0,1) (equal volumes and every cell inside), and they
meet in the plane x_3 = 3 only.  Drawn in (x_2, x_3, x_4); x_0 = 1, x_1 = 4 throughout.
Colours: slots 1 and 2 of the validated categorical palette of the dataviz skill; each cell is also
labelled in text, so the colour is not the only cue.
"""
import os
import sys
from itertools import product
from sage.all import Polyhedron, QQ, factorial
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
import numpy as np

HERE = os.path.dirname(os.path.abspath(sys.argv[0]))
PROJ = os.path.abspath(os.path.join(HERE, "..", ".."))
OUT = os.path.join(PROJ, "artefacts", "ff-pictures")

plt.rcParams.update({
    "text.usetex": True, "font.family": "serif", "font.size": 9, "axes.labelsize": 9,
    "xtick.labelsize": 7, "ytick.labelsize": 7, "axes.linewidth": 0.6,
    "text.latex.preamble": r"\usepackage{amsmath,amssymb}\newcommand{\Koz}{\operatorname{Koz}}",
    "savefig.bbox": "tight", "savefig.pad_inches": 0.03,
})
C_EDGE = "#3a3f4b"
C_CELL = ["#2a78d6", "#eb6834"]          # categorical slots 1, 2

n, d = 3, (0, 1)
binom = lambda a, b: QQ(factorial(a) / (factorial(b) * factorial(a - b))) if 0 <= b <= a else QQ(0)
c = [binom(n, k) for k in range(n + 1)]
F = {j: [c[k] if k <= j else 0 for k in range(n + 1)] for j in range(1, n + 1)}
N = n + d[-1]


def shift(v, s):
    return [0] * s + list(v) + [0] * (N - n - s)


def face(alpha, beta, s):
    return Polyhedron(vertices=[shift(F[j], s) for j in range(alpha, beta + 1)])


cells = []
for j in (1, 2):
    t = (1, d[1] + j, N)
    C = face(t[0] - d[0], t[1] - d[0], d[0]) + face(t[1] - d[1], t[2] - d[1], d[1])
    cells.append((t, C))
koz = face(1, n, 0) + face(1, n, 1)


def proj(P):                                 # drop the constant x_0 = 1, x_1 = 4
    return Polyhedron(vertices=[v[2:] for v in P.vertices_list()])


K = proj(koz)
Cs = [proj(C) for _, C in cells]
nv = [C.volume() * factorial(C.dim()) for C in Cs]
assert K.dim() == 3 and all(C.dim() == 3 for C in Cs)
assert nv == [27, 9], nv
assert sum(C.volume() for C in Cs) == K.volume() == 6
assert all(C.intersection(K) == C for C in Cs)
common = Cs[0].intersection(Cs[1])
assert common.dim() == 2 and all(v[1] == 3 for v in common.vertices_list())


def facets3d(Q, offset=(0, 0, 0)):
    polys = []
    for f in Q.faces(2):
        vs = np.array([[float(x) for x in v] for v in f.vertices()]) + np.array(offset)
        m = vs.mean(axis=0)
        nrm = np.array([float(x) for x in f.ambient_Hrepresentation()[0].A()])
        u = vs[0] - m
        u /= np.linalg.norm(u)
        w = np.cross(nrm, u)
        w /= np.linalg.norm(w)
        polys.append(vs[np.argsort([np.arctan2((v - m) @ w, (v - m) @ u) for v in vs])])
    return polys


def panel(ax, gap, title):
    for k, C in enumerate(Cs):
        off = (0, gap * k, 0)
        ax.add_collection3d(Poly3DCollection(facets3d(C, off), facecolors=C_CELL[k],
                                             edgecolors=C_EDGE, linewidths=0.6, alpha=0.30))
        v = np.array([[float(x) for x in p] for p in C.vertices_list()]) + np.array(off)
        ax.scatter(v[:, 0], v[:, 1], v[:, 2], s=8, c=C_EDGE, depthshade=False)
    ax.set_xlim(3, 6); ax.set_ylim(0, 4 + gap); ax.set_zlim(0, 1)
    ax.set_xticks(range(3, 7)); ax.set_yticks(range(0, 5) if gap == 0 else range(0, 4)); ax.set_zticks([0, 1])
    ax.set_xlabel(r"$x_2$", labelpad=-6); ax.set_ylabel(r"$x_3$", labelpad=-6)
    ax.set_zlabel(r"$x_4$", labelpad=-7)
    ax.view_init(elev=20, azim=-30)
    ax.set_box_aspect((0.9, 1.1 + 0.25 * gap, 0.6), zoom=0.95)
    ax.tick_params(pad=-3)
    for axis in (ax.xaxis, ax.yaxis, ax.zaxis):
        axis.pane.set_facecolor((1, 1, 1, 0))
        axis.pane.set_edgecolor((0.85, 0.85, 0.85, 1))
        axis._axinfo["grid"]["color"] = (0.9, 0.9, 0.9, 1)
        axis._axinfo["grid"]["linewidth"] = 0.4
    ax.set_title(title, pad=0)


fig = plt.figure(figsize=(5.6, 2.5))
a1 = fig.add_axes([-0.03, 0.0, 0.52, 0.95], projection="3d")
a2 = fig.add_axes([0.47, 0.0, 0.52, 0.95], projection="3d")
panel(a1, 0.0, r"$\Koz(3;0,1)=C_{(1,2,4)}\cup C_{(1,3,4)}$")
panel(a2, 1.2, r"the cells pulled apart along $x_3$")
labels = [r"$C_{(1,2,4)}$, $\mathrm{NV}=27$", r"$C_{(1,3,4)}$, $\mathrm{NV}=9$"]
a2.text(3.6, 1.2, 1.45, labels[0], color=C_EDGE, ha="center", fontsize=8)
a2.text(5.6, 3.6 + 1.2, 1.45, labels[1], color=C_EDGE, ha="center", fontsize=8)
os.makedirs(OUT, exist_ok=True)
for ext, kw in (("pdf", {}), ("png", {"dpi": 220})):
    fig.savefig(os.path.join(OUT, "fig-koz3-d01-tiling." + ext), **kw)
print("cells:", [(t, [tuple(v) for v in C.vertices_list()]) for (t, _), C in zip(cells, Cs)])
print("NV:", nv, " vol(Koz(3;0,1)) =", K.volume(), " common facet:", common.vertices_list())
print("wrote fig-koz3-d01-tiling.{pdf,png}")
