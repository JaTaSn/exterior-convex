# Ancillary files: Hilbert functions over the exterior algebra and f-vectors in higher rank II

These files accompany the arXiv version of the paper. They are not needed to read it. The same
material, kept current, is in the public repository
https://gitlab.liu.se/jansn19/exterior-convex (directories `lean/`, `verification-code/`, `articles/article-2/`).

## `lean/`

The Lean 4 + Mathlib development behind the "Against a proof assistant" item of the paper's section
"How the results were checked". It serves both papers of the series. `lean/README.md` is the
authoritative, declaration-by-declaration account of what is and is not formalised; the paper's
own account summarises it. To check it: install `elan`, then in `lean/` run `lake exe cache get`
and `lake build`. A clean build ends with `Build completed successfully`; `grep -rn sorry` finds
nothing, and `#print axioms` on the main declarations shows only `propext`, `Classical.choice` and
`Quot.sound`.

## `verification-code/`

Every script behind a computational claim in the series, with recorded outputs under `runs/`.
For this paper the central one is `linusson_ff_counting.py`: Linusson's recursion, the matrix
A_n, the transfer-matrix count, and an independent brute-force enumeration of the sumset. Run
`python3 linusson_ff_counting.py` for its self-validation (against Linusson's printed Tables 5 and
6, against brute force, and against the Macaulay2 lex-submodule counts). Scripts under `oneoff/`
are single-purpose checks named for what they check; each prints its own PASS/FAIL summary.
Python 3 alone suffices for the counting scripts; some others need SageMath or Macaulay2.

## `tables/`

Plain CSV, produced by `verification-code/oneoff/arxiv_anc_tables.py`, which before writing
recomputes every entry with n <= 4, r <= 2 and with n <= 3, r <= 3 by brute force and refuses to
write on any mismatch.

| file | contents |
|---|---|
| `ff-counts.csv` | `n, r, d, FF, FF_proper`: \|FF(n;d)\| and \|FF_pr(n;d)\| for 1 <= n <= 8, 1 <= r <= 4 and every gap vector with gaps 0..n+1 (larger gaps change nothing). `d` is space-separated with d_1 = 0; only the gaps matter. |
| `ff-constant-gap.csv` | `n, r, delta, FF, FF_proper` for d = (0, delta, ..., (r-1) delta), 1 <= n <= 8, 1 <= r <= 8, 0 <= delta <= n+1. |
| `joint-distribution-A_n.csv` | `n, top_tau, indeg_rho, A_n`: the nonzero entries of A_n = the joint distribution of (top, indeg) over F_n, 1 <= n <= 8. |
