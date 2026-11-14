# lean/ — formalisation of the exterior-convex series

Lean 4 / Mathlib formalisation of the mathematics of this project. Started 2026-09-10 on article 1's
vertex-structure section; it now covers two layers of article 1 and is being extended to article 2.

## Layout, reorganised 2026-09-16

One Lake library, `ExteriorConvex`, with subdirectories grouped **by mathematics rather than by
article** — deliberately, because the first group is shared:

| directory | contents | used by |
|---|---|---|
| `ExteriorConvex/Spine/` | order ideals and `f`-vectors, local LYM, Kozlov's theorem, the sumset identity, the main theorem, the permissive variant | article 1 §§4–6 and §5.1, **and article 2**, whose `𝓕_n` and `FF(d⃗)` are literally these objects |
| `ExteriorConvex/Vertices/` | the vertex criterion, the extremal matrix for both leg vectors, the vertex count | article 1 §9 and Appendix A |
| `ExteriorConvex/Counting/` | the two statistics, the joint-distribution matrix, Alexander duality, the chaining/transfer layer, the `δ = 0` exact degrees (both halves), the proper layer, the constant-gap recurrence | article 2 §§4–9 (rungs A, B, C1, C2, D1, D2, D4, D3a, D3b, D3c, D3d, D3e **done** 2026-09-16/18, all tabulated below — **the article-2 plan is complete**. Never targets: C3, `lem-joint`, `lem-lexproper`, the algebra of `def-setup`) |

Naming the directories after the articles was considered and rejected: `Spine/` is used by both, so
article-numbered names would have misdescribed the dependency structure from day one. Renaming the
*library* was also rejected — the library name is the root namespace, so it appears in the full name
of every declaration, and changing it would churn every import and every `#print axioms` invocation
for no gain. Subdirectories under one library is what Mathlib itself does.

Two files were also renamed for sense in the same pass: `Kozlov1.lean` → `Spine/KozlovThm.lean`
(Kozlov's theorem) and `Kozlov.lean` → `Vertices/ExtremalMatrix.lean` (the extremal matrix). The two
names differing by a digit had been a standing trap.

**Paths in dated `LOGBOOK/` entries were rewritten by `92-code/move_tracked.py` when the files moved,
so an entry from before 2026-09-16 may show the new path.** The entry's date still says when the work
happened; only the path was updated so the link still resolves.

**Read `working-notes/formalization-bridge-lemma.org` first** for why this is possible at all: the
project's two earlier surveys wrote §8 off as blocked by Mathlib's missing polytope theory, and that
verdict is wrong. §8.2–8.4 never needs a polytope as an object — every body there is
`convexHull ℝ S` for an explicit finite `S`, and "vertex" is `Set.extremePoints ℝ`.

**Status: rungs 1, 2 and 3 complete.** Every result of §8.2, §8.3 and §8.4 that is not a conjecture
is formalised: both extremal-matrix theorems, all five §8.3 propositions, `thm-kozlov-matrix`, and
`cor-vdesc` — the last both for a general leg vector with decreasing ratios and for the Kozlov
vector itself. Everything listed as *proved* below compiles
with no `sorry` and depends only on the three standard Mathlib axioms (`propext`,
`Classical.choice`, `Quot.sound`), checked with `lean_verify`.

**Since 2026-09-13 there is a second layer: §§4–6** (order ideals and `f`-vectors, local LYM,
Kozlov's theorem, the sumset identity and the main theorem), per
`working-notes/PLAN-formalise-rungs-1-4.org` — see the second table below for what it does and
does not carry. Same standard: no `sorry` anywhere, three standard axioms only.

**Since 2026-09-14, rung 5: §5.1** ("Properness, and the permissive convention") is formalised in
`lean/ExteriorConvex/Spine/Permissive.lean` — the permissive set `S_n⁺`, the `μ₁ ≤ 1` chain, Kozlov's theorem
in permissive form, the properness-is-a-facet identity (minus the dimension clause), and the
`f₁`-fibration `prop-permissive-fibres`, which until 2026-09-13 the manuscript stated without
proof. Same standard again; the only change to an existing file was dropping `private` from
`LYM.lean`'s four telescoping helpers (`muOf`, `muOf_of_le`, `muOf_of_gt`, `sum_mu_telescope`) so
rung 5 could reuse them — statements and proofs untouched. **`native_decide` is banned in this
development** (it would add the axiom `Lean.ofReduceBool`); in particular the manuscript's `n = 4`
census stays a Sage verification, deliberately.

## Files, in dependency order

| file | rung | contents | state |
|---|---|---|---|
| `lean/ExteriorConvex/Vertices/Bridge.lean` | 1 | `mem_extremePoints_convexHull_iff` (`lem-exposed-vertex`), `mem_extremePoints_add_iff` (`lem-vertexdecomp`) | **proved** |
| `lean/ExteriorConvex/Vertices/Windows.lean` | 2 | `exists_strictMax_two_iff` (the rank-two feasibility criterion), `thm_ones_windows` | **proved** |
| `lean/ExteriorConvex/Vertices/Simplex.lean` | 2 | the all-ones geometric layer; `thm_ones` about the Minkowski sum itself | **proved** |
| `lean/ExteriorConvex/Vertices/Binomial.lean` | 3 | `choose_ratio_lt`, `choose_ratio_pos_iff`, `choose_ratio_eq_zero` (`lem-binomial-ratio`) | **proved** |
| `lean/ExteriorConvex/Vertices/ExtremalMatrix.lean` | 3 | general-leg-vector layer (`ravA`, `ravA_succ`, `ravA_injOn`, `coefAt`, `value_diff_eq_sum`, `abel_sum`); all five §8.3 propositions; `extremal_matrix_iff` and `extremal_matrix_kozlov` | **proved** |
| `lean/ExteriorConvex/Vertices/Count.lean` | 3 | `cor-vdesc`: `vertices_eq_image`, `image_injOn`, `card_zeroPairs`, `card_vertices`, `card_vertices_kozlov` | **proved** |

### The §§4–6 layer (added 2026-09-13, session 23)

A second, independent layer per `working-notes/PLAN-formalise-rungs-1-4.org`: the combinatorial
spine of the paper, in the **degree-0-inclusive space** `Fin (n+1) → ℝ`. It deliberately does
*not* touch the files above, which live in the dropped space `Fin N → ℝ`; the bridge between the
two spaces is `eq:koz-as-ra`'s translation term and is **not formalised** (comment at `projIncl`
in `Complexes.lean` marks where it would go).

| file | rung | contents | state |
|---|---|---|---|
| `lean/ExteriorConvex/Spine/Complexes.lean` | 1 | `IsOrderIdeal`, `IsComplex`, `fEntry`, `fvec`, `Sset`, the five supporting facts, `shiftIncl`, `projIncl` | **proved** |
| `lean/ExteriorConvex/Spine/LYM.lean` | 2 | `lym` (`lem-lym`), `skel`/`skelSet`/`lymChain`, `hull_skel_eq` (`lem-mu`, both inclusions) | **proved**, minus `lem-mu`'s affine-independence clause (deliberately skipped, see file header) |
| `lean/ExteriorConvex/Spine/KozlovThm.lean` | 3 | `kozlov` (`thm-kozlov`), `skelComplex` and its face counts, `hull_Sset_eq` (`cor-facets` inclusively) | **proved**, minus `cor-facets`' facet-status clause and the `proj` form (see file header) |
| `lean/ExteriorConvex/Spine/Sumset.lean` | 4 | `ffvec`, `ffSet`, `ff_eq_sumset` (`prop-sumset`), `main` (`thm-main`), `main_chain` | **proved**, general `r` |
| `lean/ExteriorConvex/Spine/EdgeCases.lean` | — | `edge_case_r_one`, `Sset_one`, `edge_case_n_one` (`prop-edge-cases` parts 1, 3) | **proved**; parts 2/4 are non-statements; part 5's ingredient is now rung 5's `permissive_hull`, but the summand-by-summand statement itself (a permissive `ffSet` + a mirror of `Sumset.lean`) is **not formalised** |
| `lean/ExteriorConvex/Spine/Permissive.lean` | 5 | §5.1: `SsetPerm`, `e0`, `lymChainPerm`, `hull_skel_perm_eq` (`lem-mu-permissive`), `permissive_hull`/`hull_SsetPerm_eq` (`prop-permissive-hull`), `rasimpB` + `properness_*` (`prop-properness-facet` in part), `relabel`/`fEntry_relabel`/`exists_relabel` + `permissive_fibres`/`fibre_eq`/`fibres_disjoint` (`prop-permissive-fibres`) | **proved**, minus the affine-independence/dimension clauses (see below) |

### The manuscript ↔ Lean correspondence

As of 2026-09-10 the printed proofs and the Lean proofs are deliberately the *same* proofs, not
merely proofs of the same statements. Where the formalisation found a shorter route, the manuscript
was rewritten to take it; where the manuscript is more general, the Lean carries the extra lemma
that closes the gap. The reconciliation is recorded in the session-20 LOGBOOK entry.

| manuscript | Lean | note |
|---|---|---|
| `lem-exposed-vertex` | `mem_extremePoints_convexHull_iff` | |
| `lem-vertexdecomp`(1) | `mem_extremePoints_add_iff` | Lean assumes the summands lie in the *generating* sets; the manuscript allows any points of the polytopes, and `mem_of_add_eq_of_mem_extremePoints` is what bridges the two |
| `lem-vertexdecomp`(2) | `eq_of_add_eq_of_mem_extremePoints` | the midpoint exchange; Lean does `r = 2`, the manuscript runs the same argument index by index |
| `rem-no-support-functions` | — | records that neither proof needs support functions, so the Ziegler citation is gone from §8 |
| `thm-ones` | `thm_ones` | |
| `rem-digraph-collapses` | `exists_strictMax_two_iff` | the manuscript remark *is* the Lean lemma: three explicit cases, no digraph, nothing assumed about the windows |
| `lem-binomial-ratio` | `choose_ratio_lt` etc. | in `Binomial.lean` |
| `prop-row-below` | `prop_row_below_geom` | the `i = d` case whose manuscript proof was broken |
| `prop-col-beyond` | `prop_col_beyond_geom` | the large-positive-weight construction |
| `prop-diagonal` | `prop_diagonal_geom`, `wDiag_unique_max` | one threshold functional, one lemma applied twice with the same cut `p = d+t` — the manuscript now states it that way too |
| `prop-adjacent` | `prop_adjacent_upper`, `prop_adjacent_lower`, `prop_adjacent_upper_geom` | both summands cross the *same* coordinate; no partial sums, in either version |
| `prop-below-diagonal` | `prop_below_diagonal` | summation by parts (`abel_sum`) |
| `prop-gapK` | `prop_gapK_geom` | the explicit functional, private blocks at ±1; both versions fix `δ` at the midpoint, so `(1+δ)ρ_j = (ρ_{t+1}+ρ_j)/2` |
| `thm-kozlov-matrix` | `extremal_matrix_iff`, `extremal_matrix_kozlov` | assembly |
| `cor-vdesc` (§8.4) | `card_vertices`, `card_vertices_kozlov` | in `Count.lean` |

For the §§4–6 layer (all in the inclusive space; every "proved" below checked with `lean_verify`,
axioms `propext`/`Classical.choice`/`Quot.sound` only):

| manuscript | Lean | note |
|---|---|---|
| `def-complex` (order ideal, `𝒟_n`) | `IsOrderIdeal` | empty order ideal included, per the manuscript's 2026-09-13 convention |
| `def-complex` (complex, `𝒮_n`, convention (iii)) | `IsComplex` | |
| `eq:complex` (`f_j`) | `fEntry` (ℕ-valued), `fvec` (the point of `ℝ^{n+1}`) | cast once, in `fvec` |
| `def-proper` / `eq:proper` (`S_n`) | `Sset`, `Sset_finite`, `Sset_nonempty` | plus the `f₀` split (`fEntry_zero`, `fEntry_empty`) and properness (`fEntry_one`) |
| `def-shift` | `shiftIncl` | a `LinearMap`, as the manuscript stresses |
| `proj` (§ Notation) | `projIncl` | defined only; the `eq:koz-as-ra` seam is deliberately open |
| `lem-lym` | `lym` | manuscript's range hypotheses kept but unused — Mathlib's local LYM needs only `j+1 ≠ 0` |
| `eq:skeleton` (`F̃_j`) | `skel`, `skelSet` | inclusive: leading `1` kept |
| `lem-mu` | `lymChain`, `hull_skel_eq`, `convex_lymChain` | **without** the affine-independence / `(n−1)`-simplex clause |
| `thm-kozlov` | `kozlov` (+ `Sset_subset_lymChain`, `skelComplex`, `fvec_skelComplex`) | hypothesis `1 ≤ n` as printed |
| `def-kozsimplex` / `cor-facets` | `hull_Sset_eq` | the H-description of `conv(S_n)` inclusively; **not** the `proj` form, **not** the "exactly the facets" clause |
| `def-ffvector` / `eq:ffvector` | `ffvec`, `ffSet` | |
| `prop-sumset` (combinatorial half) | `ff_eq_sumset` | the algebraic half (`prop-splitting`/`prop-dictionary`) is **not formalised** |
| `thm-main` | `main`, `main_chain` | the "equivalently, by `prop-sumset`" form; **finding:** none of `n ≥ 1`, `r ≥ 1`, `0 = d₁ ≤ ⋯ ≤ d_r`, `N = n + d_r` is needed |
| `prop-edge-cases`(1) | `edge_case_r_one`, `ffSet_r_one`, `shiftIncl_zero` | |
| `prop-edge-cases`(3) | `edge_case_n_one`, `Sset_one` | |
| `prop-edge-cases`(2),(4) | — | not statements (assessment note §"Part by part"); no Lean, deliberately |
| `prop-edge-cases`(5) | — | its ingredient `prop-permissive-hull` is now formalised (below); the summand-by-summand statement itself is **not** — it needs a permissive `ffSet` and a mirror of `Sumset.lean`, mechanical but absent |
| `prop-dictionary`, `def-sr-ideal`, `prop-splitting`, `thm-kk` | — | the algebra/dictionary layer, outside rungs 1–4 |

For the §5.1 layer (rung 5, `Permissive.lean`, added 2026-09-14, session 24; every "proved"
checked with `lean_verify`, axioms `propext`/`Classical.choice`/`Quot.sound` only):

| manuscript | Lean | note |
|---|---|---|
| `eq:Splus` (`S_n⁺`) | `SsetPerm`, `SsetPerm_finite`, `Sset_subset_SsetPerm` | `f`-vectors of *non-empty* order ideals |
| `e₀` (the vertex properness removes) | `e0`, `e0_mem_SsetPerm`, `fvec_singleton_empty`, `skel_zero` | `skel n 0 = e₀`, which lets the permissive vertex family be `skel n '' Icc 0 n` |
| `lem-mu-permissive` | `lymChainPerm`, `hull_skel_perm_eq`, `convex_lymChainPerm` | **without** the affine-independence / `n`-simplex clause, same as `lem-mu`'s treatment; the proof is `lem-mu`'s telescoping started at `j = 0`, with `λ₀ = 1 − μ₁` the weight on `e₀` |
| `prop-permissive-hull` | `permissive_hull`, `hull_SsetPerm_eq`, `hull_SsetPerm_eq_rasimpB` | the `⊆` half works because `lym` was stated for **order ideals** — the manuscript's parenthetical "(which assumes only that Δ is an order ideal)" is confirmed true of the Lean development |
| `prop-properness-facet` | `rasimpB`, `skel_image_Icc`, `rasimpB_eq_insert_hull`, `rasimpB_eq_lymChainPerm`, `properness_valid`, `properness_tight_face` | the identity `eq:permissive-simplex`, the validity of `x₁ ≤ n`, and that its tight face is exactly `conv(S_n)`; **not** the "is a facet" (codimension-one) clause — dimension talk resting on the skipped affine-independence clauses, same precedent as `cor-facets`. `∠(b̄)` itself is not defined in Lean: `rasimpB` is the 0-indexed inclusive reading the proposition itself fixes |
| `prop-permissive-fibres` | `permissive_fibres`, `fibre_eq`, `fibres_disjoint`; machinery `relabel`, `fEntry_relabel`, `fvec_relabel`, `isOrderIdeal_relabel`, `support`, `card_support`, `subset_support`, `exists_relabel`, `iotaIncl`; degeneration `Sset_zero`, `fibre_zero` | **the rung's main prize** — stated without proof in the manuscript until 2026-09-13. The new lemma is relabelling invariance of `f`-vectors along `Fin k ↪ Fin n` (`Finset.map`); the `k = 0` case needs no special-casing in Lean |
| `n = 4` census (168/167/25, block sizes 1,1,2,5,16) | — | **deliberately not formalised**: kernel `decide` cannot survive `2^16` families, and `native_decide` would break the three-axioms property. Stays a Sage verification |

### The article-2 counting layer (rungs A–B, `Counting/`, added 2026-09-16/17, session 29)

Per `working-notes/PLAN-formalise-article2.org`: `def-stats`, `def-A`, `lem-alexander`,
`cor-persymmetry` and `prop-fnn2` from `articles/article-2/exterior-convex_article2_latest.org`. Everything
lives over ℕ-valued `f`-vectors (`fvecN : Fin (n+1) → ℕ`); article 2's `𝓕_n` is `Fn`, the
`f`-vectors of **order ideals** (convention (i), void family included — simpler than the
`IsComplex` convention the older files use, and load-bearing: `D_n` exchanges the void family and
the full simplex). Every "proved" checked with `lean_verify`: axioms
`propext`/`Classical.choice`/`Quot.sound` only.

| file | rung | contents | state |
|---|---|---|---|
| `lean/ExteriorConvex/Counting/Stats.lean` | A | `fvecN`, `Fn`, `top`, `indeg`, `Amat`, support condition, both corner entries | **proved** |
| `lean/ExteriorConvex/Counting/Duality.lean` | B | `dualIdeal`, `eq:alexander-f`, `Dvec`, the statistic conjugation, `Amat_persymmetric`, `SnF`, `Fcount`, `card_SnF_eq_Fcount`, `Sset_eq_image_SnF` | **proved** |

| manuscript (article 2) | Lean | note |
|---|---|---|
| `def-fn` (`𝓕_n`) | `Fn`, `mem_Fn`, `zero_mem_Fn`, `fullVec_mem_Fn`, `apply_le_choose_of_mem_Fn` | a `Finset` of ℕ-vectors; `fEntry_univ` gives the full simplex's entries |
| `def-stats` (`tp`, `indeg`) | `top` (ℤ-valued), `indeg` (ℕ-valued) | the boundary conventions are the honest values, not encodings: `top 0⃗ = −1`, `indeg (fullVec n) = n+1`; characterisations `top_eq_neg_one_iff`, `indeg_eq_succ_iff`, `le_indeg_iff` |
| `def-A` | `Amat` | **by counting, for all integer indices** (vanishes off the printed range); Linusson's `E^p(n,k)` never mentioned, per the plan |
| `def-A`, support + corners | `indeg_le_top_add_one` (every vector), `Amat_eq_zero_of_add_one_lt`, `Amat_corner_void`, `Amat_corner_full` | |
| `lem-alexander` (family level) | `dualIdeal`, `IsOrderIdeal.dual`, `dualIdeal_dualIdeal` | the involution needs no order-ideal hypothesis at all |
| `eq:alexander-f` | `fEntry_dualIdeal_add` (ℕ-safe additive form `f_j(Δ^∨) + f_{n−j}(Δ) = C(n,j)`), `fEntry_dualIdeal` | true for every family, by the explicit complementation bijection |
| `lem-alexander` (`D_n` on `𝓕_n`) | `Dvec`, `fvecN_dualIdeal`, `Dvec_mem_Fn`, `Dvec_Dvec`, `Dvec_Dvec_of_mem_Fn` | only the involution needs the entrywise bound `s(j) ≤ C(n,j)` (automatic on `𝓕_n`) |
| `eq:alexander-stats` | `indeg_Dvec`, `top_Dvec` | **finding:** both conjugations hold for *every* `s⃗ : Fin (n+1) → ℕ`, not only on `𝓕_n` — truncated ℕ-subtraction hands the strengthening over free; the manuscript's claim that the boundary conventions are "exactly what make the two extremes correspond" is confirmed by the case analysis (the empty-filter branch is `n − (−1) = n + 1`, on the nose) |
| `cor-persymmetry` | `Amat_persymmetric` | for **all** `(τ,ρ) ∈ ℤ²`, off-range classes matching emptily |
| `def-linusson` `F^n(m)` at `p = n` | `Fcount` | **by counting** — `#{s⃗ ∈ 𝓕_n : tp(s⃗) ≤ m}`; the recursion `thm-linusson` and `lem-joint` are deliberately **not formalised** (the plan's "computational shortcut, not a logical dependency") |
| `prop-fnn2` | `mem_SnF_iff`, `card_SnF_eq_Fcount` | hypothesis `n ≥ 1` exactly as printed — and genuinely necessary: `\|S_0\| = 1` while `F^0(−2) = 0` |
| — | `SnF`, `mem_SnF`, `SnF_subset_Fn`, `Sset_eq_image_SnF` | the ℕ-valued `S_n`, and the bridge identifying it with `Complexes.lean`'s real-valued `Sset` |

**What `card_SnF_eq_Fcount` does and does not certify.** It proves
`|S_n| = #{s⃗ ∈ 𝓕_n : tp(s⃗) ≤ n−2}` — the whole content of `prop-fnn2`'s proof. Reading that
right-hand side as Linusson's recursively-computed `F^n(n−2)` goes through `def-linusson` at
`p = n` (where `f₁ ≤ n` is automatic), which is the manuscript's own definition of `F`; the
*recursion* that computes it (`thm-linusson`) is outside the formal development, as the plan
prescribes.

### The article-2 chaining, transfer, structure and proper layers (rungs C1–D3, added 2026-09-17/18)

Per `working-notes/PLAN-formalise-article2.org` and `PLAN-formalise-D3-remaining.org`. Two
conventions run through all of it and are worth stating once. **Matrices are indexed by
`Fin (n+2)`**, with `tauOf k = k − 1` the dictionary to the manuscript's `τ ∈ {−1,…,n}`, so what is
proved is the printed matrix identity rather than an ad-hoc iterated sum. **And `Tmat` is total in
`δ : ℤ`** — the printed definition restricts to `δ ≥ 0`, but the formula needs no sign, and taking it
totally is what lets the counting identities hold for arbitrary, unsorted `d⃗`.

| file | rung | contents | state |
|---|---|---|---|
| `lean/ExteriorConvex/Counting/Chaining.lean` | C1 | the profile of an `f`-vector, the disjoint-window normal form, the water-filling clamp `greedySlice`, `phi_injOn_chained`, `chained_iff_gap`, `ffvec_eq_phi` | **proved** |
| `lean/ExteriorConvex/Counting/Transfer.lean` | C2 | `uVec`, `Tmat`, `Tprod`, `chainedTuples`, `ffSetN`, `Tmat_apply_eq_card`, `card_chainedTuples`, `card_ffSetN`, `cor-r1` | **proved**; the `\|FF\|` form conditional, see below |
| `lean/ExteriorConvex/Counting/Structure.lean` | D1, D4 | `truncVec`, `lem-A-structure`'s four entries, `Amat_superdiag_tauOf`, `lem-transfer-support` (`Tmat_pos_iff`), `prop-threshold` with its sharpness witness, `Pmat`/`prop-normalform`, and D4's eigenvalue layer | **proved**; "Perron" deliberately not, see below |
| `lean/ExteriorConvex/Counting/NilpotentReduction.lean` | refactor | the binomial reduction and the staircase corner evaluation, **generic** over an arbitrary matrix, vectors and nilpotency bound | **proved** |
| `lean/ExteriorConvex/Counting/Delta0.lean` | D2 | `Nmat`, `cBracket`, `delta0Poly`, `thm_delta0_degrees_improper` | **proved** |
| `lean/ExteriorConvex/Counting/Proper.lean` | D3a | `SnF_eq_filter_indeg`, `Apmat`, `upVec`, `Tpmat`, `properChainedTuples`, `ffSetPrN`, `card_properChainedTuples`, `card_ffSetPrN` | **proved**; the `\|FF_pr\|` form conditional |
| `lean/ExteriorConvex/Counting/ProperBlock.lean` | D3b | the invariant-block repair: `blockEmb`, `Bmat`, `uTilde`, `vecMul_Tpmat_zero_pow_dot_block`, `NBmat` and its nilpotence; also `lem-transfer-support`'s proper half (`Tpmat_pos_iff`) | **proved** |
| `lean/ExteriorConvex/Counting/ProperDegree.lean` | D3d | `uTilde_zero`, `cpBracket`, `delta0PolyPr`, `thm_delta0_degrees_proper` | **proved** |
| `lean/ExteriorConvex/Counting/ProperThreshold.lean` | D3c | the proper threshold `δ ≥ n−1`: `Tpmat_eq_vecMulVec_of_le` and its exactness, `properChainedTuples_eq_piFinset_iff`, the product-shaped sharpness set, and the `λ_pr` eigenvalue layer | **proved**; "Perron" deliberately not, as in D4 |
| `lean/ExteriorConvex/Counting/Recurrence.lean` | D3e | `prop-recurrence`, recurrence half: the generic Cayley–Hamilton sandwich, `TQ`/`TpQ`/`aSeq`/`apSeq`, degree + monicity + solved form, the constant-gap bridge to both counts, and the `δ = 0` charpoly cross-checks | **proved**; the `Cλ^r` growth half deliberately not (no Perron–Frobenius in Mathlib), see below |

| manuscript (article 2) | Lean | note |
|---|---|---|
| `lem-dictionary` | — | algebra (`𝔪^t ⊆ I`); **not a target**, as `def-setup` is not |
| `thm-chaining`, injectivity | `greedySlice_phi`, `phi_injOn_chained`, and `eq:water-filling` as `Qclamp`/`greedySlice` | proved by downward closure alone: no Kruskal–Katona, no algebra |
| `thm-chaining`, surjectivity | — | **rung C3, not a target**: open combinatorially, and its algebraic proof needs Amata–Crupi lex theory. Enters as an explicit `Set.SurjOn` hypothesis wherever used |
| `rem-sorted` | `chained_iff_gap` | **finding:** `Monotone d` is needed *nowhere* in the argument — only in this dictionary, and there only in one direction. The absolute form implies the printed δ-form for every `d⃗` |
| `def-uT` | `uVec`, `Tmat`, `Tmat_apply_eq_card`, `uVec_eq_sum_row` | the entry-as-a-count dictionary is how every structural claim below is proved |
| `thm-main` | `card_chainedTuples` (**unconditional**), `card_ffSetN` (with `hsurj`) | the split is the point: the counting identity needs no hypothesis at all, so surjectivity cannot be assumed by accident. `ffSetN` is a fresh definition — `Spine/Sumset.lean`'s `ffSet` is the `IsComplex` variant, i.e. `FF_pr`, and using it would have given a true theorem about the wrong object |
| `cor-r1` | `sum_uVec`, `card_chainedTuples_one` | |
| `prop-threshold` | `chainedTuples_eq_piFinset_iff`, `card_chainedTuples_eq_pow_iff`, `Tmat_eq_vecMulVec_of_le`, `filter_not_chained_at_n` | the sharpness clause is a `Finset` *identity*, not a count: the violating pair at `δ = n` is provably the singleton `{(fullVec, 0⃗)}`. Needs no sortedness |
| `lem-transfer-support` | `Tmat_pos_iff`, and `Tpmat_pos_iff` for the proper half; helper `Amat_superdiag_tauOf` | **proved**, both halves. The entry is a sum of non-negative terms over `ρ > τ − δ`, and the largest `ρ` with `A[τ'][ρ] ≠ 0` is `τ' + 1`. **Findings:** (i) the proper half's hypothesis is `2 ≤ k'.val`, i.e. `τ' ≥ 1` — with `τ' ≥ 0` the statement is *false*, since the column `τ' = 0` vanishes identically for every `δ` while the right-hand side holds for large `δ`; this is exactly why the paper restricts to the principal block. (ii) `Tmat_pos_iff` lives in `Structure.lean`, not `Transfer.lean` where `Tmat` is defined, because the `⇐` half needs `Amat_superdiag` and `Structure` imports `Transfer`. (iii) `prop-delta0`'s triangularity falls out of it in one line, recorded as an `example` in `Delta0.lean`; the existing proof is unchanged, other files depend on it |
| `lem-A-structure` | `Amat_superdiag`, `Amat_diag`, `Amat_zero_zero`, `Amat_row_void_eq_zero`, `truncVec` | **finding:** `Amat_diag` holds for all `j ≤ n`, so the printed third claim `A_n[0][0] = 0` *is* the `j = 0` case of the second, `C(n,0) − 1 = 0`. One clause could go |
| `prop-normalform` | `Pmat`, `Pmat_pow_apply`, `Tmat_row_shift`, `Tmat_eq_Pmat_pow_mul`, `uVec_eq_single_vecMul`, `card_chainedTuples_normalform` | the printed `δ ≥ 0` here is **genuinely necessary**, unlike the threshold results: for `δ ≤ −(n+2)` the totalised `T_n(δ)` is the zero matrix, which no `P_nᵟ B_n` is. The `max(τ−δ,−1)` clamp becomes truncated ℕ-subtraction on the index, so no `max` appears |
| `prop-perron-threshold`, improper | `Tmat_eq_vecMulVec_of_le` (rank one), `Tmat_mulVec_onesCol_of_le` (`1⃗` an eigenvector), `eigenvalue_eq_zero_or_card` (over ℚ) | **the word "Perron" is not certified** — that this is the eigenvalue of largest modulus with a non-negative eigenvector needs Perron–Frobenius, absent from Mathlib. Jan's decision, 2026-09-17; the spectral-radius formulation is a stretch goal |
| `prop-delta0` | `Tmat_zero_blockTriangular`, `Tmat_zero_diag`, `Tmat_zero_superdiag` (`eq:delta0-superdiag`), `Nmat_pow_eq_zero` | |
| `thm-delta0-degrees`, improper | `cBracket_eq_zero_of_ge`, `cBracket_top`, `delta0Poly`, `delta0Poly_natDegree`, `delta0Poly_leadingCoeff`, `thm_delta0_degrees_improper` | an explicit `Polynomial ℚ` is exhibited, which is what the statement asserts. **Finding:** the printed `n ≥ 1` is *slack* for this half — it holds at `n = 0` too (degree 1, leading coefficient 1, count `r+1`). Kept, since the proper half needs it |
| `thm-proper` | `SnF_eq_filter_indeg`, `Apmat`, `upVec`, `Tpmat_apply_eq_card`, `card_properChainedTuples` (**unconditional**), `card_ffSetPrN` (with `hsurj`) | `S_n = {s⃗ ∈ 𝓕_n : indeg ≥ 2}` is why zeroing two columns implements properness, and the bridge to rung B's `IsComplex`-based `SnF` is the load-bearing lemma. `hsurj` covers `lem-lexproper` as well as `thm-chaining`'s surjectivity. **Finding: `n ≥ 1` was MISSING from the printed statement and is necessary** — at `n = 0`, `A′ = 0` while `\|FF_pr\| = 1`, so the theorem read `1 = 0`. Added to the manuscript 2026-09-18 |
| the invariant block (§8's "one adjustment") | `upVec_eq_zero_of_le_one`, `Tpmat_apply_eq_zero_of_le_one`, `blockEmb`, `Bmat`, `Bmat_diag`, `Bmat_superdiag`, `uTilde`, `vecMul_Tpmat_zero_pow_dot_block` | `T′(0)` is *not* unipotent on the full index set (eigenvalues `0,0,1,…,1`), so the reduction is restricted to `τ ∈ {1,…,n}`. **Findings:** it is *exactly* columns `−1,0` that vanish, and for **every** `δ`, not only `δ = 0`; and the block-support needs no hypothesis on the vector |
| `thm-delta0-degrees`, proper | `uTilde_zero` (`u′[1] = 1`), `cpBracket_top`, `delta0PolyPr_natDegree`, `delta0PolyPr_leadingCoeff`, `thm_delta0_degrees_proper` | verified against the *printed* polynomials of `tab-delta0-polys`: leading coefficients `1, 1, 3/2, 4, 125/6` for `n = 1..5` and degrees `n−1`. Here `n ≥ 1` is real — though note `natDegree = n − 1` is *degenerately true* at `n = 0` (zero polynomial, and ℕ-subtraction gives `0 − 1 = 0`); the leading-coefficient clause is what honestly carries the boundary |
| `prop-proper-threshold` | `properChainedTuples_eq_piFinset_iff`, `card_properChainedTuples_eq_pow_iff`, `ncard_ffSetPrN_eq_pow_iff` (with `hsurj`), `Tpmat_eq_vecMulVec_of_le`, `Tpmat_ne_vecMulVec_at_sub_two`, `filter_not_properChained_at_sub_two`, `vecMul_Tpprod_dot_of_saturated` | the printed `n ≥ 1` is **genuinely load-bearing in the iff** (at `n = 0` the proper chained locus is empty while `S_0^{r+1}` is not), unlike D1's threshold which carries no hypothesis. **Finding: the sharpness set is a product, not D1's singleton** — at `δ = n−2` the violating pairs are exactly `{fullVec} ×ˢ {t ∈ S_n : indeg t = 2}` (3 elements at `n = 3`, a singleton only at `n = 1`); the void family being improper is what widens D1's single pair to a class. Thresholds stated over ℤ, so the printed `n − 1` never ℕ-truncates; at `n = 1` it honestly reads `δ ≥ 0` and is still sharp (gap `−1` fails) |
| `prop-perron-threshold`, proper | `Tpmat_eq_vecMulVec_of_le` (rank one), `Tpmat_mulVec_onesCol_of_le` (`1⃗` an eigenvector, `n ≥ 1`), `eigenvalue_pr_eq_zero_or_card` (over ℚ) | same deliberate scope as the improper half: **the word "Perron" is not certified** (no Perron–Frobenius/spectral radius in Mathlib). **Finding:** the eigenvalue dichotomy needs no `n ≥ 1` — a non-zero eigenvalue counts the `indeg ≥ 2` class, whose non-emptiness certifies `n ≥ 1` by itself |
| `prop-recurrence`, recurrence half | `sandwich_charpoly_recurrence` (generic Cayley–Hamilton sandwich), `aSeq_recurrence`/`apSeq_recurrence`, with `TQ_charpoly_natDegree` (order `n+2`), `TQ_charpoly_coeff_top` (monic, so the recurrence *determines* the next term: `aSeq_solved`/`apSeq_solved`) and the bridge to the counts at constant gap (`Tprod_const_gaps`, `cast_card_chainedTuples_of_gaps_const`, `card_chainedTuples_constGap_recurrence`/`…_solved`, proper analogues; `|FF|`/`|FF_pr|` forms with the standing `hsurj` quantified over the rank window) | the recurrence is **unconditional on both sides** — the proper half needs no `n ≥ 1`, Cayley–Hamilton being universal. **Cross-checks:** `TQ_zero_charpoly` (`charpoly T(0) = (X−1)^{n+2}`, so at `δ = 0` the recurrence is `prop-delta0`'s vanishing `(n+2)`-th finite difference, `aSeq_zero_finite_difference`) and `TpQ_zero_charpoly` (`charpoly T′(0) = X²(X−1)^n` — *not* unipotent, rung D3b's two vanishing columns; the recurrence becomes the vanishing `n`-th difference of the twice-shifted sequence, `apSeq_zero_finite_difference`, matching D3d's degree `n−1`). Anchors: `verification-code/runs/lean-anchors/recurrence-lean-anchors-20260918.md` |
| `prop-recurrence`, growth half (`a_r ∼ Cλ^r`) | — | **deliberately not formalised**: needs the Perron root to be the dominant eigenvalue (Perron–Frobenius, absent from Mathlib), and unlike D4 there is no rank-one degeneracy below the threshold, so no honest cheap restatement exists. §10.1 records the boundary |
| `thm-poly-p`, `thm-asymptotics-p`, `thm-asymptotics-p-proper` | — | rest on Linusson's Theorem 5.3, cited not reproved; outside the development |

**Why everything numeric lives over ℚ.** From `Nmat` onward the matrices are cast once into ℚ and
stay there. Two reasons, and the second is the sharper one. `T_n(0) − I` cannot live over ℕ at all,
since truncated subtraction would silently give the wrong matrix. But ℕ-*division* would be worse:
`/` is total in Lean and `Nat` division floors, so `cpBracket 3 2 / 2!` would evaluate to `1` rather
than `3/2` — a **wrong leading coefficient that still typechecks and still builds**. The `/0` case is
harmless here (`x / 0 = 0` by `div_zero`, and every denominator is a factorial), but the flooring is
not, and it is invisible. Cast early.

### Rank-r pairwise reduction (article 3, added 2026-10-20)

Formalises `working-notes/kozlov-pairwise-reduction-direct-2026-10-20.org` (reviewed: ACCEPT WITH
FIXES). Window-system form in `Vertices/PairwiseReduction.lean` (no polytopes; namespace
`ExteriorConvex.Pairwise`), the polytope form in `Vertices/RankR.lean`. Hypotheses throughout:
`a` positive on `[1,n]` (`Pos`; the polytope theorems take `∀ s, 0 < a s`, as `ExtremalMatrix.lean`
does), weakly log-concave cross-multiplied `a i · a (i+2) ≤ a (i+1)²` (`WLC`), shifts `Monotone d`
(ties allowed), choices `1 ≤ j p ≤ n` for `p < r`, windows `d p + n ≤ N`.

| file | contents | state |
|---|---|---|
| `lean/ExteriorConvex/Vertices/PairwiseReduction.lean` | `Expose`, `Feasible`, `RCond`/`LCond`, Lemmas 1–6, Theorems 1 and 2 (window form), the strict-LC/Kozlov form | **proved** |
| `lean/ExteriorConvex/Vertices/RankR.lean` | `mem_extremePoints_sum_iff` (`lem-vertexdecomp` for `r` summands), functional ↔ coefficient-sequence bridge, Theorems 1, 2 and the Kozlov corollary for extreme points of `∑ₚ conv(vsetA a N (d p) n)` | **proved** |

| note | Lean | note |
|---|---|---|
| §1 vertex criterion, (L_p)/(R_p) | `expose_iff` | needs `j ≤ n` |
| Lemma 1 (ratios) | `lc_cross`, `lc_glob`; strict: `slc_cross`, `lc_glob_strict` | division-free |
| Lemma 2(a), 2(b) | `abel_prefix_neg`, `abel_suffix_pos` | by induction, no `abel_sum` needed |
| Lemma 5 (domination), (E) and (Λ) | `transfer_prefix`, `transfer_suffix` | weak shift inequalities suffice |
| Lemma 3 (m non-decreasing), tie clause | `chosen_mono`, `chosen_eq_of_tie` | |
| Lemma 6 (gluing) | `glue_step`, `glued` | **different route**: induction on `r`, cutting at `m q`; **no tie reduction** needed (the reviewer's reindexing worry disappears) |
| Theorem 1 (1 ⟺ 2 ⟺ 3) | `pairwise_reduction`, `feasible_iff_consecutive`; polytope: `vertex_iff_consecutive` | |
| Lemma 4 (locked ⟹ 0) | `locked_infeasible` (`Locked`) | positivity only |
| Theorem 2 (i)–(iii) | `feasible_iff_CF` (`CF`); polytope: `vertex_iff_CF` | **finding:** (i) follows from (ii)+(iii), `tie_of_not_locked` |
| Theorem 2 Cases A/B/C | `gadget_caseA`, `gadget_caseB`, `gadget_caseC`, `gadget_glue`, `pair_feasible_of_CF` | sufficiency is purely rank two, then Theorem 1 |
| Corollary (Kozlov at every rank) | `locked_iff_unit`, `CF_iff_KozCond` (`KozCond`), `kozLeg_slc`, `vertex_iff_kozlov` | for `RA(κ⃗(n); d⃗)`; the `eq:koz-as-ra` projection seam to `Koz(n; d⃗)` stays open, as elsewhere |
| Corollary (rank two, σ-form) | — | **not formalised** (would follow from `vertex_iff_CF` at `r = 2` plus an unwinding of `Locked` into σ-plateaus) |
| `lem-vertexdecomp`(2) for `r` summands (distinct 𝐣 give distinct vertices) | — | **not formalised**; needed only for counting |

## Rank-two facet description (article 3), added 2026-10-20

Theorem A(1) of `working-notes/kozlov-hdescription-proof-2026-10-20.org` (independently reviewed,
`review-hdescription-2026-10-20.org`). Set equalities only; the facet counts are **not** formalised.
Axioms of every main theorem: `propext`, `Classical.choice`, `Quot.sound`.

| file | rung | contents | state |
|---|---|---|---|
| `lean/ExteriorConvex/Facets/Chain.lean` | H1 | `co` (manuscript coordinates), `chainSet`, `angle`; Fact 1 for a general positive leg vector and shift: `chain_hull_eq` | **proved** |
| `lean/ExteriorConvex/Facets/RankTwo.lean` | H1 | `completeness` (Q_Θ ⊆ RA, positivity only), `validity` (RA ⊆ Q, log-concavity), `theoremA`, `theoremA_theta` | **proved** |
| `lean/ExteriorConvex/Facets/Specialise.lean` | H1 | `theoremA_lit` (article division form), `conj_kozlov_hrep2`, `kozlov_hrep2_theta`, `conj_ones_hrep` — article 1's two H-description conjectures, as printed | **proved**; facet counts not formalised |
| `lean/ExteriorConvex/Facets/ThetaForm.lean` | H2 | Theorem B (rank-r weighted Θ-form, Q_Θ = R): `validityB` (B1), `peel` (B2), `completenessB`, `theoremB`, `theoremB_theta` | **proved**; general real weights; facet count r·n (B3) and Corollaries C, D not formalised |
| `lean/ExteriorConvex/Facets/ThetaForm.lean` | H2 | Kozlov at every rank: `theoremB_kozlov` (distinct shifts from 0, gaps ≤ n−1, unit weights); rank-2 consistency check `QZ_rank_two` | **proved** |

Also: `lean/ExteriorConvex/ModuleKK/GreedyPQ.lean` (standalone until 2026-10-21, when it was moved into the library and imported; no namespace, so `sig` etc. are top level) proves
Proposition 3 (P and Q) of `working-notes/module-kruskal-katona-greedy-proof-2026-10-20.org` for the
recursively defined lex-shadow function `sig`. The link from `sig` to actual lex shadows was at first
on paper only (verified n ≤ 8); since the third batch it is `lexInit_upShadow` in
`ModuleKK/LexShadow.lean` (table below).

**Since 2026-11-09 the `ModuleKK/` results belong to Part V**, `article/exterior-convex_article5_draft_1.org`
("Module Kruskal–Katona"), not to Part III: Part III's section `sec-module-kk` and its appendix moved
there, labels unchanged (`thm-kk-rank1`, `lem-lex-rank1`, `prop-PQ`, `prop-greedy`, `thm-module-kk`, …).
The files and declarations are unchanged.

## Article 3: symmetry, lattice points, volume, the Koz bridge, the all-ones polytope (added 2026-10-21)

Five agent-written files, wired in and rebuilt by the coordinator 2026-10-21. Axioms of every main
theorem: `propext`, `Classical.choice`, `Quot.sound` (checked on the full library build).

| file | contents | state |
|---|---|---|
| `lean/ExteriorConvex/Symmetry/Beta.lean` | the affine involution β (`beta`, `betaEquiv`, `beta_involutive`), `beta_skel_low`/`_high` (F̃_j ↔ F̃_{n−1−j}), `beta_image_koz` (β(Koz(n)) = Koz(n)); Theorem 5: `beta_bijOn_latticePts_of_prime`, `beta_not_mapsTo_latticePts_of_not_prime` (explicit witness, via Lucas); `lattice_centroid_identity_of_prime` | **proved**; covariance clause, the continuous Theorem 4 and "β = Alexander duality on Φ" not formalised |
| `lean/ExteriorConvex/Lattice/LatticePoints.lean` | `latticePts_eq_intLYM` (Koz(n) ∩ ℤ = integer LYM chains), `latticeFinset`, counts 1, 2, 5, 20 for n = 1..4 by kernel `decide`; `chained_unique` (uniqueness of chained integer decompositions, every shift vector); `idp_two` (witness min(x, C(n,·)), Brändén–Solus), `lattice_sum_eq`, `idp` (IDP at every level r, d⃗ = 0) | **proved**; existence and additivity for d⃗ ≠ 0: see `ChainedExistence.lean` below; (housekeeping 2026-10-21: the duplicated box lemmas are gone; `Counting/Chaining.lean` now has `InBox` and `*_box` forms of Theorem A — the binomial box is all it needs — with the 𝓕_n versions as corollaries) |
| `lean/ExteriorConvex/Lattice/BetaBridge.lean` | `beta_latticePts_eq_image`: the two lattice-point sets agree | **proved** |
| `lean/ExteriorConvex/Lattice/Volume.lean` | `vdiff_det`: det of vertex differences on f₂..fₙ = ∏_{k=2}^n C(n,k); `freeProj_bijOn` (dropping f₀, f₁ is a lattice bijection of the plane); `affineIndependent_skel` (the simplex clause of `lem-mu`); `volume_kozProj` (Lebesgue volume = ∏C(n,k) · vol(corner simplex)) | **proved**; vol(corner simplex) = 1/m! and lattice-normalised volume as a notion are not in Mathlib, so NV = ∏C(n,k) is certified up to the definition |
| `lean/ExteriorConvex/Facets/KozBridge.lean` | `kozMap` (injective affine RA → Koz), `koz_eq_image`, `mem_koz_iff`, `proj_koz` (= `eq:koz-as-ra`); `extremePoints_koz_eq`, `vertex_iff_kozlov_koz` (V-description of Koz(n; d⃗) itself, every rank); `koz_hdesc` (H-description of Koz(n; d⃗), distinct shifts from 0, gaps ≤ n−1) | **proved**; general d⃗ of `cor-koz-hdesc`: see `EveryD.lean` below; vertex distinctness not formalised |
| `lean/ExteriorConvex/AllOnes/Hall.lean` | Corollary C of the all-ones note via Hall: `exists_choice_of_le_cover`, `le_cover_iff_exists_choice` (arbitrary finite windows), `lattice_points_eq_sumset` (lattice points of RA(𝟙; d⃗) = sumset); Theorem A validity inequality `dot_le_sum_sup'` | **proved**; the separation step and Lemma 1's set equality: see `TheoremA.lean` below. First independent check of the (unreviewed) all-ones note: nothing wrong found |
| `lean/ExteriorConvex/Lattice/ChainedExistence.lean` (added later 2026-10-21) | `thm-chained` for the Kozlov vector, every sorted d⃗: `exists_chained` (existence, by maximising the single functional ∑ᵢ i·‖shift^{dᵢ} pᵢ‖₁ instead of the paper's lexicographic minimiser), `chainedR_formula`/`waterFill_eq_Q` (water-filling), `chainedR_unique`, `chainedR_integral`; `cor_additivity`, `existsUnique_chained_lattice` (lattice points of Koz(n; d⃗) ↔ chained tuples of 𝓛_n); `cor_idp` (IDP of Koz(n; d⃗), every d⃗) | **proved**; general log-concave leg vector c not formalised; `ChainedR` (real) not yet linked to the integer `Chained` of `Counting/Chaining.lean` |
| `lean/ExteriorConvex/Facets/EveryD.lean` (added later 2026-10-21) | `cor_facets_every_d` (set-equality half: merge equal shifts into weights, cut into runs, Θ-form per run, zeros off the windows), `koz_hdesc_every_d` / `_local` / `'` (`cor-koz-hdesc` for every d⃗, as printed) | **proved**, under weaker hypotheses than printed (weak log-concavity, n ≥ 1, unsorted shifts); facet count n·s not formalised |
| `lean/ExteriorConvex/Vertices/RankTwoCorollary.lean` (third batch, 2026-10-21) | `rank2_lc` (`cor-rank2-lc`, both directions, no n ≥ 2 or g ≤ n−1 needed; σ renamed `legSlope` to avoid Mathlib's `slope`), `rank2_all_ones`, `rank2_g_zero`, `CF_rank2_iff`; `vertex_tuple_unique` (decomposition at a vertex is unique, r summands, no log-concavity), `extremePoints_eq_image`, `vertex_injOn_admissible`, `ncard_extremePoints` (#vertices = #admissible tuples) | **proved**; no closed vertex count |
| `lean/ExteriorConvex/Lattice/SimplexVolume.lean` (third batch) | `volume_lowerSimplex`, `volume_cornerSimplex` (= 1/m!, by induction + Tonelli; not in Mathlib), `volume_kozProj_eq` (vol = ∏C(n,k)/(n−1)!), `sum_sq_sub_freeProj` (the free-coordinate projection is an isometry of the plane) | **proved**; Hausdorff-measure form on the plane not formalised |
| `lean/ExteriorConvex/Symmetry/BetaMeasure.lean` (third batch) | `thm-beta-continuous`: `kozMeasure` (Lebesgue pushforward via the free chart), `abs_det_betaFree_linear` (= 1, from involutivity), `kozMeasure_map_beta`, `integral_kozMeasure_comp_beta`, `integral_mu_add_mu_reflect`, `centroid_identity` | **proved**; no covariance matrix defined (every integral is β-invariant) |
| `lean/ExteriorConvex/Lattice/ChainedGeneral.lean` (third batch) | `thm-chained` for any positive integer leg vector with (c₂..cₙ) log-concave: `exists_chainedC`, `chainedC_unique`, `chainedC_integral`, `cor_additivityC`, `cor_idpC`; the Kozlov statements re-derived (`*_of_general`); necessity: `no_chained_cBad` for c = (1,2,1,3,1,3), d⃗ = (0,1) | **proved**; the 101/70 counts not checked |
| `lean/ExteriorConvex/Lattice/ChainedBridge.lean` (third batch) | `chained_iff_chainedR` (real vs article 2's integer chaining agree on lattice points), `chained_unique_of_chainedR`, `existsUnique_Chained_lattice`, `cor_membership` | **proved**; `cor_membership`'s "only if" takes `thm-chaining` surjectivity as hypothesis `hPartII` |
| `lean/ExteriorConvex/ModuleKK/Greedy.lean` (third batch) | `prop_greedy` (`prop-greedy`), `greedy_admissible`, abstract `greedy_le_of_exchange` | **proved** (by direct induction, not the note's descent) |
| `lean/ExteriorConvex/ModuleKK/LexShadow.lean` (third batch) | `lexInit_upShadow` (Lemma 2 (F2)+(F4): `sig` = upper shadow of a lex-initial segment, again lex-initial), `exists_isLexInit`, `isLexInit_unique`, `kk_lex`, `thm_kk_rank1` (from Mathlib's colex `kruskal_katona` via φ s = {a : rev a ∉ s}), `module_shadow_ge_greedy`, `exists_lexInit_components` | **proved**; subspaces → monomial families and the module algebra not formalised |
| `lean/ExteriorConvex/Lattice/TransferEhrhart.lean` (third batch) | `unitriangular_poly`; `ncard_kozLattice` (lattice points of Koz(n; d⃗) = u·∏T(δ)·𝟙, every sorted d⃗), `ncard_dilateLattice`; `TL0_lower`/`_diag`/`_sup` (T₀ unitriangular, superdiagonal C(n,τ+1)); `ehrhart_koz`, `ehrhart_koz_exact` (Ehrhart polynomial of Koz(n), degree n−1, leading coefficient ∏C(n,k)/(n−1)! = det/(n−1)!) | **proved** for t ≥ 1; P(0) = 1, the rank-r display, and the f-vector analogue (needs `thm-chaining` surjectivity) not formalised |
| `lean/ExteriorConvex/Lattice/LectureHall.lean` (fourth batch, 2026-10-21) | `prop_lecture_hall` (any positive leg vector: ∠(c) ≅ the s-lecture hall simplex, s = (c_n,…,c₂), λ_i = p_{n+1−i}), `koz_lecture_hall`, `koz_lattice_bijOn`, counts 1, 2, 5, 20, 162 (n ≤ 5, kernel `decide`, finite raised `maxHeartbeats`), reversal `lhRev_bijOn`, converse `lectureHall_eq_image` | **proved**; "unimodular" formalised by its ingredients |
| `lean/ExteriorConvex/Lattice/SmallN.lean` (fourth batch) | `cor_small_n` (n ≤ 3, every shift vector, sorted or not), `ffSet_eq_lattice`, `ff3_equal_shifts` (`thm-n3-equal-shifts`), `two_mul_ncard_ff3`, `centroid_ff3`, `koz4_lattice_not_ff` | **proved**; three of the four non-ff points of Koz(4) not formalised |
| `lean/ExteriorConvex/Vertices/WorkedCounts.lean` (fourth batch) | `ex_plateau_vertices` (15), `ex_plateau_kozlov_vertices` (16), `ex_plateau_ones_vertices` (13), the three matrices of `ex-plateau` entry by entry; `cf_cast_iff` (decidable CF in ℕ, proved equivalent) | **proved** |
| `lean/ExteriorConvex/Lattice/EhrhartRankR.lean` (fourth batch) | `ehrhart_display` (rank-r display), `ehrhart_rankR` / `_all` (polynomial), `ehrhart_rankR_eval_zero`, `ehrhart_koz_eval_zero`, `ehrhart_koz'` (P(0) = 1), `prop_linear_coeff` (McMullen-free, via the row-shift identity `TL_row_shift`) | **proved**; degree/leading coefficient at rank ≥ 2 not formalised |
| `lean/ExteriorConvex/Symmetry/Covariance.lean` (fourth batch) | generic `cov_fixed`, `covF_fixed`; `cov_kozMeasure_beta`, `covF_latticePts_beta_of_prime` (covariance clauses, as LΣLᵀ = Σ) | **proved** |
| `lean/ExteriorConvex/Symmetry/AlexanderCore.lean` (fourth batch) | `thm-alexander-core` (1)–(3): `Dvec_bijOn_coreF`, `coreF_centroid`, `beta_eq_DvecR` (β = Dₙ on f_{n−1} = 0), `card_topF`, `centroid_reflect_bounds`, `centroid_top_bounds`, `centroid_index_bounds` | **proved** |
| `lean/ExteriorConvex/AllOnes/TheoremA.lean` (fifth batch, 2026-10-21) | the all-ones note's Theorem A in full: `polyP_eq_polyQ` (∑ₚ Δ_{W_p} = {y([N]) = r, y(J) ≤ f(J)}, any nonempty windows), `polyP_eq_polyQ'` (lower-bound form, `lowerCover`), `polyP_subset_polyQ`; Lemma 1 as a set equality `image_ra_eq_polyP` (D(RA(𝟙; d⃗)) + τ = P(d⃗), any d with dₚ + n ≤ N — unsorted, ties allowed); `mem_ra_iff` / `mem_ra_iff'`, `ra_eq_image_tailSum` (H-description of RA(𝟙; d⃗) in x-coordinates) | **proved**; Q ⊆ P via `dot_le_sum_sup'` + `geometric_hahn_banach_point_closed` (no general support-function lemma); Theorem B (facets) not formalised |
| `lean/ExteriorConvex/Lattice/ProductRegime.lean` (fifth batch) | `prop_product_regime` (all clauses, under `ProdGaps`: every pairwise shift difference ≥ n−1; `prodGaps_of_gaps` from the paper's gap form): `projAff` an affine bijection Koz(n; d⃗) → Koz(n)^r with inverse `glue`, compatible with ℤ → ℝ, `bijOn_projZ` on lattice points of every dilate; lattice count |𝓛ₙ|^r; Ehrhart polynomial L^r for all t ≥ 0 (`ehrhart_product`); volume vol(Koz(n))^r (`volume_uProj_eq`); `ncard_ffSet_prod` (|FF| = |Sₙ|^r **without** Part II's Prop. 42 — injectivity of `glue` suffices) | **proved**; "lattice-isomorphic" formalised as affine bijection + lattice bijection; volume measured in the curried free coordinates (the relabelling's measure preservation is not stated) |
| `lean/ExteriorConvex/Symmetry/Centroids.lean` (fifth batch) | `prop-centroid-simplex`: `mean_kozMeasure` (vertex average), `muOf_mean_kozMeasure` (μ_k = (n−k+1)/n, 1 ≤ k ≤ n), `bary_mean_kozMeasure` (λ_j = 1/n), `sum_index_bary`, `baryIndex_mean_kozMeasure` ((n+1)/2); `prop-pushforward` (1) `mean_indepShiftSum`, `cov_indepShiftSum` (product measure, independence), finite `meanF_covF_indepSum`; (2) against explicit hypotheses: `meanF_covF_ff`, `meanF_covF_lattice`, `mean_cov_uniform_productRegime` (via `IsUniformOn`, `chart_rigidity`); (3) `koz_zero_shifts`, `mean_cov_dilate` (r·c, r²Σ), `mean_cov_indepSum_zero` (r·c, rΣ) | **proved**; (2) is discharged in the product regime by the bridge file below; in (3) the uniform measure on r·Koz(n) is taken as the dilation push-forward |
| `lean/ExteriorConvex/Symmetry/PushforwardBridge.lean` (fifth batch) | `prop-pushforward` (2) unconditional in the product regime (`ProdGaps`): `pushforward_ff_productRegime`, `pushforward_lattice_productRegime` (n ≥ 3, inherited), `pushforward_koz_productRegime`; `sumShift_eq_glue`, `sumShift_injOn_koz`, `sumShift_bijOn_lattice`, `hull_Sset_eq_hull_skel` | **proved**; needs no Part II Prop. 42 |
| `lean/ExteriorConvex/Centroid/Dilation.lean` (2026-11-09) | `thm-centroid-dilation` (was `cor-centroid-dilation`, renamed 2026-11-10; before that `conj-centroid-dilation`): the mixing lemma for averages, centroids, second moments and covariances (`abs_avg_sub_avg_le`, `abs_centroid_sub_centroid_le`, `abs_secondMoment_sub_le`, `abs_cov_sub_cov_le`, constant 3); the abstract limit `tendsto_centroid_div`; the per-r rate `abs_centroid_div_sub_le`; `centroid_dilation_rate` and `centroid_dilation_tendsto` (∃K, eventually |c(Aᵣ)ₖ/r − cₖ| ≤ K/r, and the limit) | **partial**: the inclusion FF ⊆ Λᵣ and the box, the polynomiality of a(r) and L(r) with deg(L − a) < deg L (cor-zero-shift, Part II), and of Sₖ with leading coefficient vol·cₖ (Ehrhart) enter as hypotheses; the covariance limit only as the finite inequality; part (3) not formalised. Axioms: propext, Classical.choice, Quot.sound. Built in the library on jts-mini 2026-11-09 |
| `lean/ExteriorConvex/Kupreyeva/VolumeRatio.lean` (2026-11-09) | Kupreyeva's limit, the volume side: `area_R3`, `area_Delta3`, `q3_area_ratio` (q₃ = 4/5 as a ratio of Lebesgue measures); `integral_step` (one step of the iterated integral of `lem-rho`, general k); `rho_closed` (closed form of ρ(a,b)); `qn_closed` ((n−1)!·ρ(2,n) = (n+1)!/(2(2n−1)!!)) | **partial** (`lem-rho`): the volume of Rₙ as a measure is formalised at n = 3 only; the pseudo-power estimate, the counting lemma and the limit theorems are not formalised. Axioms: propext, Classical.choice, Quot.sound |

## What is *not* here

`lean/ExteriorConvex/Vertices/ExtremalMatrix.lean` builds the general-leg-vector layer and uses it for `prop-adjacent`, which needs no
sums at all: consecutive vertices differ by one basis vector, so *both* summands cross the
coordinate `⟨d+t⟩` and the proposition is the observation that they need its coefficient to have
opposite signs.

(Superseded 2026-10-21: this paragraph used to say that `conj-ones-hrep` and `conj-kozlov-hrep2`
remained unformalised as conjectures needing Minkowski–Weyl. Both are now theorems, formalised in
`Facets/Specialise.lean` as set equalities — no Minkowski–Weyl needed, since the proofs are direct
inclusions both ways.)

`cor-vdesc` needed one thing nothing before it did: `eq_of_add_eq_of_mem_extremePoints`, the
*uniqueness* half of `lem-vertexdecomp`. A vertex of a Minkowski sum decomposes in exactly one way —
proved by the midpoint/exchange argument, `x = ½(s+t') + ½(s'+t)` — and that is what makes
`(i,j) ↦ v_i + u_j` injective on the surviving pairs, hence what turns the classification into a
count.

## Three things this work gave back to the manuscript

All three are fixed in the manuscript as of 2026-09-10.  The first two were found while planning the
rungs, before any Lean was written; the third by an adversarial review of §8.3's *proofs* (as
opposed to its statements), run before starting rung 3:

1. `prop-kozlov-partial` (Proposition 47 of the previous draft) part (3) was **false as literally
   stated** — it omitted the qualifier `j ≤ m` and so contradicted part (1) of the same proposition
   at the entry `(i,j) = (n, m+1)`. A Lean case split cannot close over that. It is now four
   separate propositions, each with its own hypotheses.
2. `prop-gapK` said "let `Λ > 0` be large". Lean does not accept that. Working out what bound is
   actually needed showed that **none is**: `Λ = 1` works, because `u_j` already weakly beats `u_m`
   before any penalty is applied. The manuscript's functional is now completely explicit.
3. `prop-outside-block`'s proof was **broken**, though its statement was true. Its single
   construction covers only the sub-case `i < d`, `j ≤ m` (210/210 configurations pass there, 0/924
   elsewhere): at `i = d` the private-block buffer it relies on is an empty sum, so no `Γ` is ever
   "large enough", and for `j > m` the proof said only "the mirror argument" — which is a genuinely
   *different* construction, using a large **positive** weight on the second private block. It is
   now two propositions, `prop-row-below` and `prop-col-beyond`, with two proofs and a shared
   shaping lemma. Both constructions are checked as printed.

## Build

Same toolchain and Mathlib revision as `~/Repositories/commutator-varieties/LEAN`, whose built
Mathlib makes `lake exe cache get` cheap here.

```
cd lean && lake exe cache get && lake build
```

`.lake/` is gitignored.
