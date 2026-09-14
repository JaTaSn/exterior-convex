# LEAN/ — formalisation of §8 (and now §§4–6) of article 1

Lean 4 / Mathlib formalisation of the vertex-structure section of
`article/exterior-convex_article1_latest.org`. Started 2026-09-10.

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
`ExteriorConvex/Permissive.lean` — the permissive set `S_n⁺`, the `μ₁ ≤ 1` chain, Kozlov's theorem
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
| `ExteriorConvex/Bridge.lean` | 1 | `mem_extremePoints_convexHull_iff` (`lem-exposed-vertex`), `mem_extremePoints_add_iff` (`lem-vertexdecomp`) | **proved** |
| `ExteriorConvex/Windows.lean` | 2 | `exists_strictMax_two_iff` (the rank-two feasibility criterion), `thm_ones_windows` | **proved** |
| `ExteriorConvex/Simplex.lean` | 2 | the all-ones geometric layer; `thm_ones` about the Minkowski sum itself | **proved** |
| `ExteriorConvex/Binomial.lean` | 3 | `choose_ratio_lt`, `choose_ratio_pos_iff`, `choose_ratio_eq_zero` (`lem-binomial-ratio`) | **proved** |
| `ExteriorConvex/Kozlov.lean` | 3 | general-leg-vector layer (`ravA`, `ravA_succ`, `ravA_injOn`, `coefAt`, `value_diff_eq_sum`, `abel_sum`); all five §8.3 propositions; `extremal_matrix_iff` and `extremal_matrix_kozlov` | **proved** |
| `ExteriorConvex/Count.lean` | 3 | `cor-vdesc`: `vertices_eq_image`, `image_injOn`, `card_zeroPairs`, `card_vertices`, `card_vertices_kozlov` | **proved** |

### The §§4–6 layer (added 2026-09-13, session 23)

A second, independent layer per `working-notes/PLAN-formalise-rungs-1-4.org`: the combinatorial
spine of the paper, in the **degree-0-inclusive space** `Fin (n+1) → ℝ`. It deliberately does
*not* touch the files above, which live in the dropped space `Fin N → ℝ`; the bridge between the
two spaces is `eq:koz-as-ra`'s translation term and is **not formalised** (comment at `projIncl`
in `Complexes.lean` marks where it would go).

| file | rung | contents | state |
|---|---|---|---|
| `ExteriorConvex/Complexes.lean` | 1 | `IsOrderIdeal`, `IsComplex`, `fEntry`, `fvec`, `Sset`, the five supporting facts, `shiftIncl`, `projIncl` | **proved** |
| `ExteriorConvex/LYM.lean` | 2 | `lym` (`lem-lym`), `skel`/`skelSet`/`lymChain`, `hull_skel_eq` (`lem-mu`, both inclusions) | **proved**, minus `lem-mu`'s affine-independence clause (deliberately skipped, see file header) |
| `ExteriorConvex/Kozlov1.lean` | 3 | `kozlov` (`thm-kozlov`), `skelComplex` and its face counts, `hull_Sset_eq` (`cor-facets` inclusively) | **proved**, minus `cor-facets`' facet-status clause and the `proj` form (see file header) |
| `ExteriorConvex/Sumset.lean` | 4 | `ffvec`, `ffSet`, `ff_eq_sumset` (`prop-sumset`), `main` (`thm-main`), `main_chain` | **proved**, general `r` |
| `ExteriorConvex/EdgeCases.lean` | — | `edge_case_r_one`, `Sset_one`, `edge_case_n_one` (`prop-edge-cases` parts 1, 3) | **proved**; parts 2/4 are non-statements; part 5's ingredient is now rung 5's `permissive_hull`, but the summand-by-summand statement itself (a permissive `ffSet` + a mirror of `Sumset.lean`) is **not formalised** |
| `ExteriorConvex/Permissive.lean` | 5 | §5.1: `SsetPerm`, `e0`, `lymChainPerm`, `hull_skel_perm_eq` (`lem-mu-permissive`), `permissive_hull`/`hull_SsetPerm_eq` (`prop-permissive-hull`), `rasimpB` + `properness_*` (`prop-properness-facet` in part), `relabel`/`fEntry_relabel`/`exists_relabel` + `permissive_fibres`/`fibre_eq`/`fibres_disjoint` (`prop-permissive-fibres`) | **proved**, minus the affine-independence/dimension clauses (see below) |

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

## What is *not* here

`Kozlov.lean` builds the general-leg-vector layer and uses it for `prop-adjacent`, which needs no
sums at all: consecutive vertices differ by one basis vector, so *both* summands cross the
coordinate `⟨d+t⟩` and the proposition is the observation that they need its coefficient to have
opposite signs.

Only `conj-ones-hrep` and `conj-kozlov-hrep2` remain unformalised, and those are conjectures — not
targets. They are also the two genuinely polyhedral statements in §8 (halfspace descriptions), so
they would need Minkowski–Weyl, which Mathlib does not have.

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
cd LEAN && lake exe cache get && lake build
```

`.lake/` is gitignored.
