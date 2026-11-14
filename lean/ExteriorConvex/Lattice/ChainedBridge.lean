/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The real chaining `ChainedR` is article 2's integer `Chained`, on lattice points

Links `Lattice/ChainedExistence.lean` (real chained tuples, `def-chained-points` of
`article/exterior-convex_article3_draft_4.org`, in the form "wherever summand `i` is
non-zero, summand `i+1` is full in every lower global degree") with
`Counting/Chaining.lean`'s `Chained` (article 2's `tp(s_i) + d_i < indeg(s_{i+1}) + d_{i+1}`,
used by `Lattice.chained_unique` in `Lattice/LatticePoints.lean`).

* `chained_iff_chainedR`: for tuples of lattice points of `Koz(n)` (`latticePts n`) and
  **sorted** `d⃗`, `Chained d (toN ∘ p) ↔ ChainedR d (castR ∘ p)`. (Sortedness is used in
  `←` only, to rule out `tp(p_i) = −1`; `→` holds for every `d⃗`.)
* `chained_unique_of_chainedR`: `Lattice.chained_unique` (sorted `d⃗`) re-derived from
  `Lattice.chainedR_unique` through the bridge, so the two uniqueness theorems are the same
  statement on lattice points.
* `existsUnique_Chained_lattice`: `cor-additivity`'s bijection with article 2's `Chained`:
  every lattice point of `Koz(n; d⃗)` is the shifted sum of exactly one `Chained` tuple of
  points of `𝓛_n`.
* `cor_membership` (`cor-membership`, "which lattice points are ff-vectors"):
  `x ∈ FF(n; d⃗)` iff every canonical part `waterFill n d x i` is an `f`-vector (`∈ S_n`).
  **Conditional**: the "only if" direction needs article 2's chaining reformulation
  (Part II, Thms 23 and 41 with Lemma 40: every ff-vector is the sum of a chained tuple of
  `f`-vectors), which is not formalised in this library (`Counting/Chaining.lean` formalises
  injectivity only; surjectivity routes through Amata–Crupi). It enters as the hypothesis
  `hPartII`, for the point at hand only. "If" is unconditional (`ff_eq_sumset`).

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Lattice.ChainedExistence

open Finset
open scoped Pointwise

namespace ExteriorConvex

namespace Lattice

variable {n : ℕ}

/-- **The bridge.** On tuples of lattice points of `Koz(n)` with sorted `d⃗`, article 2's
integer `Chained` (on the `ℕ`-images) is article 3's real `ChainedR` (on the real
images). -/
theorem chained_iff_chainedR (hn : 1 ≤ n) {r : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    {p : Fin r → Fin (n + 1) → ℤ} (hp : ∀ i, p i ∈ latticePts n) :
    Chained d (fun i => toN (p i)) ↔ ChainedR d (fun i => castR (p i)) := by
  have hcast : ∀ i m, ((toN (p i) m : ℕ) : ℝ) = castR (p i) m := by
    intro i m
    rw [castR_apply, ← toN_cast hn (hp i) m]; rfl
  constructor
  · intro h i j hij m m' hpos hle
    simp only at hpos ⊢
    have hpos' : 0 < toN (p i) m := by
      rw [← hcast] at hpos; exact_mod_cast hpos
    have h1 := le_top_of_pos hpos'
    have h2 := h hij
    simp only [hatTop, hatIndeg] at h2
    have hlt : m'.val < indeg (toN (p j)) := by omega
    have heq : toN (p j) m' = n.choose m'.val :=
      le_antisymm (toN_le_choose hn (hp j) m') (choose_le_of_lt_indeg hlt)
    rw [← hcast, heq]
  · intro h i j hij
    simp only [hatTop, hatIndeg]
    have hdij : d i ≤ d j := hd (Fin.le_def.mpr (by omega))
    by_contra hcon
    push Not at hcon
    have htop : 0 ≤ top (toN (p i)) := by omega
    obtain ⟨T, hT, hTpos⟩ := exists_apply_pos_of_top_nonneg htop
    have hind : indeg (toN (p j)) ≤ n := by
      have := top_le (toN (p i)); omega
    obtain ⟨m', hm', hlt⟩ := exists_apply_lt_choose_of_indeg_le hind
    have hfull := h hij T m' (by simp only; rw [← hcast]; exact_mod_cast hTpos) (by omega)
    simp only at hfull
    rw [← hcast] at hfull
    have : toN (p j) m' = n.choose m'.val := by exact_mod_cast hfull
    omega

/-- `Lattice.chained_unique` (for sorted `d⃗`) recovered from `Lattice.chainedR_unique`
via the bridge: the two uniqueness theorems agree on lattice points. -/
theorem chained_unique_of_chainedR (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {p q : Fin r → Fin (n + 1) → ℤ}
    (hp : ∀ i, p i ∈ latticePts n) (hq : ∀ i, q i ∈ latticePts n)
    (hcp : Chained d fun i => toN (p i)) (hcq : Chained d fun i => toN (q i))
    (h : ∑ i, shiftIncl N (d i) (castR (p i)) = ∑ i, shiftIncl N (d i) (castR (q i))) :
    p = q := by
  have hmem : ∀ (q : Fin r → Fin (n + 1) → ℤ), (∀ i, q i ∈ latticePts n) →
      ∀ i, castR (q i) ∈ lymChain n := fun q hq i => (mem_latticePts_iff hn _).mp (hq i)
  have := chainedR_unique hn hd hN (hmem p hp) (hmem q hq)
    ((chained_iff_chainedR hn hd hp).mp hcp) ((chained_iff_chainedR hn hd hq).mp hcq) h
  funext i
  exact castR_injective (congrFun this i)

/-- **`cor-additivity`'s bijection, with article 2's `Chained`**: every lattice point of
`Koz(n; d⃗)` is the shifted sum of exactly one `Chained` tuple of elements of `𝓛_n`. -/
theorem existsUnique_Chained_lattice (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ}
    (hd : Monotone d) (hN : ∀ i, d i + n ≤ N) {z : Fin (N + 1) → ℤ}
    (hz : castR z ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)) :
    ∃! q : Fin r → Fin (n + 1) → ℤ, (∀ i, q i ∈ latticePts n) ∧
      Chained d (fun i => toN (q i)) ∧ ∑ i, shiftZ N (d i) (q i) = z := by
  obtain ⟨q, ⟨hq, hcq, hsq⟩, huniq⟩ := existsUnique_chained_lattice hn hd hN hz
  refine ⟨q, ⟨hq, (chained_iff_chainedR hn hd hq).mpr hcq, hsq⟩, ?_⟩
  rintro q' ⟨hq', hcq', hsq'⟩
  exact huniq q' ⟨hq', (chained_iff_chainedR hn hd hq').mp hcq', hsq'⟩

/-- **`cor-membership`** (conditional on article 2's chaining reformulation for the point
at hand, `hPartII`): a lattice point `z` of `Koz(n; d⃗)` is an ff-vector iff every part of
its canonical decomposition is an `f`-vector. The "if" direction does not use `hPartII`. -/
theorem cor_membership (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {z : Fin (N + 1) → ℤ}
    (hz : castR z ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n))
    (hPartII : castR z ∈ ffSet n N d → ∃ s : Fin r → Fin (n + 1) → ℝ,
      (∀ i, s i ∈ Sset n) ∧ ChainedR d s ∧ ∑ i, shiftIncl N (d i) (s i) = castR z) :
    castR z ∈ ffSet n N d ↔ ∀ i, castR (waterFill n d z i) ∈ Sset n := by
  constructor
  · intro hff i
    obtain ⟨s, hs, hcs, hsum⟩ := hPartII hff
    have hsl : ∀ i, s i ∈ lymChain n := fun i => by
      rw [← hull_Sset_eq hn]; exact subset_convexHull ℝ _ (hs i)
    rw [← chainedR_integral hn hd hN hsl hcs hsum i]
    exact hs i
  · intro hS
    obtain ⟨-, -, hsum⟩ := waterFill_spec hn hd hN hz
    rw [ff_eq_sumset, Set.mem_fintype_sum]
    refine ⟨fun i => shiftIncl N (d i) (castR (waterFill n d z i)),
      fun i => Set.mem_image_of_mem _ (hS i), ?_⟩
    conv_rhs => rw [← hsum]
    rw [castR_sum]
    exact sum_congr rfl fun i _ => (castR_shiftZ _ _ _).symm

end Lattice

end ExteriorConvex
