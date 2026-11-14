/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Chained decompositions for a general full leg vector

Formalisation of `article/exterior-convex_article3_draft_4.org`, §"Lattice points: the
canonical chained decomposition", for a **general full leg vector** `c⃗ = (c₀, …, c_n)`:
`thm-chained` (1) existence, (2) uniqueness with the water-filling formula, (3) integrality;
`cor-additivity` and `cor-idp`; and the necessity remark of `rem-chained-credit`, as a
machine-checked counterexample. `Lattice/ChainedExistence.lean` (Kozlov vector only) is not
edited; its main statements are re-derived here from the general ones.

**Normalisation.** Degree-0-inclusive coordinates `Fin (n+1)`, summands `Fin r` (0-based),
`d : Fin r → ℕ` with `Monotone d` ("sorted"), ambient `d i + n ≤ N` for the paper's
`N = n + d_r`, as in `ChainedExistence.lean`. The leg vector is `c : ℕ → ℕ` with
`hc : ∀ k ≤ n, 0 < c k` (the paper's "positive integers"; only `c₀, …, c_n` matter).
**Deviation (a generalisation):** the paper's `c₀ = 1` is not assumed; `∠(c⃗)` has
`x₀ = c₀`. Everything else is as printed. Most theorems carry `1 ≤ n`.

* `legSkel c n j` = `F̃_j = (c₀,…,c_j,0,…,0)`; `legSimplex c n` = `∠(c⃗) = conv{F̃₁,…,F̃_n}`;
  `legChain c n` its μ-chain description; `hull_legSkel_eq` (`prop-rank-one-H`,
  degree-0-inclusive; the dropped/shifted analogue is `Facets.chain_hull_eq`).
  `RA(c⃗; d⃗)` is written out as `∑ i, shiftIncl N (d i) '' legSimplex c n`.
* `LogConcave c n` is the paper's hypothesis `c_{k−1}c_{k+1} ≤ c_k²` for `3 ≤ k ≤ n−1`
  (i.e. on `(c₂,…,c_n)` only; weaker than `Facets.LogConcaveOn`). `c_ratio_le` turns it
  into `c_{j+1+δ}/c_{j+1} ≤ c_{j+δ}/c_j` (`j ≥ 2`, `j+1+δ ≤ n`), the only place it enters,
  replacing `choose_ratio_le`. `raiseC` needs the extra hypothesis `t + δ ≤ n` (binomials
  vanish beyond `n`, a general `c` does not); it holds at the use site (`t + δ = tp`).
* `ChainedC c d p` = `def-chained-points` (as `ChainedR`, with `c` for `C(n,·)`).
* (1) `exists_chainedC` (proof: `ChainedExistence.lean`'s single linear functional).
  (2) `chainedC_formula`, `chainedC_unique`, `waterFillC_eq_Q` — no log-concavity.
  (3) `chainedC_integral`. Lattice points: `latticePtsC`, `waterFillC_spec`,
  `cor_additivityC`, `existsUnique_chainedC_lattice`; `cor_idpC` (every sorted `d⃗`, `t ≥ 1`).
* **Kozlov instance:** `legChain_choose` (`= lymChain n`), `legSimplex_choose`
  (`= conv S_n`), `logConcave_choose`, `chainedC_choose_iff` (`↔ ChainedR`, `Iff.rfl`),
  `waterFillC_choose` (`= waterFill`, `rfl`), `latticePtsC_choose`; and the existing
  `exists_chained`, `chainedR_unique`, `cor_additivity`, `cor_idp` re-proved verbatim from
  the general theorems (`*_of_general`).
* **Necessity** (`rem-chained-credit`): `cBad = (1,2,1,3,1,3)`, `dBad = (0,1)`,
  `not_logConcave_cBad` (fails at `k = 4`: `c₃c₅ = 9 > c₄² = 1`), `xBad_mem`:
  `(1,3,3,3,1,3,0) = F̃₅ + shift F̃₁ ∈ RA(c⃗; d⃗)`, and `no_chained_cBad`: it has no chained
  decomposition into real points of `∠(c⃗)` (water-filling forces `p₁ = (1,2,1,2,0,2)`,
  `μ₅ = 2/3 > μ₄ = 0`). Note this `x` *is* a sum of lattice points (non-chained), so it
  witnesses failure of existence, not of additivity; the paper's counts 101 vs 70 are not
  checked.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Lattice.ChainedExistence

open Finset
open scoped Pointwise

namespace ExteriorConvex

namespace Lattice

namespace Leg

variable {n : ℕ} {c : ℕ → ℕ}

/-! ## The right-angle simplex `∠(c⃗)` of a full leg vector, degree-0-inclusively -/

/-- The paper's log-concavity hypothesis on `(c₂, …, c_n)`:
`c_k² ≥ c_{k−1} c_{k+1}` for `3 ≤ k ≤ n−1`. -/
def LogConcave (c : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ k, 3 ≤ k → k + 1 ≤ n → c (k - 1) * c (k + 1) ≤ c k ^ 2

/-- The vertex `F̃_j = (c₀, …, c_j, 0, …, 0)` of `∠(c⃗)`. -/
def legSkel (c : ℕ → ℕ) (n j : ℕ) : Fin (n + 1) → ℝ := fun i =>
  if i.val ≤ j then (c i.val : ℝ) else 0

/-- `∠(c⃗) = conv{F̃₁, …, F̃_n} ⊆ ℝ^{n+1}`. -/
def legSimplex (c : ℕ → ℕ) (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  convexHull ℝ (legSkel c n '' Set.Icc 1 n)

/-- The μ-chain description of `∠(c⃗)` (`prop-rank-one-H`): `x₀ = c₀`, `x₁ = c₁`,
`x_{j+1}/c_{j+1} ≤ x_j/c_j` (`1 ≤ j ≤ n−1`), `x_n ≥ 0`. For the Kozlov vector this
is `lymChain n` (`legChain_choose`). -/
def legChain (c : ℕ → ℕ) (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | x 0 = c 0 ∧ x 1 = c 1 ∧
    (∀ j, (hj : 1 ≤ j) → (hjn : j ≤ n - 1) →
      x ⟨j + 1, by omega⟩ / (c (j + 1) : ℝ) ≤ x ⟨j, by omega⟩ / (c j : ℝ)) ∧
    0 ≤ x (Fin.last n)}

/-- The LYM ratio `μ_k = x_k / c_k`, total, zero beyond `n`. -/
noncomputable def muC (c : ℕ → ℕ) (n : ℕ) (x : Fin (n + 1) → ℝ) (k : ℕ) : ℝ :=
  if h : k ≤ n then x ⟨k, Nat.lt_succ_of_le h⟩ / (c k : ℝ) else 0

theorem muC_of_le {c : ℕ → ℕ} {x : Fin (n + 1) → ℝ} {k : ℕ} (h : k ≤ n) :
    muC c n x k = x ⟨k, Nat.lt_succ_of_le h⟩ / (c k : ℝ) := dite_eq_left h

theorem muC_of_gt {c : ℕ → ℕ} {x : Fin (n + 1) → ℝ} {k : ℕ} (h : n < k) :
    muC c n x k = 0 := dite_eq_right (by omega)

theorem convex_legChain (c : ℕ → ℕ) (n : ℕ) : Convex ℝ (legChain c n) := by
  intro x hx y hy a b ha hb hab
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  obtain ⟨hy0, hy1, hyc, hyn⟩ := hy
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx0, hy0]
    rw [← add_mul, hab, one_mul]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hx1, hy1]
    rw [← add_mul, hab, one_mul]
  · intro j hj hjn
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_div, mul_div_assoc]
    exact add_le_add (mul_le_mul_of_nonneg_left (hxc j hj hjn) ha)
      (mul_le_mul_of_nonneg_left (hyc j hj hjn) hb)
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha hxn) (mul_nonneg hb hyn)

section Pos

variable (hc : ∀ k, k ≤ n → 0 < c k)
include hc

theorem cpos {k : ℕ} (hk : k ≤ n) : (0 : ℝ) < (c k : ℝ) := Nat.cast_pos.mpr (hc k hk)

theorem legSkel_mem (hn : 1 ≤ n) {j : ℕ} (hj : j ∈ Set.Icc 1 n) :
    legSkel c n j ∈ legChain c n := by
  rw [Set.mem_Icc] at hj
  refine ⟨by simp [legSkel], ?_, fun k hk hkn => ?_, ?_⟩
  · rw [fin_one_eq hn]; simp only [legSkel]; rw [ite_eq_left hj.1]
  · simp only [legSkel]
    have h1 := cpos hc (k := k + 1) (by omega)
    have h0 := cpos hc (k := k) (by omega)
    split_ifs with h1' h2
    · rw [div_self h1.ne', div_self h0.ne']
    · omega
    · rw [zero_div, div_self h0.ne']; exact zero_le_one
    · rw [zero_div, zero_div]
  · simp only [legSkel, Fin.val_last]
    split_ifs
    · exact Nat.cast_nonneg _
    · exact le_rfl

omit hc in
theorem sum_muC_telescope (x : Fin (n + 1) → ℝ) {k : ℕ} (hk : k ≤ n) :
    ∑ j ∈ Finset.Icc k n, (muC c n x j - muC c n x (j + 1)) = muC c n x k := by
  have hIcc : Finset.Icc k n = Finset.Ico k (n + 1) := by
    ext j; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hcongr : ∀ i ∈ Finset.range (n + 1 - k),
      muC c n x (k + i) - muC c n x (k + i + 1) =
        (fun i => muC c n x (k + i)) i - (fun i => muC c n x (k + i)) (i + 1) := by
    intro i _; simp only []; rw [← Nat.add_assoc]
  rw [Finset.sum_congr rfl hcongr, Finset.sum_range_sub' (fun i => muC c n x (k + i))]
  simp only [Nat.add_zero]
  rw [show k + (n + 1 - k) = n + 1 by omega, muC_of_gt (Nat.lt_succ_self n), sub_zero]

theorem legChain_subset_hull (hn : 1 ≤ n) : legChain c n ⊆ legSimplex c n := by
  intro x hx
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  set w : ℕ → ℝ := fun j => muC c n x j - muC c n x (j + 1) with hw
  have hmu1 : muC c n x 1 = 1 := by
    rw [muC_of_le hn, ← fin_one_eq hn, hx1, div_self (cpos hc hn).ne']
  have hw0 : ∀ j ∈ Finset.Icc 1 n, 0 ≤ w j := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rcases eq_or_lt_of_le hj.2 with hjn | hjn
    · subst hjn
      simp only [hw]
      rw [muC_of_gt (Nat.lt_succ_self j), sub_zero, muC_of_le (le_refl j)]
      exact div_nonneg hxn (cpos hc le_rfl).le
    · have h := hxc j hj.1 (by omega)
      simp only [hw]
      rw [muC_of_le (by omega : j ≤ n), muC_of_le (by omega : j + 1 ≤ n), sub_nonneg]
      exact h
  have hsum : ∑ j ∈ Finset.Icc 1 n, w j = 1 := by
    rw [hw, sum_muC_telescope x hn, hmu1]
  have hz : ∀ j ∈ Finset.Icc 1 n, legSkel c n j ∈ legSkel c n '' Set.Icc 1 n := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    exact Set.mem_image_of_mem _ (Set.mem_Icc.mpr hj)
  have hrepr : ∑ j ∈ Finset.Icc 1 n, w j • legSkel c n j = x := by
    funext i
    rw [Finset.sum_apply]
    rcases Nat.eq_zero_or_pos i.val with hi0 | hipos
    · have hval : ∀ j ∈ Finset.Icc 1 n, (w j • legSkel c n j) i = w j * (c 0 : ℝ) := by
        intro j hj
        rw [Pi.smul_apply, smul_eq_mul]
        simp [legSkel, hi0]
      rw [Finset.sum_congr rfl hval, ← Finset.sum_mul, hsum, one_mul]
      have hi : i = 0 := Fin.ext hi0
      rw [hi, hx0]
    · have hkn : i.val ≤ n := by omega
      have hval : ∀ j ∈ Finset.Icc 1 n, (w j • legSkel c n j) i =
          if i.val ≤ j then w j * (c i.val : ℝ) else 0 := by
        intro j _
        rw [Pi.smul_apply, smul_eq_mul]
        simp only [legSkel]
        split_ifs <;> simp
      rw [Finset.sum_congr rfl hval, ← Finset.sum_filter]
      have hfilter : (Finset.Icc 1 n).filter (fun j => i.val ≤ j) = Finset.Icc i.val n := by
        ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
      rw [hfilter, ← Finset.sum_mul, sum_muC_telescope x hkn, muC_of_le hkn,
        div_mul_cancel₀ _ (cpos hc hkn).ne']
  have hcm := Finset.centerMass_mem_convexHull (Finset.Icc 1 n) hw0
    (by rw [hsum]; exact zero_lt_one) hz
  rwa [Finset.centerMass_eq_of_sum_1 _ _ hsum, hrepr] at hcm

/-- **`prop-rank-one-H` for a general full leg vector** (degree-0-inclusive):
`∠(c⃗) = conv{F̃_j}` is the μ-chain set. (The degree-0-dropped, shifted analogue is
`Facets.chain_hull_eq`.) -/
theorem hull_legSkel_eq (hn : 1 ≤ n) : legSimplex c n = legChain c n :=
  Set.Subset.antisymm
    (convexHull_min (fun _ ⟨_, hj, h⟩ => h ▸ legSkel_mem hc hn hj) (convex_legChain c n))
    (legChain_subset_hull hc hn)

omit hc in
theorem isCompact_legSimplex (c : ℕ → ℕ) (n : ℕ) : IsCompact (legSimplex c n) :=
  ((Set.finite_Icc 1 n).image _).isCompact_convexHull ℝ

theorem isCompact_legChain (hn : 1 ≤ n) : IsCompact (legChain c n) := by
  rw [← hull_legSkel_eq hc hn]; exact isCompact_legSimplex c n

omit hc in
/-- The LYM ratios decrease along `[i, n]`, `i ≥ 1`. -/
theorem muC_antitone {x : Fin (n + 1) → ℝ} (hx : x ∈ legChain c n)
    {i : ℕ} (hi : 1 ≤ i) : ∀ j, i ≤ j → j ≤ n → muC c n x j ≤ muC c n x i := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ k hik ih =>
    intro hk
    have h := hx.2.2.1 k (by omega) (by omega)
    have ih' := ih (by omega)
    rw [muC_of_le (by omega)] at ih' ⊢
    exact le_trans h ih'

theorem muC_one (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (hx : x ∈ legChain c n) :
    muC c n x 1 = 1 := by
  rw [muC_of_le hn, ← fin_one_eq hn, hx.2.1, div_self (cpos hc hn).ne']

/-- The box `0 ≤ x_m ≤ c_m` on `∠(c⃗)`, every coordinate including `0`. -/
theorem box_legChain (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (hx : x ∈ legChain c n)
    (m : Fin (n + 1)) : 0 ≤ x m ∧ x m ≤ (c m.val : ℝ) := by
  rcases Nat.eq_zero_or_pos m.val with h0 | hpos
  · have hm : m = 0 := Fin.ext h0
    subst hm
    rw [hx.1]; simp
  · have hC := cpos hc (k := m.val) (by omega)
    have hup := muC_antitone hx (le_refl 1) m.val hpos (by omega)
    have hlo := muC_antitone hx hpos n (by omega) le_rfl
    rw [muC_one hc hn hx, muC_of_le (by omega)] at hup
    rw [muC_of_le le_rfl, muC_of_le (by omega)] at hlo
    have hlast : x ⟨n, Nat.lt_succ_of_le le_rfl⟩ = x (Fin.last n) := rfl
    rw [hlast] at hlo
    have hm' : x ⟨m.val, Nat.lt_succ_of_le (by omega)⟩ = x m := rfl
    rw [hm'] at hup hlo
    refine ⟨?_, ?_⟩
    · have := le_trans (div_nonneg hx.2.2.2 (cpos hc le_rfl).le) hlo
      exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hC))
    · rwa [div_le_iff₀ hC, one_mul] at hup

end Pos

/-! ## Log-concavity in ratio form -/

/-- From `LogConcave`: `c_{j+1+δ} c_j ≤ c_{j+δ} c_{j+1}` for `j ≥ 2`, `j+1+δ ≤ n`,
i.e. `c_{j+1+δ}/c_{j+1} ≤ c_{j+δ}/c_j` (a product of `δ` adjacent comparisons). -/
theorem c_mul_le (hc : ∀ k, k ≤ n → 0 < c k) (hlc : LogConcave c n) {j : ℕ} (hj : 2 ≤ j) :
    ∀ δ, j + 1 + δ ≤ n → c (j + 1 + δ) * c j ≤ c (j + δ) * c (j + 1) := by
  intro δ
  induction δ with
  | zero => intro _; simp [mul_comm]
  | succ δ ih =>
    intro hδ
    have ih' := ih (by omega)
    have hl := hlc (j + 1 + δ) (by omega) (by omega)
    rw [show j + 1 + δ - 1 = j + δ by omega] at hl
    rw [show j + 1 + (δ + 1) = j + 1 + δ + 1 by omega, show j + (δ + 1) = j + 1 + δ by omega]
    have hpos := hc (j + 1 + δ) (by omega)
    generalize c (j + 1 + δ + 1) = A at hl ⊢
    generalize c (j + 1 + δ) = C at hl ih' hpos ⊢
    generalize c (j + δ) = D at hl ih'
    refine Nat.le_of_mul_le_mul_right ?_ hpos
    calc A * c j * C = A * (C * c j) := by ring
      _ ≤ A * (D * c (j + 1)) := Nat.mul_le_mul_left _ ih'
      _ = (D * A) * c (j + 1) := by ring
      _ ≤ C ^ 2 * c (j + 1) := Nat.mul_le_mul_right _ hl
      _ = C * c (j + 1) * C := by ring

theorem c_ratio_le (hc : ∀ k, k ≤ n → 0 < c k) (hlc : LogConcave c n) {j : ℕ} (hj : 2 ≤ j)
    (δ : ℕ) (hδ : j + 1 + δ ≤ n) :
    (c (j + 1 + δ) : ℝ) / c (j + 1) ≤ (c (j + δ) : ℝ) / c j := by
  rw [div_le_div_iff₀ (cpos hc (by omega)) (cpos hc (by omega))]
  exact_mod_cast c_mul_le hc hlc hj δ hδ

/-! ## The two block perturbations of the exchange step -/

/-- The block vector: `c_{m+δ}` on `s ≤ m ≤ t`, zero elsewhere. -/
noncomputable def blkC (c : ℕ → ℕ) (n s t δ : ℕ) : Fin (n + 1) → ℝ := fun m =>
  if s ≤ m.val ∧ m.val ≤ t then (c (m.val + δ) : ℝ) else 0

theorem blkC_nonneg (c : ℕ → ℕ) (n s t δ : ℕ) (m : Fin (n + 1)) : 0 ≤ blkC c n s t δ m := by
  unfold blkC; split_ifs <;> positivity

theorem blkC_of_lt {c : ℕ → ℕ} {s t δ : ℕ} {m : Fin (n + 1)} (h : m.val < s) :
    blkC c n s t δ m = 0 := by
  unfold blkC; split_ifs with h'
  · omega
  · rfl

/-- **Lowering a block** of `∠(c⃗)` on `[s, T]`, `T = tp`. -/
theorem lowerC (hc : ∀ k, k ≤ n → 0 < c k) (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ legChain c n) {s T : ℕ} (hs : 2 ≤ s) (hT : T ≤ n)
    (hzero : ∀ j : Fin (n + 1), T < j.val → x j = 0) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ muC c n x T) : x - ε • blkC c n s T 0 ∈ legChain c n := by
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  rw [muC_of_le hT] at hε
  refine ⟨?_, ?_, fun j hj hjn => ?_, ?_⟩
  · rw [Pi.sub_apply, Pi.smul_apply, blkC_of_lt (by simp; omega), smul_zero, sub_zero, hx0]
  · rw [fin_one_eq hn] at hx1 ⊢
    rw [Pi.sub_apply, Pi.smul_apply, blkC_of_lt (by simp; omega), smul_zero, sub_zero, hx1]
  · have h := hxc j hj hjn
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, blkC, add_zero]
    have hc1 := cpos hc (k := j + 1) (by omega)
    have hc0 := cpos hc (k := j) (by omega)
    by_cases h1 : s ≤ j + 1 ∧ j + 1 ≤ T <;> by_cases h2 : s ≤ j ∧ j ≤ T <;>
      simp only [h1, h2, and_self, ↓reduceIte, mul_zero, sub_zero]
    · rw [sub_div, sub_div, mul_div_assoc, mul_div_assoc, div_self hc1.ne',
        div_self hc0.ne']
      linarith
    · rw [sub_div, mul_div_assoc, div_self hc1.ne']
      linarith
    · have hjT : j = T := by omega
      subst hjT
      rw [hzero ⟨j + 1, by omega⟩ (by simp), zero_div, sub_div, mul_div_assoc,
        div_self hc0.ne']
      linarith
    · exact h
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, blkC, Fin.val_last, add_zero]
    by_cases h : s ≤ n ∧ n ≤ T
    · simp only [h, and_self, ↓reduceIte]
      have hTn : T = n := by omega
      subst hTn
      rw [le_div_iff₀ (cpos hc le_rfl)] at hε
      have : x ⟨T, by omega⟩ = x (Fin.last T) := rfl
      linarith
    · simp only [h, ↓reduceIte, mul_zero, sub_zero]; exact hxn

/-- **Raising a block** (where log-concavity enters): raising `μ_m` by
`ε c_{m+δ}/c_m` on `[s, t]`, `t + δ ≤ n`, past a strict drop `μ_{s−1} > μ_s`. -/
theorem raiseC (hc : ∀ k, k ≤ n → 0 < c k) (hlc : LogConcave c n) (hn : 1 ≤ n)
    {y : Fin (n + 1) → ℝ} (hy : y ∈ legChain c n)
    {s t δ : ℕ} (hs : 2 ≤ s) (hsn : s ≤ n) (ht : t + δ ≤ n) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε * ((c (s + δ) : ℝ) / c s) ≤ muC c n y (s - 1) - muC c n y s) :
    y + ε • blkC c n s t δ ∈ legChain c n := by
  obtain ⟨hy0, hy1, hyc, hyn⟩ := hy
  rw [muC_of_le (by omega), muC_of_le hsn] at hε
  refine ⟨?_, ?_, fun j hj hjn => ?_, ?_⟩
  · rw [Pi.add_apply, Pi.smul_apply, blkC_of_lt (by simp; omega), smul_zero, add_zero, hy0]
  · rw [fin_one_eq hn] at hy1 ⊢
    rw [Pi.add_apply, Pi.smul_apply, blkC_of_lt (by simp; omega), smul_zero, add_zero, hy1]
  · have h := hyc j hj hjn
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, blkC]
    have hc1 := cpos hc (k := j + 1) (by omega)
    have hc0 := cpos hc (k := j) (by omega)
    by_cases h1 : s ≤ j + 1 ∧ j + 1 ≤ t <;> by_cases h2 : s ≤ j ∧ j ≤ t <;>
      simp only [h1, h2, and_self, ↓reduceIte, mul_zero, add_zero]
    · rw [add_div, add_div, mul_div_assoc, mul_div_assoc]
      have := mul_le_mul_of_nonneg_left
        (c_ratio_le hc hlc (j := j) (by omega) δ (by omega)) hε0
      linarith
    · have hjs : j + 1 = s := by omega
      subst hjs
      rw [add_div, mul_div_assoc]
      have e : ∀ (a b : Fin (n + 1)), a.val = b.val → y a = y b := fun a b h =>
        congrArg y (Fin.ext h)
      rw [e ⟨j + 1 - 1, by omega⟩ ⟨j, by omega⟩ (by simp)] at hε
      simp only [Nat.add_sub_cancel] at hε
      linarith
    · rw [add_div, mul_div_assoc]
      have := mul_nonneg hε0 (div_nonneg (Nat.cast_nonneg (c (j + δ))) hc0.le)
      linarith
    · exact h
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg hyn (mul_nonneg hε0 (blkC_nonneg _ _ _ _ _ _))

/-- **The transfer identity**, general leg vector. -/
theorem shift_blkC_transfer (c : ℕ → ℕ) (N di δ s t : ℕ) (ht : t + δ ≤ n) :
    shiftIncl (n := n) N di (blkC c n (s + δ) (t + δ) 0) =
      shiftIncl N (di + δ) (blkC c n s t δ) := by
  funext k
  simp only [shiftIncl_apply, blkC]
  by_cases h : s + δ + di ≤ k.val ∧ k.val ≤ t + δ + di
  · rw [dite_eq_left (by omega), dite_eq_left (by omega)]
    simp only [show s + δ ≤ k.val - di ∧ k.val - di ≤ t + δ by omega,
      show s ≤ k.val - (di + δ) ∧ k.val - (di + δ) ≤ t by omega, and_self, ↓reduceIte]
    rw [show k.val - di + 0 = k.val - (di + δ) + δ by omega]
  · have e1 : (if h' : di ≤ k.val ∧ k.val - di ≤ n then
        (if s + δ ≤ k.val - di ∧ k.val - di ≤ t + δ then
          (c (k.val - di + 0) : ℝ) else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exfalso; omega
      · rfl
      · rfl
    have e2 : (if h' : di + δ ≤ k.val ∧ k.val - (di + δ) ≤ n then
        (if s ≤ k.val - (di + δ) ∧ k.val - (di + δ) ≤ t then
          (c (k.val - (di + δ) + δ) : ℝ) else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exfalso; omega
      · rfl
      · rfl
    rw [e1, e2]

/-! ## Chained tuples for a general leg vector -/

/-- **`def-chained-points`** for points of `∠(c⃗)`: wherever summand `i` is non-zero
(`p_i(m) > 0`), summand `i+1` is full (`p_{i+1}(m') = c_{m'}`) in every global degree
`m' + d_{i+1} ≤ m + d_i`. For `c = C(n,·)` this is `ChainedR` (`chainedC_choose_iff`). -/
def ChainedC (c : ℕ → ℕ) {r : ℕ} (d : Fin r → ℕ) (p : Fin r → Fin (n + 1) → ℝ) : Prop :=
  ∀ ⦃i j : Fin r⦄, i.val + 1 = j.val → ∀ m m' : Fin (n + 1), 0 < p i m →
    m'.val + d j ≤ m.val + d i → p j m' = c m'.val

theorem ChainedC.full_of_lt (hc : ∀ k, k ≤ n → 0 < c k) {r : ℕ} {d : Fin r → ℕ}
    (hd : Monotone d) {p : Fin r → Fin (n + 1) → ℝ} (hch : ChainedC c d p) :
    ∀ ⦃i j : Fin r⦄, i < j → ∀ m m' : Fin (n + 1), 0 < p i m →
      m'.val + d j ≤ m.val + d i → p j m' = c m'.val := by
  suffices H : ∀ g : ℕ, ∀ i j : Fin r, j.val = i.val + g + 1 →
      ∀ m m' : Fin (n + 1), 0 < p i m → m'.val + d j ≤ m.val + d i →
        p j m' = c m'.val by
    intro i j hij m m' hm hle
    have := Fin.lt_def.mp hij
    exact H (j.val - i.val - 1) i j (by omega) m m' hm hle
  intro g
  induction g with
  | zero => intro i j hij m m' hm hle; exact hch (by omega) m m' hm hle
  | succ g ih =>
    intro i j hij m m' hm hle
    let l : Fin r := ⟨i.val + 1, by omega⟩
    have hlj : d l ≤ d j := hd (Fin.le_def.mpr (by simp only [l]; omega))
    let m₁ : Fin (n + 1) := ⟨m.val + d i - d l, by
      have := hd (Fin.le_def.mpr (by simp only [l]; omega) : i ≤ l); omega⟩
    have h1 : p l m₁ = c m₁.val :=
      hch (i := i) (j := l) rfl m m₁ hm (by simp only [m₁]; omega)
    have hpos : 0 < p l m₁ := by
      rw [h1]; exact cpos hc (by omega)
    exact ih l j (by simp only [l]; omega) m₁ m' hpos (by simp only [m₁]; omega)

/-- **`thm-chained`(1), existence, general full leg vector, `legChain` form.** -/
theorem exists_chainedC_chain (hc : ∀ k, k ≤ n → 0 < c k) (hlc : LogConcave c n)
    (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {x : Fin (N + 1) → ℝ}
    (hx : x ∈ ∑ i, shiftIncl N (d i) '' legChain c n) :
    ∃ p : Fin r → Fin (n + 1) → ℝ, (∀ i, p i ∈ legChain c n) ∧ ChainedC c d p ∧
      ∑ i, shiftIncl N (d i) (p i) = x := by
  set R : Set (Fin r → Fin (n + 1) → ℝ) :=
    (Set.univ.pi fun _ => legChain c n) ∩
      (fun p => ∑ i, shiftIncl N (d i) (p i)) ⁻¹' {x} with hR
  have hl : ∀ i, Continuous (shiftIncl (n := n) N (d i)) := fun i =>
    LinearMap.continuous_of_finiteDimensional _
  have hcont : Continuous
      (fun p : Fin r → Fin (n + 1) → ℝ => ∑ i, shiftIncl N (d i) (p i)) :=
    continuous_finsetSum _ fun i _ => (hl i).comp (continuous_apply i)
  have hRc : IsCompact R :=
    (isCompact_univ_pi fun _ => isCompact_legChain hc hn).inter_right
      (isClosed_singleton.preimage hcont)
  have hRne : R.Nonempty := by
    rw [Set.mem_fintype_sum] at hx
    obtain ⟨g, hg, hsum⟩ := hx
    choose p hp hpg using hg
    refine ⟨p, fun i _ => hp i, ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hsum]
    exact sum_congr rfl fun i _ => hpg i
  let F : (Fin r → Fin (n + 1) → ℝ) → ℝ := fun p =>
    ∑ i, (i.val : ℝ) * ∑ k, shiftIncl N (d i) (p i) k
  have hFc : Continuous F := by
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    refine continuous_finsetSum _ fun k _ => ?_
    exact (continuous_apply k).comp ((hl i).comp (continuous_apply i))
  obtain ⟨p, hpR, hmax⟩ := hRc.exists_isMaxOn hRne hFc.continuousOn
  have hpl : ∀ l, p l ∈ legChain c n := fun l => hpR.1 l (Set.mem_univ _)
  have hpsum : ∑ i, shiftIncl N (d i) (p i) = x := hpR.2
  refine ⟨p, hpl, ?_, hpsum⟩
  intro i j hij m m' hm hle
  by_contra hne
  have hij' : i < j := Fin.lt_def.mpr (by omega)
  have hijne : i ≠ j := hij'.ne
  have hdij : d i ≤ d j := hd hij'.le
  set δ := d j - d i with hδ
  have hdj : d j = d i + δ := by omega
  have hC : ∀ k, k ≤ n → (0 : ℝ) < (c k : ℝ) := fun k hk => cpos hc hk
  have hlt : p j m' < c m'.val := lt_of_le_of_ne (box_legChain hc hn (hpl j) m').2 hne
  have hm'2 : 2 ≤ m'.val := by
    by_contra h
    rcases (show m'.val = 0 ∨ m'.val = 1 by omega) with h0 | h1
    · have : m' = 0 := Fin.ext h0
      rw [this, (hpl j).1] at hlt
      simp at hlt
    · have : m' = 1 := by rw [fin_one_eq hn]; exact Fin.ext h1
      rw [this, (hpl j).2.1, fin_one_eq hn] at hlt
      simp at hlt
  have hmu1 : muC c n (p j) 1 = 1 := muC_one hc hn (hpl j)
  have hmum' : muC c n (p j) m'.val < 1 := by
    rw [muC_of_le (by omega), div_lt_one (hC _ (by omega))]
    exact hlt
  obtain ⟨s, hs1, hsm, hdrop⟩ := exists_drop (muC c n (p j)) (show 1 ≤ m'.val by omega)
    (by rw [hmu1]; exact hmum')
  set S := univ.filter fun k : Fin (n + 1) => 0 < p i k with hS
  have hSne : S.Nonempty := ⟨m, by simp [S, hm]⟩
  set T := S.max' hSne with hT
  have hTpos : 0 < p i T := (mem_filter.mp (S.max'_mem hSne)).2
  have hmT : m ≤ T := S.le_max' m (by simp [S, hm])
  have hzero : ∀ k : Fin (n + 1), T.val < k.val → p i k = 0 := by
    intro k hk
    refine le_antisymm (not_lt.mp fun h => ?_) (box_legChain hc hn (hpl i) k).1
    have := S.le_max' k (by simp [S, h])
    exact absurd (Fin.le_def.mp this) (by omega)
  have hmT' := Fin.le_def.mp hmT
  have hsT : s + δ ≤ T.val := by omega
  set t := T.val - δ with ht
  have htT : t + δ = T.val := by omega
  have hTn : T.val ≤ n := T.is_le
  set ρ : ℝ := (c (s + δ) : ℝ) / c s with hρ
  have hρpos : 0 < ρ := div_pos (hC _ (by omega)) (hC _ (by omega))
  have hmuT : 0 < muC c n (p i) T.val := by
    rw [muC_of_le hTn]; exact div_pos hTpos (hC _ hTn)
  set ε : ℝ := min (muC c n (p i) T.val) ((muC c n (p j) (s - 1) - muC c n (p j) s) / ρ)
    with hε
  have hεpos : 0 < ε := lt_min hmuT (div_pos (by linarith) hρpos)
  set a := blkC c n (s + δ) T.val 0 with ha
  set b := blkC c n s t δ with hb
  let q : Fin r → Fin (n + 1) → ℝ := fun l =>
    if l = i then p i - ε • a else if l = j then p j + ε • b else p l
  have hqi : q i = p i - ε • a := by simp [q]
  have hqj : q j = p j + ε • b := by simp [q, hijne.symm]
  have hqmem : ∀ l, q l ∈ legChain c n := by
    intro l
    by_cases hli : l = i
    · subst hli; rw [hqi]
      exact lowerC hc hn (hpl l) (by omega) hTn hzero hεpos.le (min_le_left _ _)
    · by_cases hlj : l = j
      · subst hlj; rw [hqj]
        refine raiseC hc hlc hn (hpl l) (by omega) (by omega) (by omega) hεpos.le ?_
        have := min_le_right (muC c n (p i) T.val)
          ((muC c n (p l) (s - 1) - muC c n (p l) s) / ρ)
        exact (le_div_iff₀ hρpos).mp this
      · simp [q, hli, hlj, hpl l]
  set A := shiftIncl N (d i) a with hA
  have hAB : shiftIncl N (d j) b = A := by
    rw [hA, ha, hb, hdj, ← htT]
    exact (shift_blkC_transfer c N (d i) δ s t (by omega)).symm
  have hqshift : ∀ l, shiftIncl N (d l) (q l) = shiftIncl N (d l) (p l) +
      ((if l = i then -(ε • A) else 0) + (if l = j then ε • A else 0)) := by
    intro l
    by_cases hli : l = i
    · subst hli
      rw [hqi, map_sub, map_smul]
      simp [hijne, hA, sub_eq_add_neg]
    · by_cases hlj : l = j
      · subst hlj
        rw [hqj, map_add, map_smul, hAB]
        simp [hli]
      · simp [q, hli, hlj]
  have hqsum : ∑ l, shiftIncl N (d l) (q l) = x := by
    simp only [hqshift, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte, hpsum]
    abel
  have hqR : q ∈ R := ⟨fun l _ => hqmem l, hqsum⟩
  set M := ∑ k, A k with hM
  have hMpos : 0 < M := by
    have hk0 : T.val + d i < N + 1 := by have := hN i; omega
    have hval : A ⟨T.val + d i, hk0⟩ = c T.val := by
      rw [hA, shiftIncl_apply, dite_eq_left (by simp; omega)]
      simp only [ha, blkC, Nat.add_sub_cancel, add_zero]
      simp [hsT]
    have hnn : ∀ k, 0 ≤ A k := by
      intro k
      rw [hA, shiftIncl_apply]
      split_ifs
      · exact blkC_nonneg _ _ _ _ _ _
      · exact le_rfl
    calc (0 : ℝ) < c T.val := hC _ hTn
      _ = A ⟨T.val + d i, hk0⟩ := hval.symm
      _ ≤ M := single_le_sum (fun k _ => hnn k) (mem_univ _)
  have hFq : F q = F p + ε * M := by
    have : ∀ l : Fin r, (l.val : ℝ) * ∑ k, shiftIncl N (d l) (q l) k =
        (l.val : ℝ) * ∑ k, shiftIncl N (d l) (p l) k +
          ((if l = i then -((i.val : ℝ) * (ε * M)) else 0) +
            (if l = j then (j.val : ℝ) * (ε * M) else 0)) := by
      intro l
      rw [hqshift l]
      by_cases hli : l = i
      · subst hli
        simp [hijne, sum_add_distrib, ← mul_sum, hM, mul_add]
      · by_cases hlj : l = j
        · subst hlj
          simp [hli, sum_add_distrib, ← mul_sum, hM, mul_add]
        · simp [hli, hlj]
    simp only [F, this, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
    have hj : (j.val : ℝ) = i.val + 1 := by rw [← hij]; push_cast; ring
    rw [hj]; ring
  have := hmax hqR
  simp only [Set.mem_ofPred_eq] at this
  rw [hFq] at this
  nlinarith [mul_pos hεpos hMpos]

/-! ## Water-filling: uniqueness and integrality (no log-concavity) -/

/-- The capacity `c_{k−d}` of a summand shifted by `d`, in global degree `k`
(zero outside `[d, d+n]`). -/
def capC (c : ℕ → ℕ) (n dl k : ℕ) : ℤ := if dl ≤ k ∧ k - dl ≤ n then (c (k - dl) : ℤ) else 0

/-- **The water-filling map**, general leg vector:
`(p_i)_m = max(0, min(c_m, x_{m+d_i} − ∑_{l>i} c_{m+d_i−d_l}))`. -/
def waterFillC (c : ℕ → ℕ) (n : ℕ) {r N : ℕ} (d : Fin r → ℕ) (x : Fin (N + 1) → ℤ)
    (i : Fin r) : Fin (n + 1) → ℤ := fun m =>
  max 0 (min (c m.val : ℤ)
    (getZ x (m.val + d i) - ∑ l ∈ univ.filter (fun l => i < l), capC c n (d l) (m.val + d i)))

theorem shift_boxC (hc : ∀ k, k ≤ n → 0 < c k) (hn : 1 ≤ n) {N dl : ℕ}
    {y : Fin (n + 1) → ℝ} (hy : y ∈ legChain c n) (k : Fin (N + 1)) :
    0 ≤ shiftIncl N dl y k ∧ shiftIncl N dl y k ≤ (capC c n dl k.val : ℝ) := by
  rw [shiftIncl_apply, capC]
  split_ifs
  · simpa using box_legChain hc hn hy ⟨k.val - dl, _⟩
  · simp

/-- **`thm-chained`(2), the water-filling formula**, general leg vector, real points. -/
theorem chainedC_formula (hc : ∀ k, k ≤ n → 0 < c k) (hn : 1 ≤ n) {r N : ℕ}
    {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {p : Fin r → Fin (n + 1) → ℝ} (hp : ∀ i, p i ∈ legChain c n)
    (hch : ChainedC c d p) (i : Fin r) (m : Fin (n + 1)) :
    p i m = max 0 (min (c m.val : ℝ)
      (getR (∑ l, shiftIncl N (d l) (p l)) (m.val + d i) -
        ∑ l ∈ univ.filter (fun l => i < l), (capC c n (d l) (m.val + d i) : ℝ))) := by
  have hkN : m.val + d i ≤ N := by have := hN i; omega
  set kF : Fin (N + 1) := ⟨m.val + d i, Nat.lt_succ_of_le hkN⟩ with hkF
  set v : Fin r → ℝ := fun l => shiftIncl N (d l) (p l) kF with hv
  have hget : getR (∑ l, shiftIncl N (d l) (p l)) (m.val + d i) = ∑ l, v l := by
    rw [getR, dite_eq_left hkN, Finset.sum_apply]
  have hvi : v i = p i m := by
    simp only [hv, kF, shiftIncl_apply]
    rw [dite_eq_left (by omega)]
    congr 1; ext; simp
  have hbox : ∀ l, 0 ≤ v l ∧ v l ≤ (capC c n (d l) (m.val + d i) : ℝ) := fun l =>
    shift_boxC hc hn (hp l) kF
  have hfull : 0 < p i m → ∀ l, i < l → v l = (capC c n (d l) (m.val + d i) : ℝ) := by
    intro hpos l hil
    simp only [hv, kF, shiftIncl_apply, capC]
    split_ifs with h1
    · rw [hch.full_of_lt hc hd hil m ⟨m.val + d i - d l, _⟩ hpos (by simp; omega)]
      simp
    · simp
  have hzero : ∀ l, l < i → 0 < v l → p i m = c m.val := by
    intro l hli hvl
    simp only [hv, kF, shiftIncl_apply] at hvl
    split_ifs at hvl with h1
    · exact hch.full_of_lt hc hd hli ⟨m.val + d i - d l, _⟩ m hvl (by simp; omega)
    · exact absurd hvl (lt_irrefl 0)
  rw [hget, sum_split_at v i, hvi]
  set A := ∑ l ∈ univ.filter (fun l => l < i), v l with hA
  set B := ∑ l ∈ univ.filter (fun l => i < l), v l with hB
  set Tc := ∑ l ∈ univ.filter (fun l => i < l), (capC c n (d l) (m.val + d i) : ℝ) with hTc
  have hA0 : 0 ≤ A := sum_nonneg fun l _ => (hbox l).1
  have hB0 : 0 ≤ B := sum_nonneg fun l _ => (hbox l).1
  have hBT : B ≤ Tc := sum_le_sum fun l _ => (hbox l).2
  have hBfull : 0 < p i m → B = Tc := fun hpos =>
    sum_congr rfl fun l hl => hfull hpos l (mem_filter.mp hl).2
  have hAz : A = 0 ∨ p i m = c m.val := by
    by_cases h : ∃ l, l < i ∧ 0 < v l
    · obtain ⟨l, hl, hvl⟩ := h
      exact Or.inr (hzero l hl hvl)
    · push Not at h
      left
      exact sum_eq_zero fun l hl => le_antisymm (h l (mem_filter.mp hl).2) (hbox l).1
  have hpbox := box_legChain hc hn (hp i) m
  have hCpos : (0 : ℝ) < c m.val := cpos hc m.is_le
  rcases hpbox.1.lt_or_eq with hpos | hzero'
  · rw [hBfull hpos]
    rcases hAz with hA' | hA'
    · rw [hA', show (0 : ℝ) + p i m + Tc - Tc = p i m by ring, min_eq_right hpbox.2,
        max_eq_right hpos.le]
    · rw [hA', min_eq_left (by linarith), max_eq_right hCpos.le]
  · rcases hAz with hA' | hA'
    · rw [hA', ← hzero', min_eq_right (by linarith), max_eq_left (by linarith)]
    · exfalso; linarith

/-- **`thm-chained`(2), uniqueness**, general leg vector (no log-concavity). -/
theorem chainedC_unique (hc : ∀ k, k ≤ n → 0 < c k) (hn : 1 ≤ n) {r N : ℕ}
    {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {p q : Fin r → Fin (n + 1) → ℝ}
    (hp : ∀ i, p i ∈ legChain c n) (hq : ∀ i, q i ∈ legChain c n)
    (hcp : ChainedC c d p) (hcq : ChainedC c d q)
    (h : ∑ i, shiftIncl N (d i) (p i) = ∑ i, shiftIncl N (d i) (q i)) : p = q := by
  funext i m
  rw [chainedC_formula hc hn hd hN hp hcp, chainedC_formula hc hn hd hN hq hcq, h]

/-- **`thm-chained`(3), integrality**, general integral leg vector: the parts of a
chained decomposition of an integer point are the integer water-filling slices. -/
theorem chainedC_integral (hc : ∀ k, k ≤ n → 0 < c k) (hn : 1 ≤ n) {r N : ℕ}
    {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {p : Fin r → Fin (n + 1) → ℝ} (hp : ∀ i, p i ∈ legChain c n)
    (hch : ChainedC c d p) {z : Fin (N + 1) → ℤ}
    (hz : ∑ i, shiftIncl N (d i) (p i) = castR z) (i : Fin r) :
    p i = castR (waterFillC c n d z i) := by
  funext m
  rw [chainedC_formula hc hn hd hN hp hch, hz, getR_castR, castR_apply, waterFillC]
  push_cast
  rfl

/-- The paper's clamps `Q_c(k) = max(0, x_k − ∑_{l>c} c_{k−d_l})` (1-based `l`, i.e.
0-based `l ≥ c`). -/
def QwfC (c : ℕ → ℕ) (n : ℕ) {r N : ℕ} (d : Fin r → ℕ) (x : Fin (N + 1) → ℤ) (a k : ℕ) : ℤ :=
  max 0 (getZ x k - ∑ l ∈ univ.filter (fun l : Fin r => a ≤ l.val), capC c n (d l) k)

/-- The water-filling slice is the paper's `Q_i − Q_{i−1}` (1-based `i = i' + 1`). -/
theorem waterFillC_eq_Q {r N : ℕ} (d : Fin r → ℕ)
    (x : Fin (N + 1) → ℤ) (i : Fin r) (m : Fin (n + 1)) :
    waterFillC c n d x i m =
      QwfC c n d x (i.val + 1) (m.val + d i) - QwfC c n d x i.val (m.val + d i) := by
  have hset : univ.filter (fun l : Fin r => i.val ≤ l.val) =
      insert i (univ.filter fun l : Fin r => i < l) := by
    ext l
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.lt_def]
    constructor
    · intro h; rcases h.lt_or_eq with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h.symm)
    · rintro (rfl | h) <;> omega
  have hset' : univ.filter (fun l : Fin r => i.val + 1 ≤ l.val) =
      univ.filter fun l : Fin r => i < l := by
    ext l; simp only [mem_filter, mem_univ, true_and, Fin.lt_def]; omega
  have hcap : capC c n (d i) (m.val + d i) = c m.val := by
    rw [capC, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩), Nat.add_sub_cancel]
  have hnot : i ∉ univ.filter fun l : Fin r => i < l := by simp
  simp only [waterFillC, QwfC, hset, hset', sum_insert hnot, hcap]
  have h0 : (0 : ℤ) ≤ c m.val := Nat.cast_nonneg _
  generalize (c m.val : ℤ) = C at h0 ⊢
  generalize getZ x (m.val + d i) = y
  generalize ∑ l ∈ univ.filter (fun l : Fin r => i < l), capC c n (d l) (m.val + d i) = T
  omega

/-! ## `RA(c⃗; d⃗)` itself, and its lattice points -/

/-- **`thm-chained`(1), existence**, on `RA(c⃗; d⃗) = ∑ᵢ shift^{dᵢ} ∠(c⃗)`. -/
theorem exists_chainedC (hc : ∀ k, k ≤ n → 0 < c k) (hlc : LogConcave c n) (hn : 1 ≤ n)
    {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {x : Fin (N + 1) → ℝ}
    (hx : x ∈ ∑ i, shiftIncl N (d i) '' legSimplex c n) :
    ∃ p : Fin r → Fin (n + 1) → ℝ, (∀ i, p i ∈ legSimplex c n) ∧ ChainedC c d p ∧
      ∑ i, shiftIncl N (d i) (p i) = x := by
  simp only [hull_legSkel_eq hc hn] at hx ⊢
  exact exists_chainedC_chain hc hlc hn hd hN hx

/-- The lattice points `∠(c⃗) ∩ ℤ^{n+1}`. -/
def latticePtsC (c : ℕ → ℕ) (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {x | castR x ∈ legSimplex c n}

/-- **Existence and integrality for lattice points**: the water-filling slices of an
integer point of `RA(c⃗; d⃗)` are lattice points of `∠(c⃗)`, chained, summing to it. -/
theorem waterFillC_spec (hc : ∀ k, k ≤ n → 0 < c k) (hlc : LogConcave c n) (hn : 1 ≤ n)
    {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {z : Fin (N + 1) → ℤ}
    (hz : castR z ∈ ∑ i, shiftIncl N (d i) '' legSimplex c n) :
    (∀ i, waterFillC c n d z i ∈ latticePtsC c n) ∧
      ChainedC c d (fun i => castR (waterFillC c n d z i)) ∧
      ∑ i, shiftZ N (d i) (waterFillC c n d z i) = z := by
  rw [hull_legSkel_eq hc hn] at hz
  obtain ⟨p, hp, hch, hsum⟩ := exists_chainedC_chain hc hlc hn hd hN hz
  have hpw : (fun i => castR (waterFillC c n d z i)) = p :=
    funext fun i => (chainedC_integral hc hn hd hN hp hch hsum i).symm
  refine ⟨fun i => ?_, by rw [hpw]; exact hch, ?_⟩
  · show castR _ ∈ legSimplex c n
    rw [hull_legSkel_eq hc hn, congrFun hpw i]; exact hp i
  · apply castR_injective
    rw [castR_sum, ← hsum]
    refine sum_congr rfl fun i _ => ?_
    rw [castR_shiftZ]
    exact congrArg _ (congrFun hpw i)

/-- **`cor-additivity`**, general full leg vector:
`RA(c⃗; d⃗) ∩ ℤ^{N+1} = ∑ᵢ shift^{dᵢ}(∠(c⃗) ∩ ℤ^{n+1})`. -/
theorem cor_additivityC (hc : ∀ k, k ≤ n → 0 < c k) (hlc : LogConcave c n) (hn : 1 ≤ n)
    {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d) (hN : ∀ i, d i + n ≤ N) :
    {z : Fin (N + 1) → ℤ | castR z ∈ ∑ i, shiftIncl N (d i) '' legSimplex c n} =
      ∑ i, shiftZ N (d i) '' latticePtsC c n := by
  ext z
  rw [Set.mem_ofPred_eq]
  constructor
  · intro hz
    obtain ⟨hmem, -, hsum⟩ := waterFillC_spec hc hlc hn hd hN hz
    rw [Set.mem_fintype_sum]
    exact ⟨fun i => shiftZ N (d i) (waterFillC c n d z i), fun i => ⟨_, hmem i, rfl⟩, hsum⟩
  · rw [Set.mem_fintype_sum]
    rintro ⟨g, hg, rfl⟩
    choose q hq hqg using hg
    rw [castR_sum]
    refine Set.finsetSum_mem_finsetSum _ _ _ fun i _ => ?_
    rw [← hqg i, castR_shiftZ]
    exact Set.mem_image_of_mem _ (hq i)

/-- **`cor-additivity`, the bijection**: every lattice point of `RA(c⃗; d⃗)` is the
shifted sum of exactly one chained tuple of lattice points of `∠(c⃗)`. -/
theorem existsUnique_chainedC_lattice (hc : ∀ k, k ≤ n → 0 < c k) (hlc : LogConcave c n)
    (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ}
    (hd : Monotone d) (hN : ∀ i, d i + n ≤ N) {z : Fin (N + 1) → ℤ}
    (hz : castR z ∈ ∑ i, shiftIncl N (d i) '' legSimplex c n) :
    ∃! q : Fin r → Fin (n + 1) → ℤ, (∀ i, q i ∈ latticePtsC c n) ∧
      ChainedC c d (fun i => castR (q i)) ∧ ∑ i, shiftZ N (d i) (q i) = z := by
  refine ⟨waterFillC c n d z, waterFillC_spec hc hlc hn hd hN hz, ?_⟩
  rintro q ⟨hq, hcq, hsq⟩
  obtain ⟨hw, hcw, hsw⟩ := waterFillC_spec hc hlc hn hd hN hz
  have hmem : ∀ (q : Fin r → Fin (n + 1) → ℤ), (∀ i, q i ∈ latticePtsC c n) →
      ∀ i, castR (q i) ∈ legChain c n := fun q hq i => by
    rw [← hull_legSkel_eq hc hn]; exact hq i
  have hs : ∀ (q : Fin r → Fin (n + 1) → ℤ),
      ∑ i, shiftIncl N (d i) (castR (q i)) = castR (∑ i, shiftZ N (d i) (q i)) := by
    intro q; rw [castR_sum]; exact sum_congr rfl fun i _ => (castR_shiftZ _ _ _).symm
  have := chainedC_unique hc hn hd hN (hmem q hq) (hmem _ hw) hcq hcw
    (by rw [hs, hs, hsq, hsw])
  funext i
  exact castR_injective (congrFun this i)

theorem convex_RA (c : ℕ → ℕ) {r N : ℕ} (d : Fin r → ℕ) :
    Convex ℝ (∑ i, shiftIncl (n := n) N (d i) '' legSimplex c n) :=
  convex_sum _ fun _ _ => (convex_convexHull ℝ _).linear_image _

/-- **`cor-idp`**, general full leg vector, every sorted `d⃗`: an integer point of
`t·RA(c⃗; d⃗)` (`t ≥ 1`) is a sum of `t` lattice points of `RA(c⃗; d⃗)`, and
conversely. -/
theorem cor_idpC (hc : ∀ k, k ≤ n → 0 < c k) (hlc : LogConcave c n) (hn : 1 ≤ n)
    {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {t : ℕ} (ht : 0 < t) (z : Fin (N + 1) → ℤ) :
    castR z ∈ (t : ℝ) • ∑ i, shiftIncl N (d i) '' legSimplex c n ↔
      ∃ y : Fin t → Fin (N + 1) → ℤ,
        (∀ s, castR (y s) ∈ ∑ i, shiftIncl N (d i) '' legSimplex c n) ∧
          ∑ s, y s = z := by
  have htR : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Set.mem_smul_set.mp hz
    rw [Set.mem_fintype_sum] at hw
    obtain ⟨g, hg, hgw⟩ := hw
    choose k hk hkg using hg
    let e : Fin r × Fin t ≃ Fin (r * t) := finProdFinEquiv
    let d' : Fin (r * t) → ℕ := fun j => d (e.symm j).1
    have hd'e : ∀ i s, d' (e (i, s)) = d i := by intro i s; simp [d']
    have hd' : Monotone d' := by
      intro a b hab
      apply hd
      simp only [e, finProdFinEquiv_symm_apply, Fin.le_def, Fin.coe_divNat]
      exact Nat.div_le_div_right (Fin.le_def.mp hab)
    have hN' : ∀ j, d' j + n ≤ N := fun j => hN _
    have hz' : castR z ∈ ∑ j, shiftIncl N (d' j) '' legSimplex c n := by
      rw [Set.mem_fintype_sum]
      refine ⟨fun j => shiftIncl N (d' j) (k (e.symm j).1),
        fun j => Set.mem_image_of_mem _ (hk _), ?_⟩
      rw [← hwz, ← hgw, ← e.sum_comp, Fintype.sum_prod_type, smul_sum]
      refine sum_congr rfl fun i _ => ?_
      simp only [Equiv.symm_apply_apply, d']
      rw [sum_const, card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, hkg i]
    obtain ⟨hq, -, hqs⟩ := waterFillC_spec hc hlc hn hd' hN' hz'
    set q := waterFillC c n d' z with hqdef
    refine ⟨fun s => ∑ i, shiftZ N (d i) (q (e (i, s))), fun s => ?_, ?_⟩
    · rw [castR_sum]
      refine Set.finsetSum_mem_finsetSum _ _ _ fun i _ => ?_
      rw [castR_shiftZ]
      exact Set.mem_image_of_mem _ (hq _)
    · rw [← hqs, ← e.sum_comp, Fintype.sum_prod_type, sum_comm]
      refine sum_congr rfl fun s _ => sum_congr rfl fun i _ => ?_
      rw [hd'e]
  · rintro ⟨y, hy, rfl⟩
    refine Set.mem_smul_set.mpr ⟨∑ s, (1 / (t : ℝ)) • castR (y s), ?_, ?_⟩
    · refine (convex_RA c d).sum_mem (fun s _ => by positivity) ?_ (fun s _ => hy s)
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · rw [smul_sum, castR_sum]
      refine sum_congr rfl fun s _ => ?_
      rw [smul_smul, mul_one_div_cancel htR.ne', one_smul]

/-! ## The Kozlov instance agrees with `ChainedExistence.lean` -/

theorem choose_pos' (n : ℕ) : ∀ k, k ≤ n → 0 < n.choose k := fun _ hk => Nat.choose_pos hk

theorem logConcave_choose (n : ℕ) : LogConcave (fun k => n.choose k) n := by
  intro k hk _
  have := choose_succ_mul_le n k (k - 1) (by omega)
  rw [show k - 1 + 1 = k by omega] at this
  simpa [sq, mul_comm] using this

theorem legChain_choose : legChain (fun k => n.choose k) n = lymChain n := by
  ext x
  simp only [legChain, lymChain, Set.mem_ofPred_eq, Nat.choose_zero_right,
    Nat.cast_one, Nat.choose_one_right]

theorem legSimplex_choose (hn : 1 ≤ n) :
    legSimplex (fun k => n.choose k) n = convexHull ℝ (Sset n) := by
  rw [hull_legSkel_eq (choose_pos' n) hn, legChain_choose, hull_Sset_eq hn]

theorem chainedC_choose_iff {r : ℕ} (d : Fin r → ℕ) (p : Fin r → Fin (n + 1) → ℝ) :
    ChainedC (fun k => n.choose k) d p ↔ ChainedR d p := Iff.rfl

theorem waterFillC_choose {r N : ℕ} (d : Fin r → ℕ) :
    waterFillC (fun k => n.choose k) n d = waterFill (N := N) n d := rfl

theorem latticePtsC_choose (hn : 1 ≤ n) :
    latticePtsC (fun k => n.choose k) n = latticePts n := by
  ext x; simp only [latticePtsC, latticePts, Set.mem_ofPred_eq, legSimplex_choose hn]

/-- `Lattice.exists_chained` recovered from the general theorem. -/
theorem exists_chained_of_general (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {x : Fin (N + 1) → ℝ}
    (hx : x ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)) :
    ∃ p : Fin r → Fin (n + 1) → ℝ, (∀ i, p i ∈ convexHull ℝ (Sset n)) ∧ ChainedR d p ∧
      ∑ i, shiftIncl N (d i) (p i) = x := by
  rw [← legSimplex_choose hn] at hx ⊢
  exact exists_chainedC (choose_pos' n) (logConcave_choose n) hn hd hN hx

/-- `Lattice.cor_additivity` recovered from the general theorem. -/
theorem cor_additivity_of_general (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) :
    {z : Fin (N + 1) → ℤ | castR z ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)} =
      ∑ i, shiftZ N (d i) '' latticePts n := by
  rw [← legSimplex_choose hn, ← latticePtsC_choose hn]
  exact cor_additivityC (choose_pos' n) (logConcave_choose n) hn hd hN

/-- `Lattice.cor_idp` recovered from the general theorem. -/
theorem cor_idp_of_general (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {t : ℕ} (ht : 0 < t) (z : Fin (N + 1) → ℤ) :
    castR z ∈ (t : ℝ) • ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n) ↔
      ∃ y : Fin t → Fin (N + 1) → ℤ,
        (∀ s, castR (y s) ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)) ∧
          ∑ s, y s = z := by
  rw [← legSimplex_choose hn]
  exact cor_idpC (choose_pos' n) (logConcave_choose n) hn hd hN ht z

/-- `Lattice.chainedR_unique` recovered (uniqueness needs no log-concavity). -/
theorem chainedR_unique_of_general (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {p q : Fin r → Fin (n + 1) → ℝ}
    (hp : ∀ i, p i ∈ lymChain n) (hq : ∀ i, q i ∈ lymChain n)
    (hcp : ChainedR d p) (hcq : ChainedR d q)
    (h : ∑ i, shiftIncl N (d i) (p i) = ∑ i, shiftIncl N (d i) (q i)) : p = q := by
  rw [← legChain_choose] at hp hq
  exact chainedC_unique (choose_pos' n) hn hd hN hp hq hcp hcq h

/-! ## Log-concavity is needed: `c⃗ = (1,2,1,3,1,3)`, `d⃗ = (0,1)` (`rem-chained-credit`) -/

/-- The paper's leg vector `(1,2,1,3,1,3)` (extended by `1`, irrelevant beyond `n = 5`). -/
def cBad : ℕ → ℕ := fun k => [1, 2, 1, 3, 1, 3].getD k 1

/-- The shift vector `(0, 1)`. -/
def dBad : Fin 2 → ℕ := ![0, 1]

/-- The lattice point `F̃₅ + shift F̃₁ = (1,3,3,3,1,3,0)` of `RA(c⃗; 0,1)`. -/
def xBad : Fin 7 → ℤ := ![1, 3, 3, 3, 1, 3, 0]

theorem cBad_pos : ∀ k, k ≤ 5 → 0 < cBad k := by
  intro k hk; interval_cases k <;> decide

theorem not_logConcave_cBad : ¬ LogConcave cBad 5 := fun h => by
  have := h 4 (by norm_num) (by norm_num); revert this; decide

theorem xBad_mem : castR xBad ∈ ∑ i, shiftIncl 6 (dBad i) '' legSimplex cBad 5 := by
  rw [Set.mem_fintype_sum]
  refine ⟨![shiftIncl 6 0 (legSkel cBad 5 5), shiftIncl 6 1 (legSkel cBad 5 1)], fun i => ?_, ?_⟩
  · fin_cases i
    · refine ⟨legSkel cBad 5 5, subset_convexHull ℝ _ ⟨5, by simp, rfl⟩, ?_⟩
      rfl
    · exact ⟨legSkel cBad 5 1, subset_convexHull ℝ _ ⟨1, by simp, rfl⟩, rfl⟩
  · funext k
    simp only [Fin.sum_univ_two, Pi.add_apply, castR_apply, xBad]
    fin_cases k <;> norm_num [shiftIncl_apply, legSkel, cBad]

/-- **Necessity of log-concavity, machine-checked.** For `c⃗ = (1,2,1,3,1,3)` (not
log-concave on `(c₂,…,c₅)`) and `d⃗ = (0,1)`, the lattice point
`(1,3,3,3,1,3,0) = F̃₅ + shift F̃₁` of `RA(c⃗; d⃗)` has **no** chained decomposition into
real points of `∠(c⃗)`: the water-filling formula (valid without log-concavity) forces
`p₁ = (1,2,1,2,0,2)`, which violates `μ₅ ≤ μ₄`. -/
theorem no_chained_cBad : ¬ ∃ p : Fin 2 → Fin 6 → ℝ, (∀ i, p i ∈ legSimplex cBad 5) ∧
    ChainedC cBad dBad p ∧ ∑ i, shiftIncl 6 (dBad i) (p i) = castR xBad := by
  rintro ⟨p, hp, hch, hsum⟩
  rw [hull_legSkel_eq cBad_pos (by norm_num)] at hp
  have hd : Monotone dBad := by
    intro a b hab; fin_cases a <;> fin_cases b <;> simp_all [dBad]
  have hN : ∀ i, dBad i + 5 ≤ 6 := by intro i; fin_cases i <;> simp [dBad]
  have h4 := chainedC_formula cBad_pos (by norm_num) hd hN hp hch 0 4
  have h5 := chainedC_formula cBad_pos (by norm_num) hd hN hp hch 0 5
  rw [hsum] at h4 h5
  have hf : univ.filter (fun l : Fin 2 => (0 : Fin 2) < l) = {1} := by decide
  rw [hf, sum_singleton] at h4 h5
  norm_num [getR, xBad, capC, dBad, cBad] at h4 h5
  have hc := (hp 0).2.2.1 4 (by norm_num) (by norm_num)
  have e4 : p 0 ⟨4, by omega⟩ = p 0 4 := rfl
  have e5 : p 0 ⟨4 + 1, by omega⟩ = p 0 5 := rfl
  rw [e4, e5, h4, h5] at hc
  norm_num [cBad] at hc

end Leg

end Lattice

end ExteriorConvex
