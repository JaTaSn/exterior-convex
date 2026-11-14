/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Lattice points of the Kozlov simplex and of its dilates

Formalisation of the lattice-point layer of `article/exterior-convex_article3_draft_4.org`
(§"Lattice points: the canonical chained decomposition": `thm-chained`(2), `cor-additivity`
and `cor-idp` at `d⃗ = 0`) and of `working-notes/kozlov-polytope-volume-and-ehrhart.org`
§§"The canonical chained decomposition", "Corollary: lattice-point additivity", "Corollary:
the integer decomposition property", "Lean candidates" 1 and 2.

**Normalisation.** Degree-0-inclusive coordinates throughout, as in `Spine/LYM.lean`:
`Fin (n + 1)`, entry `i` = `f_i`, so `f₀ = 1`, `f₁ = n` on `Koz(n)`. `Koz(n)` is
`convexHull ℝ (Sset n)` (`def-kozsimplex`), equal to `lymChain n` for `n ≥ 1` by
`hull_Sset_eq`. Lattice points are `ℤ`-vectors `x : Fin (n + 1) → ℤ`, put into `ℝ^{n+1}` by
`castR` (coordinatewise `Int.cast`). Most theorems carry `1 ≤ n`, as `hull_Sset_eq` does.

* `latticePts n` is `𝓛_n = Koz(n) ∩ ℤ^{n+1}`; `intLYM n` the integer LYM chains (`f₀ = 1`,
  `f₁ = n`, `f_{j+1}·C(n,j) ≤ f_j·C(n,j+1)` for `1 ≤ j ≤ n−1`, `f_n ≥ 0`, cross-multiplied).
  `latticePts_eq_intLYM`: they are equal (target 1). `latticeFinset` is the same set as a
  decidable `Finset` (`coe_latticeFinset`), with `#𝓛_n = 1, 2, 5, 20` for `n = 1, …, 4`
  checked by kernel `decide` (`card_latticeFinset_*`; no `native_decide`).
* `lymChainAt n t` is the level-`t` chain set (`x₀ = t`, `x₁ = t·n`, the LYM chain,
  `x_n ≥ 0`). `smul_lymChain`: it is `t • Koz(n)` for `t > 0`. `sum_lymChain`: it is the
  `r`-fold Minkowski sum `Koz(n) + ⋯ + Koz(n)` for `t = r ∈ ℕ`.
* `capZ`/`capR` is the cap `min(x_j, C(n,j))`, Brändén–Solus's `λ ∧ s`. `peel`: on
  `(t+1)·Koz(n)` the cap lies in `Koz(n)` and the remainder `max(x − C, 0)` in `t·Koz(n)`.
* `idp_two` / `idp_two'` (target 3): every integer point of `Koz(n) + Koz(n)` is
  `capZ x + (x − capZ x)` with both parts in `𝓛_n`. `lattice_sum_iff` / `lattice_sum_eq`
  (stretch target): `(Koz(n) + ⋯ + Koz(n)) ∩ ℤ = 𝓛_n + ⋯ + 𝓛_n` for every `r`, which is
  `cor-additivity` at `d⃗ = 0`. `idp`: the same for the dilate `r • Koz(n)` (`r ≥ 1`), which is
  `cor-idp` for `Koz(n)` itself. The `d⃗ = 0` decomposition is due to Brändén–Solus
  (FPSAC 2020, Thm 2.1).
* `chained_unique` (target 2, **every shift vector `d`**, not only `d⃗ = 0`): two tuples of
  lattice points that are `Chained d` and have equal shifted sums `∑ᵢ shift^{dᵢ}(pᵢ)` in
  `ℝ^{N+1}` are equal. This reuses `Counting/Chaining.lean`'s `Phi`, `Chained`, `Qclamp`,
  `greedySlice`, `chained_dichotomy`, …, and its box form of Theorem A
  (`eq_of_phi_eq_phi_box`), which needs only the binomial box `s(m) ≤ C(n,m)`.
  `Chained` is on the `ℕ`-images `toN (p i)`. There `top` is the paper's `tp` and
  `indeg = fl + 1`, so `Chained` is `def-chained-points`' `tp(p_{i−1}) + d_{i−1} ≤
  fl(p_i) + d_i`, in its strict form. Neither sortedness of `d` nor log-concavity is used.
  The ambient-size hypothesis `d i + n ≤ N` stands in for the paper's `N = n + d_r`.

**Not formalised:** existence of a *chained* decomposition (`thm-chained`(1),(3)), even at
`d⃗ = 0`. `idp_two`/`lattice_sum_iff` give a decomposition but do not prove that it is
chained (it is, in reverse order: the cap is the fullest summand). Also not formalised: the
positive-gap additivity `cor-additivity` for `d⃗ ≠ 0` (which needs log-concavity, through
existence), and the lecture-hall identification.

Changelog (newest first):
2026-10-21 local box copies of Theorem A (`Qclamp_phi_box`, `greedySlice_phi_box`,
`eq_of_phi_eq_phi_box` and two single-component lemmas) deleted; `chained_unique` now uses
`Counting/Chaining.lean`'s `eq_of_phi_eq_phi_box` (Claude-Code agent, housekeeping)
2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Spine.KozlovThm
import ExteriorConvex.Counting.Chaining

open Finset
open scoped Pointwise

namespace ExteriorConvex

namespace Lattice

variable {n : ℕ}

/-! ## Integer vectors and their real images -/

/-- The inclusion `ℤ^{m} → ℝ^{m}`, coordinatewise. -/
def castR {m : ℕ} (x : Fin m → ℤ) : Fin m → ℝ := fun i => (x i : ℝ)

@[simp] theorem castR_apply {m : ℕ} (x : Fin m → ℤ) (i : Fin m) :
    castR x i = (x i : ℝ) := rfl

theorem castR_injective {m : ℕ} : Function.Injective (castR (m := m)) :=
  fun x y h => funext fun i => by
    have := congrFun h i
    simp only [castR_apply] at this
    exact_mod_cast this

theorem castR_add {m : ℕ} (x y : Fin m → ℤ) :
    castR (x + y) = castR x + castR y := by
  funext i; simp

theorem castR_sub {m : ℕ} (x y : Fin m → ℤ) :
    castR (x - y) = castR x - castR y := by
  funext i; simp

theorem castR_sum {m r : ℕ} (p : Fin r → Fin m → ℤ) :
    castR (∑ i, p i) = ∑ i, castR (p i) := by
  funext j
  simp [Finset.sum_apply]

theorem castR_zero {m : ℕ} : castR (0 : Fin m → ℤ) = 0 := by
  funext i; simp

/-! ## The lattice points `𝓛_n` and the integer LYM chains -/

/-- `𝓛_n = Koz(n) ∩ ℤ^{n+1}` (article 3, §`sec-setup`), with `Koz(n)` taken
literally as `conv(S_n)` (`def-kozsimplex`), in the degree-0-inclusive space. -/
def latticePts (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {x | castR x ∈ convexHull ℝ (Sset n)}

/-- Integer LYM chains: `f₀ = 1`, `f₁ = n`, and the LYM chain
`f_{j+1}/C(n,j+1) ≤ f_j/C(n,j)` (`1 ≤ j ≤ n−1`), `f_n ≥ 0`, written
cross-multiplied so that it is a statement about integers only. -/
def intLYM (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {x | x 0 = 1 ∧ x 1 = n ∧
    (∀ j, (hj : 1 ≤ j) → (hjn : j ≤ n - 1) →
      x ⟨j + 1, by omega⟩ * (n.choose j : ℤ) ≤
        x ⟨j, by omega⟩ * (n.choose (j + 1) : ℤ)) ∧
    0 ≤ x (Fin.last n)}

/-- An integer vector lies in the real LYM chain set iff it is an integer
LYM chain. -/
theorem castR_mem_lymChain_iff (hn : 1 ≤ n) (x : Fin (n + 1) → ℤ) :
    castR x ∈ lymChain n ↔ x ∈ intLYM n := by
  have hC : ∀ k, k ≤ n → (0 : ℝ) < (n.choose k : ℝ) := fun k hk =>
    Nat.cast_pos.mpr (Nat.choose_pos hk)
  simp only [lymChain, intLYM, Set.mem_ofPred_eq, castR_apply]
  refine and_congr (by exact_mod_cast Iff.rfl) (and_congr (by exact_mod_cast Iff.rfl)
    (and_congr ?_ (by exact_mod_cast Iff.rfl)))
  refine forall_congr' fun j => forall_congr' fun hj => forall_congr' fun hjn => ?_
  rw [div_le_div_iff₀ (hC _ (by omega)) (hC _ (by omega))]
  exact_mod_cast Iff.rfl

/-- **Target 1** (Lean candidate / item 6): the lattice points of `Koz(n)`
are exactly the integer LYM chains. -/
theorem latticePts_eq_intLYM (hn : 1 ≤ n) : latticePts n = intLYM n := by
  ext x
  simp only [latticePts, Set.mem_ofPred_eq]
  rw [hull_Sset_eq hn]
  exact castR_mem_lymChain_iff hn x

/-! ## A decidable `Finset` form, and the small counts -/

/-- A decidable restatement of `intLYM`: the chain is quantified over pairs of
`Fin` indices instead of over `ℕ` with dependent bounds. -/
def IntLYMb (n : ℕ) (x : Fin (n + 1) → ℤ) : Prop :=
  x 0 = 1 ∧ x 1 = n ∧
    (∀ j k : Fin (n + 1), k.val = j.val + 1 → 1 ≤ j.val →
      x k * (n.choose j.val : ℤ) ≤ x j * (n.choose k.val : ℤ)) ∧
    0 ≤ x (Fin.last n)

instance (n : ℕ) : DecidablePred (IntLYMb n) := fun x => by
  unfold IntLYMb; infer_instance

theorem intLYMb_iff (x : Fin (n + 1) → ℤ) : IntLYMb n x ↔ x ∈ intLYM n := by
  simp only [IntLYMb, intLYM, Set.mem_ofPred_eq]
  refine and_congr Iff.rfl (and_congr Iff.rfl (and_congr ⟨fun h j hj hjn => ?_,
    fun h j k hk hj => ?_⟩ Iff.rfl))
  · exact h ⟨j, by omega⟩ ⟨j + 1, by omega⟩ rfl hj
  · have hjn : j.val ≤ n - 1 := by omega
    obtain ⟨k, hkl⟩ := k
    simp only at hk
    subst hk
    exact h j.val hj hjn

/-- `𝓛_n` as an explicit `Finset`: the integer LYM chains inside the binomial
box `0 ≤ x_j ≤ C(n,j)`. -/
def latticeFinset (n : ℕ) : Finset (Fin (n + 1) → ℤ) :=
  (Fintype.piFinset fun j : Fin (n + 1) => Finset.Icc (0 : ℤ) (n.choose j.val)).filter
    (IntLYMb n)

/-! The counts `#𝓛_n = 1, 2, 5, 20` for `n = 1, 2, 3, 4` (article 3: `𝓛_2 = S_2`,
`#𝓛_3 = 5`, and the twenty lattice points of `Koz(4)`), by kernel `decide`. -/

theorem card_latticeFinset_one : (latticeFinset 1).card = 1 := by decide
theorem card_latticeFinset_two : (latticeFinset 2).card = 2 := by decide
theorem card_latticeFinset_three : (latticeFinset 3).card = 5 := by decide
set_option maxRecDepth 100000 in
theorem card_latticeFinset_four : (latticeFinset 4).card = 20 := by decide

/-! ## The chain set at level `t`: the dilate `t·Koz(n)` -/

/-- The LYM chain set at level `t`: `x₀ = t`, `x₁ = t·n`, the LYM chain, and
`x_n ≥ 0`.  For `t > 0` this is `t • lymChain n` (`smul_lymChain`), i.e. the
dilate `t·Koz(n)`; for `t = r ∈ ℕ` it is the `r`-fold Minkowski sum
(`sum_lymChain`). -/
def lymChainAt (n : ℕ) (t : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {x | x 0 = t ∧ x 1 = t * n ∧
    (∀ j, (hj : 1 ≤ j) → (hjn : j ≤ n - 1) →
      x ⟨j + 1, by omega⟩ / (n.choose (j + 1) : ℝ) ≤
        x ⟨j, by omega⟩ / (n.choose j : ℝ)) ∧
    0 ≤ x (Fin.last n)}

theorem lymChainAt_one : lymChainAt n 1 = lymChain n := by
  ext x
  simp [lymChainAt, lymChain]

/-- The LYM ratios of a level-`t` chain decrease along `[1, n]`. -/
theorem muOf_antitone {t : ℝ} {x : Fin (n + 1) → ℝ} (hx : x ∈ lymChainAt n t)
    {i : ℕ} (hi : 1 ≤ i) : ∀ j, i ≤ j → j ≤ n → muOf n x j ≤ muOf n x i := by
  intro j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ k hik ih =>
    intro hk
    have h := hx.2.2.1 k (by omega) (by omega)
    have ih' := ih (by omega)
    rw [muOf_of_le (by omega)] at ih' ⊢
    exact le_trans h ih'

/-- `μ₁ = t` on a level-`t` chain. -/
theorem muOf_one {t : ℝ} {x : Fin (n + 1) → ℝ} (hn : 1 ≤ n)
    (hx : x ∈ lymChainAt n t) : muOf n x 1 = t := by
  rw [muOf_of_le hn, ← fin_one_eq hn, hx.2.1, Nat.choose_one_right,
    mul_div_assoc, div_self (Nat.cast_ne_zero.mpr (by omega : n ≠ 0)), mul_one]

/-- The box bound: on a level-`t` chain, `0 ≤ x_j ≤ t·C(n,j)` for `j ≥ 1`. -/
theorem box_of_mem_lymChainAt {t : ℝ} {x : Fin (n + 1) → ℝ} (hn : 1 ≤ n)
    (hx : x ∈ lymChainAt n t) (j : Fin (n + 1)) (hj : 1 ≤ j.val) :
    0 ≤ x j ∧ x j ≤ t * (n.choose j.val : ℝ) := by
  have hC : (0 : ℝ) < (n.choose j.val : ℝ) :=
    Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have hup := muOf_antitone hx (le_refl 1) j.val hj (by omega)
  have hlo := muOf_antitone hx hj n (by omega) le_rfl
  rw [muOf_one hn hx, muOf_of_le (by omega)] at hup
  rw [muOf_of_le le_rfl, muOf_of_le (by omega), Nat.choose_self, Nat.cast_one,
    div_one] at hlo
  have hlast : x ⟨n, Nat.lt_succ_of_le le_rfl⟩ = x (Fin.last n) := rfl
  rw [hlast] at hlo
  have hj' : x ⟨j.val, Nat.lt_succ_of_le (by omega)⟩ = x j := rfl
  rw [hj'] at hup hlo
  refine ⟨?_, ?_⟩
  · have := le_trans hx.2.2.2 hlo
    exact (div_nonneg_iff.mp this).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hC))
  · rwa [div_le_iff₀ hC] at hup

/-- Level `0` is the origin. -/
theorem lymChainAt_zero (hn : 1 ≤ n) : lymChainAt n 0 = {0} := by
  ext x
  constructor
  · intro hx
    funext j
    rcases Nat.eq_zero_or_pos j.val with h0 | hpos
    · rw [show j = 0 from Fin.ext h0, hx.1]; rfl
    · have := box_of_mem_lymChainAt hn hx j hpos
      rw [zero_mul] at this
      exact le_antisymm this.2 this.1
  · rintro rfl
    refine ⟨rfl, by simp, fun j _ _ => by simp, le_rfl⟩

/-- Levels add. -/
theorem add_mem_lymChainAt {a b : ℝ} {x y : Fin (n + 1) → ℝ}
    (hx : x ∈ lymChainAt n a) (hy : y ∈ lymChainAt n b) :
    x + y ∈ lymChainAt n (a + b) := by
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  obtain ⟨hy0, hy1, hyc, hyn⟩ := hy
  refine ⟨by simp [hx0, hy0], by simp [hx1, hy1, add_mul], fun j hj hjn => ?_,
    by simpa using add_nonneg hxn hyn⟩
  simp only [Pi.add_apply, add_div]
  exact add_le_add (hxc j hj hjn) (hyc j hj hjn)

/-- Scaling: for `t > 0`, `t • Koz(n) = lymChainAt n t` (inclusively). -/
theorem smul_lymChain {t : ℝ} (ht : 0 < t) : t • lymChain n = lymChainAt n t := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, ⟨hy0, hy1, hyc, hyn⟩, rfl⟩
    refine ⟨by simp [hy0], by simp [hy1], fun j hj hjn => ?_,
      by simpa using mul_nonneg ht.le hyn⟩
    simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (hyc j hj hjn) ht.le
  · rintro ⟨hx0, hx1, hxc, hxn⟩
    refine ⟨t⁻¹ • x, ⟨?_, ?_, fun j hj hjn => ?_, ?_⟩, ?_⟩
    · simp [hx0, ht.ne']
    · simp [hx1, ht.ne']
    · simp only [Pi.smul_apply, smul_eq_mul, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hxc j hj hjn) (inv_nonneg.mpr ht.le)
    · simpa using mul_nonneg (inv_nonneg.mpr ht.le) hxn
    · rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]

/-! ## The cap `x ∧ C(n,·)`: Brändén–Solus's `λ ∧ s` -/

/-- The cap `min(x_j, C(n,j))`, coordinatewise, real version. -/
noncomputable def capR (n : ℕ) (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun j => min (x j) (n.choose j.val : ℝ)

/-- The cap `min(x_j, C(n,j))`, coordinatewise, integer version. -/
def capZ (n : ℕ) (x : Fin (n + 1) → ℤ) : Fin (n + 1) → ℤ :=
  fun j => min (x j) (n.choose j.val : ℤ)

theorem castR_capZ (x : Fin (n + 1) → ℤ) : castR (capZ n x) = capR n (castR x) := by
  funext j
  simp [capZ, capR, castR]

private theorem min_div_le_min_div {a b A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : a / A ≤ b / B) : min a A / A ≤ min b B / B := by
  rw [← min_div_div_right hA.le, ← min_div_div_right hB.le, div_self hA.ne',
    div_self hB.ne']
  exact min_le_min h le_rfl

private theorem sub_min_div_le {a b A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    (h : a / A ≤ b / B) : (a - min a A) / A ≤ (b - min b B) / B := by
  rw [sub_div, sub_div, ← min_div_div_right hA.le, ← min_div_div_right hB.le,
    div_self hA.ne', div_self hB.ne']
  generalize a / A = u at h ⊢
  generalize b / B = v at h ⊢
  rcases le_total u 1 with h1 | h1 <;> rcases le_total v 1 with h2 | h2 <;>
    simp only [min_eq_left, min_eq_right, h1, h2] <;> linarith

/-- **The peeling step.**  If `x ∈ (t+1)·Koz(n)` with `t ≥ 0`, then the cap
`min(x, C(n,·))` lies in `Koz(n)` and the remainder `x − min(x, C(n,·)) =
max(x − C(n,·), 0)` lies in `t·Koz(n)`.  In LYM coordinates: `y ↦ min(y, 1)`
and `y ↦ max(y − 1, 0)` both preserve a decreasing chain. -/
theorem peel (hn : 1 ≤ n) {t : ℝ} (ht : 0 ≤ t) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ lymChainAt n (t + 1)) :
    capR n x ∈ lymChain n ∧ x - capR n x ∈ lymChainAt n t := by
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  have hC : ∀ k, k ≤ n → (0 : ℝ) < (n.choose k : ℝ) := fun k hk =>
    Nat.cast_pos.mpr (Nat.choose_pos hk)
  have hn' : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hcap0 : capR n x 0 = 1 := by
    simp only [capR, Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, hx0]
    exact min_eq_right (by linarith)
  have hcap1 : capR n x 1 = n := by
    rw [fin_one_eq hn] at hx1 ⊢
    simp only [capR, hx1, Nat.choose_one_right]
    exact min_eq_right (by nlinarith)
  have hcapn : capR n x (Fin.last n) = min (x (Fin.last n)) 1 := by
    simp [capR]
  refine ⟨⟨hcap0, hcap1, fun j hj hjn => ?_, ?_⟩,
    ⟨?_, ?_, fun j hj hjn => ?_, ?_⟩⟩
  · exact min_div_le_min_div (hC _ (by omega)) (hC _ (by omega)) (hxc j hj hjn)
  · rw [hcapn]; exact le_min hxn zero_le_one
  · rw [Pi.sub_apply, hcap0, hx0]; ring
  · rw [Pi.sub_apply, hcap1, hx1]; ring
  · exact sub_min_div_le (hC _ (by omega)) (hC _ (by omega)) (hxc j hj hjn)
  · rw [Pi.sub_apply, hcapn]; exact sub_nonneg.mpr (min_le_left _ _)

/-- The `r`-fold Minkowski sum of `Koz(n)` with itself is the level-`r` chain
set (inclusively; `Koz(n) = lymChain n` by `hull_Sset_eq`). -/
theorem sum_lymChain (hn : 1 ≤ n) (r : ℕ) :
    ∑ _i : Fin r, lymChain n = lymChainAt n r := by
  induction r with
  | zero => rw [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero,
      lymChainAt_zero hn]; rfl
  | succ r ih =>
    rw [Fin.sum_univ_succ, ih]
    ext x
    rw [Set.mem_add]
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      have := add_mem_lymChainAt (lymChainAt_one (n := n) ▸ ha) hb
      rwa [Nat.cast_succ, add_comm (r : ℝ)]
    · intro hx
      rw [Nat.cast_succ] at hx
      obtain ⟨h1, h2⟩ := peel hn (Nat.cast_nonneg r) hx
      exact ⟨capR n x, h1, x - capR n x, h2, add_sub_cancel _ _⟩

/-! ## Lattice-point additivity at `d⃗ = 0` and the IDP -/

theorem mem_latticePts_iff (hn : 1 ≤ n) (x : Fin (n + 1) → ℤ) :
    x ∈ latticePts n ↔ castR x ∈ lymChain n := by
  simp only [latticePts, Set.mem_ofPred_eq]
  rw [hull_Sset_eq hn]

/-- **Target 3, level 2, with the explicit witness.**  If an integer point `x`
lies in `Koz(n) + Koz(n)`, then `x = min(x, C(n,·)) + max(x − C(n,·), 0)` with
both parts lattice points of `Koz(n)` — Brändén–Solus's `λ = (λ∧s) +
((λ−s)∨0)`. -/
theorem idp_two (hn : 1 ≤ n) {x : Fin (n + 1) → ℤ}
    (hx : castR x ∈ convexHull ℝ (Sset n) + convexHull ℝ (Sset n)) :
    capZ n x ∈ latticePts n ∧ x - capZ n x ∈ latticePts n := by
  rw [hull_Sset_eq hn] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_add.mp hx
  have h2 : castR x ∈ lymChainAt n (0 + 1 + 1) := by
    rw [← hab, zero_add]
    exact add_mem_lymChainAt (lymChainAt_one (n := n) ▸ ha)
      (lymChainAt_one (n := n) ▸ hb)
  obtain ⟨h1, h1'⟩ := peel hn (by norm_num) h2
  rw [mem_latticePts_iff hn, mem_latticePts_iff hn, castR_sub, castR_capZ,
    ← lymChainAt_one]
  exact ⟨lymChainAt_one (n := n) ▸ h1, by rwa [zero_add] at h1'⟩

/-- The same, as the existence statement: every integer point of
`Koz(n) + Koz(n)` is a sum of two lattice points of `Koz(n)`. -/
theorem idp_two' (hn : 1 ≤ n) {x : Fin (n + 1) → ℤ}
    (hx : castR x ∈ convexHull ℝ (Sset n) + convexHull ℝ (Sset n)) :
    ∃ a ∈ latticePts n, ∃ b ∈ latticePts n, a + b = x :=
  ⟨capZ n x, (idp_two hn hx).1, x - capZ n x, (idp_two hn hx).2, add_sub_cancel _ _⟩

/-- The peeling decomposition at every level `r`: an integer point of the
level-`r` chain set is a sum of `r` lattice points of `Koz(n)`, namely the
iterated caps `min(max(x − k·C(n,·), 0), C(n,·))`, `k = 0, …, r−1`. -/
theorem exists_lattice_decomp (hn : 1 ≤ n) :
    ∀ (r : ℕ) (x : Fin (n + 1) → ℤ), castR x ∈ lymChainAt n r →
      ∃ p : Fin r → Fin (n + 1) → ℤ, (∀ i, p i ∈ latticePts n) ∧ ∑ i, p i = x := by
  intro r
  induction r with
  | zero =>
    intro x hx
    rw [Nat.cast_zero, lymChainAt_zero hn] at hx
    refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    exact castR_injective (by rw [castR_zero]; exact hx.symm)
  | succ r ih =>
    intro x hx
    rw [Nat.cast_succ] at hx
    obtain ⟨h1, h2⟩ := peel hn (Nat.cast_nonneg r) hx
    rw [← castR_capZ, ← castR_sub] at h2
    rw [← castR_capZ] at h1
    obtain ⟨p, hp, hsum⟩ := ih _ h2
    refine ⟨Fin.cons (capZ n x) p, fun i => ?_, ?_⟩
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [Fin.cons_zero, mem_latticePts_iff hn]; exact h1
      · rw [Fin.cons_succ]; exact hp i
    · rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      rw [hsum, add_sub_cancel]

/-- **Stretch target: lattice-point additivity at `d⃗ = 0`, every rank `r`.**
An integer point lies in the `r`-fold Minkowski sum `Koz(n) + ⋯ + Koz(n)` iff
it is a sum of `r` lattice points of `Koz(n)`. -/
theorem lattice_sum_iff (hn : 1 ≤ n) (r : ℕ) (x : Fin (n + 1) → ℤ) :
    castR x ∈ ∑ _i : Fin r, convexHull ℝ (Sset n) ↔
      ∃ p : Fin r → Fin (n + 1) → ℤ, (∀ i, p i ∈ latticePts n) ∧ ∑ i, p i = x := by
  rw [hull_Sset_eq hn, sum_lymChain hn]
  constructor
  · exact exists_lattice_decomp hn r x
  · rintro ⟨p, hp, rfl⟩
    rw [← sum_lymChain hn, castR_sum]
    exact Set.finsetSum_mem_finsetSum Finset.univ _ _
      (fun i _ => (mem_latticePts_iff hn (p i)).mp (hp i))

/-- The same as an identity of sets of integer vectors:
`(Koz(n) + ⋯ + Koz(n)) ∩ ℤ^{n+1} = 𝓛_n + ⋯ + 𝓛_n` (`r` summands), the
`d⃗ = 0` case of `cor-additivity`. -/
theorem lattice_sum_eq (hn : 1 ≤ n) (r : ℕ) :
    {x : Fin (n + 1) → ℤ | castR x ∈ ∑ _i : Fin r, convexHull ℝ (Sset n)} =
      ∑ _i : Fin r, latticePts n := by
  ext x
  rw [Set.mem_ofPred_eq, lattice_sum_iff hn, Set.mem_fintype_sum]
  constructor
  · rintro ⟨p, hp, hs⟩; exact ⟨p, fun i => hp i, hs⟩
  · rintro ⟨p, hp, hs⟩; exact ⟨p, fun i => hp i, hs⟩

/-- **The integer decomposition property of `Koz(n)`** (`cor-idp` at
`d⃗ = 0`): for `r ≥ 1`, every lattice point of the dilate `r·Koz(n)` is a sum
of `r` lattice points of `Koz(n)`. -/
theorem idp (hn : 1 ≤ n) {r : ℕ} (hr : 0 < r) (x : Fin (n + 1) → ℤ) :
    castR x ∈ (r : ℝ) • convexHull ℝ (Sset n) ↔
      ∃ p : Fin r → Fin (n + 1) → ℤ, (∀ i, p i ∈ latticePts n) ∧ ∑ i, p i = x := by
  rw [← lattice_sum_iff hn, hull_Sset_eq hn, sum_lymChain hn,
    smul_lymChain (Nat.cast_pos.mpr hr)]

/-! ## Uniqueness of chained decompositions (integer version, all shifts)

Article 2's water-filling inverse (`Counting/Chaining.lean`) is proved under
the binomial box `s(m) ≤ C(n,m)` (`InBox`, `eq_of_phi_eq_phi_box`), not only
for `f`-vectors; downward closure is not used by Theorem A.  So it applies
verbatim to lattice points of `Koz(n)`, as `thm-chained`(2) says ("no
log-concavity needed"). -/

/-- The ℕ-valued image of an integer vector (used only on lattice points of
`Koz(n)`, which are non-negative), so that article 2's ℕ-valued `top`,
`indeg`, `Chained`, `Phi` apply verbatim. -/
def toN (x : Fin (n + 1) → ℤ) : Fin (n + 1) → ℕ := fun j => (x j).toNat

/-- The binomial box on `𝓛_n`: `0 ≤ x_j ≤ C(n,j)` for every `j`, including
`j = 0`. -/
theorem box_of_mem_latticePts (hn : 1 ≤ n) {x : Fin (n + 1) → ℤ}
    (hx : x ∈ latticePts n) (j : Fin (n + 1)) :
    0 ≤ x j ∧ x j ≤ (n.choose j.val : ℤ) := by
  rw [mem_latticePts_iff hn, ← lymChainAt_one] at hx
  rcases Nat.eq_zero_or_pos j.val with h0 | hpos
  · have hj : j = 0 := Fin.ext h0
    have := hx.1
    subst hj
    simp only [castR_apply] at this
    have hx0 : x 0 = 1 := by exact_mod_cast this
    simp [hx0]
  · have := box_of_mem_lymChainAt hn hx j hpos
    simp only [castR_apply, one_mul] at this
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩

/-- The `Finset` is `𝓛_n`: `↑(latticeFinset n) = Koz(n) ∩ ℤ^{n+1}`. -/
theorem coe_latticeFinset (hn : 1 ≤ n) : (latticeFinset n : Set _) = latticePts n := by
  ext x
  simp only [latticeFinset, Finset.coe_filter, Fintype.mem_piFinset, Finset.mem_Icc,
    Set.mem_ofPred_eq, intLYMb_iff, ← latticePts_eq_intLYM hn]
  constructor
  · exact fun h => h.2
  · exact fun h => ⟨fun j => box_of_mem_latticePts hn h j, h⟩

theorem mem_latticeFinset (hn : 1 ≤ n) (x : Fin (n + 1) → ℤ) :
    x ∈ latticeFinset n ↔ x ∈ latticePts n := by
  rw [← coe_latticeFinset hn]; rfl

theorem toN_le_choose (hn : 1 ≤ n) {x : Fin (n + 1) → ℤ}
    (hx : x ∈ latticePts n) (j : Fin (n + 1)) : toN x j ≤ n.choose j.val := by
  have := box_of_mem_latticePts hn hx j
  simp only [toN]
  omega

theorem toN_cast (hn : 1 ≤ n) {x : Fin (n + 1) → ℤ}
    (hx : x ∈ latticePts n) (j : Fin (n + 1)) : ((toN x j : ℕ) : ℤ) = x j :=
  Int.toNat_of_nonneg (box_of_mem_latticePts hn hx j).1

/-- The bridge from the real shift `shiftIncl` (article 1's `shift^d`) to
article 2's absolute-degree placement `shiftAbs`. -/
theorem shiftIncl_castR (hn : 1 ≤ n) {N dk : ℕ} {x : Fin (n + 1) → ℤ}
    (hx : x ∈ latticePts n) (j : Fin (N + 1)) :
    shiftIncl N dk (castR x) j = ((shiftAbs dk (extN (toN x)) j.val : ℕ) : ℝ) := by
  rw [shiftIncl_apply]
  by_cases h : dk ≤ j.val ∧ j.val - dk ≤ n
  · rw [dite_eq_left h, shiftAbs_of_le _ h.1, extN_of_le h.2, castR_apply,
      ← toN_cast hn hx]
    rfl
  · rw [dite_eq_right h]
    by_cases h1 : dk ≤ j.val
    · rw [shiftAbs_of_le _ h1, extN_of_gt (by omega), Nat.cast_zero]
    · rw [shiftAbs_of_lt _ (by omega), Nat.cast_zero]

/-- **Target 2** (Lean candidate 1, `thm-chained`(2) for lattice points, every
shift vector).  Two tuples of lattice points of `Koz(n)`, both chained for `d`
(article 2's `Chained`, i.e. `tp(p_{i}) + d_{i} < indeg(p_{i+1}) + d_{i+1}`),
with equal shifted sums `∑ᵢ shift^{dᵢ}(pᵢ) ∈ ℝ^{N+1}`, are equal.  The
hypothesis `d i + n ≤ N` says the ambient space holds every shifted summand
(the paper's `N = n + d_r` with `d` sorted); no sortedness of `d` and no
log-concavity is needed. -/
theorem chained_unique (hn : 1 ≤ n) {r N : ℕ} (d : Fin r → ℕ)
    (hN : ∀ i, d i + n ≤ N) {p q : Fin r → Fin (n + 1) → ℤ}
    (hp : ∀ i, p i ∈ latticePts n) (hq : ∀ i, q i ∈ latticePts n)
    (hcp : Chained d fun i => toN (p i)) (hcq : Chained d fun i => toN (q i))
    (h : ∑ i, shiftIncl N (d i) (castR (p i)) =
      ∑ i, shiftIncl N (d i) (castR (q i))) :
    p = q := by
  have hvan : ∀ (x : Fin r → Fin (n + 1) → ℕ) (j : ℕ), N < j →
      Phi d x j = 0 := by
    intro x j hj
    refine sum_eq_zero fun k _ => ?_
    have := hN k
    rw [shiftAbs_of_le _ (by omega), extN_of_gt (by omega)]
  have hPhi : Phi d (fun i => toN (p i)) = Phi d (fun i => toN (q i)) := by
    funext j
    by_cases hj : j ≤ N
    · have := congrFun h ⟨j, Nat.lt_succ_of_le hj⟩
      rw [Finset.sum_apply, Finset.sum_apply] at this
      simp only [shiftIncl_castR hn (hp _), shiftIncl_castR hn (hq _)] at this
      exact_mod_cast this
    · rw [hvan _ _ (by omega), hvan _ _ (by omega)]
  have hpq := eq_of_phi_eq_phi_box (fun i => toN_le_choose hn (hp i))
    (fun i => toN_le_choose hn (hq i)) hcp hcq hPhi
  funext i j
  have := congrFun (congrFun hpq i) j
  rw [← toN_cast hn (hp i), ← toN_cast hn (hq i)]
  exact_mod_cast this

end Lattice

end ExteriorConvex
