/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

Changelog (newest first):
- 2026-10-20  Created (article-3 overnight push): manuscript-coordinate accessor `co`, and Fact 1 of
              `working-notes/kozlov-hdescription-proof-2026-10-20.org` (`chain_hull_eq`) for a
              general positive leg vector and a general shift.

# Fact 1: the right-angle simplex of a general positive leg vector is a μ-chain set

`Spine/LYM.lean`'s `hull_skel_eq` proves `lem-mu` for the Kozlov skeleta, in the
degree-0-inclusive space `Fin (n+1) → ℝ`.  This file proves the general-leg, degree-0-dropped,
shifted analogue, in the space `Fin N → ℝ` of `Vertices/` (vertices `ravA a N d k`, vertex set
`vsetA a N d n`, both from `Vertices/ExtremalMatrix.lean`):

    conv{ shift^d v(1), …, shift^d v(n) } =
      { x : x vanishes off [d+1, d+n], x(d+1) = a(1),
            x(d+j+1)·a(j) ≤ x(d+j)·a(j+1) (1 ≤ j < n), x(d+n) ≥ 0 }.

The chain condition is stated without division: for positive `a` it is `μ(j+1) ≤ μ(j)` with
`μ(j) = x(d+j)/a(j)`.

**Index convention.**  To keep all coordinate arithmetic in `ℕ`, points are read through
`co x c`, the manuscript coordinate `c` (1-based) of `x : Fin N → ℝ`, extended by `0` outside
`[1, N]`.  So `co x c = x ⟨c-1, _⟩` for `1 ≤ c ≤ N`, matching `Vertices/`'s convention that
`c : Fin N` stands for the manuscript's coordinate `c.val + 1`.
-/
import Mathlib
import ExteriorConvex.Vertices.ExtremalMatrix

namespace ExteriorConvex
namespace Facets

open Finset Pointwise

variable {N : ℕ}

/-! ## Manuscript coordinates -/

/-- The manuscript coordinate `c` (1-based) of `x`, and `0` outside `[1, N]`. -/
def co (x : Fin N → ℝ) (c : ℕ) : ℝ :=
  if h : 1 ≤ c ∧ c ≤ N then x ⟨c - 1, by omega⟩ else 0

lemma co_of (x : Fin N → ℝ) {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ N) :
    co x c = x ⟨c - 1, by omega⟩ := dif_pos ⟨h1, h2⟩

lemma co_eq_zero (x : Fin N → ℝ) {c : ℕ} (h : c = 0 ∨ N < c) : co x c = 0 :=
  dif_neg (by omega)

lemma co_val (x : Fin N → ℝ) (i : Fin N) : x i = co x (i.val + 1) := by
  rw [co_of x (by omega) (by omega)]
  rfl

lemma ext_co {x y : Fin N → ℝ} (h : ∀ c, 1 ≤ c → c ≤ N → co x c = co y c) : x = y := by
  funext i
  rw [co_val x i, co_val y i]
  exact h _ (by omega) (by omega)

@[simp] lemma co_add (x y : Fin N → ℝ) (c : ℕ) : co (x + y) c = co x c + co y c := by
  unfold co; split_ifs <;> simp

@[simp] lemma co_smul (t : ℝ) (x : Fin N → ℝ) (c : ℕ) : co (t • x) c = t * co x c := by
  unfold co; split_ifs <;> simp

lemma co_sum {ι : Type*} (s : Finset ι) (f : ι → Fin N → ℝ) (c : ℕ) :
    co (∑ i ∈ s, f i) c = ∑ i ∈ s, co (f i) c := by
  unfold co; split_ifs <;> simp [Finset.sum_apply]

/-- The vertex `ravA a N d k = shift^d v(k)` in manuscript coordinates. -/
lemma co_ravA (a : ℕ → ℝ) (d k c : ℕ) :
    co (ravA a N d k) c = if 1 ≤ c ∧ c ≤ N ∧ d < c ∧ c ≤ d + k then a (c - d) else 0 := by
  unfold co
  by_cases h : 1 ≤ c ∧ c ≤ N
  · rw [dif_pos h]
    simp only [ravA]
    have e : c - 1 + 1 = c := by omega
    simp only [e]
    by_cases h' : d < c ∧ c ≤ d + k
    · rw [if_pos (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), if_neg (by omega)]
  · rw [dif_neg h, if_neg (by omega)]

/-! ## The chain set, and Fact 1 -/

/-- The μ-chain set of `shift^d ∠(a)`: support in `[d+1, d+n]`, `μ(1) = 1`, `μ` non-increasing,
`μ(n) ≥ 0`, with `μ(j) = x(d+j)/a(j)` and the chain written without division. -/
def chainSet (a : ℕ → ℝ) (N d n : ℕ) : Set (Fin N → ℝ) :=
  {x | (∀ c, c ≤ d → co x c = 0) ∧ (∀ c, d + n < c → co x c = 0) ∧ co x (d + 1) = a 1 ∧
    (∀ j, 1 ≤ j → j < n → co x (d + j + 1) * a j ≤ co x (d + j) * a (j + 1)) ∧
    0 ≤ co x (d + n)}

/-- `∠(a)` shifted by `d`, as a convex hull in `Fin N → ℝ`. -/
abbrev angle (a : ℕ → ℝ) (N d n : ℕ) : Set (Fin N → ℝ) := convexHull ℝ (vsetA a N d n)

theorem convex_chainSet (a : ℕ → ℝ) (N d n : ℕ) : Convex ℝ (chainSet a N d n) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; simp [hx1 c hc, hy1 c hc]
  · intro c hc; simp [hx2 c hc, hy2 c hc]
  · simp only [co_add, co_smul, hx3, hy3]
    linear_combination (a 1) * hst
  · intro j hj hjn
    have h1 := mul_le_mul_of_nonneg_left (hx4 j hj hjn) hs
    have h2 := mul_le_mul_of_nonneg_left (hy4 j hj hjn) ht
    simp only [co_add, co_smul]
    nlinarith
  · simp only [co_add, co_smul]
    exact add_nonneg (mul_nonneg hs hx5) (mul_nonneg ht hy5)

/-- Every vertex lies in the chain set. -/
theorem vsetA_subset_chainSet (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {d n : ℕ} (hn : 1 ≤ n)
    (hN : d + n ≤ N) : vsetA a N d n ⊆ chainSet a N d n := by
  rintro _ ⟨k, hk, rfl⟩
  rw [Set.mem_Icc] at hk
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; rw [co_ravA, if_neg (by omega)]
  · intro c hc; rw [co_ravA, if_neg (by omega)]
  · rw [co_ravA, if_pos (by omega)]
    congr 1; omega
  · intro j hj hjn
    rw [co_ravA, co_ravA]
    have e1 : d + j + 1 - d = j + 1 := by omega
    have e2 : d + j - d = j := by omega
    rw [e1, e2]
    have := hpos j
    have := hpos (j + 1)
    split_ifs with h1 h2 h2
    · rw [mul_comm]
    · omega
    · rw [zero_mul]; positivity
    · rw [zero_mul, zero_mul]
  · rw [co_ravA]
    split_ifs
    · exact (hpos _).le
    · exact le_refl 0

/-- Telescoping on an interval. -/
lemma sum_Icc_telescope (f : ℕ → ℝ) (s : ℕ) : ∀ n, s ≤ n + 1 →
    ∑ k ∈ Finset.Icc s n, (f k - f (k + 1)) = f s - f (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro hs
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hs with h | h
    · subst h; simp
    · subst h; simp
  | succ n ih =>
    intro hs
    rcases Nat.lt_or_ge (n + 1) s with h | h
    · have hs' : s = n + 2 := by omega
      subst hs'
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      ring
    · rw [Finset.sum_Icc_succ_top (by omega), ih (by omega)]
      ring

/-- The hard half of Fact 1: a point of the chain set is a convex combination of the vertices,
with barycentric weights `μ(k) − μ(k+1)`. -/
theorem chainSet_subset_hull (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {d n : ℕ} (hn : 1 ≤ n)
    (hN : d + n ≤ N) : chainSet a N d n ⊆ angle a N d n := by
  intro x hx
  obtain ⟨hx1, hx2, hx3, hx4, hx5⟩ := hx
  set μ : ℕ → ℝ := fun k => if k ≤ n then co x (d + k) / a k else 0 with hμ
  set w : ℕ → ℝ := fun k => μ k - μ (k + 1) with hw
  have hμn1 : μ (n + 1) = 0 := by simp [hμ]
  have hw0 : ∀ k ∈ Finset.Icc 1 n, 0 ≤ w k := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    simp only [hw, hμ]
    rcases eq_or_lt_of_le hk.2 with hkn | hkn
    · subst hkn
      rw [if_pos le_rfl, if_neg (by omega), sub_zero]
      exact div_nonneg hx5 (hpos _).le
    · rw [if_pos hk.2, if_pos (by omega), sub_nonneg, div_le_div_iff₀ (hpos _) (hpos _),
        show d + (k + 1) = d + k + 1 by omega]
      exact hx4 k hk.1 hkn
  have hsum : ∑ k ∈ Finset.Icc 1 n, w k = 1 := by
    rw [hw, sum_Icc_telescope μ 1 n (by omega), hμn1, sub_zero]
    simp only [hμ, if_pos hn]
    rw [hx3, div_self (hpos 1).ne']
  have hz : ∀ k ∈ Finset.Icc 1 n, ravA a N d k ∈ vsetA a N d n := by
    intro k hk
    exact Set.mem_image_of_mem _ (Set.mem_Icc.mpr (Finset.mem_Icc.mp hk))
  have hrepr : ∑ k ∈ Finset.Icc 1 n, w k • ravA a N d k = x := by
    apply ext_co
    intro c hc1 hcN
    rw [co_sum]
    simp only [co_smul, co_ravA]
    by_cases hlo : c ≤ d
    · rw [hx1 c hlo]
      apply Finset.sum_eq_zero
      intro k _
      rw [if_neg (by omega), mul_zero]
    by_cases hhi : d + n < c
    · rw [hx2 c hhi]
      apply Finset.sum_eq_zero
      intro k hk
      rw [Finset.mem_Icc] at hk
      rw [if_neg (by omega), mul_zero]
    have hval : ∀ k ∈ Finset.Icc 1 n,
        w k * (if 1 ≤ c ∧ c ≤ N ∧ d < c ∧ c ≤ d + k then a (c - d) else 0) =
          if c - d ≤ k then w k * a (c - d) else 0 := by
      intro k _
      by_cases h : c - d ≤ k
      · rw [if_pos (by omega), if_pos h]
      · rw [if_neg (by omega), if_neg h, mul_zero]
    rw [Finset.sum_congr rfl hval, ← Finset.sum_filter]
    have hfilter : (Finset.Icc 1 n).filter (fun k => c - d ≤ k) = Finset.Icc (c - d) n := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_Icc]
      omega
    rw [hfilter, ← Finset.sum_mul, hw, sum_Icc_telescope μ (c - d) n (by omega), hμn1,
      sub_zero]
    simp only [hμ, if_pos (show c - d ≤ n by omega)]
    rw [div_mul_cancel₀ _ (hpos _).ne', show d + (c - d) = c by omega]
  have hcm := Finset.centerMass_mem_convexHull (Finset.Icc 1 n) hw0
    (by rw [hsum]; exact zero_lt_one) hz
  rwa [Finset.centerMass_eq_of_sum_1 _ _ hsum, hrepr] at hcm

/-- **Fact 1** (`cor-facets` for a general positive leg vector, shifted by `d`): the convex hull of
the vertices `shift^d v(1), …, shift^d v(n)` is exactly the μ-chain set. -/
theorem chain_hull_eq (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {d n : ℕ} (hn : 1 ≤ n)
    (hN : d + n ≤ N) : angle a N d n = chainSet a N d n :=
  Set.Subset.antisymm
    (convexHull_min (vsetA_subset_chainSet a hpos hn hN) (convex_chainSet a N d n))
    (chainSet_subset_hull a hpos hn hN)

end Facets
end ExteriorConvex
