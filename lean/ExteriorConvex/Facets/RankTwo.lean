/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

Changelog (newest first):
- 2026-10-20  Created (article-3 overnight push): Theorem A(1) of
              `working-notes/kozlov-hdescription-proof-2026-10-20.org`, the rank-two H-description
              of `RA(a; 0, d) = ∠(a) + shift^d ∠(a)`, split as the 2026-10-20 review recommends:
              `completeness` (Lemma A2, positivity only) and `validity` (Lemma A1, log-concavity).

# Theorem A(1): the rank-two H-description, for a general log-concave leg vector

Standing: `1 ≤ d < n`, `N = n + d`, `a : ℕ → ℝ` positive.  `R = angle a N 0 n + angle a N d n`.
Write `A(c) = a(c − d)` for `c > d` and `A(c) = 0` for `c ≤ d` (`Aof`).  The system `Qsys a n d j₀`
is, in manuscript coordinates (`co`, see `Chain.lean`), with all chains multiplied out:

* (E)  `x(1) = a(1)`;
* (Ch1; j), `1 ≤ j < n`: `(x(j+1) − A(j+1))·a(j) ≤ (x(j) − A(j))·a(j+1)`,
  i.e. `θ(j+1) ≤ θ(j)` for `θ(c) = (x(c) − A(c))/a(c)`; this is the manuscript's
  `x_j/a_j − x_{j+1}/a_{j+1} ≥ −c_j` with `c_j = A(j+1)/a(j+1) − A(j)/a(j)`;
* (Ch2; j), `j₀ ≤ j < n`: `x(d+j+1)·a(j) ≤ x(d+j)·a(j+1)`;
* (C) `a(1) ≤ x(d+1)`, (D) `x(n+1) ≤ a(n−d+1)`, (F) `0 ≤ x(n+d)`.

`Qsys a n d 1` is the article's full system; `Qsys a n d 2` is the Θ-form `Q_Θ` (the row (Ch2; 1)
deleted).  Results:

* `completeness`: `Qsys a n d 2 ⊆ R` for **every positive** `a` (Lemma A2: the explicit
  truncation `z = min(x, shift^d a)` on the shared block, `y = x − z`, then Fact 1 twice);
* `validity`: `R ⊆ Qsys a n d 1` under log-concavity, stated without division as
  `a(j+1)·a(i) ≤ a(i+1)·a(j)` for `1 ≤ i ≤ j`, `j + 1 ≤ n` (Lemma A1, reduced by
  `convexHull_add` to the `n²` vertex sums);
* `theoremA` / `theoremA_theta`: `R = Qsys a n d 1 = Qsys a n d 2` under log-concavity.
-/
import Mathlib
import ExteriorConvex.Facets.Chain

namespace ExteriorConvex
namespace Facets

open Finset Pointwise

/-- `A(c) = a(c − d)` for `c > d`, else `0` (the manuscript's "`C(n,0)` replaced by `0`"). -/
noncomputable def Aof (a : ℕ → ℝ) (d c : ℕ) : ℝ := if d < c then a (c - d) else 0

/-- The rank-two H-system; `j₀ = 1` is the article's system, `j₀ = 2` the Θ-form. -/
def Qsys (a : ℕ → ℝ) (n d j₀ : ℕ) : Set (Fin (n + d) → ℝ) :=
  {x | co x 1 = a 1 ∧
    (∀ j, 1 ≤ j → j < n →
      (co x (j + 1) - Aof a d (j + 1)) * a j ≤ (co x j - Aof a d j) * a (j + 1)) ∧
    (∀ j, j₀ ≤ j → j < n → co x (d + j + 1) * a j ≤ co x (d + j) * a (j + 1)) ∧
    a 1 ≤ co x (d + 1) ∧ co x (n + 1) ≤ a (n - d + 1) ∧ 0 ≤ co x (n + d)}

/-- Log-concavity of the leg vector on `[1, n]`, without division. -/
def LogConcaveOn (a : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ i j, 1 ≤ i → i ≤ j → j + 1 ≤ n → a (j + 1) * a i ≤ a (i + 1) * a j

lemma Qsys_mono {a : ℕ → ℝ} {n d j₀ j₁ : ℕ} (h : j₀ ≤ j₁) : Qsys a n d j₀ ⊆ Qsys a n d j₁ := by
  rintro x ⟨h1, h2, h3, h4, h5, h6⟩
  exact ⟨h1, h2, fun j hj hjn => h3 j (le_trans h hj) hjn, h4, h5, h6⟩

lemma Aof_nonneg {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) (d c : ℕ) : 0 ≤ Aof a d c := by
  unfold Aof; split_ifs
  · exact (hpos _).le
  · exact le_refl 0

theorem convex_Qsys (a : ℕ → ℝ) (n d j₀ : ℕ) : Convex ℝ (Qsys a n d j₀) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hx1, hx2, hx3, hx4, hx5, hx6⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6⟩ := hy
  have ht' : t = 1 - s := by linarith
  subst ht'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [co_add, co_smul, hx1, hy1]; ring
  · intro j hj hjn
    have h1 := mul_le_mul_of_nonneg_left (hx2 j hj hjn) hs
    have h2 := mul_le_mul_of_nonneg_left (hy2 j hj hjn) ht
    simp only [co_add, co_smul]
    nlinarith
  · intro j hj hjn
    have h1 := mul_le_mul_of_nonneg_left (hx3 j hj hjn) hs
    have h2 := mul_le_mul_of_nonneg_left (hy3 j hj hjn) ht
    simp only [co_add, co_smul]
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hx4 hs
    have h2 := mul_le_mul_of_nonneg_left hy4 ht
    simp only [co_add, co_smul]
    nlinarith
  · have h1 := mul_le_mul_of_nonneg_left hx5 hs
    have h2 := mul_le_mul_of_nonneg_left hy5 ht
    simp only [co_add, co_smul]
    nlinarith
  · simp only [co_add, co_smul]
    exact add_nonneg (mul_nonneg hs hx6) (mul_nonneg ht hy6)

/-! ## Completeness (Lemma A2): positivity only -/

/-- A point given by a function of the manuscript coordinate. -/
def mk (N : ℕ) (f : ℕ → ℝ) : Fin N → ℝ := fun i => f (i.val + 1)

lemma co_mk {N : ℕ} (f : ℕ → ℝ) {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ N) : co (mk N f) c = f c := by
  rw [co_of _ h1 h2]
  simp only [mk]
  congr 1; omega

/-- **Lemma A2** (completeness of the Θ-form): for every positive leg vector,
`Q_Θ ⊆ ∠(a) + shift^d ∠(a)`.  No log-concavity. -/
theorem completeness (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    Qsys a n d 2 ⊆ angle a (n + d) 0 n + angle a (n + d) d n := by
  rintro x ⟨hE, hC1, hC2, hC, hD, hF⟩
  -- θ and its monotonicity
  set θ : ℕ → ℝ := fun c => (co x c - Aof a d c) / a c with hθ
  have hstep : ∀ j, 1 ≤ j → j < n → θ (j + 1) ≤ θ j := by
    intro j hj hjn
    simp only [hθ]
    rw [div_le_div_iff₀ (hpos _) (hpos _)]
    exact hC1 j hj hjn
  have hanti : ∀ i j, 1 ≤ i → i ≤ j → j ≤ n → θ j ≤ θ i := by
    intro i j hi hij hjn
    induction j, hij using Nat.le_induction with
    | base => exact le_rfl
    | succ j hij ih => exact le_trans (hstep j (by omega) (by omega)) (ih (by omega))
  have hθd1 : 0 ≤ θ (d + 1) := by
    simp only [hθ, Aof, if_pos (show d < d + 1 by omega), show d + 1 - d = 1 by omega]
    exact div_nonneg (by linarith) (hpos _).le
  -- the decomposition
  set yv : ℕ → ℝ := fun c =>
    if c ≤ d then co x c else if c ≤ n then max 0 (co x c - a (c - d)) else 0 with hyv
  set zv : ℕ → ℝ := fun c =>
    if c ≤ d then 0 else if c ≤ n then min (co x c) (a (c - d)) else co x c with hzv
  have hsplit : x = mk (n + d) yv + mk (n + d) zv := by
    apply ext_co
    intro c hc1 hcN
    rw [co_add, co_mk _ hc1 hcN, co_mk _ hc1 hcN]
    simp only [hyv, hzv]
    split_ifs with h1 h2
    · ring
    · rcases le_total (co x c) (a (c - d)) with h | h
      · rw [min_eq_left h, max_eq_left (by linarith)]; ring
      · rw [min_eq_right h, max_eq_right (by linarith)]; ring
    · ring
  -- y(c) = a(c)·max 0 θ(c) on [1, n]
  have hy_eq : ∀ c, 1 ≤ c → c ≤ n → yv c = a c * max 0 (θ c) := by
    intro c hc1 hcn
    simp only [hyv, hθ, Aof]
    by_cases hcd : c ≤ d
    · rw [if_pos hcd, if_neg (by omega), sub_zero]
      have h0 : 0 ≤ θ c := le_trans hθd1 (hanti c (d + 1) hc1 (by omega) (by omega))
      simp only [hθ, Aof, if_neg (show ¬ d < c by omega), sub_zero] at h0
      rw [max_eq_right h0, mul_div_cancel₀ _ (hpos _).ne']
    · rw [if_neg hcd, if_pos hcn, if_pos (by omega), mul_max_of_nonneg _ _ (hpos c).le, mul_zero,
        mul_div_cancel₀ _ (hpos _).ne']
  have hy : mk (n + d) yv ∈ angle a (n + d) 0 n := by
    rw [chain_hull_eq a hpos (by omega) (by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc; exact co_eq_zero _ (by omega)
    · intro c hc
      by_cases hcN : c ≤ n + d
      · rw [co_mk _ (by omega) hcN]
        simp only [hyv, if_neg (show ¬ c ≤ d by omega), if_neg (show ¬ c ≤ n by omega)]
      · exact co_eq_zero _ (by omega)
    · rw [co_mk _ (by omega) (by omega)]
      simp only [hyv, zero_add, if_pos hd]
      exact hE
    · intro j hj hjn
      simp only [zero_add]
      rw [co_mk _ (by omega) (by omega), co_mk _ (by omega) (by omega),
        hy_eq _ (by omega) (by omega), hy_eq _ (by omega) (by omega)]
      have hm : max 0 (θ (j + 1)) ≤ max 0 (θ j) := max_le_max le_rfl (hstep j hj hjn)
      have := mul_le_mul_of_nonneg_left hm (mul_nonneg (hpos (j + 1)).le (hpos j).le)
      linarith
    · simp only [zero_add]
      rw [co_mk _ (by omega) (by omega), hy_eq _ (by omega) le_rfl]
      exact mul_nonneg (hpos n).le (le_max_left _ _)
  have hz : mk (n + d) zv ∈ angle a (n + d) d n := by
    rw [chain_hull_eq a hpos (by omega) (by omega)]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · exact co_eq_zero _ (Or.inl h0)
      · rw [co_mk _ h0 (by omega)]
        simp only [hzv, if_pos hc]
    · intro c hc; exact co_eq_zero _ (by omega)
    · rw [co_mk _ (by omega) (by omega)]
      simp only [hzv, if_neg (show ¬ d + 1 ≤ d by omega), if_pos (show d + 1 ≤ n by omega),
        show d + 1 - d = 1 by omega]
      exact min_eq_right hC
    · intro j hj hjn
      rw [co_mk _ (by omega) (by omega), co_mk _ (by omega) (by omega)]
      simp only [hzv, if_neg (show ¬ d + j + 1 ≤ d by omega), if_neg (show ¬ d + j ≤ d by omega)]
      have haj := hpos j
      have haj1 := hpos (j + 1)
      by_cases h1 : d + j + 1 ≤ n
      · rw [if_pos h1, if_pos (by omega), show d + j + 1 - d = j + 1 by omega,
          show d + j - d = j by omega, min_mul_of_nonneg _ _ haj.le,
          min_mul_of_nonneg _ _ haj1.le]
        rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · have hj1 : j = 1 := by omega
          subst hj1
          have hz1 : min (co x (d + 1)) (a 1) = a 1 := min_eq_right hC
          rw [← min_mul_of_nonneg _ _ haj1.le, hz1]
          apply min_le_of_right_le
          rw [mul_comm]
        · apply le_min
          · exact min_le_of_left_le (hC2 j hj2 hjn)
          · exact min_le_of_right_le (le_of_eq (mul_comm _ _))
      · by_cases h2 : d + j ≤ n
        · have hjm : d + j = n := by omega
          rw [if_neg h1, if_pos h2, show d + j - d = j by omega, min_mul_of_nonneg _ _ haj1.le]
          have hD' : co x (d + j + 1) ≤ a (j + 1) := by
            rw [show d + j + 1 = n + 1 by omega, show j + 1 = n - d + 1 by omega]; exact hD
          apply le_min
          · rcases Nat.lt_or_ge j 2 with hj2 | hj2
            · have hj1 : j = 1 := by omega
              subst hj1
              have := mul_le_mul_of_nonneg_left hD' haj.le
              have := mul_le_mul_of_nonneg_left hC haj1.le
              nlinarith
            · exact hC2 j hj2 hjn
          · have := mul_le_mul_of_nonneg_right hD' haj.le
            linarith [mul_comm (a j) (a (j + 1))]
        · rw [if_neg h1, if_neg h2]
          exact hC2 j (by omega) hjn
    · rw [co_mk _ (by omega) (by omega)]
      simp only [hzv, if_neg (show ¬ d + n ≤ d by omega), if_neg (show ¬ d + n ≤ n by omega)]
      rw [show d + n = n + d by omega]
      exact hF
  rw [hsplit]
  exact Set.add_mem_add hy hz

/-! ## Validity (Lemma A1): log-concavity -/

lemma co_ravA_in (a : ℕ → ℝ) {N : ℕ} (e k : ℕ) {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ N) :
    co (ravA a N e k) c = if e < c ∧ c ≤ e + k then a (c - e) else 0 := by
  rw [co_ravA]
  by_cases h : e < c ∧ c ≤ e + k
  · rw [if_pos ⟨h1, h2, h⟩, if_pos h]
  · rw [if_neg (by tauto), if_neg h]

/-- **Lemma A1** (validity): under log-concavity, `∠(a) + shift^d ∠(a) ⊆ Q`, with the full second
chain (including the row (Ch2; 1)). -/
theorem validity (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n) {d : ℕ}
    (hd : 1 ≤ d) (hdn : d < n) :
    angle a (n + d) 0 n + angle a (n + d) d n ⊆ Qsys a n d 1 := by
  rw [← convexHull_add]
  apply convexHull_min _ (convex_Qsys a n d 1)
  rintro _ ⟨_, ⟨k, hk, rfl⟩, _, ⟨l, hl, rfl⟩, rfl⟩
  rw [Set.mem_Icc] at hk hl
  -- the shifted vertex, read against the roof `A`
  have hU : ∀ c, 1 ≤ c → c ≤ n + d → co (ravA a (n + d) d l) c = if c ≤ d + l then Aof a d c else 0 := by
    intro c hc1 hcN
    rw [co_ravA_in a d l hc1 hcN]
    unfold Aof
    by_cases h1 : c ≤ d + l
    · rw [if_pos h1]
      by_cases h2 : d < c
      · rw [if_pos ⟨h2, h1⟩, if_pos h2]
      · rw [if_neg (by tauto), if_neg h2]
    · rw [if_neg (by tauto), if_neg h1]
  have hV : ∀ c, 1 ≤ c → c ≤ n + d → co (ravA a (n + d) 0 k) c = if c ≤ k then a c else 0 := by
    intro c hc1 hcN
    rw [co_ravA_in a 0 k hc1 hcN]
    by_cases h : c ≤ k
    · rw [if_pos ⟨by omega, by omega⟩, if_pos h, Nat.sub_zero]
    · rw [if_neg (by omega), if_neg h]
  have hvert := fun e (he : e + n ≤ n + d) (m : ℕ) (hm : 1 ≤ m ∧ m ≤ n) =>
    vsetA_subset_chainSet a hpos (d := e) (n := n) (N := n + d) (by omega) he ⟨m, hm, rfl⟩
  have hAlc : ∀ j, 1 ≤ j → j + 1 ≤ n → Aof a d j * a (j + 1) ≤ Aof a d (j + 1) * a j := by
    intro j hj hjn
    unfold Aof
    by_cases h : d < j
    · rw [if_pos h, if_pos (by omega), show j + 1 - d = j - d + 1 by omega]
      have := hlc (j - d) j (by omega) (by omega) hjn
      linarith
    · rw [if_neg h, zero_mul]
      split_ifs
      · exact mul_nonneg (hpos _).le (hpos _).le
      · simp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [co_add, hV 1 le_rfl (by omega), hU 1 le_rfl (by omega), if_pos hk.1]
    simp only [Aof, if_neg (show ¬ d < 1 by omega)]
    split_ifs <;> ring
  · intro j hj hjn
    rw [co_add, co_add]
    have hVc := (hvert 0 (by omega) k hk).2.2.2.1 j hj hjn
    simp only [zero_add] at hVc
    have hUj : (co (ravA a (n + d) d l) (j + 1) - Aof a d (j + 1)) * a j ≤
        (co (ravA a (n + d) d l) j - Aof a d j) * a (j + 1) := by
      rw [hU _ (by omega) (by omega), hU _ (by omega) (by omega)]
      have hA0 := Aof_nonneg hpos d j
      have hA1 := Aof_nonneg hpos d (j + 1)
      have := hpos j
      have := hpos (j + 1)
      split_ifs with h1 h2 h2
      · simp
      · omega
      · rw [sub_self, zero_mul, zero_sub, neg_mul]
        exact neg_nonpos.mpr (mul_nonneg hA1 (hpos j).le)
      · have := hAlc j hj (by omega)
        linarith
    linarith
  · intro j hj hjn
    rw [co_add, co_add]
    have hUc := (hvert d (by omega) l hl).2.2.2.1 j hj hjn
    have hVj : co (ravA a (n + d) 0 k) (d + j + 1) * a j ≤ co (ravA a (n + d) 0 k) (d + j) * a (j + 1) := by
      rw [hV _ (by omega) (by omega), hV _ (by omega) (by omega)]
      have := hpos j
      have := hpos (j + 1)
      have := hpos (d + j)
      split_ifs with h1 h2 h2
      · have := hlc j (d + j) hj (by omega) (by omega)
        linarith
      · omega
      · rw [zero_mul]; positivity
      · simp
    linarith
  · rw [co_add, hV _ (by omega) (by omega), hU _ (by omega) (by omega),
      if_pos (show d + 1 ≤ d + l by omega)]
    simp only [Aof, if_pos (show d < d + 1 by omega), show d + 1 - d = 1 by omega]
    have := hpos (d + 1)
    split_ifs <;> linarith
  · rw [co_add, hV _ (by omega) (by omega), hU _ (by omega) (by omega),
      if_neg (show ¬ n + 1 ≤ k by omega), zero_add]
    simp only [Aof, if_pos (show d < n + 1 by omega), show n + 1 - d = n - d + 1 by omega]
    have := hpos (n - d + 1)
    split_ifs <;> linarith
  · rw [co_add, hV _ (by omega) (by omega), hU _ (by omega) (by omega)]
    have := Aof_nonneg hpos d (n + d)
    have := hpos (n + d)
    split_ifs <;> linarith

/-- **Theorem A(1)**, article form: under log-concavity, `RA(a; 0, d) = Q` (both chains full). -/
theorem theoremA (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n) {d : ℕ}
    (hd : 1 ≤ d) (hdn : d < n) :
    angle a (n + d) 0 n + angle a (n + d) d n = Qsys a n d 1 :=
  Set.Subset.antisymm (validity a hpos hlc hd hdn)
    (le_trans (Qsys_mono (by norm_num)) (completeness a hpos hd hdn))

/-- **Theorem A(1)**, Θ-form: under log-concavity the row (Ch2; 1) may be dropped,
`RA(a; 0, d) = Q_Θ`.  (In particular (Ch2; 1) is implied by the other rows.) -/
theorem theoremA_theta (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n) {d : ℕ}
    (hd : 1 ≤ d) (hdn : d < n) :
    angle a (n + d) 0 n + angle a (n + d) d n = Qsys a n d 2 :=
  Set.Subset.antisymm (le_trans (validity a hpos hlc hd hdn) (Qsys_mono (by norm_num)))
    (completeness a hpos hd hdn)

end Facets
end ExteriorConvex
