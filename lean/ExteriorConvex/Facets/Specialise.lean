/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

Changelog (newest first):
- 2026-10-20  Created (article-3 overnight push): the article-1 division form of Theorem A(1)
              (`theoremA_lit`), and its two specialisations, `conj_kozlov_hrep2` (Kozlov vector)
              and `conj_ones_hrep` (all-ones vector), in article 1's printed shape.

# Theorem A(1) in article 1's printed form, and the two conjectures it settles

Everything is in the dropped space `Fin N → ℝ`, `N = n + d`, read through manuscript coordinates
`co x c` (`Chain.lean`), exactly as article 1 writes `x_1, …, x_N`.

* `Qlit a n d`: the system of Theorem A with the chains in division form,
  `x_j/a_j − x_{j+1}/a_{j+1} ≥ −c_j`, `c_j = A(j+1)/a(j+1) − A(j)/a(j)`, and
  `x_{d+j}/a_j ≥ x_{d+j+1}/a_{j+1}`; `Qlit_eq` identifies it with `Qsys a n d 1`.
* `conj_kozlov_hrep2`: `conj-kozlov-hrep2`'s system (`x_1 = n`, the three-case `c_j` of
  `eq:kozlov-hrep2`, the second chain for `1 ≤ j ≤ n−1`, `x_{d+1} ≥ C(n,1) = n`,
  `x_{n+1} ≤ C(n, m+1)`, `x_N ≥ 0`) equals `RA(κ⃗(n); 0, d)`.  The facet-count clause
  ("exactly one redundant, `2n` facets") is **not** formalised; only the set equality, plus the fact
  that the row (Ch2; 1) can be dropped (`theoremA_theta`).
* `conj_ones_hrep`: `conj-ones-hrep`'s chain system equals `RA(𝟏; 0, d)`.  The facet count stated
  after it in article 1 is likewise not formalised.
-/
import Mathlib
import ExteriorConvex.Facets.RankTwo

namespace ExteriorConvex
namespace Facets

open Finset Pointwise

/-! ## The division form -/

/-- The offsets `c_j = A(j+1)/a(j+1) − A(j)/a(j)` of `eq:kozlov-hrep2`, for a general leg vector. -/
noncomputable def cOff (a : ℕ → ℝ) (d j : ℕ) : ℝ := Aof a d (j + 1) / a (j + 1) - Aof a d j / a j

/-- Theorem A's system, with the chains in article 1's division form. -/
def Qlit (a : ℕ → ℝ) (n d : ℕ) : Set (Fin (n + d) → ℝ) :=
  {x | co x 1 = a 1 ∧
    (∀ j, 1 ≤ j → j < n → co x j / a j - co x (j + 1) / a (j + 1) ≥ -cOff a d j) ∧
    (∀ j, 1 ≤ j → j < n → co x (d + j) / a j ≥ co x (d + j + 1) / a (j + 1)) ∧
    co x (d + 1) ≥ a 1 ∧ co x (n + 1) ≤ a (n - d + 1) ∧ co x (n + d) ≥ 0}

lemma Qlit_eq (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) (n d : ℕ) : Qlit a n d = Qsys a n d 1 := by
  ext x
  have key1 : ∀ j, (co x j / a j - co x (j + 1) / a (j + 1) ≥ -cOff a d j ↔
      (co x (j + 1) - Aof a d (j + 1)) * a j ≤ (co x j - Aof a d j) * a (j + 1)) := by
    intro j
    rw [← div_le_div_iff₀ (hpos _) (hpos _), sub_div, sub_div, cOff]
    constructor <;> intro h <;> linarith
  have key2 : ∀ j, (co x (d + j) / a j ≥ co x (d + j + 1) / a (j + 1) ↔
      co x (d + j + 1) * a j ≤ co x (d + j) * a (j + 1)) := by
    intro j
    rw [ge_iff_le, div_le_div_iff₀ (hpos _) (hpos _)]
  simp only [Qlit, Qsys, Set.mem_setOf_eq, key1, key2, ge_iff_le]

/-- **Theorem A(1)**, literally in article 1's form, for a positive log-concave leg vector. -/
theorem theoremA_lit (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n) {d : ℕ}
    (hd : 1 ≤ d) (hdn : d < n) :
    angle a (n + d) 0 n + angle a (n + d) d n = Qlit a n d := by
  rw [Qlit_eq a hpos, theoremA a hpos hlc hd hdn]

/-! ## The Kozlov vector: `conj-kozlov-hrep2` -/

/-- Log-concavity of the binomial row, without division. -/
lemma choose_logConcave {n i j : ℕ} (hij : i ≤ j) (hjn : j + 1 ≤ n) :
    n.choose (j + 1) * n.choose i ≤ n.choose (i + 1) * n.choose j := by
  have h1 := Nat.choose_succ_right_eq n i
  have h2 := Nat.choose_succ_right_eq n j
  obtain ⟨p, rfl⟩ : ∃ p, j = i + p := ⟨j - i, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, n = i + p + q + 1 := ⟨n - (i + p) - 1, by omega⟩
  rw [show i + p + q + 1 - i = p + q + 1 by omega] at h1
  rw [show i + p + q + 1 - (i + p) = q + 1 by omega] at h2
  set X := (i + p + q + 1).choose i
  set Y := (i + p + q + 1).choose (i + p)
  set U := (i + p + q + 1).choose (i + 1)
  set V := (i + p + q + 1).choose (i + p + 1)
  have hpos : 0 < (i + 1) * (i + p + 1) := by positivity
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc V * X * ((i + 1) * (i + p + 1)) = (V * (i + p + 1)) * X * (i + 1) := by ring
    _ = Y * (q + 1) * X * (i + 1) := by rw [h2]
    _ ≤ Y * (p + q + 1) * X * (i + p + 1) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left Y (by omega)) le_rfl)
          (by omega)
    _ = (U * (i + 1)) * Y * (i + p + 1) := by rw [h1]; ring
    _ = U * Y * ((i + 1) * (i + p + 1)) := by ring

lemma kozLeg_of_le {n s : ℕ} (h : s ≤ n) : kozLeg n s = (n.choose s : ℝ) := by
  simp only [kozLeg, if_pos h]

lemma kozLeg_logConcave (n : ℕ) : LogConcaveOn (kozLeg n) n := by
  intro i j hi hij hjn
  rw [kozLeg_of_le hjn, kozLeg_of_le (by omega), kozLeg_of_le (by omega),
    kozLeg_of_le (by omega)]
  exact_mod_cast choose_logConcave hij hjn

/-- The offsets `c_j` of `eq:kozlov-hrep2`, in article 1's three cases (`t = j − d`). -/
noncomputable def cKoz (n d j : ℕ) : ℝ :=
  if j < d then 0
  else if j = d then (n.choose 1 : ℝ) / (n.choose (d + 1) : ℝ)
  else (n.choose (j - d + 1) : ℝ) / (n.choose (j + 1) : ℝ) -
    (n.choose (j - d) : ℝ) / (n.choose j : ℝ)

/-- The system of `conj-kozlov-hrep2`, as printed in article 1. -/
def kozHrep2 (n d : ℕ) : Set (Fin (n + d) → ℝ) :=
  {x | co x 1 = (n : ℝ) ∧
    (∀ j, 1 ≤ j → j < n →
      co x j / (n.choose j : ℝ) - co x (j + 1) / (n.choose (j + 1) : ℝ) ≥ -cKoz n d j) ∧
    (∀ j, 1 ≤ j → j < n →
      co x (d + j) / (n.choose j : ℝ) ≥ co x (d + j + 1) / (n.choose (j + 1) : ℝ)) ∧
    co x (d + 1) ≥ (n.choose 1 : ℝ) ∧ co x (n + 1) ≤ (n.choose (n - d + 1) : ℝ) ∧
    co x (n + d) ≥ 0}

lemma cOff_kozLeg {n d j : ℕ} (hd : 1 ≤ d) (hjn : j < n) : cOff (kozLeg n) d j = cKoz n d j := by
  unfold cOff cKoz Aof
  rw [kozLeg_of_le (by omega : j + 1 ≤ n)]
  by_cases h1 : j < d
  · rw [if_neg (by omega), if_neg (by omega), if_pos h1]; ring
  by_cases h2 : j = d
  · subst h2
    rw [if_pos (by omega), if_neg (by omega), if_neg h1, if_pos rfl,
      show j + 1 - j = 1 by omega, kozLeg_of_le (by omega)]
    ring
  · rw [if_pos (by omega), if_pos (by omega), if_neg h1, if_neg h2,
      show j + 1 - d = j - d + 1 by omega, kozLeg_of_le (by omega), kozLeg_of_le (by omega),
      kozLeg_of_le (by omega)]

lemma kozHrep2_eq_Qlit {n d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    kozHrep2 n d = Qlit (kozLeg n) n d := by
  ext x
  simp only [kozHrep2, Qlit, Set.mem_setOf_eq]
  have e1 : kozLeg n 1 = (n : ℝ) := by rw [kozLeg_of_le (by omega), Nat.choose_one_right]
  have e1' : kozLeg n 1 = (n.choose 1 : ℝ) := kozLeg_of_le (by omega)
  have e2 : kozLeg n (n - d + 1) = (n.choose (n - d + 1) : ℝ) := kozLeg_of_le (by omega)
  have hch1 : ∀ j, 1 ≤ j → j < n →
      (co x j / (n.choose j : ℝ) - co x (j + 1) / (n.choose (j + 1) : ℝ) ≥ -cKoz n d j ↔
        co x j / kozLeg n j - co x (j + 1) / kozLeg n (j + 1) ≥ -cOff (kozLeg n) d j) := by
    intro j _ hjn
    rw [cOff_kozLeg hd hjn, kozLeg_of_le (by omega), kozLeg_of_le (by omega)]
  have hch2 : ∀ j, 1 ≤ j → j < n →
      (co x (d + j) / (n.choose j : ℝ) ≥ co x (d + j + 1) / (n.choose (j + 1) : ℝ) ↔
        co x (d + j) / kozLeg n j ≥ co x (d + j + 1) / kozLeg n (j + 1)) := by
    intro j _ hjn
    rw [kozLeg_of_le (by omega), kozLeg_of_le (by omega)]
  rw [e2]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨by rw [e1]; exact h1, fun j hj hjn => (hch1 j hj hjn).mp (h2 j hj hjn),
      fun j hj hjn => (hch2 j hj hjn).mp (h3 j hj hjn), by rw [e1']; exact h4, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨by rw [← e1]; exact h1, fun j hj hjn => (hch1 j hj hjn).mpr (h2 j hj hjn),
      fun j hj hjn => (hch2 j hj hjn).mpr (h3 j hj hjn), by rw [← e1']; exact h4, h5, h6⟩

/-- **`conj-kozlov-hrep2`** (article 1), as a set equality: for `1 ≤ d ≤ n − 1`,
`RA(κ⃗(n); 0, d) = ∠(κ⃗(n)) + shift^d ∠(κ⃗(n))` is cut out in `ℝ^N` by article 1's `2n + 1`
inequalities and one equation. -/
theorem conj_kozlov_hrep2 {n d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    angle (kozLeg n) (n + d) 0 n + angle (kozLeg n) (n + d) d n = kozHrep2 n d := by
  rw [kozHrep2_eq_Qlit hd hdn, theoremA_lit _ (kozLeg_pos n) (kozLeg_logConcave n) hd hdn]

/-- The redundancy half of `conj-kozlov-hrep2`'s last sentence, as a set equality: the second
chain at `j = 1` may be dropped.  (That it is the *only* redundant row is not formalised.) -/
theorem kozlov_hrep2_theta {n d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    angle (kozLeg n) (n + d) 0 n + angle (kozLeg n) (n + d) d n = Qsys (kozLeg n) n d 2 :=
  theoremA_theta _ (kozLeg_pos n) (kozLeg_logConcave n) hd hdn

/-! ## The all-ones vector: `conj-ones-hrep` -/

/-- The system of `conj-ones-hrep`, as printed in article 1. -/
def onesHrep (n d : ℕ) : Set (Fin (n + d) → ℝ) :=
  {x | co x 1 = 1 ∧
    (∀ j, 1 ≤ j → j < d → co x (j + 1) ≤ co x j) ∧               -- first block
    co x (d + 1) ≤ co x d + 1 ∧ 1 ≤ co x (d + 1) ∧                  -- entry to the overlap
    (∀ j, d + 1 ≤ j → j < n → co x (j + 1) ≤ co x j) ∧           -- overlap block
    co x (n + 1) ≤ co x n ∧ co x (n + 1) ≤ 1 ∧                      -- transition
    (∀ j, n + 1 ≤ j → j < n + d → co x (j + 1) ≤ co x j) ∧       -- second block
    0 ≤ co x (n + d)}

lemma onesHrep_eq_Qsys {n d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    onesHrep n d = Qsys (fun _ => (1 : ℝ)) n d 2 := by
  ext x
  simp only [onesHrep, Qsys, Set.mem_setOf_eq, mul_one]
  have hA : ∀ c, Aof (fun _ => (1 : ℝ)) d c = if d < c then 1 else 0 := fun c => rfl
  simp only [hA]
  constructor
  · rintro ⟨hE, hB1, hbump, hC, hO, hT, hD, hB2, hF⟩
    refine ⟨hE, ?_, ?_, hC, hD, hF⟩
    · intro j hj hjn
      by_cases h1 : j < d
      · rw [if_neg (by omega), if_neg (by omega)]; linarith [hB1 j hj h1]
      by_cases h2 : j = d
      · subst h2; rw [if_pos (by omega), if_neg (by omega)]; linarith
      · rw [if_pos (by omega), if_pos (by omega)]; linarith [hO j (by omega) hjn]
    · intro j hj hjn
      rcases Nat.lt_or_ge (d + j) n with h | h
      · exact hO _ (by omega) h
      rcases eq_or_lt_of_le h with h' | h'
      · rw [show d + j + 1 = n + 1 by omega, show d + j = n by omega]; exact hT
      · exact hB2 _ (by omega) (by omega)
  · rintro ⟨hE, hC1, hC2, hC, hD, hF⟩
    refine ⟨hE, ?_, ?_, hC, ?_, ?_, hD, ?_, hF⟩
    · intro j hj hjd
      have := hC1 j hj (by omega)
      rw [if_neg (by omega), if_neg (by omega)] at this; linarith
    · have := hC1 d hd hdn
      rw [if_pos (by omega), if_neg (by omega)] at this; linarith
    · intro j hj hjn
      have := hC1 j (by omega) hjn
      rw [if_pos (by omega), if_pos (by omega)] at this; linarith
    · rcases Nat.lt_or_ge (n - d) 2 with h | h
      · have e : co x n = co x (d + 1) := congrArg (co x) (by omega)
        rw [e]
        linarith
      · have := hC2 (n - d) h (by omega)
        rwa [show d + (n - d) = n by omega] at this
    · intro j hj hjN
      have := hC2 (j - d) (by omega) (by omega)
      rwa [show d + (j - d) = j by omega] at this

lemma ones_logConcave (n : ℕ) : LogConcaveOn (fun _ => (1 : ℝ)) n := by
  intro i j _ _ _; simp

/-- **`conj-ones-hrep`** (article 1), as a set equality: for `1 ≤ d ≤ n − 1`,
`RA(𝟏; 0, d)` is cut out in `ℝ^N` by the single equation and the capped chain. -/
theorem conj_ones_hrep {n d : ℕ} (hd : 1 ≤ d) (hdn : d < n) :
    angle (fun _ => (1 : ℝ)) (n + d) 0 n + angle (fun _ => (1 : ℝ)) (n + d) d n =
      onesHrep n d := by
  rw [onesHrep_eq_Qsys hd hdn,
    theoremA_theta _ (fun _ => one_pos) (ones_logConcave n) hd hdn]

end Facets
end ExteriorConvex
