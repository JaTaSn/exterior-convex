/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Part IV: irredundancy of the rank-two facet system (`thm-hrep2`(3)), witness form

`article/exterior-convex_article4_draft_1.org`, Theorem `thm-hrep2`(3): if `a⃗` is strictly
log-concave, "the system without `(Ch2; 1)` is irredundant".  Here in the witness form: for every
row `ρ` of the system `Qsys a n d 2` (the `2n` rows `(Ch1; j)`, `1 ≤ j ≤ n−1`, `(Ch2; j)`,
`2 ≤ j ≤ n−1`, `(C)`, `(D)`, `(F)`), there is a point satisfying the equation `(E)` and every other
row, but not `ρ`.  So no row is implied by the others.  (The facet *count* `2n` and "pairwise
distinct facets" are dimension statements and are not formalised.)

| Part IV | here |
|---|---|
| the rows of the system | `Row2` (`ch1 j`, `ch2 j`, `C`, `D`, `F`), `Row2.Holds`, `Row2.InSys`; `mem_Qsys_two_iff` |
| strictly log-concave `a⃗` | `Pairwise.SLC a n` (cross-multiplied, local); its global form `slc_glob` |
| **`thm-hrep2`(3)**, irredundancy | **`thm_hrep2_irredundant`** |

**The witnesses.**  Each is a point `y` of `R` (a sum of two summand vertices, so `y` satisfies every
row by `validity`) with one coordinate `c` moved by `t`; only the rows reading `c` need a check
(`witness_of`).  With `T = v_n + shift^d v_n`:

| row | `y` | moved coordinate, amount |
|---|---|---|
| `(Ch1; j)`, `j ≤ d` | `T` | `x_{j+1}`, `+1` |
| `(Ch1; j)`, `j ≥ d+1` | `T` | `x_{j+1}`, `+(a_j a_{j−d+1} − a_{j+1} a_{j−d})/a_{j−d}` (strict LC) |
| `(Ch2; j)`, `d + j + 1 ≤ n` | `v_d + shift^d v_j` | `x_{d+j}`, `−a_{j+1} a_{d+j}/a_{d+j+1}` (strict LC) |
| `(Ch2; j)`, `d + j ≥ n` | `v_1 + shift^d v_n` | `x_{d+j}`, `−1` |
| `(C)` | `v_d + shift^d v_1` | `x_{d+1}`, `−a_2 a_{d+1}/a_{d+2}` |
| `(D)` | `T` | `x_{n+1}`, `+a_n a_{m+1}/a_m` |
| `(F)` | `v_1 + shift^d v_1` | `x_N`, `−1` |

Strictness is used exactly where the paper locates it: for `(Ch1; j)`, `j ≥ d + 2`, against
`(Ch2; j − d)`, and for `(Ch2; j)`, `j ≤ m − 1`, against `(Ch1; d + j)` — the pairs of rows on the
same edge that coincide when the slope has a plateau.

Changelog (newest first): 2026-11-17 created (Claude-Code agent, run `2026-11-17_lean-parts-4-5`)
-/
import Mathlib
import ExteriorConvex.Facets.Tight
import ExteriorConvex.Vertices.PairwiseReduction

namespace ExteriorConvex
namespace Facets

open Finset

/-- The rows of `thm-hrep2`'s system. -/
inductive Row2
  | ch1 (j : ℕ)
  | ch2 (j : ℕ)
  | C
  | D
  | F

namespace Row2

/-- Row `ρ` holds at `x` (the multiplied-out form of `Qsys`). -/
def Holds (a : ℕ → ℝ) (n d : ℕ) (x : Fin (n + d) → ℝ) : Row2 → Prop
  | ch1 j => (co x (j + 1) - Aof a d (j + 1)) * a j ≤ (co x j - Aof a d j) * a (j + 1)
  | ch2 j => co x (d + j + 1) * a j ≤ co x (d + j) * a (j + 1)
  | C => a 1 ≤ co x (d + 1)
  | D => co x (n + 1) ≤ a (n - d + 1)
  | F => 0 ≤ co x (n + d)

/-- The rows of the system with `(Ch2; 1)` deleted (`2n` rows). -/
def InSys (n : ℕ) : Row2 → Prop
  | ch1 j => 1 ≤ j ∧ j < n
  | ch2 j => 2 ≤ j ∧ j < n
  | C => True
  | D => True
  | F => True

/-- The coordinates read by row `ρ`. -/
def Uses (n d c : ℕ) : Row2 → Prop
  | ch1 j => c = j ∨ c = j + 1
  | ch2 j => c = d + j ∨ c = d + j + 1
  | C => c = d + 1
  | D => c = n + 1
  | F => c = n + d

end Row2

variable {a : ℕ → ℝ} {n d : ℕ}

/-- `Qsys a n d 2` is the equation `(E)` and the rows `Row2.InSys`. -/
lemma mem_Qsys_two_iff {x : Fin (n + d) → ℝ} :
    x ∈ Qsys a n d 2 ↔ co x 1 = a 1 ∧ ∀ ρ : Row2, ρ.InSys n → ρ.Holds a n d x := by
  constructor
  · rintro ⟨hE, h1, h2, hC, hD, hF⟩
    refine ⟨hE, fun ρ hρ => ?_⟩
    cases ρ with
    | ch1 j => exact h1 j hρ.1 hρ.2
    | ch2 j => exact h2 j hρ.1 hρ.2
    | C => exact hC
    | D => exact hD
    | F => exact hF
  · rintro ⟨hE, h⟩
    exact ⟨hE, fun j h1 h2 => h (.ch1 j) ⟨h1, h2⟩, fun j h1 h2 => h (.ch2 j) ⟨h1, h2⟩,
      h .C trivial, h .D trivial, h .F trivial⟩

/-- Strict log-concavity, global form: `σ_i > σ_j` for `1 ≤ i < j ≤ n − 1`. -/
lemma slc_glob (hpos : ∀ s, 0 < a s) (hslc : Pairwise.SLC a n) {i j : ℕ} (hi : 1 ≤ i)
    (hij : i < j) (hj : j + 1 ≤ n) : a (j + 1) * a i < a (i + 1) * a j := by
  have := Pairwise.lc_glob_strict (fun s _ _ => hpos s) hslc (e := 0) (d := j - i) (c := j)
    (by omega) (by omega) (by omega)
  rw [show j + 1 - 0 = j + 1 by omega, show j - (j - i) = i by omega, show j - 0 = j by omega,
    show j + 1 - (j - i) = i + 1 by omega] at this
  linarith

/-- Strict log-concavity implies `LogConcaveOn`. -/
lemma logConcaveOn_of_slc (hpos : ∀ s, 0 < a s) (hslc : Pairwise.SLC a n) : LogConcaveOn a n := by
  intro i j hi hij hj
  rcases Nat.eq_or_lt_of_le hij with rfl | h
  · rw [mul_comm]
  · exact (slc_glob hpos hslc hi h hj).le

/-! ## The witness scheme -/

/-- The coordinate vector `e_c` of `ℝ^{n+d}`. -/
def evec2 (n d c : ℕ) : Fin (n + d) → ℝ := mk (n + d) fun c' => if c' = c then 1 else 0

lemma co_add_ev (y : Fin (n + d) → ℝ) (t : ℝ) {c : ℕ} (hc1 : 1 ≤ c) (hcN : c ≤ n + d) (c' : ℕ) :
    co (y + t • evec2 n d c) c' = co y c' + if c' = c then t else 0 := by
  rw [co_add, co_smul]
  by_cases h : 1 ≤ c' ∧ c' ≤ n + d
  · rw [evec2, co_mk _ h.1 h.2]
    split_ifs <;> ring
  · rw [co_eq_zero (evec2 n d c) (by omega : c' = 0 ∨ n + d < c'), ite_eq_right (by omega)]
    ring

lemma holds_add_ev_of_not_uses (y : Fin (n + d) → ℝ) (t : ℝ) {c : ℕ} (hc1 : 1 ≤ c)
    (hcN : c ≤ n + d) {ρ : Row2} (hu : ¬ ρ.Uses n d c) :
    ρ.Holds a n d (y + t • evec2 n d c) ↔ ρ.Holds a n d y := by
  cases ρ with
  | ch1 j =>
    simp only [Row2.Uses, not_or] at hu
    simp only [Row2.Holds, co_add_ev y t hc1 hcN]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero, add_zero]
  | ch2 j =>
    simp only [Row2.Uses, not_or] at hu
    simp only [Row2.Holds, co_add_ev y t hc1 hcN]
    rw [ite_eq_right (by omega), ite_eq_right (by omega), add_zero, add_zero]
  | C =>
    simp only [Row2.Uses] at hu
    simp only [Row2.Holds, co_add_ev y t hc1 hcN]
    rw [ite_eq_right (by omega), add_zero]
  | D =>
    simp only [Row2.Uses] at hu
    simp only [Row2.Holds, co_add_ev y t hc1 hcN]
    rw [ite_eq_right (by omega), add_zero]
  | F =>
    simp only [Row2.Uses] at hu
    simp only [Row2.Holds, co_add_ev y t hc1 hcN]
    rw [ite_eq_right (by omega), add_zero]

/-- **The witness scheme**: a point `y` satisfying the system, moved by `t` in the coordinate `c`;
if the rows other than `ρ` that read `c` still hold and `ρ` fails, `ρ` is not implied. -/
lemma witness_of (y : Fin (n + d) → ℝ) (t : ℝ) {c : ℕ} (hc2 : 2 ≤ c) (hcN : c ≤ n + d)
    (hyE : co y 1 = a 1) (hy : ∀ σ : Row2, σ.InSys n → σ.Holds a n d y) (ρ : Row2)
    (huse : ∀ σ : Row2, σ.InSys n → σ.Uses n d c → (σ.Holds a n d (y + t • evec2 n d c) ∨ σ = ρ))
    (hviol : ¬ ρ.Holds a n d (y + t • evec2 n d c)) :
    ∃ x : Fin (n + d) → ℝ, co x 1 = a 1 ∧ (∀ σ : Row2, σ.InSys n → σ ≠ ρ → σ.Holds a n d x) ∧
      ¬ ρ.Holds a n d x := by
  refine ⟨y + t • evec2 n d c, ?_, fun σ hσ hne => ?_, hviol⟩
  · rw [co_add_ev y t (by omega) hcN, ite_eq_right (by omega), add_zero, hyE]
  · by_cases hu : σ.Uses n d c
    · rcases huse σ hσ hu with h | h
      · exact h
      · exact absurd h hne
    · exact (holds_add_ev_of_not_uses y t (by omega) hcN hu).mpr (hy σ hσ)

/-- A sum of two summand vertices satisfies `(E)` and every row (`validity`). -/
lemma vsum_holds (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hd : 1 ≤ d) (hdn : d < n)
    {k l : ℕ} (hk : 1 ≤ k ∧ k ≤ n) (hl : 1 ≤ l ∧ l ≤ n) :
    co (ravA a (n + d) 0 k + ravA a (n + d) d l) 1 = a 1 ∧
      ∀ σ : Row2, σ.InSys n → σ.Holds a n d (ravA a (n + d) 0 k + ravA a (n + d) d l) :=
  mem_Qsys_two_iff.mp (Qsys_mono (by norm_num)
    (validity a hpos hlc hd hdn (vsum_mem_R2 a hk hl)))

/-- The top point `T = v_n + shift^d v_n`: on `[1, n]` the reduced chain is `a`. -/
lemma co_top_sub {c : ℕ} (hc1 : 1 ≤ c) (hcn : c ≤ n) :
    co (ravA a (n + d) 0 n + ravA a (n + d) d n) c - Aof a d c = a c := by
  rw [co_vsum a hc1 (by omega), ite_eq_left hcn]
  unfold Aof
  split_ifs <;> first | ring1 | omega

lemma co_top_gt (hdn : d < n) {c : ℕ} (hc : n < c) (hcN : c ≤ n + d) :
    co (ravA a (n + d) 0 n + ravA a (n + d) d n) c = a (c - d) := by
  rw [co_vsum a (by omega) hcN, ite_eq_right (by omega), ite_eq_left (by omega), zero_add]

/-! ## The seven witnesses -/

/-- Row `ρ` is not implied by `(E)` and the other rows: the witness form of irredundancy. -/
abbrev NotImplied (a : ℕ → ℝ) (n d : ℕ) (ρ : Row2) : Prop :=
  ∃ x : Fin (n + d) → ℝ, co x 1 = a 1 ∧ (∀ σ : Row2, σ.InSys n → σ ≠ ρ → σ.Holds a n d x) ∧
    ¬ ρ.Holds a n d x

section Witnesses

variable (hpos : ∀ s, 0 < a s) (hslc : Pairwise.SLC a n) (hd : 1 ≤ d) (hdn : d < n)
include hpos hslc hd hdn

/-- `(Ch1; j)`, `j ≤ d`: `T + e_{j+1}`. -/
lemma wit_ch1_low {j : ℕ} (hj1 : 1 ≤ j) (hjd : j ≤ d) : NotImplied a n d (.ch1 j) := by
  have hlc := logConcaveOn_of_slc hpos hslc
  obtain ⟨hyE, hy⟩ := vsum_holds hpos hlc hd hdn (k := n) (l := n) ⟨by omega, le_rfl⟩
    ⟨by omega, le_rfl⟩
  have hc1 : 1 ≤ j + 1 := by omega
  have hcN : j + 1 ≤ n + d := by omega
  refine witness_of _ 1 (by omega) hcN hyE hy (.ch1 j) (fun σ hσ hu => ?_) ?_
  · have hyσ := hy σ hσ
    cases σ with
    | ch1 j' =>
      simp only [Row2.Uses, Row2.InSys, Row2.Holds] at hu hσ hyσ ⊢
      by_cases hjj : j' = j
      · exact Or.inr (by rw [hjj])
      left
      obtain rfl : j' = j + 1 := by omega
      rw [co_add_ev _ 1 hc1 hcN, co_add_ev _ 1 hc1 hcN, ite_eq_right (by omega),
        ite_eq_left rfl]
      have := hpos (j + 1 + 1)
      nlinarith
    | ch2 j' => simp only [Row2.Uses, Row2.InSys] at hu hσ; omega
    | C =>
      left
      simp only [Row2.Uses, Row2.Holds] at hu hyσ ⊢
      rw [co_add_ev _ 1 hc1 hcN, ite_eq_left (by omega)]
      linarith
    | D => simp only [Row2.Uses] at hu; omega
    | F => simp only [Row2.Uses] at hu; omega
  · simp only [Row2.Holds]
    rw [co_add_ev _ 1 hc1 hcN, co_add_ev _ 1 hc1 hcN, ite_eq_left rfl, ite_eq_right (by omega),
      add_zero]
    have e1 := co_top_sub (a := a) (n := n) (d := d) hc1 (by omega)
    have e0 := co_top_sub (a := a) (n := n) (d := d) hj1 (by omega)
    have := hpos j
    intro h
    rw [add_sub_right_comm, e1, e0] at h
    linarith

/-- `(Ch1; j)`, `j ≥ d + 1`: `T + δ e_{j+1}`, `δ a_{j−d} = a_j a_{j−d+1} − a_{j+1} a_{j−d}`. -/
lemma wit_ch1_high {j : ℕ} (hdj : d + 1 ≤ j) (hjn : j < n) : NotImplied a n d (.ch1 j) := by
  have hlc := logConcaveOn_of_slc hpos hslc
  obtain ⟨hyE, hy⟩ := vsum_holds hpos hlc hd hdn (k := n) (l := n) ⟨by omega, le_rfl⟩
    ⟨by omega, le_rfl⟩
  have hc1 : 1 ≤ j + 1 := by omega
  have hcN : j + 1 ≤ n + d := by omega
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (a j * a (j - d + 1) - a (j + 1) * a (j - d)) / a (j - d) :=
    ⟨_, rfl⟩
  have htd : t * a (j - d) = a j * a (j - d + 1) - a (j + 1) * a (j - d) := by
    rw [ht, div_mul_cancel₀ _ (hpos _).ne']
  have htpos : 0 < t := by
    have hs := slc_glob hpos hslc (i := j - d) (j := j) (by omega) (by omega) (by omega)
    rw [ht]
    exact div_pos (by linarith [hs, mul_comm (a (j - d + 1)) (a j)]) (hpos _)
  refine witness_of _ t (by omega) hcN hyE hy (.ch1 j) (fun σ hσ hu => ?_) ?_
  · have hyσ := hy σ hσ
    cases σ with
    | ch1 j' =>
      simp only [Row2.Uses, Row2.InSys, Row2.Holds] at hu hσ hyσ ⊢
      by_cases hjj : j' = j
      · exact Or.inr (by rw [hjj])
      left
      obtain rfl : j' = j + 1 := by omega
      rw [co_add_ev _ t hc1 hcN, co_add_ev _ t hc1 hcN, ite_eq_right (by omega),
        ite_eq_left rfl]
      have := mul_pos htpos (hpos (j + 1 + 1))
      nlinarith
    | ch2 j' =>
      left
      simp only [Row2.Uses, Row2.InSys, Row2.Holds] at hu hσ hyσ ⊢
      rw [co_add_ev _ t hc1 hcN, co_add_ev _ t hc1 hcN]
      rcases hu with hu | hu
      · -- `x_{d+j'}` raised: easier
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        have := mul_pos htpos (hpos (j' + 1))
        nlinarith
      · -- `x_{d+j'+1}` raised, `j' = j − d`: equality by the choice of `t`
        obtain rfl : j' = j - d := by omega
        rw [ite_eq_left (by omega), ite_eq_right (by omega), add_zero,
          show d + (j - d) + 1 = j + 1 by omega, show d + (j - d) = j by omega,
          co_vsum a (by omega) (by omega), co_vsum a (by omega) (by omega),
          ite_eq_left (show j + 1 ≤ n by omega), ite_eq_left (show j ≤ n by omega),
          ite_eq_left (show d < j + 1 ∧ j + 1 ≤ d + n by omega),
          ite_eq_left (show d < j ∧ j ≤ d + n by omega),
          show j + 1 - d = j - d + 1 by omega]
        nlinarith
    | C => simp only [Row2.Uses] at hu; omega
    | D => simp only [Row2.Uses] at hu; omega
    | F => simp only [Row2.Uses] at hu; omega
  · simp only [Row2.Holds]
    rw [co_add_ev _ t hc1 hcN, co_add_ev _ t hc1 hcN, ite_eq_left rfl, ite_eq_right (by omega),
      add_zero]
    have e1 := co_top_sub (a := a) (n := n) (d := d) hc1 (by omega)
    have e0 := co_top_sub (a := a) (n := n) (d := d) (c := j) (by omega) (by omega)
    have := mul_pos htpos (hpos j)
    intro h
    rw [add_sub_right_comm, e1, e0] at h
    linarith

/-- `(Ch2; j)`, `d + j + 1 ≤ n`: `v_d + shift^d v_j − δ e_{d+j}`, `δ = a_{j+1} a_{d+j}/a_{d+j+1}`. -/
lemma wit_ch2_low {j : ℕ} (hj2 : 2 ≤ j) (hjm : d + j + 1 ≤ n) : NotImplied a n d (.ch2 j) := by
  have hlc := logConcaveOn_of_slc hpos hslc
  obtain ⟨hyE, hy⟩ := vsum_holds hpos hlc hd hdn (k := d) (l := j) ⟨hd, by omega⟩
    ⟨by omega, by omega⟩
  have hc1 : 1 ≤ d + j := by omega
  have hcN : d + j ≤ n + d := by omega
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = a (j + 1) * a (d + j) / a (d + j + 1) := ⟨_, rfl⟩
  have hδm : δ * a (d + j + 1) = a (j + 1) * a (d + j) := by
    rw [hδ, div_mul_cancel₀ _ (hpos _).ne']
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos (mul_pos (hpos _) (hpos _)) (hpos _)
  refine witness_of _ (-δ) (by omega) hcN hyE hy (.ch2 j) (fun σ hσ hu => ?_) ?_
  · have hyσ := hy σ hσ
    cases σ with
    | ch1 j' =>
      left
      simp only [Row2.Uses, Row2.InSys, Row2.Holds] at hu hσ hyσ ⊢
      rw [co_add_ev _ (-δ) hc1 hcN, co_add_ev _ (-δ) hc1 hcN]
      rcases hu with hu | hu
      · -- `j' = d + j`: equality by the choice of `δ`
        obtain rfl : j' = d + j := by omega
        rw [ite_eq_right (by omega), ite_eq_left rfl, add_zero,
          co_vsum a (by omega) (by omega), co_vsum a (by omega) (by omega),
          ite_eq_right (show ¬ d + j + 1 ≤ d by omega),
          ite_eq_right (show ¬ (d < d + j + 1 ∧ d + j + 1 ≤ d + j) by omega),
          ite_eq_right (show ¬ d + j ≤ d by omega),
          ite_eq_left (show d < d + j ∧ d + j ≤ d + j by omega)]
        unfold Aof
        rw [ite_eq_left (show d < d + j + 1 by omega), ite_eq_left (show d < d + j by omega),
          show d + j + 1 - d = j + 1 by omega, show d + j - d = j by omega]
        nlinarith
      · -- `x_{j'+1}` lowered: easier
        rw [ite_eq_left (by omega), ite_eq_right (by omega)]
        have := mul_pos hδpos (hpos j')
        nlinarith
    | ch2 j' =>
      simp only [Row2.Uses, Row2.InSys, Row2.Holds] at hu hσ hyσ ⊢
      by_cases hjj : j' = j
      · exact Or.inr (by rw [hjj])
      left
      obtain rfl : j' = j - 1 := by omega
      rw [co_add_ev _ (-δ) hc1 hcN, co_add_ev _ (-δ) hc1 hcN, ite_eq_left (by omega),
        ite_eq_right (by omega)]
      have := mul_pos hδpos (hpos (j - 1))
      nlinarith
    | C => simp only [Row2.Uses] at hu; omega
    | D => simp only [Row2.Uses] at hu; omega
    | F => simp only [Row2.Uses] at hu; omega
  · simp only [Row2.Holds]
    rw [co_add_ev _ (-δ) hc1 hcN, co_add_ev _ (-δ) hc1 hcN, ite_eq_right (by omega),
      ite_eq_left rfl, add_zero, co_vsum a (by omega) (by omega), co_vsum a (by omega) (by omega),
      ite_eq_right (show ¬ d + j + 1 ≤ d by omega),
      ite_eq_right (show ¬ (d < d + j + 1 ∧ d + j + 1 ≤ d + j) by omega),
      ite_eq_right (show ¬ d + j ≤ d by omega),
      ite_eq_left (show d < d + j ∧ d + j ≤ d + j by omega), show d + j - d = j by omega]
    have hs := slc_glob hpos hslc (i := j) (j := d + j) (by omega) (by omega) hjm
    have := hpos (j + 1)
    have := hpos (d + j + 1)
    intro h
    -- `0 ≤ (a_j − δ) a_{j+1}` forces `δ ≤ a_j`, against strict log-concavity
    have h1 : δ ≤ a j := by nlinarith
    have := mul_le_mul_of_nonneg_right h1 (hpos (d + j + 1)).le
    nlinarith

/-- `(Ch2; j)`, `d + j ≥ n`: `v_1 + shift^d v_n − e_{d+j}`. -/
lemma wit_ch2_high {j : ℕ} (hj2 : 2 ≤ j) (hjn : j < n) (hjm : n ≤ d + j) :
    NotImplied a n d (.ch2 j) := by
  have hlc := logConcaveOn_of_slc hpos hslc
  obtain ⟨hyE, hy⟩ := vsum_holds hpos hlc hd hdn (k := 1) (l := n) ⟨le_rfl, by omega⟩
    ⟨by omega, le_rfl⟩
  have hc1 : 1 ≤ d + j := by omega
  have hcN : d + j ≤ n + d := by omega
  refine witness_of _ (-1) (by omega) hcN hyE hy (.ch2 j) (fun σ hσ hu => ?_) ?_
  · have hyσ := hy σ hσ
    cases σ with
    | ch1 j' =>
      left
      simp only [Row2.Uses, Row2.InSys, Row2.Holds] at hu hσ hyσ ⊢
      obtain rfl : j' = d + j - 1 := by omega
      rw [co_add_ev _ (-1) hc1 hcN, co_add_ev _ (-1) hc1 hcN, ite_eq_left (by omega),
        ite_eq_right (by omega)]
      have := hpos (d + j - 1)
      nlinarith
    | ch2 j' =>
      simp only [Row2.Uses, Row2.InSys, Row2.Holds] at hu hσ hyσ ⊢
      by_cases hjj : j' = j
      · exact Or.inr (by rw [hjj])
      left
      obtain rfl : j' = j - 1 := by omega
      rw [co_add_ev _ (-1) hc1 hcN, co_add_ev _ (-1) hc1 hcN, ite_eq_left (by omega),
        ite_eq_right (by omega)]
      have := hpos (j - 1)
      nlinarith
    | C => simp only [Row2.Uses] at hu; omega
    | D =>
      left
      simp only [Row2.Uses, Row2.Holds] at hu hyσ ⊢
      rw [co_add_ev _ (-1) hc1 hcN, ite_eq_left (by omega)]
      linarith
    | F => simp only [Row2.Uses] at hu; omega
  · simp only [Row2.Holds]
    rw [co_add_ev _ (-1) hc1 hcN, co_add_ev _ (-1) hc1 hcN, ite_eq_right (by omega),
      ite_eq_left rfl, add_zero, co_vsum a (by omega) (by omega), co_vsum a (by omega) (by omega),
      ite_eq_right (show ¬ d + j + 1 ≤ 1 by omega),
      ite_eq_left (show d < d + j + 1 ∧ d + j + 1 ≤ d + n by omega),
      ite_eq_right (show ¬ d + j ≤ 1 by omega),
      ite_eq_left (show d < d + j ∧ d + j ≤ d + n by omega),
      show d + j + 1 - d = j + 1 by omega, show d + j - d = j by omega]
    have := hpos (j + 1)
    intro h
    nlinarith

/-- `(C)`: `v_d + shift^d v_1 − δ e_{d+1}`, `δ = a_2 a_{d+1}/a_{d+2}`. -/
lemma wit_C : NotImplied a n d .C := by
  have hlc := logConcaveOn_of_slc hpos hslc
  obtain ⟨hyE, hy⟩ := vsum_holds hpos hlc hd hdn (k := d) (l := 1) ⟨hd, by omega⟩
    ⟨le_rfl, by omega⟩
  have hc1 : 1 ≤ d + 1 := by omega
  have hcN : d + 1 ≤ n + d := by omega
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = a 2 * a (d + 1) / a (d + 2) := ⟨_, rfl⟩
  have hδm : δ * a (d + 2) = a 2 * a (d + 1) := by rw [hδ, div_mul_cancel₀ _ (hpos _).ne']
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos (mul_pos (hpos _) (hpos _)) (hpos _)
  refine witness_of _ (-δ) (by omega) hcN hyE hy .C (fun σ hσ hu => ?_) ?_
  · have hyσ := hy σ hσ
    cases σ with
    | ch1 j' =>
      left
      simp only [Row2.Uses, Row2.InSys, Row2.Holds] at hu hσ hyσ ⊢
      rw [co_add_ev _ (-δ) hc1 hcN, co_add_ev _ (-δ) hc1 hcN]
      rcases hu with hu | hu
      · -- `j' = d + 1`: equality by the choice of `δ`
        obtain rfl : j' = d + 1 := by omega
        rw [ite_eq_right (by omega), ite_eq_left rfl, add_zero,
          co_vsum a (by omega) (by omega), co_vsum a (by omega) (by omega),
          ite_eq_right (show ¬ d + 1 + 1 ≤ d by omega),
          ite_eq_right (show ¬ (d < d + 1 + 1 ∧ d + 1 + 1 ≤ d + 1) by omega),
          ite_eq_right (show ¬ d + 1 ≤ d by omega),
          ite_eq_left (show d < d + 1 ∧ d + 1 ≤ d + 1 by omega)]
        unfold Aof
        rw [ite_eq_left (show d < d + 1 + 1 by omega), ite_eq_left (show d < d + 1 by omega),
          show d + 1 + 1 - d = 2 by omega, show d + 1 - d = 1 by omega,
          show d + 1 + 1 = d + 2 by omega]
        nlinarith
      · -- `x_{j'+1}` lowered, `j' = d`: easier
        rw [ite_eq_left (by omega), ite_eq_right (by omega)]
        have := mul_pos hδpos (hpos j')
        nlinarith
    | ch2 j' => simp only [Row2.Uses, Row2.InSys] at hu hσ; omega
    | C => exact Or.inr rfl
    | D => simp only [Row2.Uses] at hu; omega
    | F => simp only [Row2.Uses] at hu; omega
  · simp only [Row2.Holds]
    rw [co_add_ev _ (-δ) hc1 hcN, ite_eq_left rfl, co_vsum a (by omega) (by omega),
      ite_eq_right (show ¬ d + 1 ≤ d by omega),
      ite_eq_left (show d < d + 1 ∧ d + 1 ≤ d + 1 by omega), show d + 1 - d = 1 by omega]
    intro h
    linarith

/-- `(D)`: `T + δ e_{n+1}`, `δ = a_n a_{m+1}/a_m`, `m = n − d`. -/
lemma wit_D : NotImplied a n d .D := by
  have hlc := logConcaveOn_of_slc hpos hslc
  obtain ⟨hyE, hy⟩ := vsum_holds hpos hlc hd hdn (k := n) (l := n) ⟨by omega, le_rfl⟩
    ⟨by omega, le_rfl⟩
  have hc1 : 1 ≤ n + 1 := by omega
  have hcN : n + 1 ≤ n + d := by omega
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = a n * a (n - d + 1) / a (n - d) := ⟨_, rfl⟩
  have hδm : δ * a (n - d) = a n * a (n - d + 1) := by rw [hδ, div_mul_cancel₀ _ (hpos _).ne']
  have hδpos : 0 < δ := by rw [hδ]; exact div_pos (mul_pos (hpos _) (hpos _)) (hpos _)
  refine witness_of _ δ (by omega) hcN hyE hy .D (fun σ hσ hu => ?_) ?_
  · have hyσ := hy σ hσ
    cases σ with
    | ch1 j' => simp only [Row2.Uses, Row2.InSys] at hu hσ; omega
    | ch2 j' =>
      left
      simp only [Row2.Uses, Row2.InSys, Row2.Holds] at hu hσ hyσ ⊢
      rw [co_add_ev _ δ hc1 hcN, co_add_ev _ δ hc1 hcN]
      rcases hu with hu | hu
      · -- `x_{d+j'}` raised: easier
        rw [ite_eq_right (by omega), ite_eq_left (by omega)]
        have := mul_pos hδpos (hpos (j' + 1))
        nlinarith
      · -- `j' = m`: equality by the choice of `δ`
        obtain rfl : j' = n - d := by omega
        rw [ite_eq_left (by omega), ite_eq_right (by omega), add_zero,
          show d + (n - d) + 1 = n + 1 by omega, show d + (n - d) = n by omega,
          co_top_gt (a := a) hdn (show n < n + 1 by omega) hcN, show n + 1 - d = n - d + 1 by omega]
        have e0 := co_top_sub (a := a) (n := n) (d := d) (c := n) (by omega) le_rfl
        unfold Aof at e0
        rw [ite_eq_left (show d < n by omega)] at e0
        have : co (ravA a (n + d) 0 n + ravA a (n + d) d n) n = a n + a (n - d) := by linarith
        rw [this]
        nlinarith
    | C => simp only [Row2.Uses] at hu; omega
    | D => exact Or.inr rfl
    | F =>
      left
      simp only [Row2.Uses, Row2.Holds] at hu hyσ ⊢
      rw [co_add_ev _ δ hc1 hcN, ite_eq_left (by omega)]
      linarith
  · simp only [Row2.Holds]
    rw [co_add_ev _ δ hc1 hcN, ite_eq_left rfl,
      co_top_gt (a := a) hdn (show n < n + 1 by omega) hcN,
      show n + 1 - d = n - d + 1 by omega]
    intro h
    linarith

/-- `(F)`: `v_1 + shift^d v_1 − e_N`. -/
lemma wit_F : NotImplied a n d .F := by
  have hlc := logConcaveOn_of_slc hpos hslc
  obtain ⟨hyE, hy⟩ := vsum_holds hpos hlc hd hdn (k := 1) (l := 1) ⟨le_rfl, by omega⟩
    ⟨le_rfl, by omega⟩
  have hc1 : 1 ≤ n + d := by omega
  have hcN : n + d ≤ n + d := le_rfl
  refine witness_of _ (-1) (by omega) hcN hyE hy .F (fun σ hσ hu => ?_) ?_
  · have hyσ := hy σ hσ
    cases σ with
    | ch1 j' => simp only [Row2.Uses, Row2.InSys] at hu hσ; omega
    | ch2 j' =>
      left
      simp only [Row2.Uses, Row2.InSys, Row2.Holds] at hu hσ hyσ ⊢
      rw [co_add_ev _ (-1) hc1 hcN, co_add_ev _ (-1) hc1 hcN, ite_eq_left (by omega),
        ite_eq_right (by omega)]
      have := hpos j'
      nlinarith
    | C => simp only [Row2.Uses] at hu; omega
    | D =>
      left
      simp only [Row2.Uses, Row2.Holds] at hu hyσ ⊢
      rw [co_add_ev _ (-1) hc1 hcN, ite_eq_left (by omega)]
      linarith
    | F => exact Or.inr rfl
  · simp only [Row2.Holds]
    rw [co_add_ev _ (-1) hc1 hcN, ite_eq_left rfl, co_vsum a hc1 hcN,
      ite_eq_right (show ¬ n + d ≤ 1 by omega),
      ite_eq_right (show ¬ (d < n + d ∧ n + d ≤ d + 1) by omega)]
    intro h
    linarith

end Witnesses

/-! ## `thm-hrep2`(3) -/

/-- **`thm-hrep2`(3), irredundancy (witness form).**  For a positive strictly log-concave leg
vector and `1 ≤ d < n`, no row of the system without `(Ch2; 1)` is implied by the equation `(E)` and
the other rows: for each row there is a point satisfying `(E)` and all other rows but not that one. -/
theorem thm_hrep2_irredundant (hpos : ∀ s, 0 < a s) (hslc : Pairwise.SLC a n) (hd : 1 ≤ d)
    (hdn : d < n) (ρ : Row2) (hρ : ρ.InSys n) :
    ∃ x : Fin (n + d) → ℝ, co x 1 = a 1 ∧ (∀ σ : Row2, σ.InSys n → σ ≠ ρ → σ.Holds a n d x) ∧
      ¬ ρ.Holds a n d x := by
  cases ρ with
  | ch1 j =>
    rcases Nat.lt_or_ge d j with h | h
    · exact wit_ch1_high hpos hslc hd hdn h hρ.2
    · exact wit_ch1_low hpos hslc hd hdn hρ.1 h
  | ch2 j =>
    rcases Nat.lt_or_ge (d + j) n with h | h
    · exact wit_ch2_low hpos hslc hd hdn hρ.1 h
    · exact wit_ch2_high hpos hslc hd hdn hρ.1 hρ.2 h
  | C => exact wit_C hpos hslc hd hdn
  | D => exact wit_D hpos hslc hd hdn
  | F => exact wit_F hpos hslc hd hdn

end Facets
end ExteriorConvex
