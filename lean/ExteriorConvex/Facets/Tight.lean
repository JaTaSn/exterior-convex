/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Part IV: tightness of the facet inequalities, the implied row, and the value table

`article/exterior-convex_article4_draft_1.org`, Section "The facets at every rank".  The existing
files prove only the set equalities: `Facets/RankTwo.lean` (`validity`, `completeness`, `theoremA`)
for `thm-hrep2`(1), `Facets/ThetaForm.lean` (`validityB`, `completenessB`, `theoremB`) for
`thm-theta`.  This file adds:

| Part IV | here |
|---|---|
| `lem-value-table`, the table | `value_table` (with `Aof` as the paper's `A_s`, `a_s = 0` for `s ≤ 0`) |
| `lem-value-table`, the signs of `V(ℓ, j)` | `Vt`, `Vt_nonpos`, `Vt_self`, `Vt_nonneg` |
| `thm-hrep2`(1), "every inequality is tight": a point of `R` with equality | `tight_Ch1`, `tight_Ch2`, `tight_C`, `tight_D`, `tight_F`; together `thm_hrep2_tight` |
| `thm-hrep2`(1), "its bound is the support value of `R`" (valid + tight) | `support_Ch1`, `support_Ch2`, `support_C`, `support_D`, `support_F` (`IsGreatest` / `IsLeast`) |
| `thm-hrep2`(2), first clause: `(Ch2;1)` is implied by the other rows | `thm_hrep2_ch2_one_implied` |
| `thm-theta`, "every inequality is tight" | `tightB_I`, `tightB_C`, `tightB_D`, `tightB_F`; together `thm_theta_tight` |
| `thm-theta`, valid and tight (support values) | `supportB_I`, `supportB_C`, `supportB_D`, `supportB_F` |

**Hypotheses.**  Tightness in the attainment sense (a point of `R` at which the row holds with
equality) needs **no log-concavity and no positivity**: the witnesses are explicit sums of summand
vertices.  The witnesses are, with `v_k` the summand vertices:

* rank two: `(Ch1; j)` at `v_n + shift^d v_n`; `(Ch2; j)` at `v_1 + shift^d v_n`; `(C)`, `(F)` at
  `v_1 + shift^d v_1`; `(D)` at `v_1 + shift^d v_n`;
* rank `r`: `(I; p)` at `∑_{q<p} λ_q shift^{d_q} v_1 + ∑_{q≥p} λ_q shift^{d_q} v_n`; `(C; p)` and `(F)`
  at `∑_q λ_q shift^{d_q} v_1`; `(D; p)` at `∑_q λ_q shift^{d_q} v_n`.

`(F)` needs `n ≥ 2` (for `n = 1`, `x_N = λ_r a_1 > 0` on all of `R`); this is the section's standing
assumption "`n ≥ 2`", and for rank two it follows from `1 ≤ d < n`.  The `thm-theta` witnesses need
only strictly increasing shifts and `d_r + n ≤ N`, not the gap bound and not positive weights.  The
support-value forms add validity, hence the paper's hypotheses (positive, log-concave `a⃗`;
non-negative weights for `thm-theta`).  All rows of `thm-theta` are treated for every `p < r` and
every `1 ≤ j < n`, which includes the rows of the system (`j ≥ 2` for `p ≥ 1`).

Coordinates are the manuscript's, through `co` (`Facets/Chain.lean`); the rows are in the
multiplied-out form of `Qsys` / `QZ`.

Changelog (newest first): 2026-11-17 created (Claude-Code agent, run `2026-11-17_lean-parts-4-5`)
-/
import Mathlib
import ExteriorConvex.Facets.ThetaForm

namespace ExteriorConvex
namespace Facets

open Finset
open scoped Pointwise

/-! ## `lem-value-table` -/

/-- **`lem-value-table`** (the table).  The value of `u = e_{c+1}/a_{j+1} − e_c/a_j` on the vertex
`shift^d v_k` (`k ≥ 1`), with local index `ℓ = c − d` (an integer; `ℓ ≤ 0` allowed): `0` for
`k < ℓ`, `−a_ℓ/a_j` for `k = ℓ`, and `V(ℓ, j) = A_{ℓ+1}/a_{j+1} − A_ℓ/a_j` for `k ≥ ℓ + 1`, where
`A_s = a_s` for `s ≥ 1` and `A_s = 0` for `s ≤ 0` (`Aof a d c = A_{c−d}`).  No hypothesis on `a`. -/
theorem value_table (a : ℕ → ℝ) {N : ℕ} (d k c j : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ c)
    (hcN : c + 1 ≤ N) :
    co (ravA a N d k) (c + 1) / a (j + 1) - co (ravA a N d k) c / a j =
      if d + k < c then 0
      else if c = d + k then -(a (c - d) / a j)
      else Aof a d (c + 1) / a (j + 1) - Aof a d c / a j := by
  rw [co_ravA_in a d k (by omega) hcN, co_ravA_in a d k hc (by omega)]
  unfold Aof
  by_cases h1 : d + k < c
  · rw [ite_eq_left h1, ite_eq_right (by omega), ite_eq_right (by omega)]
    ring
  · rw [ite_eq_right h1]
    by_cases h2 : c = d + k
    · rw [ite_eq_left h2, ite_eq_right (by omega), ite_eq_left (by omega)]
      ring
    · rw [ite_eq_right h2]
      by_cases h3 : d < c
      · rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
          ite_eq_left h3]
      · by_cases h4 : d < c + 1
        · rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left h4,
            ite_eq_right h3]
        · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right h4,
            ite_eq_right h3]

/-- `V(ℓ, j) = a_{ℓ+1}/a_{j+1} − a_ℓ/a_j` (`lem-value-table`). -/
noncomputable def Vt (a : ℕ → ℝ) (ℓ j : ℕ) : ℝ := a (ℓ + 1) / a (j + 1) - a ℓ / a j

/-- `lem-value-table`: `V(ℓ, j) ≤ 0` for `j < ℓ ≤ n − 1`. -/
theorem Vt_nonpos {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n) {ℓ j : ℕ}
    (hj : 1 ≤ j) (hjl : j < ℓ) (hl : ℓ + 1 ≤ n) : Vt a ℓ j ≤ 0 := by
  unfold Vt
  rw [sub_nonpos, div_le_div_iff₀ (hpos _) (hpos _)]
  have := hlc j ℓ hj hjl.le hl
  linarith [mul_comm (a (j + 1)) (a ℓ)]

/-- `lem-value-table`: `V(j, j) = 0`. -/
theorem Vt_self {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) (j : ℕ) : Vt a j j = 0 := by
  unfold Vt
  rw [div_self (hpos _).ne', div_self (hpos _).ne', sub_self]

/-- `lem-value-table`: `V(ℓ, j) ≥ 0` for `1 ≤ ℓ < j ≤ n − 1`. -/
theorem Vt_nonneg {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n) {ℓ j : ℕ}
    (hl : 1 ≤ ℓ) (hlj : ℓ < j) (hj : j + 1 ≤ n) : 0 ≤ Vt a ℓ j := by
  unfold Vt
  rw [sub_nonneg, div_le_div_iff₀ (hpos _) (hpos _)]
  have := hlc ℓ j hl hlj.le hj
  linarith [mul_comm (a (ℓ + 1)) (a j)]

/-! ## Rank two: `thm-hrep2` -/

section RankTwo

variable (a : ℕ → ℝ) {n d : ℕ}

/-- The rank-two polytope `R = ∠(a⃗) + shift^d ∠(a⃗)` in `ℝ^{n+d}`. -/
abbrev R2 (a : ℕ → ℝ) (n d : ℕ) : Set (Fin (n + d) → ℝ) := angle a (n + d) 0 n + angle a (n + d) d n

/-- A sum of two summand vertices lies in `R`. -/
lemma vsum_mem_R2 {k l : ℕ} (hk : 1 ≤ k ∧ k ≤ n) (hl : 1 ≤ l ∧ l ≤ n) :
    ravA a (n + d) 0 k + ravA a (n + d) d l ∈ R2 a n d :=
  Set.add_mem_add (subset_convexHull ℝ _ (ravA_mem_vsetA hk.1 hk.2))
    (subset_convexHull ℝ _ (ravA_mem_vsetA hl.1 hl.2))

/-- The value of a sum of two summand vertices at a manuscript coordinate. -/
lemma co_vsum {k l c : ℕ} (hc : 1 ≤ c) (hcN : c ≤ n + d) :
    co (ravA a (n + d) 0 k + ravA a (n + d) d l) c =
      (if c ≤ k then a c else 0) + (if d < c ∧ c ≤ d + l then a (c - d) else 0) := by
  rw [co_add, co_ravA_in a 0 k hc hcN, co_ravA_in a d l hc hcN, Nat.sub_zero]
  congr 1
  by_cases h : c ≤ k
  · rw [ite_eq_left ⟨by omega, by omega⟩, ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h]

/-- **`thm-hrep2`(1), `(Ch1; j)` is tight**: equality at `v_n + shift^d v_n`. -/
theorem tight_Ch1 (hd : 1 ≤ d) (hdn : d < n) {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    ∃ x ∈ R2 a n d,
      (co x (j + 1) - Aof a d (j + 1)) * a j = (co x j - Aof a d j) * a (j + 1) := by
  refine ⟨_, vsum_mem_R2 a (k := n) (l := n) ⟨by omega, le_rfl⟩ ⟨by omega, le_rfl⟩, ?_⟩
  rw [co_vsum a (by omega) (by omega), co_vsum a (by omega) (by omega)]
  unfold Aof
  split_ifs <;> first | ring1 | omega

/-- **`thm-hrep2`(1), `(Ch2; j)` is tight**: equality at `v_1 + shift^d v_n`. -/
theorem tight_Ch2 (hd : 1 ≤ d) {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    ∃ x ∈ R2 a n d, co x (d + j + 1) * a j = co x (d + j) * a (j + 1) := by
  refine ⟨_, vsum_mem_R2 a (k := 1) (l := n) ⟨le_rfl, by omega⟩ ⟨by omega, le_rfl⟩, ?_⟩
  rw [co_vsum a (by omega) (by omega), co_vsum a (by omega) (by omega),
    ite_eq_right (show ¬ d + j + 1 ≤ 1 by omega), ite_eq_right (show ¬ d + j ≤ 1 by omega),
    ite_eq_left ⟨by omega, by omega⟩, ite_eq_left ⟨by omega, by omega⟩,
    show d + j + 1 - d = j + 1 by omega, show d + j - d = j by omega]
  ring

/-- **`thm-hrep2`(1), `(C)` is tight**: equality at `v_1 + shift^d v_1`. -/
theorem tight_C (hd : 1 ≤ d) (hdn : d < n) : ∃ x ∈ R2 a n d, a 1 = co x (d + 1) := by
  refine ⟨_, vsum_mem_R2 a (k := 1) (l := 1) ⟨le_rfl, by omega⟩ ⟨le_rfl, by omega⟩, ?_⟩
  rw [co_vsum a (by omega) (by omega), ite_eq_right (show ¬ d + 1 ≤ 1 by omega),
    ite_eq_left ⟨by omega, le_rfl⟩, show d + 1 - d = 1 by omega, zero_add]

/-- **`thm-hrep2`(1), `(D)` is tight**: equality at `v_1 + shift^d v_n`. -/
theorem tight_D (hd : 1 ≤ d) (hdn : d < n) : ∃ x ∈ R2 a n d, co x (n + 1) = a (n - d + 1) := by
  refine ⟨_, vsum_mem_R2 a (k := 1) (l := n) ⟨le_rfl, by omega⟩ ⟨by omega, le_rfl⟩, ?_⟩
  rw [co_vsum a (by omega) (by omega), ite_eq_right (show ¬ n + 1 ≤ 1 by omega),
    ite_eq_left ⟨by omega, by omega⟩, show n + 1 - d = n - d + 1 by omega, zero_add]

/-- **`thm-hrep2`(1), `(F)` is tight**: equality at `v_1 + shift^d v_1` (here `n ≥ 2`, from
`1 ≤ d < n`, is used). -/
theorem tight_F (hd : 1 ≤ d) (hdn : d < n) : ∃ x ∈ R2 a n d, 0 = co x (n + d) := by
  refine ⟨_, vsum_mem_R2 a (k := 1) (l := 1) ⟨le_rfl, by omega⟩ ⟨le_rfl, by omega⟩, ?_⟩
  rw [co_vsum a (by omega) le_rfl, ite_eq_right (show ¬ n + d ≤ 1 by omega),
    ite_eq_right (show ¬ (d < n + d ∧ n + d ≤ d + 1) by omega), add_zero]

/-- **`thm-hrep2`(1), tightness**: every inequality of the system `Qsys a n d 1` (rows `(Ch1; j)`,
`(Ch2; j)`, `(C)`, `(D)`, `(F)`) holds with equality at some point of `R`.  No log-concavity and no
positivity is needed for this half; validity (`validity`) is the other half. -/
theorem thm_hrep2_tight (hd : 1 ≤ d) (hdn : d < n) :
    (∀ j, 1 ≤ j → j < n → ∃ x ∈ R2 a n d,
        (co x (j + 1) - Aof a d (j + 1)) * a j = (co x j - Aof a d j) * a (j + 1)) ∧
      (∀ j, 1 ≤ j → j < n → ∃ x ∈ R2 a n d, co x (d + j + 1) * a j = co x (d + j) * a (j + 1)) ∧
      (∃ x ∈ R2 a n d, a 1 = co x (d + 1)) ∧
      (∃ x ∈ R2 a n d, co x (n + 1) = a (n - d + 1)) ∧
      (∃ x ∈ R2 a n d, 0 = co x (n + d)) :=
  ⟨fun _ hj hjn => tight_Ch1 a hd hdn hj hjn, fun _ hj hjn => tight_Ch2 a hd hj hjn,
    tight_C a hd hdn, tight_D a hd hdn, tight_F a hd hdn⟩

/-! ### Support values: valid and tight -/

variable {a}

/-- `(Ch1; j)`: the maximum over `R` of `x_{j+1} a_j − x_j a_{j+1}` is `A_{j+1} a_j − A_j a_{j+1}`
(the multiplied-out form of "the bound `−γ_j` is the support value"). -/
theorem support_Ch1 (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hd : 1 ≤ d) (hdn : d < n)
    {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    IsGreatest ((fun x => co x (j + 1) * a j - co x j * a (j + 1)) '' R2 a n d)
      (Aof a d (j + 1) * a j - Aof a d j * a (j + 1)) := by
  obtain ⟨x, hx, he⟩ := tight_Ch1 a hd hdn hj hjn
  refine ⟨⟨x, hx, by simp only; linarith⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have := (validity a hpos hlc hd hdn hy).2.1 j hj hjn
  simp only
  linarith

/-- `(Ch2; j)`: the maximum over `R` of `x_{d+j+1} a_j − x_{d+j} a_{j+1}` is `0`. -/
theorem support_Ch2 (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hd : 1 ≤ d) (hdn : d < n)
    {j : ℕ} (hj : 1 ≤ j) (hjn : j < n) :
    IsGreatest ((fun x => co x (d + j + 1) * a j - co x (d + j) * a (j + 1)) '' R2 a n d) 0 := by
  obtain ⟨x, hx, he⟩ := tight_Ch2 a hd hj hjn
  refine ⟨⟨x, hx, by simp only; linarith⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  have := (validity a hpos hlc hd hdn hy).2.2.1 j hj hjn
  simp only
  linarith

/-- `(C)`: the minimum over `R` of `x_{d+1}` is `a_1`. -/
theorem support_C (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hd : 1 ≤ d) (hdn : d < n) :
    IsLeast ((fun x => co x (d + 1)) '' R2 a n d) (a 1) := by
  obtain ⟨x, hx, he⟩ := tight_C a hd hdn
  exact ⟨⟨x, hx, he.symm⟩, by
    rintro _ ⟨y, hy, rfl⟩; exact (validity a hpos hlc hd hdn hy).2.2.2.1⟩

/-- `(D)`: the maximum over `R` of `x_{n+1}` is `a_{m+1}`, `m = n − d`. -/
theorem support_D (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hd : 1 ≤ d) (hdn : d < n) :
    IsGreatest ((fun x => co x (n + 1)) '' R2 a n d) (a (n - d + 1)) := by
  obtain ⟨x, hx, he⟩ := tight_D a hd hdn
  exact ⟨⟨x, hx, he⟩, by
    rintro _ ⟨y, hy, rfl⟩; exact (validity a hpos hlc hd hdn hy).2.2.2.2.1⟩

/-- `(F)`: the minimum over `R` of `x_N` is `0`. -/
theorem support_F (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hd : 1 ≤ d) (hdn : d < n) :
    IsLeast ((fun x => co x (n + d)) '' R2 a n d) 0 := by
  obtain ⟨x, hx, he⟩ := tight_F a hd hdn
  exact ⟨⟨x, hx, he.symm⟩, by
    rintro _ ⟨y, hy, rfl⟩; exact (validity a hpos hlc hd hdn hy).2.2.2.2.2⟩

/-- **`thm-hrep2`(2), first clause: the row `(Ch2; 1)` is implied by the others.**  Every point
satisfying all rows except `(Ch2; 1)` (the system `Qsys a n d 2`) satisfies `(Ch2; 1)`:
`completeness` (which does not use the row, for every positive `a⃗`) puts it in `R`, and `validity`
(log-concavity) gives the row on `R`. -/
theorem thm_hrep2_ch2_one_implied (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hd : 1 ≤ d)
    (hdn : d < n) {x : Fin (n + d) → ℝ} (hx : x ∈ Qsys a n d 2) :
    co x (d + 1 + 1) * a 1 ≤ co x (d + 1) * a (1 + 1) :=
  (validity a hpos hlc hd hdn (completeness a hpos hd hdn hx)).2.2.1 1 le_rfl (by omega)

end RankTwo

/-! ## Rank `r`: `thm-theta` -/

section Theta

variable (a : ℕ → ℝ) {N n : ℕ} {d : ℕ → ℕ} (lam : ℕ → ℝ) {r : ℕ}

/-- The sum `∑_{q<r} λ_q shift^{d_q} v_{K q}` of chosen summand vertices. -/
noncomputable def vsumB (N : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r : ℕ) (K : ℕ → ℕ) : Fin N → ℝ :=
  ∑ q ∈ range r, lam q • ravA a N (d q) (K q)

lemma vsumB_mem {K : ℕ → ℕ} (hK : ∀ q < r, 1 ≤ K q ∧ K q ≤ n) :
    vsumB a N d lam r K ∈ Rsum a N n d lam r := by
  unfold vsumB Rsum
  rw [Set.mem_finsetSum]
  refine ⟨fun q => lam q • ravA a N (d q) (K q), fun {q} hq => ?_, rfl⟩
  have hq' := hK q (Finset.mem_range.mp hq)
  exact Set.smul_mem_smul_set (subset_convexHull ℝ _ (ravA_mem_vsetA hq'.1 hq'.2))

lemma co_vsumB (K : ℕ → ℕ) (c : ℕ) :
    co (vsumB a N d lam r K) c = ∑ q ∈ range r, lam q * co (ravA a N (d q) (K q)) c := by
  unfold vsumB
  rw [co_sum]
  simp only [co_smul]

/-- On `[1, N]` the top vertex `v_n` of a window is the window function `Aw`. -/
lemma co_ravA_top (e : ℕ) {c : ℕ} (hc : 1 ≤ c) (hcN : c ≤ N) :
    co (ravA a N e n) c = Aw a n e c := by
  rw [co_ravA_in a e n hc hcN]
  rfl

/-- The vertex `v_1` of a window is supported on its first coordinate. -/
lemma co_ravA_one_of_ne (e : ℕ) {c : ℕ} (hc : c ≠ e + 1) : co (ravA a N e 1) c = 0 := by
  rw [co_ravA, ite_eq_right (by omega)]

/-- The witness of `(I; p)`: `v_1` in the windows before `p`, `v_n` from `p` on. -/
def topFrom (n p : ℕ) : ℕ → ℕ := fun q => if q < p then 1 else n

/-- At the witness of `(I; p)`, the reduced chain of window `p` is the chain of `λ_p v_n`:
`x_c − M(p; c) = λ_p a_{c − d_p}` on the window. -/
lemma co_topFrom_sub_roof (hd : Incr d r) (hN : d (r - 1) + n ≤ N) {p c : ℕ} (hp : p < r)
    (hc1 : d p < c) (hc2 : c ≤ d p + n) :
    co (vsumB a N d lam r (topFrom n p)) c - roof a n d lam r p c = lam p * a (c - d p) := by
  have hcN : c ≤ N := by
    have := hd.le (show p ≤ r - 1 by omega) (by omega)
    omega
  rw [co_vsumB, roof, ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single p]
  · rw [topFrom, ite_eq_right (lt_irrefl p), ite_eq_right (lt_irrefl p), sub_zero,
      co_ravA_top a (d p) (by omega) hcN, Aw_of_in hc1 hc2]
  · intro q hq hqp
    have hqr := Finset.mem_range.mp hq
    rcases Nat.lt_or_gt_of_ne hqp with h | h
    · have hdq := hd.lt h hp
      rw [topFrom, ite_eq_left h, ite_eq_right (show ¬ p < q by omega),
        co_ravA_one_of_ne a (d q) (show c ≠ d q + 1 by omega)]
      ring
    · rw [topFrom, ite_eq_right (show ¬ q < p by omega), ite_eq_left h,
        co_ravA_top a (d q) (by omega) hcN]
      ring
  · intro h; exact absurd (Finset.mem_range.mpr hp) h

/-- **`thm-theta`, `(I; p)` is tight** (every window `p < r`, every link `1 ≤ j < n`): equality at
`∑_{q<p} λ_q shift^{d_q} v_1 + ∑_{q≥p} λ_q shift^{d_q} v_n`. -/
theorem tightB_I (hd : Incr d r) (hN : d (r - 1) + n ≤ N) {p j : ℕ} (hp : p < r) (hj : 1 ≤ j)
    (hjn : j < n) :
    ∃ x ∈ Rsum a N n d lam r,
      (co x (d p + j + 1) - roof a n d lam r p (d p + j + 1)) * a j =
        (co x (d p + j) - roof a n d lam r p (d p + j)) * a (j + 1) := by
  refine ⟨_, vsumB_mem a lam (K := topFrom n p) fun q _ => ?_, ?_⟩
  · unfold topFrom; split_ifs <;> omega
  · rw [co_topFrom_sub_roof a lam hd hN hp (by omega) (by omega),
      co_topFrom_sub_roof a lam hd hN hp (by omega) (by omega),
      show d p + j + 1 - d p = j + 1 by omega, show d p + j - d p = j by omega]
    ring

/-- **`thm-theta`, `(C; p+1)` is tight**: equality at `∑_q λ_q shift^{d_q} v_1`. -/
theorem tightB_C (hn : 1 ≤ n) (hd : Incr d r) (hN : d (r - 1) + n ≤ N) {p : ℕ} (hp : p + 1 < r) :
    ∃ x ∈ Rsum a N n d lam r, lam (p + 1) * a 1 = co x (d (p + 1) + 1) := by
  refine ⟨_, vsumB_mem a lam (K := fun _ => 1) fun q _ => ⟨le_rfl, hn⟩, ?_⟩
  have hcN : d (p + 1) + 1 ≤ N := by
    have := hd.le (show p + 1 ≤ r - 1 by omega) (by omega)
    omega
  rw [co_vsumB, Finset.sum_eq_single (p + 1)]
  · rw [co_ravA, ite_eq_left ⟨by omega, hcN, by omega, le_rfl⟩,
      show d (p + 1) + 1 - d (p + 1) = 1 by omega]
  · intro q hq hqp
    have hqr := Finset.mem_range.mp hq
    have hne : d q ≠ d (p + 1) := by
      rcases Nat.lt_or_gt_of_ne hqp with h | h
      · exact (hd.lt h hp).ne
      · exact (hd.lt h hqr).ne'
    rw [co_ravA_one_of_ne a (d q) (show d (p + 1) + 1 ≠ d q + 1 by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr hp) h

/-- **`thm-theta`, `(D; p+1)` is tight**: equality at `∑_q λ_q shift^{d_q} v_n`. -/
theorem tightB_D (hn : 1 ≤ n) (hd : Incr d r) (hN : d (r - 1) + n ≤ N) {p : ℕ}
    (hp : p + 1 < r) :
    ∃ x ∈ Rsum a N n d lam r, co x (d p + n + 1) = roof a n d lam r p (d p + n + 1) := by
  refine ⟨_, vsumB_mem a lam (K := fun _ => n) fun q _ => ⟨hn, le_rfl⟩, ?_⟩
  have hcN : d p + n + 1 ≤ N := by
    have h1 := hd p hp
    have := hd.le (show p + 1 ≤ r - 1 by omega) (by omega)
    omega
  rw [co_vsumB, roof]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [co_ravA_top a (d q) (by omega) hcN]
  split_ifs with h
  · rfl
  · have := hd.le (show q ≤ p by omega) (by omega)
    unfold Aw
    rw [ite_eq_right (by omega), mul_zero]

/-- **`thm-theta`, `(F)` is tight** (`n ≥ 2`): equality at `∑_q λ_q shift^{d_q} v_1`. -/
theorem tightB_F (hn : 2 ≤ n) (hd : Incr d r) :
    ∃ x ∈ Rsum a N n d lam r, 0 = co x (d (r - 1) + n) := by
  refine ⟨_, vsumB_mem a lam (K := fun _ => 1) fun q _ => ⟨le_rfl, by omega⟩, ?_⟩
  rw [co_vsumB, Finset.sum_eq_zero]
  intro q hq
  have := hd.le (show q ≤ r - 1 by have := Finset.mem_range.mp hq; omega)
    (by have := Finset.mem_range.mp hq; omega)
  rw [co_ravA_one_of_ne a (d q) (show d (r - 1) + n ≠ d q + 1 by omega), mul_zero]

/-- **`thm-theta`, tightness**: every inequality of the Θ-form (`(I; p)` for every `p < r` and
`1 ≤ j < n` — which includes the system's rows, `j ≥ 2` for `p ≥ 1` — `(C; p)`, `(D; p)` for
`2 ≤ p ≤ r` (here `p + 1 < r`), and `(F)`) holds with equality at some point of
`R = ∑_p λ_p shift^{d_p} ∠(a⃗)`.  Needs `n ≥ 2` (for `(F)`), strictly increasing shifts and
`d_r + n ≤ N`; no log-concavity, positivity, gap bound or sign of the weights. -/
theorem thm_theta_tight (hn : 2 ≤ n) (hd : Incr d r) (hN : d (r - 1) + n ≤ N) :
    (∀ p j, p < r → 1 ≤ j → j < n → ∃ x ∈ Rsum a N n d lam r,
        (co x (d p + j + 1) - roof a n d lam r p (d p + j + 1)) * a j =
          (co x (d p + j) - roof a n d lam r p (d p + j)) * a (j + 1)) ∧
      (∀ p, p + 1 < r → ∃ x ∈ Rsum a N n d lam r, lam (p + 1) * a 1 = co x (d (p + 1) + 1)) ∧
      (∀ p, p + 1 < r → ∃ x ∈ Rsum a N n d lam r,
        co x (d p + n + 1) = roof a n d lam r p (d p + n + 1)) ∧
      (∃ x ∈ Rsum a N n d lam r, 0 = co x (d (r - 1) + n)) :=
  ⟨fun _ _ hp hj hjn => tightB_I a lam hd hN hp hj hjn,
    fun _ hp => tightB_C a lam (by omega) hd hN hp,
    fun _ hp => tightB_D a lam (by omega) hd hN hp, tightB_F a lam hn hd⟩

/-! ### Support values: valid and tight -/

variable {a lam}

/-- `(I; p)` at `c = d_p + j` (a row of the system: `j ≥ 1` for `p = 0`, `j ≥ 2` for `p ≥ 1`): the
maximum over `R` of `x_{c+1} a_j − x_c a_{j+1}` is `M(p; c+1) a_j − M(p; c) a_{j+1}`. -/
theorem supportB_I (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hd : Incr d r)
    (hN : d (r - 1) + n ≤ N) (hlam : ∀ p, 0 ≤ lam p) {p j : ℕ} (hp : p < r) (hj : 1 ≤ j)
    (hj2 : 0 < p → 2 ≤ j) (hjn : j < n) :
    IsGreatest ((fun x => co x (d p + j + 1) * a j - co x (d p + j) * a (j + 1)) ''
        Rsum a N n d lam r)
      (roof a n d lam r p (d p + j + 1) * a j - roof a n d lam r p (d p + j) * a (j + 1)) := by
  obtain ⟨x, hx, he⟩ := tightB_I a lam hd hN hp hj hjn
  refine ⟨⟨x, hx, by simp only; linarith⟩, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨-, -, -, hI0, hI, -, -, -⟩ := validityB a hpos hlc (by omega) hd hN hlam hy
  have hrow : (co y (d p + j + 1) - roof a n d lam r p (d p + j + 1)) * a j ≤
      (co y (d p + j) - roof a n d lam r p (d p + j)) * a (j + 1) := by
    rcases Nat.eq_zero_or_pos p with h0 | h0
    · subst h0; exact hI0 j hj hjn
    · exact hI p j h0 hp (hj2 h0) hjn
  simp only
  linarith

/-- `(C; p+1)`: the minimum over `R` of `x_{d_{p+1}+1}` is `λ_{p+1} a_1`. -/
theorem supportB_C (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hn : 1 ≤ n) (hd : Incr d r)
    (hN : d (r - 1) + n ≤ N) (hlam : ∀ p, 0 ≤ lam p) {p : ℕ} (hp : p + 1 < r) :
    IsLeast ((fun x => co x (d (p + 1) + 1)) '' Rsum a N n d lam r) (lam (p + 1) * a 1) := by
  obtain ⟨x, hx, he⟩ := tightB_C a lam hn hd hN hp
  exact ⟨⟨x, hx, he.symm⟩, by
    rintro _ ⟨y, hy, rfl⟩; exact (validityB a hpos hlc (by omega) hd hN hlam hy).2.2.2.2.2.1 p hp⟩

/-- `(D; p+1)`: the maximum over `R` of `x_{d_p+n+1}` is the roof `M(p; d_p+n+1)`. -/
theorem supportB_D (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hn : 1 ≤ n) (hd : Incr d r)
    (hN : d (r - 1) + n ≤ N) (hlam : ∀ p, 0 ≤ lam p) {p : ℕ} (hp : p + 1 < r) :
    IsGreatest ((fun x => co x (d p + n + 1)) '' Rsum a N n d lam r)
      (roof a n d lam r p (d p + n + 1)) := by
  obtain ⟨x, hx, he⟩ := tightB_D a lam hn hd hN hp
  exact ⟨⟨x, hx, he⟩, by
    rintro _ ⟨y, hy, rfl⟩
    exact (validityB a hpos hlc (by omega) hd hN hlam hy).2.2.2.2.2.2.1 p hp⟩

/-- `(F)`: the minimum over `R` of `x_N` is `0` (`n ≥ 2`, `r ≥ 1`). -/
theorem supportB_F (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hn : 2 ≤ n) (hr : 1 ≤ r)
    (hd : Incr d r) (hN : d (r - 1) + n ≤ N) (hlam : ∀ p, 0 ≤ lam p) :
    IsLeast ((fun x => co x (d (r - 1) + n)) '' Rsum a N n d lam r) 0 := by
  obtain ⟨x, hx, he⟩ := tightB_F a lam hn hd (N := N)
  exact ⟨⟨x, hx, he.symm⟩, by
    rintro _ ⟨y, hy, rfl⟩
    exact (validityB a hpos hlc hr hd hN hlam hy).2.2.2.2.2.2.2⟩

end Theta

end Facets
end ExteriorConvex
