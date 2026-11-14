/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Article 3: the rank-two σ-plateau corollary, and distinctness of the vertices

Two V-side items of `article/exterior-convex_article3_draft_4.org` that sit on top of
`PairwiseReduction.lean` (window form) and `RankR.lean` (polytope form).

## 1. `cor-rank2-lc` (rank two, every weakly log-concave leg vector)

With the slope `σ(u) = a(u+1)/a(u)` (`legSlope`), `m = n − g`, `t = i − g`, the paper states, for
`n ≥ 2`, `1 ≤ g ≤ n−1`:

  `E(a; g)[i][j] = 0 ⟺ 1 ≤ t ≤ m, 1 ≤ j ≤ m`, and (`j < t`, or `j = t+1`, or `j ≥ t+2` and `σ` is
  constant on `[t+1, j+g−1]`);

for `g ≥ n` the matrix is all ones and for `g = 0` it is the identity.

| paper | here |
|---|---|
| `σ`, "constant on `[s,e]`" | `legSlope`, `ConstOn` (`∀ u ∈ [s,e], σ u = σ s`) |
| the zero condition | `rank2Zero` (`t = i − g`, `m = n − g` written out in `ℕ`; `1 ≤ i − g` is `g < i`) |
| `cor-rank2-lc`, `1 ≤ g` | `rank2_lc` — **no upper bound on `g` and no `n ≥ 2` needed**: for `g ≥ n` the zero condition is unsatisfiable (`rank2Zero_of_le`), which is the "all ones" clause, `rank2_all_ones` |
| "for `g = 0` it is the identity" | `rank2_g_zero` |
| the window-system core (no polytope) | `CF_rank2_iff`, `locked_rank2_iff` |
| the proof's step "`a(u+g)/a(u)` constant on `[t+1,j]` ⟺ `σ` constant on `[t+1,j+g−1]`" | `ratio_const_iff_slope_const` (uses weak log-concavity, via `legSlope_anti`) |

Normalisation, as in `RankR.lean`: the polytope is `conv(vsetA a N 0 n) + conv(vsetA a N g n)` in
`Fin N → ℝ` for any `N ≥ n + g` (the paper's `N = n + g` is a special case), `a` positive
everywhere (it is only read on `[1,n]`), and `WLC` is the cross-multiplied weak log-concavity of
`PairwiseReduction.lean`.  "Entry `= 1`" is membership in `Set.extremePoints`.

## 2. Distinctness of the vertices, and the count

| paper (`cor-kozlov-vertices`, "Distinct admissible `𝐣` give distinct vertices") | here |
|---|---|
| uniqueness of the decomposition at a vertex, `r` summands (`lem-vertexdecomp`(2), Part I Lemma 59(2)) | `eq_of_sum_eq_of_mem_extremePoints` |
| distinct admissible tuples give distinct vertices | `vertex_tuple_unique` (only *one* of the two sums need be a vertex, no log-concavity), `vertex_injOn_admissible` |
| every vertex comes from an admissible tuple | `extremePoints_eq_image` |
| `#vertices = #admissible tuples` | `ncard_extremePoints` |

The count is stated for weakly log-concave `a` and sorted shifts, with "admissible" meaning
Theorem 2's (i)–(iii) (`Pairwise.CF`) for every consecutive pair; tuples are `Fin r → ℕ` with
entries in `[1,n]`, extended to `ℕ → ℕ` by `extTuple` to feed `RankR.lean`.

Changelog (newest first): 2026-10-21 `slope` renamed `legSlope` (clashed with Mathlib's root `slope`;
coordinator); 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Vertices.RankR

namespace ExteriorConvex

open Set Pointwise

/-! ## Slopes and plateaus -/

/-- The legSlope `σ(u) = a(u+1)/a(u)`. -/
noncomputable def legSlope (a : ℕ → ℝ) (u : ℕ) : ℝ := a (u + 1) / a u

/-- `f` is constant on `[s, e]`. -/
def ConstOn (f : ℕ → ℝ) (s e : ℕ) : Prop := ∀ u, s ≤ u → u ≤ e → f u = f s

/-- Consecutive equalities on `[s, e]` make `f` constant there. -/
lemma constOn_of_step (f : ℕ → ℝ) {s e : ℕ} (h : ∀ u, s ≤ u → u < e → f u = f (u + 1)) :
    ConstOn f s e := by
  have key : ∀ k, s + k ≤ e → f (s + k) = f s := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
        intro hk
        rw [← add_assoc, ← h (s + k) (by omega) (by omega)]
        exact ih (by omega)
  intro u hs he
  obtain ⟨k, rfl⟩ : ∃ k, u = s + k := ⟨u - s, by omega⟩
  exact key k he

variable {a : ℕ → ℝ} {n : ℕ}

/-- Weak log-concavity: one step of the legSlope is weakly decreasing. -/
lemma slope_step (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {u : ℕ} (hu : 1 ≤ u)
    (hun : u + 2 ≤ n) : legSlope a (u + 1) ≤ legSlope a u := by
  unfold legSlope
  rw [div_le_div_iff₀ (hpos _) (hpos _)]
  have := hlc u hu hun
  nlinarith [this]

/-- The legSlope is weakly decreasing on `[1, n−1]`. -/
lemma legSlope_anti (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) :
    ∀ k w, 1 ≤ w → w + k + 1 ≤ n → legSlope a (w + k) ≤ legSlope a w := by
  intro k
  induction k with
  | zero => intro w _ _; exact le_rfl
  | succ k ih =>
      intro w hw hk
      have h1 := slope_step hpos hlc (u := w + k) (by omega) (by omega)
      have h2 := ih w hw (by omega)
      rw [← add_assoc]
      linarith

/-- Equality of consecutive `g`-ratios is equality of slopes `g` apart. -/
lemma ratio_step_iff (hpos : ∀ s, 0 < a s) (u g : ℕ) :
    a (u + g) / a u = a (u + 1 + g) / a (u + 1) ↔ legSlope a (u + g) = legSlope a u := by
  unfold legSlope
  rw [div_eq_div_iff (hpos _).ne' (hpos _).ne', div_eq_div_iff (hpos _).ne' (hpos _).ne',
    show u + 1 + g = u + g + 1 by omega]
  constructor <;> intro h <;> linarith [mul_comm (a (u + g)) (a (u + 1)),
    mul_comm (a (u + g + 1)) (a u)]

/-- **The step of the paper's proof**: for `t+2 ≤ j`, the ratio `a(u+g)/a(u)` is constant on
`[t+1, j]` iff `σ` is constant on `[t+1, j+g−1]`.  The forward direction uses weak
log-concavity. -/
theorem ratio_const_iff_slope_const (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n)
    {g t j : ℕ} (hg1 : 1 ≤ g) (ht : 1 ≤ t) (htj : t + 2 ≤ j) (hjn : j + g ≤ n) :
    (∀ u, t < u → u ≤ j → a (u + g) / a u = a (j + g) / a j) ↔
      ConstOn (legSlope a) (t + 1) (j + g - 1) := by
  constructor
  · intro h
    -- slopes `g` apart agree from `t+1` to `j−1`
    have hg : ∀ u, t + 1 ≤ u → u ≤ j - 1 → legSlope a (u + g) = legSlope a u := fun u h1 h2 =>
      (ratio_step_iff hpos u g).mp (by
        rw [h u (by omega) (by omega), h (u + 1) (by omega) (by omega)])
    refine constOn_of_step _ fun w hw1 hw2 => ?_
    obtain ⟨u, hu1, hu5, hu6⟩ : ∃ u, t + 1 ≤ u ∧ w + 1 - g ≤ u ∧ (u = t + 1 ∨ u = w + 1 - g) :=
      ⟨max (t + 1) (w + 1 - g), le_max_left _ _, le_max_right _ _, by omega⟩
    have hu2 : u ≤ w := by omega
    have hu3 : u ≤ j - 1 := by omega
    have hu4 : w + 1 ≤ u + g := by omega
    have e1 := hg u hu1 hu3
    have a1 : legSlope a w ≤ legSlope a u := by
      have := legSlope_anti hpos hlc (w - u) u (by omega) (by omega)
      rwa [show u + (w - u) = w by omega] at this
    have a2 : legSlope a (w + 1) ≤ legSlope a w := slope_step hpos hlc (by omega) (by omega)
    have a3 : legSlope a (u + g) ≤ legSlope a (w + 1) := by
      have := legSlope_anti hpos hlc (u + g - (w + 1)) (w + 1) (by omega) (by omega)
      rwa [show w + 1 + (u + g - (w + 1)) = u + g by omega] at this
    linarith
  · intro h
    have hR : ConstOn (fun u => a (u + g) / a u) (t + 1) j := by
      refine constOn_of_step _ fun u h1 h2 => ?_
      refine (ratio_step_iff hpos u g).mpr ?_
      rw [h (u + g) (by omega) (by omega), h u h1 (by omega)]
    intro u h1 h2
    have := hR u (by omega) h2
    have := hR j (by omega) le_rfl
    simp only at *
    linarith

/-! ## The window-system core -/

/-- The zero condition of `cor-rank2-lc`, with `t = i − g` and `m = n − g`. -/
def rank2Zero (a : ℕ → ℝ) (n g i j : ℕ) : Prop :=
  1 ≤ i - g ∧ i - g ≤ n - g ∧ 1 ≤ j ∧ j ≤ n - g ∧
    (j < i - g ∨ j = i - g + 1 ∨ (i - g + 2 ≤ j ∧ ConstOn (legSlope a) (i - g + 1) (j + g - 1)))

/-- For `g ≥ n` the zero condition never holds (the matrix is all ones). -/
lemma rank2Zero_of_le {g i j : ℕ} (hg : n ≤ g) (hin : i ≤ n) : ¬ rank2Zero a n g i j := by
  rintro ⟨h1, -⟩
  omega

/-- The locked condition of the pair `(0, g)` at `(i, j)` is the paper's `j = t+1` or plateau. -/
theorem locked_rank2_iff (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {g i j : ℕ}
    (hg1 : 1 ≤ g) (hj : 1 ≤ j) :
    Pairwise.Locked a n 0 g i (g + j) ↔
      g < i ∧ j + g ≤ n ∧ (j = i - g + 1 ∨ (i - g + 2 ≤ j ∧
        ConstOn (legSlope a) (i - g + 1) (j + g - 1))) ∧ i < g + j := by
  have hratio : ∀ t, i = g + t →
      ((∀ c ∈ Finset.Ioc i (g + j), a (c - 0) * a (g + j - g) = a (g + j - 0) * a (c - g)) ↔
        ∀ u, t < u → u ≤ j → a (u + g) / a u = a (j + g) / a j) := by
    intro t rfl
    constructor
    · intro h u h1 h2
      have := h (g + u) (by rw [Finset.mem_Ioc]; omega)
      simp only [Nat.sub_zero, Nat.add_sub_cancel_left] at this
      rw [div_eq_div_iff (hpos _).ne' (hpos _).ne', add_comm u g, add_comm j g]
      linarith
    · intro h c hc
      rw [Finset.mem_Ioc] at hc
      obtain ⟨u, rfl⟩ : ∃ u, c = g + u := ⟨c - g, by omega⟩
      have := h u (by omega) (by omega)
      rw [div_eq_div_iff (hpos _).ne' (hpos _).ne', add_comm u g, add_comm j g] at this
      simp only [Nat.sub_zero, Nat.add_sub_cancel_left]
      linarith
  constructor
  · rintro ⟨hlt, hdm, hmn, hconst⟩
    obtain ⟨t, rfl⟩ : ∃ t, i = g + t := ⟨i - g, by omega⟩
    have hR := (hratio t rfl).mp hconst
    refine ⟨hdm, by omega, ?_, hlt⟩
    rcases Nat.lt_or_ge j (t + 2) with h | h
    · left; omega
    · right
      rw [show g + t - g = t by omega]
      exact ⟨h, (ratio_const_iff_slope_const hpos hlc hg1 (by omega) h (by omega)).mp hR⟩
  · rintro ⟨hgi, hjn, hcase, hlt⟩
    obtain ⟨t, rfl⟩ : ∃ t, i = g + t := ⟨i - g, by omega⟩
    rw [show g + t - g = t by omega] at hcase
    refine ⟨hlt, hgi, by omega, (hratio t rfl).mpr ?_⟩
    rcases hcase with h | ⟨h, hc⟩
    · intro u h1 h2
      obtain rfl : u = j := by omega
      rfl
    · exact (ratio_const_iff_slope_const hpos hlc hg1 (by omega) h (by omega)).mpr hc

/-- The leg data of a rank-two system with shifts `(0, g)` and choices `(i, j)`. -/
def shift2 (g : ℕ) : ℕ → ℕ := fun p => p * g

/-- The choices `(i, j)` as a sequence. -/
def choice2 (i j : ℕ) : ℕ → ℕ := fun p => if p = 0 then i else j

lemma shift2_mono (g : ℕ) : Monotone (shift2 g) := fun _ _ h => Nat.mul_le_mul_right g h

/-- **`cor-rank2-lc`, window form**: Theorem 2's (i)–(iii) for the pair `(0, g)` at `(i, j)`
fail exactly on the paper's zero set. -/
theorem CF_rank2_iff (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {g i j : ℕ} (hg : 1 ≤ g)
    (hi : 1 ≤ i ∧ i ≤ n) (hj : 1 ≤ j ∧ j ≤ n) :
    Pairwise.CF a n (shift2 g) (choice2 i j) 0 ↔ ¬ rank2Zero a n g i j := by
  have e : Pairwise.CF a n (shift2 g) (choice2 i j) 0 ↔
      i ≤ g + j ∧ ¬ Pairwise.Locked a n 0 g i (g + j) := by
    simp only [Pairwise.CF, shift2, choice2, zero_mul, one_mul, zero_add, one_ne_zero, ↓reduceIte]
    constructor
    · rintro ⟨-, h2, h3⟩; exact ⟨h2, h3⟩
    · rintro ⟨h2, h3⟩; exact ⟨fun h => by omega, h2, h3⟩
  rw [e, locked_rank2_iff hpos hlc hg hj.1]
  unfold rank2Zero
  constructor
  · rintro ⟨h1, h2⟩ ⟨z1, z2, z3, z4, z5⟩
    rcases z5 with z | z | ⟨z, zc⟩
    · omega
    · exact h2 ⟨by omega, by omega, Or.inl z, by omega⟩
    · exact h2 ⟨by omega, by omega, Or.inr ⟨z, zc⟩, by omega⟩
  · intro hz
    refine ⟨?_, ?_⟩
    · by_contra hlt
      exact hz ⟨by omega, by omega, hj.1, by omega, Or.inl (by omega)⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact hz ⟨by omega, by omega, hj.1, by omega, Or.inr h3⟩

/-! ## The polytope form -/

variable {N : ℕ}

/-- The two-summand vertex question as the `r = 2` case of `RankR.lean`. -/
lemma vertex_rank2_iff_CF (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {g i j : ℕ}
    (hN : g + n ≤ N) (hi : 1 ≤ i ∧ i ≤ n) (hj : 1 ≤ j ∧ j ≤ n) :
    ravA a N 0 i + ravA a N g j ∈
        Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N g n)) ↔
      Pairwise.CF a n (shift2 g) (choice2 i j) 0 := by
  have h := vertex_iff_CF (N := N) (r := 2) hpos hlc (shift2_mono g)
    (fun p hp => by
      show p * g + n ≤ N
      interval_cases p <;> omega)
    (fun p hp => by
      show 1 ≤ (if p = 0 then i else j) ∧ (if p = 0 then i else j) ≤ n
      interval_cases p <;> simp <;> omega)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, shift2,
    zero_mul, one_mul, one_ne_zero, ↓reduceIte] at h
  refine h.trans ?_
  constructor
  · intro h0; exact h0 0 (by omega)
  · intro h0 p hp
    obtain rfl : p = 0 := by omega
    exact h0

/-- **`cor-rank2-lc`** (rank two, every weakly log-concave leg vector).  For `g ≥ 1`,
`E(a; g)[i][j] = 1` iff `(i, j)` is outside the paper's zero set.  No upper bound on `g` is
assumed: for `g ≥ n` the zero set is empty (`rank2_all_ones`). -/
theorem rank2_lc (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {g i j : ℕ} (hg : 1 ≤ g)
    (hN : g + n ≤ N) (hi : 1 ≤ i ∧ i ≤ n) (hj : 1 ≤ j ∧ j ≤ n) :
    ravA a N 0 i + ravA a N g j ∈
        Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N g n)) ↔
      ¬ rank2Zero a n g i j := by
  rw [vertex_rank2_iff_CF hpos hlc hN hi hj, CF_rank2_iff hpos hlc hg hi hj]

/-- `cor-rank2-lc`, the clause "for `g ≥ n` the matrix is all ones". -/
theorem rank2_all_ones (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {g i j : ℕ}
    (hg : n ≤ g) (hg1 : 1 ≤ g) (hN : g + n ≤ N) (hi : 1 ≤ i ∧ i ≤ n) (hj : 1 ≤ j ∧ j ≤ n) :
    ravA a N 0 i + ravA a N g j ∈
        Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N g n)) :=
  (rank2_lc hpos hlc hg1 hN hi hj).mpr (rank2Zero_of_le hg hi.2)

/-- `cor-rank2-lc`, the clause "for `g = 0` it is the identity". -/
theorem rank2_g_zero (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {i j : ℕ}
    (hN : n ≤ N) (hi : 1 ≤ i ∧ i ≤ n) (hj : 1 ≤ j ∧ j ≤ n) :
    ravA a N 0 i + ravA a N 0 j ∈
        Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N 0 n)) ↔
      i = j := by
  have h := vertex_rank2_iff_CF (g := 0) hpos hlc (show 0 + n ≤ N by omega) hi hj
  rw [h]
  simp only [Pairwise.CF, shift2, choice2, mul_zero, zero_add, one_ne_zero, ite_true,
    ite_false]
  constructor
  · rintro ⟨h1, -, -⟩; exact h1 trivial
  · rintro rfl
    exact ⟨fun _ => rfl, le_rfl, fun hl => by obtain ⟨h, -⟩ := hl; omega⟩

/-! ## Distinctness of the vertices -/

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **Uniqueness of the decomposition at a vertex, `r` summands** (`lem-vertexdecomp`(2)): if a sum
of generators is a vertex of the Minkowski sum, any other way of writing it as a sum of generators
is the same one. -/
theorem eq_of_sum_eq_of_mem_extremePoints {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (S : ι → Set E) (hS : ∀ i ∈ s, (S i).Finite) (x y : ι → E) (hx : ∀ i ∈ s, x i ∈ S i)
    (hy : ∀ i ∈ s, y i ∈ S i)
    (hv : ∑ i ∈ s, x i ∈ Set.extremePoints ℝ (∑ i ∈ s, convexHull ℝ (S i)))
    (heq : ∑ i ∈ s, y i = ∑ i ∈ s, x i) : ∀ i ∈ s, y i = x i := by
  obtain ⟨f, hf⟩ := (mem_extremePoints_sum_iff s S hS x hx).mp hv
  by_contra hc
  push Not at hc
  obtain ⟨i, hi, hne⟩ := hc
  have hlt : ∑ k ∈ s, f (y k) < ∑ k ∈ s, f (x k) := by
    refine Finset.sum_lt_sum (fun k hk => ?_) ⟨i, hi, hf i hi (y i) (hy i hi) hne⟩
    rcases eq_or_ne (y k) (x k) with h | h
    · rw [h]
    · exact (hf k hk (y k) (hy k hk) h).le
  rw [← map_sum, ← map_sum, heq] at hlt
  exact lt_irrefl _ hlt

end General

/-- **Distinct tuples give distinct vertices.**  If `∑ₚ shift^{d p} v(j p)` is a vertex and equals
`∑ₚ shift^{d p} v(j' p)` for another tuple of choices in `[1,n]`, the tuples agree.  Only positivity
of `a` is used (no log-concavity, no sorting of the shifts). -/
theorem vertex_tuple_unique (hpos : ∀ s, 0 < a s) {r : ℕ} {d j j' : ℕ → ℕ}
    (hN : ∀ p < r, d p + n ≤ N) (hj : ∀ p < r, 1 ≤ j p ∧ j p ≤ n)
    (hj' : ∀ p < r, 1 ≤ j' p ∧ j' p ≤ n)
    (hv : ∑ p ∈ Finset.range r, ravA a N (d p) (j p) ∈
        Set.extremePoints ℝ (∑ p ∈ Finset.range r, convexHull ℝ (vsetA a N (d p) n)))
    (heq : ∑ p ∈ Finset.range r, ravA a N (d p) (j' p) =
        ∑ p ∈ Finset.range r, ravA a N (d p) (j p)) :
    ∀ p < r, j' p = j p := by
  intro p hp
  have h := eq_of_sum_eq_of_mem_extremePoints (Finset.range r) (fun p => vsetA a N (d p) n)
    (fun p _ => vsetA_finite a N (d p) n) (fun p => ravA a N (d p) (j p))
    (fun p => ravA a N (d p) (j' p))
    (fun p hp => ravA_mem_vsetA (hj p (Finset.mem_range.mp hp)).1
      (hj p (Finset.mem_range.mp hp)).2)
    (fun p hp => ravA_mem_vsetA (hj' p (Finset.mem_range.mp hp)).1
      (hj' p (Finset.mem_range.mp hp)).2) hv heq p (Finset.mem_range.mpr hp)
  exact ravA_injOn a hpos (hN p hp) ⟨(hj' p hp).1, (hj' p hp).2⟩ ⟨(hj p hp).1, (hj p hp).2⟩ h

/-! ## The vertex count -/

/-- A tuple `Fin r → ℕ`, extended to `ℕ → ℕ` (by `1` beyond `r`; the value there is never read). -/
def extTuple {r : ℕ} (J : Fin r → ℕ) : ℕ → ℕ := fun p => if h : p < r then J ⟨p, h⟩ else 1

/-- The sum of chosen vertices for a tuple. -/
noncomputable def vertexOf (a : ℕ → ℝ) (N : ℕ) (d : ℕ → ℕ) {r : ℕ} (J : Fin r → ℕ) :
    Fin N → ℝ :=
  ∑ p ∈ Finset.range r, ravA a N (d p) (extTuple J p)

open Classical in
/-- The admissible tuples: entries in `[1,n]`, and Theorem 2's (i)–(iii) for every consecutive
pair. -/
noncomputable def admissible (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℕ) (r : ℕ) : Finset (Fin r → ℕ) :=
  (Fintype.piFinset fun _ => Finset.Icc 1 n).filter
    fun J => ∀ p, p + 1 < r → Pairwise.CF a n d (extTuple J) p

lemma mem_admissible {d : ℕ → ℕ} {r : ℕ} {J : Fin r → ℕ} :
    J ∈ admissible a n d r ↔
      (∀ p < r, 1 ≤ extTuple J p ∧ extTuple J p ≤ n) ∧
        ∀ p, p + 1 < r → Pairwise.CF a n d (extTuple J) p := by
  classical
  unfold admissible
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine and_congr_left' ⟨fun h p hp => ?_, fun h q => ?_⟩
  · simpa [extTuple, hp, Finset.mem_Icc] using h ⟨p, hp⟩
  · have := h q.val q.isLt
    simpa [extTuple, q.isLt, Finset.mem_Icc] using this

lemma extTuple_bounds {d : ℕ → ℕ} {r : ℕ} {J : Fin r → ℕ} (hJ : J ∈ admissible a n d r) :
    ∀ p < r, 1 ≤ extTuple J p ∧ extTuple J p ≤ n := (mem_admissible.mp hJ).1

/-- **The vertex set is the image of the admissible tuples.** -/
theorem extremePoints_eq_image (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {r : ℕ}
    {d : ℕ → ℕ} (hd : Monotone d) (hN : ∀ p < r, d p + n ≤ N) :
    Set.extremePoints ℝ (∑ p ∈ Finset.range r, convexHull ℝ (vsetA a N (d p) n)) =
      vertexOf a N d '' (admissible a n d r : Set (Fin r → ℕ)) := by
  ext x
  constructor
  · intro hx
    have hx' := hx
    rw [← convexHull_sum] at hx'
    have hmem := extremePoints_convexHull_subset hx'
    rw [Set.mem_finsetSum] at hmem
    obtain ⟨y, hy, rfl⟩ := hmem
    have hc : ∀ p : Fin r, ∃ k, (1 ≤ k ∧ k ≤ n) ∧ ravA a N (d p) k = y p := fun p => by
      obtain ⟨k, hk, hk'⟩ := hy (Finset.mem_range.mpr p.isLt)
      exact ⟨k, hk, hk'⟩
    choose J hJ hJy using hc
    have hext : ∀ p < r, ravA a N (d p) (extTuple J p) = y p := fun p hp => by
      simpa [extTuple, hp] using hJy ⟨p, hp⟩
    have hbd : ∀ p < r, 1 ≤ extTuple J p ∧ extTuple J p ≤ n := fun p hp => by
      simpa [extTuple, hp] using hJ ⟨p, hp⟩
    have hsum : vertexOf a N d J = ∑ p ∈ Finset.range r, y p :=
      Finset.sum_congr rfl fun p hp => hext p (Finset.mem_range.mp hp)
    refine ⟨J, ?_, hsum⟩
    rw [Finset.mem_coe, mem_admissible]
    refine ⟨hbd, (vertex_iff_CF hpos hlc hd hN hbd).mp ?_⟩
    rw [show (∑ p ∈ Finset.range r, ravA a N (d p) (extTuple J p)) = vertexOf a N d J from rfl,
      hsum]
    exact hx
  · rintro ⟨J, hJ, rfl⟩
    rw [Finset.mem_coe, mem_admissible] at hJ
    exact (vertex_iff_CF hpos hlc hd hN hJ.1).mpr hJ.2

/-- **Distinct admissible tuples give distinct vertices.** -/
theorem vertex_injOn_admissible (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {r : ℕ}
    {d : ℕ → ℕ} (hd : Monotone d) (hN : ∀ p < r, d p + n ≤ N) :
    Set.InjOn (vertexOf a N d) (admissible a n d r : Set (Fin r → ℕ)) := by
  intro J hJ J' hJ' heq
  rw [Finset.mem_coe] at hJ hJ'
  have hv := (vertex_iff_CF hpos hlc hd hN (extTuple_bounds hJ)).mpr (mem_admissible.mp hJ).2
  have h := vertex_tuple_unique hpos hN (extTuple_bounds hJ) (extTuple_bounds hJ') hv heq.symm
  funext p
  have := h p.val p.isLt
  simpa [extTuple, p.isLt] using this.symm

/-- **`#vertices = #admissible tuples`** (for weakly log-concave `a` and sorted shifts). -/
theorem ncard_extremePoints (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {r : ℕ}
    {d : ℕ → ℕ} (hd : Monotone d) (hN : ∀ p < r, d p + n ≤ N) :
    (Set.extremePoints ℝ (∑ p ∈ Finset.range r, convexHull ℝ (vsetA a N (d p) n))).ncard =
      (admissible a n d r).card := by
  rw [extremePoints_eq_image hpos hlc hd hN,
    (vertex_injOn_admissible hpos hlc hd hN).ncard_image, Set.ncard_coe_finset]

end ExteriorConvex
