/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Small `n`: every lattice point is an ff-vector (`cor-small-n`, `thm-n3-equal-shifts`)

Formalisation of `cor-small-n` and `thm-n3-equal-shifts` of
`article/exterior-convex_article3_draft_4.org`, and of the `n = 4` remark after `cor-small-n`
(`ex-koz3-koz4`).

**Normalisation**, as in `Lattice/LatticePoints.lean` and `Lattice/ChainedExistence.lean`:
degree-0-inclusive coordinates (`Fin (n+1)`, entry `i` = `f_i`); `Koz(n; d⃗)` is
`∑ᵢ shift^{dᵢ} conv(S_n)` in `Fin (N+1) → ℝ` (`= conv FF(n; d⃗)` by `main`); `FF(n; d⃗)` is
`ffSet n N d` (`= ∑ᵢ shift^{dᵢ}(S_n)` by `ff_eq_sumset`); lattice points are `ℤ`-vectors pushed
into `ℝ` by `castR`. The ambient-size hypothesis `d i + n ≤ N` stands in for the paper's
`N = n + d_r`.

| paper | here |
|---|---|
| `𝓛_2 = S_2`, `𝓛_3 = S_3` (`ex-koz3-koz4`), and `𝓛_1` a point | `latticeFinset_{one,two,three}_eq` (kernel `decide`), `castR_mem_Sset_of_latticePts` (explicit witness complexes `cx2`, `cx3`, checked by `decide` through the decidable `IsComplexB`), `latticePts_eq_Sset` (`castR '' 𝓛_n = S_n`, `1 ≤ n ≤ 3`) |
| `cor-small-n`: for `n ≤ 3` every lattice point of `Koz(n; d⃗)` is an ff-vector, every `r`, every `d⃗` | `cor_small_n`; as a set identity `FF(n; d⃗) = Koz(n; d⃗) ∩ ℤ^{N+1}`: `ffSet_eq_lattice`. Proof as the paper's: `cor_additivity` and `𝓛_n = S_n`. **No sortedness of `d⃗` needed**: the sorted case `lattice_mem_ffSet_of_mono` is extended to every `d⃗` by `Tuple.sort` (both sides are sums over `Fin r`) |
| `thm-n3-equal-shifts`: `FF(3; 0^r) = r·Koz(3) ∩ ℤ⁴` | `ff3_equal_shifts` (`r ≥ 1`, `N = 3`), via `koz_zero_shifts` (`Koz(n; 0^r) = r·Koz(n)`) |
| … the triangle `0 ≤ 3f₃ ≤ f₂ ≤ 3r` (and `f₀ = r`, `f₁ = 3r`) | `mem_r_koz3_iff`; as a `Finset`: `tri r`, `coe_tri`, `ff3_eq_tri` |
| … `(r+1)(3r+2)/2` points | `two_mul_card_tri`, `two_mul_ncard_ff3` (stated as `2·# = (r+1)(3r+2)`) |
| … the centroid `(r, 3r, 3r(2r+1)/(3r+2), r²/(3r+2))` | `centroid_ff3` (over `ℚ`, means of `f₂`, `f₃` over `tri r`; `f₀`, `f₁` are constant). The sums: `two_mul_sum_tri_f2`, `two_mul_sum_tri_f3`, as in the paper's proof. `ν₂ = c₂/(3r)`, `ν₃ = c₃/r` and the limits are not restated |
| "At `n = 4` this fails already at rank one" | `koz4_lattice_not_ff`: `(1,4,2,1,0) ∈ 𝓛_4` but `∉ S_4` (`three_le_fEntry_two`: a triangle needs three edges). Only the first of the paper's four points `(2,1,0), (3,2,0), (4,2,0), (5,3,0)` |

`cor-small-n` is stated for `1 ≤ n ≤ 3`; `n = 0` (not meaningful in the paper) is excluded because
`cor_additivity` needs `1 ≤ n`. `ff3_equal_shifts` needs `r ≥ 1` (at `r = 0` the dilate is `{0}`
while `FF(3; ∅) = {0}` too, but `smul_lymChain` needs `t > 0`); the count and the centroid hold for
every `r` over `tri r`. All finite checks are kernel `decide` (no `native_decide`).

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Lattice.ChainedExistence
import ExteriorConvex.Spine.Sumset

open Finset
open scoped Pointwise

namespace ExteriorConvex

namespace Lattice

/-! ## A decidable test for being a complex -/

/-- `IsComplex` with the order-ideal condition bounded by `powerset`, hence decidable. -/
def IsComplexB {n : ℕ} (D : Finset (Finset (Fin n))) : Prop :=
  (∀ s ∈ D, ∀ t ∈ s.powerset, t ∈ D) ∧ (∅ : Finset (Fin n)) ∈ D ∧
    ∀ i : Fin n, ({i} : Finset (Fin n)) ∈ D

instance {n : ℕ} (D : Finset (Finset (Fin n))) : Decidable (IsComplexB D) := by
  unfold IsComplexB; infer_instance

theorem IsComplexB.isComplex {n : ℕ} {D : Finset (Finset (Fin n))} (h : IsComplexB D) :
    IsComplex D where
  ideal := fun s t hs hts => h.1 s hs t (mem_powerset.mpr hts)
  empty_mem := h.2.1
  singleton_mem := h.2.2

/-- A witness complex certifies membership of an integer vector in `S_n`. -/
theorem castR_mem_Sset_of {n : ℕ} {x : Fin (n + 1) → ℤ} (D : Finset (Finset (Fin n)))
    (hD : IsComplexB D) (hf : ∀ j : Fin (n + 1), (fEntry D j.val : ℤ) = x j) :
    castR x ∈ Sset n := by
  refine ⟨D, hD.isComplex, funext fun j => ?_⟩
  simp only [fvec, castR_apply, ← hf j]
  norm_cast

/-! ## `𝓛_n` for `n = 1, 2, 3`, explicitly -/

theorem latticeFinset_one_eq : latticeFinset 1 = {![1, 1]} := by decide

theorem latticeFinset_two_eq : latticeFinset 2 = {![1, 2, 0], ![1, 2, 1]} := by decide

theorem latticeFinset_three_eq :
    latticeFinset 3 = {![1, 3, 0, 0], ![1, 3, 1, 0], ![1, 3, 2, 0], ![1, 3, 3, 0],
      ![1, 3, 3, 1]} := by decide

/-! ## `𝓛_n = S_n` for `n ≤ 3`: witness complexes -/

/-- The witness complexes on `[3]`: three vertices and `k` edges (`k = 0..3`), and the full
triangle. -/
def cx3 : Fin 5 → Finset (Finset (Fin 3)) :=
  ![{∅, {0}, {1}, {2}}, {∅, {0}, {1}, {2}, {0, 1}}, {∅, {0}, {1}, {2}, {0, 1}, {0, 2}},
    {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}},
    {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}}]

/-- The witness complexes on `[2]`: two vertices, and the edge. -/
def cx2 : Fin 2 → Finset (Finset (Fin 2)) := ![{∅, {0}, {1}}, {∅, {0}, {1}, {0, 1}}]

/-- **`𝓛_n ⊆ S_n` for `1 ≤ n ≤ 3`** (`ex-koz3-koz4`: `𝓛_2 = S_2`, `𝓛_3 = S_3`): every lattice
point of `Koz(n)` is the `f`-vector of a simplicial complex on `[n]`. -/
theorem castR_mem_Sset_of_latticePts {n : ℕ} (hn : 1 ≤ n) (h3 : n ≤ 3) {x : Fin (n + 1) → ℤ}
    (hx : x ∈ latticePts n) : castR x ∈ Sset n := by
  rw [← mem_latticeFinset hn] at hx
  interval_cases n
  · rw [latticeFinset_one_eq, mem_singleton] at hx
    subst hx
    exact castR_mem_Sset_of {∅, {0}} (by decide) (by decide)
  · rw [latticeFinset_two_eq] at hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact castR_mem_Sset_of (cx2 0) (by decide) (by decide)
    · exact castR_mem_Sset_of (cx2 1) (by decide) (by decide)
  · rw [latticeFinset_three_eq] at hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact castR_mem_Sset_of (cx3 0) (by decide) (by decide)
    · exact castR_mem_Sset_of (cx3 1) (by decide) (by decide)
    · exact castR_mem_Sset_of (cx3 2) (by decide) (by decide)
    · exact castR_mem_Sset_of (cx3 3) (by decide) (by decide)
    · exact castR_mem_Sset_of (cx3 4) (by decide) (by decide)

/-- Every element of `S_n` is an integer vector. -/
theorem Sset_subset_castR {n : ℕ} {y : Fin (n + 1) → ℝ} (hy : y ∈ Sset n) :
    ∃ x : Fin (n + 1) → ℤ, castR x = y := by
  obtain ⟨D, -, rfl⟩ := hy
  exact ⟨fun j => (fEntry D j.val : ℤ), funext fun j => by simp [fvec]⟩

/-- **`𝓛_n = S_n` for `1 ≤ n ≤ 3`**, as sets of real points: the lattice points of `Koz(n)` are
exactly the `f`-vectors of simplicial complexes on `[n]`. -/
theorem latticePts_eq_Sset {n : ℕ} (hn : 1 ≤ n) (h3 : n ≤ 3) :
    castR '' latticePts n = Sset n := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact castR_mem_Sset_of_latticePts hn h3 hx
  · intro hy
    obtain ⟨x, rfl⟩ := Sset_subset_castR hy
    exact ⟨x, subset_convexHull ℝ _ hy, rfl⟩

/-! ## `cor-small-n` -/

/-- `cor-small-n`, sorted shifts: for `1 ≤ n ≤ 3`, every lattice point of `Koz(n; d⃗)` is an
ff-vector. -/
theorem lattice_mem_ffSet_of_mono {n : ℕ} (hn : 1 ≤ n) (h3 : n ≤ 3) {r N : ℕ} {d : Fin r → ℕ}
    (hd : Monotone d) (hN : ∀ i, d i + n ≤ N) {z : Fin (N + 1) → ℤ}
    (hz : castR z ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)) :
    castR z ∈ ffSet n N d := by
  have hz' : z ∈ ∑ i, shiftZ N (d i) '' latticePts n := by
    rw [← cor_additivity hn hd hN]; exact hz
  rw [Set.mem_fintype_sum] at hz'
  obtain ⟨g, hg, rfl⟩ := hz'
  choose q hq hqg using hg
  rw [ff_eq_sumset, castR_sum]
  refine Set.finsetSum_mem_finsetSum _ _ _ fun i _ => ?_
  rw [← hqg i, castR_shiftZ]
  exact Set.mem_image_of_mem _ (castR_mem_Sset_of_latticePts hn h3 (hq i))

/-- Reindexing a sum over `Fin r` by a permutation. -/
theorem sum_perm_shift {n r N : ℕ} (d : Fin r → ℕ) (σ : Equiv.Perm (Fin r))
    (S : Set (Fin (n + 1) → ℝ)) :
    ∑ i, shiftIncl N (d (σ i)) '' S = ∑ i, shiftIncl N (d i) '' S :=
  Equiv.sum_comp σ (fun i => shiftIncl N (d i) '' S)

/-- **`cor-small-n`** (every `r`, every shift vector — sorted or not): for `1 ≤ n ≤ 3`, every
lattice point of `Koz(n; d⃗)` is an ff-vector. -/
theorem cor_small_n {n : ℕ} (hn : 1 ≤ n) (h3 : n ≤ 3) {r N : ℕ} (d : Fin r → ℕ)
    (hN : ∀ i, d i + n ≤ N) {z : Fin (N + 1) → ℤ}
    (hz : castR z ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)) :
    castR z ∈ ffSet n N d := by
  set σ := Tuple.sort d
  rw [← sum_perm_shift d σ] at hz
  have h := lattice_mem_ffSet_of_mono hn h3 (d := d ∘ σ) (Tuple.monotone_sort d)
    (fun i => hN _) hz
  rw [ff_eq_sumset] at h ⊢
  rwa [← sum_perm_shift d σ]

/-- **`cor-small-n`, as a set identity**: for `1 ≤ n ≤ 3` and every shift vector,
`FF(n; d⃗) = Koz(n; d⃗) ∩ ℤ^{N+1}`. -/
theorem ffSet_eq_lattice {n : ℕ} (hn : 1 ≤ n) (h3 : n ≤ 3) {r N : ℕ} (d : Fin r → ℕ)
    (hN : ∀ i, d i + n ≤ N) :
    ffSet n N d =
      castR '' {z : Fin (N + 1) → ℤ | castR z ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)} := by
  ext y
  constructor
  · intro hy
    have hint : ∃ z : Fin (N + 1) → ℤ, castR z = y := by
      rw [ff_eq_sumset, Set.mem_fintype_sum] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      choose x hx hxg using hg
      choose q hq using fun i => Sset_subset_castR (hx i)
      refine ⟨∑ i, shiftZ N (d i) (q i), ?_⟩
      rw [castR_sum]
      exact sum_congr rfl fun i _ => by rw [castR_shiftZ, hq, hxg]
    obtain ⟨z, rfl⟩ := hint
    refine ⟨z, ?_, rfl⟩
    rw [Set.mem_ofPred_eq, ← main n N d]
    exact subset_convexHull ℝ _ hy
  · rintro ⟨z, hz, rfl⟩
    exact cor_small_n hn h3 d hN hz

/-! ## `thm-n3-equal-shifts` -/

theorem shiftIncl_zero_self {n : ℕ} (x : Fin (n + 1) → ℝ) : shiftIncl n 0 x = x := by
  funext j
  have h : 0 ≤ j.val ∧ j.val - 0 ≤ n := ⟨Nat.zero_le _, by omega⟩
  rw [shiftIncl_apply, dite_eq_left_of_eq_true (eq_true h)]
  rfl

/-- `Koz(n; 0^r) = r·Koz(n)` (`r ≥ 1`, ambient `N = n`). -/
theorem koz_zero_shifts {n r : ℕ} (hn : 1 ≤ n) (hr : 0 < r) :
    ∑ _i : Fin r, shiftIncl n 0 '' convexHull ℝ (Sset n) = (r : ℝ) • convexHull ℝ (Sset n) := by
  have h : shiftIncl n 0 '' convexHull ℝ (Sset n) = convexHull ℝ (Sset n) := by
    simp [shiftIncl_zero_self]
  rw [h, hull_Sset_eq hn, sum_lymChain hn, smul_lymChain (Nat.cast_pos.mpr hr)]

/-- **`thm-n3-equal-shifts`, the set identity**: `FF(3; 0^r) = r·Koz(3) ∩ ℤ⁴` for `r ≥ 1`. -/
theorem ff3_equal_shifts {r : ℕ} (hr : 0 < r) :
    ffSet 3 3 (fun _ : Fin r => 0) =
      castR '' {z : Fin 4 → ℤ | castR z ∈ (r : ℝ) • convexHull ℝ (Sset 3)} := by
  rw [ffSet_eq_lattice (by norm_num) le_rfl _ (fun _ => le_rfl), koz_zero_shifts (by norm_num) hr]

/-- The triangle: an integer vector lies in `r·Koz(3)` iff `f₀ = r`, `f₁ = 3r` and
`0 ≤ 3f₃ ≤ f₂ ≤ 3r`. -/
theorem mem_r_koz3_iff {r : ℕ} (hr : 0 < r) (z : Fin 4 → ℤ) :
    castR z ∈ (r : ℝ) • convexHull ℝ (Sset 3) ↔
      z 0 = r ∧ z 1 = 3 * r ∧ 0 ≤ 3 * z 3 ∧ 3 * z 3 ≤ z 2 ∧ z 2 ≤ 3 * r := by
  rw [hull_Sset_eq (by norm_num), smul_lymChain (Nat.cast_pos.mpr hr)]
  simp only [lymChainAt, Set.mem_ofPred_eq, castR_apply]
  constructor
  · rintro ⟨h0, h1, hc, h3⟩
    have c1 : (z 2 : ℝ) / ((3 : ℕ).choose 2 : ℕ) ≤ z 1 / ((3 : ℕ).choose 1 : ℕ) :=
      hc 1 le_rfl (by norm_num)
    have c2 : (z 3 : ℝ) / ((3 : ℕ).choose 3 : ℕ) ≤ z 2 / ((3 : ℕ).choose 2 : ℕ) :=
      hc 2 (by norm_num) (by norm_num)
    have h3' : (0 : ℝ) ≤ z 3 := h3
    simp only [Nat.choose, Nat.reduceAdd] at c1 c2
    norm_num at c1 c2
    have h1' : (z 1 : ℝ) = 3 * r := by rw [h1]; push_cast; ring
    have e2 : (3 : ℝ) * z 3 ≤ z 2 := by
      have := (le_div_iff₀ (by norm_num : (0:ℝ) < 3)).mp c2
      linarith
    have e3 : (z 2 : ℝ) ≤ 3 * r := by
      rw [div_le_div_iff_of_pos_right (by norm_num)] at c1; linarith
    refine ⟨by exact_mod_cast h0, by exact_mod_cast h1', ?_, by exact_mod_cast e2,
      by exact_mod_cast e3⟩
    have : (0 : ℝ) ≤ 3 * z 3 := by linarith
    exact_mod_cast this
  · rintro ⟨h0, h1, h3a, h3b, h2⟩
    have h0' : (z 0 : ℝ) = r := by exact_mod_cast h0
    have h1' : (z 1 : ℝ) = 3 * r := by exact_mod_cast h1
    have h3a' : (0 : ℝ) ≤ 3 * z 3 := by exact_mod_cast h3a
    have h3b' : (3 : ℝ) * z 3 ≤ z 2 := by exact_mod_cast h3b
    have h2' : (z 2 : ℝ) ≤ 3 * r := by exact_mod_cast h2
    refine ⟨h0', by rw [h1']; push_cast; ring, fun j hj hjn => ?_, by
      show (0 : ℝ) ≤ z 3; linarith⟩
    obtain rfl | rfl : j = 1 ∨ j = 2 := by omega
    · simp only [Nat.reduceAdd, Nat.choose]
      norm_num
      show (z 2 : ℝ) / 3 ≤ z 1 / 3
      rw [h1']; linarith
    · simp only [Nat.reduceAdd, Nat.choose]
      norm_num
      show (z 3 : ℝ) ≤ z 2 / 3
      rw [le_div_iff₀ (by norm_num)]; linarith

/-! ### The count and the centroid -/

/-- The triangle `0 ≤ 3f₃ ≤ f₂ ≤ 3r` in `ℕ²` (pairs `(f₂, f₃)`). -/
def triN (r : ℕ) : Finset (ℕ × ℕ) :=
  ((range (3 * r + 1)) ×ˢ (range (r + 1))).filter fun p => 3 * p.2 ≤ p.1

/-- The lattice point of `r·Koz(3)` with free coordinates `(f₂, f₃)`. -/
def triPt (r : ℕ) (p : ℕ × ℕ) : Fin 4 → ℤ := ![r, 3 * r, p.1, p.2]

/-- The lattice points of `r·Koz(3)`, as a `Finset`. -/
def tri (r : ℕ) : Finset (Fin 4 → ℤ) := (triN r).image (triPt r)

theorem triPt_injective (r : ℕ) : Function.Injective (triPt r) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp only [triPt] at h2 h3
  simp only [Matrix.cons_val] at h2 h3
  simp only [Prod.mk.injEq]
  exact ⟨by exact_mod_cast h2, by exact_mod_cast h3⟩

/-- The lattice points of `r·Koz(3)` are the `Finset` `tri r`. -/
theorem coe_tri {r : ℕ} (hr : 0 < r) :
    {z : Fin 4 → ℤ | castR z ∈ (r : ℝ) • convexHull ℝ (Sset 3)} = (tri r : Set (Fin 4 → ℤ)) := by
  ext z
  rw [Set.mem_ofPred_eq, mem_r_koz3_iff hr, tri, coe_image, Set.mem_image]
  constructor
  · rintro ⟨h0, h1, h3a, h3b, h2⟩
    refine ⟨((z 2).toNat, (z 3).toNat), ?_, ?_⟩
    · simp only [triN, coe_filter, mem_product, mem_range, Set.mem_ofPred_eq]
      omega
    · funext i
      fin_cases i <;> simp [triPt, h0, h1] <;> omega
  · rintro ⟨⟨a, b⟩, hp, rfl⟩
    simp only [triN, coe_filter, mem_product, mem_range, Set.mem_ofPred_eq] at hp
    simp only [triPt, Matrix.cons_val]
    simp
    omega

/-- Sums over the triangle, fibred over `f₂`. -/
theorem sum_triN (r : ℕ) (f : ℕ × ℕ → ℕ) :
    ∑ p ∈ triN r, f p = ∑ a ∈ range (3 * r + 1), ∑ b ∈ range (a / 3 + 1), f (a, b) := by
  rw [triN, sum_filter, sum_product]
  refine sum_congr rfl fun a ha => ?_
  rw [← sum_filter]
  refine sum_congr ?_ fun _ _ => rfl
  ext b
  simp only [mem_filter, mem_range] at ha ⊢
  omega

theorem triN_count (r : ℕ) :
    2 * ∑ a ∈ range (3 * r + 1), ∑ _b ∈ range (a / 3 + 1), (1 : ℕ) = (r + 1) * (3 * r + 2) := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [show 3 * (r + 1) + 1 = 3 * r + 1 + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ]
    simp only [sum_const, card_range, smul_eq_mul, mul_one] at ih ⊢
    rw [show (3 * r + 1) / 3 = r by omega, show (3 * r + 1 + 1) / 3 = r by omega,
      show (3 * r + 1 + 1 + 1) / 3 = r + 1 by omega]
    nlinarith [ih]

theorem triN_sum2 (r : ℕ) :
    2 * ∑ a ∈ range (3 * r + 1), ∑ _b ∈ range (a / 3 + 1), a = 3 * r * (r + 1) * (2 * r + 1) := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [show 3 * (r + 1) + 1 = 3 * r + 1 + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ]
    simp only [sum_const, card_range, smul_eq_mul] at ih ⊢
    rw [show (3 * r + 1) / 3 = r by omega, show (3 * r + 1 + 1) / 3 = r by omega,
      show (3 * r + 1 + 1 + 1) / 3 = r + 1 by omega]
    nlinarith [ih]

theorem triN_sum3 (r : ℕ) :
    2 * ∑ a ∈ range (3 * r + 1), ∑ b ∈ range (a / 3 + 1), b = r ^ 2 * (r + 1) := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [show 3 * (r + 1) + 1 = 3 * r + 1 + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ]
    rw [show (3 * r + 1) / 3 = r by omega, show (3 * r + 1 + 1) / 3 = r by omega,
      show (3 * r + 1 + 1 + 1) / 3 = r + 1 by omega]
    have g1 := sum_range_id_mul_two (r + 1)
    have g2 := sum_range_id_mul_two (r + 1 + 1)
    simp only [Nat.add_sub_cancel] at g1 g2
    nlinarith [ih, g1, g2]

/-- **`thm-n3-equal-shifts`, the count**: `r·Koz(3)` has `(r+1)(3r+2)/2` lattice points
(stated as `2·# = (r+1)(3r+2)`). -/
theorem two_mul_card_tri (r : ℕ) : 2 * (tri r).card = (r + 1) * (3 * r + 2) := by
  rw [tri, card_image_of_injective _ (triPt_injective r), card_eq_sum_ones, sum_triN]
  exact triN_count r

theorem sum_tri (r : ℕ) (g : (Fin 4 → ℤ) → ℤ) :
    ∑ z ∈ tri r, g z = ∑ p ∈ triN r, g (triPt r p) := by
  rw [tri, sum_image fun x _ y _ h => triPt_injective r h]

/-- `∑ f₂ = 3r(r+1)(2r+1)/2` over the lattice points of `r·Koz(3)`. -/
theorem two_mul_sum_tri_f2 (r : ℕ) : 2 * ∑ z ∈ tri r, z 2 = 3 * r * (r + 1) * (2 * r + 1) := by
  rw [sum_tri]
  simp only [triPt, Matrix.cons_val]
  rw [← Nat.cast_sum, sum_triN]
  exact_mod_cast triN_sum2 r

/-- `∑ f₃ = r²(r+1)/2` over the lattice points of `r·Koz(3)`. -/
theorem two_mul_sum_tri_f3 (r : ℕ) : 2 * ∑ z ∈ tri r, z 3 = r ^ 2 * (r + 1) := by
  rw [sum_tri]
  simp only [triPt, Matrix.cons_val]
  rw [← Nat.cast_sum, sum_triN]
  exact_mod_cast triN_sum3 r

/-- `FF(3; 0^r)` is `tri r`, as real points. -/
theorem ff3_eq_tri {r : ℕ} (hr : 0 < r) :
    ffSet 3 3 (fun _ : Fin r => 0) = castR '' (tri r : Set (Fin 4 → ℤ)) := by
  rw [ff3_equal_shifts hr, coe_tri hr]

/-- **`thm-n3-equal-shifts`, the count of ff-vectors**: `#FF(3; 0^r) = (r+1)(3r+2)/2`. -/
theorem two_mul_ncard_ff3 {r : ℕ} (hr : 0 < r) :
    2 * (ffSet 3 3 (fun _ : Fin r => 0)).ncard = (r + 1) * (3 * r + 2) := by
  rw [ff3_eq_tri hr, Set.ncard_image_of_injective _ castR_injective, Set.ncard_coe_finset]
  exact two_mul_card_tri r

/-- **`thm-n3-equal-shifts`, the centroid**: the uniform measure on `FF(3; 0^r)` (= the lattice
points of `r·Koz(3)`, `tri r`) has `f₂`-mean `3r(2r+1)/(3r+2)` and `f₃`-mean `r²/(3r+2)`; its
`f₀`, `f₁` are constantly `r`, `3r`. -/
theorem centroid_ff3 (r : ℕ) :
    (∑ z ∈ tri r, (z 2 : ℚ)) / (tri r).card = 3 * r * (2 * r + 1) / (3 * r + 2) ∧
      (∑ z ∈ tri r, (z 3 : ℚ)) / (tri r).card = r ^ 2 / (3 * r + 2) := by
  have hc : ((tri r).card : ℚ) = (r + 1) * (3 * r + 2) / 2 := by
    have := two_mul_card_tri r
    rw [eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)]
    exact_mod_cast (by linarith : (tri r).card * 2 = (r + 1) * (3 * r + 2))
  have h2 : (∑ z ∈ tri r, (z 2 : ℚ)) = 3 * r * (r + 1) * (2 * r + 1) / 2 := by
    have := two_mul_sum_tri_f2 r
    rw [eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)]
    have : ((2 * ∑ z ∈ tri r, z 2 : ℤ) : ℚ) = ((3 * r * (r + 1) * (2 * r + 1) : ℤ) : ℚ) := by
      rw [this]
    push_cast at this
    linarith
  have h3 : (∑ z ∈ tri r, (z 3 : ℚ)) = r ^ 2 * (r + 1) / 2 := by
    have := two_mul_sum_tri_f3 r
    rw [eq_div_iff (by norm_num : (2 : ℚ) ≠ 0)]
    have : ((2 * ∑ z ∈ tri r, z 3 : ℤ) : ℚ) = ((r ^ 2 * (r + 1) : ℤ) : ℚ) := by
      rw [this]
    push_cast at this
    linarith
  have hr1 : (r : ℚ) + 1 ≠ 0 := by positivity
  have hr2 : 3 * (r : ℚ) + 2 ≠ 0 := by positivity
  rw [hc, h2, h3]
  constructor <;> field_simp

/-! ## `n = 4`: the first lattice point that is not an `f`-vector -/

/-- A complex with a triangle has at least three edges. -/
theorem three_le_fEntry_two {n : ℕ} {D : Finset (Finset (Fin n))} (hD : IsOrderIdeal D)
    (h : 1 ≤ fEntry D 3) : 3 ≤ fEntry D 2 := by
  obtain ⟨s, hs⟩ := card_pos.mp (h : 0 < fEntry D 3)
  rw [mem_filter] at hs
  have hsub : s.powersetCard 2 ⊆ D.filter fun t => #t = 2 := by
    intro t ht
    rw [mem_powersetCard] at ht
    exact mem_filter.mpr ⟨hD hs.1 ht.1, ht.2⟩
  have := card_le_card hsub
  rw [card_powersetCard, hs.2] at this
  exact this

/-- **`n = 4` fails already at rank one** (`ex-koz3-koz4`, the point `(f₂, f₃, f₄) = (2, 1, 0)`):
`(1, 4, 2, 1, 0)` is a lattice point of `Koz(4)` but not an `f`-vector — one triangle needs
three edges. -/
theorem koz4_lattice_not_ff :
    ![1, 4, 2, 1, 0] ∈ latticePts 4 ∧ castR ![1, 4, 2, 1, 0] ∉ Sset 4 := by
  refine ⟨(mem_latticeFinset (by norm_num) _).mp ?_, ?_⟩
  · rw [latticeFinset, mem_filter, Fintype.mem_piFinset]
    decide
  rintro ⟨D, hD, hf⟩
  have h3 := congrFun hf 3
  have h2 := congrFun hf 2
  simp [fvec, castR_apply] at h2 h3
  have e3 : fEntry D 3 = 1 := by exact_mod_cast h3
  have e2 : fEntry D 2 = 2 := by exact_mod_cast h2
  have := three_le_fEntry_two hD.ideal (by omega)
  omega

end Lattice

end ExteriorConvex
