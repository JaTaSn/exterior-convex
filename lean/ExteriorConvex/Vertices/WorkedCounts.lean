/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Article 3: worked vertex counts (`ex-plateau`)

`ex-plateau` of `article/exterior-convex_article3_draft_4.org` takes `n = 5`, the shift vector
`d⃗ = (0, 1)` (`g = 1`), and compares three leg vectors:

| paper | here | #vertices of `RA(a⃗; 0, 1)` |
|---|---|---|
| the plateau vector `(1,2,4,4,4)`, slopes `(2,2,1,1)` | `plateauLeg`, `ex_plateau_vertices` | 15 |
| the Kozlov vector `κ⃗(5) = (C(5,1),…,C(5,5))` | `kozLeg 5`, `ex_plateau_kozlov_vertices` | 16 |
| the all-ones vector `𝟙(5)` | `onesLeg`, `ex_plateau_ones_vertices` | 13 |

All three by the same route: `ncard_extremePoints` (`Vertices/RankTwoCorollary.lean`,
#vertices = #admissible tuples) turns the count into the cardinality of the `Finset`
`admissible a n d r`, whose filter is Theorem 2's conditions (i)–(iii) (`Pairwise.CF`) — a
statement about *real* numbers, and filtered with a classical decidability instance. For a leg
vector with natural-number values, `CF` is equivalent to `CFN`, the same three conditions with the
locking equalities read in `ℕ` (`cf_cast_iff`, proved, by `Nat.cast` injectivity); so
`admissible` equals the decidable `admissibleN` (`admissible_cast_eq`), whose card is computed by
kernel `decide` (no `native_decide`).

The Kozlov count 16 is also `card_vertices_kozlov` of `Vertices/Count.lean` (`n² − (m−1)(m+2)/2`
with `m = 4`); it is recomputed here as an independent check of the route.

**Normalisation**, as in `RankTwoCorollary.lean`: the polytope is
`conv(vsetA a N 0 5) + conv(vsetA a N 1 5)` in `Fin N → ℝ` for any `N ≥ 6` (the paper's `N = n + g
= 6` is a special case); `a` is a function `ℕ → ℝ`, positive everywhere, read only on `[1, 5]`.
The plateau vector is extended by `4` at `0` and beyond `5` (`plateauNat`); the value off `[1,5]`
does not matter, only positivity is needed for `ncard_extremePoints`. The shift vector is
`d p = min p 1` (so `d 0 = 0`, `d 1 = 1`, and `d` is monotone on all of `ℕ`, as the theorem asks).
The three displayed matrices `E(a⃗; 1)` are also checked entry by entry
(`plateau_matrix_correct`, `kozlov_matrix_correct`, `ones_matrix_correct`, via `pair_vertex_iff`),
with entry `(i, j)` of `E(a⃗; g)` being the tuple `(j₁, j₂) = (i, j)`, as in `cor-rank2-lc`'s proof
(`m₁ = i`, `m₂ = g + j`); and `plateau_kozlov_differ`: the plateau and Kozlov matrices differ in
the single entry `(3, 4)`, as the example says. The `g = 2` remark and the explicit Case C
functional `φ` are not formalised.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Vertices.RankTwoCorollary

namespace ExteriorConvex

namespace WorkedCounts

open Finset
open scoped Pointwise

/-! ## A decidable form of Theorem 2's conditions for natural-number leg vectors -/

/-- `Pairwise.Locked` with the locking equalities read in `ℕ`. -/
def LockedN (a : ℕ → ℕ) (n dp dq mp mq : ℕ) : Prop :=
  mp < mq ∧ dq < mp ∧ mq ≤ dp + n ∧
    ∀ c ∈ Ioc mp mq, a (c - dp) * a (mq - dq) = a (mq - dp) * a (c - dq)

instance (a : ℕ → ℕ) (n dp dq mp mq : ℕ) : Decidable (LockedN a n dp dq mp mq) := by
  unfold LockedN; infer_instance

/-- `Pairwise.CF` with the locking equalities read in `ℕ`. -/
def CFN (a : ℕ → ℕ) (n : ℕ) (d j : ℕ → ℕ) (p : ℕ) : Prop :=
  (d p = d (p + 1) → d p + j p = d (p + 1) + j (p + 1)) ∧
    d p + j p ≤ d (p + 1) + j (p + 1) ∧
    ¬ LockedN a n (d p) (d (p + 1)) (d p + j p) (d (p + 1) + j (p + 1))

instance (a : ℕ → ℕ) (n : ℕ) (d j : ℕ → ℕ) (p : ℕ) : Decidable (CFN a n d j p) := by
  unfold CFN; infer_instance

theorem locked_cast_iff (a : ℕ → ℕ) (n dp dq mp mq : ℕ) :
    Pairwise.Locked (fun s => (a s : ℝ)) n dp dq mp mq ↔ LockedN a n dp dq mp mq := by
  simp only [Pairwise.Locked, LockedN]
  norm_cast

/-- **The reformulation is faithful**: for a natural-number leg vector, Theorem 2's (i)–(iii)
over `ℝ` are the decidable `CFN`. -/
theorem cf_cast_iff (a : ℕ → ℕ) (n : ℕ) (d j : ℕ → ℕ) (p : ℕ) :
    Pairwise.CF (fun s => (a s : ℝ)) n d j p ↔ CFN a n d j p := by
  simp only [Pairwise.CF, CFN, locked_cast_iff]

/-- The admissible tuples, decidably. -/
def admissibleN (a : ℕ → ℕ) (n : ℕ) (d : ℕ → ℕ) (r : ℕ) : Finset (Fin r → ℕ) :=
  (Fintype.piFinset fun _ => Icc 1 n).filter
    fun J => ∀ p < r - 1, CFN a n d (extTuple J) p

theorem admissible_cast_eq (a : ℕ → ℕ) (n : ℕ) (d : ℕ → ℕ) (r : ℕ) :
    admissible (fun s => (a s : ℝ)) n d r = admissibleN a n d r := by
  classical
  ext J
  simp only [admissible, admissibleN, mem_filter, cf_cast_iff]
  refine and_congr_right' ⟨fun h p hp => h p (by omega), fun h p hp => h p (by omega)⟩

/-- `ncard_extremePoints` for a natural-number leg vector, in decidable form. -/
theorem ncard_extremePoints_nat {a : ℕ → ℕ} (hpos : ∀ s, 0 < a s)
    (hlc : Pairwise.WLC (fun s => (a s : ℝ)) n) {N r : ℕ} {d : ℕ → ℕ} (hd : Monotone d)
    (hN : ∀ p < r, d p + n ≤ N) :
    (Set.extremePoints ℝ
        (∑ p ∈ range r, convexHull ℝ (vsetA (fun s => (a s : ℝ)) N (d p) n))).ncard =
      (admissibleN a n d r).card := by
  rw [ncard_extremePoints (fun s => by exact_mod_cast hpos s) hlc hd hN, admissible_cast_eq]

/-- Weak log-concavity of a cast natural-number vector is weak log-concavity in `ℕ`. -/
theorem wlc_cast_iff (a : ℕ → ℕ) (n : ℕ) :
    Pairwise.WLC (fun s => (a s : ℝ)) n ↔
      ∀ i ∈ Icc 1 n, i + 2 ≤ n → a i * a (i + 2) ≤ a (i + 1) ^ 2 := by
  simp only [Pairwise.WLC, mem_Icc]
  norm_cast
  exact ⟨fun h i hi => h i hi.1, fun h i h1 h2 => h i ⟨h1, by omega⟩ h2⟩

/-! ## The data of `ex-plateau` -/

/-- The shift vector `d⃗ = (0, 1)`, extended monotonically to `ℕ`. -/
def d01 : ℕ → ℕ := fun p => min p 1

theorem d01_mono : Monotone d01 := fun _ _ h => min_le_min_right 1 h

theorem d01_le {N : ℕ} (hN : 6 ≤ N) : ∀ p < 2, d01 p + 5 ≤ N := by
  intro p _; simp only [d01]; omega

/-- The plateau vector `(1, 2, 4, 4, 4)` on `[1, 5]`, extended by `4`. -/
def plateauNat : ℕ → ℕ := fun s => if s = 1 then 1 else if s = 2 then 2 else 4

/-- The plateau leg vector, as a real vector. -/
noncomputable def plateauLeg : ℕ → ℝ := fun s => (plateauNat s : ℝ)

/-- The Kozlov leg vector `kozLeg 5` in `ℕ`. -/
def kozNat (n : ℕ) : ℕ → ℕ := fun s => if s ≤ n then n.choose s else 1

theorem kozLeg_eq (n : ℕ) : kozLeg n = fun s => (kozNat n s : ℝ) := by
  funext s; simp only [kozLeg, kozNat]; split_ifs <;> simp

/-- The all-ones leg vector. -/
noncomputable def onesLeg : ℕ → ℝ := fun _ => ((1 : ℕ) : ℝ)

theorem plateauNat_pos : ∀ s, 0 < plateauNat s := by
  intro s; simp only [plateauNat]; split_ifs <;> omega

theorem kozNat_pos (n : ℕ) : ∀ s, 0 < kozNat n s := by
  intro s; simp only [kozNat]; split_ifs with h
  · exact Nat.choose_pos h
  · exact one_pos

theorem plateau_wlc : Pairwise.WLC plateauLeg 5 := (wlc_cast_iff plateauNat 5).mpr (by decide)

theorem kozlov5_wlc : Pairwise.WLC (fun s => (kozNat 5 s : ℝ)) 5 :=
  (wlc_cast_iff (kozNat 5) 5).mpr (by decide)

theorem ones_wlc : Pairwise.WLC onesLeg 5 := (wlc_cast_iff (fun _ => 1) 5).mpr (by decide)

/-! ## The three counts -/

/-- The rank-two sum written with `∑ p ∈ range 2`, as `ncard_extremePoints` has it. -/
theorem sum_range_two (a : ℕ → ℝ) (N : ℕ) :
    ∑ p ∈ range 2, convexHull ℝ (vsetA a N (d01 p) 5) =
      convexHull ℝ (vsetA a N 0 5) + convexHull ℝ (vsetA a N 1 5) := by
  simp [sum_range_succ, d01]

/-- **`ex-plateau`: `RA((1,2,4,4,4); 0, 1)` has 15 vertices.** -/
theorem ex_plateau_vertices {N : ℕ} (hN : 6 ≤ N) :
    (Set.extremePoints ℝ
        (convexHull ℝ (vsetA plateauLeg N 0 5) + convexHull ℝ (vsetA plateauLeg N 1 5))).ncard =
      15 := by
  rw [← sum_range_two]
  unfold plateauLeg
  rw [    ncard_extremePoints_nat plateauNat_pos plateau_wlc d01_mono (d01_le hN)]
  decide

/-- **`ex-plateau`, the Kozlov comparison: `RA(κ⃗(5); 0, 1)` has 16 vertices.** -/
theorem ex_plateau_kozlov_vertices {N : ℕ} (hN : 6 ≤ N) :
    (Set.extremePoints ℝ
        (convexHull ℝ (vsetA (kozLeg 5) N 0 5) + convexHull ℝ (vsetA (kozLeg 5) N 1 5))).ncard =
      16 := by
  rw [← sum_range_two, kozLeg_eq,
    ncard_extremePoints_nat (kozNat_pos 5) kozlov5_wlc d01_mono (d01_le hN)]
  decide

/-- **`ex-plateau`, the all-ones comparison: `RA(𝟙(5); 0, 1)` has 13 vertices.** -/
theorem ex_plateau_ones_vertices {N : ℕ} (hN : 6 ≤ N) :
    (Set.extremePoints ℝ
        (convexHull ℝ (vsetA onesLeg N 0 5) + convexHull ℝ (vsetA onesLeg N 1 5))).ncard =
      13 := by
  rw [← sum_range_two]
  unfold onesLeg
  rw [    ncard_extremePoints_nat (a := fun _ => 1) (fun _ => one_pos) ones_wlc d01_mono (d01_le hN)]
  decide

/-! ## The three displayed matrices, entry by entry -/

/-- The tuple `(j₁, j₂) = (i, j)`, extended to `ℕ → ℕ`. -/
def pairTuple (i j : ℕ) : ℕ → ℕ := fun p => if p = 0 then i else j

/-- Rank-two vertex test for a natural-number leg vector: `v_i + shift(v_j)` is a vertex of
`conv(vsetA a N 0 5) + conv(vsetA a N 1 5)` iff the decidable `CFN` holds at the pair. -/
theorem pair_vertex_iff {a : ℕ → ℕ} (hpos : ∀ s, 0 < a s)
    (hlc : Pairwise.WLC (fun s => (a s : ℝ)) 5) {N : ℕ} (hN : 6 ≤ N) {i j : ℕ}
    (hi : 1 ≤ i ∧ i ≤ 5) (hj : 1 ≤ j ∧ j ≤ 5) :
    ravA (fun s => (a s : ℝ)) N 0 i + ravA (fun s => (a s : ℝ)) N 1 j ∈
        Set.extremePoints ℝ (convexHull ℝ (vsetA (fun s => (a s : ℝ)) N 0 5) +
          convexHull ℝ (vsetA (fun s => (a s : ℝ)) N 1 5)) ↔
      CFN a 5 d01 (pairTuple i j) 0 := by
  have h := vertex_iff_CF (N := N) (r := 2) (fun s => (by exact_mod_cast hpos s : (0 : ℝ) < a s))
    hlc d01_mono (d01_le hN) (j := pairTuple i j)
    (fun p hp => by
      rcases (show p = 0 ∨ p = 1 by omega) with rfl | rfl
      · simpa [pairTuple] using hi
      · simpa [pairTuple] using hj)
  rw [sum_range_two] at h
  simp only [sum_range_succ, sum_range_zero, zero_add, pairTuple, d01] at h
  simp only [ite_true, show (1 : ℕ) ≠ 0 from one_ne_zero, ite_false, min_self,
    show min 0 1 = 0 from rfl] at h
  rw [h, ← cf_cast_iff]
  exact ⟨fun h => h 0 (by norm_num), fun h p hp => by
    obtain rfl : p = 0 := by omega
    exact h⟩

/-- `E((1,2,4,4,4); 1)`, as displayed in `ex-plateau` (row `i`, column `j`, from `1`). -/
def plateauMatrix : Fin 5 → Fin 5 → ℕ :=
  ![![1, 1, 1, 1, 1], ![1, 0, 1, 1, 1], ![0, 1, 0, 0, 1], ![0, 0, 1, 0, 1], ![0, 0, 0, 1, 1]]

/-- `E(κ⃗(5); 1)`, as displayed in `ex-plateau`. -/
def kozlovMatrix : Fin 5 → Fin 5 → ℕ :=
  ![![1, 1, 1, 1, 1], ![1, 0, 1, 1, 1], ![0, 1, 0, 1, 1], ![0, 0, 1, 0, 1], ![0, 0, 0, 1, 1]]

/-- `E(𝟙(5); 1)`, as displayed in `ex-plateau`. -/
def onesMatrix : Fin 5 → Fin 5 → ℕ :=
  ![![1, 1, 1, 1, 1], ![1, 0, 0, 0, 1], ![0, 1, 0, 0, 1], ![0, 0, 1, 0, 1], ![0, 0, 0, 1, 1]]

/-- **The plateau matrix of `ex-plateau` is correct, entry by entry.** -/
theorem plateau_matrix_correct {N : ℕ} (hN : 6 ≤ N) (i j : Fin 5) :
    ravA plateauLeg N 0 (i.val + 1) + ravA plateauLeg N 1 (j.val + 1) ∈
        Set.extremePoints ℝ (convexHull ℝ (vsetA plateauLeg N 0 5) +
          convexHull ℝ (vsetA plateauLeg N 1 5)) ↔ plateauMatrix i j = 1 := by
  unfold plateauLeg
  rw [pair_vertex_iff plateauNat_pos plateau_wlc hN (by omega) (by omega)]
  revert i j; decide

/-- **The Kozlov matrix of `ex-plateau` is correct, entry by entry.** -/
theorem kozlov_matrix_correct {N : ℕ} (hN : 6 ≤ N) (i j : Fin 5) :
    ravA (kozLeg 5) N 0 (i.val + 1) + ravA (kozLeg 5) N 1 (j.val + 1) ∈
        Set.extremePoints ℝ (convexHull ℝ (vsetA (kozLeg 5) N 0 5) +
          convexHull ℝ (vsetA (kozLeg 5) N 1 5)) ↔ kozlovMatrix i j = 1 := by
  rw [kozLeg_eq, pair_vertex_iff (kozNat_pos 5) kozlov5_wlc hN (by omega) (by omega)]
  revert i j; decide

/-- **The all-ones matrix of `ex-plateau` is correct, entry by entry.** -/
theorem ones_matrix_correct {N : ℕ} (hN : 6 ≤ N) (i j : Fin 5) :
    ravA onesLeg N 0 (i.val + 1) + ravA onesLeg N 1 (j.val + 1) ∈
        Set.extremePoints ℝ (convexHull ℝ (vsetA onesLeg N 0 5) +
          convexHull ℝ (vsetA onesLeg N 1 5)) ↔ onesMatrix i j = 1 := by
  unfold onesLeg
  rw [pair_vertex_iff (a := fun _ => 1) (fun _ => one_pos) ones_wlc hN (by omega) (by omega)]
  revert i j; decide

/-- The plateau and Kozlov matrices differ in exactly one entry, `(i, j) = (3, 4)`. -/
theorem plateau_kozlov_differ :
    ∀ i j : Fin 5, plateauMatrix i j ≠ kozlovMatrix i j ↔ (i.val + 1 = 3 ∧ j.val + 1 = 4) := by
  decide

end WorkedCounts

end ExteriorConvex
