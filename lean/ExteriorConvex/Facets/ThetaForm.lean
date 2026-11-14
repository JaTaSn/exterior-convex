/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

Changelog (newest first):
- 2026-10-20  Created (article-3 overnight push): Theorem B of
              `working-notes/kozlov-hdescription-proof-2026-10-20.org`, the rank-`r` weighted
              Θ-form H-description `Q_Θ = R` (validity = Lemma B1, completeness = induction on `r`
              with the peel of Lemma B2 as the step), and its Kozlov specialisation.

# Theorem B: the rank-`r` Θ-form H-description

Standing: `a : ℕ → ℝ` positive, weakly log-concave on `[1, n]` (`LogConcaveOn`, `RankTwo.lean`).
Windows are indexed `p = 0, …, r−1` (the note's `p = 1, …, r`), shifts `d p`, weights `lam p > 0`:

    R = Rsum a N n d lam r = ∑_{p < r} lam p • shift^{d p} ∠(a)   ⊂ Fin N → ℝ.

The roof after `p`, `roof … p c = ∑_{q > p} lam q · Aw a n (d q) c`, with `Aw a n e c = a(c − e)` on
the window `[e+1, e+n]` and `0` elsewhere (the maximum of coordinate `c` over the summands after
`p`).  The system `QZ a N n d lam r` (manuscript coordinates `co`, chains multiplied out):

* (Z) `x(c) = 0` for `c ≤ d 0` and for `c > d(r−1) + n`  (vacuous when `d 0 = 0`,
  `N = d(r−1) + n`; see `QTheta` / `QZ_eq_QTheta`);
* (E) `x(d 0 + 1) = lam 0 · a 1`;
* (I; 0) `(x(c+1) − M(0; c+1))·a j ≤ (x(c) − M(0; c))·a(j+1)`, `c = d 0 + j`, `1 ≤ j < n`;
* (I; p), `1 ≤ p < r`: the same with `M(p; ·)`, `c = d p + j`, `2 ≤ j < n`;
* (C; p+1), `p + 1 < r`: `lam(p+1)·a 1 ≤ x(d(p+1) + 1)`;
* (D; p+1), `p + 1 < r`: `x(d p + n + 1) ≤ M(p; d p + n + 1)`;
* (F) `0 ≤ x(d(r−1) + n)`.

This is the note's Theorem B system verbatim (its (D; p) is indexed by the window *before*), with
the first shift and the ambient dimension left free so that the peel stays in one space.

Results:
* `validityB` (Lemma B1): `R ⊆ QZ` for strictly increasing shifts, weights `≥ 0`, log-concave `a`;
  no gap condition.
* `peel` (Lemma B2) and `completenessB`: `QZ ⊆ R` for strictly increasing shifts with all gaps
  `≤ n − 1`, weights `> 0`, log-concave `a`; induction on `r`, the peel being
  `w = min(x, M(0; ·))` on the first window (the rank-two truncation of `RankTwo.lean`).
* `theoremB` (`R = QZ`), `theoremB_theta` (`R = QTheta` for `d 0 = 0`, `N = d(r−1) + n`), and
  `theoremB_kozlov` (leg vector `κ⃗(n)`, unit weights); `QZ_rank_two` checks that at `r = 2` the
  system is `RankTwo.lean`'s `Qsys a n d 2`.

Weights are general reals; positivity is assumed for every index (`∀ p, 0 < lam p`), which is no
loss since `R` and `Q_Θ` only read `lam` below `r`.  The facet count (Lemma B3) and the
tied-shift / block corollaries C, D are not formalised.
-/
import Mathlib
import ExteriorConvex.Facets.Specialise

namespace ExteriorConvex
namespace Facets

open Finset Pointwise

/-! ## Definitions -/

/-- The window function of `shift^e ∠(a)`'s top vertex: `a(c − e)` on `[e+1, e+n]`, else `0`. -/
noncomputable def Aw (a : ℕ → ℝ) (n e c : ℕ) : ℝ := if e < c ∧ c ≤ e + n then a (c - e) else 0

/-- The roof after window `p`: `M(p; c) = ∑_{p < q < r} lam q · Aw a n (d q) c`. -/
noncomputable def roof (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r p c : ℕ) : ℝ :=
  ∑ q ∈ range r, if p < q then lam q * Aw a n (d q) c else 0

/-- Strictly increasing shifts on the first `r` windows. -/
def Incr (d : ℕ → ℕ) (r : ℕ) : Prop := ∀ p, p + 1 < r → d p < d (p + 1)

/-- All gaps at most `n − 1`. -/
def Gaps (n : ℕ) (d : ℕ → ℕ) (r : ℕ) : Prop := ∀ p, p + 1 < r → d (p + 1) < d p + n

/-- The Minkowski sum `R = ∑_{p<r} lam p • shift^{d p} ∠(a)`. -/
def Rsum (a : ℕ → ℝ) (N n : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r : ℕ) : Set (Fin N → ℝ) :=
  ∑ p ∈ range r, lam p • angle a N (d p) n

/-- The weighted Θ-form system, with free first shift and ambient dimension (support rows (Z)). -/
def QZ (a : ℕ → ℝ) (N n : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r : ℕ) : Set (Fin N → ℝ) :=
  {x | (∀ c, c ≤ d 0 → co x c = 0) ∧ (∀ c, d (r - 1) + n < c → co x c = 0) ∧
    co x (d 0 + 1) = lam 0 * a 1 ∧
    (∀ j, 1 ≤ j → j < n →
      (co x (d 0 + j + 1) - roof a n d lam r 0 (d 0 + j + 1)) * a j ≤
        (co x (d 0 + j) - roof a n d lam r 0 (d 0 + j)) * a (j + 1)) ∧
    (∀ p j, 0 < p → p < r → 2 ≤ j → j < n →
      (co x (d p + j + 1) - roof a n d lam r p (d p + j + 1)) * a j ≤
        (co x (d p + j) - roof a n d lam r p (d p + j)) * a (j + 1)) ∧
    (∀ p, p + 1 < r → lam (p + 1) * a 1 ≤ co x (d (p + 1) + 1)) ∧
    (∀ p, p + 1 < r → co x (d p + n + 1) ≤ roof a n d lam r p (d p + n + 1)) ∧
    0 ≤ co x (d (r - 1) + n)}

/-! ## Elementary facts -/

lemma Incr.lt {d : ℕ → ℕ} {r : ℕ} (h : Incr d r) {p q : ℕ} (hpq : p < q) (hq : q < r) :
    d p < d q := by
  induction q, hpq using Nat.le_induction with
  | base => exact h p hq
  | succ q hpq ih => exact lt_trans (ih (by omega)) (h q hq)

lemma Incr.le {d : ℕ → ℕ} {r : ℕ} (h : Incr d r) {p q : ℕ} (hpq : p ≤ q) (hq : q < r) :
    d p ≤ d q := by
  rcases eq_or_lt_of_le hpq with h' | h'
  · rw [h']
  · exact (h.lt h' hq).le

lemma Incr.tail {d : ℕ → ℕ} {r : ℕ} (h : Incr d (r + 1)) : Incr (fun p => d (p + 1)) r :=
  fun p hp => h (p + 1) (by omega)

lemma Gaps.tail {n : ℕ} {d : ℕ → ℕ} {r : ℕ} (h : Gaps n d (r + 1)) :
    Gaps n (fun p => d (p + 1)) r :=
  fun p hp => h (p + 1) (by omega)

lemma Aw_nonneg {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) (n e c : ℕ) : 0 ≤ Aw a n e c := by
  unfold Aw; split_ifs
  · exact (hpos _).le
  · exact le_rfl

lemma Aw_of_le {a : ℕ → ℝ} {n e c : ℕ} (h : c ≤ e) : Aw a n e c = 0 := by
  unfold Aw; rw [if_neg (by omega)]

lemma Aw_of_in {a : ℕ → ℝ} {n e c : ℕ} (h1 : e < c) (h2 : c ≤ e + n) : Aw a n e c = a (c - e) := by
  unfold Aw; rw [if_pos ⟨h1, h2⟩]

lemma co_sub {N : ℕ} (x y : Fin N → ℝ) (c : ℕ) : co (x - y) c = co x c - co y c := by
  unfold co; split_ifs <;> simp

lemma co_ravA_nonneg {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {N : ℕ} (e k c : ℕ) :
    0 ≤ co (ravA a N e k) c := by
  rw [co_ravA]; split_ifs
  · exact (hpos _).le
  · exact le_rfl

lemma co_ravA_le_Aw {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {N n e k : ℕ} (hk : k ≤ n) (c : ℕ) :
    co (ravA a N e k) c ≤ Aw a n e c := by
  rw [co_ravA]; unfold Aw
  split_ifs with h1 h2 h2
  · exact le_rfl
  · omega
  · exact (hpos _).le
  · exact le_rfl

/-- The roof over an empty tail is `0`. -/
lemma roof_eq_zero_of_le {a : ℕ → ℝ} {n : ℕ} {d : ℕ → ℕ} {lam : ℕ → ℝ} {r p c : ℕ}
    (h : ∀ q, p < q → q < r → c ≤ d q) : roof a n d lam r p c = 0 := by
  unfold roof
  apply Finset.sum_eq_zero
  intro q hq
  rw [Finset.mem_range] at hq
  split_ifs with hpq
  · rw [Aw_of_le (h q hpq hq), mul_zero]
  · rfl

lemma roof_nonneg {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {n : ℕ} {d : ℕ → ℕ} {lam : ℕ → ℝ}
    (hlam : ∀ p, 0 ≤ lam p) (r p c : ℕ) : 0 ≤ roof a n d lam r p c := by
  unfold roof
  apply Finset.sum_nonneg
  intro q _
  split_ifs
  · exact mul_nonneg (hlam q) (Aw_nonneg hpos _ _ _)
  · exact le_rfl

/-- The peeled system's roofs are the original roofs, one window later. -/
lemma roof_tail (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r p c : ℕ) :
    roof a n (fun q => d (q + 1)) (fun q => lam (q + 1)) r p c = roof a n d lam (r + 1) (p + 1) c := by
  unfold roof
  rw [Finset.sum_range_succ']
  simp only [Nat.not_lt_zero, ite_false, add_zero, Nat.add_lt_add_iff_right]

/-! ## Convexity of the system -/

section Convexity

variable {s t X Y K : ℝ}

lemma cvx_eq (hst : s + t = 1) (hx : X = K) (hy : Y = K) : s * X + t * Y = K := by
  rw [hx, hy, ← add_mul, hst, one_mul]

lemma cvx_le (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (hx : X ≤ K) (hy : Y ≤ K) :
    s * X + t * Y ≤ K := by
  obtain rfl : t = 1 - s := by linarith
  have := mul_le_mul_of_nonneg_left hx hs
  have := mul_le_mul_of_nonneg_left hy ht
  linarith

lemma cvx_ge (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1) (hx : K ≤ X) (hy : K ≤ Y) :
    K ≤ s * X + t * Y := by
  obtain rfl : t = 1 - s := by linarith
  have := mul_le_mul_of_nonneg_left hx hs
  have := mul_le_mul_of_nonneg_left hy ht
  linarith

lemma cvx_chain {X1 X0 Y1 Y0 M1 M0 α β : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
    (hx : (X1 - M1) * α ≤ (X0 - M0) * β) (hy : (Y1 - M1) * α ≤ (Y0 - M0) * β) :
    (s * X1 + t * Y1 - M1) * α ≤ (s * X0 + t * Y0 - M0) * β := by
  obtain rfl : t = 1 - s := by linarith
  have h1 := mul_le_mul_of_nonneg_left hx hs
  have h2 := mul_le_mul_of_nonneg_left hy ht
  linarith

end Convexity

theorem convex_QZ (a : ℕ → ℝ) (N n : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r : ℕ) :
    Convex ℝ (QZ a N n d lam r) := by
  intro x hx y hy s t hs ht hst
  obtain ⟨hx1, hx2, hx3, hx4, hx5, hx6, hx7, hx8⟩ := hx
  obtain ⟨hy1, hy2, hy3, hy4, hy5, hy6, hy7, hy8⟩ := hy
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc; simp only [co_add, co_smul, hx1 c hc, hy1 c hc]; ring
  · intro c hc; simp only [co_add, co_smul, hx2 c hc, hy2 c hc]; ring
  · simp only [co_add, co_smul]; exact cvx_eq hst hx3 hy3
  · intro j hj hjn
    simp only [co_add, co_smul]; exact cvx_chain hs ht hst (hx4 j hj hjn) (hy4 j hj hjn)
  · intro p j h1 h2 h3 h4
    simp only [co_add, co_smul]
    exact cvx_chain hs ht hst (hx5 p j h1 h2 h3 h4) (hy5 p j h1 h2 h3 h4)
  · intro p hp; simp only [co_add, co_smul]; exact cvx_ge hs ht hst (hx6 p hp) (hy6 p hp)
  · intro p hp; simp only [co_add, co_smul]; exact cvx_le hs ht hst (hx7 p hp) (hy7 p hp)
  · simp only [co_add, co_smul]; exact add_nonneg (mul_nonneg hs hx8) (mul_nonneg ht hy8)

/-! ## Validity (Lemma B1) -/

/-- Lemma B1, windows `q ≤ p` (no roof): the link `(c, c+1)` with `c ≥ e + j`. -/
lemma window_L {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n) {N e k c j : ℕ}
    (hkn : k ≤ n) (hj : 1 ≤ j) (hjn : j + 1 ≤ n) (hc : e + j ≤ c) (hcN : c + 1 ≤ N) :
    co (ravA a N e k) (c + 1) * a j ≤ co (ravA a N e k) c * a (j + 1) := by
  rw [co_ravA_in a e k (by omega) hcN, co_ravA_in a e k (by omega) (by omega)]
  have := hpos j
  have := hpos (j + 1)
  have := hpos (c - e)
  split_ifs with h1 h2 h2
  · rw [show c + 1 - e = c - e + 1 by omega]
    have := hlc j (c - e) hj (by omega) (by omega)
    linarith
  · omega
  · rw [zero_mul]; positivity
  · simp

/-- Lemma B1, windows `q > p` (roof present): the link `(c, c+1)` with `c < e + j`,
`c + 1 ≤ e + n`. -/
lemma window_R {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n) {N e k c j : ℕ}
    (hk : 1 ≤ k) (hj : 1 ≤ j) (hjn : j + 1 ≤ n) (hc0 : 1 ≤ c) (hc : c < e + j)
    (hc1 : c + 1 ≤ e + n) (hcN : c + 1 ≤ N) :
    (co (ravA a N e k) (c + 1) - Aw a n e (c + 1)) * a j ≤
      (co (ravA a N e k) c - Aw a n e c) * a (j + 1) := by
  rw [co_ravA_in a e k (by omega) hcN, co_ravA_in a e k hc0 (by omega)]
  unfold Aw
  rcases Nat.lt_or_ge e c with hec | hec
  · have key := hlc (c - e) j (by omega) (by omega) hjn
    rw [show c + 1 - e = c - e + 1 by omega]
    have := hpos j
    have := hpos (j + 1)
    have := hpos (c - e)
    have := hpos (c - e + 1)
    rw [if_pos (show e < c + 1 ∧ c + 1 ≤ e + n by omega), if_pos (show e < c ∧ c ≤ e + n by omega)]
    split_ifs with h1 h2 h2
    · simp
    · omega
    · nlinarith
    · nlinarith
  · split_ifs <;> first | omega | simp

lemma sum_row {s : Finset ℕ} (F1 F0 R1 R0 : ℕ → ℝ) (α β : ℝ)
    (h : ∀ q ∈ s, (F1 q - R1 q) * α ≤ (F0 q - R0 q) * β) :
    (∑ q ∈ s, F1 q - ∑ q ∈ s, R1 q) * α ≤ (∑ q ∈ s, F0 q - ∑ q ∈ s, R0 q) * β := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_le_sum h

/-- **Lemma B1** (validity): for strictly increasing shifts, non-negative weights and a
log-concave leg vector, `R ⊆ Q_Θ`.  (No gap condition is needed.) -/
theorem validityB (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n)
    {N r : ℕ} (hr : 1 ≤ r) {d : ℕ → ℕ} (hd : Incr d r) (hN : d (r - 1) + n ≤ N)
    {lam : ℕ → ℝ} (hlam : ∀ p, 0 ≤ lam p) :
    Rsum a N n d lam r ⊆ QZ a N n d lam r := by
  have hR : Rsum a N n d lam r = convexHull ℝ (∑ p ∈ range r, lam p • vsetA a N (d p) n) := by
    rw [convexHull_sum]; simp only [convexHull_smul]; rfl
  rw [hR]
  refine convexHull_min ?_ (convex_QZ a N n d lam r)
  intro x hx
  obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum _ _ _).mp hx
  have hg' : ∀ q ∈ range r, ∃ k, 1 ≤ k ∧ k ≤ n ∧ g q = lam q • ravA a N (d q) k := by
    intro q hq
    obtain ⟨v, ⟨k, hk, rfl⟩, hv⟩ := Set.mem_smul_set.mp (hg hq)
    exact ⟨k, hk.1, hk.2, hv.symm⟩
  have hdle : ∀ q, q < r → d q + n ≤ N := fun q hq => by
    have := hd.le (show q ≤ r - 1 by omega) (by omega); omega
  have hco : ∀ q ∈ range r, ∀ c, 0 ≤ co (g q) c := by
    intro q hq c
    obtain ⟨k, -, -, hk⟩ := hg' q hq
    rw [hk, co_smul]
    exact mul_nonneg (hlam q) (co_ravA_nonneg hpos _ _ _)
  -- the chain rows, for every window and every link `j ≥ 1`
  have hrow : ∀ p j, p < r → 1 ≤ j → j < n →
      (co (∑ q ∈ range r, g q) (d p + j + 1) - roof a n d lam r p (d p + j + 1)) * a j ≤
        (co (∑ q ∈ range r, g q) (d p + j) - roof a n d lam r p (d p + j)) * a (j + 1) := by
    intro p j hp hj hjn
    rw [co_sum, co_sum]
    unfold roof
    apply sum_row
    intro q hq
    have hqr := Finset.mem_range.mp hq
    obtain ⟨k, hk1, hkn, hk⟩ := hg' q hq
    rw [hk, co_smul, co_smul]
    have hpN := hdle p hp
    by_cases hpq : p < q
    · rw [if_pos hpq, if_pos hpq]
      have hdpq := hd.lt hpq hqr
      have hW := window_R hpos hlc (N := N) (e := d q) (k := k) (c := d p + j) hk1 hj (by omega)
        (by omega) (by omega) (by omega) (by omega)
      have := mul_le_mul_of_nonneg_left hW (hlam q)
      linarith
    · rw [if_neg hpq, if_neg hpq, sub_zero, sub_zero]
      have hdqp := hd.le (show q ≤ p by omega) hp
      have hW := window_L hpos hlc (N := N) (e := d q) (k := k) (c := d p + j) hkn hj (by omega)
        (by omega) (by omega)
      have := mul_le_mul_of_nonneg_left hW (hlam q)
      linarith
  refine ⟨?_, ?_, ?_, fun j hj hjn => hrow 0 j (by omega) hj hjn,
    fun p j _ hp hj hjn => hrow p j hp (by omega) hjn, ?_, ?_, ?_⟩
  · -- (Z), below
    intro c hc
    rw [co_sum]
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨k, -, -, hk⟩ := hg' q hq
    have := hd.le (Nat.zero_le q) (Finset.mem_range.mp hq)
    rw [hk, co_smul, co_ravA, if_neg (by omega), mul_zero]
  · -- (Z), above
    intro c hc
    rw [co_sum]
    apply Finset.sum_eq_zero
    intro q hq
    obtain ⟨k, -, hkn, hk⟩ := hg' q hq
    have := hd.le (show q ≤ r - 1 by have := Finset.mem_range.mp hq; omega) (by omega)
    rw [hk, co_smul, co_ravA, if_neg (by omega), mul_zero]
  · -- (E)
    rw [co_sum, Finset.sum_eq_single 0]
    · obtain ⟨k, hk1, hkn, hk⟩ := hg' 0 (Finset.mem_range.mpr (by omega))
      have := hdle 0 (by omega)
      rw [hk, co_smul, co_ravA, if_pos (by omega), show d 0 + 1 - d 0 = 1 by omega]
    · intro q hq hq0
      obtain ⟨k, -, -, hk⟩ := hg' q hq
      have := hd.lt (show 0 < q by omega) (Finset.mem_range.mp hq)
      rw [hk, co_smul, co_ravA, if_neg (by omega), mul_zero]
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  · -- (C)
    intro p hp
    rw [co_sum]
    have hmem : p + 1 ∈ range r := Finset.mem_range.mpr hp
    refine le_trans ?_ (Finset.single_le_sum (fun q hq => hco q hq _) hmem)
    obtain ⟨k, hk1, hkn, hk⟩ := hg' (p + 1) hmem
    have := hdle (p + 1) hp
    rw [hk, co_smul, co_ravA, if_pos (by omega), show d (p + 1) + 1 - d (p + 1) = 1 by omega]
  · -- (D)
    intro p hp
    rw [co_sum]
    unfold roof
    apply Finset.sum_le_sum
    intro q hq
    obtain ⟨k, -, hkn, hk⟩ := hg' q hq
    rw [hk, co_smul]
    by_cases hpq : p < q
    · rw [if_pos hpq]
      exact mul_le_mul_of_nonneg_left (co_ravA_le_Aw hpos hkn _) (hlam q)
    · rw [if_neg hpq]
      have := hd.le (show q ≤ p by omega) (by omega)
      rw [co_ravA, if_neg (by omega), mul_zero]
  · -- (F)
    rw [co_sum]
    exact Finset.sum_nonneg (fun q hq => hco q hq _)

/-! ## Completeness (Lemma B2, the peel) -/

lemma Rsum_succ (a : ℕ → ℝ) (N n : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r : ℕ) :
    Rsum a N n d lam (r + 1) =
      lam 0 • angle a N (d 0) n + Rsum a N n (fun p => d (p + 1)) (fun p => lam (p + 1)) r := by
  unfold Rsum; rw [Finset.sum_range_succ', add_comm]

/-- The windows `1, …, p` of the first roof: `S(p; c) = ∑_{0 < q ≤ p} lam q · Aw a n (d q) c`. -/
noncomputable def roofS (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r p c : ℕ) : ℝ :=
  ∑ q ∈ range r, if 0 < q ∧ q ≤ p then lam q * Aw a n (d q) c else 0

/-- (P1) of Lemma B2: `M(0; c) = S(p; c) + M(p; c)`. -/
lemma roof_zero_split (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r p c : ℕ) :
    roof a n d lam r 0 c = roofS a n d lam r p c + roof a n d lam r p c := by
  unfold roof roofS
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  split_ifs <;> first | omega | simp

lemma sub_min_self (u m : ℝ) : u - min u m = max 0 (u - m) := by
  rcases le_total u m with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]; ring
  · rw [min_eq_right h, max_eq_right (by linarith)]

/-- **Lemma B2** (the peel).  For `x ∈ Q_Θ(d; lam)` with `r + 1 ≥ 2` windows, the truncation
`w = min(x, M(0; ·))` on the first window (and `w = x` beyond it) satisfies the peeled system
`Q_Θ(d ∘ succ; lam ∘ succ)` with `r` windows — including its equation `w(d 1 + 1) = lam 1 · a 1`,
its support rows `w(c) = 0` for `c ≤ d 1` (the note's (ii)), and its first window's full chain
`j = 1, …, n−1` — while `y = x − w` lies in `lam 0 • shift^{d 0} ∠(a)`. -/
theorem peel (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n) (hn : 1 ≤ n)
    {N r : ℕ} (hr : 1 ≤ r) {d : ℕ → ℕ} (hd : Incr d (r + 1)) (hg : Gaps n d (r + 1))
    (hN : d r + n ≤ N) {lam : ℕ → ℝ} (hlam : ∀ p, 0 < lam p) {x : Fin N → ℝ}
    (hx : x ∈ QZ a N n d lam (r + 1)) :
    ∃ y w, x = y + w ∧ y ∈ lam 0 • angle a N (d 0) n ∧
      w ∈ QZ a N n (fun p => d (p + 1)) (fun p => lam (p + 1)) r := by
  obtain ⟨hZ1, hZ2, hE, hI0, hI, hC, hD, hF⟩ := hx
  rw [Nat.add_sub_cancel] at hZ2 hF
  have hlam0 : ∀ p, 0 ≤ lam p := fun p => (hlam p).le
  have hd01 : d 0 < d 1 := hd 0 (by omega)
  have hgap1 : d 1 < d 0 + n := hg 0 (by omega)
  have hdr : d 0 < d r := hd.lt (by omega) (by omega)
  have hdq1 : ∀ q, 1 ≤ q → q < r + 1 → d 1 ≤ d q := fun q hq hqr => hd.le hq hqr
  set e := d 0 with he
  set M0 := roof a n d lam (r + 1) 0 with hM0
  -- the first roof vanishes up to `d 1` and equals `lam 1 · a 1` at `d 1 + 1`
  have hM0_le : ∀ c, c ≤ d 1 → M0 c = 0 := fun c hc =>
    roof_eq_zero_of_le (fun q hq hqr => le_trans hc (hdq1 q (by omega) hqr))
  have hM0_d1 : M0 (d 1 + 1) = lam 1 * a 1 := by
    simp only [hM0, roof]
    rw [Finset.sum_eq_single 1]
    · rw [if_pos (by omega), Aw_of_in (by omega) (by omega), show d 1 + 1 - d 1 = 1 by omega]
    · intro q hq hq1
      split_ifs with h
      · rw [Aw_of_le (by have := hd.lt (show 1 < q by omega) (Finset.mem_range.mp hq); omega),
          mul_zero]
      · rfl
    · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
  have hM0_nn : ∀ c, 0 ≤ M0 c := fun c => roof_nonneg hpos hlam0 _ _ _
  -- `G = x − M(0; ·)`: non-negative on `(e, d 1 + 1]`
  have hGd1 : 0 ≤ co x (d 1 + 1) - M0 (d 1 + 1) := by
    rw [hM0_d1]; linarith [hC 0 (by omega)]
  have hGnn : ∀ m, m ≤ d 1 - e → 0 ≤ co x (d 1 + 1 - m) - M0 (d 1 + 1 - m) := by
    intro m
    induction m with
    | zero => intro _; simpa using hGd1
    | succ m ih =>
      intro hm
      have h1 := ih (by omega)
      have hch := hI0 (d 1 - m - e) (by omega) (by omega)
      rw [show e + (d 1 - m - e) + 1 = d 1 + 1 - m by omega,
        show e + (d 1 - m - e) = d 1 + 1 - (m + 1) by omega] at hch
      have := mul_nonneg h1 (hpos (d 1 - m - e)).le
      have hp := hpos (d 1 - m - e + 1)
      by_contra hneg
      push_neg at hneg
      nlinarith
  have hxnn : ∀ c, e < c → c ≤ d 1 → 0 ≤ co x c := by
    intro c hc1 hc2
    have := hGnn (d 1 + 1 - c) (by omega)
    rw [show d 1 + 1 - (d 1 + 1 - c) = c by omega, hM0_le c hc2, sub_zero] at this
    exact this
  -- the truncation
  set wf : ℕ → ℝ := fun c => if c ≤ e + n then min (co x c) (M0 c) else co x c with hwf
  set w : Fin N → ℝ := mk N wf with hwdef
  have hw : ∀ c, co w c = wf c := by
    intro c
    by_cases h0 : c = 0
    · subst h0
      rw [co_eq_zero _ (Or.inl rfl)]
      simp only [hwf, if_pos (Nat.zero_le _), co_eq_zero x (c := 0) (Or.inl rfl), hM0_le 0 (Nat.zero_le _),
        min_self]
    by_cases hcN : c ≤ N
    · exact co_mk _ (by omega) hcN
    · rw [co_eq_zero w (Or.inr (by omega))]
      simp only [hwf, if_neg (show ¬ c ≤ e + n by omega), co_eq_zero x (c := c) (Or.inr (by omega))]
  have hw_in : ∀ c, c ≤ e + n → co w c = min (co x c) (M0 c) := fun c hc => by
    rw [hw]; simp only [hwf, if_pos hc]
  have hw_out : ∀ c, e + n < c → co w c = co x c := fun c hc => by
    rw [hw]; simp only [hwf, if_neg (show ¬ c ≤ e + n by omega)]
  refine ⟨x - w, w, (sub_add_cancel x w).symm, ?_, ?_⟩
  · -- (i): `y = x − w ∈ lam 0 • shift^e ∠(a)`
    have hy : ∀ c, co (x - w) c = if c ≤ e + n then max 0 (co x c - M0 c) else 0 := by
      intro c
      rw [co_sub]
      split_ifs with hc
      · rw [hw_in c hc, sub_min_self]
      · rw [hw_out c (by omega), sub_self]
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (hlam 0).ne', chain_hull_eq a hpos hn (by omega)]
    have hli := inv_nonneg.mpr (hlam0 0)
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro c hc
      rw [co_smul, hy, if_pos (by omega), hZ1 c hc, hM0_le c (by omega)]
      simp
    · intro c hc
      rw [co_smul, hy, if_neg (by omega), mul_zero]
    · rw [co_smul, hy, if_pos (by omega), hE, hM0_le _ (by omega), sub_zero,
        max_eq_right (mul_nonneg (hlam0 0) (hpos 1).le), ← mul_assoc,
        inv_mul_cancel₀ (hlam 0).ne', one_mul]
    · intro j hj hjn
      rw [co_smul, co_smul, hy, hy, if_pos (by omega), if_pos (by omega)]
      have hch := hI0 j hj hjn
      have hm : max 0 (co x (e + j + 1) - M0 (e + j + 1)) * a j ≤
          max 0 (co x (e + j) - M0 (e + j)) * a (j + 1) := by
        have := hpos j
        have := hpos (j + 1)
        rcases le_total (co x (e + j + 1) - M0 (e + j + 1)) 0 with h | h
        · rw [max_eq_left h, zero_mul]; positivity
        · rw [max_eq_right h]
          exact le_trans hch (mul_le_mul_of_nonneg_right (le_max_right _ _) this.le)
      have := mul_le_mul_of_nonneg_left hm hli
      linarith
    · rw [co_smul, hy, if_pos le_rfl]
      exact mul_nonneg hli (le_max_left _ _)
  · -- (iii): `w` satisfies the peeled system
    -- (P3): the partial roof is a chain
    have hP3 : ∀ P j, P < r + 1 → 1 ≤ j → j + 1 ≤ n → d P + j + 1 ≤ e + n + 1 →
        roofS a n d lam (r + 1) P (d P + j + 1) * a j ≤
          roofS a n d lam (r + 1) P (d P + j) * a (j + 1) := by
      intro P j hP hj hjn hc
      unfold roofS
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro q hq
      split_ifs with hq'
      · have hqP := hd.le hq'.2 hP
        have hq1 := hdq1 q hq'.1 (by have := Finset.mem_range.mp hq; omega)
        rw [Aw_of_in (by omega) (by omega), Aw_of_in (by omega) (by omega),
          show d P + j + 1 - d q = d P + j - d q + 1 by omega]
        have key := hlc j (d P + j - d q) hj (by omega) (by omega)
        have := mul_le_mul_of_nonneg_left key (hlam0 q)
        linarith
      · simp
    -- the core link argument, for an original window `P ≥ 1`
    have hcore : ∀ P j, 1 ≤ P → P < r + 1 → 1 ≤ j → j + 1 ≤ n →
        ((d P + j ≤ e + n ∧ roofS a n d lam (r + 1) P (d P + j) ≤
            co x (d P + j) - roof a n d lam (r + 1) P (d P + j)) ∨
          (co x (d P + j + 1) - roof a n d lam (r + 1) P (d P + j + 1)) * a j ≤
            (co x (d P + j) - roof a n d lam (r + 1) P (d P + j)) * a (j + 1)) →
        (co w (d P + j + 1) - roof a n d lam (r + 1) P (d P + j + 1)) * a j ≤
          (co w (d P + j) - roof a n d lam (r + 1) P (d P + j)) * a (j + 1) := by
      intro P j hP1 hP hj hjn halt
      have haj := (hpos j).le
      have haj1 := (hpos (j + 1)).le
      have hsplit := fun c => roof_zero_split a n d lam (r + 1) P c
      by_cases hc : d P + j ≤ e + n
      · have hfc : co w (d P + j) - roof a n d lam (r + 1) P (d P + j) =
            min (co x (d P + j) - roof a n d lam (r + 1) P (d P + j))
              (roofS a n d lam (r + 1) P (d P + j)) := by
          rw [hw_in _ hc, hM0, hsplit, ← min_sub_sub_right, add_sub_cancel_right]
        have hf1 : co w (d P + j + 1) - roof a n d lam (r + 1) P (d P + j + 1) ≤
              co x (d P + j + 1) - roof a n d lam (r + 1) P (d P + j + 1) ∧
            co w (d P + j + 1) - roof a n d lam (r + 1) P (d P + j + 1) ≤
              roofS a n d lam (r + 1) P (d P + j + 1) := by
          by_cases hc1 : d P + j + 1 ≤ e + n
          · rw [hw_in _ hc1, hM0, hsplit, ← min_sub_sub_right, add_sub_cancel_right]
            exact ⟨min_le_left _ _, min_le_right _ _⟩
          · rw [hw_out _ (by omega)]
            refine ⟨le_rfl, ?_⟩
            have hD0 := hD 0 (by omega)
            rw [show d 0 + n + 1 = d P + j + 1 by omega, hsplit] at hD0
            linarith
        have hS := hP3 P j hP hj hjn (by omega)
        rw [hfc]
        rcases halt with ⟨-, halt⟩ | halt
        · rw [min_eq_right halt]
          exact le_trans (mul_le_mul_of_nonneg_right hf1.2 haj) hS
        · rw [min_mul_of_nonneg _ _ haj1]
          exact le_min (le_trans (mul_le_mul_of_nonneg_right hf1.1 haj) halt)
            (le_trans (mul_le_mul_of_nonneg_right hf1.2 haj) hS)
      · rw [hw_out _ (by omega), hw_out _ (by omega)]
        rcases halt with ⟨h, -⟩ | halt
        · exact absurd h hc
        · exact halt
    have hroof1 : roof a n d lam (r + 1) 1 (d 1 + 1) = 0 :=
      roof_eq_zero_of_le (fun q hq hqr => by have := hd.lt hq hqr; omega)
    have hS1 : roofS a n d lam (r + 1) 1 (d 1 + 1) = lam 1 * a 1 := by
      unfold roofS
      rw [Finset.sum_eq_single 1]
      · rw [if_pos (by omega), Aw_of_in (by omega) (by omega), show d 1 + 1 - d 1 = 1 by omega]
      · intro q _ hq1
        rw [if_neg (by omega)]
      · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- (Z), below: the note's (ii)
      intro c hc
      simp only [zero_add] at hc
      rw [hw_in c (by omega), hM0_le c hc]
      by_cases hce : c ≤ e
      · rw [hZ1 c hce, min_self]
      · exact min_eq_right (hxnn c (by omega) hc)
    · -- (Z), above
      intro c hc
      simp only [Nat.sub_add_cancel hr] at hc
      rw [hw_out c (by omega)]
      exact hZ2 c hc
    · -- (E′): `w(d 1 + 1) = lam 1 · a 1`
      simp only [zero_add]
      rw [hw_in _ (by omega), hM0_d1]
      exact min_eq_right (hC 0 (by omega))
    · -- (I′; 0): the first peeled window, all links `j = 1, …, n − 1`
      intro j hj hjn
      simp only [zero_add, roof_tail]
      apply hcore 1 j le_rfl (by omega) hj (by omega)
      rcases Nat.lt_or_ge j 2 with hj2 | hj2
      · obtain rfl : j = 1 := by omega
        left
        refine ⟨by omega, ?_⟩
        rw [hS1, hroof1, sub_zero]
        exact hC 0 (by omega)
      · right; exact hI 1 j (by omega) (by omega) hj2 hjn
    · -- (I′; p), `p ≥ 1`
      intro p j hp0 hp hj hjn
      simp only [roof_tail]
      exact hcore (p + 1) j (by omega) (by omega) (by omega) (by omega)
        (Or.inr (hI (p + 1) j (by omega) (by omega) hj hjn))
    · -- (C′)
      intro p hp
      simp only
      by_cases hc : d (p + 1 + 1) + 1 ≤ e + n
      · rw [hw_in _ hc]
        refine le_min (hC (p + 1) (by omega)) ?_
        rw [hM0]
        unfold roof
        have hmem : p + 1 + 1 ∈ range (r + 1) := Finset.mem_range.mpr (by omega)
        refine le_trans ?_ (Finset.single_le_sum (fun q _ => ?_) hmem)
        · rw [if_pos (by omega), Aw_of_in (by omega) (by have := hd (p + 1) (by omega); omega),
            show d (p + 1 + 1) + 1 - d (p + 1 + 1) = 1 by omega]
        · split_ifs
          · exact mul_nonneg (hlam0 q) (Aw_nonneg hpos _ _ _)
          · exact le_rfl
      · rw [hw_out _ (by omega)]
        exact hC (p + 1) (by omega)
    · -- (D′)
      intro p hp
      simp only [roof_tail]
      have := hd.le (show 1 ≤ p + 1 by omega) (show p + 1 < r + 1 by omega)
      rw [hw_out _ (by omega)]
      exact hD (p + 1) (by omega)
    · -- (F′)
      simp only [Nat.sub_add_cancel hr]
      rw [hw_out _ (by omega)]
      exact hF

/-- **Completeness** (`Q_Θ ⊆ R`), by induction on the number of windows, the peel being the
step: strictly increasing shifts, all gaps `≤ n − 1`, positive weights, log-concave `a`. -/
theorem completenessB (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n)
    (hn : 1 ≤ n) {N : ℕ} :
    ∀ r, 1 ≤ r → ∀ (d : ℕ → ℕ) (lam : ℕ → ℝ), Incr d r → Gaps n d r → d (r - 1) + n ≤ N →
      (∀ p, 0 < lam p) → QZ a N n d lam r ⊆ Rsum a N n d lam r := by
  intro r hr
  induction r, hr using Nat.le_induction with
  | base =>
    intro d lam _ _ hN hlam x hx
    obtain ⟨hZ1, hZ2, hE, hI0, -, -, -, hF⟩ := hx
    simp only [Nat.sub_self] at hZ2 hN hF
    have hroof : ∀ c, roof a n d lam 1 0 c = 0 := fun c => by simp [roof]
    unfold Rsum
    rw [Finset.sum_range_one, Set.mem_smul_set_iff_inv_smul_mem₀ (hlam 0).ne',
      chain_hull_eq a hpos hn hN]
    have hli := inv_nonneg.mpr (hlam 0).le
    refine ⟨fun c hc => by rw [co_smul, hZ1 c hc, mul_zero],
      fun c hc => by rw [co_smul, hZ2 c hc, mul_zero], ?_, ?_, ?_⟩
    · rw [co_smul, hE, ← mul_assoc, inv_mul_cancel₀ (hlam 0).ne', one_mul]
    · intro j hj hjn
      have h := hI0 j hj hjn
      rw [hroof, hroof, sub_zero, sub_zero] at h
      rw [co_smul, co_smul]
      have := mul_le_mul_of_nonneg_left h hli
      linarith
    · rw [co_smul]; exact mul_nonneg hli hF
  | succ r hr ih =>
    intro d lam hd hg hN hlam x hx
    simp only [Nat.add_sub_cancel] at hN
    obtain ⟨y, w, rfl, hy, hw⟩ := peel a hpos hlc hn hr hd hg hN hlam hx
    rw [Rsum_succ]
    refine Set.add_mem_add hy (ih _ _ hd.tail hg.tail ?_ (fun p => hlam (p + 1)) hw)
    simp only [Nat.sub_add_cancel hr]
    exact hN

/-! ## Theorem B -/

/-- **Theorem B** (`Q_Θ = R`), with free first shift and ambient dimension: for a positive weakly
log-concave leg vector, `r ≥ 1` windows with strictly increasing shifts and all gaps `≤ n − 1`, and
positive weights, `∑_p lam p • shift^{d p} ∠(a)` is cut out by the weighted Θ-form system. -/
theorem theoremB (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n) (hn : 1 ≤ n)
    {N r : ℕ} (hr : 1 ≤ r) {d : ℕ → ℕ} (hd : Incr d r) (hg : Gaps n d r)
    (hN : d (r - 1) + n ≤ N) {lam : ℕ → ℝ} (hlam : ∀ p, 0 < lam p) :
    Rsum a N n d lam r = QZ a N n d lam r :=
  Set.Subset.antisymm (validityB a hpos hlc hr hd hN (fun p => (hlam p).le))
    (completenessB a hpos hlc hn r hr d lam hd hg hN hlam)

/-- The Θ-form exactly as the note prints it: first shift `0`, ambient `ℝ^N`, `N = d(r−1) + n`;
no support rows. -/
def QTheta (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r : ℕ) : Set (Fin (d (r - 1) + n) → ℝ) :=
  {x | co x 1 = lam 0 * a 1 ∧
    (∀ j, 1 ≤ j → j < n →
      (co x (j + 1) - roof a n d lam r 0 (j + 1)) * a j ≤
        (co x j - roof a n d lam r 0 j) * a (j + 1)) ∧
    (∀ p j, 0 < p → p < r → 2 ≤ j → j < n →
      (co x (d p + j + 1) - roof a n d lam r p (d p + j + 1)) * a j ≤
        (co x (d p + j) - roof a n d lam r p (d p + j)) * a (j + 1)) ∧
    (∀ p, p + 1 < r → lam (p + 1) * a 1 ≤ co x (d (p + 1) + 1)) ∧
    (∀ p, p + 1 < r → co x (d p + n + 1) ≤ roof a n d lam r p (d p + n + 1)) ∧
    0 ≤ co x (d (r - 1) + n)}

lemma QZ_eq_QTheta (a : ℕ → ℝ) (n : ℕ) {d : ℕ → ℕ} (lam : ℕ → ℝ) (r : ℕ) (h0 : d 0 = 0) :
    QZ a (d (r - 1) + n) n d lam r = QTheta a n d lam r := by
  ext x
  simp only [QZ, QTheta, Set.mem_setOf_eq, h0, zero_add]
  constructor
  · rintro ⟨-, -, h⟩; exact h
  · intro h
    refine ⟨fun c hc => co_eq_zero x (Or.inl (by omega)),
      fun c hc => co_eq_zero x (Or.inr hc), h⟩

/-- **Theorem B**, in the note's printed form (`d 0 = 0`, `N = d(r−1) + n`). -/
theorem theoremB_theta (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n)
    (hn : 1 ≤ n) {r : ℕ} (hr : 1 ≤ r) {d : ℕ → ℕ} (h0 : d 0 = 0) (hd : Incr d r)
    (hg : Gaps n d r) {lam : ℕ → ℝ} (hlam : ∀ p, 0 < lam p) :
    Rsum a (d (r - 1) + n) n d lam r = QTheta a n d lam r := by
  rw [← QZ_eq_QTheta a n lam r h0]
  exact theoremB a hpos hlc hn hr hd hg le_rfl hlam

lemma Rsum_one (a : ℕ → ℝ) (N n : ℕ) (d : ℕ → ℕ) (r : ℕ) :
    Rsum a N n d (fun _ => 1) r = ∑ p ∈ range r, angle a N (d p) n := by
  simp only [Rsum, one_smul]

/-- **Theorem B for the Kozlov leg vector `κ⃗(n)`, every rank**: for distinct shifts
`0 = d 0 < d 1 < ⋯ < d (r−1)` with all gaps `≤ n − 1`,
`RA(κ⃗(n); d⃗) = ∑_p shift^{d p} ∠(κ⃗(n))` is the Θ-form with unit weights. -/
theorem theoremB_kozlov {n r : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) {d : ℕ → ℕ} (h0 : d 0 = 0)
    (hd : Incr d r) (hg : Gaps n d r) :
    ∑ p ∈ range r, angle (kozLeg n) (d (r - 1) + n) (d p) n =
      QTheta (kozLeg n) n d (fun _ => 1) r := by
  rw [← Rsum_one]
  exact theoremB_theta _ (kozLeg_pos n) (kozLeg_logConcave n) hn hr h0 hd hg (fun _ => one_pos)

/-- Consistency with `RankTwo.lean`: at `r = 2`, unit weights, shifts `(0, dd)`, the rank-`r`
system coincides with Theorem A's Θ-form `Qsys a n dd 2` (both equal `R`). -/
theorem QZ_rank_two (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n) {dd : ℕ}
    (hd : 1 ≤ dd) (hdn : dd < n) :
    QZ a (n + dd) n (fun p => if p = 0 then 0 else dd) (fun _ => 1) 2 = Qsys a n dd 2 := by
  rw [← theoremB a hpos hlc (by omega) (by norm_num : 1 ≤ 2) (fun p hp => by
      obtain rfl : p = 0 := by omega
      simp; omega)
    (fun p hp => by obtain rfl : p = 0 := by omega
                    simp; omega)
    (by simp; omega) (fun _ => one_pos), ← theoremA_theta a hpos hlc hd hdn]
  simp [Rsum, Finset.sum_range_succ]

end Facets
end ExteriorConvex
