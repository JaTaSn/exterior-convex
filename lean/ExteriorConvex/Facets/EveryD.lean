/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)

# Corollary `cor-facets-every-d` (H-description half) and `cor-koz-hdesc` for every `d⃗`

Article 3, Corollary `cor-facets-every-d`: for arbitrary shifts, an H-description of
`RA(a; d⃗) = ∑_p shift^{d_p} ∠(a)` is obtained by merging equal shifts into one summand weighted
by the multiplicity, cutting the distinct shifts into maximal runs (consecutive gaps `≤ n − 1`),
writing the Θ-form of Theorem `thm-theta` for each run in its own coordinates, and adding `x_c = 0`
on every coordinate covered by no window.  Then Corollary `cor-koz-hdesc` for general `d⃗`.

The paper's three proof steps, each a Lean statement:

* **Merging**: `sum_const_convex` (`∑_{p ∈ t} A = |t| • A`, `A` convex nonempty) and
  `sum_angle_eq_Rsum`: `∑_{p<r} ∠(d p) = Rsum a N n M.e M.wt M.s`, the weighted sum of
  `ThetaForm.lean` over the distinct shifts `M.e 0 < ⋯ < M.e (M.s − 1)` with weight
  `M.wt i = #{p : d p = M.e i}` (`mult`, `KozBridge.lean`).  `Merge d r` packages the distinct
  values; `Merge.canon` builds them (sorted image of `d`).
* **Runs and blocks**: `Runs n e s` is a cut `[β b, β(b+1))`, `b < k`, with inner gaps `≤ n − 1`
  and gaps between runs `≥ n` (this determines the cut: it is the cut into maximal runs);
  `Runs.nonempty` builds one.  No product-of-polytopes theory: `mem_add_iff_msk` /
  `mem_sum_iff_msk` show directly that a Minkowski sum of sets living on disjoint coordinate
  blocks decomposes blockwise (`msk W x` keeps the coordinates in `W`).
  `Rsum_eq_runs`: for distinct shifts with *arbitrary* gaps, `Rsum = {x | every run's rows hold ∧
  x_c = 0 off all windows}`; each run goes through `theoremB` (`ThetaForm.lean`) in the global
  ambient space, whose support rows (Z) are exactly what makes the blocks disjoint.
* **The corollary**: `cor_facets_every_d`: `∑_{p<r} ∠(a; d p) = EverySys a N n d r M R`, where
  `EverySys` is "for each run `b`, `x ∈ QRows` of run `b`" plus "`x_c = 0` whenever no
  `[d p + 1, d p + n]` contains `c`".  `QRows` is `ThetaForm`'s `QZ` minus its support rows, i.e.
  the Θ-form rows (E), (I;p), (C;p), (D;p), (F) of the run, read in the global coordinates.
  `QRows_iff_QTheta` shows this *is* the run's `QTheta` in its own coordinates (window re-indexed
  from `1` by `loc`, shifts `d q − d_first`), and `mem_EverySys_iff_local` restates
  `EverySys` that way, which is the corollary as printed.
* **`cor-koz-hdesc`, general `d⃗`**: `koz_hdesc_every_d` (via `mem_koz_iff`): `f ∈ Koz(n; d⃗)` iff
  `f₀ = #{p : d_p = 0}` and `(f_c − #{p : d_p = c})_{c=1..N}` (`= π(f) − ∑_{p:d_p≥1} e_{d_p}`) is
  in `EverySys (κ⃗(n)) …`; `koz_hdesc_every_d_local` with each run's `QTheta`;
  `koz_hdesc_every_d'` with the canonical merge and cut, so with nothing to supply.

**Relation to the printed statement.**
* Hypotheses are *weaker* than the paper's: the leg vector need only be positive and weakly
  log-concave (`LogConcaveOn`; the paper's strictness is only for the facet count), `n ≥ 1`, and
  the shifts are arbitrary (unsorted, `d 0 = 0` not needed), in any ambient `N ≥ d p + n`; the
  paper's `0 = d_1 ≤ ⋯ ≤ d_r`, `N = d_r + n` is a special case.  For `d 0 = 0` the "uncovered"
  zeros include nothing below the first window; if `N > max d + n` they include the tail.
* The run data (`Merge`, `Runs`) are hypotheses-as-structures; both are unique up to the
  representation and both exist (`Merge.canon`, `Runs.nonempty`), so the system is the paper's.
* **Not formalised**: the facet count `ns` and irredundancy (Mathlib has no face dimensions); that
  half stays the paper's proof.  The weights of a run are `R.wt M.wt b q = M.wt (β b + q)` and
  `QRows` reads them only below the run length.

Sanity check before formalising (Sage, exact polyhedra): the system (merged, cut into runs, rows in
global coordinates, zeros off the windows) equals `RA(a; d⃗)` in 469 cases: `n = 2, 3, 4`,
`r ≤ 3`, all consecutive gaps `0..n+2` (ties, `n − 1`, `n`, `n + 1`), legs `κ⃗(n)`, `𝟙`,
`(3,3,1)`, `(2,3,2)`, `(5,7,6,2)`, ambient `N = d_r + n` and `N = d_r + n + 1`; no mismatch.
-/
import Mathlib
import ExteriorConvex.Facets.KozBridge

namespace ExteriorConvex
namespace EveryD

open Finset Pointwise Facets KozBridge

variable {N : ℕ}

/-! ## Coordinate masks and blockwise Minkowski sums -/

/-- Keep the manuscript coordinates `c` with `W c`, zero the rest. -/
def msk (W : ℕ → Prop) [DecidablePred W] (x : Fin N → ℝ) : Fin N → ℝ :=
  fun i => if W (i.val + 1) then x i else 0

lemma co_msk (W : ℕ → Prop) [DecidablePred W] (x : Fin N → ℝ) (c : ℕ) :
    co (msk W x) c = if W c then co x c else 0 := by
  by_cases h : 1 ≤ c ∧ c ≤ N
  · rw [co_of _ h.1 h.2, co_of _ h.1 h.2]
    simp only [msk, Nat.sub_add_cancel h.1]
  · rw [co_eq_zero _ (by omega), co_eq_zero _ (by omega)]
    simp

/-- **Two blocks.**  If `A` lives on the coordinates outside `W` and `B` on those inside `W`, then
`x ∈ A + B` iff the outside part of `x` is in `A` and the inside part is in `B`. -/
theorem mem_add_iff_msk {W : ℕ → Prop} [DecidablePred W] {A B : Set (Fin N → ℝ)}
    (hA : ∀ y ∈ A, ∀ c, W c → co y c = 0) (hB : ∀ y ∈ B, ∀ c, ¬ W c → co y c = 0)
    (x : Fin N → ℝ) :
    x ∈ A + B ↔ msk (fun c => ¬ W c) x ∈ A ∧ msk W x ∈ B := by
  constructor
  · rintro ⟨u, hu, v, hv, rfl⟩
    have h1 : msk (fun c => ¬ W c) (u + v) = u := ext_co fun c _ _ => by
      rw [co_msk, co_add]
      by_cases hc : W c
      · simp [hc, hA u hu c hc]
      · simp [hc, hB v hv c hc]
    have h2 : msk W (u + v) = v := ext_co fun c _ _ => by
      rw [co_msk, co_add]
      by_cases hc : W c
      · simp [hc, hA u hu c hc]
      · simp [hc, hB v hv c hc]
    rw [h1, h2]
    exact ⟨hu, hv⟩
  · rintro ⟨hu, hv⟩
    refine ⟨_, hu, _, hv, ext_co fun c _ _ => ?_⟩
    rw [co_add, co_msk, co_msk]
    by_cases hc : W c <;> simp [hc]

/-- A sum of sets each vanishing at `c` vanishes at `c`. -/
lemma co_eq_zero_of_mem_sum {k : ℕ} {S : ℕ → Set (Fin N → ℝ)} {c : ℕ}
    (h : ∀ b < k, ∀ y ∈ S b, co y c = 0) {x : Fin N → ℝ} (hx : x ∈ ∑ b ∈ range k, S b) :
    co x c = 0 := by
  rw [Set.mem_finsetSum] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  rw [co_sum]
  exact Finset.sum_eq_zero fun b hb => h b (Finset.mem_range.mp hb) _ (hg hb)

/-- **Finitely many blocks.**  If `S b` (`b < k`) lives on the coordinate block `W b` and the blocks
are pairwise disjoint, then `x ∈ ∑_b S b` iff each block of `x` is in its set and `x` vanishes on
the coordinates covered by no block. -/
theorem mem_sum_iff_msk (k : ℕ) (W : ℕ → ℕ → Prop) [∀ b, DecidablePred (W b)]
    (S : ℕ → Set (Fin N → ℝ)) (hS : ∀ b < k, ∀ y ∈ S b, ∀ c, ¬ W b c → co y c = 0)
    (hdisj : ∀ b b' c, b < b' → b' < k → W b c → W b' c → False) (x : Fin N → ℝ) :
    x ∈ ∑ b ∈ range k, S b ↔
      (∀ b < k, msk (W b) x ∈ S b) ∧ ∀ c, (∀ b < k, ¬ W b c) → co x c = 0 := by
  induction k generalizing x with
  | zero =>
      simp only [Finset.range_zero, Finset.sum_empty, Set.mem_zero, Nat.not_lt_zero,
        IsEmpty.forall_iff, implies_true, true_and]
      exact ⟨fun h c _ => by rw [h]; unfold co; split_ifs <;> rfl,
        fun h => ext_co fun c _ _ => by rw [h c trivial]; unfold co; split_ifs <;> rfl⟩
  | succ k ih =>
      have hS' : ∀ b < k, ∀ y ∈ S b, ∀ c, ¬ W b c → co y c = 0 :=
        fun b hb => hS b (by omega)
      have hdisj' : ∀ b b' c, b < b' → b' < k → W b c → W b' c → False :=
        fun b b' c h1 h2 => hdisj b b' c h1 (by omega)
      rw [Finset.sum_range_succ,
        mem_add_iff_msk (W := W k) (fun y hy c hc => co_eq_zero_of_mem_sum
          (fun b hb y' hy' => hS b (by omega) y' hy' c (fun hb' => hdisj b k c hb (by omega) hb' hc))
          hy) (hS k (by omega)), ih hS' hdisj']
      have hmm : ∀ b < k, msk (W b) (msk (fun c => ¬ W k c) x) = msk (W b) x := fun b hb =>
        ext_co fun c _ _ => by
          rw [co_msk, co_msk, co_msk]
          by_cases hc : W b c
          · simp only [hc, if_true]
            by_cases hk : W k c
            · exact (hdisj b k c hb (by omega) hc hk).elim
            · simp [hk]
          · simp [hc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨fun b hb => ?_, fun c hc => ?_⟩
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
          · rw [← hmm b hb]; exact h1 b hb
          · exact h3
        · have := h2 c (fun b hb => hc b (by omega))
          rw [co_msk, if_pos (hc k (by omega))] at this
          exact this
      · rintro ⟨h1, h2⟩
        refine ⟨⟨fun b hb => ?_, fun c hc => ?_⟩, h1 k (by omega)⟩
        · rw [hmm b hb]; exact h1 b (by omega)
        · rw [co_msk]
          by_cases hk : W k c
          · simp [hk]
          · rw [if_pos hk]
            exact h2 c fun b hb => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
              · exact hc b hb
              · exact hk

/-! ## The Θ-form of one run, read in the global coordinates -/

/-- The Θ-form rows of `QZ` (Theorem `thm-theta`'s (E), (I;p), (C;p), (D;p), (F)) *without* the
support rows (Z): the system of one run, in the ambient coordinates.  Every row reads only
coordinates in the run's window `[d 0 + 1, d(r−1) + n]` (`QRows_congr`). -/
def QRows (a : ℕ → ℝ) (N n : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r : ℕ) : Set (Fin N → ℝ) :=
  {x | co x (d 0 + 1) = lam 0 * a 1 ∧
    (∀ j, 1 ≤ j → j < n →
      (co x (d 0 + j + 1) - roof a n d lam r 0 (d 0 + j + 1)) * a j ≤
        (co x (d 0 + j) - roof a n d lam r 0 (d 0 + j)) * a (j + 1)) ∧
    (∀ p j, 0 < p → p < r → 2 ≤ j → j < n →
      (co x (d p + j + 1) - roof a n d lam r p (d p + j + 1)) * a j ≤
        (co x (d p + j) - roof a n d lam r p (d p + j)) * a (j + 1)) ∧
    (∀ p, p + 1 < r → lam (p + 1) * a 1 ≤ co x (d (p + 1) + 1)) ∧
    (∀ p, p + 1 < r → co x (d p + n + 1) ≤ roof a n d lam r p (d p + n + 1)) ∧
    0 ≤ co x (d (r - 1) + n)}

lemma mem_QZ_iff (a : ℕ → ℝ) (N n : ℕ) (d : ℕ → ℕ) (lam : ℕ → ℝ) (r : ℕ) (x : Fin N → ℝ) :
    x ∈ QZ a N n d lam r ↔ (∀ c, c ≤ d 0 → co x c = 0) ∧ (∀ c, d (r - 1) + n < c → co x c = 0) ∧
      x ∈ QRows a N n d lam r := Iff.rfl

/-- The run's window `[d 0 + 1, d(r−1) + n]`. -/
def Win (n : ℕ) (d : ℕ → ℕ) (r : ℕ) (c : ℕ) : Prop := d 0 < c ∧ c ≤ d (r - 1) + n

instance (n : ℕ) (d : ℕ → ℕ) (r : ℕ) : DecidablePred (Win n d r) :=
  fun c => inferInstanceAs (Decidable (d 0 < c ∧ c ≤ d (r - 1) + n))

lemma QRows_of_agree {a : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) {d : ℕ → ℕ} {lam : ℕ → ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hd : Incr d r) {x y : Fin N → ℝ} (hxy : ∀ c, Win n d r c → co x c = co y c)
    (hx : x ∈ QRows a N n d lam r) : y ∈ QRows a N n d lam r := by
  have hle : ∀ p, p < r → d 0 ≤ d p ∧ d p ≤ d (r - 1) := fun p hp =>
    ⟨hd.le (Nat.zero_le p) hp, hd.le (by omega) (by omega)⟩
  have hsucc : ∀ p, p + 1 < r → d p + 1 ≤ d (p + 1) := fun p hp => hd p hp
  obtain ⟨hE, hI0, hI, hC, hD, hF⟩ := hx
  have h0 := hle 0 (by omega)
  refine ⟨?_, fun j hj hjn => ?_, fun p j hp hpr hj hjn => ?_, fun p hp => ?_, fun p hp => ?_, ?_⟩
  · rw [← hxy _ ⟨by omega, by omega⟩]; exact hE
  · rw [← hxy (d 0 + j + 1) ⟨by omega, by omega⟩, ← hxy (d 0 + j) ⟨by omega, by omega⟩]
    exact hI0 j hj hjn
  · have := hle p hpr
    have := hle 0 (by omega)
    have := hd.lt hp hpr
    rw [← hxy (d p + j + 1) ⟨by omega, by omega⟩, ← hxy (d p + j) ⟨by omega, by omega⟩]
    exact hI p j hp hpr hj hjn
  · have := hle (p + 1) hp
    have := hsucc p hp
    rw [← hxy _ ⟨by omega, by omega⟩]; exact hC p hp
  · have := hle (p + 1) hp
    have := hle p (by omega)
    have := hsucc p hp
    rw [← hxy _ ⟨by omega, by omega⟩]; exact hD p hp
  · have := hle (r - 1) (by omega)
    rw [← hxy _ ⟨by omega, by omega⟩]; exact hF

/-- The rows only read the run's window. -/
lemma QRows_congr {a : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) {d : ℕ → ℕ} {lam : ℕ → ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hd : Incr d r) {x y : Fin N → ℝ} (hxy : ∀ c, Win n d r c → co x c = co y c) :
    x ∈ QRows a N n d lam r ↔ y ∈ QRows a N n d lam r :=
  ⟨QRows_of_agree hn hr hd hxy, QRows_of_agree hn hr hd fun c hc => (hxy c hc).symm⟩

/-- Masking to the window turns `QZ` (rows + support) into the bare rows. -/
lemma msk_mem_QZ_iff {a : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) {d : ℕ → ℕ} {lam : ℕ → ℝ} {r : ℕ}
    (hr : 1 ≤ r) (hd : Incr d r) (x : Fin N → ℝ) :
    msk (Win n d r) x ∈ QZ a N n d lam r ↔ x ∈ QRows a N n d lam r := by
  rw [mem_QZ_iff, QRows_congr hn hr hd (y := x) fun c hc => by rw [co_msk, if_pos hc]]
  refine ⟨fun h => h.2.2, fun h => ⟨fun c hc => ?_, fun c hc => ?_, h⟩⟩
  · rw [co_msk, if_neg (fun h' : Win n d r c => by unfold Win at h'; omega)]
  · rw [co_msk, if_neg (fun h' : Win n d r c => by unfold Win at h'; omega)]

/-- Weights are read only below `r`. -/
lemma roof_congr {a : ℕ → ℝ} {n : ℕ} {d : ℕ → ℕ} {lam lam' : ℕ → ℝ} {r : ℕ}
    (h : ∀ q < r, lam q = lam' q) (p c : ℕ) : roof a n d lam r p c = roof a n d lam' r p c :=
  Finset.sum_congr rfl fun q hq => by rw [h q (Finset.mem_range.mp hq)]

lemma QRows_congr_lam (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℕ) {lam lam' : ℕ → ℝ} {r : ℕ} (hr : 1 ≤ r)
    (h : ∀ q < r, lam q = lam' q) : QRows a N n d lam r = QRows a N n d lam' r := by
  ext x
  simp only [QRows, Set.mem_setOf_eq, roof_congr h, h 0 hr]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, fun p hp => by rw [← h (p + 1) hp]; exact h4 p hp, h5, h6⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨h1, h2, h3, fun p hp => by rw [h (p + 1) hp]; exact h4 p hp, h5, h6⟩

lemma Rsum_congr_lam (a : ℕ → ℝ) (N n : ℕ) (d : ℕ → ℕ) {lam lam' : ℕ → ℝ} {r : ℕ}
    (h : ∀ q < r, lam q = lam' q) : Rsum a N n d lam r = Rsum a N n d lam' r :=
  Finset.sum_congr rfl fun q hq => by rw [h q (Finset.mem_range.mp hq)]

/-! ## A run in its own coordinates: `QRows` is `QTheta` re-indexed -/

/-- The window of a run, re-indexed so that it starts at coordinate `1`:
`loc x c = x_{d 0 + c}`, `c = 1, …, d(r−1) − d 0 + n`. -/
def loc (n : ℕ) (d : ℕ → ℕ) (r : ℕ) (x : Fin N → ℝ) :
    Fin ((fun q => d q - d 0) (r - 1) + n) → ℝ :=
  fun i => co x (d 0 + i.val + 1)

lemma co_loc (n : ℕ) (d : ℕ → ℕ) (r : ℕ) (x : Fin N → ℝ) {c c' : ℕ} (h1 : 1 ≤ c)
    (h2 : c ≤ d (r - 1) - d 0 + n) (hc' : c' = d 0 + c) : co (loc n d r x) c = co x c' := by
  rw [co_of (loc n d r x) h1 h2, hc']
  simp only [loc]
  congr 1
  omega

lemma roof_loc (a : ℕ → ℝ) (n : ℕ) {d : ℕ → ℕ} (lam : ℕ → ℝ) {r : ℕ} (hd : Incr d r)
    (p : ℕ) {c c' : ℕ} (hc' : c' = d 0 + c) :
    roof a n (fun q => d q - d 0) lam r p c = roof a n d lam r p c' := by
  refine Finset.sum_congr rfl fun q hq => ?_
  have := hd.le (Nat.zero_le q) (Finset.mem_range.mp hq)
  simp only [Aw]
  split_ifs <;> first | rfl | omega | (congr 2; omega)

/-- **A run's rows are its Θ-form in its own coordinates**: `x` satisfies the rows of `QRows`
(global coordinates) iff its window, re-indexed from `1`, lies in `QTheta` of
Theorem `thm-theta` for the shifts `d q − d 0` (first shift `0`, ambient `d(r−1) − d 0 + n`). -/
theorem QRows_iff_QTheta (a : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) {d : ℕ → ℕ} (lam : ℕ → ℝ) {r : ℕ}
    (hr : 1 ≤ r) (hd : Incr d r) (x : Fin N → ℝ) :
    x ∈ QRows a N n d lam r ↔ loc n d r x ∈ QTheta a n (fun q => d q - d 0) lam r := by
  have hle : ∀ p, p < r → d 0 ≤ d p ∧ d p ≤ d (r - 1) := fun p hp =>
    ⟨hd.le (Nat.zero_le p) hp, hd.le (by omega) (by omega)⟩
  have hsucc : ∀ p, p + 1 < r → d p + 1 ≤ d (p + 1) := fun p hp => hd p hp
  have hco := fun {c c' : ℕ} => co_loc n d r x (c := c) (c' := c')
  have hrf := fun p {c c' : ℕ} => roof_loc a n lam hd p (c := c) (c' := c')
  simp only [QRows, QTheta, Set.mem_setOf_eq]
  have h0 := hle 0 (by omega)
  refine and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ (and_congr ?_ ?_))))
  · rw [hco le_rfl (by omega) rfl]
  · refine forall_congr' fun j => imp_congr_right fun hj => imp_congr_right fun hjn => ?_
    rw [hco (c := j + 1) (c' := d 0 + j + 1) (by omega) (by omega) (by omega), hco (c := j) hj (by omega) rfl,
      hrf 0 (c := j + 1) (c' := d 0 + j + 1) (by omega), hrf 0 (c := j) rfl]
  · refine forall_congr' fun p => forall_congr' fun j => imp_congr_right fun hp =>
      imp_congr_right fun hpr => imp_congr_right fun hj => imp_congr_right fun hjn => ?_
    have := hle p hpr
    rw [hco (c := d p - d 0 + j + 1) (c' := d p + j + 1) (by omega) (by omega) (by omega),
      hco (c := d p - d 0 + j) (c' := d p + j) (by omega) (by omega) (by omega),
      hrf p (c := d p - d 0 + j + 1) (c' := d p + j + 1) (by omega),
      hrf p (c := d p - d 0 + j) (c' := d p + j) (by omega)]
  · refine forall_congr' fun p => imp_congr_right fun hp => ?_
    have := hle (p + 1) hp
    rw [hco (c := d (p + 1) - d 0 + 1) (c' := d (p + 1) + 1) (by omega) (by omega) (by omega)]
  · refine forall_congr' fun p => imp_congr_right fun hp => ?_
    have := hle (p + 1) hp
    have := hle p (by omega)
    have := hsucc p hp
    rw [hco (c := d p - d 0 + n + 1) (c' := d p + n + 1) (by omega) (by omega) (by omega),
      hrf p (c := d p - d 0 + n + 1) (c' := d p + n + 1) (by omega)]
  · have := hle (r - 1) (by omega)
    rw [hco (c := d (r - 1) - d 0 + n) (c' := d (r - 1) + n) (by omega) le_rfl (by omega)]

/-! ## Runs -/

/-- A cut of the distinct shifts `e 0 < ⋯ < e (s−1)` into `k` consecutive runs
`[β b, β (b+1))`, with every gap inside a run `≤ n − 1` and every gap between runs `≥ n`.  This is
the cut into maximal runs (it is determined by `e`, and `Runs.exists` builds it). -/
structure Runs (n : ℕ) (e : ℕ → ℕ) (s : ℕ) where
  k : ℕ
  β : ℕ → ℕ
  β0 : β 0 = 0
  βk : β k = s
  βlt : ∀ b < k, β b < β (b + 1)
  inner : ∀ b < k, ∀ i, β b ≤ i → i + 1 < β (b + 1) → e (i + 1) < e i + n
  cut : ∀ b, 0 < b → b < k → e (β b - 1) + n ≤ e (β b)

namespace Runs

variable {n : ℕ} {e : ℕ → ℕ} {s : ℕ} (R : Runs n e s)

/-- The shifts of run `b`, re-indexed from `0`. -/
def sh (b : ℕ) : ℕ → ℕ := fun q => e (R.β b + q)

/-- The weights of run `b`, re-indexed from `0`. -/
def wt (lam : ℕ → ℝ) (b : ℕ) : ℕ → ℝ := fun q => lam (R.β b + q)

/-- The number of shifts in run `b`. -/
def len (b : ℕ) : ℕ := R.β (b + 1) - R.β b

lemma β_mono {b b' : ℕ} (h : b ≤ b') (hb' : b' ≤ R.k) : R.β b ≤ R.β b' := by
  induction b', h using Nat.le_induction with
  | base => exact le_rfl
  | succ m hm ih => exact le_trans (ih (by omega)) (R.βlt m (by omega)).le

lemma β_le_s {b : ℕ} (hb : b ≤ R.k) : R.β b ≤ s := by
  have := R.β_mono hb le_rfl; rwa [R.βk] at this

lemma len_pos {b : ℕ} (hb : b < R.k) : 1 ≤ R.len b := by
  have := R.βlt b hb; unfold len; omega

lemma sh_last {b : ℕ} (hb : b < R.k) : R.sh b (R.len b - 1) = e (R.β (b + 1) - 1) := by
  have := R.βlt b hb
  unfold sh len; congr 1; omega

/-- Summing over the shifts is summing over the runs. -/
lemma sum_runs {M : Type*} [AddCommMonoid M] (f : ℕ → M) :
    ∑ p ∈ range s, f p = ∑ b ∈ range R.k, ∑ q ∈ range (R.len b), f (R.β b + q) := by
  have key : ∀ m, m ≤ R.k →
      ∑ p ∈ range (R.β m), f p = ∑ b ∈ range m, ∑ q ∈ range (R.len b), f (R.β b + q) := by
    intro m
    induction m with
    | zero => intro _; simp [R.β0]
    | succ m ih =>
        intro hm
        rw [Finset.sum_range_succ, ← ih (by omega), len, ← Finset.sum_Ico_eq_sum_range,
          Finset.sum_range_add_sum_Ico _ (R.β_mono (Nat.le_succ m) hm)]
  rw [← key R.k le_rfl, R.βk]

lemma incr_run (he : Incr e s) {b : ℕ} (hb : b < R.k) : Incr (R.sh b) (R.len b) := by
  intro p hp
  have := R.β_le_s (b := b + 1) (by omega)
  unfold len at hp
  exact he (R.β b + p) (by omega)

lemma gaps_run {b : ℕ} (hb : b < R.k) : Gaps n (R.sh b) (R.len b) := by
  intro p hp
  unfold len at hp
  exact R.inner b hb (R.β b + p) (by omega) (by omega)

/-- Which run an index lies in. -/
lemma exists_run {i : ℕ} (hi : i < s) : ∃ b < R.k, R.β b ≤ i ∧ i < R.β (b + 1) := by
  have key : ∀ m, m ≤ R.k → i < R.β m → ∃ b < m, R.β b ≤ i ∧ i < R.β (b + 1) := by
    intro m
    induction m with
    | zero => intro _ h; rw [R.β0] at h; omega
    | succ m ih =>
        intro hm h
        by_cases h' : i < R.β m
        · obtain ⟨b, hb, h1⟩ := ih (by omega) h'
          exact ⟨b, by omega, h1⟩
        · exact ⟨m, by omega, by omega, h⟩
  obtain ⟨b, hb, h⟩ := key R.k le_rfl (by rw [R.βk]; exact hi)
  exact ⟨b, hb, h⟩

/-- A coordinate is covered by some run's window iff it is covered by some summand's window. -/
lemma covered_iff (he : Incr e s) (c : ℕ) :
    (∃ b < R.k, Win n (R.sh b) (R.len b) c) ↔ ∃ i < s, e i < c ∧ c ≤ e i + n := by
  constructor
  · rintro ⟨b, hb, h1, h2⟩
    rw [R.sh_last hb] at h2
    simp only [sh, add_zero] at h1
    have hlt := R.βlt b hb
    have hs := R.β_le_s (b := b + 1) (by omega)
    classical
    let P : ℕ → Prop := fun i => R.β b ≤ i ∧ e i < c
    have hPg : P (Nat.findGreatest P (R.β (b + 1) - 1)) :=
      Nat.findGreatest_spec (P := P) (m := R.β b) (by omega) ⟨le_rfl, h1⟩
    have hg : Nat.findGreatest P (R.β (b + 1) - 1) ≤ R.β (b + 1) - 1 :=
      Nat.findGreatest_le (P := P) _
    have hgr : ∀ m, Nat.findGreatest P (R.β (b + 1) - 1) < m → m ≤ R.β (b + 1) - 1 → ¬ P m :=
      fun m h h' => Nat.findGreatest_is_greatest h h'
    generalize Nat.findGreatest P (R.β (b + 1) - 1) = g at hPg hg hgr
    refine ⟨g, by omega, hPg.2, ?_⟩
    by_cases htop : g = R.β (b + 1) - 1
    · rw [htop]; exact h2
    · have hnot : ¬ P (g + 1) := hgr (g + 1) (by omega) (by omega)
      have hc : c ≤ e (g + 1) := by
        by_contra hc
        exact hnot ⟨by have := hPg.1; omega, by omega⟩
      have := R.inner b hb g hPg.1 (by omega)
      omega
  · rintro ⟨i, hi, h1, h2⟩
    obtain ⟨b, hb, hbi, hib⟩ := R.exists_run hi
    have hs := R.β_le_s (b := b + 1) (by omega)
    refine ⟨b, hb, ?_, ?_⟩
    · have := he.le hbi hi
      simp only [sh, add_zero]; omega
    · rw [R.sh_last hb]
      have := he.le (show i ≤ R.β (b + 1) - 1 by omega) (by omega)
      omega

/-- Distinct runs have disjoint windows. -/
lemma win_disjoint (he : Incr e s) {b b' c : ℕ} (hbb : b < b') (hb' : b' < R.k)
    (h : Win n (R.sh b) (R.len b) c) (h' : Win n (R.sh b') (R.len b') c) : False := by
  obtain ⟨-, h2⟩ := h
  obtain ⟨h1, -⟩ := h'
  rw [R.sh_last (by omega)] at h2
  simp only [sh, add_zero] at h1
  have hcut := R.cut (b + 1) (by omega) (by omega)
  have hs := R.β_le_s (b := b' + 1) (by omega)
  have hlt := R.βlt b' hb'
  have := he.le (R.β_mono (show b + 1 ≤ b' by omega) (by omega)) (by omega)
  omega

end Runs

/-! ## Distinct shifts, arbitrary gaps -/

/-- **The H-description for distinct shifts and arbitrary gaps** (the "runs" step of
`cor-facets-every-d`, weighted): for a positive weakly log-concave leg vector, distinct shifts
`e 0 < ⋯ < e (s−1)` (no condition on the gaps, nor on `e 0`), positive weights, and the cut `R`
into maximal runs, `∑_i lam i • shift^{e i} ∠(a)` is cut out by the Θ-form rows of every run
(`QRows`, in the global coordinates) together with `x_c = 0` on every coordinate covered by no
window. -/
theorem Rsum_eq_runs (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n)
    (hn : 1 ≤ n) {e : ℕ → ℕ} {s : ℕ} (he : Incr e s) {lam : ℕ → ℝ} (hlam : ∀ i < s, 0 < lam i)
    (hN : ∀ i < s, e i + n ≤ N) (R : Runs n e s) :
    Rsum a N n e lam s =
      {x | (∀ b < R.k, x ∈ QRows a N n (R.sh b) (R.wt lam b) (R.len b)) ∧
        ∀ c, (∀ i < s, ¬ (e i < c ∧ c ≤ e i + n)) → co x c = 0} := by
  set lam' : ℕ → ℝ := fun i => if i < s then lam i else 1 with hlam'def
  have hlam' : ∀ i, 0 < lam' i := fun i => by
    simp only [hlam'def]; split_ifs with h
    · exact hlam i h
    · exact one_pos
  have heq : ∀ i < s, lam i = lam' i := fun i hi => by simp [hlam'def, hi]
  have hrun : ∀ b < R.k, ∀ q < R.len b, R.wt lam b q = R.wt lam' b q := fun b hb q hq => by
    have := R.β_le_s (b := b + 1) (by omega)
    unfold Runs.len at hq
    exact heq _ (by omega)
  have hRB : ∀ b < R.k, Rsum a N n (R.sh b) (R.wt lam' b) (R.len b) =
      QZ a N n (R.sh b) (R.wt lam' b) (R.len b) := fun b hb =>
    theoremB a hpos hlc hn (R.len_pos hb) (R.incr_run he hb) (R.gaps_run hb)
      (by rw [R.sh_last hb]; have := R.βlt b hb; have := R.β_le_s (b := b + 1) (by omega)
          exact hN _ (by omega))
      (fun q => hlam' _)
  have hsplit : Rsum a N n e lam s =
      ∑ b ∈ range R.k, QZ a N n (R.sh b) (R.wt lam' b) (R.len b) := by
    rw [Rsum_congr_lam a N n e heq, Rsum, R.sum_runs]
    exact Finset.sum_congr rfl fun b hb => by
      rw [← hRB b (Finset.mem_range.mp hb)]; rfl
  ext x
  rw [hsplit, mem_sum_iff_msk R.k (fun b => Win n (R.sh b) (R.len b))]
  · simp only [Set.mem_setOf_eq]
    refine and_congr (forall₂_congr fun b hb => ?_) (forall_congr' fun c => ?_)
    · rw [msk_mem_QZ_iff hn (R.len_pos hb) (R.incr_run he hb),
        QRows_congr_lam a n _ (R.len_pos hb) (hrun b hb)]
    · have := R.covered_iff he c
      constructor
      · intro h hc
        apply h
        intro b hb hw
        obtain ⟨i, hi, hw'⟩ := this.mp ⟨b, hb, hw⟩
        exact hc i hi hw'
      · intro h hc
        apply h
        intro i hi hw
        obtain ⟨b, hb, hw'⟩ := this.mpr ⟨i, hi, hw⟩
        exact hc b hb hw'
  · intro b hb y hy c hc
    obtain ⟨hZ1, hZ2, -⟩ := hy
    by_cases h1 : c ≤ R.sh b 0
    · exact hZ1 c h1
    · exact hZ2 c (by unfold Win at hc; omega)
  · intro b b' c hbb hb' h h'
    exact R.win_disjoint he hbb hb' h h'

/-- The cut into maximal runs exists, for every `e` and `s`. -/
theorem Runs.nonempty (n : ℕ) (e : ℕ → ℕ) (s : ℕ) : Nonempty (Runs n e s) := by
  induction s with
  | zero =>
      exact ⟨⟨0, fun _ => 0, rfl, rfl, fun b hb => absurd hb (Nat.not_lt_zero _),
        fun b hb => absurd hb (Nat.not_lt_zero _), fun b _ hb => absurd hb (Nat.not_lt_zero _)⟩⟩
  | succ s ih =>
      obtain ⟨R⟩ := ih
      by_cases hs : s = 0
      · subst hs
        refine ⟨⟨1, fun b => if b = 0 then 0 else 1, by simp, by simp, fun b hb => ?_,
          fun b hb i h1 h2 => ?_, fun b h0 h1 => by omega⟩⟩
        · obtain rfl : b = 0 := by omega
          simp
        · obtain rfl : b = 0 := by omega
          simp at h2
      have hk : 0 < R.k := by
        by_contra h0
        have := R.βk
        rw [show R.k = 0 by omega, R.β0] at this
        omega
      have hβk := R.βk
      by_cases hg : e s < e (s - 1) + n
      · refine ⟨⟨R.k, fun b => if b = R.k then s + 1 else R.β b, ?_, by simp, ?_, ?_, ?_⟩⟩
        · rw [if_neg (by omega)]; exact R.β0
        · intro b hb
          rw [if_neg (by omega)]
          split_ifs with h
          · have := R.βlt b hb; rw [h] at this; omega
          · exact R.βlt b hb
        · intro b hb i h1 h2
          rw [if_neg (by omega)] at h1
          split_ifs at h2 with h
          · by_cases hi : i + 1 < s
            · exact R.inner b hb i h1 (by rw [h, hβk]; exact hi)
            · obtain rfl : i = s - 1 := by omega
              rwa [Nat.sub_add_cancel (by omega)]
          · exact R.inner b hb i h1 h2
        · intro b h0 hb
          rw [if_neg (by omega)]
          exact R.cut b h0 hb
      · refine ⟨⟨R.k + 1, fun b => if b = R.k + 1 then s + 1 else R.β b, ?_, by simp, ?_, ?_, ?_⟩⟩
        · rw [if_neg (by omega)]; exact R.β0
        · intro b hb
          rw [if_neg (by omega)]
          split_ifs with h
          · obtain rfl : b = R.k := by omega
            omega
          · exact R.βlt b (by omega)
        · intro b hb i h1 h2
          rw [if_neg (by omega)] at h1
          split_ifs at h2 with h
          · obtain rfl : b = R.k := by omega
            omega
          · exact R.inner b (by omega) i h1 h2
        · intro b h0 hb
          rw [if_neg (by omega)]
          by_cases hbk : b = R.k
          · subst hbk; rw [hβk]; omega
          · exact R.cut b h0 (by omega)

/-! ## Merging tied shifts -/

/-- `∑_{p ∈ t} A = |t| • A` for a convex nonempty `A`: tied summands merge into one, weighted by
the multiplicity. -/
lemma sum_const_convex {E : Type*} [AddCommGroup E] [Module ℝ E] {A : Set E} (hA : Convex ℝ A)
    (hne : A.Nonempty) (t : Finset ℕ) : ∑ _p ∈ t, A = (t.card : ℝ) • A := by
  induction t using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.card_empty, Nat.cast_zero, Set.zero_smul_set hne]
  | insert p t hp ih =>
      rw [Finset.sum_insert hp, ih, Finset.card_insert_of_notMem hp, Nat.cast_succ,
        Convex.add_smul hA (by positivity) zero_le_one, one_smul, add_comm]

/-- The distinct values `e 0 < ⋯ < e (s−1)` of the shifts `d 0, …, d (r−1)` (any order, ties
allowed).  `Merge.canon` builds it. -/
structure Merge (d : ℕ → ℕ) (r : ℕ) where
  s : ℕ
  e : ℕ → ℕ
  incr : Incr e s
  img : ∀ p < r, ∃ i < s, d p = e i
  surj : ∀ i < s, ∃ p < r, d p = e i

namespace Merge

variable {d : ℕ → ℕ} {r : ℕ} (M : Merge d r)

/-- The merged weight of the `i`-th distinct shift: its multiplicity `#{p < r : d p = e i}`. -/
noncomputable def wt (i : ℕ) : ℝ := (mult d r (M.e i) : ℝ)

lemma wt_pos {i : ℕ} (hi : i < M.s) : 0 < M.wt i := by
  obtain ⟨p, hp, hpe⟩ := M.surj i hi
  unfold wt mult
  exact_mod_cast Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, hpe⟩⟩

lemma e_injOn : Set.InjOn M.e (range M.s) := by
  intro i hi j hj h
  rw [Finset.coe_range, Set.mem_Iio] at hi hj
  rcases lt_trichotomy i j with hij | rfl | hij
  · exact absurd h (M.incr.lt hij hj).ne
  · rfl
  · exact absurd h (M.incr.lt hij hi).ne'

lemma image_eq : (range r).image d = (range M.s).image M.e := by
  ext v
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨p, hp, rfl⟩
    obtain ⟨i, hi, h⟩ := M.img p hp
    exact ⟨i, hi, h.symm⟩
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨p, hp, h⟩ := M.surj i hi
    exact ⟨p, hp, h⟩

/-- The canonical merge: the sorted distinct values of `d` on `range r`. -/
noncomputable def canon (d : ℕ → ℕ) (r : ℕ) : Merge d r where
  s := ((range r).image d).card
  e := fun i => if h : i < ((range r).image d).card then
      ((range r).image d).orderEmbOfFin rfl ⟨i, h⟩ else 0
  incr := fun p hp => by
    simp only [dif_pos hp, dif_pos (show p < ((range r).image d).card by omega)]
    exact (((range r).image d).orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self p))
  img := fun p hp => by
    have hm : d p ∈ (range r).image d := Finset.mem_image_of_mem d (Finset.mem_range.mpr hp)
    have hm' : d p ∈ Set.range (((range r).image d).orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr hm
    obtain ⟨j, hj⟩ := hm'
    exact ⟨j.val, j.isLt, by simp only [dif_pos j.isLt]; exact hj.symm⟩
  surj := fun i hi => by
    have hm := ((range r).image d).orderEmbOfFin_mem rfl ⟨i, hi⟩
    obtain ⟨p, hp, hpe⟩ := Finset.mem_image.mp hm
    exact ⟨p, Finset.mem_range.mp hp, by simp only [dif_pos hi]; exact hpe⟩

end Merge

/-- **Merging** (first step of `cor-facets-every-d`): `RA(a; d⃗) = ∑_p shift^{d p} ∠(a)` is the
weighted sum over the distinct shifts, each weighted by its multiplicity. -/
theorem sum_angle_eq_Rsum (a : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) {d : ℕ → ℕ} {r : ℕ}
    (M : Merge d r) :
    ∑ p ∈ range r, angle a N (d p) n = Rsum a N n M.e M.wt M.s := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := (range r).image d) (g := d)
    (fun p hp => Finset.mem_image_of_mem d hp)]
  have hfib : ∀ v, ∑ p ∈ range r with d p = v, angle a N (d p) n =
      (mult d r v : ℝ) • angle a N v n := fun v => by
    rw [Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]]
    exact sum_const_convex (convex_convexHull ℝ _)
      ⟨_, subset_convexHull ℝ _ (ravA_mem_vsetA (a := a) (N := N) (d := v) le_rfl hn)⟩ _
  simp only [hfib]
  rw [M.image_eq, Finset.sum_image M.e_injOn]
  rfl

/-! ## Corollary `cor-facets-every-d`, the H-description -/

/-- The system of Corollary `cor-facets-every-d`: the Θ-form rows of every run of the merged
shifts (weights = multiplicities), plus `x_c = 0` on every coordinate covered by no window. -/
def EverySys (a : ℕ → ℝ) (N n : ℕ) (d : ℕ → ℕ) (r : ℕ) (M : Merge d r) (R : Runs n M.e M.s) :
    Set (Fin N → ℝ) :=
  {x | (∀ b < R.k, x ∈ QRows a N n (R.sh b) (R.wt M.wt b) (R.len b)) ∧
    ∀ c, (∀ p < r, ¬ (d p < c ∧ c ≤ d p + n)) → co x c = 0}

/-- **Corollary `cor-facets-every-d`, H-description half.**  For a positive weakly log-concave leg
vector and *arbitrary* shifts `d 0, …, d (r−1)` (any order, ties and gaps of any size, ambient `N`
with `d p + n ≤ N`), `RA(a; d⃗)` is cut out by the merged-and-cut Θ-form system. -/
theorem cor_facets_every_d (a : ℕ → ℝ) (hpos : ∀ s, 0 < a s) {n : ℕ} (hlc : LogConcaveOn a n)
    (hn : 1 ≤ n) {d : ℕ → ℕ} {r : ℕ} (hN : ∀ p < r, d p + n ≤ N) (M : Merge d r)
    (R : Runs n M.e M.s) :
    ∑ p ∈ range r, angle a N (d p) n = EverySys a N n d r M R := by
  rw [sum_angle_eq_Rsum a hn M, Rsum_eq_runs a hpos hlc hn M.incr (fun i hi => M.wt_pos hi)
    (fun i hi => by obtain ⟨p, hp, h⟩ := M.surj i hi; rw [← h]; exact hN p hp) R]
  ext x
  simp only [EverySys, Set.mem_setOf_eq]
  refine and_congr Iff.rfl (forall_congr' fun c => imp_congr_left ?_)
  constructor
  · intro h p hp hw
    obtain ⟨i, hi, he⟩ := M.img p hp
    exact h i hi (he ▸ hw)
  · intro h i hi hw
    obtain ⟨p, hp, he⟩ := M.surj i hi
    exact h p hp (he ▸ hw)

/-- **Corollary `cor-koz-hdesc` for general `d⃗`**: `f ∈ Koz(n; d⃗)` iff `f₀ = #{p : d_p = 0}` and
`(f_c − #{p : d_p = c})_{c = 1..N}` (that is, `π(f) − ∑_{p : d_p ≥ 1} e_{d_p}`) satisfies the
system of Corollary `cor-facets-every-d` for `κ⃗(n)`. -/
theorem koz_hdesc_every_d {n : ℕ} (hn : 1 ≤ n) {d : ℕ → ℕ} {r : ℕ} (hN : ∀ p < r, d p + n ≤ N)
    (M : Merge d r) (R : Runs n M.e M.s) (f : Fin (N + 1) → ℝ) :
    f ∈ convexHull ℝ (ffSet n N (fun i : Fin r => d i)) ↔
      f 0 = (mult d r 0 : ℝ) ∧
        (fun i : Fin N => f i.succ - (mult d r (i.val + 1) : ℝ)) ∈
          EverySys (kozLeg n) N n d r M R := by
  rw [mem_koz_iff hn d hN, cor_facets_every_d _ (kozLeg_pos n) (kozLeg_logConcave n) hn hN M R]

/-- The same with the canonical merge and cut, so with no data to supply. -/
theorem koz_hdesc_every_d' {n : ℕ} (hn : 1 ≤ n) {d : ℕ → ℕ} {r : ℕ} (hN : ∀ p < r, d p + n ≤ N)
    (f : Fin (N + 1) → ℝ) :
    f ∈ convexHull ℝ (ffSet n N (fun i : Fin r => d i)) ↔
      f 0 = (mult d r 0 : ℝ) ∧
        (fun i : Fin N => f i.succ - (mult d r (i.val + 1) : ℝ)) ∈
          EverySys (kozLeg n) N n d r (Merge.canon d r)
            (Classical.choice (Runs.nonempty n (Merge.canon d r).e (Merge.canon d r).s)) :=
  koz_hdesc_every_d hn hN _ _ f

/-- The system of `cor-facets-every-d` as printed: each run's Θ-form `QTheta` of
Theorem `thm-theta`, written in the run's own coordinates (window re-indexed from `1`, shifts
`d q − d_first`), plus `x_c = 0` on every coordinate covered by no window. -/
theorem mem_EverySys_iff_local {a : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n) {d : ℕ → ℕ} {r : ℕ}
    (M : Merge d r) (R : Runs n M.e M.s) (x : Fin N → ℝ) :
    x ∈ EverySys a N n d r M R ↔
      (∀ b < R.k, loc n (R.sh b) (R.len b) x ∈
          QTheta a n (fun q => R.sh b q - R.sh b 0) (R.wt M.wt b) (R.len b)) ∧
        ∀ c, (∀ p < r, ¬ (d p < c ∧ c ≤ d p + n)) → co x c = 0 := by
  simp only [EverySys, Set.mem_setOf_eq]
  exact and_congr (forall₂_congr fun b hb =>
    QRows_iff_QTheta a hn _ (R.len_pos hb) (R.incr_run M.incr hb) x) Iff.rfl

/-- `cor-koz-hdesc` for general `d⃗`, with each run's system in its own coordinates. -/
theorem koz_hdesc_every_d_local {n : ℕ} (hn : 1 ≤ n) {d : ℕ → ℕ} {r : ℕ}
    (hN : ∀ p < r, d p + n ≤ N) (M : Merge d r) (R : Runs n M.e M.s) (f : Fin (N + 1) → ℝ) :
    f ∈ convexHull ℝ (ffSet n N (fun i : Fin r => d i)) ↔
      f 0 = (mult d r 0 : ℝ) ∧
        (∀ b < R.k, loc n (R.sh b) (R.len b)
            (fun i : Fin N => f i.succ - (mult d r (i.val + 1) : ℝ)) ∈
          QTheta (kozLeg n) n (fun q => R.sh b q - R.sh b 0) (R.wt M.wt b) (R.len b)) ∧
        ∀ c, (∀ p < r, ¬ (d p < c ∧ c ≤ d p + n)) →
          co (fun i : Fin N => f i.succ - (mult d r (i.val + 1) : ℝ)) c = 0 := by
  rw [koz_hdesc_every_d hn hN M R, mem_EverySys_iff_local hn]

end EveryD
end ExteriorConvex
