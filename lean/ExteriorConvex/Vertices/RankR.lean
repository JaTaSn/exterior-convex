/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Article 3: the rank-`r` vertex theorem for `RA(a; d⃗)`

The bridge from `PairwiseReduction.lean`'s window systems to the polytope.  Two ingredients:

* `mem_extremePoints_sum_iff`: `lem-vertexdecomp` for a Minkowski sum of **any finite number** of
  polytopes given by finite generating sets (the existing `mem_extremePoints_add_iff` in
  `Bridge.lean` is the two-summand case).  Same proof: `convexHull_sum` reduces to one polytope,
  then `mem_extremePoints_convexHull_iff` and an exchange argument.
* `map_ravA_eq_sum` / `clmOf`: a linear functional on `Fin N → ℝ` and a coefficient sequence
  `φ : ℕ → ℝ` determine each other on the vertices `ravA a N d k` of `ExtremalMatrix.lean`
  (manuscript coordinate `c` ↔ `Fin` index `c − 1`), so "a functional uniquely maximised at each
  chosen vertex" is exactly `Pairwise.Feasible`.

Main results, for a leg vector positive everywhere (as in `ExtremalMatrix.lean`; `ravA` only reads
`a` on `[1,n]`, so this is a convention, cf. `kozLeg`), shifts with `d p + n ≤ N`:

* `vertex_iff_feasible`: the sum of chosen vertices is a vertex of `∑ₚ shift^{d p}(∠(a))` iff the
  window system is feasible — for any finite set of summands.
* `vertex_iff_CF` (**Theorem 2 at the polytope level, every rank**): for weakly log-concave `a` and
  sorted shifts, `M[𝐣] = 1` iff every consecutive pair satisfies (i)–(iii).
* `vertex_iff_consecutive` (**Theorem 1 at the polytope level**): `M[𝐣] = 1` iff every consecutive
  rank-two entry `M^{(p,p+1)}[j p][j (p+1)]` is `1`.
-/
import Mathlib
import ExteriorConvex.Vertices.Bridge
import ExteriorConvex.Vertices.ExtremalMatrix
import ExteriorConvex.Vertices.PairwiseReduction

namespace ExteriorConvex

open Set Pointwise

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
lemma finite_finset_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : ι → Set E)
    (hS : ∀ i ∈ s, (S i).Finite) : (∑ i ∈ s, S i).Finite := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hS i (Finset.mem_insert_self i s)).add
        (ih fun k hk => hS k (Finset.mem_insert_of_mem hk))

/-- **`lem-vertexdecomp` for `r` summands.**  A sum of generators is a vertex of a finite Minkowski
sum of polytopes iff one functional has every summand as its unique maximiser. -/
theorem mem_extremePoints_sum_iff {ι : Type*} [DecidableEq ι] (s : Finset ι) (S : ι → Set E)
    (hS : ∀ i ∈ s, (S i).Finite) (x : ι → E) (hx : ∀ i ∈ s, x i ∈ S i) :
    ∑ i ∈ s, x i ∈ Set.extremePoints ℝ (∑ i ∈ s, convexHull ℝ (S i)) ↔
      ∃ f : E →L[ℝ] ℝ, ∀ i ∈ s, ∀ y ∈ S i, y ≠ x i → f y < f (x i) := by
  rw [← convexHull_sum, mem_extremePoints_convexHull_iff (finite_finset_sum s S hS)]
  constructor
  · rintro ⟨-, f, hf⟩
    refine ⟨f, fun i hi y hy hne => ?_⟩
    have hmem : ∑ k ∈ s, Function.update x i y k ∈ ∑ k ∈ s, S k := by
      rw [Set.mem_finsetSum]
      refine ⟨Function.update x i y, fun {k} hk => ?_, rfl⟩
      rcases eq_or_ne k i with rfl | h
      · simpa using hy
      · rw [Function.update_of_ne h]; exact hx k hk
    have hsum : ∑ k ∈ s, Function.update x i y k = y - x i + ∑ k ∈ s, x k := by
      rw [Finset.sum_update_of_mem hi, ← Finset.add_sum_erase s x hi, Finset.sdiff_singleton_eq_erase]
      abel
    have hne' : ∑ k ∈ s, Function.update x i y k ≠ ∑ k ∈ s, x k := by
      rw [hsum]
      intro h
      exact hne (sub_eq_zero.mp (by simpa using h))
    have := hf _ hmem hne'
    rw [hsum, map_add, map_sub] at this
    linarith
  · rintro ⟨f, hf⟩
    refine ⟨?_, f, fun z hz hne => ?_⟩
    · rw [Set.mem_finsetSum]
      exact ⟨x, fun {i} hi => hx i hi, rfl⟩
    · rw [Set.mem_finsetSum] at hz
      obtain ⟨g, hg, rfl⟩ := hz
      have hsome : ∃ i ∈ s, g i ≠ x i := by
        by_contra hc
        push Not at hc
        exact hne (Finset.sum_congr rfl hc)
      rw [map_sum, map_sum]
      refine Finset.sum_lt_sum (fun i hi => ?_) ?_
      · rcases eq_or_ne (g i) (x i) with h | h
        · rw [h]
        · exact (hf i hi (g i) (hg hi) h).le
      · obtain ⟨i, hi, h⟩ := hsome
        exact ⟨i, hi, hf i hi (g i) (hg hi) h⟩

end General

/-! ## Functionals versus coefficient sequences -/

variable {N : ℕ}

/-- The value of a functional on a vertex, in the window-system form of `PairwiseReduction`, with
the coefficient sequence `c ↦ coefAt f (c − 1)` (manuscript coordinate `c` is `Fin` index `c−1`). -/
lemma map_ravA_eq_sum (f : (Fin N → ℝ) →L[ℝ] ℝ) (a : ℕ → ℝ) (d : ℕ) :
    ∀ k, d + k ≤ N →
      f (ravA a N d k) = ∑ i ∈ Finset.Icc 1 k, a i * coefAt f (d + i - 1) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
      intro hk
      rw [map_ravA_succ' f a d k (by omega), ih (by omega), Finset.sum_Icc_succ_top (by omega)]
      congr 2

/-- The functional with prescribed coefficients: `x ↦ ∑_c φ(c+1) · x c`. -/
noncomputable def clmOf (N : ℕ) (φ : ℕ → ℝ) : (Fin N → ℝ) →L[ℝ] ℝ :=
  ∑ c : Fin N, φ (c.val + 1) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) c

lemma coefAt_clmOf (φ : ℕ → ℝ) {c : ℕ} (hc : c < N) : coefAt (clmOf N φ) c = φ (c + 1) := by
  rw [coefAt, dif_pos hc, clmOf]
  simp [Pi.single_apply]

/-- The local exposure condition only reads `φ` on the window `[d+1, d+n]`. -/
lemma expose_congr {a : ℕ → ℝ} {n d j : ℕ} {φ ψ : ℕ → ℝ} (hj : j ≤ n)
    (h : ∀ i, 1 ≤ i → i ≤ n → φ (d + i) = ψ (d + i)) :
    Pairwise.Expose a n d j φ → Pairwise.Expose a n d j ψ := by
  have hs : ∀ l, l ≤ n → ∑ i ∈ Finset.Icc 1 l, a i * φ (d + i)
      = ∑ i ∈ Finset.Icc 1 l, a i * ψ (d + i) := fun l hl =>
    Finset.sum_congr rfl fun i hi => by
      rw [Finset.mem_Icc] at hi; rw [h i hi.1 (by omega)]
  intro hφ l h1 h2 h3
  rw [← hs l h2, ← hs j hj]
  exact hφ l h1 h2 h3

/-- For one summand: unique maximality of `f` on the vertex set is the window condition. -/
lemma unique_max_iff_expose {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {n d j : ℕ} (hdN : d + n ≤ N)
    (hj : 1 ≤ j ∧ j ≤ n) (f : (Fin N → ℝ) →L[ℝ] ℝ) :
    (∀ y ∈ vsetA a N d n, y ≠ ravA a N d j → f y < f (ravA a N d j)) ↔
      Pairwise.Expose a n d j (fun c => coefAt f (c - 1)) := by
  have hval : ∀ k, k ≤ n →
      f (ravA a N d k) = ∑ i ∈ Finset.Icc 1 k, a i * (fun c => coefAt f (c - 1)) (d + i) :=
    fun k hk => map_ravA_eq_sum f a d k (by omega)
  constructor
  · intro h l h1 h2 h3
    rw [← hval l h2, ← hval j hj.2]
    exact h _ (ravA_mem_vsetA h1 h2) fun hc =>
      h3 (ravA_injOn a hpos (n := n) hdN ⟨h1, h2⟩ ⟨hj.1, hj.2⟩ hc)
  · rintro h y ⟨l, ⟨h1, h2⟩, rfl⟩ hne
    rw [hval l h2, hval j hj.2]
    exact h l h1 h2 fun hc => hne (by rw [hc])

/-- **The vertex criterion for `r` summands, window form.**  For any finite set `s` of summands
(windows inside `[1,N]`, choices in `[1,n]`): the sum of the chosen vertices is a vertex of the
Minkowski sum iff the window system is feasible. -/
theorem vertex_iff_feasible {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {n : ℕ} {d j : ℕ → ℕ}
    (s : Finset ℕ) (hN : ∀ p ∈ s, d p + n ≤ N) (hj : ∀ p ∈ s, 1 ≤ j p ∧ j p ≤ n) :
    ∑ p ∈ s, ravA a N (d p) (j p) ∈
        Set.extremePoints ℝ (∑ p ∈ s, convexHull ℝ (vsetA a N (d p) n)) ↔
      Pairwise.Feasible a n d j s := by
  rw [mem_extremePoints_sum_iff s _ (fun p _ => vsetA_finite a N (d p) n) _
    (fun p hp => ravA_mem_vsetA (hj p hp).1 (hj p hp).2)]
  constructor
  · rintro ⟨f, hf⟩
    exact ⟨_, fun p hp => (unique_max_iff_expose hpos (hN p hp) (hj p hp) f).mp (hf p hp)⟩
  · rintro ⟨φ, hφ⟩
    refine ⟨clmOf N φ, fun p hp => (unique_max_iff_expose hpos (hN p hp) (hj p hp) _).mpr ?_⟩
    refine expose_congr (hj p hp).2 (fun i h1 h2 => ?_) (hφ p hp)
    have := hN p hp
    rw [coefAt_clmOf φ (by omega)]
    congr 1
    omega

/-- **Theorem 2 at the polytope level, every rank.**  For a positive weakly log-concave leg vector
and sorted shifts, `∑ₚ shift^{d p} v(j p)` is a vertex of `RA(a; d⃗)` iff every consecutive pair
satisfies the note's (i)–(iii). -/
theorem vertex_iff_CF {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {n r : ℕ} (hlc : Pairwise.WLC a n)
    {d j : ℕ → ℕ} (hd : Monotone d) (hN : ∀ p < r, d p + n ≤ N)
    (hj : ∀ p < r, 1 ≤ j p ∧ j p ≤ n) :
    ∑ p ∈ Finset.range r, ravA a N (d p) (j p) ∈
        Set.extremePoints ℝ (∑ p ∈ Finset.range r, convexHull ℝ (vsetA a N (d p) n)) ↔
      ∀ p, p + 1 < r → Pairwise.CF a n d j p := by
  rw [vertex_iff_feasible hpos _ (fun p hp => hN p (Finset.mem_range.mp hp))
    (fun p hp => hj p (Finset.mem_range.mp hp))]
  exact Pairwise.feasible_iff_CF (fun i _ _ => hpos i) hlc hd hj

/-- **Theorem 1 at the polytope level (the consecutive pairwise reduction), every rank.**
`M[𝐣] = 1` iff `M^{(p,p+1)}[j p][j (p+1)] = 1` for every consecutive pair. -/
theorem vertex_iff_consecutive {a : ℕ → ℝ} (hpos : ∀ s, 0 < a s) {n r : ℕ}
    (hlc : Pairwise.WLC a n) {d j : ℕ → ℕ} (hd : Monotone d) (hN : ∀ p < r, d p + n ≤ N)
    (hj : ∀ p < r, 1 ≤ j p ∧ j p ≤ n) :
    ∑ p ∈ Finset.range r, ravA a N (d p) (j p) ∈
        Set.extremePoints ℝ (∑ p ∈ Finset.range r, convexHull ℝ (vsetA a N (d p) n)) ↔
      ∀ p, p + 1 < r → ravA a N (d p) (j p) + ravA a N (d (p + 1)) (j (p + 1)) ∈
        Set.extremePoints ℝ
          (convexHull ℝ (vsetA a N (d p) n) + convexHull ℝ (vsetA a N (d (p + 1)) n)) := by
  rw [vertex_iff_feasible hpos _ (fun p hp => hN p (Finset.mem_range.mp hp))
    (fun p hp => hj p (Finset.mem_range.mp hp)),
    (Pairwise.feasible_iff_consecutive (fun i _ _ => hpos i) hlc hd hj).2]
  refine forall_congr' fun p => imp_congr_right fun hp => ?_
  have hpair := vertex_iff_feasible (N := N) hpos (d := d) (j := j) {p, p + 1}
    (fun q hq => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> exact hN _ (by omega))
    (fun q hq => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl <;> exact hj _ (by omega))
  have hne : p ≠ p + 1 := by omega
  rw [Finset.sum_pair hne, Finset.sum_pair hne] at hpair
  exact hpair.symm

/-! ## The Kozlov leg vector at every rank -/

/-- The binomial coefficients are strictly log-concave. -/
lemma choose_slc {n i : ℕ} (hi : 1 ≤ i) (hin : i + 2 ≤ n) :
    n.choose i * n.choose (i + 2) < n.choose (i + 1) ^ 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = i + 2 + k := ⟨n - (i + 2), by omega⟩
  have hB := Nat.choose_succ_right_eq (i + 2 + k) i
  have hC := Nat.choose_succ_right_eq (i + 2 + k) (i + 1)
  have e1 : i + 2 + k - i = k + 2 := by omega
  have e2 : i + 2 + k - (i + 1) = k + 1 := by omega
  rw [e1] at hB
  rw [e2] at hC
  have hBpos : 0 < (i + 2 + k).choose (i + 1) := Nat.choose_pos (by omega)
  set A := (i + 2 + k).choose i
  set B := (i + 2 + k).choose (i + 1)
  set C := (i + 2 + k).choose (i + 1 + 1)
  have key : A * C * ((k + 2) * (i + 2)) < B ^ 2 * ((k + 2) * (i + 2)) := by
    have h1 : A * C * ((k + 2) * (i + 2)) = (B * (i + 1)) * (B * (k + 1)) := by
      rw [hB, ← hC]; ring
    rw [h1]
    have : (i + 1) * (k + 1) < (k + 2) * (i + 2) := by nlinarith
    calc B * (i + 1) * (B * (k + 1)) = B ^ 2 * ((i + 1) * (k + 1)) := by ring
      _ < B ^ 2 * ((k + 2) * (i + 2)) := Nat.mul_lt_mul_of_pos_left this (by positivity)
  exact Nat.lt_of_mul_lt_mul_right key

lemma kozLeg_slc (n : ℕ) : Pairwise.SLC (kozLeg n) n := fun i h1 h2 => by
  simp only [kozLeg]
  rw [if_pos (by omega), if_pos (by omega), if_pos (by omega)]
  exact_mod_cast choose_slc h1 h2

/-- **The vertices of `RA(κ⃗(n); d⃗)` at every rank** (note, Corollary "the Kozlov polytope at every
rank"; Part I's Remark `obs-pairwise`).  For sorted shifts, `∑ₚ shift^{d p} v(j p)` is a vertex iff
the chosen points `m p = d p + j p` climb weakly, equal shifts give equal points, and no step is a
unit step `m (p+1) = m p + 1` with `d (p+1) < m p < d p + n`.  The identification of
`RA(κ⃗(n); d⃗)` with the projection of `Koz(n; d⃗)` (`eq:koz-as-ra`) is not formalised. -/
theorem vertex_iff_kozlov {n r : ℕ} {d j : ℕ → ℕ} (hd : Monotone d) (hN : ∀ p < r, d p + n ≤ N)
    (hj : ∀ p < r, 1 ≤ j p ∧ j p ≤ n) :
    ∑ p ∈ Finset.range r, ravA (kozLeg n) N (d p) (j p) ∈
        Set.extremePoints ℝ
          (∑ p ∈ Finset.range r, convexHull ℝ (vsetA (kozLeg n) N (d p) n)) ↔
      ∀ p, p + 1 < r → Pairwise.KozCond n d j p := by
  rw [vertex_iff_CF (kozLeg_pos n) (kozLeg_slc n).wlc hd hN hj]
  refine forall_congr' fun p => imp_congr_right fun hp => ?_
  exact Pairwise.CF_iff_KozCond (fun i _ _ => kozLeg_pos n i) (kozLeg_slc n)
    (hd (show p ≤ p + 1 by omega)) (hj (p + 1) hp).2

end ExteriorConvex
