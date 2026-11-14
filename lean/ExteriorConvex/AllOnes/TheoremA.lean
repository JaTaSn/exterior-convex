/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The all-ones polytope: Theorem A (H-description) and Lemma 1 (coordinate change)

Completes, on top of `AllOnes/Hall.lean`, two results of
`working-notes/allones-hdescription-generalized-permutohedra.org` (note labels in brackets).

**Theorem A** (`thm-A`), for an arbitrary finite index set `ι`, an arbitrary finite family of
*nonempty* windows `W : κ → Finset ι` (repeats and non-intervals allowed), `r = Fintype.card κ`:

* `simplexOn I` is the note's `Δ_I = conv{e_i : i ∈ I}`; `polyP W = ∑ₚ Δ_{W p}` is `P`.
* `polyQ W = {y : y(univ) = r, y(J) ≤ f(J) ∀ J}` (`f = cover W`, from `Hall.lean`) is `Q`;
  `polyQ' W = {y : y(univ) = r, y(K) ≥ g(K) ∀ K}` with `g = lowerCover W`, `g(K) = #{p : W p ⊆ K}`.
* `polyP_subset_polyQ` (`P ⊆ Q`, no nonemptiness needed), `polyQ_eq_polyQ'` (the two descriptions
  agree, via `f(univ ∖ K) + g(K) = r`, `cover_compl_add_lowerCover`), and
  `polyP_eq_polyQ` / `polyP_eq_polyQ'` (**Theorem A**).  `Q ⊆ P` is the note's argument:
  `Hall.lean`'s `dot_le_sum_sup'` (the Abel-summation inequality, proved there by a different
  induction) bounds `c · y` by `h_P(c) = ∑ₚ max_{W_p} c`, the bound is attained at a vertex sum
  `∑ₚ e_{mₚ} ∈ P`, and Mathlib's `geometric_hahn_banach_point_closed` separates `y ∉ P` from the
  compact convex `P` (`isCompact_polyP`, `convex_polyP`).

**Lemma 1** (`lem-coords`), in the library's coordinates (`RA(𝟙; d⃗)` =
`∑ₚ convexHull ℝ (vsetA (fun _ => 1) N (d p) n)`, `Fin N`, `Fin` index `k` ↔ manuscript `k+1`):

* `tauP N d = Pi.single (d−1) 1` for `d ≥ 1` and `0` for `d = 0` (as a function: `k ↦ [k+1 = d]`);
  `tau N d = ∑ₚ tauP N (d p)`, i.e. the note's `τ = ∑_{p : d_p ≥ 1} e_{d_p}`, shifted to `Fin`.
* `dmap_ravA_add_tauP`: `D(shift^d v_j) + τ_d = e_{d+j}` (manuscript) = `Pi.single ⟨d+j−1⟩ 1`.
* `image_ra_eq_polyP` (**Lemma 1's polytope equality** `D(RA(𝟙; d⃗)) + τ = P(d⃗)`), with windows
  `win N (d p) n` (`Hall.lean`; manuscript `[d_p+1, d_p+n]`).  Hypothesis `d p + n ≤ N` for every
  `p` (the library's standing one); `d` unsorted, ties and gaps allowed, no `d = 0` summand needed,
  and `n = 0` allowed (both sides then degenerate together).  Unimodularity of `D` is not restated
  (`dmap_injective` in `Hall.lean`; `tailSum` below is the inverse).

**Corollary (stretch)**, the H-description of `RA(𝟙; d⃗)` itself (`1 ≤ n`, `d p + n ≤ N`):

* `mem_ra_iff`: `x ∈ RA ↔ ∑_k (Dx + τ)_k = r ∧ ∀ J, ∑_{k∈J} (Dx + τ)_k ≤ f(J)`, where
  `(Dx)_k = x_k − x_{k+1}` (`x_{N+1} := 0`), i.e. `RA = (D · + τ)⁻¹(Q)`;
  `mem_ra_iff'` the same with the lower bounds `g(K)`.
* `tailSum y k = ∑_{l ≥ k} y l` (the note's `x_k = ∑_{l ≥ k} y_l`), `dmap_tailSum`,
  `tailSum_dmap` (the two are mutually inverse), and `ra_eq_image_tailSum`:
  `RA(𝟙; d⃗) = {tailSum (y − τ) : y ∈ Q}`.

The note's specialisation to sorted `d` with `d₁ = 0`, `N = n + d_r` is a special case throughout.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.AllOnes.Hall

namespace ExteriorConvex.AllOnes

open Finset Pointwise

/-! ## Theorem A -/

section TheoremA

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

/-- The coordinate simplex `Δ_I = conv{e_i : i ∈ I}`. -/
def simplexOn (I : Finset ι) : Set (ι → ℝ) :=
  convexHull ℝ ((fun i => (Pi.single i (1 : ℝ) : ι → ℝ)) '' (I : Set ι))

/-- The note's `P = ∑ₚ Δ_{W_p}`. -/
def polyP (W : κ → Finset ι) : Set (ι → ℝ) := ∑ p, simplexOn (W p)

/-- The note's `Q = {y : y([N]) = r, y(J) ≤ f(J) ∀ J}`. -/
def polyQ (W : κ → Finset ι) : Set (ι → ℝ) :=
  {y | ∑ i, y i = Fintype.card κ ∧ ∀ J : Finset ι, ∑ i ∈ J, y i ≤ cover W J}

/-- The note's `g(K) = #{p : W_p ⊆ K}`. -/
def lowerCover (W : κ → Finset ι) (K : Finset ι) : ℕ := (univ.filter fun p => W p ⊆ K).card

/-- The lower-bound description `{y : y([N]) = r, y(K) ≥ g(K) ∀ K}`. -/
def polyQ' (W : κ → Finset ι) : Set (ι → ℝ) :=
  {y | ∑ i, y i = Fintype.card κ ∧ ∀ K : Finset ι, (lowerCover W K : ℝ) ≤ ∑ i ∈ K, y i}

/-- `y(J)` as a linear functional. -/
def sumJ (J : Finset ι) : (ι → ℝ) →ₗ[ℝ] ℝ :=
  ∑ k ∈ J, LinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) k

omit [Fintype ι] [DecidableEq ι] in
lemma sumJ_apply (J : Finset ι) (y : ι → ℝ) : sumJ J y = ∑ k ∈ J, y k := by
  simp [sumJ]

omit [Fintype ι] in
lemma sumJ_single (J : Finset ι) (i : ι) :
    sumJ J (Pi.single i (1 : ℝ)) = if i ∈ J then 1 else 0 := by
  rw [sumJ_apply, sum_pi_single']

/-- `f(univ ∖ K) + g(K) = r`, i.e. `g(K) = r − f([N] ∖ K)`. -/
lemma cover_compl_add_lowerCover (W : κ → Finset ι) (K : Finset ι) :
    cover W (univ \ K) + lowerCover W K = Fintype.card κ := by
  have hneg : (univ.filter fun p => W p ⊆ K)
      = univ.filter fun p => ¬ (W p ∩ (univ \ K)).Nonempty := by
    ext p
    simp only [mem_filter, mem_univ, true_and, not_nonempty_iff_eq_empty]
    constructor
    · intro h; ext i; simp only [mem_inter, mem_sdiff, mem_univ, true_and]
      simp only [Finset.notMem_empty, iff_false, not_and, not_not]; exact fun hi => h hi
    · intro h i hi
      by_contra hk
      have : i ∈ W p ∩ (univ \ K) := by simp [hi, hk]
      rw [h] at this; simp at this
  rw [lowerCover, hneg, cover, card_filter_add_card_filter_not, card_univ]

/-- The upper- and lower-bound descriptions of `Q` agree. -/
theorem polyQ_eq_polyQ' (W : κ → Finset ι) : polyQ W = polyQ' W := by
  ext y
  simp only [polyQ, polyQ', Set.mem_ofPred_eq]
  refine and_congr_right fun hsum => ?_
  have key : ∀ K : Finset ι, ∑ i ∈ univ \ K, y i + ∑ i ∈ K, y i = Fintype.card κ := by
    intro K; rw [← hsum, sum_sdiff (subset_univ K)]
  have key2 : ∀ K : Finset ι, (cover W (univ \ K) : ℝ) + lowerCover W K = Fintype.card κ := by
    intro K; exact_mod_cast cover_compl_add_lowerCover W K
  constructor
  · intro h K; have := h (univ \ K); have := key K; have := key2 K; linarith
  · intro h J
    have h1 := h (univ \ J); have h2 := key (univ \ J); have h3 := key2 (univ \ J)
    rw [Finset.sdiff_sdiff_eq_self (subset_univ J)] at h2 h3
    linarith

/-- **Theorem A, `P ⊆ Q`.** No nonemptiness of the windows is needed. -/
theorem polyP_subset_polyQ (W : κ → Finset ι) : polyP W ⊆ polyQ W := by
  intro y hy
  have hgen : ∀ p, ∀ z ∈ (fun i => (Pi.single i (1 : ℝ) : ι → ℝ)) '' (W p : Set ι),
      ∃ i ∈ W p, z = Pi.single i 1 := by
    rintro p z ⟨i, hi, rfl⟩; exact ⟨i, hi, rfl⟩
  have hJ : ∀ J : Finset ι, ∑ i ∈ J, y i ≤ cover W J := by
    intro J
    have := le_of_mem_sum_convexHull _ (sumJ J)
      (fun p => if (W p ∩ J).Nonempty then 1 else 0) ?_ hy
    · rwa [sumJ_apply, sum_boole] at this
    · intro p z hz
      obtain ⟨i, hi, rfl⟩ := hgen p z hz
      rw [sumJ_single]
      split_ifs with h1 h2 h2
      · exact le_rfl
      · exact absurd ⟨i, mem_inter.2 ⟨hi, h1⟩⟩ h2
      · exact zero_le_one
      · exact le_rfl
  refine ⟨le_antisymm ?_ ?_, hJ⟩
  · have := hJ univ
    have hc : cover W univ ≤ Fintype.card κ := card_le_univ _
    calc _ ≤ _ := this
      _ ≤ _ := by exact_mod_cast hc
  · have := le_of_mem_sum_convexHull _ (-sumJ univ) (fun _ => -1) ?_ hy
    · simp only [LinearMap.neg_apply, sumJ_apply, sum_neg_distrib, sum_const, card_univ,
        nsmul_eq_mul, mul_one] at this
      linarith
    · intro p z hz
      obtain ⟨i, hi, rfl⟩ := hgen p z hz
      rw [LinearMap.neg_apply, sumJ_single]; simp

omit [Fintype κ] in
lemma isCompact_finsetSum {E : Type*} [AddCommGroup E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] (s : Finset κ) (S : κ → Set E) (h : ∀ p, IsCompact (S p)) :
    IsCompact (∑ p ∈ s, S p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert p s hp ih => rw [sum_insert hp]; exact (h p).add ih

omit [Fintype ι] in
lemma isCompact_polyP (W : κ → Finset ι) : IsCompact (polyP W) :=
  isCompact_finsetSum _ _ fun p => ((W p).finite_toSet.image _).isCompact_convexHull ℝ

omit [Fintype ι] in
lemma convex_polyP (W : κ → Finset ι) : Convex ℝ (polyP W) :=
  convex_sum _ fun _ _ => convex_convexHull ℝ _

/-- **Theorem A, `Q ⊆ P`**: the note's support-function argument, closed by Hahn–Banach. -/
theorem polyQ_subset_polyP (W : κ → Finset ι) (hW : ∀ p, (W p).Nonempty) :
    polyQ W ⊆ polyP W := by
  rintro y ⟨hsum, hJ⟩
  by_contra hy
  obtain ⟨f, u, hfy, hfb⟩ := geometric_hahn_banach_point_closed (convex_polyP W)
    (isCompact_polyP W).isClosed hy
  have hf : ∀ z : ι → ℝ, f z = ∑ i, z i * f (Pi.single i 1) := by
    intro z
    have := LinearMap.pi_apply_eq_sum_univ (f : (ι → ℝ) →ₗ[ℝ] ℝ) z
    rw [ContinuousLinearMap.coe_coe] at this
    rw [this]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul]
    congr 2
    funext j
    simp [Pi.single_apply, eq_comm]
  let c : ι → ℝ := fun i => -f (Pi.single i 1)
  choose m hmW hm using fun p => exists_mem_eq_sup' (hW p) c
  have hb : (∑ p, (Pi.single (m p) (1 : ℝ) : ι → ℝ)) ∈ polyP W :=
    (Set.mem_finsetSum _ _ _).2 ⟨fun p => Pi.single (m p) 1,
      fun {p} _ => subset_convexHull ℝ _ ⟨m p, hmW p, rfl⟩, rfl⟩
  have h1 := hfb _ hb
  have h2 := dot_le_sum_sup' W hW y hsum hJ c
  have h3 : f (∑ p, (Pi.single (m p) (1 : ℝ) : ι → ℝ)) = -∑ p, (W p).sup' (hW p) c := by
    rw [map_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [hm p]; simp [c]
  have h4 : ∑ i, c i * y i = -f y := by
    rw [hf y, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp [c]; ring
  linarith

/-- **Theorem A** (`thm-A`): `∑ₚ Δ_{W_p} = {y : y([N]) = r, y(J) ≤ f(J) ∀ J}`. -/
theorem polyP_eq_polyQ (W : κ → Finset ι) (hW : ∀ p, (W p).Nonempty) :
    polyP W = polyQ W :=
  (polyP_subset_polyQ W).antisymm (polyQ_subset_polyP W hW)

/-- **Theorem A**, lower-bound form: `∑ₚ Δ_{W_p} = {y : y([N]) = r, y(K) ≥ g(K) ∀ K}`. -/
theorem polyP_eq_polyQ' (W : κ → Finset ι) (hW : ∀ p, (W p).Nonempty) :
    polyP W = polyQ' W := by
  rw [polyP_eq_polyQ W hW, polyQ_eq_polyQ']

end TheoremA

/-! ## Lemma 1: the coordinate change -/

section Lemma1

variable {κ : Type*} [Fintype κ]

/-- The translation of one summand: `e_d` (manuscript index) if `d ≥ 1`, i.e. `Fin` index `d − 1`;
`0` if `d = 0`. -/
def tauP (N d : ℕ) : Fin N → ℝ := fun k => if k.val + 1 = d then 1 else 0

/-- The note's `τ = ∑_{p : d_p ≥ 1} e_{d_p}` (manuscript indices). -/
def tau (N : ℕ) (d : κ → ℕ) : Fin N → ℝ := ∑ p, tauP N (d p)

/-- The library's `RA(𝟙; d⃗) = ∑ₚ shift^{d_p}(∠(𝟙(n)))`. -/
def ra (N : ℕ) (d : κ → ℕ) (n : ℕ) : Set (Fin N → ℝ) :=
  ∑ p, convexHull ℝ (vsetA (fun _ => 1) N (d p) n)

/-- The affine map `x ↦ Dx + τ_d` of one summand. -/
def dAff (N d : ℕ) : (Fin N → ℝ) →ᵃ[ℝ] (Fin N → ℝ) :=
  (dmap N).toAffineMap + AffineMap.const ℝ (Fin N → ℝ) (tauP N d)

lemma dAff_apply (N d : ℕ) (x : Fin N → ℝ) : dAff N d x = dmap N x + tauP N d := rfl

/-- `D(shift^d v_j) + τ_d = e_{d+j}` (manuscript index), i.e. `Fin` index `d + j − 1`. -/
lemma dmap_ravA_add_tauP {N : ℕ} (d j : ℕ) (hj : 1 ≤ j) (hdj : d + j ≤ N) :
    dmap N (ravA (fun _ => 1) N d j) + tauP N d = Pi.single ⟨d + j - 1, by omega⟩ 1 := by
  funext k
  rw [Pi.add_apply, dmap_ravA d j hj hdj, tauP, Pi.single_apply]
  simp only [Fin.ext_iff]
  split_ifs <;> ring

lemma dAff_image_vsetA {N : ℕ} (d n : ℕ) (hN : d + n ≤ N) :
    dAff N d '' vsetA (fun _ => 1) N d n
      = (fun i => (Pi.single i (1 : ℝ) : Fin N → ℝ)) '' (win N d n : Set (Fin N)) := by
  ext z
  constructor
  · rintro ⟨_, ⟨j, ⟨hj1, hjn⟩, rfl⟩, rfl⟩
    refine ⟨⟨d + j - 1, by omega⟩, ?_, ?_⟩
    · simp only [win, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq]; omega
    · rw [dAff_apply, dmap_ravA_add_tauP d j hj1 (by omega)]
  · rintro ⟨k, hk, rfl⟩
    simp only [win, coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk
    refine ⟨_, ravA_mem_vsetA (k := k.val + 1 - d) (by omega) (by omega), ?_⟩
    rw [dAff_apply, dmap_ravA_add_tauP d _ (by omega) (by omega)]
    congr 1; ext; simp; omega

lemma dAff_image_convexHull {N : ℕ} (d n : ℕ) (hN : d + n ≤ N) :
    dAff N d '' convexHull ℝ (vsetA (fun _ => 1) N d n) = simplexOn (win N d n) := by
  rw [AffineMap.image_convexHull, dAff_image_vsetA d n hN, simplexOn]

/-- **Lemma 1** (`lem-coords`), the polytope equality `D(RA(𝟙; d⃗)) + τ = P(d⃗)`. -/
theorem image_ra_eq_polyP {N : ℕ} (d : κ → ℕ) (n : ℕ) (hN : ∀ p, d p + n ≤ N) :
    (fun x => dmap N x + tau N d) '' ra N d n = polyP (fun p => win N (d p) n) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum _ _ _).1 hx
    refine (Set.mem_finsetSum _ _ _).2 ⟨fun p => dAff N (d p) (g p), fun {p} _ => ?_, ?_⟩
    · rw [← dAff_image_convexHull (d p) n (hN p)]
      exact Set.mem_image_of_mem _ (hg (mem_univ p))
    · simp only [dAff_apply, sum_add_distrib, map_sum, tau]
  · intro hy
    obtain ⟨h, hh, rfl⟩ := (Set.mem_finsetSum _ _ _).1 hy
    have : ∀ p, ∃ x ∈ convexHull ℝ (vsetA (fun _ => 1) N (d p) n), dAff N (d p) x = h p := by
      intro p
      have := hh (mem_univ p)
      rwa [← dAff_image_convexHull (d p) n (hN p)] at this
    choose g hg hgh using this
    refine ⟨∑ p, g p, (Set.mem_finsetSum _ _ _).2 ⟨g, fun {p} _ => hg p, rfl⟩, ?_⟩
    simp only [← hgh, dAff_apply, sum_add_distrib, map_sum, tau]

/-! ## Corollary: the H-description of `RA(𝟙; d⃗)` in `x`-coordinates -/

/-- The inverse of `D`: `x_k = ∑_{l ≥ k} y_l`. -/
def tailSum {N : ℕ} (y : Fin N → ℝ) : Fin N → ℝ := fun k => ∑ l ∈ univ.filter (k ≤ ·), y l

lemma dmap_tailSum {N : ℕ} (y : Fin N → ℝ) : dmap N (tailSum y) = y := by
  funext k
  rw [dmap_apply]
  by_cases h : k.val + 1 < N
  · have hk : ext0 (tailSum y) (k.val + 1) = tailSum y ⟨k.val + 1, h⟩ := ext0_of_lt _ ⟨_, h⟩
    rw [hk, tailSum, tailSum]
    have hs : univ.filter (k ≤ ·) = insert k (univ.filter ((⟨k.val + 1, h⟩ : Fin N) ≤ ·)) := by
      ext l; simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.le_iff_val_le_val,
        Fin.ext_iff]; omega
    rw [hs, sum_insert (by simp [Fin.le_iff_val_le_val])]
    ring
  · have hk : ext0 (tailSum y) (k.val + 1) = 0 := by simp [ext0, h]
    rw [hk, sub_zero, tailSum]
    have hs : univ.filter (k ≤ ·) = {k} := by
      ext l; simp only [mem_filter, mem_univ, true_and, mem_singleton, Fin.le_iff_val_le_val,
        Fin.ext_iff]; have := l.isLt; omega
    rw [hs, sum_singleton]

lemma tailSum_dmap {N : ℕ} (x : Fin N → ℝ) : tailSum (dmap N x) = x :=
  dmap_injective (dmap_tailSum _)

/-- **H-description of `RA(𝟙; d⃗)`** (Lemma 1 + Theorem A): `RA = (D · + τ)⁻¹(Q)`, i.e.
`x ∈ RA` iff `∑_k (x_k − x_{k+1} + τ_k) = r` and `∑_{k∈J} (x_k − x_{k+1} + τ_k) ≤ f(J)` for all
`J`. -/
theorem mem_ra_iff {N : ℕ} (d : κ → ℕ) (n : ℕ) (hn : 1 ≤ n) (hN : ∀ p, d p + n ≤ N)
    (x : Fin N → ℝ) :
    x ∈ ra N d n ↔
      (∑ k, (dmap N x k + tau N d k) = Fintype.card κ ∧
        ∀ J : Finset (Fin N), ∑ k ∈ J, (dmap N x k + tau N d k) ≤ cover (fun p => win N (d p) n) J) := by
  have hW : ∀ p, (win N (d p) n).Nonempty := fun p =>
    ⟨⟨d p, by have := hN p; omega⟩, by simp [win]; omega⟩
  have hinj : Function.Injective (fun x : Fin N → ℝ => dmap N x + tau N d) := by
    intro x x' h; exact dmap_injective (add_right_cancel h)
  have := image_ra_eq_polyP d n hN
  rw [polyP_eq_polyQ _ hW] at this
  rw [← hinj.mem_set_image, this]
  rfl

/-- The same, with the lower bounds `y(K) ≥ g(K)`. -/
theorem mem_ra_iff' {N : ℕ} (d : κ → ℕ) (n : ℕ) (hn : 1 ≤ n) (hN : ∀ p, d p + n ≤ N)
    (x : Fin N → ℝ) :
    x ∈ ra N d n ↔
      (∑ k, (dmap N x k + tau N d k) = Fintype.card κ ∧
        ∀ K : Finset (Fin N), (lowerCover (fun p => win N (d p) n) K : ℝ)
          ≤ ∑ k ∈ K, (dmap N x k + tau N d k)) := by
  rw [mem_ra_iff d n hn hN]
  have := Set.ext_iff.1 (polyQ_eq_polyQ' (fun p => win N (d p) n)) (dmap N x + tau N d)
  exact this

/-- **`RA(𝟙; d⃗)` as the image of `Q` under `y ↦ x`, `x_k = ∑_{l ≥ k} (y_l − τ_l)`.** -/
theorem ra_eq_image_tailSum {N : ℕ} (d : κ → ℕ) (n : ℕ) (hn : 1 ≤ n) (hN : ∀ p, d p + n ≤ N) :
    ra N d n = (fun y => tailSum (y - tau N d)) '' polyQ (fun p => win N (d p) n) := by
  ext x
  rw [mem_ra_iff d n hn hN]
  constructor
  · intro hx
    refine ⟨dmap N x + tau N d, hx, ?_⟩
    simp only [add_sub_cancel_right, tailSum_dmap]
  · rintro ⟨y, hy, rfl⟩
    have : dmap N (tailSum (y - tau N d)) + tau N d = y := by
      rw [dmap_tailSum, sub_add_cancel]
    have h := congrFun this
    simp only [Pi.add_apply] at h
    simp only [h]
    exact hy

end Lemma1

end ExteriorConvex.AllOnes
