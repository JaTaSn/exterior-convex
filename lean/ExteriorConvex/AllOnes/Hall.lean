/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The all-ones polytope: Hall's theorem (Corollary C) and the Abel-summation inequality (Theorem A)

Formalises two results of `working-notes/allones-hdescription-generalized-permutohedra.org`
(note labels in brackets).

**Combinatorial layer** — an arbitrary finite index set `ι` of coordinates and an arbitrary finite
family of "windows" `W : κ → Finset ι` (any finite sets: empty, repeated, non-interval windows all
allowed; the number of summands is `r = Fintype.card κ`).  `cover W J` is the note's coverage
function `f(J) = #{p : W_p ∩ J ≠ ∅}`, `mult c` the multiplicity vector `∑ₚ e_{c p}` of a choice.

* `exists_choice_of_le_cover` (`cor-C`, combinatorial form, ℕ): if `y : ι → ℕ` has `∑ y = r` and
  `y(J) ≤ f(J)` for every `J`, there is `c p ∈ W p` with `y = ∑ₚ e_{c p}`.  Hall's theorem
  (`Finset.all_card_le_biUnion_card_iff_exists_injective`) on the multiset `Σ i, Fin (y i)`.
* `le_cover_iff_exists_choice`: the same as an iff (the converse is the easy `P ⊆ Q` direction).
* `exists_choice_of_le_cover_real`: the version for real `y` with integer entries — the note's
  `P ∩ ℤ^N ⊆ sumset` step, including its derivation of `y_i ≥ 0` from `J = [N] ∖ {i}`.
* `dot_le_sum_sup'` (`thm-A`, the `Q ⊆ P` validity inequality): for `y : ι → ℝ` in the note's
  `Q = {y : y([N]) = r, y(J) ≤ f(J) ∀ J}` and nonempty windows, `c · y ≤ ∑ₚ max_{W_p} c` for every
  `c`.  **Proof differs from the note's:** instead of sorting `c` and Abel-summing, induct on the
  number of distinct values of `c`, raising the minimum level `v` to the next value `u`; this uses
  only the inequalities for the super-level sets `{c > v}`, exactly the sets `S_k` the note's
  Abel summation uses.  The separation-theorem step that turns this into `Q ⊆ P` is not formalised.

**Polytope layer** (`cor-C` as printed, in the library's objects).  `RA(𝟙; d⃗)` is
`∑ₚ convexHull ℝ (vsetA (fun _ => 1) N (d p) n)` (degree-0-dropped coordinates, `Fin N`,
`Fin` index `k` ↔ manuscript coordinate `k+1`, as in `Vertices/ExtremalMatrix.lean`).

* `dmap` is the note's `D` (`lem-coords`), `(Dx)_k = x_k − x_{k+1}`; `dmap_injective`,
  `dmap_ravA` (`D(shift^d v_j) = e_{d+j} − e_d`, manuscript indices).  Lemma 1's polytope equality
  `D(RA) + τ = P(d⃗)` itself is not stated; only the two inclusions needed are used.
* `lattice_points_eq_sumset`: for any `d : κ → ℕ` with `d p + n ≤ N` (ties, gaps, unsorted shifts,
  no `d = 0` summand required),
  `RA(𝟙; d⃗) ∩ ℤ^N = ∑ₚ {shift^{d p}(v_j) : 1 ≤ j ≤ n}` (Minkowski sum of the vertex sets).
  The hypothesis `d p + n ≤ N` is the library's standing one (`RankR.lean`); the note's
  `N = n + d_r` is a special case.

Changelog (newest first): 2026-10-21 header note: the separation step and Lemma 1's set equality,
marked "not formalised" above, are now in `AllOnes/TheoremA.lean` (coordinator).
2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Vertices.ExtremalMatrix

namespace ExteriorConvex.AllOnes

open Finset Pointwise

section Combinatorial

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The coverage function `f(J) = #{p : W_p ∩ J ≠ ∅}`. -/
def cover (W : κ → Finset ι) (J : Finset ι) : ℕ :=
  (univ.filter fun p => (W p ∩ J).Nonempty).card

/-- The multiplicity vector `∑_p e_{c p}` of a choice `c`, as a function `ι → ℕ`. -/
def mult (c : κ → ι) (i : ι) : ℕ := (univ.filter fun p => c p = i).card

/-- **Corollary C, combinatorial form (Hall).**  If `∑ y = r` and `y(J) ≤ f(J)` for every `J`, then
`y = ∑ₚ e_{c p}` for some choice `c p ∈ W p`.  The windows are arbitrary finite sets. -/
theorem exists_choice_of_le_cover (W : κ → Finset ι) (y : ι → ℕ)
    (hsum : ∑ i, y i = Fintype.card κ)
    (hJ : ∀ J : Finset ι, ∑ i ∈ J, y i ≤ cover W J) :
    ∃ c : κ → ι, (∀ p, c p ∈ W p) ∧ ∀ i, y i = mult c i := by
  let T := Σ i : ι, Fin (y i)
  let t : T → Finset κ := fun x => univ.filter fun p => x.1 ∈ W p
  have hall : ∀ s : Finset T, s.card ≤ (s.biUnion t).card := by
    intro s
    set J := s.image Sigma.fst with hJdef
    have h1 : s.card ≤ ∑ i ∈ J, y i := by
      calc s.card ≤ (J.sigma fun i => (univ : Finset (Fin (y i)))).card := by
            apply card_le_card
            intro x hx
            rw [Finset.mem_sigma]
            exact ⟨Finset.mem_image_of_mem _ hx, Finset.mem_univ _⟩
        _ = ∑ i ∈ J, y i := by simp [card_sigma]
    have h2 : s.biUnion t = univ.filter fun p => (W p ∩ J).Nonempty := by
      ext p
      simp only [mem_biUnion, mem_filter, mem_univ, true_and, t, J, Finset.Nonempty, mem_inter,
        mem_image]
      constructor
      · rintro ⟨x, hx, hp⟩; exact ⟨x.1, hp, x, hx, rfl⟩
      · rintro ⟨i, hp, x, hx, rfl⟩; exact ⟨x, hx, hp⟩
    calc s.card ≤ _ := h1
      _ ≤ cover W J := hJ J
      _ = _ := by rw [h2]; rfl
  obtain ⟨g, hg, hgt⟩ := (all_card_le_biUnion_card_iff_exists_injective t).1 hall
  have hcard : Fintype.card T = Fintype.card κ := by simp [T, Fintype.card_sigma, hsum]
  have hbij : Function.Bijective g := (Fintype.bijective_iff_injective_and_card g).2 ⟨hg, hcard⟩
  let e := Equiv.ofBijective g hbij
  refine ⟨fun p => (e.symm p).1, fun p => ?_, fun i => ?_⟩
  · have h := hgt (e.symm p)
    have he : g (e.symm p) = p := e.apply_symm_apply p
    simp only [t, mem_filter, mem_univ, true_and] at h
    rwa [he] at h
  · have hmap : (univ.filter fun p => (e.symm p).1 = i).map e.symm.toEmbedding
        = ({i} : Finset ι).sigma fun i => (univ : Finset (Fin (y i))) := by
      ext x
      simp only [mem_filter, mem_univ, true_and, mem_map, Equiv.toEmbedding_apply]
      constructor
      · rintro ⟨p, hp, rfl⟩
        exact Finset.mem_sigma.2 ⟨Finset.mem_singleton.2 hp, mem_univ _⟩
      · intro hx
        refine ⟨e x, ?_, by simp⟩
        simpa using (Finset.mem_singleton.1 (Finset.mem_sigma.1 hx).1)
    have := congrArg Finset.card hmap
    rw [card_map, card_sigma] at this
    simp only [sum_singleton, card_univ, Fintype.card_fin] at this
    exact this.symm

omit [Fintype ι] [DecidableEq κ] in
/-- `y(J) = #{p : c p ∈ J}` for a multiplicity vector. -/
lemma sum_mult (c : κ → ι) (J : Finset ι) :
    ∑ i ∈ J, mult c i = (univ.filter fun p => c p ∈ J).card := by
  have H : ∀ p ∈ univ.filter (fun p => c p ∈ J), c p ∈ J := fun p hp => (mem_filter.1 hp).2
  rw [card_eq_sum_card_fiberwise H]
  refine sum_congr rfl fun i hi => ?_
  unfold mult
  congr 1
  ext p
  simp only [mem_filter, mem_univ, true_and]
  exact ⟨fun h => ⟨h ▸ hi, h⟩, fun h => h.2⟩

/-- **Corollary C, combinatorial form, as an iff.**  For `y : ι → ℕ`, `y` is a sum `∑ₚ e_{c p}` of
one basis vector per window iff `∑ y = r` and `y(J) ≤ f(J)` for every `J`. -/
theorem le_cover_iff_exists_choice (W : κ → Finset ι) (y : ι → ℕ) :
    (∑ i, y i = Fintype.card κ ∧ ∀ J : Finset ι, ∑ i ∈ J, y i ≤ cover W J) ↔
      ∃ c : κ → ι, (∀ p, c p ∈ W p) ∧ ∀ i, y i = mult c i := by
  constructor
  · rintro ⟨h1, h2⟩; exact exists_choice_of_le_cover W y h1 h2
  · rintro ⟨c, hc, hy⟩
    obtain rfl : y = mult c := funext hy
    refine ⟨?_, fun J => ?_⟩
    · rw [sum_mult]; simp
    · rw [sum_mult]
      refine card_le_card fun p hp => ?_
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      exact ⟨c p, mem_inter.2 ⟨hc p, hp⟩⟩

/-- **Corollary C, the integer-point step for real `y`.**  An integer point of the note's `Q` is a
sum of one basis vector per window.  Nonnegativity is derived, as in the note, from `J = [N]∖{i}`. -/
theorem exists_choice_of_le_cover_real (W : κ → Finset ι) (y : ι → ℝ)
    (hint : ∀ i, ∃ z : ℤ, y i = z)
    (hsum : ∑ i, y i = Fintype.card κ)
    (hJ : ∀ J : Finset ι, ∑ i ∈ J, y i ≤ cover W J) :
    ∃ c : κ → ι, (∀ p, c p ∈ W p) ∧ ∀ i, y i = mult c i := by
  have hnn : ∀ i, 0 ≤ y i := by
    intro i
    have h1 := hJ (univ.erase i)
    have h2 : (cover W (univ.erase i) : ℝ) ≤ Fintype.card κ := by
      exact_mod_cast (card_le_univ _ : cover W (univ.erase i) ≤ Fintype.card κ)
    have h3 := add_sum_erase univ y (mem_univ i)
    linarith
  choose z hz using hint
  have hzn : ∀ i, ((z i).toNat : ℝ) = y i := fun i => by
    have : 0 ≤ z i := by have := hnn i; rw [hz i] at this; exact_mod_cast this
    rw [hz i]; exact_mod_cast Int.toNat_of_nonneg this
  obtain ⟨c, hc, hy⟩ := exists_choice_of_le_cover W (fun i => (z i).toNat)
    (by exact_mod_cast (show ((∑ i, (z i).toNat : ℕ) : ℝ) = Fintype.card κ by
      push_cast; simp only [hzn]; exact hsum))
    (fun J => by
      have : ((∑ i ∈ J, (z i).toNat : ℕ) : ℝ) ≤ cover W J := by
        push_cast; simp only [hzn]; exact hJ J
      exact_mod_cast this)
  exact ⟨c, hc, fun i => by rw [← hzn i, hy i]⟩

omit [DecidableEq κ] in
/-- **Theorem A, the validity inequality behind `Q ⊆ P`.**  If `y([N]) = r` and `y(J) ≤ f(J)` for
all `J`, then `c · y ≤ ∑ₚ max_{W_p} c = h_P(c)` for every `c`, provided every window is nonempty. -/
theorem dot_le_sum_sup' (W : κ → Finset ι) (hW : ∀ p, (W p).Nonempty) (y : ι → ℝ)
    (hsum : ∑ i, y i = Fintype.card κ)
    (hJ : ∀ J : Finset ι, ∑ i ∈ J, y i ≤ cover W J) (c : ι → ℝ) :
    ∑ i, c i * y i ≤ ∑ p, (W p).sup' (hW p) c := by
  induction hm : (univ.image c).card using Nat.strong_induction_on generalizing c with
  | _ m ih =>
  rcases isEmpty_or_nonempty ι with hι | hι
  · have : IsEmpty κ := ⟨fun p => by obtain ⟨i, -⟩ := hW p; exact hι.elim i⟩
    simp
  set v := (univ.image c).min' (univ_nonempty.image c) with hvdef
  have hv : ∀ i, v ≤ c i := fun i => min'_le _ _ (mem_image_of_mem c (mem_univ i))
  obtain ⟨i0, -, hi0⟩ := mem_image.1 (min'_mem (univ.image c) (univ_nonempty.image c))
  rw [← hvdef] at hi0
  set S := univ.filter fun i => v < c i with hSdef
  rcases S.eq_empty_or_nonempty with hS | hS
  · -- `c` is constant
    have hc : ∀ i, c i = v := by
      intro i
      refine le_antisymm ?_ (hv i)
      by_contra h
      have : i ∈ S := by simp [S]; exact lt_of_not_ge h
      simp [hS] at this
    rw [sum_congr rfl fun i _ => by rw [hc i],
      sum_congr rfl fun p _ => (sup'_congr (hW p) rfl fun i _ => hc i).trans (sup'_const _ _)]
    rw [← mul_sum, hsum, sum_const, card_univ, nsmul_eq_mul, mul_comm]
  set u := (S.image c).min' (hS.image c) with hudef
  have hu : ∀ i, v < c i → u ≤ c i := fun i h =>
    min'_le _ _ (mem_image_of_mem c (by simp [S, h]))
  obtain ⟨i1, hi1S, hi1⟩ := mem_image.1 (min'_mem (S.image c) (hS.image c))
  rw [← hudef] at hi1
  have hvu : v < u := by rw [← hi1]; simpa [S] using hi1S
  set c' : ι → ℝ := fun i => max (c i) u with hc'def
  -- fewer distinct values
  have hcard : (univ.image c').card < m := by
    have hsub : univ.image c' ⊆ (univ.image c).erase v := by
      intro x hx
      obtain ⟨i, -, rfl⟩ := mem_image.1 hx
      rcases lt_or_eq_of_le (hv i) with h | h
      · have : c' i = c i := max_eq_left (hu i h)
        rw [this]
        exact mem_erase.2 ⟨ne_of_gt h, mem_image_of_mem c (mem_univ i)⟩
      · have : c' i = u := max_eq_right (by rw [← h]; exact hvu.le)
        rw [this]
        exact mem_erase.2 ⟨ne_of_gt hvu, hi1 ▸ mem_image_of_mem c (mem_univ i1)⟩
    calc (univ.image c').card ≤ ((univ.image c).erase v).card := card_le_card hsub
      _ < m := by
        rw [← hm]
        exact card_erase_lt_of_mem (hi0 ▸ mem_image_of_mem c (mem_univ i0))
  have hrec := ih _ hcard c' rfl
  set L := univ.filter fun i => ¬ v < c i with hLdef
  -- coordinatewise identity
  have hlhs : ∑ i, c i * y i = ∑ i, c' i * y i - (u - v) * ∑ i ∈ L, y i := by
    rw [sum_filter, mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun i _ => ?_
    by_cases h : v < c i
    · rw [if_neg (not_not.2 h), mul_zero, sub_zero]
      simp only [c', max_eq_left (hu i h)]
    · rw [if_pos h]
      have : c i = v := le_antisymm (not_lt.1 h) (hv i)
      simp only [c', this, max_eq_right hvu.le]
      ring
  -- coordinatewise identity for the maxima
  have hsup : ∀ p, (W p).sup' (hW p) c
      = (W p).sup' (hW p) c' - (u - v) * (if W p ⊆ L then 1 else 0) := by
    intro p
    split_ifs with hp
    · have h1 : ∀ i ∈ W p, c i = v := fun i hi =>
        le_antisymm (not_lt.1 (mem_filter.1 (hp hi)).2) (hv i)
      have h2 : ∀ i ∈ W p, c' i = u := fun i hi => by
        simp [c', h1 i hi, max_eq_right hvu.le]
      rw [sup'_congr (hW p) rfl h1, sup'_congr (hW p) rfl h2, sup'_const, sup'_const]
      ring
    · obtain ⟨i, hiW, hiL⟩ := not_subset.1 hp
      have hci : v < c i := by simpa [L] using hiL
      rw [mul_zero, sub_zero]
      refine le_antisymm (sup'_le _ _ fun j hj => (le_max_left _ _).trans (le_sup' c' hj)) ?_
      refine sup'_le _ _ fun j hj => max_le (le_sup' c hj) ((hu i hci).trans (le_sup' c hiW))
  have hrhs : ∑ p, (W p).sup' (hW p) c = ∑ p, (W p).sup' (hW p) c'
      - (u - v) * ((univ.filter fun p => W p ⊆ L).card : ℝ) := by
    rw [sum_congr rfl fun p _ => hsup p, sum_sub_distrib, ← mul_sum, sum_boole]
  -- the lower bound `y(L) ≥ g(L)`
  have hyL : ((univ.filter fun p => W p ⊆ L).card : ℝ) ≤ ∑ i ∈ L, y i := by
    have h1 : ∑ i ∈ S, y i + ∑ i ∈ L, y i = Fintype.card κ := by
      rw [← hsum]; exact sum_filter_add_sum_filter_not _ _ _
    have h2 : cover W S + (univ.filter fun p => W p ⊆ L).card = Fintype.card κ := by
      have hneg : (univ.filter fun p => W p ⊆ L)
          = univ.filter fun p => ¬ (W p ∩ S).Nonempty := by
        ext p
        rw [mem_filter, mem_filter, subset_iff, not_nonempty_iff_eq_empty,
          ← disjoint_iff_inter_eq_empty, disjoint_left]
        simp [L, S]
      rw [hneg, cover, card_filter_add_card_filter_not, card_univ]
    have h3 := hJ S
    have h2' : (cover W S : ℝ) + ((univ.filter fun p => W p ⊆ L).card : ℝ) = Fintype.card κ := by
      exact_mod_cast h2
    linarith
  rw [hlhs, hrhs]
  nlinarith

end Combinatorial

/-! ## The polytope `RA(𝟙; d⃗)` -/

section Polytope

variable {κ : Type*} [Fintype κ] [DecidableEq κ] {N : ℕ}

/-- Extension by zero of `x : Fin N → ℝ` to `ℕ`. -/
def ext0 (x : Fin N → ℝ) (k : ℕ) : ℝ := if h : k < N then x ⟨k, h⟩ else 0

lemma ext0_of_lt (x : Fin N → ℝ) (k : Fin N) : ext0 x k.val = x k := by
  simp [ext0, k.isLt]

/-- The note's difference map `D` (`lem-coords`): `(Dx)_k = x_k − x_{k+1}`, with `x_{N+1} := 0`
(manuscript indices). -/
def dmap (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) where
  toFun x k := x k - ext0 x (k.val + 1)
  map_add' x x' := by
    funext k; simp only [ext0, Pi.add_apply]; split_ifs <;> ring
  map_smul' t x := by
    funext k; simp only [ext0, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

lemma dmap_apply (x : Fin N → ℝ) (k : Fin N) : dmap N x k = x k - ext0 x (k.val + 1) := rfl

/-- `D` is injective (it is unitriangular). -/
lemma dmap_injective : Function.Injective (dmap N) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have key : ∀ m k, N ≤ k + m → ext0 z k = 0 := by
    intro m
    induction m with
    | zero => intro k hk; simp [ext0, show ¬ k < N by omega]
    | succ m ih =>
        intro k hk
        by_cases hkN : k < N
        · have h1 := congrFun hz ⟨k, hkN⟩
          rw [dmap_apply, Pi.zero_apply, ih (k + 1) (by omega), sub_zero] at h1
          simp [ext0, hkN, h1]
        · simp [ext0, hkN]
  funext k
  have := key N k.val (by omega)
  rwa [ext0_of_lt] at this

/-- `D` of an all-ones vertex: `D(shift^d v_j) = e_{d+j} − e_d` in manuscript indices, i.e.
`Fin` indices `d+j−1` and `d−1`, the second term absent for `d = 0`. -/
lemma dmap_ravA (d j : ℕ) (hj : 1 ≤ j) (hdj : d + j ≤ N) (k : Fin N) :
    dmap N (ravA (fun _ => 1) N d j) k
      = (if k.val = d + j - 1 then 1 else 0) - (if k.val + 1 = d then 1 else 0) := by
  rw [dmap_apply]
  have hk := k.isLt
  simp only [ext0, ravA]
  by_cases h : k.val + 1 < N
  · rw [dif_pos h]
    split_ifs <;> first | (exfalso; omega) | ring
  · rw [dif_neg h]
    split_ifs <;> first | (exfalso; omega) | ring
/-- The window of a summand shifted by `d`, in `Fin` indices: `{k : d ≤ k < d + n}`, i.e. the
manuscript's `W = [d+1, d+n]`. -/
def win (N d n : ℕ) : Finset (Fin N) := univ.filter fun k => d ≤ k.val ∧ k.val < d + n

omit [DecidableEq κ] in
/-- A linear functional bounded on each generating set is bounded on the Minkowski sum of their
convex hulls (the easy half of "support function of a sum is the sum of support functions"). -/
lemma le_of_mem_sum_convexHull {E : Type*} [AddCommGroup E] [Module ℝ E] (S : κ → Set E)
    (ℓ : E →ₗ[ℝ] ℝ) (b : κ → ℝ) (h : ∀ p, ∀ z ∈ S p, ℓ z ≤ b p) {x : E}
    (hx : x ∈ ∑ p, convexHull ℝ (S p)) : ℓ x ≤ ∑ p, b p := by
  obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum _ _ _).1 hx
  rw [map_sum]
  refine sum_le_sum fun p _ => ?_
  have hsub : convexHull ℝ (S p) ⊆ {w | ℓ w ≤ b p} :=
    convexHull_min (fun z hz => h p z hz) (convex_halfSpace_le ℓ.isLinear (b p))
  exact hsub (hg (mem_univ p))

/-- `y(J)` for `y = Dx`, as a linear functional of `x`. -/
def ellJ (N : ℕ) (J : Finset (Fin N)) : (Fin N → ℝ) →ₗ[ℝ] ℝ :=
  (∑ k ∈ J, LinearMap.proj (R := ℝ) (φ := fun _ : Fin N => ℝ) k) ∘ₗ dmap N

lemma ellJ_apply (J : Finset (Fin N)) (x : Fin N → ℝ) : ellJ N J x = ∑ k ∈ J, dmap N x k := by
  simp [ellJ]

/-- The shift contribution `[k + 1 = d]` summed over `J` (the manuscript's `τ(J)` for one summand). -/
def tauJ (d : ℕ) (J : Finset (Fin N)) : ℝ := ∑ k ∈ J, if k.val + 1 = d then 1 else 0

lemma sum_top_ind (d j : ℕ) (hj : 1 ≤ j) (hdj : d + j ≤ N) (J : Finset (Fin N)) :
    (∑ k ∈ J, if k.val = d + j - 1 then (1 : ℝ) else 0)
      = if (⟨d + j - 1, by omega⟩ : Fin N) ∈ J then 1 else 0 := by
  rw [← sum_ite_eq' J (⟨d + j - 1, by omega⟩ : Fin N) (fun _ => (1 : ℝ))]
  refine sum_congr rfl fun k _ => ?_
  simp only [Fin.ext_iff]

lemma ellJ_ravA (d j : ℕ) (hj : 1 ≤ j) (hdj : d + j ≤ N) (J : Finset (Fin N)) :
    ellJ N J (ravA (fun _ => 1) N d j)
      = (if (⟨d + j - 1, by omega⟩ : Fin N) ∈ J then 1 else 0) - tauJ d J := by
  rw [ellJ_apply, ← sum_top_ind d j hj hdj J, tauJ, ← sum_sub_distrib]
  exact sum_congr rfl fun k _ => dmap_ravA d j hj hdj k

/-- **Corollary C, polytope form.** The lattice points of `RA(𝟙; d⃗) = ∑ₚ shift^{dₚ}(∠(𝟙))`
are exactly the sums of summand vertices. -/
theorem lattice_points_eq_sumset (d : κ → ℕ) (n : ℕ) (hN : ∀ p, d p + n ≤ N) :
    (∑ p, convexHull ℝ (vsetA (fun _ => 1) N (d p) n)) ∩ {x | ∀ k, ∃ z : ℤ, x k = z}
      = ∑ p, vsetA (fun _ => 1) N (d p) n := by
  ext x
  constructor
  · rintro ⟨hx, hint⟩
    -- the generators, unpacked
    have hgen : ∀ p, ∀ z ∈ vsetA (fun _ => 1) N (d p) n, ∃ j, 1 ≤ j ∧ j ≤ n ∧
        z = ravA (fun _ => 1) N (d p) j := by
      rintro p z ⟨j, ⟨hj1, hjn⟩, rfl⟩; exact ⟨j, hj1, hjn, rfl⟩
    let τ : Fin N → ℝ := fun k => ∑ p, if k.val + 1 = d p then 1 else 0
    let y : Fin N → ℝ := fun k => dmap N x k + τ k
    have hτJ : ∀ J : Finset (Fin N), ∑ k ∈ J, τ k = ∑ p, tauJ (d p) J := by
      intro J; simp only [τ, tauJ]; exact sum_comm
    have hyJ : ∀ J, ∑ k ∈ J, y k = ellJ N J x + ∑ p, tauJ (d p) J := by
      intro J; rw [ellJ_apply, ← hτJ, ← sum_add_distrib]
    -- validity of `y(J) ≤ f(J)`
    have hle : ∀ J, ∑ k ∈ J, y k ≤ cover (fun p => win N (d p) n) J := by
      intro J
      have := le_of_mem_sum_convexHull _ (ellJ N J)
        (fun p => (if (win N (d p) n ∩ J).Nonempty then 1 else 0) - tauJ (d p) J) ?_ hx
      · rw [hyJ, cover, ← Finset.sum_boole (R := ℝ)]
        rw [sum_sub_distrib] at this
        linarith
      · intro p z hz
        obtain ⟨j, hj1, hjn, rfl⟩ := hgen p z hz
        have hpN := hN p
        rw [ellJ_ravA (d p) j hj1 (by omega)]
        gcongr
        split_ifs with h1 h2 h2
        · exact le_rfl
        · exact absurd ⟨_, mem_inter.2 ⟨by simp [win]; omega, h1⟩⟩ h2
        · exact zero_le_one
        · exact le_rfl
    -- the equation `y([N]) = r`
    have heq : ∑ k, y k = Fintype.card κ := by
      refine le_antisymm ((hle univ).trans ?_) ?_
      · have hc : cover (fun p => win N (d p) n) univ ≤ Fintype.card κ := card_le_univ _
        exact_mod_cast hc
      · have := le_of_mem_sum_convexHull _ (-ellJ N univ)
          (fun p => -(1 - tauJ (N := N) (d p) univ)) ?_ hx
        · rw [hyJ]
          simp only [LinearMap.neg_apply, sum_neg_distrib, sum_sub_distrib, sum_const,
            card_univ, nsmul_eq_mul, mul_one] at this
          linarith
        · intro p z hz
          obtain ⟨j, hj1, hjn, rfl⟩ := hgen p z hz
          have hpN := hN p
          rw [LinearMap.neg_apply, ellJ_ravA (d p) j hj1 (by omega), if_pos (mem_univ _)]
    -- integrality of `y`
    have hyint : ∀ k, ∃ z : ℤ, y k = z := by
      intro k
      obtain ⟨a, ha⟩ := hint k
      have hb : ∃ b : ℤ, ext0 x (k.val + 1) = b := by
        unfold ext0
        split_ifs with h
        · exact hint _
        · exact ⟨0, by simp⟩
      obtain ⟨b, hb⟩ := hb
      refine ⟨a - b + ∑ p, if k.val + 1 = d p then 1 else 0, ?_⟩
      simp only [y, τ, dmap_apply, ha, hb]
      push_cast
      ring
    -- Hall
    obtain ⟨c, hcW, hcy⟩ := exists_choice_of_le_cover_real (fun p => win N (d p) n) y hyint heq hle
    have hc : ∀ p, d p ≤ (c p).val ∧ (c p).val < d p + n := fun p => by
      simpa [win] using hcW p
    let j : κ → ℕ := fun p => (c p).val + 1 - d p
    have hj : ∀ p, 1 ≤ j p ∧ j p ≤ n ∧ d p + j p ≤ N ∧ d p + j p - 1 = (c p).val := fun p => by
      have := hc p; have := hN p; have := (c p).isLt; simp only [j]; omega
    refine (Set.mem_finsetSum _ _ _).2 ⟨fun p => ravA (fun _ => 1) N (d p) (j p),
      fun {p} _ => ravA_mem_vsetA (hj p).1 (hj p).2.1, ?_⟩
    apply dmap_injective
    funext k
    rw [map_sum, Finset.sum_apply]
    have h1 : ∀ p, dmap N (ravA (fun _ => 1) N (d p) (j p)) k
        = (if c p = k then 1 else 0) - (if k.val + 1 = d p then 1 else 0) := by
      intro p
      rw [dmap_ravA (d p) (j p) (hj p).1 (hj p).2.2.1, (hj p).2.2.2]
      congr 1
      simp only [Fin.ext_iff, eq_comm]
    rw [sum_congr rfl fun p _ => h1 p, sum_sub_distrib, sum_boole]
    have := hcy k
    simp only [y, mult] at this
    simp only [τ] at this
    linarith
  · intro hx
    obtain ⟨g, hg, rfl⟩ := (Set.mem_finsetSum _ _ _).1 hx
    refine ⟨(Set.mem_finsetSum _ _ _).2 ⟨g, fun {p} hp => subset_convexHull ℝ _ (hg hp), rfl⟩, ?_⟩
    intro k
    have : ∀ p, ∃ z : ℤ, g p k = z := by
      intro p
      obtain ⟨j, -, hj⟩ := hg (mem_univ p)
      rw [← hj]
      simp only [ravA]
      split_ifs
      · exact ⟨1, by simp⟩
      · exact ⟨0, by simp⟩
    choose z hz using this
    exact ⟨∑ p, z p, by rw [Finset.sum_apply]; push_cast; exact sum_congr rfl fun p _ => hz p⟩

end Polytope

end ExteriorConvex.AllOnes
