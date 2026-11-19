/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Module Kruskal–Katona (Part V): lexF segments, their shadows, the growth bound

Formalisation, at the level of monomial families, of the following statements of
`article/exterior-convex_article5_draft_1.org` (Part V, "Module Kruskal–Katona"):

* §`sec-lex`: `lexF` segments in the paper's concrete form (`IsLexFSeg`: greedy component sizes,
  lex-initial components), existence and uniqueness (`exists_isLexFSeg`, `isLexFSeg_unique`),
  nesting by size (`IsLexFSeg.forall₂_subset`); and the paper's definition, initial segments of
  `Mon_j(F)` for the position-over-term order (`IsLexFInitial`), shown equivalent
  (`isLexFInitial_iff`, `isLexFInitial_iff_exists`).
* `lem-lexF-shadow`: the componentwise upper shadow of a `lexF` segment is a `lexF` segment in the
  next degree (`lem_lexF_shadow`), and the nesting consequence (`lem_lexF_shadow_subset`).
* `def-B` in *shadow form* (`Bω`, and `Bωj` indexed by `(h, j)`): the Macaulay term `a^{(k_ℓ)}`
  replaced by `macShadow n k_ℓ a = C(n,k_ℓ+1) − ωₙ(k_ℓ, C(n,k_ℓ) − a)`. `growthB M` is `def-B` with
  an arbitrary Macaulay-term function `M` as a separate summand, so `def-B` itself is
  `growthB (fun k a => a^{(k)})`, and `growthB_congr` is the one-step glue to a file proving
  `macShadow n k a = a^{(k)}` for `a < C(n,k)`.
* `thm-module-kk` for monomial families: the formula (`thm_module_kk_formula`, from the identity
  `cost_greedy_add_Bω`) and the inequality (`thm_module_kk_ineq_mon`, `thm_module_kk_bound_mon`).
* `cor-prop41` for monomial submodules (`cor_prop41_mon`).
* `thm-ac42` for monomial submodules (`IsMonSubmodule`, `IsLexSubmodule`):
  (1_mon) ⇒ (2) `cor_prop41_mon`, (2) ⇒ (3) `thm_ac42_two_three`, uniqueness `thm_ac42_unique`,
  and the equivalence `thm_ac42_mon`.
* `cor-initial` (`cor_initial`, `cor_initial_growthB`, `cor_initial_instances`; the computation is
  `growthB_count`).
* Numerical anchors, entrywise: `ex-lexF-n3`, `ex-kk-n3-d01`, `ex-ac-smallest`.

Representation (as in `ModuleKK/LexShadow.lean`): a monomial family of `F_j` is a list
`𝒜s : List (Finset (Finset (Fin n)))` matched to the list `ks : List ℤ` of exterior degrees
`kᵢ = j − dᵢ` (`ks.Pairwise (· ≥ ·)`) by `List.Forall₂ Component ks 𝒜s`. No vector spaces here
(`lem-monomial`, the passage from subspaces to monomial families, is not formalised).

Observations (no defect found): `cor-initial`'s two evaluations hold for every `j₀ ∈ ℤ`, not only
the initial degree, and the second also for `h = 0`; in `thm-ac42` the equivalence holds for any
window `[d₁, d_r + n]` containing the support of `h` (the proof never uses `d₁ = min d`,
`d_r = max d`); in shadow form the convention `0^{(k)} = 0` is automatic (`macShadow_zero`).

Changelog (newest first): 2026-11-17 created (Claude-Code agent, lean-parts-4-5 run)
-/
import Mathlib
import ExteriorConvex.ModuleKK.GreedyPQ
import ExteriorConvex.ModuleKK.Greedy
import ExteriorConvex.ModuleKK.LexShadow

open Finset
open scoped FinsetFamily

namespace ExteriorConvex
namespace ModuleKK

/-! ### Greedy-shaped vectors -/

section Shape

variable {ι : Type*}

/-- `us` is *greedy-shaped* for the capacities `C` on the degree list `ks`: `uᵢ ≤ C kᵢ`, and
positive mass after position `i` forces `uᵢ = C kᵢ`. These are exactly the greedy vectors
(`greedyShape_greedy`, `GreedyShape.eq_greedy`). -/
def GreedyShape (C : ι → ℕ) : List ι → List ℕ → Prop
  | [], [] => True
  | k :: ks, u :: us => u ≤ C k ∧ (0 < us.sum → u = C k) ∧ GreedyShape C ks us
  | _, _ => False

lemma greedyShape_greedy (C : ι → ℕ) (ks : List ι) (T : ℕ) :
    GreedyShape C ks (greedy C ks T) := by
  induction ks generalizing T with
  | nil => simp [greedy, GreedyShape]
  | cons k ks ih =>
    simp only [greedy, GreedyShape]
    refine ⟨min_le_right _ _, fun h => ?_, ih _⟩
    rw [greedy_sum] at h
    omega

lemma GreedyShape.eq_greedy {C : ι → ℕ} : ∀ {ks : List ι} {us : List ℕ},
    GreedyShape C ks us → us = greedy C ks us.sum
  | [], [], _ => rfl
  | k :: ks, u :: us, h => by
    obtain ⟨h1, h2, h3⟩ := h
    have hmin : min (u + us.sum) (C k) = u := by
      rcases Nat.eq_zero_or_pos us.sum with h | h
      · omega
      · have := h2 h; omega
    simp only [List.sum_cons, greedy, hmin, Nat.add_sub_cancel_left]
    exact congrArg _ h3.eq_greedy
  | [], _ :: _, h => by simp [GreedyShape] at h
  | _ :: _, [], h => by simp [GreedyShape] at h

lemma greedy_mono (C : ι → ℕ) (ks : List ι) {T T' : ℕ} (h : T ≤ T') :
    List.Forall₂ (· ≤ ·) (greedy C ks T) (greedy C ks T') := by
  induction ks generalizing T T' with
  | nil => exact List.Forall₂.nil
  | cons k ks ih =>
    simp only [greedy]
    exact List.Forall₂.cons (by omega) (ih (by omega))

end Shape

/-! ### Capacities and costs of integer degrees -/

section CapCost

/-- `T_ℓ(j)` of §`sec-setup`: the total capacity `∑_{i > ℓ} C(n, kᵢ)` of the components after
position `ℓ` (1-indexed in the paper; here the components `ks.drop ℓ`). `tailCap n ks 0` is
`dim F_j`, and `tailCap n (ks.map (· + 1)) ℓ` is `T_ℓ(j+1)`. -/
def tailCap (n : ℕ) (ks : List ℤ) (ℓ : ℕ) : ℕ := ((ks.drop ℓ).map (capZ n)).sum

variable {n : ℕ}

@[simp] lemma tailCap_nil (ℓ : ℕ) : tailCap n [] ℓ = 0 := by simp [tailCap]

@[simp] lemma tailCap_cons_zero (k : ℤ) (ks : List ℤ) :
    tailCap n (k :: ks) 0 = capZ n k + tailCap n ks 0 := by simp [tailCap]

@[simp] lemma tailCap_cons_succ (k : ℤ) (ks : List ℤ) (ℓ : ℕ) :
    tailCap n (k :: ks) (ℓ + 1) = tailCap n ks ℓ := by simp [tailCap]

lemma tailCap_zero (ks : List ℤ) : tailCap n ks 0 = (ks.map (capZ n)).sum := by simp [tailCap]

lemma costZ_zero (k : ℤ) : costZ n k 0 = 0 := by
  unfold costZ; split_ifs <;> simp [sig_zero]

/-- `ωₙ(k,t) ≤ C(n,k+1)`: a lex shadow is a family of `(k+1)`-sets. -/
lemma sig_le_choose_succ (n k t : ℕ) (ht : t ≤ n.choose k) : sig n k t ≤ n.choose (k + 1) := by
  obtain ⟨𝒜, h𝒜, rfl⟩ := exists_isLexInit n k t ht
  rw [← (lexInit_upShadow n k 𝒜 h𝒜).1]
  have := (lexInit_upShadow n k 𝒜 h𝒜).2.1.card_le
  simpa using this

lemma capZ_succ_of_nonneg {k : ℤ} (hk : 0 ≤ k) : capZ n (k + 1) = n.choose (k.toNat + 1) := by
  have e : (k + 1).toNat = k.toNat + 1 := by omega
  simp only [capZ, show (0 : ℤ) ≤ k + 1 by omega, ↓reduceIte, e]

lemma costZ_le_capZ_succ {k : ℤ} {t : ℕ} (ht : t ≤ capZ n k) : costZ n k t ≤ capZ n (k + 1) := by
  by_cases hk : 0 ≤ k
  · rw [capZ_succ_of_nonneg hk]
    simp only [capZ, costZ, hk, ↓reduceIte] at ht ⊢
    exact sig_le_choose_succ n _ t ht
  · simp only [costZ, hk, ↓reduceIte]; exact Nat.zero_le _

/-- A full component of degree `k ≥ 0` has full shadow (`lem-lex-rank1`(1)). -/
lemma costZ_capZ {k : ℤ} (hk : 0 ≤ k) : costZ n k (capZ n k) = capZ n (k + 1) := by
  rw [capZ_succ_of_nonneg hk]
  simp only [capZ, costZ, hk, ↓reduceIte, sig_full]

lemma cost_pos : ∀ (ks : List ℤ) (us : List ℕ), 0 < cost (costZ n) ks us →
    (∃ k ∈ ks, 0 ≤ k) ∧ 0 < us.sum
  | [], _, h => by simp at h
  | _ :: _, [], h => by simp [cost] at h
  | k :: ks, u :: us, h => by
    rw [cost_cons] at h
    by_cases h0 : 0 < costZ n k u
    · have hk : 0 ≤ k := by
        by_contra hk; simp [costZ, hk] at h0
      have hu : 0 < u := by
        by_contra hu; rw [show u = 0 by omega, costZ_zero] at h0; exact lt_irrefl _ h0
      exact ⟨⟨k, List.mem_cons_self, hk⟩, by simp only [List.sum_cons]; omega⟩
    · obtain ⟨⟨k', hk', h'⟩, hs⟩ := cost_pos ks us (by omega)
      exact ⟨⟨k', List.mem_cons_of_mem _ hk', h'⟩, by simp only [List.sum_cons]; omega⟩

lemma exists_nonneg_of_tailCap_pos : ∀ {ks : List ℤ}, 0 < tailCap n ks 0 → ∃ k ∈ ks, 0 ≤ k
  | [], h => by simp at h
  | k :: ks, h => by
    rw [tailCap_cons_zero] at h
    by_cases hk : 0 ≤ k
    · exact ⟨k, List.mem_cons_self, hk⟩
    · have : capZ n k = 0 := by simp [capZ, hk]
      obtain ⟨k', hk', h'⟩ := exists_nonneg_of_tailCap_pos (ks := ks) (by omega)
      exact ⟨k', List.mem_cons_of_mem _ hk', h'⟩

lemma cost_greedy_zero (ks : List ℤ) : cost (costZ n) ks (greedy (capZ n) ks 0) = 0 := by
  induction ks with
  | nil => simp [greedy]
  | cons k ks ih => simp [greedy, ih, costZ_zero]

/-- The shadow sizes of the greedy vector, `(cᵢ(t*ᵢ))ᵢ`, are greedy-shaped for the capacities of
the next degree (the numerical half of `lem-lexF-shadow`). -/
lemma greedyShape_shadow (n : ℕ) : ∀ (ks : List ℤ), ks.Pairwise (· ≥ ·) → ∀ t,
    GreedyShape (capZ n) (ks.map (· + 1)) (List.zipWith (costZ n) ks (greedy (capZ n) ks t))
  | [], _, _ => by simp [greedy, GreedyShape]
  | k :: ks, hks, t => by
    rw [List.pairwise_cons] at hks
    simp only [greedy, List.map_cons, List.zipWith_cons_cons, GreedyShape]
    refine ⟨costZ_le_capZ_succ (min_le_right _ _), fun hpos => ?_,
      greedyShape_shadow n ks hks.2 _⟩
    obtain ⟨⟨k', hk', hk'0⟩, hs⟩ := cost_pos ks _ hpos
    rw [greedy_sum] at hs
    have hm : min t (capZ n k) = capZ n k := by omega
    rw [hm]
    exact costZ_capZ (le_trans hk'0 (hks.1 k' hk'))

end CapCost

/-! ### Target 1: `lexF` segments -/

section LexF

variable {n : ℕ}

/-- **`lexF` segment** (§`sec-lex`): the `lexF` segment of size `t` of `Mon_j(F)`, for the
exterior degrees `ks` (`kᵢ = j − dᵢ`, `k₁ ≥ ⋯ ≥ k_r`). In the paper's concrete form ("fills
components `1,…,ℓ−1`, takes a lex-initial segment of component `ℓ`, and leaves the rest empty"):
the component sizes are the greedy vector `greedy (capZ n) ks t` (capacities `Cᵢ = C(n,kᵢ)`), and
each component is a lex-initial family of `kᵢ`-sets (empty if `kᵢ < 0`). For `t ≥ dim F_j` it is
all of `Mon_j(F)` (`IsLexFSeg.card_sum`). -/
def IsLexFSeg (n : ℕ) (ks : List ℤ) (t : ℕ) (𝒜s : List (Finset (Finset (Fin n)))) : Prop :=
  List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks 𝒜s ∧
    𝒜s.map card = greedy (capZ n) ks t

/-- `lexF` segments of every size exist. -/
theorem exists_isLexFSeg (n : ℕ) (ks : List ℤ) (t : ℕ) : ∃ 𝒜s, IsLexFSeg n ks t 𝒜s := by
  obtain ⟨𝒜s, h1, h2, -⟩ :=
    exists_lexInit_components (n := n) ks _ (greedy_feasible (capZ n) ks t)
  exact ⟨𝒜s, h1, h2⟩

lemma eq_of_forall₂_lexInit {ks : List ℤ} {𝒜s ℬs : List (Finset (Finset (Fin n)))}
    (h1 : List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks 𝒜s)
    (h2 : List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks ℬs)
    (hc : 𝒜s.map card = ℬs.map card) : 𝒜s = ℬs := by
  induction h1 generalizing ℬs with
  | nil => cases h2; rfl
  | cons ha _ ih =>
    cases h2 with
    | cons hb h2' =>
      simp only [List.map_cons, List.cons.injEq] at hc
      rw [isLexInit_unique ha.2 hb.2 hc.1, ih h2' hc.2]

/-- The `lexF` segment of a given size is unique. -/
theorem isLexFSeg_unique {ks : List ℤ} {t : ℕ} {𝒜s ℬs : List (Finset (Finset (Fin n)))}
    (h𝒜 : IsLexFSeg n ks t 𝒜s) (hℬ : IsLexFSeg n ks t ℬs) : 𝒜s = ℬs :=
  eq_of_forall₂_lexInit h𝒜.1 hℬ.1 (h𝒜.2.trans hℬ.2.symm)

/-- The size of the `lexF` segment of size `t` is `min t (dim F_j)`. -/
lemma IsLexFSeg.card_sum {ks : List ℤ} {t : ℕ} {𝒜s : List (Finset (Finset (Fin n)))}
    (h : IsLexFSeg n ks t 𝒜s) : (𝒜s.map card).sum = min t (tailCap n ks 0) := by
  rw [h.2, greedy_sum, tailCap_zero]

/-- A `lexF` segment is the `lexF` segment of its own size. -/
lemma IsLexFSeg.resize {ks : List ℤ} {t : ℕ} {𝒜s : List (Finset (Finset (Fin n)))}
    (h : IsLexFSeg n ks t 𝒜s) : IsLexFSeg n ks (𝒜s.map card).sum 𝒜s := by
  refine ⟨h.1, ?_⟩
  have := (greedyShape_greedy (capZ n) ks t).eq_greedy
  rw [← h.2] at this
  exact this

/-- Two `lexF` segments of the same total size coincide. -/
theorem isLexFSeg_unique' {ks : List ℤ} {t t' : ℕ} {𝒜s ℬs : List (Finset (Finset (Fin n)))}
    (h𝒜 : IsLexFSeg n ks t 𝒜s) (hℬ : IsLexFSeg n ks t' ℬs)
    (hc : (𝒜s.map card).sum = (ℬs.map card).sum) : 𝒜s = ℬs := by
  have h1 := h𝒜.resize; rw [hc] at h1
  exact isLexFSeg_unique h1 hℬ.resize

/-- Lex-initial families of the same degree are nested by size. -/
lemma isLexInit_subset_of_card_le {𝒜 ℬ : Finset (Finset (Fin n))} {k : ℕ} (h𝒜 : IsLexInit 𝒜 k)
    (hℬ : IsLexInit ℬ k) (hc : #𝒜 ≤ #ℬ) : 𝒜 ⊆ ℬ := by
  by_cases hk : k ≤ n
  · have himg : ∀ 𝒞 : Finset (Finset (Fin n)), #(𝒞.image phi) = #𝒞 :=
      fun 𝒞 => card_image_of_injective _ phi_injective
    rcases (isInitSeg_image_phi hk h𝒜).total (isInitSeg_image_phi hk hℬ) with h | h
    · exact (image_subset_image_iff phi_injective).mp h
    · have e := eq_of_subset_of_card_le h (by rw [himg, himg]; exact hc)
      refine (image_subset_image_iff phi_injective).mp ?_
      rw [e]
  · have e : ∀ 𝒞 : Finset (Finset (Fin n)), IsLexInit 𝒞 k → 𝒞 = ∅ := fun 𝒞 h𝒞 => by
      have := h𝒞.1.card_le; rw [Fintype.card_fin, Nat.choose_eq_zero_of_lt (by omega)] at this
      exact card_eq_zero.mp (by omega)
    rw [e 𝒜 h𝒜]; exact empty_subset _

lemma forall₂_subset_of_le {ks : List ℤ} {𝒜s ℬs : List (Finset (Finset (Fin n)))}
    (h1 : List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks 𝒜s)
    (h2 : List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks ℬs)
    (hle : List.Forall₂ (· ≤ ·) (𝒜s.map card) (ℬs.map card)) :
    List.Forall₂ (· ⊆ ·) 𝒜s ℬs := by
  induction h1 generalizing ℬs with
  | nil => cases h2; exact List.Forall₂.nil
  | cons ha _ ih =>
    cases h2 with
    | cons hb h2' =>
      simp only [List.map_cons] at hle
      cases hle with
      | cons hc hle' => exact List.Forall₂.cons (isLexInit_subset_of_card_le ha.2 hb.2 hc) (ih h2' hle')

/-- `lexF` segments of one degree are nested by size ("Segments of one degree are nested by size",
proof of `lem-lexF-shadow`). -/
theorem IsLexFSeg.forall₂_subset {ks : List ℤ} {t t' : ℕ}
    {𝒜s ℬs : List (Finset (Finset (Fin n)))} (h𝒜 : IsLexFSeg n ks t 𝒜s)
    (hℬ : IsLexFSeg n ks t' ℬs) (hle : (𝒜s.map card).sum ≤ (ℬs.map card).sum) :
    List.Forall₂ (· ⊆ ·) 𝒜s ℬs := by
  have hm := greedy_mono (capZ n) ks hle
  rw [← h𝒜.resize.2, ← hℬ.resize.2] at hm
  exact forall₂_subset_of_le h𝒜.1 hℬ.1 hm

/-! #### The order-theoretic definition: initial segments of `Mon_j(F)` for `>_{lexF}` -/

/-- `𝒜s ⊆ Mon_j(F)` is an **initial segment of `Mon_j(F)` for the position-over-term order
`>_{lexF}`** (§`sec-lex`, the paper's definition of a `lexF` segment, following Amata–Crupi
Section 2). The monomials of `Mon_j(F)` are the pairs `(i, u)`, `u` a `kᵢ`-subset of `[n]` with
`kᵢ ≥ 0` (here `u ∈ 𝒜s.getD i ∅`, components indexed from `0`), and `u gᵢ >_{lexF} v g_l` iff
`i < l`, or `i = l` and `u >_lex v` (`LexLT u v`). `isLexFInitial_iff` shows that this is the
concrete form `IsLexFSeg` (the paper's "Concretely, a `lexF` segment fills components
`1,…,ℓ−1`, takes a lex-initial segment of component `ℓ`, and leaves the rest empty"). -/
def IsLexFInitial (n : ℕ) (ks : List ℤ) (𝒜s : List (Finset (Finset (Fin n)))) : Prop :=
  List.Forall₂ Component ks 𝒜s ∧
    ∀ ⦃i l : ℕ⦄ ⦃u v : Finset (Fin n)⦄, v ∈ 𝒜s.getD l ∅ →
      i < ks.length → 0 ≤ ks.getD i 0 → #u = (ks.getD i 0).toNat →
      (i < l ∨ (i = l ∧ LexLT u v)) → u ∈ 𝒜s.getD i ∅

lemma isLexFInitial_cons_iff {k : ℤ} {ks : List ℤ} {𝒜 : Finset (Finset (Fin n))}
    {𝒜s : List (Finset (Finset (Fin n)))} :
    IsLexFInitial n (k :: ks) (𝒜 :: 𝒜s) ↔
      (Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ∧
      ((∃ l, (𝒜s.getD l ∅).Nonempty) → ∀ u : Finset (Fin n), 0 ≤ k → #u = k.toNat → u ∈ 𝒜) ∧
      IsLexFInitial n ks 𝒜s := by
  constructor
  · rintro ⟨hF, hI⟩
    rw [List.forall₂_cons] at hF
    refine ⟨⟨hF.1, hF.1.1, fun s t hs hts ht => ?_⟩, fun ⟨l, v, hv⟩ u hk hu => ?_, ⟨hF.2, ?_⟩⟩
    · have hk : 0 ≤ k := by
        by_contra hk; rw [hF.1.2 (by omega)] at hs; simp at hs
      exact hI (i := 0) (l := 0) (v := s) (by simpa using hs) (by simp) (by simpa using hk)
        (by simpa using ht) (Or.inr ⟨rfl, hts⟩)
    · exact hI (i := 0) (l := l + 1) (v := v) (by simpa using hv) (by simp) (by simpa using hk)
        (by simpa using hu) (Or.inl (by omega))
    · intro i l u v hv hi hk hu hil
      exact hI (i := i + 1) (l := l + 1) (v := v) (by simpa using hv) (by simpa using hi)
        (by simpa using hk) (by simpa using hu)
        (hil.imp (fun h => by omega) (fun h => ⟨by omega, h.2⟩))
  · rintro ⟨⟨hC, hL⟩, hfull, hF, hI⟩
    refine ⟨List.Forall₂.cons hC hF, fun i l u v hv hi hk hu hil => ?_⟩
    rcases i with _ | i <;> rcases l with _ | l
    · simp only [List.getD_cons_zero] at hv hk hu ⊢
      rcases hil with h | ⟨-, h⟩
      · omega
      · exact hL.2 hv h hu
    · simp only [List.getD_cons_zero, List.getD_cons_succ] at hv hk hu ⊢
      exact hfull ⟨l, v, hv⟩ u hk hu
    · rcases hil with h | ⟨h, -⟩ <;> omega
    · simp only [List.getD_cons_succ, List.length_cons] at hv hi hk hu ⊢
      exact hI hv (by omega) hk hu (hil.imp (fun h => by omega) (fun h => ⟨by omega, h.2⟩))

lemma exists_getD_nonempty_iff : ∀ (𝒜s : List (Finset (Finset (Fin n)))),
    (∃ l, (𝒜s.getD l ∅).Nonempty) ↔ 0 < (𝒜s.map card).sum
  | [] => by simp
  | 𝒜 :: 𝒜s => by
    rw [List.map_cons, List.sum_cons]
    constructor
    · rintro ⟨l, hl⟩
      rcases l with _ | l
      · simp only [List.getD_cons_zero] at hl; have := hl.card_pos; omega
      · simp only [List.getD_cons_succ] at hl
        have := (exists_getD_nonempty_iff 𝒜s).mp ⟨l, hl⟩; omega
    · intro h
      by_cases h𝒜 : 0 < #𝒜
      · exact ⟨0, by simpa using card_pos.mp h𝒜⟩
      · obtain ⟨l, hl⟩ := (exists_getD_nonempty_iff 𝒜s).mpr (by omega)
        exact ⟨l + 1, by simpa using hl⟩

/-- A component is full (contains every monomial of its degree) iff it has `C(n,k)` elements. -/
lemma Component.full_iff {k : ℤ} {𝒜 : Finset (Finset (Fin n))} (h : Component k 𝒜) :
    (∀ u : Finset (Fin n), 0 ≤ k → #u = k.toNat → u ∈ 𝒜) ↔ #𝒜 = capZ n k := by
  by_cases hk : 0 ≤ k
  · have hsub : 𝒜 ⊆ powersetCard k.toNat univ :=
      fun s hs => mem_powersetCard.mpr ⟨subset_univ _, h.1 hs⟩
    simp only [capZ, hk, ↓reduceIte]
    constructor
    · intro hf
      have : 𝒜 = powersetCard k.toNat univ :=
        subset_antisymm hsub (fun u hu => hf u (by trivial) (mem_powersetCard.mp hu).2)
      rw [this, card_powersetCard, card_univ, Fintype.card_fin]
    · intro hc u _ hu
      have := eq_of_subset_of_card_le hsub
        (by rw [card_powersetCard, card_univ, Fintype.card_fin, hc])
      rw [this]; exact mem_powersetCard.mpr ⟨subset_univ _, hu⟩
  · simp [capZ, hk, h.2 (by omega)]

lemma isLexFInitial_iff_shape : ∀ (ks : List ℤ) (𝒜s : List (Finset (Finset (Fin n)))),
    IsLexFInitial n ks 𝒜s ↔
      List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks 𝒜s ∧
        GreedyShape (capZ n) ks (𝒜s.map card)
  | [], [] => by simp [IsLexFInitial, GreedyShape]
  | [], _ :: _ => by simp [IsLexFInitial]
  | _ :: _, [] => by simp [IsLexFInitial]
  | k :: ks, 𝒜 :: 𝒜s => by
    rw [isLexFInitial_cons_iff, isLexFInitial_iff_shape ks 𝒜s, List.forall₂_cons]
    simp only [List.map_cons, GreedyShape]
    constructor
    · rintro ⟨hCL, hfull, hF, hS⟩
      exact ⟨⟨hCL, hF⟩, hCL.1.card_le,
        fun hpos => hCL.1.full_iff.mp (hfull ((exists_getD_nonempty_iff 𝒜s).mpr hpos)), hS⟩
    · rintro ⟨⟨hCL, hF⟩, -, hpos, hS⟩
      exact ⟨hCL, fun hne => hCL.1.full_iff.mpr (hpos ((exists_getD_nonempty_iff 𝒜s).mp hne)),
        hF, hS⟩

/-- **The paper's definition of a `lexF` segment agrees with the concrete one**: `𝒜s` is an
initial segment of `Mon_j(F)` for `>_{lexF}` iff it is the `lexF` segment (`IsLexFSeg`) of its own
size. -/
theorem isLexFInitial_iff {ks : List ℤ} {𝒜s : List (Finset (Finset (Fin n)))} :
    IsLexFInitial n ks 𝒜s ↔ IsLexFSeg n ks (𝒜s.map card).sum 𝒜s := by
  rw [isLexFInitial_iff_shape]
  constructor
  · rintro ⟨hF, hS⟩; exact ⟨hF, hS.eq_greedy⟩
  · intro h
    refine ⟨h.1, ?_⟩
    rw [h.2]; exact greedyShape_greedy _ _ _

/-- `IsLexFInitial n ks 𝒜s ↔ ∃ t, IsLexFSeg n ks t 𝒜s`. -/
theorem isLexFInitial_iff_exists {ks : List ℤ} {𝒜s : List (Finset (Finset (Fin n)))} :
    IsLexFInitial n ks 𝒜s ↔ ∃ t, IsLexFSeg n ks t 𝒜s :=
  ⟨fun h => ⟨_, isLexFInitial_iff.mp h⟩, fun ⟨_, h⟩ => isLexFInitial_iff.mpr h.resize⟩

end LexF

/-! ### Target 2: `lem-lexF-shadow` -/

section Shadow

variable {n : ℕ}

lemma component_lexInit_upShadow {k : ℤ} {𝒜 : Finset (Finset (Fin n))}
    (h : Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) :
    (Component (k + 1) (∂⁺ 𝒜) ∧ IsLexInit (∂⁺ 𝒜) (k + 1).toNat) ∧ #(∂⁺ 𝒜) = costZ n k #𝒜 := by
  by_cases hk : 0 ≤ k
  · have e : (k + 1).toNat = k.toNat + 1 := by omega
    obtain ⟨h1, h2⟩ := lexInit_upShadow n k.toNat 𝒜 h.2
    refine ⟨⟨⟨by rw [e]; exact h2.1, fun h' => by omega⟩, by rw [e]; exact h2⟩, ?_⟩
    simp only [costZ, hk, ↓reduceIte, h1]
  · have h0 : 𝒜 = ∅ := h.1.2 (by omega)
    subst h0
    rw [upShadow_empty]
    exact ⟨⟨⟨by simp, fun _ => rfl⟩, isLexInit_empty _⟩, by simp [costZ_zero]⟩

/-- The shadow sizes of a `lexF` segment, component by component: `|∇ Lex(kᵢ, t*ᵢ)| = cᵢ(t*ᵢ)`. -/
lemma IsLexFSeg.shadow_card {ks : List ℤ} {t : ℕ} {𝒜s : List (Finset (Finset (Fin n)))}
    (h : IsLexFSeg n ks t 𝒜s) :
    𝒜s.map (fun 𝒜 => #(∂⁺ 𝒜)) = List.zipWith (costZ n) ks (greedy (capZ n) ks t) := by
  rw [← h.2]
  obtain ⟨h1, -⟩ := h
  induction h1 with
  | nil => rfl
  | cons ha _ ih =>
    simp only [List.map_cons, List.zipWith_cons_cons, ih, (component_lexInit_upShadow ha).2]

/-- `|Shad L| = ∑ᵢ cᵢ(t*ᵢ)` for the `lexF` segment `L` of size `t`. -/
lemma IsLexFSeg.shadow_sum {ks : List ℤ} {t : ℕ} {𝒜s : List (Finset (Finset (Fin n)))}
    (h : IsLexFSeg n ks t 𝒜s) :
    (𝒜s.map (fun 𝒜 => #(∂⁺ 𝒜))).sum = cost (costZ n) ks (greedy (capZ n) ks t) := by
  rw [h.shadow_card]; rfl

/-- **Lemma `lem-lexF-shadow`**, first sentence. The componentwise upper shadow `Shad L` of the
`lexF` segment `L` of size `t` in degree `j` (exterior degrees `ks`) is the `lexF` segment of
size `∑ᵢ cᵢ(t*ᵢ)` in degree `j+1` (exterior degrees `ks.map (· + 1)`): its component sizes are the
greedy vector for the capacities `C(n, kᵢ+1)`, and every component is lex-initial. Components
with `kᵢ = −1` are empty in degree `j` and of capacity `1` in degree `j+1`; components with
`kᵢ > n` are empty in both degrees. -/
theorem lem_lexF_shadow {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·)) {t : ℕ}
    {𝒜s : List (Finset (Finset (Fin n)))} (h : IsLexFSeg n ks t 𝒜s) :
    IsLexFSeg n (ks.map (· + 1)) (cost (costZ n) ks (greedy (capZ n) ks t))
      (𝒜s.map upShadow) := by
  refine ⟨?_, ?_⟩
  · rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
    exact h.1.imp fun k 𝒜 h' => (component_lexInit_upShadow h').1
  · rw [List.map_map]
    have e : (card ∘ upShadow) = fun 𝒜 : Finset (Finset (Fin n)) => #(∂⁺ 𝒜) := rfl
    rw [e, h.shadow_card]
    exact (greedyShape_shadow n ks hks t).eq_greedy

/-- **Lemma `lem-lexF-shadow`**, second sentence. For `lexF` segments `L` of `Mon_j(F)` and `L'`
of `Mon_{j+1}(F)`, `|Shad L| ≤ |L'|` implies `Shad L ⊆ L'` (componentwise). -/
theorem lem_lexF_shadow_subset {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·)) {t t' : ℕ}
    {𝒜s ℬs : List (Finset (Finset (Fin n)))} (hL : IsLexFSeg n ks t 𝒜s)
    (hL' : IsLexFSeg n (ks.map (· + 1)) t' ℬs)
    (hle : (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum ≤ (ℬs.map card).sum) :
    List.Forall₂ (fun 𝒜 ℬ => ∂⁺ 𝒜 ⊆ ℬ) 𝒜s ℬs := by
  have h2 := (lem_lexF_shadow hks hL).forall₂_subset hL' (by rw [List.map_map]; exact hle)
  rwa [List.forall₂_map_left_iff] at h2

end Shadow

/-! ### Target 3: `def-B` in shadow form, and the formula half of `thm-module-kk` -/

section DefB

variable {n : ℕ}

lemma exists_tailCap_le (n : ℕ) (ks : List ℤ) (h : ℕ) : ∃ ℓ, tailCap n ks ℓ ≤ h :=
  ⟨ks.length, by simp [tailCap]⟩

/-- `ℓ(h,j) = min {ℓ ∈ [0,r] : T_ℓ(j) ≤ h}` of `def-B` (the minimum over `ℕ` is `≤ r`, since
`T_r(j) = 0`). -/
def ellB (n : ℕ) (ks : List ℤ) (h : ℕ) : ℕ := Nat.find (exists_tailCap_le n ks h)

/-- `a = h − T_ℓ(j)` of `def-B`. -/
def remB (n : ℕ) (ks : List ℤ) (h : ℕ) : ℕ := h - tailCap n ks (ellB n ks h)

/-- `k_ℓ = j − d_ℓ` of `def-B` (the `ℓ`-th exterior degree, 1-indexed; unused when `ℓ = 0`). -/
def kB (n : ℕ) (ks : List ℤ) (h : ℕ) : ℤ := ks.getD (ellB n ks h - 1) 0

/-- The Macaulay term of `def-B` in *shadow form*: `C(n,k+1) − ωₙ(k, C(n,k) − a)`. By the
"Moreover" of `thm-kk-rank1` this is `a^{(k)}` for `k ≥ 1`, `0 ≤ a < C(n,k)` (proved elsewhere);
for `a = 0` it is `0` for every `k` (`macShadow_zero`). -/
def macShadow (n k a : ℕ) : ℕ := n.choose (k + 1) - sig n k (n.choose k - a)

/-- **`def-B`**, with the Macaulay term `a^{(k)}` abstracted as `M k a`:
`B(h,j) = T_ℓ(j+1) + M k_ℓ a`, where the second summand is `0` when `ℓ = 0` (the paper's
convention `0^{(k)} = 0`, which covers `ℓ = 0`). `def-B` itself is
`growthB (fun k a => a^{(k)})`. -/
def growthB (M : ℕ → ℕ → ℕ) (n : ℕ) (ks : List ℤ) (h : ℕ) : ℕ :=
  tailCap n (ks.map (· + 1)) (ellB n ks h) +
    (if ellB n ks h = 0 then 0 else M (kB n ks h).toNat (remB n ks h))

/-- **`def-B` in ω-form**: `B(h,j)` with `a^{(k_ℓ)}` replaced by `macShadow n k_ℓ a`
`= C(n,k_ℓ+1) − ωₙ(k_ℓ, C(n,k_ℓ) − a)`. Here `ks` are the exterior degrees in degree `j`. -/
def Bω (n : ℕ) (ks : List ℤ) (h : ℕ) : ℕ := growthB (macShadow n) n ks h

lemma ellB_eq_iff {ks : List ℤ} {h ℓ : ℕ} :
    ellB n ks h = ℓ ↔ tailCap n ks ℓ ≤ h ∧ ∀ m < ℓ, ¬ tailCap n ks m ≤ h :=
  Nat.find_eq_iff _

lemma ellB_eq_zero_iff {ks : List ℤ} {h : ℕ} : ellB n ks h = 0 ↔ tailCap n ks 0 ≤ h :=
  Nat.find_eq_zero _

lemma tailCap_ellB_le (ks : List ℤ) (h : ℕ) : tailCap n ks (ellB n ks h) ≤ h :=
  Nat.find_spec (exists_tailCap_le n ks h)

lemma ellB_cons {k : ℤ} {ks : List ℤ} {h : ℕ} (hlt : h < tailCap n (k :: ks) 0) :
    ellB n (k :: ks) h = ellB n ks h + 1 := by
  rw [ellB_eq_iff]
  refine ⟨by simpa using tailCap_ellB_le ks h, fun m hm => ?_⟩
  rcases m with _ | m
  · omega
  · simpa using Nat.find_min (exists_tailCap_le n ks h) (by unfold ellB at hm; omega)

lemma macShadow_zero (n k : ℕ) : macShadow n k 0 = 0 := by
  simp [macShadow, sig_full]

/-- `ℓ = 0`: `B(h,j) = T_0(j+1) = dim F_{j+1}` when `h ≥ dim F_j`. -/
lemma growthB_of_le {M : ℕ → ℕ → ℕ} {ks : List ℤ} {h : ℕ} (hh : tailCap n ks 0 ≤ h) :
    growthB M n ks h = tailCap n (ks.map (· + 1)) 0 := by
  have : ellB n ks h = 0 := ellB_eq_zero_iff.mpr hh
  simp [growthB, this]

/-- The recursion of `def-B` in the first component. -/
lemma growthB_cons {M : ℕ → ℕ → ℕ} {k : ℤ} {ks : List ℤ} {h : ℕ}
    (hlt : h < tailCap n (k :: ks) 0) :
    growthB M n (k :: ks) h =
      if tailCap n ks 0 ≤ h then tailCap n (ks.map (· + 1)) 0 + M k.toNat (h - tailCap n ks 0)
      else growthB M n ks h := by
  have e := ellB_cons hlt
  split_ifs with h0
  · have e0 : ellB n ks h = 0 := ellB_eq_zero_iff.mpr h0
    simp [growthB, remB, kB, e, e0]
  · have e0 : ellB n ks h ≠ 0 := fun h' => h0 (ellB_eq_zero_iff.mp h')
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero e0
    simp [growthB, remB, kB, e, hm]

/-- In the domain `0 ≤ h ≤ dim F_j` of `def-B`, with `ℓ ≥ 1`: `k_ℓ ≥ 0`, `a < C(n,k_ℓ)`. These are
the hypotheses under which `macShadow n k a = a^{(k)}` (`thm-kk-rank1`, "Moreover", with `a = 0`
when `k_ℓ = 0`). -/
lemma kB_remB_of_pos {ks : List ℤ} {h : ℕ} (hh : h ≤ tailCap n ks 0) (hℓ : ellB n ks h ≠ 0) :
    0 ≤ kB n ks h ∧ remB n ks h < n.choose (kB n ks h).toNat := by
  induction ks generalizing h with
  | nil => exact absurd (ellB_eq_zero_iff.mpr (by simp)) hℓ
  | cons k ks ih =>
    have hlt : h < tailCap n (k :: ks) 0 := by
      rcases lt_or_eq_of_le hh with h' | h'
      · exact h'
      · exact absurd (ellB_eq_zero_iff.mpr h'.ge) hℓ
    have e := ellB_cons hlt
    rw [tailCap_cons_zero] at hlt
    by_cases h0 : tailCap n ks 0 ≤ h
    · have e0 : ellB n ks h = 0 := ellB_eq_zero_iff.mpr h0
      simp only [kB, remB, e, e0, zero_add, Nat.sub_self, List.getD_cons_zero, tailCap_cons_succ]
      by_cases hk : 0 ≤ k
      · simp only [capZ, hk, ↓reduceIte] at hlt
        exact ⟨hk, by omega⟩
      · simp only [capZ, hk, ↓reduceIte] at hlt; omega
    · have e0 : ellB n ks h ≠ 0 := fun h' => h0 (ellB_eq_zero_iff.mp h')
      obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero e0
      have := ih (h := h) (by omega) e0
      simp only [kB, remB, hm, e, Nat.add_sub_cancel, List.getD_cons_succ,
        tailCap_cons_succ] at this ⊢
      exact this

/-- **Glue.** `def-B` does not depend on the Macaulay term outside `a < C(n,k)`: if `M` and `M'`
agree there, they give the same `B(h,j)` for `0 ≤ h ≤ dim F_j`. Applied with `M = macShadow n` and
`M' = (fun k a => a^{(k)})` and the identity of `thm-kk-rank1` ("Moreover"), it turns every
statement about `Bω` below into the same statement about `def-B`. -/
theorem growthB_congr {M M' : ℕ → ℕ → ℕ} {ks : List ℤ} {h : ℕ}
    (hM : ∀ k a, a < n.choose k → M k a = M' k a) (hh : h ≤ tailCap n ks 0) :
    growthB M n ks h = growthB M' n ks h := by
  unfold growthB
  split_ifs with hℓ
  · rfl
  · obtain ⟨-, h2⟩ := kB_remB_of_pos hh hℓ
    rw [hM _ _ h2]

/-- The computation in the proof of `thm-module-kk` (formula part), numerically: for
`0 ≤ t ≤ dim F_j` and the greedy vector `t*` of `t`, `∑ᵢ cᵢ(t*ᵢ) + Bω(dim F_j − t) = dim F_{j+1}`.
Proof by induction on the number of components (the recursion `growthB_cons`). -/
theorem cost_greedy_add_Bω (ks : List ℤ) (hks : ks.Pairwise (· ≥ ·)) (t : ℕ)
    (ht : t ≤ tailCap n ks 0) :
    cost (costZ n) ks (greedy (capZ n) ks t) + Bω n ks (tailCap n ks 0 - t) =
      tailCap n (ks.map (· + 1)) 0 := by
  induction ks generalizing t with
  | nil =>
    simp only [tailCap_nil, Nat.le_zero] at ht
    subst ht
    simp [Bω, greedy, growthB_of_le]
  | cons k ks ih =>
    rw [List.pairwise_cons] at hks
    have hT := tailCap_cons_zero (n := n) k ks
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · rw [Nat.sub_zero, Bω, growthB_of_le le_rfl, cost_greedy_zero, zero_add]
    have hlt : tailCap n (k :: ks) 0 - t < tailCap n (k :: ks) 0 := by omega
    simp only [Bω] at ih ⊢
    rw [growthB_cons hlt]
    simp only [List.map_cons, tailCap_cons_zero, greedy, cost_cons]
    rw [hT] at ht hlt
    by_cases htC : t ≤ capZ n k
    · -- the segment ends inside the first component
      have hk : 0 ≤ k := by by_contra hk; simp [capZ, hk] at htC; omega
      rw [ite_eq_left (by omega), min_eq_left htC, Nat.sub_self, cost_greedy_zero, add_zero,
        show capZ n k + tailCap n ks 0 - t - tailCap n ks 0 = capZ n k - t by omega,
        capZ_succ_of_nonneg hk]
      simp only [capZ, costZ, hk, ↓reduceIte] at htC ⊢
      have hle := sig_le_choose_succ n k.toNat t htC
      rw [macShadow, show n.choose k.toNat - (n.choose k.toNat - t) = t by omega]
      omega
    · -- the first component is full
      rw [not_le] at htC
      have hR : 0 < tailCap n ks 0 := by omega
      obtain ⟨k', hk', hk'0⟩ := exists_nonneg_of_tailCap_pos hR
      have hk : 0 ≤ k := le_trans hk'0 (hks.1 k' hk')
      rw [ite_eq_right (by omega), min_eq_right htC.le, costZ_capZ hk]
      have := ih hks.2 (t - capZ n k) (by omega)
      rw [show tailCap n ks 0 - (t - capZ n k) = capZ n k + tailCap n ks 0 - t by omega] at this
      omega

/-- `B(h,j) ≤ dim F_{j+1}` in the domain `h ≤ dim F_j`. -/
lemma Bω_le {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·)) {h : ℕ} (hh : h ≤ tailCap n ks 0) :
    Bω n ks h ≤ tailCap n (ks.map (· + 1)) 0 := by
  have := cost_greedy_add_Bω ks hks (tailCap n ks 0 - h) (Nat.sub_le _ _)
  rw [show tailCap n ks 0 - (tailCap n ks 0 - h) = h by omega] at this
  omega

/-- **Theorem `thm-module-kk`, the formula** (monomial form, Macaulay term in shadow form): for the
`lexF` segment `L` of `Mon_j(F)`, `dim F_{j+1} − |Shad L| = Bω(dim F_j − |L|, j)`. -/
theorem thm_module_kk_formula {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·)) {t : ℕ}
    {𝒜s : List (Finset (Finset (Fin n)))} (hL : IsLexFSeg n ks t 𝒜s) :
    tailCap n (ks.map (· + 1)) 0 - (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum =
      Bω n ks (tailCap n ks 0 - (𝒜s.map card).sum) := by
  have hs : (𝒜s.map card).sum ≤ tailCap n ks 0 := by rw [hL.card_sum]; exact min_le_right _ _
  have := cost_greedy_add_Bω ks hks _ hs
  rw [hL.resize.shadow_sum]
  omega

/-! ### Target 4: the inequality half, for monomial families -/

lemma sum_card_le_tailCap {ks : List ℤ} {𝒜s : List (Finset (Finset (Fin n)))}
    (h : List.Forall₂ Component ks 𝒜s) : (𝒜s.map card).sum ≤ tailCap n ks 0 := by
  induction h with
  | nil => simp
  | cons ha _ ih => simp only [List.map_cons, List.sum_cons, tailCap_cons_zero]; have := ha.card_le; omega

/-- **Theorem `thm-module-kk`, the inequality** (monomial form; with `Lemma lem-monomial`, not
formalised here, it gives the subspace form). For every monomial family `𝒜 = ⨆ᵢ 𝒜ᵢ gᵢ` of
`Mon_j(F)`, `|Shad 𝒜| ≥ |Shad L|` for the `lexF` segment `L` with `|L| = |𝒜|`. -/
theorem thm_module_kk_ineq_mon {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·))
    {𝒜s ℒs : List (Finset (Finset (Fin n)))} (h𝒜 : List.Forall₂ Component ks 𝒜s) {t : ℕ}
    (hL : IsLexFSeg n ks t ℒs) (hsz : (ℒs.map card).sum = (𝒜s.map card).sum) :
    (ℒs.map fun ℒ => #(∂⁺ ℒ)).sum ≤ (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum := by
  rw [hL.resize.shadow_sum, hsz]
  exact module_shadow_ge_greedy ks hks 𝒜s h𝒜

/-- **The growth bound for monomial families** (`thm-module-kk` with `cor-prop41`'s computation):
`dim F_{j+1} − |Shad 𝒜| ≤ Bω(dim F_j − |𝒜|, j)`. -/
theorem thm_module_kk_bound_mon {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·))
    {𝒜s : List (Finset (Finset (Fin n)))} (h𝒜 : List.Forall₂ Component ks 𝒜s) :
    tailCap n (ks.map (· + 1)) 0 - (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum ≤
      Bω n ks (tailCap n ks 0 - (𝒜s.map card).sum) := by
  obtain ⟨ℒs, hL⟩ := exists_isLexFSeg n ks (𝒜s.map card).sum
  have hsz : (ℒs.map card).sum = (𝒜s.map card).sum := by
    rw [hL.card_sum]; exact min_eq_left (sum_card_le_tailCap h𝒜)
  have h1 := thm_module_kk_formula hks hL
  have h2 := thm_module_kk_ineq_mon hks h𝒜 hL hsz
  rw [hsz] at h1
  omega

/-- Evaluation of `def-B` once `ℓ` is known (used for the numerical anchors). -/
lemma growthB_eq_of {M : ℕ → ℕ → ℕ} {ks : List ℤ} {h ℓ : ℕ} (h1 : tailCap n ks ℓ ≤ h)
    (h2 : ∀ m < ℓ, ¬ tailCap n ks m ≤ h) :
    growthB M n ks h = tailCap n (ks.map (· + 1)) ℓ +
      (if ℓ = 0 then 0 else M (ks.getD (ℓ - 1) 0).toNat (h - tailCap n ks ℓ)) := by
  have e : ellB n ks h = ℓ := ellB_eq_iff.mpr ⟨h1, h2⟩
  simp only [growthB, remB, kB, e]

end DefB

/-! ### Target 5: `thm-ac42` for monomial submodules -/

section Submodule

variable {n : ℕ}

/-- The exterior degrees `kᵢ = j − dᵢ` of the components of `F` in degree `j`, for the generator
degrees `ds = (d₁,…,d_r)`. -/
def extDeg (ds : List ℤ) (j : ℤ) : List ℤ := ds.map (j - ·)

lemma extDeg_succ (ds : List ℤ) (j : ℤ) : extDeg ds (j + 1) = (extDeg ds j).map (· + 1) := by
  simp only [extDeg, List.map_map]
  congr 1; funext d; simp only [Function.comp_apply]; ring

lemma extDeg_pairwise {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·)) (j : ℤ) :
    (extDeg ds j).Pairwise (· ≥ ·) := by
  unfold extDeg
  rw [List.pairwise_map]
  exact hds.imp fun h => by omega

/-- `dim F_j = ∑ᵢ C(n, j − dᵢ) = T_0(j)` (§`sec-setup`). -/
def dimF (n : ℕ) (ds : List ℤ) (j : ℤ) : ℕ := tailCap n (extDeg ds j) 0

/-- `B(h,j)` of `def-B` in ω-form (`Bω`), for the generator degrees `ds` (`d₁ ≤ ⋯ ≤ d_r`). -/
def Bωj (n : ℕ) (ds : List ℤ) (h : ℕ) (j : ℤ) : ℕ := Bω n (extDeg ds j) h

/-- A **monomial submodule** `M = I₁g₁ ⊕ ⋯ ⊕ I_r g_r ⊆ F` (§`sec-setup`), as the sequence of the
monomial families of its graded pieces: `A j` is the set of monomials of `M_j`, its `i`-th
component a family of `(j − dᵢ)`-sets (`Component`). `M` is an `E`-submodule iff it is closed under
multiplication by `E₁` (which generates `E`), i.e. iff `Shad(A_j) ⊆ A_{j+1}` componentwise. -/
structure IsMonSubmodule (n : ℕ) (ds : List ℤ) (A : ℤ → List (Finset (Finset (Fin n)))) :
    Prop where
  comp : ∀ j, List.Forall₂ Component (extDeg ds j) (A j)
  shad : ∀ j, List.Forall₂ (fun 𝒜 ℬ => ∂⁺ 𝒜 ⊆ ℬ) (A j) (A (j + 1))

/-- The Hilbert function of the quotient, `H_{F/M}(j) = dim F_j − dim M_j`. -/
def quotHF (n : ℕ) (ds : List ℤ) (A : ℤ → List (Finset (Finset (Fin n)))) (j : ℤ) : ℕ :=
  dimF n ds j - ((A j).map card).sum

/-- A **lex submodule** (§`sec-lex`): a monomial submodule all of whose graded pieces are `lexF`
segments (`∃ t, IsLexFSeg …`, equivalently `IsLexFInitial …` by `isLexFInitial_iff_exists`). -/
def IsLexSubmodule (n : ℕ) (ds : List ℤ) (L : ℤ → List (Finset (Finset (Fin n)))) : Prop :=
  IsMonSubmodule n ds L ∧ ∀ j, ∃ t, IsLexFSeg n (extDeg ds j) t (L j)

lemma sum_card_le_of_forall₂_subset {𝒜s ℬs : List (Finset (Finset (Fin n)))}
    (h : List.Forall₂ (fun 𝒜 ℬ => ∂⁺ 𝒜 ⊆ ℬ) 𝒜s ℬs) :
    (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum ≤ (ℬs.map card).sum := by
  induction h with
  | nil => simp
  | cons hab _ ih =>
    simp only [List.map_cons, List.sum_cons]; have := card_le_card hab; omega

/-- **Corollary `cor-prop41`, for monomial submodules** (and so `thm-ac42` (1_mon) ⇒ (2)): for
every monomial submodule `M ⊆ F` and every `j ∈ ℤ`, `H_{F/M}(j+1) ≤ B(H_{F/M}(j), j)`. -/
theorem cor_prop41_mon {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·))
    {A : ℤ → List (Finset (Finset (Fin n)))} (hA : IsMonSubmodule n ds A) (j : ℤ) :
    quotHF n ds A (j + 1) ≤ Bωj n ds (quotHF n ds A j) j := by
  have h1 := thm_module_kk_bound_mon (extDeg_pairwise hds j) (hA.comp j)
  have h2 := sum_card_le_of_forall₂_subset (hA.shad j)
  unfold quotHF dimF Bωj
  rw [extDeg_succ]
  omega

/-- The lex sequence of `h`: `L_j` is the `lexF` segment of size `dim F_j − h_j`. -/
noncomputable def lexSeq (n : ℕ) (ds : List ℤ) (h : ℤ → ℕ) (j : ℤ) :
    List (Finset (Finset (Fin n))) :=
  Classical.choose (exists_isLexFSeg n (extDeg ds j) (dimF n ds j - h j))

lemma lexSeq_spec (n : ℕ) (ds : List ℤ) (h : ℤ → ℕ) (j : ℤ) :
    IsLexFSeg n (extDeg ds j) (dimF n ds j - h j) (lexSeq n ds h j) :=
  Classical.choose_spec (exists_isLexFSeg n (extDeg ds j) (dimF n ds j - h j))

/-- (2) ⇒ (3) of `thm-ac42`, core: if `h_j ≤ dim F_j` and `h_{j+1} ≤ B(h_j,j)` for all `j`, the
`lexF` segments `L_j` of size `dim F_j − h_j` form a lex submodule with quotient Hilbert
function `h`. -/
theorem lexSeq_isLexSubmodule {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·)) (h : ℤ → ℕ)
    (hdim : ∀ j, h j ≤ dimF n ds j) (hB : ∀ j, h (j + 1) ≤ Bωj n ds (h j) j) :
    IsLexSubmodule n ds (lexSeq n ds h) ∧ ∀ j, quotHF n ds (lexSeq n ds h) j = h j := by
  refine ⟨⟨⟨fun j => (lexSeq_spec n ds h j).1.imp fun _ _ h' => h'.1, fun j => ?_⟩,
    fun j => ⟨_, lexSeq_spec n ds h j⟩⟩, fun j => ?_⟩
  · have hks := extDeg_pairwise hds j
    have hL := lexSeq_spec n ds h j
    have hL' : IsLexFSeg n ((extDeg ds j).map (· + 1)) (dimF n ds (j + 1) - h (j + 1))
        (lexSeq n ds h (j + 1)) := by
      rw [← extDeg_succ]; exact lexSeq_spec n ds h (j + 1)
    refine lem_lexF_shadow_subset hks hL hL' ?_
    rw [hL.shadow_sum, hL'.card_sum]
    have hT := hdim j
    have hT' := hdim (j + 1)
    have hb := hB j
    have e1 := cost_greedy_add_Bω (extDeg ds j) hks (dimF n ds j - h j) (Nat.sub_le _ _)
    unfold dimF at hT hT' e1 ⊢
    unfold Bωj at hb
    rw [extDeg_succ] at hT' ⊢
    rw [show tailCap n (extDeg ds j) 0 - (tailCap n (extDeg ds j) 0 - h j) = h j by omega] at e1
    rw [min_eq_left (Nat.sub_le _ _)]
    omega
  · have hs := (lexSeq_spec n ds h j).card_sum
    unfold quotHF
    unfold dimF at hs ⊢
    have := hdim j
    unfold dimF at this
    rw [hs, min_eq_left (Nat.sub_le _ _)]
    omega

/-- **Theorem `thm-ac42`, (2) ⇒ (3)**, with the paper's support conditions: if `h_j = 0` outside
`[d₁, d_r + n]` and `h_{j+1} ≤ B(h_j, j)` for `j ∈ [d₁ − 1, d_r + n − 1]`, then `h` is the quotient
Hilbert function of a lex submodule. -/
theorem thm_ac42_two_three {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·)) {d₁ dr : ℤ} (h : ℤ → ℕ)
    (hsupp : ∀ j, j < d₁ ∨ dr + n < j → h j = 0)
    (hB : ∀ j, d₁ - 1 ≤ j → j ≤ dr + n - 1 → h (j + 1) ≤ Bωj n ds (h j) j) :
    ∃ L, IsLexSubmodule n ds L ∧ ∀ j, quotHF n ds L j = h j := by
  have hB' : ∀ j, h (j + 1) ≤ Bωj n ds (h j) j := by
    intro j
    by_cases hj : d₁ - 1 ≤ j ∧ j ≤ dr + n - 1
    · exact hB j hj.1 hj.2
    · rw [hsupp (j + 1) (by omega)]; exact Nat.zero_le _
  have hnat : ∀ m : ℕ, h (d₁ - 1 + m) ≤ dimF n ds (d₁ - 1 + m) := by
    intro m
    induction m with
    | zero => rw [hsupp _ (by omega)]; exact Nat.zero_le _
    | succ m ih =>
      have := hB' (d₁ - 1 + m)
      have hle := Bω_le (n := n) (extDeg_pairwise hds (d₁ - 1 + m)) ih
      unfold Bωj at this
      unfold dimF
      rw [show d₁ - 1 + ((m + 1 : ℕ) : ℤ) = d₁ - 1 + m + 1 by push_cast; ring, extDeg_succ]
      omega
  have hdim : ∀ j, h j ≤ dimF n ds j := by
    intro j
    by_cases hj : d₁ - 1 ≤ j
    · have := hnat (j - (d₁ - 1)).toNat
      rwa [show d₁ - 1 + ((j - (d₁ - 1)).toNat : ℤ) = j by omega] at this
    · rw [hsupp j (by omega)]; exact Nat.zero_le _
  exact ⟨_, lexSeq_isLexSubmodule hds h hdim hB'⟩

/-- **Theorem `thm-ac42`, uniqueness**: a lex submodule is determined by its quotient Hilbert
function. -/
theorem thm_ac42_unique {ds : List ℤ} {L L' : ℤ → List (Finset (Finset (Fin n)))}
    (hL : IsLexSubmodule n ds L) (hL' : IsLexSubmodule n ds L')
    (hh : ∀ j, quotHF n ds L j = quotHF n ds L' j) : L = L' := by
  funext j
  obtain ⟨t, ht⟩ := hL.2 j
  obtain ⟨t', ht'⟩ := hL'.2 j
  have h1 := sum_card_le_tailCap (hL.1.comp j)
  have h2 := sum_card_le_tailCap (hL'.1.comp j)
  have := hh j
  unfold quotHF dimF at this
  exact isLexFSeg_unique' ht ht' (by omega)

/-- **Theorem `thm-ac42` for monomial submodules** (`A&C` Theorem 4.2): for `h : ℤ → ℕ` with
`h_j = 0` outside `[d₁, d_r + n]`, the following are equivalent:
(1_mon) `h = H_{F/M}` for a monomial submodule `M ⊆ F`;
(2) `h_{j+1} ≤ B(h_j, j)` for every `j ∈ [d₁ − 1, d_r + n − 1]` (where `h_{d₁−1} = 0`);
(3) `h = H_{F/L}` for a lex submodule `L ⊆ F`.
Here `d₁ = ds.head`, `d_r = ds.getLast` (the hypotheses `hd₁`, `hdr`); the proof does not use
them, so the equivalence holds for any window `[d₁, d_r + n]` containing the support of `h`. -/
theorem thm_ac42_mon {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·)) {d₁ dr : ℤ}
    (_hd₁ : ds.head? = some d₁) (_hdr : ds.getLast? = some dr) (h : ℤ → ℕ)
    (hsupp : ∀ j, j < d₁ ∨ dr + n < j → h j = 0) :
    List.TFAE [∃ A, IsMonSubmodule n ds A ∧ ∀ j, quotHF n ds A j = h j,
      ∀ j, d₁ - 1 ≤ j → j ≤ dr + n - 1 → h (j + 1) ≤ Bωj n ds (h j) j,
      ∃ L, IsLexSubmodule n ds L ∧ ∀ j, quotHF n ds L j = h j] := by
  tfae_have 1 → 2 := by
    rintro ⟨A, hA, hAh⟩ j _ _
    have := cor_prop41_mon hds hA j
    rwa [hAh, hAh] at this
  tfae_have 2 → 3 := thm_ac42_two_three hds h hsupp
  tfae_have 3 → 1 := fun ⟨L, hL, hLh⟩ => ⟨L, hL.1, hLh⟩
  tfae_finish

end Submodule

/-! ### Target 6: `cor-initial` -/

section Initial

variable {n : ℕ}

lemma count_le_tailCap : ∀ (ks : List ℤ), ks.count 0 ≤ tailCap n ks 0
  | [] => by simp
  | k :: ks => by
    rw [tailCap_cons_zero, List.count_cons]
    have : ks.count 0 ≤ tailCap n ks 0 := count_le_tailCap ks
    by_cases hk : k = 0
    · subst hk; simp [capZ]; omega
    · simp [hk]; omega

lemma tailCap_of_nonpos : ∀ {ks : List ℤ}, (∀ k ∈ ks, k ≤ 0) → tailCap n ks 0 = ks.count 0
  | [], _ => by simp
  | k :: ks, h => by
    rw [tailCap_cons_zero, tailCap_of_nonpos (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')),
      List.count_cons]
    have hk := h k List.mem_cons_self
    rcases lt_or_eq_of_le hk with hk | rfl
    · simp [capZ, show ¬ (0 ≤ k) by omega, show k ≠ 0 by omega]
    · simp [capZ]; omega

lemma tailCap_succ_of_nonpos : ∀ {ks : List ℤ}, (∀ k ∈ ks, k ≤ 0) →
    tailCap n (ks.map (· + 1)) 0 = n * ks.count 0 + ks.count (-1)
  | [], _ => by simp
  | k :: ks, h => by
    rw [List.map_cons, tailCap_cons_zero,
      tailCap_succ_of_nonpos (fun k' hk' => h k' (List.mem_cons_of_mem _ hk')),
      List.count_cons, List.count_cons]
    have hk := h k List.mem_cons_self
    rcases (show k = 0 ∨ k = -1 ∨ k ≤ -2 by omega) with rfl | rfl | hk2
    · simp [capZ]; ring
    · simp [capZ]; ring
    · simp [capZ, show ¬ (0 ≤ k + 1) by omega, show k ≠ 0 by omega, show k ≠ -1 by omega]

/-- A leading component of degree `k ≥ 0` does not affect `B(h,j)` while `h` fits in the rest,
provided the Macaulay term vanishes at `a = 0`. -/
lemma growthB_cons_of_le {M : ℕ → ℕ → ℕ} (hM0 : ∀ k, M k 0 = 0) {k : ℤ} {ks : List ℤ}
    (hk : 0 ≤ k) {h : ℕ} (hh : h ≤ tailCap n ks 0) :
    growthB M n (k :: ks) h = growthB M n ks h := by
  by_cases hfull : tailCap n (k :: ks) 0 ≤ h
  · rw [tailCap_cons_zero] at hfull
    have hC : capZ n k = 0 := by omega
    have hC1 : capZ n (k + 1) = 0 := by
      rw [capZ_succ_of_nonneg hk]
      simp only [capZ, hk, ↓reduceIte] at hC
      exact Nat.choose_eq_zero_of_lt (by have := Nat.choose_eq_zero_iff.mp hC; omega)
    rw [growthB_of_le (by rw [tailCap_cons_zero]; omega), growthB_of_le (by omega)]
    simp [hC1]
  · rw [growthB_cons (by omega)]
    split_ifs with h0
    · have : h = tailCap n ks 0 := le_antisymm hh h0
      rw [this, Nat.sub_self, hM0, add_zero, growthB_of_le le_rfl]
    · rfl

/-- The computation behind `cor-initial`: for `k₁ ≥ ⋯ ≥ k_r` and `0 ≤ h ≤ #{i : kᵢ = 0}`,
`B(h,j) = n·h + #{i : kᵢ = −1}`, for every Macaulay term with `M k 0 = 0` (here `a = 0`
throughout, so `def-B` and its ω-form agree). -/
theorem growthB_count {M : ℕ → ℕ → ℕ} (hM0 : ∀ k, M k 0 = 0) : ∀ (ks : List ℤ),
    ks.Pairwise (· ≥ ·) → ∀ h, h ≤ ks.count 0 → growthB M n ks h = n * h + ks.count (-1)
  | [], _, h, hh => by
    simp only [List.count_nil, Nat.le_zero] at hh; subst hh
    simp [growthB_of_le]
  | k :: ks, hks, h, hh => by
    rw [List.pairwise_cons] at hks
    by_cases hk : 1 ≤ k
    · have hc0 : (k :: ks).count 0 = ks.count 0 := by
        simp [show k ≠ 0 by omega]
      have hc1 : (k :: ks).count (-1) = ks.count (-1) := by
        simp [show k ≠ -1 by omega]
      rw [hc0] at hh
      rw [growthB_cons_of_le hM0 (by omega) (le_trans hh (count_le_tailCap ks)), hc1]
      exact growthB_count hM0 ks hks.2 h hh
    · have hall : ∀ k' ∈ k :: ks, k' ≤ 0 := by
        intro k' hk'
        rcases List.mem_cons.mp hk' with rfl | hk'
        · omega
        · have := hks.1 k' hk'; omega
      by_cases hfull : h = (k :: ks).count 0
      · rw [growthB_of_le (by rw [tailCap_of_nonpos hall]; omega), tailCap_succ_of_nonpos hall,
          hfull]
      · have hk0 : k = 0 := by
          by_contra hne
          have : (k :: ks).count 0 = 0 := by
            rw [List.count_eq_zero]
            intro hm
            rcases List.mem_cons.mp hm with h' | h'
            · exact hne h'.symm
            · have := hks.1 0 h'; omega
          omega
        subst hk0
        have hc0 : ((0 : ℤ) :: ks).count 0 = ks.count 0 + 1 := by simp
        have hc1 : ((0 : ℤ) :: ks).count (-1) = ks.count (-1) := by simp
        have hall' : ∀ k' ∈ ks, k' ≤ 0 := fun k' hk' => hall k' (List.mem_cons_of_mem _ hk')
        rw [hc0] at hh hfull
        rw [growthB_cons_of_le hM0 le_rfl (by rw [tailCap_of_nonpos hall']; omega), hc1]
        exact growthB_count hM0 ks hks.2 h (by omega)

lemma count_extDeg (ds : List ℤ) (j c : ℤ) : (extDeg ds j).count c = ds.count (j - c) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [extDeg, List.map_cons, List.count_cons] at ih ⊢
    rw [ih]
    by_cases h : d = j - c
    · simp [h]
    · simp [h, show j - d ≠ c by omega]

/-- **Corollary `cor-initial`**, for `def-B` with any Macaulay term `M` with `M k 0 = 0` (true of
`a^{(k)}`, by the convention `0^{(k)} = 0`, and of the shadow form `macShadow`): with
`r̃₀ = #{i : dᵢ = j₀}` and `r̃₁ = #{i : dᵢ = j₀ + 1}`, `B(0, j₀ − 1) = r̃₀`, and
`B(h, j₀) = n·h + r̃₁` for `1 ≤ h ≤ r̃₀`. The Macaulay term vanishes in both evaluations (`a = 0`).
The paper takes `j₀` to be the initial degree of `h`; the identities hold for every `j₀ ∈ ℤ`
(and the second also for `h = 0`). -/
theorem cor_initial_growthB {M : ℕ → ℕ → ℕ} (hM0 : ∀ k, M k 0 = 0) {ds : List ℤ}
    (hds : ds.Pairwise (· ≤ ·)) (j₀ : ℤ) :
    growthB M n (extDeg ds (j₀ - 1)) 0 = ds.count j₀ ∧
      ∀ h, 1 ≤ h → h ≤ ds.count j₀ →
        growthB M n (extDeg ds j₀) h = n * h + ds.count (j₀ + 1) := by
  refine ⟨?_, fun h _ hh => ?_⟩
  · rw [growthB_count hM0 _ (extDeg_pairwise hds _) 0 (Nat.zero_le _), count_extDeg]
    rw [mul_zero, zero_add, show j₀ - 1 - -1 = j₀ by ring]
  · rw [growthB_count hM0 _ (extDeg_pairwise hds _) h (by rw [count_extDeg, sub_zero]; exact hh),
      count_extDeg, show j₀ - -1 = j₀ + 1 by ring]

/-- **Corollary `cor-initial`** (ω-form `Bωj`). -/
theorem cor_initial {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·)) (j₀ : ℤ) :
    Bωj n ds 0 (j₀ - 1) = ds.count j₀ ∧
      ∀ h, 1 ≤ h → h ≤ ds.count j₀ → Bωj n ds h j₀ = n * h + ds.count (j₀ + 1) :=
  cor_initial_growthB (macShadow_zero n) hds j₀

/-- `cor-initial`, last sentence: if `h_{j₀−1} = 0` and `h_{j₀} ≥ 1`, the instances `j = j₀ − 1` and
`j = j₀` of condition (2) of `thm-ac42` are `h_{j₀} ≤ r̃₀` and `h_{j₀+1} ≤ n·h_{j₀} + r̃₁`. -/
theorem cor_initial_instances {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·)) (h : ℤ → ℕ) (j₀ : ℤ)
    (h0 : h (j₀ - 1) = 0) (h1 : 1 ≤ h j₀) :
    (h j₀ ≤ Bωj n ds (h (j₀ - 1)) (j₀ - 1) ↔ h j₀ ≤ ds.count j₀) ∧
      (h j₀ ≤ ds.count j₀ →
        (h (j₀ + 1) ≤ Bωj n ds (h j₀) j₀ ↔ h (j₀ + 1) ≤ n * h j₀ + ds.count (j₀ + 1))) := by
  obtain ⟨c1, c2⟩ := cor_initial (n := n) hds j₀
  refine ⟨by rw [h0, c1], fun hh => by rw [c2 _ h1 hh]⟩

end Initial

/-! ### Numerical anchors (entrywise) -/

section Anchors

/-! `ex-lexF-n3`: `n = 3`, `d = (0,1)`, `j = 2`: `k = (2,1)`, `dim F_2 = 3 + 3`. -/

example : extDeg [0, 1] 2 = [2, 1] := by decide
example : dimF 3 [0, 1] 2 = 6 := by decide
-- the `lexF` segment of size 4 fills component 1 (3 sets) and takes 1 set of component 2
example : greedy (capZ 3) [2, 1] 4 = [3, 1] := by decide
-- its shadow sizes, component by component: `|∇(all 2-sets)| = 1`, `|∇{{1}}| = 2`
example : List.zipWith (costZ 3) [2, 1] [3, 1] = [1, 2] := by decide
-- `|Shad L| = 3`, and `Shad L` is the `lexF` segment of size 3 of `Mon_3(F)` (sizes `(1,2)`)
example : cost (costZ 3) [2, 1] (greedy (capZ 3) [2, 1] 4) = 3 := by decide
example : greedy (capZ 3) ([2, 1].map (· + 1)) 3 = [1, 2] := by decide
example : dimF 3 [0, 1] 3 = 4 := by decide
-- the sets themselves (`Fin 3` = `{0,1,2}` for the paper's `[3] = {1,2,3}`)
example : ∂⁺ ({{0, 1}, {0, 2}, {1, 2}} : Finset (Finset (Fin 3))) = {{0, 1, 2}} := by decide
example : ∂⁺ ({{0}} : Finset (Finset (Fin 3))) = {{0, 1}, {0, 2}} := by decide
-- `h = 2`: `ℓ = 2`, `a = 2`, `k_ℓ = 1`, `B(2,2) = 1 = 4 − 3`
example : ellB 3 (extDeg [0, 1] 2) 2 = 2 := ellB_eq_iff.mpr ⟨by decide, by decide⟩
example : remB 3 (extDeg [0, 1] 2) 2 = 2 := by
  rw [remB, (ellB_eq_iff (ℓ := 2)).mpr ⟨by decide, by decide⟩]; decide
example : kB 3 (extDeg [0, 1] 2) 2 = 1 := by
  rw [kB, (ellB_eq_iff (ℓ := 2)).mpr ⟨by decide, by decide⟩]; decide
example : Bωj 3 [0, 1] 2 2 = 1 := by
  rw [Bωj, Bω, growthB_eq_of (ℓ := 2) (by decide) (by decide)]; decide

/-! `ex-kk-n3-d01`: `n = 3`, `d = (0,1)`, `dim F_j = 1, 4, 6, 4, 1`; `B(4,2) = 3` (`ℓ = 1`,
`a = 1`), `B(3,3) = 1` (`ℓ = 1`, `a = 0`); `n = 4`, `d = (0,1)`: `B(6,2) = 6` (`ℓ = 1`, `a = 2`). -/

example : [0, 1, 2, 3, 4].map (dimF 3 [0, 1]) = [1, 4, 6, 4, 1] := by decide
example : ellB 3 (extDeg [0, 1] 2) 4 = 1 := ellB_eq_iff.mpr ⟨by decide, by decide⟩
example : remB 3 (extDeg [0, 1] 2) 4 = 1 := by
  rw [remB, (ellB_eq_iff (ℓ := 1)).mpr ⟨by decide, by decide⟩]; decide
example : Bωj 3 [0, 1] 4 2 = 3 := by
  rw [Bωj, Bω, growthB_eq_of (ℓ := 1) (by decide) (by decide)]; decide
example : ellB 3 (extDeg [0, 1] 3) 3 = 1 := ellB_eq_iff.mpr ⟨by decide, by decide⟩
example : remB 3 (extDeg [0, 1] 3) 3 = 0 := by
  rw [remB, (ellB_eq_iff (ℓ := 1)).mpr ⟨by decide, by decide⟩]; decide
example : Bωj 3 [0, 1] 3 3 = 1 := by
  rw [Bωj, Bω, growthB_eq_of (ℓ := 1) (by decide) (by decide)]; decide
example : dimF 4 [0, 1] 2 = 10 := by decide
example : ellB 4 (extDeg [0, 1] 2) 6 = 1 := ellB_eq_iff.mpr ⟨by decide, by decide⟩
example : remB 4 (extDeg [0, 1] 2) 6 = 2 := by
  rw [remB, (ellB_eq_iff (ℓ := 1)).mpr ⟨by decide, by decide⟩]; decide
example : Bωj 4 [0, 1] 6 2 = 6 := by
  rw [Bωj, Bω, growthB_eq_of (ℓ := 1) (by decide) (by decide)]; decide

/-! `ex-ac-smallest`: `n = 1`, `d = (0,0)`: `B(0,−1) = 2 = r̃₀`, `B(1,0) = 1 = n·1 + r̃₁ < 2`. -/

example : Bωj 1 [0, 0] 0 (-1) = 2 := by
  rw [Bωj, Bω, growthB_eq_of (ℓ := 0) (by decide) (by decide)]; decide
example : Bωj 1 [0, 0] 1 0 = 1 := by
  rw [Bωj, Bω, growthB_eq_of (ℓ := 1) (by decide) (by decide)]; decide

/-! `ex-lexF-n3` on the sets themselves: the paper's
`L = {e₁e₂g₁, e₁e₃g₁, e₂e₃g₁, e₁g₂}` is the `lexF` segment of size `4` of `Mon_2(F)`, and
`Shad L = {e₁e₂e₃g₁, e₁e₂g₂, e₁e₃g₂}` is the `lexF` segment of size `3` of `Mon_3(F)`
(`Fin 3 = {0,1,2}` for `[3] = {1,2,3}`). Checked by `decide` on the definitions, not via the
lemmas above. -/

instance (n : ℕ) (s t : Finset (Fin n)) : Decidable (LexLT s t) := by
  unfold LexLT; infer_instance

lemma isLexInit_iff_forall {n : ℕ} (𝒜 : Finset (Finset (Fin n))) (k : ℕ) :
    IsLexInit 𝒜 k ↔ (∀ s ∈ 𝒜, #s = k) ∧
      ∀ s ∈ 𝒜, ∀ t : Finset (Fin n), LexLT t s → #t = k → t ∈ 𝒜 := by
  unfold IsLexInit Set.Sized; simp only [mem_coe]
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, fun s hs t => h2 hs⟩, fun ⟨h1, h2⟩ => ⟨h1, fun s t hs => h2 s hs t⟩⟩

example : IsLexFSeg 3 (extDeg [0, 1] 2) 4 [{{0, 1}, {0, 2}, {1, 2}}, {{0}}] := by
  refine ⟨?_, by decide⟩
  refine List.Forall₂.cons ⟨⟨?_, by decide⟩, ?_⟩
    (List.Forall₂.cons ⟨⟨?_, by decide⟩, ?_⟩ List.Forall₂.nil)
  · intro s hs; simp only [mem_coe] at hs; revert s; decide
  · rw [isLexInit_iff_forall]; decide
  · intro s hs; simp only [mem_coe] at hs; revert s; decide
  · rw [isLexInit_iff_forall]; decide

example : IsLexFSeg 3 (extDeg [0, 1] 3) 3 [{{0, 1, 2}}, {{0, 1}, {0, 2}}] := by
  refine ⟨?_, by decide⟩
  refine List.Forall₂.cons ⟨⟨?_, by decide⟩, ?_⟩
    (List.Forall₂.cons ⟨⟨?_, by decide⟩, ?_⟩ List.Forall₂.nil)
  · intro s hs; simp only [mem_coe] at hs; revert s; decide
  · rw [isLexInit_iff_forall]; decide
  · intro s hs; simp only [mem_coe] at hs; revert s; decide
  · rw [isLexInit_iff_forall]; decide

end Anchors

end ModuleKK
end ExteriorConvex

#print axioms ExteriorConvex.ModuleKK.exists_isLexFSeg
#print axioms ExteriorConvex.ModuleKK.isLexFSeg_unique
#print axioms ExteriorConvex.ModuleKK.isLexFInitial_iff
#print axioms ExteriorConvex.ModuleKK.lem_lexF_shadow
#print axioms ExteriorConvex.ModuleKK.lem_lexF_shadow_subset
#print axioms ExteriorConvex.ModuleKK.growthB_congr
#print axioms ExteriorConvex.ModuleKK.cost_greedy_add_Bω
#print axioms ExteriorConvex.ModuleKK.thm_module_kk_formula
#print axioms ExteriorConvex.ModuleKK.thm_module_kk_ineq_mon
#print axioms ExteriorConvex.ModuleKK.thm_module_kk_bound_mon
#print axioms ExteriorConvex.ModuleKK.cor_prop41_mon
#print axioms ExteriorConvex.ModuleKK.thm_ac42_two_three
#print axioms ExteriorConvex.ModuleKK.thm_ac42_unique
#print axioms ExteriorConvex.ModuleKK.thm_ac42_mon
#print axioms ExteriorConvex.ModuleKK.cor_initial_growthB
#print axioms ExteriorConvex.ModuleKK.cor_initial
#print axioms ExteriorConvex.ModuleKK.cor_initial_instances
