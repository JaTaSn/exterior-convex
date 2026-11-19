/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Part IV: the second proof (`lem-certificate`, `lem-path-rank`, `lem-tight`, `lem-tight-edge`,
# `prop-certified-span`)

`article/exterior-convex_article4_draft_1.org`, Section "A second proof, through the facet normals".

| Part IV | here |
|---|---|
| "`u` is tight at `x`", `u · x = h(u, R)` | `TightAt R x u` (`∀ y ∈ R, u · y ≤ u · x`) |
| `φ = ∑_{u tight} u` | `certFun R x U` |
| **`lem-certificate`** | **`lem_certificate`** (any linear form `e` constant on `R` in place of `e_1`); the paper's `e_1` form: `lem_certificate_e1` |
| anchor / link, the multigraph `G`, its components | `IsAnchorAt`, `IsLinkAt`; `Edge`, `Joined`, `IsStart` (a component is indexed by its first coordinate) |
| anchored component | `Anchored` |
| the non-anchored components | `freeStarts` |
| **`lem-path-rank`** | **`lem_path_rank`** |
| the remark "tightness is checked summand by summand" | `tightAt_iff` |
| the directions `u(p; c)`, `u^C_p`, `u^D_p`, `u^F` | `linkU a N (d p) c`, `-eVec N (d p + 1)`, `eVec N (d (p−1) + n + 1)`, `-eVec N N` |
| **`lem-tight`** (1)–(4) | **`lem_tight_link`**, **`lem_tight_C`**, **`lem_tight_D`**, **`lem_tight_F`** |
| "certified", "belongs to the list" | `CertLink`, `InList`; the certified directions as a set: `certSet` |
| **`lem-tight-edge`** (1), (2) | **`lem_tight_edge_one`**, **`lem_tight_edge_two`** (with `k = cnt d J r c`) |
| **`prop-certified-span`** | **`prop_certified_span`** |
| the second proof of sufficiency in `thm-vdesc`, reduced case | `second_proof_vertex` (with `certSet_tight`) |

Vectors are points of `Fin N → ℝ`, the dot product is `⬝ᵥ`, coordinates are the manuscript's
`1, …, N` through `Facets.co`.  Windows are indexed `p = 0, …, r−1` (the paper's `1, …, r`), so
the paper's "`p ≥ 2`" is `0 < p` here; `R = RAsum a N n d r`, `x(𝐣) = xJ a N d r J`.

**`lem-tight`, scope.**  (1) is proved for every link `u(p; c)` with `c, c+1 ∈ W_p` (the list
asks in addition `c ≥ d_p + 2` for `p ≥ 2`); none of (1)–(4) needs the gap bound or `d_1 = 0`.
**Finding: (4) needs `n ≥ 2`.**  For `n = 1` (which, with distinct shifts and gaps `≤ n − 1`, forces
`r = 1`) the polytope is the single point `a_1 e_1`, `u^F` is tight, but `m_r = N`, so the printed
"iff" fails.  The section has no standing `n ≥ 2` (the facet section does); harmless for the
second proof, since then `R` is a point.  `lem_tight_F` assumes `2 ≤ n`.

**`prop-certified-span`, hypotheses.**  "Whenever `m_p < m_{p+1}` and both lie in the overlap
`O_p`, the ratio is not constant on `[m_p+1, m_{p+1}]`" is stated as
`¬ Pairwise.Locked a n (d p) (d (p+1)) (m p) (m (p+1))` (Lemma `lem-locked`'s definition, which is
exactly this).  Weak log-concavity is not used in the proposition itself (only in `lem-tight`).

**`lem-certificate`, scope.**  The lemma is stated for any finite family of sets `P p` and any
points `x^{(p)} ∈ P p` (polytopes and vertices are not needed: the proof uses neither), and for any
vector `e` with `e · y` constant on `R` in place of `e_1`; `lem_certificate_e1` is the printed form.

**`lem-path-rank`, encoding.**  The components of `G` are intervals; the component containing a
coordinate is identified with its first coordinate `s` (`IsStart`: `1 ≤ s ≤ N` and no link on the
edge `{s−1, s}`), and `Joined s c` says that `s ≤ c` and every edge between them carries a link.  A
component is anchored iff some `c` joined to its start carries an anchor or two linearly
independent links on the edge `{c, c+1}` (`LinearIndependent ℝ ![v, w]`).  The proof is the
paper's, read on the annihilator: the vectors orthogonal to `S` vanish on anchored components and
are determined on a non-anchored one by their value at its start (`ker_equiv_bijective`).

Changelog (newest first): 2026-11-17 created (Claude-Code agent, run `2026-11-17_lean-parts-4-5`)
-/
import Mathlib
import ExteriorConvex.Facets.Tight
import ExteriorConvex.Vertices.PairwiseReduction

namespace ExteriorConvex
namespace SecondProof

open Finset Matrix Facets
open scoped Pointwise

variable {N : ℕ}

/-! ## `lem-certificate` -/

/-- `u` is **tight at `x`** on `R`: `u · x` is the maximum `h(u, R)` of `u` over `R`. -/
def TightAt (R : Set (Fin N → ℝ)) (x u : Fin N → ℝ) : Prop := ∀ y ∈ R, u ⬝ᵥ y ≤ u ⬝ᵥ x

open Classical in
/-- The certificate functional `φ = ∑_{u ∈ U tight at x} u`. -/
noncomputable def certFun (R : Set (Fin N → ℝ)) (x : Fin N → ℝ) (U : Finset (Fin N → ℝ)) :
    Fin N → ℝ :=
  ∑ u ∈ U.filter (TightAt R x), u

/-- A vector orthogonal to a spanning set is zero. -/
lemma eq_zero_of_span_eq_top {T : Set (Fin N → ℝ)} (hT : Submodule.span ℝ T = ⊤)
    {w : Fin N → ℝ} (hw : ∀ u ∈ T, u ⬝ᵥ w = 0) : w = 0 := by
  have key : ∀ v ∈ Submodule.span ℝ T, v ⬝ᵥ w = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem u hu => exact hw u hu
    | zero => exact zero_dotProduct w
    | add u v _ _ hu hv => rw [add_dotProduct, hu, hv, add_zero]
    | smul t u _ hu => rw [smul_dotProduct, hu, smul_zero]
  funext i
  have := key (Pi.single i 1) (by rw [hT]; trivial)
  rwa [single_dotProduct, one_mul] at this

open Classical in
/-- **`lem-certificate`** (a rank certificate).  Let `R = ∑_{p ∈ s} P p`, `x = ∑_p x^{(p)}` with
`x^{(p)} ∈ P p`, `e · y` constant on `R` (the paper: `e = e_1`, `x_1` constant on `R`), and `U` a
finite set of vectors.  If the vectors of `U` tight at `x`, together with `e`, span `ℝ^N`, then
`φ = ∑_{u tight} u` is uniquely maximised on `R` at `x`, and on every `P p` at `x^{(p)}`; in
particular `x` is a vertex of `R`. -/
theorem lem_certificate {ι : Type*} [DecidableEq ι] (s : Finset ι) (P : ι → Set (Fin N → ℝ))
    (xp : ι → Fin N → ℝ) (hxp : ∀ p ∈ s, xp p ∈ P p) (e : Fin N → ℝ)
    (he : ∀ y ∈ ∑ p ∈ s, P p, e ⬝ᵥ y = e ⬝ᵥ ∑ p ∈ s, xp p) (U : Finset (Fin N → ℝ))
    (hspan : Submodule.span ℝ
      (insert e (U.filter (TightAt (∑ p ∈ s, P p) (∑ p ∈ s, xp p)) : Set (Fin N → ℝ))) = ⊤) :
    (∀ y ∈ ∑ p ∈ s, P p, y ≠ ∑ p ∈ s, xp p →
        certFun (∑ p ∈ s, P p) (∑ p ∈ s, xp p) U ⬝ᵥ y <
          certFun (∑ p ∈ s, P p) (∑ p ∈ s, xp p) U ⬝ᵥ ∑ p ∈ s, xp p) ∧
      (∀ p ∈ s, ∀ z ∈ P p, z ≠ xp p →
        certFun (∑ p ∈ s, P p) (∑ p ∈ s, xp p) U ⬝ᵥ z <
          certFun (∑ p ∈ s, P p) (∑ p ∈ s, xp p) U ⬝ᵥ xp p) ∧
      ∑ p ∈ s, xp p ∈ Set.extremePoints ℝ (∑ p ∈ s, P p) := by
  set R := ∑ p ∈ s, P p with hR
  set x := ∑ p ∈ s, xp p with hx
  set T := U.filter (TightAt R x) with hT
  set φ := certFun R x U with hφ
  have hφT : φ = ∑ u ∈ T, u := rfl
  have hxR : x ∈ R := (Set.mem_finsetSum _ _ _).mpr ⟨xp, fun hp => hxp _ hp, rfl⟩
  -- the weak inequality, and the equality case
  have hle : ∀ y ∈ R, ∀ u ∈ T, u ⬝ᵥ y ≤ u ⬝ᵥ x := fun y hy u hu =>
    (Finset.mem_filter.mp hu).2 y hy
  have hmax : ∀ y ∈ R, φ ⬝ᵥ y ≤ φ ⬝ᵥ x := fun y hy => by
    rw [hφT, sum_dotProduct, sum_dotProduct]
    exact Finset.sum_le_sum (hle y hy)
  have heq : ∀ y ∈ R, φ ⬝ᵥ y = φ ⬝ᵥ x → y = x := by
    intro y hy h
    rw [hφT, sum_dotProduct, sum_dotProduct, Finset.sum_eq_sum_iff_of_le (hle y hy)] at h
    have h0 : y - x = 0 := by
      refine eq_zero_of_span_eq_top hspan fun u hu => ?_
      rcases Set.mem_insert_iff.mp hu with rfl | hu
      · rw [dotProduct_sub, he y hy, sub_self]
      · rw [dotProduct_sub, h u hu, sub_self]
    exact sub_eq_zero.mp h0
  have hstrict : ∀ y ∈ R, y ≠ x → φ ⬝ᵥ y < φ ⬝ᵥ x := fun y hy hne =>
    lt_of_le_of_ne (hmax y hy) fun h => hne (heq y hy h)
  refine ⟨hstrict, fun p hp z hz hne => ?_, ⟨hxR, fun x₁ hx₁ x₂ hx₂ hseg => ?_⟩⟩
  · -- the summands: replace `x^{(p)}` by `z`
    have hmem : ∑ q ∈ s, Function.update xp p z q ∈ R := by
      rw [hR, Set.mem_finsetSum]
      refine ⟨Function.update xp p z, fun {q} hq => ?_, rfl⟩
      rcases eq_or_ne q p with rfl | h
      · simpa using hz
      · rw [Function.update_of_ne h]; exact hxp q hq
    have hsum : ∑ q ∈ s, Function.update xp p z q = z - xp p + x := by
      rw [Finset.sum_update_of_mem hp, hx, ← Finset.add_sum_erase s xp hp,
        Finset.sdiff_singleton_eq_erase]
      abel
    have hne' : ∑ q ∈ s, Function.update xp p z q ≠ x := by
      rw [hsum]
      intro h
      exact hne (sub_eq_zero.mp (by simpa using h))
    have := hstrict _ hmem hne'
    rw [hsum, dotProduct_add, dotProduct_sub] at this
    linarith
  · -- `x` is an extreme point
    obtain ⟨a, b, ha, hb, hab, hxe⟩ := hseg
    by_contra hne
    have h1 := hstrict x₁ hx₁ hne
    have h2 := hmax x₂ hx₂
    have hv : φ ⬝ᵥ x = a * φ ⬝ᵥ x₁ + b * φ ⬝ᵥ x₂ := by
      rw [← hxe, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    have : a * φ ⬝ᵥ x₁ + b * φ ⬝ᵥ x₂ < (a + b) * φ ⬝ᵥ x := by
      have := mul_lt_mul_of_pos_left h1 ha
      have := mul_le_mul_of_nonneg_left h2 hb.le
      linarith
    rw [hab, one_mul, ← hv] at this
    exact lt_irrefl _ this

open Classical in
/-- **`lem-certificate`, as printed**: `e = e_1`, with `x_1` constant on `R`. -/
theorem lem_certificate_e1 {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (P : ι → Set (Fin (N + 1) → ℝ)) (xp : ι → Fin (N + 1) → ℝ) (hxp : ∀ p ∈ s, xp p ∈ P p)
    (h1 : ∀ y ∈ ∑ p ∈ s, P p, y 0 = (∑ p ∈ s, xp p) 0) (U : Finset (Fin (N + 1) → ℝ))
    (hspan : Submodule.span ℝ (insert (Pi.single 0 1)
      (U.filter (TightAt (∑ p ∈ s, P p) (∑ p ∈ s, xp p)) : Set (Fin (N + 1) → ℝ))) = ⊤) :
    (∀ y ∈ ∑ p ∈ s, P p, y ≠ ∑ p ∈ s, xp p →
        certFun (∑ p ∈ s, P p) (∑ p ∈ s, xp p) U ⬝ᵥ y <
          certFun (∑ p ∈ s, P p) (∑ p ∈ s, xp p) U ⬝ᵥ ∑ p ∈ s, xp p) ∧
      (∀ p ∈ s, ∀ z ∈ P p, z ≠ xp p →
        certFun (∑ p ∈ s, P p) (∑ p ∈ s, xp p) U ⬝ᵥ z <
          certFun (∑ p ∈ s, P p) (∑ p ∈ s, xp p) U ⬝ᵥ xp p) ∧
      ∑ p ∈ s, xp p ∈ Set.extremePoints ℝ (∑ p ∈ s, P p) :=
  lem_certificate s P xp hxp (Pi.single 0 1)
    (fun y hy => by rw [single_dotProduct, single_dotProduct, one_mul, one_mul]; exact h1 y hy)
    U hspan

/-! ## `lem-path-rank` -/

/-- An **anchor** at the coordinate `c ∈ [1, N]`: a non-zero multiple of `e_c`. -/
def IsAnchorAt (v : Fin N → ℝ) (c : ℕ) : Prop :=
  1 ≤ c ∧ c ≤ N ∧ co v c ≠ 0 ∧ ∀ c', c' ≠ c → co v c' = 0

/-- A **link** on the edge `{c, c+1}` (`1 ≤ c`, `c + 1 ≤ N`): supported exactly on the pair. -/
def IsLinkAt (v : Fin N → ℝ) (c : ℕ) : Prop :=
  1 ≤ c ∧ c + 1 ≤ N ∧ co v c ≠ 0 ∧ co v (c + 1) ≠ 0 ∧ ∀ c', c' ≠ c → c' ≠ c + 1 → co v c' = 0

section PathRank

variable (S : Finset (Fin N → ℝ))

/-- The edge `{c, c+1}` of the multigraph `G` carries a link of `S`. -/
def Edge (c : ℕ) : Prop := ∃ v ∈ S, IsLinkAt v c

/-- `s ≤ c` lie in one component of `G`: every edge between them carries a link. -/
def Joined (s c : ℕ) : Prop := s ≤ c ∧ ∀ e, s ≤ e → e < c → Edge S e

/-- `s` is the first coordinate of its component of `G`. -/
def IsStart (s : ℕ) : Prop := 1 ≤ s ∧ s ≤ N ∧ ¬ Edge S (s - 1)

/-- The component starting at `s` is **anchored**: it contains the support of an anchor, or it
carries two linearly independent links on the same edge. -/
def Anchored (s : ℕ) : Prop :=
  ∃ c, Joined S s c ∧ ((∃ v ∈ S, IsAnchorAt v c) ∨
    ∃ v ∈ S, ∃ w ∈ S, IsLinkAt v c ∧ IsLinkAt w c ∧ LinearIndependent ℝ ![v, w])

open Classical in
/-- The **non-anchored components** of `G`, by their first coordinates. -/
noncomputable def freeStarts : Finset ℕ :=
  (Finset.Icc 1 N).filter fun s => IsStart S s ∧ ¬ Anchored S s

variable {S}

/-! ### Dot products with anchors and links -/

lemma co_eq_apply (z : Fin N → ℝ) (i : Fin N) : co z (i.val + 1) = z i := (co_val z i).symm

lemma dot_anchor {v : Fin N → ℝ} {c : ℕ} (hv : IsAnchorAt v c) (z : Fin N → ℝ) :
    v ⬝ᵥ z = co v c * co z c := by
  obtain ⟨h1, h2, -, h0⟩ := hv
  rw [dotProduct, Fintype.sum_eq_single (⟨c - 1, by omega⟩ : Fin N)]
  · rw [co_of v h1 h2, co_of z h1 h2]
  · intro i hi
    have : co v (i.val + 1) = 0 := h0 _ fun h => hi (Fin.ext (by simp; omega))
    rw [co_eq_apply] at this
    rw [this, zero_mul]

lemma dot_link {v : Fin N → ℝ} {c : ℕ} (hv : IsLinkAt v c) (z : Fin N → ℝ) :
    v ⬝ᵥ z = co v c * co z c + co v (c + 1) * co z (c + 1) := by
  obtain ⟨h1, h2, -, -, h0⟩ := hv
  rw [dotProduct, Fintype.sum_eq_add (⟨c - 1, by omega⟩ : Fin N) (⟨c, by omega⟩ : Fin N)
    (fun h => by have := congrArg Fin.val h; simp at this; omega)]
  · rw [co_of v h1 (by omega), co_of z h1 (by omega), co_of v (by omega) h2,
      co_of z (by omega) h2]
    rfl
  · rintro i ⟨hi1, hi2⟩
    have : co v (i.val + 1) = 0 := h0 _ (fun h => hi1 (Fin.ext (by simp; omega)))
      (fun h => hi2 (Fin.ext (by simp; omega)))
    rw [co_eq_apply] at this
    rw [this, zero_mul]

/-- Two links on one edge are linearly independent iff their `2 × 2` determinant is non-zero. -/
lemma linearIndependent_links_iff {v w : Fin N → ℝ} {c : ℕ} (hv : IsLinkAt v c)
    (hw : IsLinkAt w c) :
    LinearIndependent ℝ ![v, w] ↔ co v c * co w (c + 1) ≠ co v (c + 1) * co w c := by
  rw [LinearIndependent.pair_iff]
  constructor
  · intro h hdet
    have hz : co w c • v + (-co v c) • w = 0 := by
      apply ext_co
      intro c' h1 h2
      rw [co_add, co_smul, co_smul]
      simp only [co_of (0 : Fin N → ℝ) h1 h2, Pi.zero_apply]
      by_cases hc : c' = c
      · subst hc; ring
      · by_cases hc1 : c' = c + 1
        · subst hc1; linear_combination -hdet
        · rw [hv.2.2.2.2 c' hc hc1, hw.2.2.2.2 c' hc hc1]; ring
    exact hv.2.2.1 (neg_eq_zero.mp (h _ _ hz).2)
  · intro hdet s t hst
    have e1 := congrArg (fun x => co x c) hst
    have e2 := congrArg (fun x => co x (c + 1)) hst
    simp only [co_add, co_smul] at e1 e2
    rw [co_of (0 : Fin N → ℝ) hv.1 (by have := hv.2.1; omega), Pi.zero_apply] at e1
    rw [co_of (0 : Fin N → ℝ) (by omega) hv.2.1, Pi.zero_apply] at e2
    have hs : s * (co v c * co w (c + 1) - co v (c + 1) * co w c) = 0 := by
      linear_combination co w (c + 1) * e1 - co w c * e2
    have hs0 : s = 0 := by
      rcases mul_eq_zero.mp hs with h | h
      · exact h
      · exact absurd (sub_eq_zero.mp h) hdet
    subst hs0
    refine ⟨rfl, ?_⟩
    have : t * co w c = 0 := by linear_combination e1
    rcases mul_eq_zero.mp this with h | h
    · exact h
    · exact absurd h hw.2.2.1

/-! ### Vectors orthogonal to `S` -/

/-- `z` is orthogonal to every vector of `S`. -/
def Orth (S : Finset (Fin N → ℝ)) (z : Fin N → ℝ) : Prop := ∀ v ∈ S, v ⬝ᵥ z = 0

/-- Along an edge carrying a link, an orthogonal vector vanishes at one end iff at the other. -/
lemma orth_edge {z : Fin N → ℝ} (hz : Orth S z) {c : ℕ} (he : Edge S c) :
    co z c = 0 ↔ co z (c + 1) = 0 := by
  obtain ⟨v, hvS, hv⟩ := he
  have h := hz v hvS
  rw [dot_link hv] at h
  have hα := hv.2.2.1
  have hβ := hv.2.2.2.1
  constructor
  · intro h0
    rw [h0, mul_zero, zero_add] at h
    exact (mul_eq_zero.mp h).resolve_left hβ
  · intro h0
    rw [h0, mul_zero, add_zero] at h
    exact (mul_eq_zero.mp h).resolve_left hα

/-- Within a component, an orthogonal vector vanishes at one coordinate iff at any other. -/
lemma orth_joined {z : Fin N → ℝ} (hz : Orth S z) {s c : ℕ} (hj : Joined S s c) :
    co z s = 0 ↔ co z c = 0 := by
  obtain ⟨hsc, he⟩ := hj
  induction c, hsc using Nat.le_induction with
  | base => exact Iff.rfl
  | succ c hsc ih =>
    rw [ih fun e h1 h2 => he e h1 (by omega)]
    exact orth_edge hz (he c hsc (by omega))

/-- **On an anchored component an orthogonal vector vanishes** (at its start, hence everywhere). -/
lemma orth_anchored {z : Fin N → ℝ} (hz : Orth S z) {s : ℕ} (ha : Anchored S s) :
    co z s = 0 := by
  obtain ⟨c, hj, hac⟩ := ha
  rw [orth_joined hz hj]
  rcases hac with ⟨v, hvS, hv⟩ | ⟨v, hvS, w, hwS, hv, hw, hli⟩
  · have h := hz v hvS
    rw [dot_anchor hv] at h
    exact (mul_eq_zero.mp h).resolve_left hv.2.2.1
  · have hdet := (linearIndependent_links_iff hv hw).mp hli
    have h1 := hz v hvS
    have h2 := hz w hwS
    rw [dot_link hv] at h1
    rw [dot_link hw] at h2
    have : co z c * (co v c * co w (c + 1) - co v (c + 1) * co w c) = 0 := by
      linear_combination co w (c + 1) * h1 - co v (c + 1) * h2
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hdet)

/-- **Injectivity**: an orthogonal vector vanishing at the start of every non-anchored component
is zero. -/
lemma orth_eq_zero {z : Fin N → ℝ} (hz : Orth S z) (h0 : ∀ s ∈ freeStarts S, co z s = 0) :
    z = 0 := by
  classical
  have key : ∀ c, 1 ≤ c → c ≤ N → co z c = 0 := by
    intro c
    induction c with
    | zero => intro h; omega
    | succ c ih =>
      intro _ hcN
      by_cases he : Edge S c
      · have hc1 : 1 ≤ c := by obtain ⟨v, -, hv⟩ := he; exact hv.1
        exact (orth_edge hz he).mp (ih hc1 (by omega))
      · have hstart : IsStart S (c + 1) := ⟨by omega, hcN, by simpa using he⟩
        by_cases ha : Anchored S (c + 1)
        · exact orth_anchored hz ha
        · exact h0 _ (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, hcN⟩, hstart, ha⟩)
  apply ext_co
  intro c h1 h2
  rw [key c h1 h2, co_of (0 : Fin N → ℝ) h1 h2, Pi.zero_apply]

/-! ### The orthogonal vector of a non-anchored component -/

variable (S)

open Classical in
/-- The ratio `−α/β` of the chosen link `α e_c + β e_{c+1}` on the edge `c`. -/
noncomputable def ratio (c : ℕ) : ℝ :=
  if h : Edge S c then -(co h.choose c / co h.choose (c + 1)) else 0

open Classical in
/-- The vector of the component starting at `s`, coordinate by coordinate: `1` at `s`, continued
along the chosen links, `0` elsewhere. -/
noncomputable def zfun (s : ℕ) : ℕ → ℝ
  | 0 => 0
  | c + 1 => if c + 1 = s then 1 else if Edge S c then ratio S c * zfun s c else 0

/-- `zfun` as a point of `ℝ^N`. -/
noncomputable def zvec (s : ℕ) : Fin N → ℝ := fun i => zfun S s (i.val + 1)

variable {S}

lemma co_zvec (s : ℕ) {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ N) : co (zvec S s) c = zfun S s c := by
  rw [co_of _ h1 h2]
  simp only [zvec]
  congr 1
  omega

lemma zfun_ne_zero {s : ℕ} : ∀ c, zfun S s c ≠ 0 → Joined S s c := by
  intro c
  induction c with
  | zero => intro h; exact absurd rfl h
  | succ c ih =>
    intro h
    simp only [zfun] at h
    by_cases hs : c + 1 = s
    · exact ⟨hs.ge, fun e h1 h2 => by omega⟩
    · rw [ite_eq_right hs] at h
      by_cases he : Edge S c
      · rw [ite_eq_left he] at h
        obtain ⟨hsc, hj⟩ := ih (right_ne_zero_of_mul h)
        refine ⟨by omega, fun e h1 h2 => ?_⟩
        rcases Nat.lt_or_ge e c with h3 | h3
        · exact hj e h1 h3
        · obtain rfl : e = c := by omega
          exact he
      · rw [ite_eq_right he] at h
        exact absurd rfl h

lemma zfun_self {s : ℕ} (hs : 1 ≤ s) : zfun S s s = 1 := by
  obtain ⟨c, rfl⟩ : ∃ c, s = c + 1 := ⟨s - 1, by omega⟩
  simp [zfun]

lemma zfun_start {s s' : ℕ} (hs' : IsStart S s') (hne : s' ≠ s) : zfun S s s' = 0 := by
  obtain ⟨h1, -, he⟩ := hs'
  obtain ⟨c, rfl⟩ : ∃ c, s' = c + 1 := ⟨s' - 1, by omega⟩
  simp only [zfun]
  rw [ite_eq_right hne, ite_eq_right (by simpa using he)]

/-- **The vector of a non-anchored component is orthogonal to `S`** (the paper's `z`). -/
lemma orth_zvec (hS : ∀ v ∈ S, (∃ c, IsAnchorAt v c) ∨ ∃ c, IsLinkAt v c) {s : ℕ}
    (hs : s ∈ freeStarts S) : Orth S (zvec S s) := by
  classical
  obtain ⟨-, hstart, hna⟩ := Finset.mem_filter.mp hs
  intro v hvS
  rcases hS v hvS with ⟨c, hv⟩ | ⟨c, hv⟩
  · rw [dot_anchor hv, co_zvec s hv.1 hv.2.1]
    by_cases h : zfun S s c = 0
    · rw [h, mul_zero]
    · exact absurd ⟨c, zfun_ne_zero c h, Or.inl ⟨v, hvS, hv⟩⟩ hna
  · have he : Edge S c := ⟨v, hvS, hv⟩
    rw [dot_link hv, co_zvec s hv.1 (by have := hv.2.1; omega), co_zvec s (by omega) hv.2.1]
    have hne : c + 1 ≠ s := by
      rintro rfl
      exact hstart.2.2 (by simpa using he)
    have hz1 : zfun S s (c + 1) = ratio S c * zfun S s c := by
      simp only [zfun]
      rw [ite_eq_right hne, ite_eq_left he]
    rw [hz1]
    by_cases h : zfun S s c = 0
    · rw [h]; ring
    · have hj := zfun_ne_zero c h
      have hu := he.choose_spec
      have hpar : co v c * co he.choose (c + 1) = co v (c + 1) * co he.choose c := by
        by_contra hdet
        exact hna ⟨c, hj, Or.inr ⟨v, hvS, he.choose, hu.1, hv, hu.2,
          (linearIndependent_links_iff hv hu.2).mpr hdet⟩⟩
      have hβ := hu.2.2.2.2.1
      rw [ratio, dite_eq_left he]
      field_simp
      linear_combination zfun S s c * hpar

/-! ### The rank -/

/-- The annihilator of `S`, as the kernel of `z ↦ (v · z)_{v ∈ S}`. -/
noncomputable def orthMap (S : Finset (Fin N → ℝ)) : (Fin N → ℝ) →ₗ[ℝ] (S → ℝ) :=
  (Matrix.of fun (v : S) (i : Fin N) => v.1 i).mulVecLin

lemma mem_ker_orthMap {z : Fin N → ℝ} : z ∈ LinearMap.ker (orthMap S) ↔ Orth S z := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h v hv
    have := congrFun h ⟨v, hv⟩
    simpa [orthMap, mulVec, dotProduct] using this
  · intro h
    funext v
    simpa [orthMap, mulVec, dotProduct] using h v.1 v.2

/-- The values at the starts of the non-anchored components. -/
noncomputable def startVals (S : Finset (Fin N → ℝ)) : (Fin N → ℝ) →ₗ[ℝ] (freeStarts S → ℝ) where
  toFun z s := co z s.1
  map_add' x y := by funext s; simp
  map_smul' t x := by funext s; simp

/-- **The annihilator of `S` is `ℝ^{non-anchored components}`**, by the values at the starts. -/
theorem ker_equiv_bijective (hS : ∀ v ∈ S, (∃ c, IsAnchorAt v c) ∨ ∃ c, IsLinkAt v c) :
    Function.Bijective ((startVals S).comp (LinearMap.ker (orthMap S)).subtype) := by
  classical
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    apply Subtype.ext
    refine orth_eq_zero (mem_ker_orthMap.mp z.2) fun s hs => ?_
    have := congrFun hz ⟨s, hs⟩
    simpa [startVals] using this
  · intro f
    set z : Fin N → ℝ := ∑ s : freeStarts S, f s • zvec S s.1 with hzdef
    have hz : z ∈ LinearMap.ker (orthMap S) := by
      rw [hzdef]
      refine Submodule.sum_mem _ fun s _ => Submodule.smul_mem _ _ ?_
      exact mem_ker_orthMap.mpr (orth_zvec hS s.2)
    refine ⟨⟨z, hz⟩, ?_⟩
    funext s'
    have hs' := Finset.mem_filter.mp s'.2
    have hb := Finset.mem_Icc.mp hs'.1
    simp only [LinearMap.comp_apply, Submodule.subtype_apply, startVals, LinearMap.coe_mk,
      AddHom.coe_mk, hzdef, co_sum, co_smul]
    rw [Finset.sum_eq_single s']
    · rw [co_zvec _ hb.1 hb.2, zfun_self hb.1, mul_one]
    · intro s _ hne
      rw [co_zvec _ hb.1 hb.2, zfun_start hs'.2.1 (fun h => hne (Subtype.ext h.symm)), mul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h

/-- **`lem-path-rank`** (rank of path-supported vectors).  If every vector of the finite set `S` is
an anchor or a link, then `rank S = N − #{non-anchored components of G}`. -/
theorem lem_path_rank (hS : ∀ v ∈ S, (∃ c, IsAnchorAt v c) ∨ ∃ c, IsLinkAt v c) :
    Module.finrank ℝ (Submodule.span ℝ (S : Set (Fin N → ℝ))) = N - (freeStarts S).card := by
  have hset : Set.range (Matrix.of fun (v : S) (i : Fin N) => v.1 i).row =
      (S : Set (Fin N → ℝ)) := by
    ext x
    constructor
    · rintro ⟨v, rfl⟩; exact v.2
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  have hrank : Module.finrank ℝ (Submodule.span ℝ (S : Set (Fin N → ℝ))) =
      Module.finrank ℝ (LinearMap.range (orthMap S)) := by
    have h := Matrix.rank_eq_finrank_span_row (Matrix.of fun (v : S) (i : Fin N) => v.1 i)
    rw [Matrix.rank, hset] at h
    exact h.symm
  have hker : Module.finrank ℝ (LinearMap.ker (orthMap S)) = (freeStarts S).card := by
    rw [(LinearEquiv.ofBijective _ (ker_equiv_bijective hS)).finrank_eq,
      Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  have := LinearMap.finrank_range_add_finrank_ker (orthMap S)
  rw [Module.finrank_fin_fun] at this
  omega

end PathRank

/-! ## The directions of the second proof, and `lem-tight` -/

section Tight

/-- The dot product in manuscript coordinates. -/
lemma dot_eq_sum_co (u y : Fin N → ℝ) : u ⬝ᵥ y = ∑ c ∈ Finset.Icc 1 N, co u c * co y c := by
  set g : ℕ → ℝ := fun c => co u c * co y c with hg
  have h : ∀ i : Fin N, u i * y i = g ((i : ℕ) + 1) := fun i => by
    simp only [hg]; rw [← co_val, ← co_val]
  calc u ⬝ᵥ y = ∑ i : Fin N, g ((i : ℕ) + 1) := Finset.sum_congr rfl fun i _ => h i
    _ = ∑ i ∈ range N, g (i + 1) := Fin.sum_univ_eq_sum_range (fun i => g (i + 1)) N
    _ = ∑ c ∈ Finset.Icc 1 N, g c := by
      rw [← Nat.Ico_zero_eq_range, Finset.sum_Ico_add', zero_add,
        Finset.Ico_add_one_right_eq_Icc]

/-- The coordinate vector `e_c` (manuscript coordinate `c`). -/
def eVec (N c : ℕ) : Fin N → ℝ := mk N fun c' => if c' = c then 1 else 0

lemma co_eVec_of_ne {c c' : ℕ} (h : c' ≠ c) : co (eVec N c) c' = 0 := by
  by_cases hc : 1 ≤ c' ∧ c' ≤ N
  · rw [eVec, co_mk _ hc.1 hc.2, ite_eq_right h]
  · exact co_eq_zero _ (by omega)

lemma co_eVec_self {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ N) : co (eVec N c) c = 1 := by
  rw [eVec, co_mk _ h1 h2, ite_eq_left rfl]

lemma dot_eVec (c : ℕ) (y : Fin N → ℝ) : eVec N c ⬝ᵥ y = co y c := by
  rw [dot_eq_sum_co]
  by_cases hc : 1 ≤ c ∧ c ≤ N
  · rw [Finset.sum_eq_single c]
    · rw [co_eVec_self hc.1 hc.2, one_mul]
    · intro c' _ hne; rw [co_eVec_of_ne hne, zero_mul]
    · intro h; exact absurd (Finset.mem_Icc.mpr hc) h
  · rw [co_eq_zero y (by omega)]
    exact Finset.sum_eq_zero fun c' hc' => by
      rw [co_eVec_of_ne (by rw [Finset.mem_Icc] at hc'; omega), zero_mul]

/-- The link `u(p; c) = e_{c+1}/a_{ℓ+1} − e_c/a_ℓ`, `ℓ = c − e`, of the window with shift `e`. -/
noncomputable def linkU (a : ℕ → ℝ) (N e c : ℕ) : Fin N → ℝ :=
  mk N fun c' => if c' = c + 1 then 1 / a (c + 1 - e) else if c' = c then -(1 / a (c - e)) else 0

lemma co_linkU_of_ne (a : ℕ → ℝ) {e c c' : ℕ} (h1 : c' ≠ c) (h2 : c' ≠ c + 1) :
    co (linkU a N e c) c' = 0 := by
  by_cases hc : 1 ≤ c' ∧ c' ≤ N
  · rw [linkU, co_mk _ hc.1 hc.2, ite_eq_right h2, ite_eq_right h1]
  · exact co_eq_zero _ (by omega)

lemma co_linkU_left (a : ℕ → ℝ) {e c : ℕ} (hc : 1 ≤ c) (hcN : c ≤ N) :
    co (linkU a N e c) c = -(1 / a (c - e)) := by
  rw [linkU, co_mk _ hc hcN, ite_eq_right (by omega), ite_eq_left rfl]

lemma co_linkU_right (a : ℕ → ℝ) {e c : ℕ} (hcN : c + 1 ≤ N) :
    co (linkU a N e c) (c + 1) = 1 / a (c + 1 - e) := by
  rw [linkU, co_mk _ (by omega) hcN, ite_eq_left rfl]

lemma dot_linkU (a : ℕ → ℝ) {e c : ℕ} (hc : 1 ≤ c) (hcN : c + 1 ≤ N) (y : Fin N → ℝ) :
    linkU a N e c ⬝ᵥ y = co y (c + 1) / a (c + 1 - e) - co y c / a (c - e) := by
  rw [dot_eq_sum_co, Finset.sum_eq_add (c + 1) c (by omega)]
  · rw [co_linkU_right a hcN, co_linkU_left a hc (by omega)]
    ring
  · intro c' _ hne
    rw [co_linkU_of_ne a hne.2 hne.1, zero_mul]
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨by omega, hcN⟩) h
  · intro h; exact absurd (Finset.mem_Icc.mpr ⟨hc, by omega⟩) h

/-- `RA(a⃗; d⃗) = ∑_{p<r} shift^{d_p} ∠(a⃗)` in `ℝ^N`. -/
def RAsum (a : ℕ → ℝ) (N n : ℕ) (d : ℕ → ℕ) (r : ℕ) : Set (Fin N → ℝ) :=
  ∑ p ∈ range r, convexHull ℝ (vsetA a N (d p) n)

/-- `x(𝐣) = ∑_{p<r} shift^{d_p} v_{j_p}`. -/
noncomputable def xJ (a : ℕ → ℝ) (N : ℕ) (d : ℕ → ℕ) (r : ℕ) (J : ℕ → ℕ) : Fin N → ℝ :=
  ∑ p ∈ range r, ravA a N (d p) (J p)

variable {a : ℕ → ℝ} {n r : ℕ} {d : ℕ → ℕ}

/-- **Tightness is checked summand by summand** (the remark after `lem-certificate`): `u` is
tight at `x(𝐣)` iff every `j_q` maximises `k ↦ u · shift^{d_q} v_k`. -/
theorem tightAt_iff {J : ℕ → ℕ} (hJ : ∀ p < r, 1 ≤ J p ∧ J p ≤ n) (u : Fin N → ℝ) :
    TightAt (RAsum a N n d r) (xJ a N d r J) u ↔
      ∀ q < r, ∀ k, 1 ≤ k → k ≤ n → u ⬝ᵥ ravA a N (d q) k ≤ u ⬝ᵥ ravA a N (d q) (J q) := by
  classical
  constructor
  · intro h q hq k hk1 hkn
    set g : ℕ → Fin N → ℝ := fun p => ravA a N (d p) (J p) with hg
    have hqr : q ∈ range r := Finset.mem_range.mpr hq
    have hmem : ∑ p ∈ range r, Function.update g q (ravA a N (d q) k) p ∈ RAsum a N n d r := by
      rw [RAsum, Set.mem_finsetSum]
      refine ⟨Function.update g q (ravA a N (d q) k), fun {p} hp => ?_, rfl⟩
      rcases eq_or_ne p q with rfl | hpq
      · rw [Function.update_self]; exact subset_convexHull ℝ _ (ravA_mem_vsetA hk1 hkn)
      · rw [Function.update_of_ne hpq]
        have := hJ p (Finset.mem_range.mp hp)
        exact subset_convexHull ℝ _ (ravA_mem_vsetA this.1 this.2)
    have hsum : ∑ p ∈ range r, Function.update g q (ravA a N (d q) k) p =
        ravA a N (d q) k - g q + xJ a N d r J := by
      rw [Finset.sum_update_of_mem hqr, xJ, ← Finset.add_sum_erase _ g hqr,
        Finset.sdiff_singleton_eq_erase]
      abel
    have := h _ hmem
    rw [hsum, dotProduct_add, dotProduct_sub] at this
    simp only [hg] at this
    linarith
  · intro h y hy
    rw [RAsum, Set.mem_finsetSum] at hy
    obtain ⟨g, hg, rfl⟩ := hy
    rw [xJ, dotProduct_sum, dotProduct_sum]
    refine Finset.sum_le_sum fun q hq => ?_
    have hq' := Finset.mem_range.mp hq
    have hconv : Convex ℝ {z : Fin N → ℝ | u ⬝ᵥ z ≤ u ⬝ᵥ ravA a N (d q) (J q)} := by
      intro z1 hz1 z2 hz2 s t hs ht hst
      show u ⬝ᵥ (s • z1 + t • z2) ≤ _
      have h1 : u ⬝ᵥ z1 ≤ _ := hz1
      have h2 : u ⬝ᵥ z2 ≤ _ := hz2
      rw [dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
      have := mul_le_mul_of_nonneg_left h1 hs
      have := mul_le_mul_of_nonneg_left h2 ht
      have hX : s * u ⬝ᵥ ravA a N (d q) (J q) + t * u ⬝ᵥ ravA a N (d q) (J q) =
          u ⬝ᵥ ravA a N (d q) (J q) := by rw [← add_mul, hst, one_mul]
      linarith
    have hsub : vsetA a N (d q) n ⊆ {z | u ⬝ᵥ z ≤ u ⬝ᵥ ravA a N (d q) (J q)} := by
      rintro _ ⟨k, hk, rfl⟩
      exact h q hq' k hk.1 hk.2
    exact convexHull_min hsub hconv (hg hq)

lemma dN_of {N : ℕ} (hd : Incr d r) (hN : d (r - 1) + n ≤ N) {q : ℕ} (hq : q < r) :
    d q + n ≤ N := by
  have := hd.le (show q ≤ r - 1 by omega) (by omega)
  omega

/-- **`lem-tight`(1)**: the link `u(p; c)` (any `c` with `c, c+1` in window `p`) is tight at
`x(𝐣)` if `m_p ≠ c`, `m_q ≤ c − 1` for `q < p` and `m_q ≥ c + 1` for `q > p`. -/
theorem lem_tight_link (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hd : Incr d r)
    (hN : d (r - 1) + n ≤ N) {J : ℕ → ℕ} (hJ : ∀ q < r, 1 ≤ J q ∧ J q ≤ n) {p c : ℕ}
    (hp : p < r) (hc1 : d p + 1 ≤ c) (hc2 : c + 1 ≤ d p + n) (hm : d p + J p ≠ c)
    (hlt : ∀ q < p, d q + J q ≤ c - 1) (hgt : ∀ q, p < q → q < r → c + 1 ≤ d q + J q) :
    TightAt (RAsum a N n d r) (xJ a N d r J) (linkU a N (d p) c) := by
  have hcN : c + 1 ≤ N := by have := dN_of hd hN hp; omega
  rw [tightAt_iff hJ]
  intro q hq k hk1 hkn
  have hJq := hJ q hq
  set j := c - d p with hj
  have hj1 : 1 ≤ j := by omega
  have hjn : j + 1 ≤ n := by omega
  have e1 : c + 1 - d p = j + 1 := by omega
  rw [dot_linkU a (by omega) hcN, dot_linkU a (by omega) hcN, e1,
    value_table a (d q) k c j hk1 (by omega) hcN,
    value_table a (d q) (J q) c j hJq.1 (by omega) hcN]
  have hnp : ∀ e, 0 ≤ a e / a j := fun e => div_nonneg (hpos _).le (hpos _).le
  rcases lt_trichotomy q p with hqp | hqp | hqp
  · -- a window before `p`: the value at `j_q` is `0`, every value is `≤ 0`
    have hdq := hd.lt hqp hp
    have := hlt q hqp
    rw [ite_eq_left (show d q + J q < c by omega)]
    split_ifs with h1 h2
    · exact le_rfl
    · exact neg_nonpos.mpr (hnp _)
    · have hW : Aof a (d q) (c + 1) / a (j + 1) - Aof a (d q) c / a j = Vt a (c - d q) j := by
        unfold Aof Vt
        rw [ite_eq_left (show d q < c + 1 by omega), ite_eq_left (show d q < c by omega),
          show c + 1 - d q = c - d q + 1 by omega]
      rw [hW]
      exact Vt_nonpos hpos hlc hj1 (by omega) (by omega)
  · -- window `p` itself: the values are `0, −1, 0`
    subst hqp
    have hW : Aof a (d q) (c + 1) / a (j + 1) - Aof a (d q) c / a j = 0 := by
      unfold Aof
      rw [ite_eq_left (show d q < c + 1 by omega), ite_eq_left (show d q < c by omega), e1, ← hj,
        div_self (hpos _).ne', div_self (hpos _).ne', sub_self]
    have hR : (if d q + J q < c then (0 : ℝ) else if c = d q + J q then -(a (c - d q) / a j)
        else Aof a (d q) (c + 1) / a (j + 1) - Aof a (d q) c / a j) = 0 := by
      split_ifs with h1 h2
      · rfl
      · omega
      · exact hW
    rw [hR]
    split_ifs with h1 h2
    · exact le_rfl
    · exact neg_nonpos.mpr (hnp _)
    · exact hW.le
  · -- a window after `p`: the value at `j_q` is `V(ℓ, j) ≥ 0`, the largest
    have hdq := hd.lt hqp hq
    have := hgt q hqp hq
    rw [ite_eq_right (show ¬ d q + J q < c by omega), ite_eq_right (show ¬ c = d q + J q by omega)]
    have hW : 0 ≤ Aof a (d q) (c + 1) / a (j + 1) - Aof a (d q) c / a j := by
      unfold Aof
      by_cases h1 : d q < c
      · rw [ite_eq_left (show d q < c + 1 by omega), ite_eq_left h1,
          show c + 1 - d q = c - d q + 1 by omega]
        exact Vt_nonneg hpos hlc (ℓ := c - d q) (j := j) (by omega) (by omega) hjn
      · rw [ite_eq_right h1, zero_div, sub_zero]
        split_ifs
        · exact div_nonneg (hpos _).le (hpos _).le
        · rw [zero_div]
    split_ifs with h1 h2
    · exact hW
    · exact le_trans (neg_nonpos.mpr (hnp (c - d q))) hW
    · exact le_rfl

/-- **`lem-tight`(2)**: the lower anchor `u^C_p = −e_{d_p+1}` (`p ≥ 1`, the paper's `p ≥ 2`) is
tight at `x(𝐣)` iff `m_q ≤ d_p` for every `q < p`. -/
theorem lem_tight_C (hpos : ∀ s, 0 < a s) (hd : Incr d r) (hN : d (r - 1) + n ≤ N)
    {J : ℕ → ℕ} (hJ : ∀ q < r, 1 ≤ J q ∧ J q ≤ n) {p : ℕ} (hp0 : 0 < p) (hp : p < r) :
    TightAt (RAsum a N n d r) (xJ a N d r J) (-eVec N (d p + 1)) ↔
      ∀ q < p, d q + J q ≤ d p := by
  have hbN : d p + 1 ≤ N := by
    have := dN_of hd hN hp; obtain ⟨h1, h2⟩ := hJ p hp; omega
  have hval : ∀ q k, (-eVec N (d p + 1)) ⬝ᵥ ravA a N (d q) k =
      -(if d q < d p + 1 ∧ d p + 1 ≤ d q + k then a (d p + 1 - d q) else 0) := by
    intro q k
    rw [neg_dotProduct, dot_eVec, co_ravA_in a (d q) k (by omega) hbN]
  rw [tightAt_iff hJ]
  simp only [hval]
  constructor
  · intro h q hqp
    have hdq := hd.lt hqp hp
    have := h q (by omega) 1 le_rfl (le_trans (hJ p hp).1 (hJ p hp).2)
    rw [ite_eq_right (show ¬ (d q < d p + 1 ∧ d p + 1 ≤ d q + 1) by omega)] at this
    by_contra hlt
    rw [ite_eq_left (show d q < d p + 1 ∧ d p + 1 ≤ d q + J q by omega)] at this
    have := hpos (d p + 1 - d q)
    linarith
  · intro h q hq k hk1 _
    rcases lt_trichotomy q p with hqp | hqp | hqp
    · have := h q hqp
      rw [ite_eq_right (show ¬ (d q < d p + 1 ∧ d p + 1 ≤ d q + J q) by omega), neg_zero,
        neg_nonpos]
      split_ifs
      · exact (hpos _).le
      · exact le_rfl
    · subst hqp
      rw [ite_eq_left (show d q < d q + 1 ∧ d q + 1 ≤ d q + k by omega),
        ite_eq_left (show d q < d q + 1 ∧ d q + 1 ≤ d q + J q by have := (hJ q hq).1; omega)]
    · have hdq := hd.lt hqp hq
      rw [ite_eq_right (show ¬ (d q < d p + 1 ∧ d p + 1 ≤ d q + k) by omega),
        ite_eq_right (show ¬ (d q < d p + 1 ∧ d p + 1 ≤ d q + J q) by omega)]

/-- **`lem-tight`(3)**: the upper anchor `u^D_p = e_{d_{p−1}+n+1}` (`p ≥ 1`) is tight at `x(𝐣)` iff
`m_q ≥ d_{p−1} + n + 1` for every `q ≥ p`. -/
theorem lem_tight_D (hpos : ∀ s, 0 < a s) (hd : Incr d r) (hN : d (r - 1) + n ≤ N)
    {J : ℕ → ℕ} (hJ : ∀ q < r, 1 ≤ J q ∧ J q ≤ n) {p : ℕ} (hp0 : 0 < p) (hp : p < r) :
    TightAt (RAsum a N n d r) (xJ a N d r J) (eVec N (d (p - 1) + n + 1)) ↔
      ∀ q, p ≤ q → q < r → d (p - 1) + n + 1 ≤ d q + J q := by
  have hdp := hd (p - 1) (by omega)
  rw [show p - 1 + 1 = p by omega] at hdp
  have hcN : d (p - 1) + n + 1 ≤ N := by have := dN_of hd hN hp; omega
  have hval : ∀ q k, eVec N (d (p - 1) + n + 1) ⬝ᵥ ravA a N (d q) k =
      if d q < d (p - 1) + n + 1 ∧ d (p - 1) + n + 1 ≤ d q + k
        then a (d (p - 1) + n + 1 - d q) else 0 := by
    intro q k
    rw [dot_eVec, co_ravA_in a (d q) k (by omega) hcN]
  rw [tightAt_iff hJ]
  simp only [hval]
  constructor
  · intro h q hpq hq
    have hdq := hd.le hpq hq
    by_contra hlt
    have hn : 1 ≤ n := le_trans (hJ q hq).1 (hJ q hq).2
    have := h q hq n hn le_rfl
    rw [ite_eq_left (show d q < d (p - 1) + n + 1 ∧ d (p - 1) + n + 1 ≤ d q + n by omega),
      ite_eq_right (show ¬ (d q < d (p - 1) + n + 1 ∧ d (p - 1) + n + 1 ≤ d q + J q) by omega)]
      at this
    have := hpos (d (p - 1) + n + 1 - d q)
    linarith
  · intro h q hq k _ hkn
    rcases Nat.lt_or_ge q p with hqp | hqp
    · have := hd.le (show q ≤ p - 1 by omega) (by omega)
      have := (hJ q hq).2
      rw [ite_eq_right (show ¬ (d q < d (p - 1) + n + 1 ∧ d (p - 1) + n + 1 ≤ d q + k) by omega),
        ite_eq_right (show ¬ (d q < d (p - 1) + n + 1 ∧ d (p - 1) + n + 1 ≤ d q + J q) by omega)]
    · have := h q hqp hq
      by_cases h1 : d q < d (p - 1) + n + 1
      · rw [ite_eq_left (show d q < d (p - 1) + n + 1 ∧ d (p - 1) + n + 1 ≤ d q + J q by omega)]
        split_ifs
        · exact le_rfl
        · exact (hpos _).le
      · rw [ite_eq_right (show ¬ (d q < d (p - 1) + n + 1 ∧ d (p - 1) + n + 1 ≤ d q + k) by omega),
          ite_eq_right (show ¬ (d q < d (p - 1) + n + 1 ∧ d (p - 1) + n + 1 ≤ d q + J q) by omega)]

/-- **`lem-tight`(4)**: the last anchor `u^F = −e_N` is tight at `x(𝐣)` iff `m_r ≤ N − 1`, for
`N = d_r + n`.  **Needs `n ≥ 2`** (for `n = 1` — so `r = 1` under the gap bound — `R` is a point,
`u^F` is tight, and `m_1 = N`). -/
theorem lem_tight_F (hpos : ∀ s, 0 < a s) (hd : Incr d r) (hr : 1 ≤ r) (hn : 2 ≤ n)
    (hN : d (r - 1) + n = N) {J : ℕ → ℕ} (hJ : ∀ q < r, 1 ≤ J q ∧ J q ≤ n) :
    TightAt (RAsum a N n d r) (xJ a N d r J) (-eVec N N) ↔ d (r - 1) + J (r - 1) ≤ N - 1 := by
  have hval : ∀ q k, (-eVec N N) ⬝ᵥ ravA a N (d q) k =
      -(if d q < N ∧ N ≤ d q + k then a (N - d q) else 0) := by
    intro q k
    rw [neg_dotProduct, dot_eVec, co_ravA_in a (d q) k (by omega) le_rfl]
  rw [tightAt_iff hJ]
  simp only [hval]
  constructor
  · intro h
    have := h (r - 1) (by omega) 1 le_rfl (by omega)
    rw [ite_eq_right (show ¬ (d (r - 1) < N ∧ N ≤ d (r - 1) + 1) by omega)] at this
    by_contra hlt
    rw [ite_eq_left (show d (r - 1) < N ∧ N ≤ d (r - 1) + J (r - 1) by omega)] at this
    have := hpos (N - d (r - 1))
    linarith
  · intro h q hq k _ hkn
    rcases Nat.lt_or_ge q (r - 1) with hqr | hqr
    · have := hd.lt hqr (by omega)
      have := (hJ q hq).2
      rw [ite_eq_right (show ¬ (d q < N ∧ N ≤ d q + k) by omega),
        ite_eq_right (show ¬ (d q < N ∧ N ≤ d q + J q) by omega)]
    · obtain rfl : q = r - 1 := by omega
      rw [ite_eq_right (show ¬ (d (r - 1) < N ∧ N ≤ d (r - 1) + J (r - 1)) by omega), neg_zero,
        neg_nonpos]
      split_ifs
      · exact (hpos _).le
      · exact le_rfl

end Tight

/-! ## `lem-tight-edge` -/

section Edge

variable {n r : ℕ} {d J : ℕ → ℕ}

/-- The link `u(p; c)` is **certified** at `x(𝐣)`: the condition of `lem-tight`(1). -/
def CertLink (d J : ℕ → ℕ) (r p c : ℕ) : Prop :=
  d p + J p ≠ c ∧ (∀ q < p, d q + J q ≤ c - 1) ∧ ∀ q, p < q → q < r → c + 1 ≤ d q + J q

/-- The link `u(p; c)` belongs to the list `U`: `c, c + 1 ∈ W_p`, and `c ≥ d_p + 2` unless `p` is
the first window. -/
def InList (n : ℕ) (d : ℕ → ℕ) (p c : ℕ) : Prop :=
  d p + 1 ≤ c ∧ c + 1 ≤ d p + n ∧ (0 < p → d p + 2 ≤ c)

/-- The chosen points `m_q = d_q + j_q` are weakly increasing. -/
def MonoM (d J : ℕ → ℕ) (r : ℕ) : Prop := ∀ p, p + 1 < r → d p + J p ≤ d (p + 1) + J (p + 1)

lemma MonoM.le (h : MonoM d J r) {p q : ℕ} (hpq : p ≤ q) (hq : q < r) :
    d p + J p ≤ d q + J q := by
  induction q, hpq using Nat.le_induction with
  | base => exact le_rfl
  | succ q _ ih => exact le_trans (ih (by omega)) (h q hq)

/-- `k = #{q : m_q < c}`. -/
def cnt (d J : ℕ → ℕ) (r c : ℕ) : ℕ := ((range r).filter fun q => d q + J q < c).card

lemma cnt_le (c : ℕ) : cnt d J r c ≤ r :=
  le_trans (Finset.card_filter_le _ _) (by rw [Finset.card_range])

/-- With weakly increasing chosen points, `{q : m_q < c}` is the initial segment `[0, k)`. -/
lemma lt_cnt_iff (h : MonoM d J r) {c q : ℕ} (hq : q < r) : q < cnt d J r c ↔ d q + J q < c := by
  unfold cnt
  constructor
  · intro hlt
    by_contra hge
    push Not at hge
    have hsub : (range r).filter (fun q' => d q' + J q' < c) ⊆ range q := by
      intro q' hq'
      rw [Finset.mem_filter, Finset.mem_range] at hq'
      rw [Finset.mem_range]
      by_contra h'
      have := h.le (show q ≤ q' by omega) hq'.1
      omega
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega
  · intro hlt
    have hsub : range (q + 1) ⊆ (range r).filter (fun q' => d q' + J q' < c) := by
      intro q' hq'
      rw [Finset.mem_range] at hq'
      rw [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, lt_of_le_of_lt (h.le (show q' ≤ q by omega) hq) hlt⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_range] at this
    omega

/-- **`lem-tight-edge`(1)**: if `c = m_q` for some `q`, no link on the edge `{c, c+1}` is
certified. -/
theorem lem_tight_edge_one {c : ℕ} (hc1 : 1 ≤ c) (hc : ∃ q < r, d q + J q = c) :
    ∀ p < r, ¬ CertLink d J r p c := by
  obtain ⟨q, hq, hqc⟩ := hc
  rintro p hp ⟨h1, h2, h3⟩
  rcases lt_trichotomy q p with hqp | rfl | hqp
  · have := h2 q hqp; omega
  · exact h1 hqc
  · have := h3 q hqp hq; omega

/-- **`lem-tight-edge`(2)**: if `c` is no chosen point, then with `k = #{q : m_q < c}` the
certified links of the list on the edge `{c, c+1}` are exactly the `u(p; c)` with `p + 1 = k`
and `c ≤ d_p + n − 1`, or `p = k` and (`k = 0` or `c ≥ d_k + 2`).  (Windows are indexed from `0`,
so the paper's `u(k; c)`, `u(k+1; c)` are `p = k − 1`, `p = k` here.) -/
theorem lem_tight_edge_two (h0 : d 0 = 0) (hmono : MonoM d J r)
    (hJ : ∀ q < r, 1 ≤ J q ∧ J q ≤ n) {c : ℕ} (hc1 : 1 ≤ c) (hc : ∀ q < r, d q + J q ≠ c)
    {p : ℕ} (hp : p < r) :
    CertLink d J r p c ∧ InList n d p c ↔
      (p + 1 = cnt d J r c ∧ c + 1 ≤ d p + n) ∨ (p = cnt d J r c ∧ (p = 0 ∨ d p + 2 ≤ c)) := by
  have hK := fun q (hq : q < r) => lt_cnt_iff (c := c) hmono hq
  have hKr := cnt_le (d := d) (J := J) (r := r) c
  set K := cnt d J r c
  obtain ⟨hJ1, hJ2⟩ := hJ p hp
  have hcert : CertLink d J r p c ↔ p ≤ K ∧ K ≤ p + 1 := by
    constructor
    · rintro ⟨_, h2, h3⟩
      constructor
      · rcases Nat.eq_zero_or_pos p with h | h
        · omega
        · have := (hK (p - 1) (by omega)).mpr (by have := h2 (p - 1) (by omega); omega)
          omega
      · by_contra hlt
        have := (hK (p + 1) (by omega)).mp (by omega)
        have := h3 (p + 1) (by omega) (by omega)
        omega
    · rintro ⟨h1, h2⟩
      refine ⟨hc p hp, fun q hq => ?_, fun q hq hqr => ?_⟩
      · have := (hK q (by omega)).mp (by omega); omega
      · have h' := (hK q hqr).not.mp (by omega)
        have := hc q hqr
        omega
  rw [hcert]
  constructor
  · rintro ⟨⟨h1, h2⟩, hl1, hl2, hl3⟩
    rcases Nat.eq_or_lt_of_le h1 with h | h
    · right
      refine ⟨h, ?_⟩
      rcases Nat.eq_zero_or_pos p with h' | h'
      · exact Or.inl h'
      · exact Or.inr (hl3 h')
    · left; exact ⟨by omega, hl2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hm := (hK p hp).mp (by omega)
      exact ⟨⟨by omega, by omega⟩, by omega, h2, fun _ => by omega⟩
    · have hm := (hK p hp).not.mp (by omega)
      have := hc p hp
      refine ⟨⟨by omega, by omega⟩, ?_, by omega, ?_⟩
      · rcases h2 with h2 | h2
        · subst h2; rw [h0]; omega
        · omega
      · intro hp0
        rcases h2 with h2 | h2
        · omega
        · exact h2

end Edge

/-! ## `prop-certified-span` -/

section Span

variable {a : ℕ → ℝ} {n r : ℕ} {d J : ℕ → ℕ}

lemma co_neg (x : Fin N → ℝ) (c : ℕ) : co (-x) c = -co x c := by
  unfold co; split_ifs <;> simp

lemma isAnchorAt_eVec {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ N) : IsAnchorAt (eVec N c) c :=
  ⟨h1, h2, by rw [co_eVec_self h1 h2]; exact one_ne_zero, fun _ h => co_eVec_of_ne h⟩

lemma isAnchorAt_neg_eVec {c : ℕ} (h1 : 1 ≤ c) (h2 : c ≤ N) : IsAnchorAt (-eVec N c) c :=
  ⟨h1, h2, by rw [co_neg, co_eVec_self h1 h2]; exact neg_ne_zero.mpr one_ne_zero,
    fun _ h => by rw [co_neg, co_eVec_of_ne h, neg_zero]⟩

lemma isLinkAt_linkU (hpos : ∀ s, 0 < a s) {e c : ℕ} (he : e + 1 ≤ c) (hcN : c + 1 ≤ N) :
    IsLinkAt (linkU a N e c) c :=
  ⟨by omega, hcN, by
    rw [co_linkU_left a (by omega) (by omega)]
    exact neg_ne_zero.mpr (one_div_ne_zero (hpos _).ne'),
    by rw [co_linkU_right a hcN]; exact one_div_ne_zero (hpos _).ne',
    fun _ h1 h2 => co_linkU_of_ne a h1 h2⟩

lemma not_isLinkAt_of_single {v : Fin N → ℝ} {b c : ℕ} (hv : ∀ c', c' ≠ b → co v c' = 0) :
    ¬ IsLinkAt v c := by
  rintro ⟨-, -, h1, h2, -⟩
  by_cases hcb : c = b
  · exact h2 (hv _ (by omega))
  · exact h1 (hv _ hcb)

lemma eq_of_isLinkAt_linkU {e c c' : ℕ} (h : IsLinkAt (linkU a N e c') c) : c = c' := by
  obtain ⟨-, -, h1, h2, -⟩ := h
  by_contra hne
  by_cases hc : c = c' + 1
  · exact h2 (co_linkU_of_ne a (by omega) (by omega))
  · exact h1 (co_linkU_of_ne a hne hc)

open Classical in
/-- **The certified directions** at `x(𝐣)`: the certified links of the list `U`, and the certified
anchors `u^C_p`, `u^D_p` (`p ≥ 1`), `u^F` (the conditions of `lem-tight`(2)–(4)). -/
noncomputable def certSet (a : ℕ → ℝ) (N n : ℕ) (d J : ℕ → ℕ) (r : ℕ) : Finset (Fin N → ℝ) :=
  ((range r ×ˢ range N).filter fun pc => CertLink d J r pc.1 pc.2 ∧ InList n d pc.1 pc.2).image
      (fun pc => linkU a N (d pc.1) pc.2) ∪
    ((range r).filter fun p => 0 < p ∧ ∀ q < p, d q + J q ≤ d p).image
      (fun p => -eVec N (d p + 1)) ∪
    ((range r).filter fun p => 0 < p ∧ ∀ q, p ≤ q → q < r → d (p - 1) + n + 1 ≤ d q + J q).image
      (fun p => eVec N (d (p - 1) + n + 1)) ∪
    (if d (r - 1) + J (r - 1) ≤ N - 1 then {-eVec N N} else ∅)

lemma mem_certSet_link {p c : ℕ} (hp : p < r) (hcN : c < N) (hc : CertLink d J r p c)
    (hl : InList n d p c) : linkU a N (d p) c ∈ certSet a N n d J r := by
  classical
  unfold certSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ ?_))
  exact Finset.mem_image.mpr ⟨(p, c), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr hp, Finset.mem_range.mpr hcN⟩, hc, hl⟩, rfl⟩

lemma mem_certSet_C {p : ℕ} (hp0 : 0 < p) (hp : p < r) (h : ∀ q < p, d q + J q ≤ d p) :
    -eVec N (d p + 1) ∈ certSet a N n d J r := by
  classical
  unfold certSet
  refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
  exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, hp0, h⟩, rfl⟩

lemma mem_certSet_D {p : ℕ} (hp0 : 0 < p) (hp : p < r)
    (h : ∀ q, p ≤ q → q < r → d (p - 1) + n + 1 ≤ d q + J q) :
    eVec N (d (p - 1) + n + 1) ∈ certSet a N n d J r := by
  classical
  unfold certSet
  refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
  exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp, hp0, h⟩, rfl⟩

lemma mem_certSet_F (h : d (r - 1) + J (r - 1) ≤ N - 1) :
    -eVec N N ∈ certSet a N n d J r := by
  classical
  unfold certSet
  refine Finset.mem_union_right _ ?_
  rw [ite_eq_left h]
  exact Finset.mem_singleton_self _

/-- A certified direction is a certified link of the list, or a signed coordinate vector `±e_b`
with `b ∈ [1, N]`. -/
lemma mem_certSet_cases (hd : Incr d r) (hN : d (r - 1) + n = N) (hn : 1 ≤ n) {v : Fin N → ℝ}
    (hv : v ∈ certSet a N n d J r) :
    (∃ p c, p < r ∧ c < N ∧ CertLink d J r p c ∧ InList n d p c ∧ v = linkU a N (d p) c) ∨
      ∃ b, 1 ≤ b ∧ b ≤ N ∧ (v = eVec N b ∨ v = -eVec N b) := by
  classical
  unfold certSet at hv
  rcases Finset.mem_union.mp hv with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨⟨p, c⟩, hpc, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨hpc, hcert, hl⟩ := Finset.mem_filter.mp hpc
        obtain ⟨hp, hc⟩ := Finset.mem_product.mp hpc
        exact Or.inl ⟨p, c, Finset.mem_range.mp hp, Finset.mem_range.mp hc, hcert, hl, rfl⟩
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        have hp' := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
        exact Or.inr ⟨d p + 1, by omega, by have := dN_of hd hN.le hp'; omega, Or.inr rfl⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hp, hp0, -⟩ := Finset.mem_filter.mp hp
      have hp' := Finset.mem_range.mp hp
      have := hd (p - 1) (by omega)
      rw [show p - 1 + 1 = p by omega] at this
      exact Or.inr ⟨d (p - 1) + n + 1, by omega, by have := dN_of hd hN.le hp'; omega, Or.inl rfl⟩
  · split_ifs at h with hF
    · rw [Finset.mem_singleton] at h
      subst h
      exact Or.inr ⟨N, by omega, le_rfl, Or.inr rfl⟩
    · simp at h

/-- If the ratio `a_{c−d_P}/a_{c−d_Q}` is not constant on `[m_P+1, m_Q]` (the step is not locked,
while `m_P < m_Q`, `d_Q < m_P`, `m_Q ≤ d_P + n`), two consecutive values differ. -/
lemma exists_step_of_not_locked (hpos : ∀ s, 0 < a s) {dP dQ mP mQ : ℕ} (h1 : mP < mQ)
    (h2 : dQ < mP) (h3 : mQ ≤ dP + n) (hnl : ¬ Pairwise.Locked a n dP dQ mP mQ) :
    ∃ c, mP + 1 ≤ c ∧ c + 1 ≤ mQ ∧
      a (c - dP) * a (c + 1 - dQ) ≠ a (c + 1 - dP) * a (c - dQ) := by
  by_contra hcon
  push Not at hcon
  apply hnl
  refine ⟨h1, h2, h3, ?_⟩
  have key : ∀ t c, c + t = mQ → mP < c →
      a (c - dP) * a (mQ - dQ) = a (mQ - dP) * a (c - dQ) := by
    intro t
    induction t with
    | zero => intro c hc _; rw [show c = mQ by omega]
    | succ t ih =>
      intro c hc hpc
      have e1 := ih (c + 1) (by omega) (by omega)
      have e2 := hcon c (by omega) (by omega)
      apply mul_right_cancel₀ (hpos (c + 1 - dQ)).ne'
      linear_combination a (mQ - dQ) * e2 + a (c - dQ) * e1
  intro c hc
  rw [Finset.mem_Ioc] at hc
  exact key (mQ - c) c (by omega) hc.1

/-- **`prop-certified-span`.**  Let `a⃗` be positive, the shifts `0 = d_0 < ⋯ < d_{r−1}` with every
gap at most `n − 1`, `N = d_{r−1} + n`, `𝐣 ∈ [n]^r` with weakly increasing chosen points, and suppose
that no consecutive step is locked (`Pairwise.Locked`: whenever `m_p < m_{p+1}` both lie in the
overlap `[d_{p+1}+1, d_p+n]`, the ratio `a_{c−d_p}/a_{c−d_{p+1}}` is not constant on
`[m_p+1, m_{p+1}]`).  Then the directions certified at `x(𝐣)`, together with `e_1`, span
`ℝ^N`. -/
theorem prop_certified_span (hpos : ∀ s, 0 < a s) (h0 : d 0 = 0) (hr : 1 ≤ r) (hd : Incr d r)
    (hg : Gaps n d r) (hN : d (r - 1) + n = N) (hJ : ∀ q < r, 1 ≤ J q ∧ J q ≤ n)
    (hmono : MonoM d J r)
    (hlock : ∀ p, p + 1 < r →
      ¬ Pairwise.Locked a n (d p) (d (p + 1)) (d p + J p) (d (p + 1) + J (p + 1))) :
    Submodule.span ℝ (insert (eVec N 1) (certSet a N n d J r) : Set (Fin N → ℝ)) = ⊤ := by
  classical
  set S := insert (eVec N 1) (certSet a N n d J r) with hSdef
  have hn1 : 1 ≤ n := le_trans (hJ 0 (by omega)).1 (hJ 0 (by omega)).2
  have hdN : ∀ q < r, d q + n ≤ N := fun q hq => dN_of hd hN.le hq
  have hN1 : 1 ≤ N := by have := hdN 0 (by omega); omega
  have hwin : ∀ q < r, d q + 1 ≤ d q + J q ∧ d q + J q ≤ d q + n := fun q hq => by
    obtain ⟨h1, h2⟩ := hJ q hq; omega
  -- every vector of `S` is an anchor or a link
  have hS : ∀ v ∈ S, (∃ c, IsAnchorAt v c) ∨ ∃ c, IsLinkAt v c := by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact Or.inl ⟨1, isAnchorAt_eVec le_rfl hN1⟩
    · rcases mem_certSet_cases hd hN hn1 hv with ⟨p, c, hp, -, -, hl, rfl⟩ |
        ⟨b, hb1, hb2, rfl | rfl⟩
      · exact Or.inr ⟨c, isLinkAt_linkU hpos hl.1 (by have := hdN p hp; have := hl.2.1; omega)⟩
      · exact Or.inl ⟨b, isAnchorAt_eVec hb1 hb2⟩
      · exact Or.inl ⟨b, isAnchorAt_neg_eVec hb1 hb2⟩
  -- the edges of `G` are the edges carrying a certified link of the list
  have hedge : ∀ c, Edge S c ↔ ∃ p < r, CertLink d J r p c ∧ InList n d p c := by
    intro c
    constructor
    · rintro ⟨v, hv, hlink⟩
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact absurd hlink (not_isLinkAt_of_single (b := 1) fun _ h => co_eVec_of_ne h)
      · rcases mem_certSet_cases hd hN hn1 hv with ⟨p, c', hp, -, hcert, hl, rfl⟩ |
          ⟨b, -, -, rfl | rfl⟩
        · obtain rfl := eq_of_isLinkAt_linkU hlink
          exact ⟨p, hp, hcert, hl⟩
        · exact absurd hlink (not_isLinkAt_of_single (b := b) fun _ h => co_eVec_of_ne h)
        · exact absurd hlink (not_isLinkAt_of_single (b := b) fun _ h => by
            rw [co_neg, co_eVec_of_ne h, neg_zero])
    · rintro ⟨p, hp, hcert, hl⟩
      have := hdN p hp
      exact ⟨_, Finset.mem_insert_of_mem (mem_certSet_link hp (by have := hl.2.1; omega) hcert hl),
        isLinkAt_linkU hpos hl.1 (by have := hl.2.1; omega)⟩
  have hjoin : ∀ s t, s ≤ t →
      (∀ c, s ≤ c → c < t → ∃ p < r, CertLink d J r p c ∧ InList n d p c) → Joined S s t :=
    fun s t hst h => ⟨hst, fun e h1 h2 => (hedge e).mpr (h e h1 h2)⟩
  have hanchor : ∀ v ∈ S, ∀ c, IsAnchorAt v c → ∀ s, Joined S s c → Anchored S s :=
    fun v hv c hc s hj => ⟨c, hj, Or.inl ⟨v, hv, hc⟩⟩
  -- every component of `G` is anchored
  have hanch : ∀ s, IsStart S s → Anchored S s := by
    intro s hs
    obtain ⟨hs1, hsN, hse⟩ := hs
    rw [hedge] at hse
    push Not at hse
    rcases Nat.lt_or_ge s 2 with hs2 | hs2
    · -- the component of the coordinate `1`, anchored by `e_1`
      obtain rfl : s = 1 := by omega
      exact hanchor _ (Finset.mem_insert_self _ _) 1 (isAnchorAt_eVec le_rfl hN1) 1
        ⟨le_rfl, fun e h1 h2 => by omega⟩
    set K := cnt d J r s with hKdef
    have hK : ∀ q < r, (q < K ↔ d q + J q < s) := fun q hq => lt_cnt_iff hmono hq
    have hKr : K ≤ r := cnt_le s
    have hge : ∀ q, K ≤ q → q < r → s ≤ d q + J q := fun q h1 h2 => by
      by_contra h
      push Not at h
      have := (hK q h2).mpr h
      omega
    rcases Nat.eq_zero_or_pos K with hK0 | hKpos
    · -- the head: the edge `s − 1` carries the certified link `u(0; s−1)`, impossible
      exfalso
      have hm0 := hge 0 (by omega) (by omega)
      have hw0 := hwin 0 (by omega)
      refine hse 0 (by omega) ⟨by omega, fun q hq => absurd hq (Nat.not_lt_zero q),
        fun q hq hqr => ?_⟩ ⟨by rw [h0]; omega, by rw [h0] at hw0 ⊢; omega, fun h => by omega⟩
      have := hmono.le (show 0 ≤ q by omega) hqr
      omega
    set P := K - 1 with hPdef
    have hPr : P < r := by omega
    have hPK : P + 1 = K := by omega
    have hmP : d P + J P < s := (hK P hPr).mp (by omega)
    have hle : ∀ q ≤ P, d q + J q ≤ d P + J P := fun q hq => hmono.le hq hPr
    have hwP := hwin P hPr
    rcases Nat.lt_or_ge (d P + J P) (s - 1) with hB | hA
    · -- `s − 1` is no chosen point: `u(P; s−1)` is certified, so it is not in the list
      have hcertP : CertLink d J r P (s - 1) :=
        ⟨by omega, fun q hq => by have := hle q hq.le; omega, fun q hq hqr => by
          have := hge q (by omega) hqr; omega⟩
      have hsA : d P + n + 1 ≤ s := by
        by_contra h
        exact hse P hPr hcertP ⟨by omega, by omega, fun _ => by omega⟩
      rcases Nat.eq_or_lt_of_le hKr with hKr' | hKr'
      · exfalso
        rw [show P = r - 1 by omega] at hsA
        omega
      · -- `u(K; s−1)` is certified too, so not in the list: `s = d_P + n + 1 = d_K + 2`
        have hmK := hge K le_rfl hKr'
        have hcertK : CertLink d J r K (s - 1) :=
          ⟨by omega, fun q hq => by have := hle q (by omega); omega, fun q hq hqr => by
            have := hmono.le (show K ≤ q by omega) hqr; omega⟩
        have hwK := hwin K hKr'
        have hgap := hg P (by omega)
        rw [hPK] at hgap
        have hsB : s - 1 ≤ d K + 1 := by
          by_contra h
          exact hse K hKr' hcertK ⟨by omega, by omega, fun _ => by omega⟩
        have hsD : d (K - 1) + n + 1 = s := by rw [← hPdef]; omega
        refine hanchor (eVec N s) ?_ s (isAnchorAt_eVec (by omega) hsN) s
          ⟨le_rfl, fun e h1 h2 => by omega⟩
        rw [← hsD]
        exact Finset.mem_insert_of_mem (mem_certSet_D (by omega) hKr' fun q hq hqr => by
          rw [hsD]; exact hge q hq hqr)
    · -- `m_P = s − 1`: the block `I` starts at `s`
      have hmPs : d P + J P = s - 1 := by omega
      rcases Nat.eq_or_lt_of_le hKr with hKr' | hKr'
      · -- the tail: links `u(P; c)` up to `N`, and the last anchor `u^F`
        have hP : P = r - 1 := by omega
        refine hanchor (-eVec N N) ?_ N (isAnchorAt_neg_eVec hN1 le_rfl) s
          (hjoin s N hsN fun c hc1 hc2 => ⟨P, hPr, ⟨by omega, fun q hq => by
            have := hle q hq.le; omega, fun q hq hqr => by omega⟩, by omega, by
              rw [hP]; omega, fun _ => by omega⟩)
        exact Finset.mem_insert_of_mem (mem_certSet_F (by rw [← hP]; omega))
      · -- a middle block between the junction `(P, K)`
        have hmK := hge K le_rfl hKr'
        have hwK := hwin K hKr'
        have hgap := hg P (by omega)
        rw [hPK] at hgap
        have hdPK : d P < d K := by have := hd P (by omega); rwa [hPK] at this
        have hlinkP : ∀ c, s ≤ c → c + 1 ≤ d K + J K → c + 1 ≤ d P + n →
            CertLink d J r P c ∧ InList n d P c := fun c h1 h2 h3 =>
          ⟨⟨by omega, fun q hq => by have := hle q hq.le; omega, fun q hq hqr => by
            have := hmono.le (show K ≤ q by omega) hqr; omega⟩, by omega, h3, fun _ => by omega⟩
        by_cases hBs : s ≤ d K + 1
        · -- the lower anchor `u^C_K = −e_{d_K+1}` is certified
          refine hanchor (-eVec N (d K + 1)) ?_ (d K + 1)
            (isAnchorAt_neg_eVec (by omega) (by have := hdN K hKr'; omega)) s
            (hjoin s (d K + 1) hBs fun c h1 h2 =>
              ⟨P, hPr, hlinkP c h1 (by omega) (by omega)⟩)
          exact Finset.mem_insert_of_mem (mem_certSet_C (by omega) hKr' fun q hq => by
            have := hle q (by omega); omega)
        · by_cases hAm : d P + n + 1 ≤ d K + J K
          · -- the upper anchor `u^D_K = e_{d_P+n+1}` is certified
            have hKP : K - 1 = P := by omega
            refine hanchor (eVec N (d P + n + 1)) ?_ (d P + n + 1)
              (isAnchorAt_eVec (by omega) (by have := hdN K hKr'; omega)) s
              (hjoin s (d P + n + 1) (by omega) fun c h1 h2 => ?_)
            · have := mem_certSet_D (a := a) (N := N) (n := n) (d := d) (J := J) (p := K)
                (by omega) hKr' fun q hq hqr => by
                  rw [hKP]; have := hmono.le hq hqr; omega
              rw [hKP] at this
              exact Finset.mem_insert_of_mem this
            · rcases Nat.lt_or_ge (c + 1) (d P + n + 1) with hc | hc
              · exact ⟨P, hPr, hlinkP c h1 (by omega) (by omega)⟩
              · -- the edge `c = d_P + n` carries `u(K; c)`
                exact ⟨K, hKr', ⟨by omega, fun q hq => by have := hle q (by omega); omega,
                  fun q hq hqr => by have := hmono.le (show K ≤ q by omega) hqr; omega⟩,
                  by omega, by omega, fun _ => by omega⟩
          · -- both chosen points in the overlap: two independent links on one edge
            have hnl := hlock P (by omega)
            rw [hPK] at hnl
            obtain ⟨c, hc1, hc2, hne⟩ := exists_step_of_not_locked hpos (n := n)
              (show d P + J P < d K + J K by omega) (show d K < d P + J P by omega)
              (show d K + J K ≤ d P + n by omega) hnl
            have hcP := hlinkP c (by omega) (by omega) (by omega)
            have hcK : CertLink d J r K c ∧ InList n d K c :=
              ⟨⟨by omega, fun q hq => by have := hle q (by omega); omega, fun q hq hqr => by
                have := hmono.le (show K ≤ q by omega) hqr; omega⟩, by omega, by omega,
                fun _ => by omega⟩
            have hcN : c + 1 ≤ N := by have := hdN K hKr'; omega
            have hvP := isLinkAt_linkU (a := a) hpos (e := d P) (by omega) hcN
            have hvK := isLinkAt_linkU (a := a) hpos (e := d K) (by omega) hcN
            refine ⟨c, hjoin s c (by omega) fun c' h1 h2 =>
                ⟨P, hPr, hlinkP c' h1 (by omega) (by omega)⟩,
              Or.inr ⟨linkU a N (d P) c, Finset.mem_insert_of_mem
                (mem_certSet_link hPr (by omega) hcP.1 hcP.2), linkU a N (d K) c,
                Finset.mem_insert_of_mem (mem_certSet_link hKr' (by omega) hcK.1 hcK.2),
                hvP, hvK, (linearIndependent_links_iff hvP hvK).mpr ?_⟩⟩
            rw [co_linkU_left a (by omega) (by omega), co_linkU_right a hcN,
              co_linkU_left a (by omega) (by omega), co_linkU_right a hcN]
            intro h
            apply hne
            have hA := (hpos (c - d P)).ne'
            have hB := (hpos (c + 1 - d P)).ne'
            have hC := (hpos (c - d K)).ne'
            have hD := (hpos (c + 1 - d K)).ne'
            field_simp at h
            linarith
  have hfree : freeStarts S = ∅ := by
    rw [freeStarts, Finset.filter_eq_empty_iff]
    rintro s - ⟨hs, hna⟩
    exact hna (hanch s hs)
  have hrank := lem_path_rank hS
  rw [hfree, Finset.card_empty, Nat.sub_zero] at hrank
  have hcoe : (S : Set (Fin N → ℝ)) = insert (eVec N 1) (certSet a N n d J r : Set _) := by
    rw [hSdef, Finset.coe_insert]
  rw [hcoe] at hrank
  exact Submodule.eq_top_of_finrank_eq (by rw [hrank, Module.finrank_fin_fun])

end Span

/-! ## The second proof of sufficiency in `thm-vdesc` (reduced case) -/

section Sufficiency

variable {a : ℕ → ℝ} {n r : ℕ} {d J : ℕ → ℕ}

/-- **Certified directions are tight** (`lem-tight`, all four parts). -/
lemma certSet_tight (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hr : 1 ≤ r) (hd : Incr d r)
    (hN : d (r - 1) + n = N) (hJ : ∀ q < r, 1 ≤ J q ∧ J q ≤ n) {v : Fin N → ℝ}
    (hv : v ∈ certSet a N n d J r) : TightAt (RAsum a N n d r) (xJ a N d r J) v := by
  classical
  unfold certSet at hv
  rcases Finset.mem_union.mp hv with h | h
  · rcases Finset.mem_union.mp h with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨⟨p, c⟩, hpc, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨hpc, ⟨hm, hlt, hgt⟩, hl1, hl2, -⟩ := Finset.mem_filter.mp hpc
        exact lem_tight_link hpos hlc hd hN.le hJ
          (Finset.mem_range.mp (Finset.mem_product.mp hpc).1)
          hl1 hl2 hm hlt hgt
      · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
        obtain ⟨hp, hp0, hcond⟩ := Finset.mem_filter.mp hp
        exact (lem_tight_C hpos hd hN.le hJ hp0 (Finset.mem_range.mp hp)).mpr hcond
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      obtain ⟨hp, hp0, hcond⟩ := Finset.mem_filter.mp hp
      exact (lem_tight_D hpos hd hN.le hJ hp0 (Finset.mem_range.mp hp)).mpr hcond
  · split_ifs at h with hF
    · rw [Finset.mem_singleton] at h
      subst h
      have := hJ (r - 1) (by omega)
      exact (lem_tight_F hpos hd hr (by omega) hN hJ).mpr hF
    · simp at h

/-- **The second proof of sufficiency in `thm-vdesc`**, in the case it reduces to (distinct shifts
`0 = d_0 < ⋯ < d_{r−1}`, every gap at most `n − 1`, `N = d_{r−1} + n`): if the chosen points are
weakly increasing (condition (2)) and no consecutive step is locked (condition (3)), then the sum of
the certified directions is uniquely maximised on `RA(a⃗; d⃗)` at `x(𝐣)` and on every summand at
its chosen vertex, and `x(𝐣)` is a vertex — by `lem-certificate`, `lem-tight` and
`prop-certified-span`, with `U` the certified directions.  The reduction of ties and of gaps
`≥ n` is not formalised here (the first proof, `vertex_iff_CF`, needs none). -/
theorem second_proof_vertex (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (h0 : d 0 = 0)
    (hr : 1 ≤ r) (hd : Incr d r) (hg : Gaps n d r) (hN : d (r - 1) + n = N)
    (hJ : ∀ q < r, 1 ≤ J q ∧ J q ≤ n) (hmono : MonoM d J r)
    (hlock : ∀ p, p + 1 < r →
      ¬ Pairwise.Locked a n (d p) (d (p + 1)) (d p + J p) (d (p + 1) + J (p + 1))) :
    (∀ y ∈ RAsum a N n d r, y ≠ xJ a N d r J →
        certFun (RAsum a N n d r) (xJ a N d r J) (certSet a N n d J r) ⬝ᵥ y <
          certFun (RAsum a N n d r) (xJ a N d r J) (certSet a N n d J r) ⬝ᵥ xJ a N d r J) ∧
      (∀ p ∈ range r, ∀ z ∈ convexHull ℝ (vsetA a N (d p) n), z ≠ ravA a N (d p) (J p) →
        certFun (RAsum a N n d r) (xJ a N d r J) (certSet a N n d J r) ⬝ᵥ z <
          certFun (RAsum a N n d r) (xJ a N d r J) (certSet a N n d J r) ⬝ᵥ
            ravA a N (d p) (J p)) ∧
      xJ a N d r J ∈ Set.extremePoints ℝ (RAsum a N n d r) := by
  classical
  have hdN : ∀ q < r, d q + n ≤ N := fun q hq => dN_of hd hN.le hq
  have hN1 : 1 ≤ N := by have := hdN 0 (by omega); have := hJ 0 (by omega); omega
  -- `x_1` is constant on `R`: both `e_1` and `−e_1` are tight
  have hval1 : ∀ q < r, ∀ k, 1 ≤ k → co (ravA a N (d q) k) 1 = if q = 0 then a 1 else 0 := by
    intro q hq k hk
    rw [co_ravA_in a (d q) k le_rfl hN1]
    rcases Nat.eq_zero_or_pos q with rfl | hq0
    · rw [h0, ite_eq_left ⟨by omega, by omega⟩, ite_eq_left rfl]
    · have := hd.lt hq0 hq
      rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have ht1 : TightAt (RAsum a N n d r) (xJ a N d r J) (eVec N 1) := by
    rw [tightAt_iff hJ]
    intro q hq k hk _
    rw [dot_eVec, dot_eVec, hval1 q hq k hk, hval1 q hq (J q) (hJ q hq).1]
  have ht1' : TightAt (RAsum a N n d r) (xJ a N d r J) (-eVec N 1) := by
    rw [tightAt_iff hJ]
    intro q hq k hk _
    rw [neg_dotProduct, neg_dotProduct, dot_eVec, dot_eVec, hval1 q hq k hk,
      hval1 q hq (J q) (hJ q hq).1]
  have he : ∀ y ∈ RAsum a N n d r, eVec N 1 ⬝ᵥ y = eVec N 1 ⬝ᵥ xJ a N d r J := by
    intro y hy
    have h1 := ht1 y hy
    have h2 := ht1' y hy
    rw [neg_dotProduct, neg_dotProduct] at h2
    linarith
  have hspan := prop_certified_span hpos h0 hr hd hg hN hJ hmono hlock
  have hfilt : (certSet a N n d J r).filter (TightAt (∑ p ∈ range r,
      convexHull ℝ (vsetA a N (d p) n)) (∑ p ∈ range r, ravA a N (d p) (J p))) =
      certSet a N n d J r :=
    Finset.filter_true_of_mem fun v hv => certSet_tight hpos hlc hr hd hN hJ hv
  exact lem_certificate (range r) (fun p => convexHull ℝ (vsetA a N (d p) n))
    (fun p => ravA a N (d p) (J p))
    (fun p hp => subset_convexHull ℝ _ (ravA_mem_vsetA (hJ p (Finset.mem_range.mp hp)).1
      (hJ p (Finset.mem_range.mp hp)).2))
    (eVec N 1) he (certSet a N n d J r) (by rw [hfilt]; exact hspan)

end Sufficiency

end SecondProof
end ExteriorConvex
