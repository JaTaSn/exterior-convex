/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The Alexander core: `β` is Part II's Alexander duality on `S_n°`

Formalisation of `thm-alexander-core` (all three parts) and of the last clause of `lem-beta`
("on the face `Φ = {μ_{n−1} = 0}`, `β` is `f_k ↦ C(n,k) − f_{n−k}`, the Alexander duality map")
from `article/exterior-convex_article3_draft_4.org`; roadmap item 6 of
`working-notes/lean-roadmap-article3-2026-10-21.org`.

Conventions are those of `Counting/Duality.lean` (`SnF n` = `S_n`, ℕ-valued `f`-vectors
`Fin (n + 1) → ℕ` of simplicial complexes on `[n]`, entry `j` = number of faces of size `j`;
`Dvec` = `D_n`, `(D s⃗)_j = C(n,j) − s_{n−j}`) and of `Symmetry/Beta.lean` (`beta`, `muOf`,
`penult n` = coordinate `n − 1`). `castR` casts an `f`-vector into `ℝ^{n+1}`.

* `coreF n` = `S_n° = {s⃗ ∈ S_n : s_{n−1} = 0}`, `topF n` = `S_n^top = S_n ∖ S_n°`.
* **Part (1).** `last_eq_zero_of_mem_coreF` (`s_{n−1} = 0 ⟹ s_n = 0`, from LYM),
  `Dvec_mem_coreF`, `Dvec_bijOn_coreF`: **`D_n` is an involution of `S_n°`** (`n ≥ 3`);
  `sum_coreF_add_rev` (ℕ form) and `coreF_centroid`: the centroid of `S_n°` has
  `μ_k + μ_{n−k} = 1` — proved for every `0 ≤ k ≤ n`, the paper states `1 ≤ k ≤ n − 1`;
  `muOf_penult_last_of_mem_coreF`: `μ_{n−1} = μ_n = 0` on the core (pointwise).
  `coreF_nonempty` (the 1-skeleton).
* **`lem-beta`, last clause.** `beta_eq_DvecR`: for `x ∈ Koz(n)` with `x_{n−1} = 0`,
  `β(x) = (C(n,k) − x_{n−k})_k` in **every** coordinate (on `{0,1,n−1,n}`, where `β` is the
  identity, this uses `f₀ = 1`, `f₁ = n`, `f_n = 0`). `beta_castR_of_mem_coreF`: on `S_n°`,
  `β(s⃗) = D_n(s⃗)` — so `β` *is* `D_n` on the core.
* **Part (2).** `card_topF`: `|S_n^top| = ∑_{m=0}^{n−1} |S_m|` (`n ≥ 3`), with
  `card_SnF_zero : |S_0| = 1`. As in the paper's proof: `lk` (the link of a vertex),
  `fEntry_succ_eq` (`f_{k+1}(Δ) = C(n−1,k+1) + f_k(lk_Δ v)` when `[n] ∖ {v} ∈ Δ`),
  `liftVec` (the parametrisation `f_k = C(n−1,k) + g_{k−1}`), `liftVec_mem_topF` (cone a
  complex on `m < n` vertices and add the full simplex on `[n] ∖ {v}`),
  `exists_liftVec_of_mem_topF` (relabel the link onto its vertex set, `orderEmbOfFin`),
  `topF_eq_biUnion`; the pieces are disjoint because `f₂ = C(n−1,2) + m` (`liftVec_two`).
  No relabelling of `Δ` itself is needed: the vertex `v` missing from a facet of size `n − 1`
  is used directly.
* **Part (3).** `avgS n f` = the uniform average over `S_n`, `epsN n = |S_n^top|/|S_n|`.
  `centroid_reflect_bounds`: `0 ≤ μ_k + μ_{n−k} − 1 ≤ ε_n` (`1 ≤ k ≤ n−1`);
  `centroid_top_bounds`: `0 ≤ μ_n ≤ μ_{n−1} ≤ ε_n`; `centroid_index_bounds`: the mean
  barycentric index lies in `[(n−1)/2, (n−1)/2 + (n+1)ε_n/2]`. Here `μ_k` of the centroid is
  the average of `μ_k` (`μ_k` is linear) and the **barycentric index** is
  `baryIndex n x = ∑_{k=1}^n μ_k(x)` (`= ∑_j j·λ_j`, `λ_j = μ_j − μ_{j+1}`, so `F̃_j` has
  index `j`; the paper does not define the term, this is the reading under which its numbers
  `(n−1)/2` and `(n+1)/2` come out). The pointwise bound on `S_n^top` is
  `choose_le_add_rev_of_mem_topF` (`s_k + s_{n−k} ≥ C(n−1,k) + C(n−1,k−1) = C(n,k)` from the
  full simplex on a facet of size `n − 1`); part (3) does not use part (2).

Nothing in the paper's statement or proof was found to be wrong. `n ≥ 3` is the paper's
hypothesis throughout (for `n = 2` the core is empty).

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Symmetry.Beta
import ExteriorConvex.Counting.Duality
import ExteriorConvex.Spine.KozlovThm

open Finset

namespace ExteriorConvex
namespace AlexanderCore

open Beta

variable {n : ℕ}

/-! ## Notation: the core, the top part, μ-coordinates of an `f`-vector -/

/-- The Alexander core `S_n° = {s⃗ ∈ S_n : s_{n−1} = 0}`. -/
def coreF (n : ℕ) : Finset (Fin (n + 1) → ℕ) :=
  (SnF n).filter fun s => s (penult n) = 0

/-- `S_n^top = S_n ∖ S_n°`. -/
def topF (n : ℕ) : Finset (Fin (n + 1) → ℕ) :=
  (SnF n).filter fun s => s (penult n) ≠ 0

/-- An ℕ-valued vector as a point of `ℝ^{n+1}`. -/
def castR (s : Fin (n + 1) → ℕ) : Fin (n + 1) → ℝ := fun j => (s j : ℝ)

theorem mem_coreF {s : Fin (n + 1) → ℕ} : s ∈ coreF n ↔ s ∈ SnF n ∧ s (penult n) = 0 := by
  simp [coreF]

theorem mem_topF {s : Fin (n + 1) → ℕ} : s ∈ topF n ↔ s ∈ SnF n ∧ s (penult n) ≠ 0 := by
  simp [topF]

theorem rev_val (j : Fin (n + 1)) : j.rev.val = n - j.val := by
  rw [Fin.val_rev]; omega

theorem refl_eq_rev (i : Fin (n + 1)) : Beta.refl n i = i.rev :=
  Fin.ext (by rw [rev_val]; rfl)

theorem muOf_castR (s : Fin (n + 1) → ℕ) (j : Fin (n + 1)) :
    muOf n (castR s) j.val = (s j : ℝ) / n.choose j.val := by
  rw [muOf_of_le j.is_le]; rfl

theorem muOf_castR_rev (s : Fin (n + 1) → ℕ) (j : Fin (n + 1)) :
    muOf n (castR s) (n - j.val) = (s j.rev : ℝ) / n.choose j.val := by
  rw [← rev_val, muOf_castR, choose_rev_val]

/-! ## Facts about `f`-vectors of complexes -/

theorem le_choose_of_mem_SnF {s : Fin (n + 1) → ℕ} (hs : s ∈ SnF n) (j : Fin (n + 1)) :
    s j ≤ n.choose j.val :=
  apply_le_choose_of_mem_Fn (SnF_subset_Fn hs) j

/-- The LYM inequality `μ_n ≤ μ_{n−1}` in ℕ form, `n·s_n ≤ s_{n−1}`. -/
theorem last_mul_le_penult (hn : 2 ≤ n) {s : Fin (n + 1) → ℕ} (hs : s ∈ SnF n) :
    n * s (Fin.last n) ≤ s (penult n) := by
  obtain ⟨D, hD, rfl⟩ := mem_SnF.mp hs
  have h := lym hD.ideal (j := n - 1) (by omega) le_rfl
  rw [show n - 1 + 1 = n by omega, Nat.choose_self, Nat.cast_one, div_one,
    Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right,
    le_div_iff₀ (by exact_mod_cast (by omega : 0 < n))] at h
  show n * fEntry D (Fin.last n).val ≤ fEntry D (penult n).val
  simp only [Fin.val_last, penult]
  have : ((n * fEntry D n : ℕ) : ℝ) ≤ (fEntry D (n - 1) : ℕ) := by push_cast; linarith
  exact_mod_cast this

/-! ## Part 1: Alexander duality is an involution of the core -/

theorem rev_zero_eq_last : (⟨0, by omega⟩ : Fin (n + 1)).rev = Fin.last n :=
  Fin.ext (by rw [rev_val]; simp)

theorem rev_one_eq_penult (hn : 1 ≤ n) : (⟨1, by omega⟩ : Fin (n + 1)).rev = penult n :=
  Fin.ext (by rw [rev_val]; rfl)

theorem rev_penult (hn : 1 ≤ n) : (penult n).rev = (⟨1, by omega⟩ : Fin (n + 1)) :=
  Fin.ext (by rw [rev_val]; simp [penult]; omega)

/-- On the core, `s_{n−1} = 0` forces `s_n = 0` (a face of size `n` has faces of size `n−1`). -/
theorem last_eq_zero_of_mem_coreF (hn : 2 ≤ n) {s : Fin (n + 1) → ℕ} (hs : s ∈ coreF n) :
    s (Fin.last n) = 0 := by
  obtain ⟨hS, h⟩ := mem_coreF.mp hs
  have := last_mul_le_penult hn hS
  rw [h, Nat.le_zero, Nat.mul_eq_zero] at this
  omega

/-- **`thm-alexander-core` (1), first half**: `D_n` maps the core `S_n°` into itself. -/
theorem Dvec_mem_coreF (hn : 3 ≤ n) {s : Fin (n + 1) → ℕ} (hs : s ∈ coreF n) :
    Dvec s ∈ coreF n := by
  obtain ⟨hS, h⟩ := mem_coreF.mp hs
  have hl := last_eq_zero_of_mem_coreF (by omega) hs
  have hsF := (mem_SnF_iff (by omega)).mp hS
  refine mem_coreF.mpr ⟨(mem_SnF_iff (by omega)).mpr ⟨Dvec_mem_Fn hsF.1, ?_, ?_⟩, ?_⟩
  · rw [Dvec_apply, rev_zero_eq_last, hl]; simp
  · rw [Dvec_apply, rev_one_eq_penult (by omega), h]; simp
  · rw [Dvec_apply, rev_penult (by omega), hsF.2.2]
    show n.choose (n - 1) - n = 0
    rw [Nat.choose_symm (by omega), Nat.choose_one_right, Nat.sub_self]

theorem Dvec_Dvec_of_mem_coreF {s : Fin (n + 1) → ℕ} (hs : s ∈ coreF n) :
    Dvec (Dvec s) = s :=
  Dvec_Dvec_of_mem_Fn (SnF_subset_Fn (mem_coreF.mp hs).1)

/-- **`thm-alexander-core` (1)**: Alexander duality `D_n` restricts to an involution
(a bijection) of the core `S_n°`, `n ≥ 3`. -/
theorem Dvec_bijOn_coreF (hn : 3 ≤ n) :
    Set.BijOn Dvec (coreF n : Set (Fin (n + 1) → ℕ)) (coreF n) :=
  ⟨fun _ hs => Dvec_mem_coreF hn hs,
    fun a ha b hb hab => by
      rw [← Dvec_Dvec_of_mem_coreF ha, ← Dvec_Dvec_of_mem_coreF hb, hab],
    fun t ht => ⟨Dvec t, Dvec_mem_coreF hn ht, Dvec_Dvec_of_mem_coreF ht⟩⟩

/-- The core is non-empty for `n ≥ 3`: it contains the `f`-vector of the 1-skeleton. -/
theorem coreF_nonempty (hn : 3 ≤ n) : (coreF n).Nonempty :=
  ⟨fvecN (skelComplex n 1), mem_coreF.mpr
    ⟨mem_SnF.mpr ⟨_, isComplex_skelComplex le_rfl, rfl⟩,
      fEntry_skelComplex_of_gt (by simp [penult]; omega)⟩⟩

/-- The summed core identity, ℕ form, every index `j`:
`∑_{S_n°} s_j + ∑_{S_n°} s_{n−j} = |S_n°|·C(n,j)`. -/
theorem sum_coreF_add_rev (hn : 3 ≤ n) (j : Fin (n + 1)) :
    ∑ s ∈ coreF n, s j + ∑ s ∈ coreF n, s j.rev = #(coreF n) * n.choose j.val := by
  have h1 : ∑ s ∈ coreF n, s j = ∑ s ∈ coreF n, Dvec s j :=
    Finset.sum_nbij' Dvec Dvec (fun _ hs => Dvec_mem_coreF hn hs)
      (fun _ hs => Dvec_mem_coreF hn hs) (fun _ hs => Dvec_Dvec_of_mem_coreF hs)
      (fun _ hs => Dvec_Dvec_of_mem_coreF hs)
      (fun _ hs => by rw [Dvec_Dvec_of_mem_coreF hs])
  rw [h1, ← sum_add_distrib, ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun s hs => ?_
  have hle := le_choose_of_mem_SnF (mem_coreF.mp hs).1 j.rev
  rw [choose_rev_val] at hle
  rw [Dvec_apply]
  omega

/-- **`thm-alexander-core` (1), centroid**: the centroid of `S_n°` satisfies
`μ_k + μ_{n−k} = 1`, for every `0 ≤ k ≤ n` (the paper states `1 ≤ k ≤ n−1`). -/
theorem coreF_centroid (hn : 3 ≤ n) {k : ℕ} (hk : k ≤ n) :
    (∑ s ∈ coreF n, muOf n (castR s) k) / #(coreF n) +
      (∑ s ∈ coreF n, muOf n (castR s) (n - k)) / #(coreF n) = 1 := by
  set j : Fin (n + 1) := ⟨k, by omega⟩
  have hc : (#(coreF n) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (coreF_nonempty hn).card_pos.ne'
  have hC : (n.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  have h := sum_coreF_add_rev hn j
  have h' : ∑ s ∈ coreF n, (s j : ℝ) + ∑ s ∈ coreF n, (s j.rev : ℝ) =
      #(coreF n) * n.choose k := by exact_mod_cast h
  simp only [show k = j.val from rfl, muOf_castR, muOf_castR_rev]
  rw [← add_div, ← sum_div, ← sum_div, ← add_div, h', mul_div_cancel_right₀ _ hC,
    div_self hc]

/-- **`thm-alexander-core` (1), the vanishing coordinates**: on the core `μ_{n−1} = μ_n = 0`
pointwise (so also for the centroid). -/
theorem muOf_penult_last_of_mem_coreF (hn : 2 ≤ n) {s : Fin (n + 1) → ℕ} (hs : s ∈ coreF n) :
    muOf n (castR s) (n - 1) = 0 ∧ muOf n (castR s) n = 0 := by
  constructor
  · rw [show n - 1 = (penult n).val from rfl, muOf_castR, (mem_coreF.mp hs).2]; simp
  · have e := muOf_castR s (Fin.last n)
    rw [Fin.val_last] at e
    rw [e, last_eq_zero_of_mem_coreF hn hs]; simp

/-! ## `lem-beta`: on the face `Φ = {μ_{n−1} = 0}`, `β` is Alexander duality -/

/-- `D_n` on real vectors, `x ↦ (C(n,i) − x_{n−i})_i`. -/
noncomputable def DvecR (x : Fin (n + 1) → ℝ) : Fin (n + 1) → ℝ :=
  fun i => (n.choose i.val : ℝ) - x i.rev

theorem DvecR_castR {s : Fin (n + 1) → ℕ} (hs : ∀ j, s j ≤ n.choose j.val) :
    DvecR (castR s) = castR (Dvec s) := by
  funext i
  have := hs i.rev
  rw [choose_rev_val] at this
  simp only [DvecR, castR, Dvec_apply]
  rw [Nat.cast_sub this]

/-- **`lem-beta`, last clause**: on `Φ = Koz(n) ∩ {μ_{n−1} = 0}` (`n ≥ 3`), `β` is
`f_k ↦ C(n,k) − f_{n−k}`, Part II's Alexander duality map, for **every** coordinate
`0 ≤ k ≤ n` (on `{0, 1, n−1, n}`, where `β` is the identity, this uses `f₀ = 1`, `f₁ = n`,
`f_{n−1} = f_n = 0`). -/
theorem beta_eq_DvecR (hn : 3 ≤ n) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ convexHull ℝ (skelSet n)) (h : x (penult n) = 0) : beta n x = DvecR x := by
  rw [hull_skel_eq (by omega)] at hx
  obtain ⟨h0, h1, hch, hlast⟩ := hx
  rw [fin_one_eq (by omega)] at h1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hxn : x (Fin.last n) = 0 := by
    have := hch (n - 1) (by omega) le_rfl
    have e1 : (⟨n - 1 + 1, by omega⟩ : Fin (n + 1)) = Fin.last n := Fin.ext (by simp; omega)
    have e2 : (⟨n - 1, by omega⟩ : Fin (n + 1)) = penult n := rfl
    rw [e1, e2, h, show n - 1 + 1 = n by omega, Nat.choose_self, Nat.cast_one, div_one,
      zero_div] at this
    linarith
  funext i
  rw [beta_apply, refl_eq_rev]
  simp only [DvecR]
  split_ifs with hmid
  · rw [h]; ring
  · have hi : i.val = 0 ∨ i.val = 1 ∨ i.val = n - 1 ∨ i.val = n := by
      have := i.is_le; omega
    rcases hi with hi | hi | hi | hi
    · have e : i = 0 := Fin.ext (by simp [hi])
      have e' : i.rev = Fin.last n := Fin.ext (by rw [rev_val, hi]; simp)
      rw [e', hxn, hi, e, h0]; simp
    · have e : i = ⟨1, by omega⟩ := Fin.ext hi
      rw [e, rev_one_eq_penult (by omega), h, h1]; simp
    · have e : i = penult n := Fin.ext hi
      rw [e, rev_penult (by omega), h1, h, show (penult n).val = n - 1 from rfl,
        Nat.choose_symm (by omega), Nat.choose_one_right]; ring
    · have e : i = Fin.last n := Fin.ext hi
      have e' : (Fin.last n).rev = 0 := Fin.ext (by rw [rev_val]; simp)
      rw [e, e', hxn, h0]; simp

/-- **Discrete form**: on the core, `β` (restricted to `f`-vectors) *is* `D_n`:
`β(s⃗) = D_n(s⃗)` for `s⃗ ∈ S_n°`, `n ≥ 3`. -/
theorem beta_castR_of_mem_coreF (hn : 3 ≤ n) {s : Fin (n + 1) → ℕ} (hs : s ∈ coreF n) :
    beta n (castR s) = castR (Dvec s) := by
  have hS := (mem_coreF.mp hs).1
  have hK : castR s ∈ convexHull ℝ (skelSet n) := by
    rw [hull_skel_eq (by omega)]
    exact Sset_subset_lymChain (by omega) (by rw [Sset_eq_image_SnF]; exact ⟨s, hS, rfl⟩)
  rw [beta_eq_DvecR hn hK (by simp [castR, (mem_coreF.mp hs).2]),
    DvecR_castR (le_choose_of_mem_SnF hS)]

/-! ## Part 3: the centroid of `S_n` is Alexander self-dual up to `ε_n` -/

/-- An order ideal containing a face `τ` has at least `C(|τ|, k)` faces of size `k`. -/
theorem choose_card_le_fEntry {D : Finset (Finset (Fin n))} (hD : IsOrderIdeal D)
    {τ : Finset (Fin n)} (hτ : τ ∈ D) (k : ℕ) : (#τ).choose k ≤ fEntry D k := by
  rw [← card_powersetCard, fEntry]
  refine card_le_card fun σ hσ => ?_
  rw [mem_powersetCard] at hσ
  exact mem_filter.mpr ⟨hD hτ hσ.1, hσ.2⟩

/-- On `S_n^top`, `s_k + s_{n−k} ≥ C(n,k)` for `k ≥ 1`: the complex contains the full simplex
on a facet `τ` of size `n − 1`, contributing `C(n−1,k) + C(n−1,n−k) = C(n,k)`. -/
theorem choose_le_add_rev_of_mem_topF {s : Fin (n + 1) → ℕ} (hs : s ∈ topF n)
    {j : Fin (n + 1)} (hj : 1 ≤ j.val) : n.choose j.val ≤ s j + s j.rev := by
  obtain ⟨hS, htop⟩ := mem_topF.mp hs
  obtain ⟨D, hD, rfl⟩ := mem_SnF.mp hS
  have hne : (D.filter fun σ => #σ = n - 1).Nonempty := by
    rw [← card_pos]; exact Nat.pos_of_ne_zero htop
  obtain ⟨τ, hτ⟩ := hne
  obtain ⟨hτD, hτc⟩ := mem_filter.mp hτ
  have h1 := choose_card_le_fEntry hD.ideal hτD j.val
  have h2 := choose_card_le_fEntry hD.ideal hτD j.rev.val
  rw [hτc] at h1 h2
  rw [rev_val] at h2
  simp only [fvecN_apply, rev_val]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := j.is_le; omega⟩
  obtain ⟨i, hi⟩ : ∃ i, j.val = i + 1 := ⟨j.val - 1, by omega⟩
  have hjle := j.is_le
  rw [hi, Nat.choose_succ_succ']
  simp only [Nat.add_sub_cancel, hi] at h1 h2
  have e : m.choose (m + 1 - (i + 1)) = m.choose i :=
    Nat.choose_symm_of_eq_add (by omega)
  rw [e] at h2
  omega

/-- The uniform average over `S_n`. -/
noncomputable def avgS (n : ℕ) (f : (Fin (n + 1) → ℕ) → ℝ) : ℝ :=
  (∑ s ∈ SnF n, f s) / #(SnF n)

/-- `ε_n = |S_n^top| / |S_n|`. -/
noncomputable def epsN (n : ℕ) : ℝ := #(topF n) / #(SnF n)

theorem SnF_nonempty (hn : 3 ≤ n) : (SnF n).Nonempty := by
  obtain ⟨s, hs⟩ := coreF_nonempty hn
  exact ⟨s, (mem_coreF.mp hs).1⟩

theorem sum_SnF_split (f : (Fin (n + 1) → ℕ) → ℝ) :
    ∑ s ∈ SnF n, f s = ∑ s ∈ coreF n, f s + ∑ s ∈ topF n, f s :=
  (sum_filter_add_sum_filter_not (SnF n) (fun s => s (penult n) = 0) f).symm

theorem avgS_add (f g : (Fin (n + 1) → ℕ) → ℝ) :
    avgS n (fun s => f s + g s) = avgS n f + avgS n g := by
  simp only [avgS, sum_add_distrib, add_div]

theorem avgS_const (hn : 3 ≤ n) (c : ℝ) : avgS n (fun _ => c) = c := by
  have h : (#(SnF n) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (SnF_nonempty hn).card_pos.ne'
  simp only [avgS, sum_const, nsmul_eq_mul]
  field_simp

theorem avgS_sum (t : Finset ℕ) (f : ℕ → (Fin (n + 1) → ℕ) → ℝ) :
    avgS n (fun s => ∑ k ∈ t, f k s) = ∑ k ∈ t, avgS n (f k) := by
  simp only [avgS]
  rw [sum_comm, sum_div]

theorem avgS_le_of_core_zero (hn : 3 ≤ n) (f : (Fin (n + 1) → ℕ) → ℝ)
    (hcore : ∑ s ∈ coreF n, f s = 0) (hlo : ∀ s ∈ topF n, 0 ≤ f s)
    (hhi : ∀ s ∈ topF n, f s ≤ 1) : 0 ≤ avgS n f ∧ avgS n f ≤ epsN n := by
  have hpos : (0 : ℝ) < #(SnF n) := Nat.cast_pos.mpr (SnF_nonempty hn).card_pos
  simp only [avgS, epsN, sum_SnF_split, hcore, zero_add]
  refine ⟨div_nonneg (sum_nonneg hlo) hpos.le, div_le_div_of_nonneg_right ?_ hpos.le⟩
  calc ∑ s ∈ topF n, f s ≤ ∑ _s ∈ topF n, (1 : ℝ) := sum_le_sum hhi
    _ = #(topF n) := by simp

/-- **`thm-alexander-core` (3), first claim**: for `n ≥ 3` and `1 ≤ k ≤ n − 1` the centroid
of `S_n` satisfies `0 ≤ μ_k + μ_{n−k} − 1 ≤ ε_n`. -/
theorem centroid_reflect_bounds (hn : 3 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    0 ≤ avgS n (fun s => muOf n (castR s) k) + avgS n (fun s => muOf n (castR s) (n - k)) - 1 ∧
      avgS n (fun s => muOf n (castR s) k) + avgS n (fun s => muOf n (castR s) (n - k)) - 1 ≤
        epsN n := by
  set j : Fin (n + 1) := ⟨k, by omega⟩
  have hC : (0 : ℝ) < n.choose k := Nat.cast_pos.mpr (Nat.choose_pos (by omega))
  have e : avgS n (fun s => muOf n (castR s) k) + avgS n (fun s => muOf n (castR s) (n - k)) - 1
      = avgS n (fun s => muOf n (castR s) k + muOf n (castR s) (n - k) - 1) := by
    rw [show (fun s => muOf n (castR s) k + muOf n (castR s) (n - k) - 1) =
        fun s => (muOf n (castR s) k + muOf n (castR s) (n - k)) + (-1 : ℝ) from
        funext fun _ => by ring, avgS_add, avgS_add, avgS_const hn]
    ring
  rw [e]
  have hpt : ∀ s : Fin (n + 1) → ℕ, muOf n (castR s) k + muOf n (castR s) (n - k) - 1 =
      ((s j : ℝ) + s j.rev - n.choose k) / n.choose k := by
    intro s
    have hC' : (n.choose j.val : ℝ) ≠ 0 := hC.ne'
    simp only [show k = j.val from rfl, muOf_castR, muOf_castR_rev]
    rw [← add_div, sub_div, div_self hC']
  refine avgS_le_of_core_zero hn _ ?_ (fun s hs => ?_) (fun s hs => ?_)
  · have h := coreF_centroid hn (k := k) (by omega)
    have hc : (#(coreF n) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (coreF_nonempty hn).card_pos.ne'
    rw [← add_div, div_eq_one_iff_eq hc] at h
    rw [sum_sub_distrib, sum_add_distrib, h]; simp
  · rw [hpt]
    have := choose_le_add_rev_of_mem_topF hs (j := j) hk1
    refine div_nonneg ?_ hC.le
    have : ((n.choose k : ℕ) : ℝ) ≤ ((s j + s j.rev : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  · rw [hpt, div_le_one hC]
    have h1 := le_choose_of_mem_SnF (mem_topF.mp hs).1 j
    have h2 := le_choose_of_mem_SnF (mem_topF.mp hs).1 j.rev
    rw [choose_rev_val] at h2
    have : ((s j + s j.rev : ℕ) : ℝ) ≤ ((2 * n.choose k : ℕ) : ℝ) := by
      exact_mod_cast (by simp only [j] at h1 h2 ⊢; omega)
    push_cast at this; linarith

/-- **`thm-alexander-core` (3), second claim**: `0 ≤ μ_n ≤ μ_{n−1} ≤ ε_n` for the centroid of
`S_n`, `n ≥ 3`. -/
theorem centroid_top_bounds (hn : 3 ≤ n) :
    0 ≤ avgS n (fun s => muOf n (castR s) n) ∧
      avgS n (fun s => muOf n (castR s) n) ≤ avgS n (fun s => muOf n (castR s) (n - 1)) ∧
      avgS n (fun s => muOf n (castR s) (n - 1)) ≤ epsN n := by
  have hpos : (0 : ℝ) < #(SnF n) := Nat.cast_pos.mpr (SnF_nonempty hn).card_pos
  have eL : ∀ s : Fin (n + 1) → ℕ, muOf n (castR s) n = s (Fin.last n) := by
    intro s; have e := muOf_castR s (Fin.last n); rw [Fin.val_last] at e; rw [e]; simp
  have eP : ∀ s : Fin (n + 1) → ℕ, muOf n (castR s) (n - 1) = (s (penult n) : ℝ) / n := by
    intro s
    rw [show n - 1 = (penult n).val from rfl, muOf_castR, show (penult n).val = n - 1 from rfl,
      Nat.choose_symm (by omega), Nat.choose_one_right]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  refine ⟨div_nonneg (sum_nonneg fun s _ => by rw [eL]; positivity) hpos.le,
    div_le_div_of_nonneg_right (sum_le_sum fun s hs => ?_) hpos.le, ?_⟩
  · rw [eL, eP, le_div_iff₀ hn0]
    have := last_mul_le_penult (by omega) hs
    have : ((n * s (Fin.last n) : ℕ) : ℝ) ≤ (s (penult n) : ℝ) := by exact_mod_cast this
    push_cast at this; linarith
  · refine (avgS_le_of_core_zero hn _ ?_ (fun s _ => by rw [eP]; positivity)
      (fun s hs => ?_)).2
    · exact sum_eq_zero fun s hs => (muOf_penult_last_of_mem_coreF (by omega) hs).1
    · rw [eP, div_le_one hn0]
      have h := le_choose_of_mem_SnF (mem_topF.mp hs).1 (penult n)
      rw [show (penult n).val = n - 1 from rfl, Nat.choose_symm (by omega),
        Nat.choose_one_right] at h
      exact_mod_cast h

/-- The barycentric index `∑_{k=1}^n μ_k` (= `∑_j j·λ_j` with `λ_j = μ_j − μ_{j+1}`, so
`F̃_j` has index `j`). -/
noncomputable def baryIndex (n : ℕ) (x : Fin (n + 1) → ℝ) : ℝ :=
  ∑ k ∈ Icc 1 n, muOf n x k

/-- `∑_{k=1}^n μ_k = ½ ∑_{k=1}^{n−1} (μ_k + μ_{n−k}) + μ_n`, for any point. -/
theorem baryIndex_eq (hn : 1 ≤ n) (x : Fin (n + 1) → ℝ) :
    baryIndex n x = (∑ k ∈ Icc 1 (n - 1), (muOf n x k + muOf n x (n - k))) / 2 +
      muOf n x n := by
  have hrefl : ∑ k ∈ Icc 1 (n - 1), muOf n x (n - k) = ∑ k ∈ Icc 1 (n - 1), muOf n x k :=
    sum_nbij' (fun k => n - k) (fun k => n - k)
      (fun k hk => by simp only [mem_Icc] at hk ⊢; omega)
      (fun k hk => by simp only [mem_Icc] at hk ⊢; omega)
      (fun k hk => by simp only [mem_Icc] at hk; omega)
      (fun k hk => by simp only [mem_Icc] at hk; omega)
      (fun _ _ => rfl)
  have htop := Finset.sum_Icc_succ_top (a := 1) (b := n - 1) (by omega) (fun k => muOf n x k)
  rw [show n - 1 + 1 = n by omega] at htop
  rw [baryIndex, sum_add_distrib, hrefl, htop]
  ring

/-- **`thm-alexander-core` (3), third claim**: the mean barycentric index of `S_n` lies in
`[(n−1)/2, (n−1)/2 + (n+1)ε_n/2]`, `n ≥ 3`. -/
theorem centroid_index_bounds (hn : 3 ≤ n) :
    ((n : ℝ) - 1) / 2 ≤ avgS n (fun s => baryIndex n (castR s)) ∧
      avgS n (fun s => baryIndex n (castR s)) ≤ ((n : ℝ) - 1) / 2 + (n + 1) * epsN n / 2 := by
  have e : avgS n (fun s => baryIndex n (castR s)) =
      (∑ k ∈ Icc 1 (n - 1), (avgS n (fun s => muOf n (castR s) k) +
        avgS n (fun s => muOf n (castR s) (n - k)))) / 2 +
        avgS n (fun s => muOf n (castR s) n) := by
    simp_rw [baryIndex_eq (by omega : 1 ≤ n)]
    rw [avgS_add]
    congr 1
    rw [show (fun s : Fin (n + 1) → ℕ => (∑ k ∈ Icc 1 (n - 1),
        (muOf n (castR s) k + muOf n (castR s) (n - k))) / 2) =
        fun s => ∑ k ∈ Icc 1 (n - 1),
          (muOf n (castR s) k / 2 + muOf n (castR s) (n - k) / 2) from
        funext fun s => by rw [sum_div]; exact sum_congr rfl fun _ _ => by ring,
      avgS_sum, sum_div]
    refine sum_congr rfl fun k _ => ?_
    rw [avgS_add]
    simp only [avgS, div_eq_mul_inv, ← Finset.sum_mul]
    ring
  have hcard : ((Icc 1 (n - 1)).card : ℝ) = n - 1 := by
    rw [Nat.card_Icc, show n - 1 + 1 - 1 = n - 1 by omega, Nat.cast_sub (by omega)]; simp
  obtain ⟨t0, t1, t2⟩ := centroid_top_bounds hn
  have hlo : (n : ℝ) - 1 ≤ ∑ k ∈ Icc 1 (n - 1), (avgS n (fun s => muOf n (castR s) k) +
      avgS n (fun s => muOf n (castR s) (n - k))) := by
    rw [← hcard, ← nsmul_one, ← sum_const]
    exact sum_le_sum fun k hk => by
      rw [mem_Icc] at hk; linarith [(centroid_reflect_bounds hn hk.1 hk.2).1]
  have hhi : ∑ k ∈ Icc 1 (n - 1), (avgS n (fun s => muOf n (castR s) k) +
      avgS n (fun s => muOf n (castR s) (n - k))) ≤ ((n : ℝ) - 1) * (1 + epsN n) := by
    rw [← hcard, ← nsmul_eq_mul, ← sum_const]
    exact sum_le_sum fun k hk => by
      rw [mem_Icc] at hk; linarith [(centroid_reflect_bounds hn hk.1 hk.2).2]
  rw [e]
  constructor
  · linarith
  · nlinarith

/-! ## Part 2: `|S_n^top| = ∑_{m=0}^{n−1} |S_m|`, via the link of a vertex -/

section Link

variable {m : ℕ}

/-- The link `lk_Δ(v) = {σ ∖ {v} : v ∈ σ ∈ Δ}`. -/
def lk (D : Finset (Finset (Fin n))) (v : Fin n) : Finset (Finset (Fin n)) :=
  (D.filter fun σ => v ∈ σ).image fun σ => σ.erase v

theorem mem_lk {D : Finset (Finset (Fin n))} {v : Fin n} {τ : Finset (Fin n)} :
    τ ∈ lk D v ↔ v ∉ τ ∧ insert v τ ∈ D := by
  constructor
  · intro h
    obtain ⟨σ, hσ, rfl⟩ := mem_image.mp h
    obtain ⟨hσD, hvσ⟩ := mem_filter.mp hσ
    exact ⟨notMem_erase v σ, by rw [insert_erase hvσ]; exact hσD⟩
  · rintro ⟨hv, hD⟩
    exact mem_image.mpr ⟨insert v τ, mem_filter.mpr ⟨hD, mem_insert_self v τ⟩,
      erase_insert hv⟩

theorem isOrderIdeal_lk {D : Finset (Finset (Fin n))} (hD : IsOrderIdeal D) (v : Fin n) :
    IsOrderIdeal (lk D v) := by
  intro σ τ hσ hτσ
  rw [mem_lk] at hσ ⊢
  exact ⟨fun h => hσ.1 (hτσ h), hD hσ.2 (insert_subset_insert v hτσ)⟩

/-- **The link decomposition**: if the order ideal `Δ` contains the facet `[n] ∖ {v}`, then
`f_{k+1}(Δ) = C(n−1, k+1) + f_k(lk_Δ v)`. -/
theorem fEntry_succ_eq {D : Finset (Finset (Fin n))} (hD : IsOrderIdeal D) {v : Fin n}
    (hv : univ.erase v ∈ D) (k : ℕ) :
    fEntry D (k + 1) = (n - 1).choose (k + 1) + fEntry (lk D v) k := by
  rw [fEntry, ← card_filter_add_card_filter_not (fun σ => v ∉ σ)]
  congr 1
  · rw [show n - 1 = #(univ.erase v) by simp, ← card_powersetCard (k + 1) (univ.erase v)]
    congr 1
    ext σ
    simp only [mem_filter, mem_powersetCard]
    constructor
    · rintro ⟨⟨-, hc⟩, hvσ⟩
      exact ⟨fun x hx => mem_erase.mpr ⟨fun h => hvσ (h ▸ hx), mem_univ x⟩, hc⟩
    · rintro ⟨hsub, hc⟩
      exact ⟨⟨hD hv hsub, hc⟩, fun h => (notMem_erase v univ) (hsub h)⟩
  · rw [fEntry]
    refine card_bij' (fun σ _ => σ.erase v) (fun τ _ => insert v τ) ?_ ?_ ?_ ?_
    · intro σ hσ
      simp only [mem_filter, not_not] at hσ
      refine mem_filter.mpr ⟨mem_lk.mpr ⟨notMem_erase v σ, ?_⟩, ?_⟩
      · rw [insert_erase hσ.2]; exact hσ.1.1
      · rw [card_erase_of_mem hσ.2, hσ.1.2]; rfl
    · intro τ hτ
      obtain ⟨hτl, hc⟩ := mem_filter.mp hτ
      obtain ⟨hvτ, hins⟩ := mem_lk.mp hτl
      simp only [mem_filter, not_not]
      exact ⟨⟨hins, by rw [card_insert_of_notMem hvτ, hc]⟩, mem_insert_self v τ⟩
    · intro σ hσ
      simp only [mem_filter, not_not] at hσ
      exact insert_erase hσ.2
    · intro τ hτ
      exact erase_insert (mem_lk.mp (mem_filter.mp hτ).1).1

/-- Relabelling along an embedding `Fin m ↪ Fin n` preserves the `f`-vector. -/
theorem fEntry_map_emb (e : Fin m ↪ Fin n) (G : Finset (Finset (Fin m))) (k : ℕ) :
    fEntry (G.map (mapEmbedding e).toEmbedding) k = fEntry G k := by
  rw [fEntry, fEntry, filter_map, card_map]
  congr 1
  refine filter_congr fun τ _ => ?_
  simp [mapEmbedding_apply]

/-- `S_n^top`'s parametrisation: `f_k = C(n−1, k) + g_{k−1}` (`g_{−1} := 0`, `g_j := 0` for
`j > m`) for the `f`-vector `g` of the link, a complex on `m ≤ n − 1` vertices. -/
def liftVec (n m : ℕ) (g : Fin (m + 1) → ℕ) : Fin (n + 1) → ℕ := fun k =>
  (n - 1).choose k.val + if h : 1 ≤ k.val ∧ k.val - 1 ≤ m then g ⟨k.val - 1, by omega⟩ else 0

theorem liftVec_zero (g : Fin (m + 1) → ℕ) : liftVec n m g 0 = 1 := by
  simp [liftVec]

theorem liftVec_succ (g : Fin (m + 1) → ℕ) (k : ℕ) (hk : k + 1 ≤ n) :
    liftVec n m g ⟨k + 1, by omega⟩ =
      (n - 1).choose (k + 1) + if h : k ≤ m then g ⟨k, by omega⟩ else 0 := by
  simp only [liftVec, Nat.add_sub_cancel]
  congr 1
  by_cases h : k ≤ m
  · rw [dite_eq_left ⟨by omega, h⟩, dite_eq_left h]
  · rw [dite_eq_right (by omega), dite_eq_right h]

/-- The `f`-vector of `Δ` is `liftVec` of that of the relabelled link. -/
theorem fvecN_eq_liftVec {D : Finset (Finset (Fin n))} (hD : IsOrderIdeal D) (hne : D.Nonempty)
    {v : Fin n} (hv : univ.erase v ∈ D) (e : Fin m ↪ Fin n) (G : Finset (Finset (Fin m)))
    (hG : G.map (mapEmbedding e).toEmbedding = lk D v) :
    fvecN D = liftVec n m (fvecN G) := by
  funext k
  rcases k with ⟨_ | k, hk⟩
  · rw [show (⟨0, hk⟩ : Fin (n + 1)) = 0 from rfl, liftVec_zero, fvecN_apply]
    exact fEntry_zero hD hne
  · rw [liftVec_succ _ k (by omega), fvecN_apply]
    show fEntry D (k + 1) = _
    rw [fEntry_succ_eq hD hv, ← hG, fEntry_map_emb]
    congr 1
    split_ifs with h
    · rfl
    · exact fEntry_eq_zero_of_lt (by omega)

/-- `liftVec` remembers `m` in its entry `2`: `f₂ = C(n−1,2) + m`. -/
theorem liftVec_two (hn : 3 ≤ n) {g : Fin (m + 1) → ℕ} (hg : g ∈ SnF m) :
    liftVec n m g ⟨2, by omega⟩ = (n - 1).choose 2 + m := by
  rw [liftVec_succ _ 1 (by omega)]
  congr 1
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [dite_eq_right (by omega)]
  · rw [dite_eq_left (by omega)]
    exact ((mem_SnF_iff hm).mp hg).2.2

theorem liftVec_injective (hm : m < n) : Function.Injective (liftVec n m) := by
  intro g g' h
  funext i
  have := congrFun h ⟨i.val + 1, by omega⟩
  rw [liftVec_succ _ _ (by omega), liftVec_succ _ _ (by omega),
    dite_eq_left (by omega), dite_eq_left (by omega)] at this
  simpa using this

/-- Every `liftVec` of an `f`-vector on `m < n` vertices is in `S_n^top`: cone the complex
over a new vertex `v` and add the full simplex on `[n] ∖ {v}`. -/
theorem liftVec_mem_topF (hn : 2 ≤ n) (hm : m < n) {g : Fin (m + 1) → ℕ} (hg : g ∈ SnF m) :
    liftVec n m g ∈ topF n := by
  obtain ⟨G, hG, rfl⟩ := mem_SnF.mp hg
  set v : Fin n := ⟨n - 1, by omega⟩
  set e : Fin m ↪ Fin n := Fin.castLEEmb (by omega)
  have hev : ∀ i, e i ≠ v := fun i h => by
    have := congrArg Fin.val h; simp [e, v] at this; omega
  set G' := G.map (mapEmbedding e).toEmbedding
  have hvG' : ∀ τ ∈ G', v ∉ τ := by
    intro τ hτ hvτ
    obtain ⟨ρ, -, rfl⟩ := mem_map.mp hτ
    obtain ⟨i, -, hi⟩ := mem_map.mp (by simpa [mapEmbedding_apply] using hvτ)
    exact hev i hi
  set D := (univ.erase v).powerset ∪ G'.image (insert v)
  have hvD : univ.erase v ∈ D := mem_union_left _ (mem_powerset_self _)
  have hlk : G' = lk D v := by
    ext τ
    rw [mem_lk]
    constructor
    · intro hτ
      exact ⟨hvG' τ hτ, mem_union_right _ (mem_image_of_mem _ hτ)⟩
    · rintro ⟨hvτ, hins⟩
      rcases mem_union.mp hins with h | h
      · exact absurd ((mem_powerset.mp h) (mem_insert_self v τ)) (notMem_erase v univ)
      · obtain ⟨τ', hτ', heq⟩ := mem_image.mp h
        have : τ' = τ := by
          rw [← erase_insert (hvG' τ' hτ'), heq, erase_insert hvτ]
        exact this ▸ hτ'
  have hideal : IsOrderIdeal D := by
    intro σ ρ hσ hρσ
    rcases mem_union.mp hσ with h | h
    · exact mem_union_left _ (mem_powerset.mpr ((hρσ.trans (mem_powerset.mp h))))
    · obtain ⟨τ', hτ', rfl⟩ := mem_image.mp h
      by_cases hvρ : v ∈ ρ
      · refine mem_union_right _ (mem_image.mpr ⟨ρ.erase v, ?_, insert_erase hvρ⟩)
        obtain ⟨τ, hτ, rfl⟩ := mem_map.mp hτ'
        refine mem_map.mpr ⟨τ.filter fun i => e i ∈ ρ,
          hG.ideal hτ (filter_subset _ _), ?_⟩
        ext x
        simp only [mapEmbedding_apply, mem_map, mem_filter,
          mem_erase, RelEmbedding.coe_toEmbedding]
        constructor
        · rintro ⟨i, ⟨-, hi⟩, rfl⟩
          exact ⟨hev i, hi⟩
        · rintro ⟨hxv, hxρ⟩
          have hx := hρσ hxρ
          rcases mem_insert.mp hx with hx | hx
          · exact absurd hx hxv
          · simp only [RelEmbedding.coe_toEmbedding, mapEmbedding_apply, mem_map] at hx
            obtain ⟨i, hi, rfl⟩ := hx
            exact ⟨i, ⟨hi, hxρ⟩, rfl⟩
      · refine mem_union_left _ (mem_powerset.mpr fun x hx => mem_erase.mpr ⟨?_, mem_univ x⟩)
        rintro rfl; exact hvρ hx
  have hcx : IsComplex D := by
    refine ⟨hideal, mem_union_left _ (mem_powerset.mpr (empty_subset _)), fun i => ?_⟩
    by_cases hi : i = v
    · subst hi
      refine mem_union_right _ (mem_image.mpr ⟨∅, mem_map.mpr ⟨∅, hG.empty_mem, ?_⟩, ?_⟩)
      · simp [mapEmbedding_apply]
      · rfl
    · exact mem_union_left _ (mem_powerset.mpr (by simpa using hi))
  have hfv := fvecN_eq_liftVec hideal hcx.nonempty hvD e G hlk
  rw [← hfv]
  refine mem_topF.mpr ⟨mem_SnF.mpr ⟨D, hcx, rfl⟩, ?_⟩
  rw [fvecN_apply]
  show fEntry D (n - 1) ≠ 0
  rw [fEntry, ← Nat.pos_iff_ne_zero, card_pos]
  refine ⟨univ.erase v, mem_filter.mpr ⟨hvD, ?_⟩⟩
  rw [card_erase_of_mem (mem_univ v), card_univ, Fintype.card_fin]

/-- Conversely every member of `S_n^top` is a `liftVec`: relabel so that `[n] ∖ {v}` is a
face; the link of `v`, relabelled onto its own vertex set `W` (`|W| = m ≤ n − 1`), is a
complex on `[m]`. -/
theorem exists_liftVec_of_mem_topF (hn : 1 ≤ n) {s : Fin (n + 1) → ℕ} (hs : s ∈ topF n) :
    ∃ m < n, ∃ g ∈ SnF m, liftVec n m g = s := by
  obtain ⟨hS, htop⟩ := mem_topF.mp hs
  obtain ⟨D, hD, rfl⟩ := mem_SnF.mp hS
  have hne : (D.filter fun σ => #σ = n - 1).Nonempty := by
    rw [← card_pos]; exact Nat.pos_of_ne_zero htop
  obtain ⟨τ, hτ⟩ := hne
  obtain ⟨hτD, hτc⟩ := mem_filter.mp hτ
  obtain ⟨v, hvτ⟩ : ∃ v, v ∉ τ := by
    by_contra h
    simp only [not_exists, not_not] at h
    rw [eq_univ_of_forall h, card_univ, Fintype.card_fin] at hτc
    omega
  have hτeq : τ = univ.erase v :=
    eq_of_subset_of_card_le (fun x hx => mem_erase.mpr ⟨fun h => hvτ (h ▸ hx), mem_univ x⟩)
      (by rw [card_erase_of_mem (mem_univ v), card_univ, Fintype.card_fin, hτc])
  have hv : univ.erase v ∈ D := hτeq ▸ hτD
  have hL := isOrderIdeal_lk hD.ideal v
  set W : Finset (Fin n) := univ.filter fun i => ({i} : Finset (Fin n)) ∈ lk D v with hWdef
  have hvW : v ∉ W := by simp [W, mem_lk]
  have hm : #W < n := by
    calc #W < #(univ : Finset (Fin n)) :=
          card_lt_card ⟨subset_univ _, fun h => hvW (h (mem_univ v))⟩
      _ = n := by simp
  set e : Fin #W ↪o Fin n := W.orderEmbOfFin rfl
  have hrange : ∀ x, x ∈ W ↔ ∃ i, e i = x := by
    intro x
    rw [← Finset.mem_coe, ← W.range_orderEmbOfFin rfl]
    rfl
  have hsubW : ∀ ρ ∈ lk D v, ∀ x ∈ ρ, x ∈ W := fun ρ hρ x hx =>
    mem_filter.mpr ⟨mem_univ x, hL hρ (singleton_subset_iff.mpr hx)⟩
  set G : Finset (Finset (Fin #W)) := univ.filter fun τ => τ.map e.toEmbedding ∈ lk D v
  have hGmap : G.map (mapEmbedding e.toEmbedding).toEmbedding = lk D v := by
    ext ρ
    simp only [mem_map, G, mem_filter, mem_univ, true_and, RelEmbedding.coe_toEmbedding,
      mapEmbedding_apply]
    constructor
    · rintro ⟨τ, hτ, rfl⟩; exact hτ
    · intro hρ
      have hρeq : (univ.filter fun i => e i ∈ ρ).map e.toEmbedding = ρ := by
        ext x
        simp only [mem_map, mem_filter, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
        constructor
        · rintro ⟨i, hi, rfl⟩; exact hi
        · intro hx
          obtain ⟨i, rfl⟩ := (hrange x).mp (hsubW ρ hρ x hx)
          exact ⟨i, hx, rfl⟩
      exact ⟨_, by rw [hρeq]; exact hρ, hρeq⟩
  have hGcx : IsComplex G := by
    refine ⟨fun σ ρ hσ hρσ => ?_, ?_, fun i => ?_⟩
    · simp only [G, mem_filter, mem_univ, true_and] at hσ ⊢
      exact hL hσ (map_subset_map.mpr hρσ)
    · simp only [G, mem_filter, mem_univ, true_and, map_empty]
      exact mem_lk.mpr ⟨notMem_empty v, by simpa using hD.singleton_mem v⟩
    · simp only [G, mem_filter, mem_univ, true_and, map_singleton]
      have : e i ∈ W := (hrange _).mpr ⟨i, rfl⟩
      exact (mem_filter.mp this).2
  exact ⟨#W, hm, fvecN G, mem_SnF.mpr ⟨G, hGcx, rfl⟩,
    (fvecN_eq_liftVec hD.ideal hD.nonempty hv e.toEmbedding G hGmap).symm⟩

/-- `S_n^top` is the disjoint union over `0 ≤ m ≤ n − 1` of the `liftVec`-images of `S_m`. -/
theorem topF_eq_biUnion (hn : 3 ≤ n) :
    topF n = (range n).biUnion fun m => (SnF m).image (liftVec n m) := by
  ext s
  simp only [mem_biUnion, mem_range, mem_image]
  constructor
  · intro hs
    obtain ⟨m, hm, g, hg, rfl⟩ := exists_liftVec_of_mem_topF (by omega) hs
    exact ⟨m, hm, g, hg, rfl⟩
  · rintro ⟨m, hm, g, hg, rfl⟩
    exact liftVec_mem_topF (by omega) hm hg

/-- **`thm-alexander-core` (2)**: `|S_n^top| = ∑_{m=0}^{n−1} |S_m|` for `n ≥ 3`. -/
theorem card_topF (hn : 3 ≤ n) : #(topF n) = ∑ m ∈ range n, #(SnF m) := by
  rw [topF_eq_biUnion hn, card_biUnion]
  · refine sum_congr rfl fun m hm => ?_
    exact card_image_of_injective _ (liftVec_injective (mem_range.mp hm))
  · intro m _ m' _ hmm'
    refine disjoint_left.mpr fun x hx hx' => hmm' ?_
    obtain ⟨g, hg, rfl⟩ := mem_image.mp hx
    obtain ⟨g', hg', heq⟩ := mem_image.mp hx'
    have h1 := liftVec_two hn hg
    have h2 := liftVec_two hn hg'
    rw [← heq] at h1
    omega

/-- `|S_0| = 1` (the void-vertex complex `{∅}`), matching the paper's convention. -/
theorem card_SnF_zero : #(SnF 0) = 1 := by decide

end Link

end AlexanderCore
end ExteriorConvex

