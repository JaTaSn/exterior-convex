/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The product regime: `Koz(n; d⃗) ≅ Koz(n)^r` when every gap is at least `n − 1`

Formalisation of `prop-product-regime` of `article/exterior-convex_article3_draft_4.org`
(§"Discrete volume versus volume"), roadmap item 11 of
`working-notes/lean-roadmap-article3-2026-10-21.org`.

**Conventions.** Degree-0-inclusive coordinates throughout, as in `Lattice/LatticePoints.lean`:
`Koz(n) = convexHull ℝ (Sset n) ⊆ ℝ^{n+1}` (own degrees `k = 0..n`, `x₀ = 1`, `x₁ = n`),
`Koz(n; d⃗) = ∑ᵢ shiftIncl N (dᵢ) '' Koz(n) ⊆ ℝ^{N+1}`, `d : Fin r → ℕ` (rank `r`, `Fin`
index `i` is the paper's `i+1`), `dᵢ + n ≤ N`. The product-regime hypothesis is
`ProdGaps n d : ∀ i < j, dᵢ + (n−1) ≤ d_j` (index order). It needs neither sortedness nor
`d₁ = 0`; for the paper's sorted `d⃗` it is equivalent to "every gap `δᵢ = dᵢ − d_{i−1} ≥ n−1`",
and `prodGaps_of_gaps` derives it from that form (`gaps` of `Counting/Transfer.lean`, rank
`r+1`). All results assume `1 ≤ n`.

**The maps** (named, with formulas, for bridging to `prop-pushforward`):
* `glue N d p = ∑ᵢ shiftIncl N (dᵢ) (pᵢ)` (`glueZ` over `ℤ`, via `shiftZ`): `(ℝ^{n+1})^r → ℝ^{N+1}`.
* `proj n d t x`, the block projection `Φ_t`, over any ring:
  `Φ_t(x)ᵢ(0) = t`, `Φ_t(x)ᵢ(1) = t·n`, `Φ_t(x)ᵢ(k) = x_{dᵢ+k} − corr_t(i, dᵢ+k)` for `k ≥ 2`,
  where `corr_t(i, m) = ∑_{j≠i} (t·[d_j = m] + t·n·[d_j + 1 = m])` is the constant that the
  other summands' `f₀, f₁` put into degree `m` (non-zero only when a gap is exactly `n−1` or
  `n`: the paper's "the later summand is constant there"). `projAff n N d t` is the same map as
  an `AffineMap` (`coe_projAff`), with linear part `projLin`.
* `uProj n N d x = (x_{dᵢ+a+2})_{i, a}`, the coordinate projection to `ℝ^U`,
  `U = ⋃ᵢ [dᵢ+2, dᵢ+n]`, indexed by `Fin r × Fin (n−1)` (curried); `uIdx_injective`: these
  `r(n−1)` degrees are distinct. `uShift` is the constant `uProj ∘ glue − (freeProj)^r`.

**Results.**
* `getC_glue`, `proj_glue`: the key computation `Φ_t ∘ glue = id` on tuples on the plane
  `{x₀ = t, x₁ = t·n}`. `sum_image_eq_glue_image`, `smul_koz_eq_glue`:
  `t·Koz(n; d⃗) = glue '' (t·Koz(n))^r` (no hypothesis, any real `t`).
* `bijOn_proj`, `invOn_glue_proj`, `bijOn_proj_one`: `Φ_t : t·Koz(n; d⃗) → (t·Koz(n))^r` is a
  bijection with inverse `glue`, every real `t` (the "lattice-isomorphic" claim, set half).
* `castR_proj`, `castR_glueZ`, `bijOn_projZ`, `bijOn_projZ_one`: `Φ_t` commutes with
  `ℤ → ℝ` and its integer version maps `t·Koz(n; d⃗) ∩ ℤ^{N+1}` (`dilKozLattice`) bijectively
  onto `(t·Koz(n) ∩ ℤ^{n+1})^r` (`dilateLattice`), every `t ∈ ℕ`; at `t = 1`, `kozLattice` onto
  `𝓛_n^r` (the lattice half). The dilate is handled via `(t·Koz(n))^r` and the same map, not via
  `d⃗^{(t)}` (which is not in the product regime).
* `ncard_kozLattice_prod`: `#(Koz(n; d⃗) ∩ ℤ) = |𝓛_n|^r`; `ncard_dilKozLattice`:
  `#(t·Koz(n; d⃗) ∩ ℤ) = #(t·Koz(n) ∩ ℤ)^r` for all `t ∈ ℕ`; `ncard_univ_pi` (generic).
* `ehrhart_product`, `exists_ehrhart_product`: for any Ehrhart polynomial `P` of `Koz(n)` (as in
  `ehrhart_koz`), `P^r` counts `t·Koz(n; d⃗) ∩ ℤ` for **all** `t ∈ ℕ`, `t = 0` included.
* `volume_uProj`, `volume_uProj_eq`: `vol(uProj '' Koz(n; d⃗)) = vol(kozProj n)^r
  = (∏_{k=2}^n C(n,k)/(n−1)!)^r`, the `kozProj` volume of `Lattice/SimplexVolume.lean`.
* `ncard_ffSet_prod`: `|FF(n; d⃗)| = |S_n|^r` (`ffSet` of `Spine/Sumset.lean`, proper
  complexes) — article 2's Proposition 42 in this regime, unconditionally: it falls out of the
  injectivity of `glue`, no `thm-chaining` surjectivity needed.
* `prop_product_regime`: the conjunction of the above, as one statement.

**Deviations.** (1) `1 ≤ n` assumed. (2) The volume is the Lebesgue measure on the curried
`Fin r → Fin (n−1) → ℝ`, i.e. `ℝ^U` reindexed by the bijection `(i, a) ↦ dᵢ + a + 2`
(`uIdx_injective`); the measure-preservation of the currying/reindexing equivalence and the
isometry of the projection on the affine hull are not stated, matching the library's rank-one
convention (`volume_kozProj_eq` is also the volume of a projection). The coordinate projection
differs from `(freeProj)^r ∘ Φ` by the translation `uShift`, which is why the paper says
"affine". (3) "Lattice-isomorphic" is formalised as the two `BijOn` statements plus
`castR_proj` (an affine bijection of the polytopes restricting to a bijection of lattice
points), not as a statement about lattices of the affine hulls.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Lattice.EhrhartRankR
import ExteriorConvex.Lattice.SimplexVolume
import ExteriorConvex.Spine.Sumset

open Finset Polynomial MeasureTheory
open scoped Pointwise

namespace ExteriorConvex

namespace ProductRegime

open _root_.ExteriorConvex.Lattice _root_.ExteriorConvex.TransferEhrhart
  _root_.ExteriorConvex.EhrhartRankR

variable {n N r : ℕ}

/-! ## The hypothesis -/

/-- The product regime: every two summands, in index order, are at least `n − 1` apart. -/
def ProdGaps (n : ℕ) (d : Fin r → ℕ) : Prop := ∀ i j : Fin r, i < j → d i + (n - 1) ≤ d j

/-- The paper's form of the hypothesis: consecutive gaps `δ_{i+1} = d_{i+1} − d_i ≥ n − 1`
(`gaps` of `Counting/Transfer.lean`, in `ℤ`), for rank `r + 1`. -/
theorem prodGaps_of_gaps (hn : 1 ≤ n) {d : Fin (r + 1) → ℕ}
    (h : ∀ i, (n : ℤ) - 1 ≤ gaps d i) : ProdGaps n d := by
  have hstep : ∀ k : Fin r, d k.castSucc + (n - 1) ≤ d k.succ := fun k => by
    have := h k; simp only [gaps] at this; omega
  have hmono : Monotone d := Fin.monotone_iff_le_succ.mpr fun k => by
    have := hstep k; omega
  intro i j hij
  obtain ⟨k, rfl⟩ : ∃ k : Fin r, k.castSucc = i :=
    ⟨⟨i.val, by have := j.isLt; omega⟩, Fin.ext rfl⟩
  have hkj : k.succ ≤ j := by
    rw [Fin.le_def]; simp only [Fin.val_succ]; rw [Fin.lt_def] at hij; simpa using hij
  have := hstep k
  have := hmono hkj
  omega

/-! ## The two maps -/

/-- The glue map `(p₁, …, p_r) ↦ ∑ᵢ shift^{dᵢ}(pᵢ)`. -/
def glue (N : ℕ) (d : Fin r → ℕ) (p : Fin r → Fin (n + 1) → ℝ) : Fin (N + 1) → ℝ :=
  ∑ i, shiftIncl N (d i) (p i)

/-- The integer glue map. -/
def glueZ (N : ℕ) (d : Fin r → ℕ) (q : Fin r → Fin (n + 1) → ℤ) : Fin (N + 1) → ℤ :=
  ∑ i, shiftZ N (d i) (q i)

/-- Total coordinate read-off: `x_m`, or `0` for `m > N`. -/
def getC {R : Type*} [Zero R] (x : Fin (N + 1) → R) (m : ℕ) : R :=
  if h : m < N + 1 then x ⟨m, h⟩ else 0

/-- The constant that the *other* summands contribute in global degree `m`, in the product
regime, at dilation `t`: `t` for every `j ≠ i` with `d_j = m` (its `f₀`) and `t·n` for every
`j ≠ i` with `d_j + 1 = m` (its `f₁`). -/
def corr {R : Type*} [Ring R] (n : ℕ) (d : Fin r → ℕ) (t : R) (i : Fin r) (m : ℕ) : R :=
  ∑ j ∈ univ.erase i, ((if d j = m then t else 0) + (if d j + 1 = m then t * n else 0))

/-- **The block projection `Φ_t`**: block `i`, own degree `k`:
`Φ_t(x)ᵢ(0) = t`, `Φ_t(x)ᵢ(1) = t·n`, and for `k ≥ 2`
`Φ_t(x)ᵢ(k) = x_{dᵢ+k} − corr_t(i, dᵢ+k)`. -/
def proj {R : Type*} [Ring R] (n : ℕ) (d : Fin r → ℕ) (t : R) (x : Fin (N + 1) → R) :
    Fin r → Fin (n + 1) → R := fun i k =>
  if k.val = 0 then t else if k.val = 1 then t * n else getC x (d i + k.val) - corr n d t i (d i + k.val)

/-! ## The key computation -/

variable {d : Fin r → ℕ}

theorem getC_glue (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) (t : ℝ)
    {p : Fin r → Fin (n + 1) → ℝ}
    (hp0 : ∀ j (k : Fin (n + 1)), k.val = 0 → p j k = t)
    (hp1 : ∀ j (k : Fin (n + 1)), k.val = 1 → p j k = t * n)
    (i : Fin r) (k : Fin (n + 1)) (hk : 2 ≤ k.val) :
    getC (glue N d p) (d i + k.val) = p i k + corr n d t i (d i + k.val) := by
  have hkn := k.isLt
  have hlt : d i + k.val < N + 1 := by have := hN i; omega
  rw [getC, dite_eq_left hlt, glue, Finset.sum_apply, ← Finset.add_sum_erase _ _ (mem_univ i), corr]
  congr 1
  · rw [shiftIncl_apply, dite_eq_left ⟨by simp, by simp; omega⟩]
    congr 1; ext; simp
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hji := Finset.ne_of_mem_erase hj
    rw [shiftIncl_apply]
    simp only
    rcases lt_or_gt_of_ne hji with h | h
    · have := hg j i h
      rw [dite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega), add_zero]
    · have := hg i j h
      by_cases hA : d j = d i + k.val
      · rw [dite_eq_left ⟨by omega, by omega⟩, ite_eq_left hA, ite_eq_right (by omega), add_zero]
        exact hp0 _ _ (by show d i + k.val - d j = 0; omega)
      by_cases hB : d j + 1 = d i + k.val
      · rw [dite_eq_left ⟨by omega, by omega⟩, ite_eq_right hA, ite_eq_left hB, zero_add]
        exact hp1 _ _ (by show d i + k.val - d j = 1; omega)
      · rw [dite_eq_right (by omega), ite_eq_right hA, ite_eq_right hB, add_zero]

/-- `Φ_t ∘ glue = id` on tuples whose blocks lie on the plane `{x₀ = t, x₁ = t·n}`. -/
theorem proj_glue (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) (t : ℝ)
    {p : Fin r → Fin (n + 1) → ℝ}
    (hp0 : ∀ j (k : Fin (n + 1)), k.val = 0 → p j k = t)
    (hp1 : ∀ j (k : Fin (n + 1)), k.val = 1 → p j k = t * n) :
    proj n d t (glue N d p) = p := by
  funext i k
  unfold proj
  split_ifs with h0 h1
  · exact (hp0 i k h0).symm
  · exact (hp1 i k h1).symm
  · rw [getC_glue hg hN t hp0 hp1 i k (by omega), add_sub_cancel_right]

/-! ## Set level: `Koz(n; d⃗)` and its dilates are glued products -/

/-- No hypothesis: a Minkowski sum of shifted copies of one set is the glue image of the
product. -/
theorem sum_image_eq_glue_image (d : Fin r → ℕ) (S : Set (Fin (n + 1) → ℝ)) :
    ∑ i, shiftIncl N (d i) '' S = glue N d '' Set.univ.pi fun _ => S := by
  ext x
  rw [Set.mem_fintype_sum]
  constructor
  · rintro ⟨g, hg, rfl⟩
    choose p hp hpg using hg
    exact ⟨p, fun i _ => hp i, by simp only [glue, hpg]⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨fun i => shiftIncl N (d i) (p i), fun i => ⟨p i, hp i (Set.mem_univ _), rfl⟩, rfl⟩

/-- The dilate `t·Koz(n; d⃗)` is the glue image of `(t·Koz(n))^r`, any real `t`. -/
theorem smul_koz_eq_glue (d : Fin r → ℕ) (t : ℝ) :
    t • ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n) =
      glue N d '' Set.univ.pi fun _ => t • convexHull ℝ (Sset n) := by
  rw [← sum_image_eq_glue_image, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := image_smul_setₛₗ (shiftIncl N (d i)) t (convexHull ℝ (Sset n))
  rw [RingHom.id_apply] at h
  exact h.symm

/-- Points of `t·Koz(n)` lie on the plane `{x₀ = t, x₁ = t·n}`. -/
theorem plane_of_mem_smul (hn : 1 ≤ n) {t : ℝ} {y : Fin (n + 1) → ℝ}
    (hy : y ∈ t • convexHull ℝ (Sset n)) :
    (∀ k : Fin (n + 1), k.val = 0 → y k = t) ∧ (∀ k : Fin (n + 1), k.val = 1 → y k = t * n) := by
  rw [hull_Sset_eq hn] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  obtain ⟨h0, h1, -, -⟩ := hx
  refine ⟨fun k hk => ?_, fun k hk => ?_⟩
  · have : k = 0 := Fin.ext hk
    subst this; simp only [Pi.smul_apply, smul_eq_mul, h0, mul_one]
  · have : k = 1 := by rw [fin_one_eq hn]; exact Fin.ext hk
    subst this; simp only [Pi.smul_apply, smul_eq_mul, h1]

/-- **The lattice isomorphism, set level, every dilate.** In the product regime the block
projection `Φ_t` is a bijection `t·Koz(n; d⃗) → (t·Koz(n))^r`, with inverse `glue`. -/
theorem bijOn_proj (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) (t : ℝ) :
    Set.BijOn (proj n d t) (t • ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n))
      (Set.univ.pi fun _ => t • convexHull ℝ (Sset n)) := by
  rw [smul_koz_eq_glue]
  have key : ∀ p ∈ Set.univ.pi (fun _ : Fin r => t • convexHull ℝ (Sset n)),
      proj n d t (glue N d p) = p := fun p hp =>
    proj_glue hg hN t (fun j k hk => (plane_of_mem_smul hn (hp j (Set.mem_univ _))).1 k hk)
      (fun j k hk => (plane_of_mem_smul hn (hp j (Set.mem_univ _))).2 k hk)
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    rw [key p hp]; exact hp
  · rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩ h
    rw [key p hp, key q hq] at h
    rw [h]
  · intro p hp
    exact ⟨glue N d p, ⟨p, hp, rfl⟩, key p hp⟩

/-- `glue` is the inverse of `Φ_t` on the two sets. -/
theorem invOn_glue_proj (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) (t : ℝ) :
    Set.InvOn (glue N d) (proj n d t) (t • ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n))
      (Set.univ.pi fun _ => t • convexHull ℝ (Sset n)) := by
  have key : ∀ p ∈ Set.univ.pi (fun _ : Fin r => t • convexHull ℝ (Sset n)),
      proj n d t (glue N d p) = p := fun p hp =>
    proj_glue hg hN t (fun j k hk => (plane_of_mem_smul hn (hp j (Set.mem_univ _))).1 k hk)
      (fun j k hk => (plane_of_mem_smul hn (hp j (Set.mem_univ _))).2 k hk)
  rw [smul_koz_eq_glue]
  refine ⟨?_, key⟩
  rintro _ ⟨p, hp, rfl⟩
  rw [key p hp]

/-- The undilated statement: `Φ = Φ₁ : Koz(n; d⃗) → Koz(n)^r` is a bijection. -/
theorem bijOn_proj_one (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) :
    Set.BijOn (proj n d (1 : ℝ)) (∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n))
      (Set.univ.pi fun _ => convexHull ℝ (Sset n)) := by
  simpa only [one_smul] using bijOn_proj (N := N) hn hg hN 1

/-! ## Lattice level -/

theorem castR_proj (t : ℤ) (z : Fin (N + 1) → ℤ) (i : Fin r) :
    castR (proj n d t z i) = proj n d (t : ℝ) (castR z) i := by
  funext k
  simp only [castR_apply, proj, getC, corr]
  split_ifs <;> push_cast <;> simp

theorem castR_glueZ (q : Fin r → Fin (n + 1) → ℤ) :
    castR (glueZ N d q) = glue N d (fun i => castR (q i)) := by
  simp only [glueZ, glue, castR_sum, castR_shiftZ]

/-- **The lattice isomorphism, every dilate `t ∈ ℕ`.** In the product regime the integer
block projection `Φ_t` maps the lattice points of `t·Koz(n; d⃗)` bijectively onto
`(t·Koz(n) ∩ ℤ^{n+1})^r`; its inverse is `glueZ`. -/
theorem bijOn_projZ (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) (t : ℕ) :
    Set.BijOn (proj n d (t : ℤ)) (dilKozLattice n (N := N) t d)
      (Set.univ.pi fun _ => dilateLattice n t) := by
  have hB := bijOn_proj (N := N) hn hg hN (t : ℝ)
  have hI := invOn_glue_proj (N := N) hn hg hN (t : ℝ)
  have hc : ∀ z : Fin (N + 1) → ℤ, ∀ i, castR (proj n d (t : ℤ) z i) =
      proj n d (t : ℝ) (castR z) i := fun z i => by rw [castR_proj]; simp
  refine ⟨?_, ?_, ?_⟩
  · intro z hz i _
    show castR (proj n d (t : ℤ) z i) ∈ (t : ℝ) • convexHull ℝ (Sset n)
    rw [hc]
    exact hB.mapsTo hz i (Set.mem_univ _)
  · intro z hz w hw h
    apply castR_injective
    refine hB.injOn hz hw ?_
    funext i
    rw [← hc, ← hc, h]
  · intro q hq
    have hq' : (fun i => castR (q i)) ∈
        Set.univ.pi (fun _ : Fin r => (t : ℝ) • convexHull ℝ (Sset n)) :=
      fun i _ => hq i (Set.mem_univ _)
    refine ⟨glueZ N d q, ?_, ?_⟩
    · show castR (glueZ N d q) ∈ (t : ℝ) • ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)
      rw [castR_glueZ, smul_koz_eq_glue]
      exact ⟨_, hq', rfl⟩
    · funext i
      apply castR_injective
      rw [hc, castR_glueZ, hI.2 hq']

/-- The undilated lattice statement: `Φ` maps `Koz(n; d⃗) ∩ ℤ^{N+1}` onto `𝓛_n^r`. -/
theorem bijOn_projZ_one (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) :
    Set.BijOn (proj n d (1 : ℤ)) (kozLattice n (N := N) d)
      (Set.univ.pi fun _ => latticePts n) := by
  have h := bijOn_projZ (N := N) hn hg hN 1
  simp only [Nat.cast_one] at h
  have e1 : dilKozLattice n (N := N) 1 d = kozLattice n (N := N) d := by
    ext z; simp [dilKozLattice, kozLattice]
  have e2 : dilateLattice n 1 = latticePts n := by
    ext z; simp [dilateLattice, latticePts]
  rwa [e1, e2] at h

/-- `ncard` of a finite product of sets (no finiteness hypothesis: both sides are `0` as soon
as one factor is infinite and none is empty). -/
theorem ncard_univ_pi {ι α : Type*} [Fintype ι] [DecidableEq ι] (S : ι → Set α) :
    (Set.univ.pi S).ncard = ∏ i, (S i).ncard := by
  classical
  by_cases hfin : ∀ i, (S i).Finite
  · have : Set.univ.pi S = ↑(Fintype.piFinset fun i => (hfin i).toFinset) := by
      ext x; simp
    rw [this, Set.ncard_coe_finset, Fintype.card_piFinset]
    exact Finset.prod_congr rfl fun i _ => (Set.ncard_eq_toFinset_card _ (hfin i)).symm
  · push Not at hfin
    obtain ⟨i, hi⟩ := hfin
    rw [Finset.prod_eq_zero (mem_univ i) hi.ncard]
    by_cases hne : ∀ j, (S j).Nonempty
    · have hinf : (Set.univ.pi S).Infinite := by
        intro hf
        apply hi
        have := hf.image (Function.eval i)
        rwa [Set.eval_image_univ_pi (Set.univ_pi_nonempty_iff.mpr hne)] at this
      exact hinf.ncard
    · push Not at hne
      obtain ⟨j, hj⟩ := hne
      rw [Set.univ_pi_eq_empty hj, Set.ncard_empty]

/-- **Ehrhart counts multiply**: `#(t·Koz(n; d⃗) ∩ ℤ) = #(t·Koz(n) ∩ ℤ)^r` for every `t ∈ ℕ`. -/
theorem ncard_dilKozLattice (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N)
    (t : ℕ) : (dilKozLattice n (N := N) t d).ncard = (dilateLattice n t).ncard ^ r := by
  have h := bijOn_projZ (N := N) hn hg hN t
  rw [← h.injOn.ncard_image, h.image_eq, ncard_univ_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin]

/-- **The lattice-point count**: `#(Koz(n; d⃗) ∩ ℤ^{N+1}) = |𝓛_n|^r`. -/
theorem ncard_kozLattice_prod (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) :
    (kozLattice n (N := N) d).ncard = (latticeFinset n).card ^ r := by
  have h := bijOn_projZ_one (N := N) hn hg hN
  rw [← h.injOn.ncard_image, h.image_eq, ncard_univ_pi, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ← coe_latticeFinset hn, Set.ncard_coe_finset]

/-! ## The Ehrhart polynomial -/

/-- **The Ehrhart polynomial is `L_{Koz(n)}(t)^r`**: if `P` is the Ehrhart polynomial of
`Koz(n)` (agreement for `t ≥ 1`, as in `ehrhart_koz`), then `P^r` counts the lattice points of
every dilate of `Koz(n; d⃗)`, `t = 0` included. -/
theorem ehrhart_product [NeZero n] (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) (P : ℚ[X])
    (hP : ∀ t : ℕ, 1 ≤ t → P.eval (t : ℚ) = (dilateLattice n t).ncard) (t : ℕ) :
    (P ^ r).eval (t : ℚ) = (dilKozLattice n (N := N) t d).ncard := by
  have hn : 1 ≤ n := NeZero.one_le
  rw [Polynomial.eval_pow]
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [dilKozLattice_zero, Set.ncard_singleton, Nat.cast_zero, ehrhart_koz_eval_zero P hP,
      one_pow, Nat.cast_one]
  · rw [hP t ht, ncard_dilKozLattice hn hg hN t, Nat.cast_pow]

/-- Existence form: an explicit polynomial (`ehrhart_koz`'s, to the `r`-th power). -/
theorem exists_ehrhart_product [NeZero n] (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) :
    ∃ P : ℚ[X], (∀ t : ℕ, 1 ≤ t → P.eval (t : ℚ) = (dilateLattice n t).ncard) ∧
      ∀ t : ℕ, (P ^ r).eval (t : ℚ) = (dilKozLattice n (N := N) t d).ncard := by
  obtain ⟨P, -, -, hP⟩ := ehrhart_koz n
  exact ⟨P, hP, ehrhart_product hg hN P hP⟩

/-! ## `|FF(n; d⃗)| = |S_n|^r` -/

/-- **Article 2's Proposition 42 in the product regime** (`ffSet` is the proper-complex
`FF(n; d⃗)` of article 3): `|FF(n; d⃗)| = |S_n|^r`. -/
theorem ncard_ffSet_prod (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) :
    (ffSet n N d).ncard = (Sset n).ncard ^ r := by
  have hI := invOn_glue_proj (N := N) hn hg hN (1 : ℝ)
  have hinj : Set.InjOn (glue N d) (Set.univ.pi fun _ : Fin r => convexHull ℝ (Sset n)) := by
    have := hI.2.injOn
    simpa only [one_smul] using this
  rw [ff_eq_sumset, sum_image_eq_glue_image,
    (hinj.mono (Set.pi_mono fun _ _ => subset_convexHull ℝ _)).ncard_image, ncard_univ_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-! ## Volume -/

/-- **The coordinate projection to `ℝ^U`**, `U = ⋃ᵢ [dᵢ+2, dᵢ+n]`, indexed by
`(i, a) ∈ Fin r × Fin (n−1)` standing for the global degree `dᵢ + a + 2`; in the product regime
these `r(n−1)` degrees are distinct. -/
def uProj (n N : ℕ) (d : Fin r → ℕ) (x : Fin (N + 1) → ℝ) : Fin r → Fin (n - 1) → ℝ :=
  fun i a => getC x (d i + a.val + 2)

/-- The constant translation between `uProj` and the free coordinates of `Φ`. -/
def uShift (n : ℕ) (d : Fin r → ℕ) : Fin r → Fin (n - 1) → ℝ :=
  fun i a => corr n d (1 : ℝ) i (d i + a.val + 2)

theorem uProj_glue (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N)
    {p : Fin r → Fin (n + 1) → ℝ}
    (hp0 : ∀ j (k : Fin (n + 1)), k.val = 0 → p j k = 1)
    (hp1 : ∀ j (k : Fin (n + 1)), k.val = 1 → p j k = 1 * n) :
    uProj n N d (glue N d p) = (fun i => KozVolume.freeProj n (p i)) + uShift n d := by
  funext i a
  have h := getC_glue hg hN 1 hp0 hp1 i (KozVolume.freeIdx n a) (by simp [KozVolume.freeIdx])
  simp only [KozVolume.freeIdx] at h
  simp only [uProj, uShift, Pi.add_apply, KozVolume.freeProj, KozVolume.freeIdx]
  rw [show d i + a.val + 2 = d i + (a.val + 2) by ring, h]

/-- The `U`-projection of `Koz(n; d⃗)` is a translate of `(proj Koz(n))^r`. -/
theorem uProj_image (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) :
    uProj n N d '' (∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)) =
      (fun y => y + uShift n d) '' Set.univ.pi fun _ => KozVolume.kozProj n := by
  have hK : convexHull ℝ (skelSet n) = convexHull ℝ (Sset n) := by
    rw [hull_skel_eq hn, hull_Sset_eq hn]
  rw [sum_image_eq_glue_image, Set.image_image, KozVolume.kozProj, hK,
    ← Set.piMap_image_univ_pi, Set.image_image]
  refine Set.image_congr fun p hp => ?_
  have hp' : ∀ j, p j ∈ (1 : ℝ) • convexHull ℝ (Sset n) := fun j => by
    rw [one_smul]; exact hp j (Set.mem_univ _)
  rw [uProj_glue hg hN (fun j k hk => (plane_of_mem_smul hn (hp' j)).1 k hk)
    (fun j k hk => (plane_of_mem_smul hn (hp' j)).2 k hk)]
  rfl

/-- **The volume**: the `D = r(n−1)`-dimensional Lebesgue volume of the coordinate
projection of `Koz(n; d⃗)` to `ℝ^U` is `vol(Koz(n))^r`. -/
theorem volume_uProj (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) :
    volume (uProj n N d '' (∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n))) =
      volume (KozVolume.kozProj n) ^ r := by
  rw [uProj_image hn hg hN, Set.image_add_right, measure_preimage_add_right, volume_pi_pi,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The same, explicitly: `vol(Koz(n; d⃗)) = (∏_{k=2}^n C(n,k) / (n−1)!)^r`. -/
theorem volume_uProj_eq (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) :
    volume (uProj n N d '' (∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n))) =
      ENNReal.ofReal ((∏ k ∈ Icc 2 n, (n.choose k : ℝ)) / (n - 1).factorial) ^ r := by
  rw [volume_uProj hn hg hN, KozVolume.volume_kozProj_eq hn]

/-! ## `Φ` as an affine map, and the summary -/

/-- The linear part of `Φ_t`: zero on own degrees `0, 1`, the coordinate `x_{dᵢ+k}` on
own degree `k ≥ 2`. -/
def projLin (n N : ℕ) (d : Fin r → ℕ) :
    (Fin (N + 1) → ℝ) →ₗ[ℝ] (Fin r → Fin (n + 1) → ℝ) :=
  LinearMap.pi fun i => LinearMap.pi fun k =>
    if h : 2 ≤ k.val ∧ d i + k.val < N + 1 then LinearMap.proj ⟨d i + k.val, h.2⟩ else 0

/-- **`Φ_t` as an affine map** `ℝ^{N+1} → (ℝ^{n+1})^r`; `⇑(projAff n N d t) = proj n d t`
(`coe_projAff`). -/
def projAff (n N : ℕ) (d : Fin r → ℕ) (t : ℝ) :
    (Fin (N + 1) → ℝ) →ᵃ[ℝ] (Fin r → Fin (n + 1) → ℝ) where
  toFun := proj n d t
  linear := projLin n N d
  map_vadd' x v := by
    funext i k
    simp only [proj, projLin, getC, vadd_eq_add, Pi.add_apply, LinearMap.pi_apply]
    by_cases h0 : k.val = 0
    · simp [h0]
    by_cases h1 : k.val = 1
    · simp [h1]
    by_cases hN : d i + k.val < N + 1
    · rw [dite_eq_left (show 2 ≤ k.val ∧ d i + k.val < N + 1 by omega)]
      simp [h0, h1, hN]; ring
    · rw [dite_eq_right (show ¬(2 ≤ k.val ∧ d i + k.val < N + 1) by omega)]
      simp [h0, h1, hN]

@[simp] theorem coe_projAff (t : ℝ) : ⇑(projAff n N d t) = proj n d t := rfl

/-- In the product regime the `r(n−1)` degrees `dᵢ + a + 2` of `U` are distinct, so `uProj`
is a genuine coordinate projection to `ℝ^U` (reindexed by `Fin r × Fin (n−1)`). -/
theorem uIdx_injective (hg : ProdGaps n d) :
    Function.Injective fun ia : Fin r × Fin (n - 1) => d ia.1 + ia.2.val + 2 := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  simp only at h
  have ha := a.isLt; have hb := b.isLt
  rcases lt_trichotomy i j with hij | rfl | hij
  · have := hg i j hij; omega
  · simp only [Prod.mk.injEq, true_and]; exact Fin.ext (by omega)
  · have := hg j i hij; omega

/-- **`prop-product-regime`**, collected. For `n ≥ 1`, every two shifts at least `n − 1` apart
(`ProdGaps`, e.g. from `prodGaps_of_gaps`) and `dᵢ + n ≤ N`, with
`Koz(n; d⃗) = ∑ᵢ shift^{dᵢ} Koz(n)` and `Φ = projAff n N d 1`:
1. `Φ` is an affine bijection `Koz(n; d⃗) → Koz(n)^r` (inverse `glue`), and it carries
   integer points to integer points (`Φ ∘ castR = castR ∘ Φ_ℤ`), `Φ_ℤ` being a bijection
   `Koz(n; d⃗) ∩ ℤ^{N+1} → 𝓛_n^r` (inverse `glueZ`);
2. `#(Koz(n; d⃗) ∩ ℤ^{N+1}) = |𝓛_n|^r`, and `#(t·Koz(n; d⃗) ∩ ℤ) = #(t·Koz(n) ∩ ℤ)^r`, all `t`;
3. `vol_U(Koz(n; d⃗)) = vol(Koz(n))^r`;
4. `|FF(n; d⃗)| = |S_n|^r`. -/
theorem prop_product_regime (hn : 1 ≤ n) (hg : ProdGaps n d) (hN : ∀ i, d i + n ≤ N) :
    Set.BijOn (projAff n N d 1) (∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n))
        (Set.univ.pi fun _ => convexHull ℝ (Sset n)) ∧
      (∀ z : Fin (N + 1) → ℤ, projAff n N d 1 (castR z) = fun i => castR (proj n d (1 : ℤ) z i)) ∧
      Set.BijOn (proj n d (1 : ℤ)) (kozLattice n (N := N) d) (Set.univ.pi fun _ => latticePts n) ∧
      (kozLattice n (N := N) d).ncard = (latticeFinset n).card ^ r ∧
      (∀ t : ℕ, (dilKozLattice n (N := N) t d).ncard = (dilateLattice n t).ncard ^ r) ∧
      volume (uProj n N d '' (∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n))) =
        volume (KozVolume.kozProj n) ^ r ∧
      (ffSet n N d).ncard = (Sset n).ncard ^ r := by
  refine ⟨by simpa using bijOn_proj_one (N := N) hn hg hN, fun z => ?_,
    bijOn_projZ_one hn hg hN, ncard_kozLattice_prod hn hg hN, ncard_dilKozLattice hn hg hN,
    volume_uProj hn hg hN, ncard_ffSet_prod hn hg hN⟩
  funext i
  rw [castR_proj, coe_projAff, Int.cast_one]

end ProductRegime

end ExteriorConvex
