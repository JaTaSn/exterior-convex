/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The uniform measure on `Koz(n)` is `β`-invariant

Formalisation of `thm-beta-continuous` in `article/exterior-convex_article3_draft_4.org`
(= Theorem 4 (continuous) of `working-notes/centroids-and-moments-discrete-vs-continuous.org`),
for `n ≥ 3`, using `β` from `Symmetry/Beta.lean`.

**Coordinates and the measure.**  `lift n : ℝ^{n−1} →ᵃ ℝ^{n+1}`, `y ↦ (1, n, y)` (equal to
`KozVolume.liftFree`, `lift_eq_liftFree`), is an affine chart of the plane
`P = {x₀ = 1, x₁ = n}` with inverse `proj n = freeProj n` on `P`.  The uniform measure on `Koz(n)`
is `kozMeasure n := (volume.restrict (kozProj n)).map (lift n)` — Lebesgue measure of the free
coordinates `f₂..fₙ`, restricted to the projected simplex and pushed into `P`.  It is not
normalised: its mass is `V = ∏_{k=2}^n C(n,k)/(n−1)!` (`kozMeasure_univ`, from
`Lattice/SimplexVolume.lean`); by `KozVolume.sum_sq_sub_freeProj` it is the Euclidean
`(n−1)`-volume on `Koz(n)`.

* `betaFree n = proj ∘ β ∘ lift`: `β` descended to an affine map of `ℝ^{n−1}`;
  `beta_lift`: `β ∘ lift = lift ∘ β̄`; `betaFree_involutive`.
* `abs_det_betaFree_linear`: `|det| = 1` of its linear part (from involutivity: `det² = 1`);
  `measurePreserving_betaFree`: `β̄` preserves Lebesgue measure on `ℝ^{n−1}`
  (`Measure.map_linearMap_addHaar_eq_smul_addHaar` plus translation invariance).
* `betaFree_image_kozProj`: `β̄(kozProj n) = kozProj n` (from `beta_image_koz`);
  `map_betaFree_restrict`: the restricted Lebesgue measure is `β̄`-invariant.
* `kozMeasure_map_beta`: **`β_* μ = μ`** for the uniform measure `μ` on `Koz(n)`
  (the invariance clause of `thm-beta-continuous`); `integral_kozMeasure_comp_beta`:
  `∫ F∘β dμ = ∫ F dμ` for every integrand `F` (so all moments, in particular the covariance
  matrix, are `β`-invariant — this is the covariance clause, in the form "invariance of every
  integral"; the covariance matrix is not separately defined).
* `integral_mu_add_mu_reflect`: `∫ (μ_k + μ_{n−k}) dμ = ∫ (1 + μ_{n−1}) dμ`, `1 ≤ k ≤ n−1`;
  `centroid_identity`: the same divided by `V`, i.e. the centroid identity
  `μ_k(c) + μ_{n−k}(c) = 1 + μ_{n−1}(c)`.  For `k ∈ {1, n−1}` it is the identity `μ₁ = 1` on
  `Koz(n)` (`ae_kozMeasure_mem`).

**Hypotheses.**  `n ≥ 3` (the paper's), used for `beta_image_koz`; the chart lemmas need
`n ≥ 1`. No primality: this is the continuous statement.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Symmetry.Beta
import ExteriorConvex.Lattice.SimplexVolume

open Finset MeasureTheory

namespace ExteriorConvex
namespace BetaMeasure

open KozVolume Beta

variable {n : ℕ}

/-! ## The free-coordinate chart of the plane `{x₀ = 1, x₁ = n}` as an affine map -/

/-- Linear part of the lift `ℝ^{n−1} → ℝ^{n+1}`: `y ↦ (0, 0, y₀, …, y_{n−2})`. -/
noncomputable def liftLin (n : ℕ) : (Fin (n - 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) :=
  LinearMap.pi fun i => if h : 2 ≤ i.val then
    LinearMap.proj (R := ℝ) (φ := fun _ : Fin (n - 1) => ℝ)
      ⟨i.val - 2, by have := i.isLt; omega⟩ else 0

/-- Translation part of the lift: `(1, n, 0, …, 0)`. -/
def liftConst (n : ℕ) : Fin (n + 1) → ℝ := fun i =>
  if i.val = 0 then 1 else if i.val = 1 then (n : ℝ) else 0

/-- The lift `y ↦ (1, n, y)` as an affine map; it agrees with `KozVolume.liftFree`. -/
noncomputable def lift (n : ℕ) : (Fin (n - 1) → ℝ) →ᵃ[ℝ] (Fin (n + 1) → ℝ) :=
  (liftLin n).toAffineMap + AffineMap.const ℝ _ (liftConst n)

theorem lift_eq_liftFree (y : Fin (n - 1) → ℝ) : lift n y = liftFree n y := by
  funext i
  simp only [lift, AffineMap.coe_add, LinearMap.coe_toAffineMap, AffineMap.coe_const,
    Pi.add_apply, Function.const_apply, liftLin, LinearMap.pi_apply, liftConst, liftFree]
  have := i.isLt
  by_cases h0 : i.val = 0
  · simp [h0]
  by_cases h1 : i.val = 1
  · simp [h1]
  have h2 : 2 ≤ i.val := by omega
  have h3 : i.val - 2 < n - 1 := by omega
  simp [h0, h1, h2, h3]

/-- The free-coordinate projection `freeProj n` as a linear map. -/
noncomputable def proj (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n - 1) → ℝ) :=
  LinearMap.funLeft ℝ ℝ (freeIdx n)

theorem coe_proj : ⇑(proj n) = freeProj n := rfl

theorem proj_lift (y : Fin (n - 1) → ℝ) : proj n (lift n y) = y := by
  rw [lift_eq_liftFree, coe_proj, freeProj_liftFree]

theorem lift_mem_plane (hn : 1 ≤ n) (y : Fin (n - 1) → ℝ) : lift n y ∈ plane ℝ n := by
  rw [lift_eq_liftFree]; exact liftFree_mem_plane hn y

theorem lift_proj (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (hx : x ∈ plane ℝ n) :
    lift n (proj n x) = x :=
  freeProj_injOn hn (lift_mem_plane hn _) hx (proj_lift _)

theorem continuous_lift : Continuous (lift n) := (lift n).continuous_of_finiteDimensional

theorem continuous_proj : Continuous (proj n) := (proj n).continuous_of_finiteDimensional

theorem range_lift (hn : 1 ≤ n) : Set.range (lift n) = plane ℝ n := by
  refine Set.Subset.antisymm ?_ fun x hx => ⟨proj n x, lift_proj hn hx⟩
  rintro _ ⟨y, rfl⟩
  exact lift_mem_plane hn y

theorem isClosed_plane : IsClosed (plane ℝ n) :=
  (isClosed_eq (continuous_apply 0) continuous_const).inter
    (isClosed_eq (continuous_apply 1) continuous_const)

theorem measurableEmbedding_lift (hn : 1 ≤ n) : MeasurableEmbedding (lift n) :=
  MeasurableEmbedding.of_measurable_inverse continuous_lift.measurable
    (by rw [range_lift hn]; exact isClosed_plane.measurableSet) continuous_proj.measurable
    proj_lift

/-! ## `β` descends to an affine involution of `ℝ^{n−1}` -/

/-- `β` preserves the plane `{x₀ = 1, x₁ = n}` (it fixes the coordinates `0` and `1`). -/
theorem beta_mem_plane (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (hx : x ∈ plane ℝ n) :
    beta n x ∈ plane ℝ n := by
  refine ⟨?_, ?_⟩
  · rw [beta_apply_not_mid _ _ (by simp)]; exact hx.1
  · rw [beta_apply_not_mid _ _ (by rw [fin_one_eq hn]; simp)]; exact hx.2

/-- `β` in the free coordinates: `β̄ = proj ∘ β ∘ lift`, an affine map of `ℝ^{n−1}`. -/
noncomputable def betaFree (n : ℕ) : (Fin (n - 1) → ℝ) →ᵃ[ℝ] (Fin (n - 1) → ℝ) :=
  (proj n).toAffineMap.comp ((beta n).comp (lift n))

theorem betaFree_apply (y : Fin (n - 1) → ℝ) : betaFree n y = proj n (beta n (lift n y)) := rfl

/-- `β ∘ lift = lift ∘ β̄`. -/
theorem beta_lift (hn : 1 ≤ n) (y : Fin (n - 1) → ℝ) :
    beta n (lift n y) = lift n (betaFree n y) :=
  (lift_proj hn (beta_mem_plane hn (lift_mem_plane hn y))).symm

theorem betaFree_involutive (hn : 1 ≤ n) : Function.Involutive (betaFree n) := by
  intro y
  rw [betaFree_apply, ← beta_lift hn, beta_beta, proj_lift]

/-- The linear part of `β̄` has determinant `±1`. -/
theorem abs_det_betaFree_linear (hn : 1 ≤ n) : |LinearMap.det (betaFree n).linear| = 1 := by
  have hcomp : (betaFree n).comp (betaFree n) = AffineMap.id ℝ _ := by
    exact AffineMap.ext fun y => betaFree_involutive hn y
  have hlin : (betaFree n).linear.comp (betaFree n).linear = LinearMap.id :=
    congrArg AffineMap.linear hcomp
  have hdet := congrArg LinearMap.det hlin
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  rcases mul_self_eq_one_iff.mp hdet with h | h <;> simp [h]

/-- **`β̄` preserves Lebesgue measure on `ℝ^{n−1}`.** -/
theorem measurePreserving_betaFree (hn : 1 ≤ n) :
    MeasurePreserving (betaFree n) volume volume := by
  set L := (betaFree n).linear
  have habs := abs_det_betaFree_linear hn
  have hdet : LinearMap.det L ≠ 0 := by
    intro h; rw [h, abs_zero] at habs; exact zero_ne_one habs
  have hL : MeasurePreserving L volume volume := by
    refine ⟨L.continuous_of_finiteDimensional.measurable, ?_⟩
    rw [Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet, abs_inv, habs]
    simp
  have hdec : ⇑(betaFree n) = (fun y => y + betaFree n 0) ∘ ⇑L := by
    funext y
    rw [Function.comp_apply]
    exact congrFun (AffineMap.decomp (betaFree n)) y
  rw [hdec]
  exact (measurePreserving_add_right volume (betaFree n 0)).comp hL

/-- `β̄` as a measurable equivalence (it is a continuous involution). -/
noncomputable def betaFreeEquiv (hn : 1 ≤ n) : (Fin (n - 1) → ℝ) ≃ᵐ (Fin (n - 1) → ℝ) where
  toEquiv := Function.Involutive.toPerm _ (betaFree_involutive hn)
  measurable_toFun := (betaFree n).continuous_of_finiteDimensional.measurable
  measurable_invFun := (betaFree n).continuous_of_finiteDimensional.measurable

/-- `β̄` maps the projected simplex `kozProj n` onto itself (`lem-beta` in free coordinates). -/
theorem betaFree_image_kozProj (hn : 3 ≤ n) : betaFree n '' kozProj n = kozProj n := by
  have hP := convexHull_skelSet_subset_plane (n := n) (by omega)
  have hlp : lift n '' kozProj n = convexHull ℝ (skelSet n) := by
    rw [kozProj, Set.image_image]
    refine Eq.trans (Set.image_congr fun x hx => lift_proj (by omega) (hP hx)) (Set.image_id _)
  have : ⇑(betaFree n) = ⇑(proj n) ∘ ⇑(beta n) ∘ ⇑(lift n) := rfl
  rw [this, Set.image_comp, Set.image_comp, hlp, beta_image_koz hn, kozProj, coe_proj]

theorem betaFree_preimage_kozProj (hn : 3 ≤ n) : betaFree n ⁻¹' kozProj n = kozProj n := by
  have hi := betaFree_involutive (n := n) (by omega)
  rw [← congrFun (Set.image_eq_preimage_of_inverse hi hi) (kozProj n), betaFree_image_kozProj hn]

theorem isCompact_kozProj (hn : 1 ≤ n) : IsCompact (kozProj n) := by
  rw [kozProj_eq hn, cornerSimplex]
  refine IsCompact.image ?_ (LinearMap.continuous_on_pi (Matrix.toLin' (vdiff n)))
  exact ((Set.finite_range _).insert 0).isCompact_convexHull ℝ

theorem measurableSet_kozProj (hn : 1 ≤ n) : MeasurableSet (kozProj n) :=
  (isCompact_kozProj hn).isClosed.measurableSet

/-- Lebesgue measure restricted to `kozProj n` is `β̄`-invariant. -/
theorem map_betaFree_restrict (hn : 3 ≤ n) :
    (volume.restrict (kozProj n)).map (betaFree n) = volume.restrict (kozProj n) := by
  have h := (measurePreserving_betaFree (n := n) (by omega)).restrict_preimage_emb
    (betaFreeEquiv (n := n) (by omega)).measurableEmbedding (kozProj n)
  rw [betaFree_preimage_kozProj hn] at h
  exact h.map_eq

/-! ## The uniform measure on `Koz(n)` and its `β`-invariance -/

/-- The uniform (Lebesgue) measure on `Koz(n) ⊆ ℝ^{n+1}`, unnormalised: Lebesgue measure of
`ℝ^{n−1}` restricted to the projected simplex, pushed into the plane `{x₀ = 1, x₁ = n}` by
`lift`. Its total mass is `vol(kozProj n) = ∏_{k=2}^n C(n,k)/(n−1)!` (`kozMeasure_univ`). -/
noncomputable def kozMeasure (n : ℕ) : Measure (Fin (n + 1) → ℝ) :=
  (volume.restrict (kozProj n)).map (lift n)

theorem kozMeasure_univ (hn : 1 ≤ n) :
    kozMeasure n Set.univ =
      ENNReal.ofReal ((∏ k ∈ Icc 2 n, (n.choose k : ℝ)) / (n - 1).factorial) := by
  rw [kozMeasure, Measure.map_apply continuous_lift.measurable MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply_univ, volume_kozProj_eq hn]

/-- `kozMeasure n` is concentrated on `Koz(n)`. -/
theorem ae_kozMeasure_mem (hn : 1 ≤ n) :
    ∀ᵐ x ∂kozMeasure n, x ∈ convexHull ℝ (skelSet n) := by
  rw [kozMeasure, (measurableEmbedding_lift hn).ae_map_iff]
  refine (ae_restrict_iff' (measurableSet_kozProj hn)).mpr (Filter.Eventually.of_forall ?_)
  rintro _ ⟨x, hx, rfl⟩
  rw [← coe_proj, lift_proj hn (convexHull_skelSet_subset_plane hn hx)]
  exact hx

/-- **`thm-beta-continuous`, invariance**: the uniform measure on `Koz(n)` is `β`-invariant. -/
theorem kozMeasure_map_beta (hn : 3 ≤ n) : (kozMeasure n).map (beta n) = kozMeasure n := by
  have hβ : Measurable (beta n) := (beta n).continuous_of_finiteDimensional.measurable
  rw [kozMeasure, Measure.map_map hβ continuous_lift.measurable]
  have : ⇑(beta n) ∘ ⇑(lift n) = ⇑(lift n) ∘ ⇑(betaFree n) := funext (beta_lift (by omega))
  rw [this, ← Measure.map_map continuous_lift.measurable
    (betaFree n).continuous_of_finiteDimensional.measurable, map_betaFree_restrict hn]

/-- `β` as a measurable equivalence of `ℝ^{n+1}`. -/
noncomputable def betaMeas (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ (Fin (n + 1) → ℝ) where
  toEquiv := Function.Involutive.toPerm _ beta_involutive
  measurable_toFun := (beta n).continuous_of_finiteDimensional.measurable
  measurable_invFun := (beta n).continuous_of_finiteDimensional.measurable

/-- Integral form of the invariance, for every integrand (so in particular the second moments
and the covariance matrix are `β`-invariant). -/
theorem integral_kozMeasure_comp_beta (hn : 3 ≤ n) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (F : (Fin (n + 1) → ℝ) → E) :
    ∫ x, F (beta n x) ∂kozMeasure n = ∫ x, F x ∂kozMeasure n := by
  conv_rhs => rw [← kozMeasure_map_beta hn]
  exact ((betaMeas n).measurableEmbedding.integral_map F).symm

theorem continuous_muOf (k : ℕ) : Continuous fun x : Fin (n + 1) → ℝ => muOf n x k := by
  unfold muOf
  split_ifs <;> fun_prop

theorem integrable_muOf (hn : 1 ≤ n) (k : ℕ) :
    Integrable (fun x => muOf n x k) (kozMeasure n) := by
  rw [kozMeasure, (measurableEmbedding_lift hn).integrable_map_iff]
  exact ((continuous_muOf k).comp continuous_lift).continuousOn.integrableOn_compact
    (isCompact_kozProj hn)

theorem isFiniteMeasure_kozMeasure (hn : 1 ≤ n) : IsFiniteMeasure (kozMeasure n) := by
  rw [kozMeasure]
  have : IsFiniteMeasure (volume.restrict (kozProj n)) :=
    isFiniteMeasure_restrict.mpr (isCompact_kozProj hn).measure_lt_top.ne
  infer_instance

/-- **`thm-beta-continuous`, centroid identity** (summed form): for `n ≥ 3` and
`1 ≤ k ≤ n − 1`, `∫ (μ_k + μ_{n−k}) = ∫ (1 + μ_{n−1})` over the uniform measure on `Koz(n)`. -/
theorem integral_mu_add_mu_reflect (hn : 3 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    ∫ x, (muOf n x k + muOf n x (n - k)) ∂kozMeasure n =
      ∫ x, (1 + muOf n x (n - 1)) ∂kozMeasure n := by
  by_cases hmid : 2 ≤ k ∧ k ≤ n - 2
  · have hre : ∫ x, muOf n x (n - k) ∂kozMeasure n =
        ∫ x, muOf n (beta n x) (n - k) ∂kozMeasure n :=
      (integral_kozMeasure_comp_beta hn (fun x => muOf n x (n - k))).symm
    have hpt : ∀ x, muOf n (beta n x) (n - k) = 1 + muOf n x (n - 1) - muOf n x k := by
      intro x
      rw [muOf_beta x (by omega) (by omega), show n - (n - k) = k by omega]
    simp_rw [hpt] at hre
    have := isFiniteMeasure_kozMeasure (n := n) (by omega)
    have i1 := integrable_muOf (n := n) (by omega) k
    have i2 := integrable_muOf (n := n) (by omega) (n - k)
    have i3 := integrable_muOf (n := n) (by omega) (n - 1)
    have i0 : Integrable (fun _ : Fin (n + 1) → ℝ => (1 : ℝ)) (kozMeasure n) :=
      integrable_const 1
    rw [integral_add i1 i2, hre,
      integral_sub (f := fun x => 1 + muOf n x (n - 1)) (i0.add i3) i1,
      integral_add (f := fun _ => (1 : ℝ)) i0 i3]
    ring
  · refine integral_congr_ae ((ae_kozMeasure_mem (by omega)).mono fun x hx => ?_)
    have h1 := muOf_one_of_mem_koz (by omega) hx
    rcases (by omega : k = 1 ∨ k = n - 1) with rfl | rfl
    · simp only [h1]
    · simp only [show n - (n - 1) = 1 by omega, h1, add_comm]

/-- **`thm-beta-continuous`, centroid identity** (averaged form): with `V = ∏_{k=2}^n C(n,k)/(n−1)!`
the total mass, the centroid `c` (`μ_k(c) = (1/V) ∫ μ_k`) satisfies
`μ_k(c) + μ_{n−k}(c) = 1 + μ_{n−1}(c)` for `1 ≤ k ≤ n − 1`. -/
theorem centroid_identity (hn : 3 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    let V : ℝ := (∏ j ∈ Icc 2 n, (n.choose j : ℝ)) / (n - 1).factorial
    (∫ x, muOf n x k ∂kozMeasure n) / V + (∫ x, muOf n x (n - k) ∂kozMeasure n) / V =
      1 + (∫ x, muOf n x (n - 1) ∂kozMeasure n) / V := by
  intro V
  have hV : 0 < V := by
    refine div_pos (prod_pos fun j hj => ?_) (Nat.cast_pos.mpr (Nat.factorial_pos _))
    rw [mem_Icc] at hj
    exact Nat.cast_pos.mpr (Nat.choose_pos hj.2)
  have h := integral_mu_add_mu_reflect hn hk1 hk2
  have := isFiniteMeasure_kozMeasure (n := n) (by omega)
  have i0 : Integrable (fun _ : Fin (n + 1) → ℝ => (1 : ℝ)) (kozMeasure n) :=
    integrable_const 1
  have i1 := integrable_muOf (n := n) (by omega) k
  have i2 := integrable_muOf (n := n) (by omega) (n - k)
  have i3 := integrable_muOf (n := n) (by omega) (n - 1)
  rw [integral_add i1 i2, integral_add (f := fun _ => (1 : ℝ)) i0 i3, integral_const,
    smul_eq_mul, mul_one, measureReal_def, kozMeasure_univ (by omega),
    ENNReal.toReal_ofReal hV.le] at h
  rw [← add_div, h, add_div, div_self hV.ne']

end BetaMeasure
end ExteriorConvex
