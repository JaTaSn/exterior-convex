/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Centroids: the simplex `Koz(n)`, independent sums, the product regime, equal shifts

Formalisation of `prop-centroid-simplex` and `prop-pushforward` of
`article/exterior-convex_article3_draft_4.org` (section `sec-centroid`); roadmap item 12 of
`working-notes/lean-roadmap-article3-2026-10-21.org`. Means and covariances are `Covariance.mean`,
`Covariance.cov` (normalised by the mass), `meanF`, `covF` (uniform on a `Finset`).
Coordinates are the library's degree-0-inclusive `f`-coordinates.

**Generic layer.** `mean_map_affine`, `cov_map_affine`: `c(A_*ν) = A c(ν)`,
`Σ(A_*ν) = M Σ(ν) Mᵀ` for affine `A : ℝ^d → ℝ^e`; `mean_smul_measure`, `cov_smul_measure`.
`mean_corner`: the corner simplex `conv{0, e₀, …, e_{m−1}}` has centroid `(1/(m+1), …)`
(permutation symmetry + `∫(1 − ∑y) = 1/(m+1)!` by slicing one dimension up);
`mean_map_corner`: **centroid of a simplex = vertex average**, for any affine image.

**`prop-centroid-simplex`** (`n ≥ 1`; the paper does not state a bound):
* `mean_kozMeasure`: `c(Koz(n)) = (1/n) ∑_{j=1}^n F̃_j` (via `kozMeasure_eq_smul_map`:
  `kozMeasure` is a multiple of the push-forward of the corner simplex under `lift ∘ vdiff`).
* `muOf_mean_kozMeasure`: `μ_k(c) = (n − k + 1)/n` for `1 ≤ k ≤ n` (for `k = 0`, `μ_0 = 1`).
* `bary_mean_kozMeasure`: `λ_j = μ_j − μ_{j+1} = 1/n`, `1 ≤ j ≤ n` (`μ_{n+1} = 0`).
* `sum_index_bary`: `∑_j j λ_j = ∑_k μ_k` (`AlexanderCore.baryIndex`) for every point;
  `baryIndex_mean_kozMeasure`, `sum_index_bary_mean_kozMeasure`: both are `(n+1)/2` at `c`.

**`prop-pushforward` (1)** — the independent sum is modelled as the push-forward of a product
of probability measures `Measure.pi ν` under `sumShift N d : (x_i) ↦ ∑ shift^{d_i} x_i`:
* `mean_indepSum`, `cov_indepSum` (unshifted core; covariance additivity from `iIndepFun_pi`),
  `mean_indepShiftSum`, `cov_indepShiftSum`: centroid `∑ shift^{d_i} c(ν_i)`, covariance
  `∑ P_i Σ(ν_i) P_iᵀ`, `P_i = toMatrix' shift^{d_i}`.
* `mean_indepSum_koz`, `cov_indepSum_koz`: `ν_i = kozProb n` (`kozMeasure` normalised).
* `meanF_covF_indepSum`: the finite version, uniform measure on `L_1 × ⋯ × L_r`
  (`unifF`, `pi_unifF`: the product of uniform measures is uniform on the product); with
  `L_i = S_n` (`SnF`) or `𝓛_n` this is the independent sum of `c(S_n)`, resp. of lattice points.

**`prop-pushforward` (2)**, stated against explicit hypotheses (the product-regime bridge,
`prop-product-regime`, is not imported):
* `meanF_covF_of_bijOn`: if `sumShift` is a bijection `L_1 × ⋯ × L_r → F`, then `c(F)`, `Σ(F)`
  are the sums of shifted rank-one ones. `meanF_covF_ff`: `F = FF(n; d⃗)` (as a `Finset`),
  hypothesis **only injectivity of `sumShift` on `S_n^r`** (surjectivity is `ff_eq_sumset`);
  this is what Part II Prop. 42 (`|FF| = |S_n|^r`) gives. `meanF_covF_lattice`: lattice points,
  hypothesis `Set.BijOn (sumShift N d) (𝓛_n^r) (conv FF ∩ ℤ^{N+1})`.
* Polytope clause. `IsUniformOn ρ K`: `ρ` is Lebesgue measure transported by an injective affine
  chart `φ : ℝ^D → ℝ^{N+1}` with `K ⊆ range φ` (`kozMeasure_isUniformOn`: `kozMeasure` is one).
  `chart_rigidity`: an affine image of Lebesgue measure on a set with interior is a positive
  multiple of any such chart measure (if that is non-zero). `uniform_eq_smul_indepSum`,
  `mean_cov_uniform_productRegime`: if `sumShift` is **injective on `Koz(n)^r`** (it is always onto
  `Koz(n; d⃗)`, `image_kozProj_pi`), any non-zero uniform measure on `Koz(n; d⃗)` is a multiple of
  the independent-sum law, so its centroid and covariance are the independent-sum ones.

**`prop-pushforward` (3)**: `koz_zero_shifts`: `Koz(n; 0^r) = r·Koz(n)` (Minkowski sum of `r`
copies of a convex set, `sum_const_convex`). `mean_cov_dilate`: the uniform measure on `r·Koz(n)`,
taken as the push-forward of `kozMeasure n` by `x ↦ r x` (`dil`), has centroid `r·c` and covariance
`r²·Σ`; `mean_cov_indepSum_zero`: the independent sum has centroid `r·c`, covariance `r·Σ`.

**Deviations.** (2)'s hypotheses are injectivity/bijectivity of the sumset map rather than
"product regime"; in (2)-polytope, `ρ ≠ 0` is assumed (a chart of the wrong dimension gives the
zero measure). In (3) "uniform measure on `r·Koz(n)`" is the dilation push-forward of `kozMeasure`
(an `IsUniformOn` measure up to a constant, not separately proved). Nothing in the paper was
found wrong.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Symmetry.Covariance
import ExteriorConvex.Symmetry.AlexanderCore
import ExteriorConvex.Spine.Sumset

open Finset MeasureTheory Matrix

namespace ExteriorConvex
namespace Centroids

open Covariance

/-! ## Generic: mean and covariance under affine pushforward and scaling -/

section Generic

variable {d e : ℕ}

theorem affine_apply_eq' (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ)) (x : Fin d → ℝ) (i : Fin e) :
    A x i = ∑ j, LinearMap.toMatrix' A.linear i j * x j + A 0 i := by
  have h := congrFun (congrFun (AffineMap.decomp A) x) i
  rw [h]
  simp only [Pi.add_apply]
  congr 1
  rw [← LinearMap.toMatrix'_mulVec, Matrix.mulVec, dotProduct]

theorem affine_sub_apply' (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ)) (x y : Fin d → ℝ) (i : Fin e) :
    A x i - A y i = ∑ j, LinearMap.toMatrix' A.linear i j * (x j - y j) := by
  rw [affine_apply_eq' A x, affine_apply_eq' A y]
  simp only [mul_sub, sum_sub_distrib]
  ring

variable {ν : Measure (Fin d → ℝ)}

theorem measureReal_univ_map (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ)) :
    (ν.map A).real Set.univ = ν.real Set.univ := by
  rw [measureReal_def, measureReal_def,
    Measure.map_apply A.continuous_of_finiteDimensional.measurable MeasurableSet.univ,
    Set.preimage_univ]

/-- **The centroid commutes with affine maps**: `c(A_*ν) = A(c(ν))` (linearity of expectation). -/
theorem mean_map_affine [IsFiniteMeasure ν] (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ))
    (hν : ν Set.univ ≠ 0) (hint : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν) :
    mean (ν.map A) = A (mean ν) := by
  have hAm : Measurable A := A.continuous_of_finiteDimensional.measurable
  have h0 : ν.real Set.univ ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨hν, measure_ne_top ν _⟩
  funext i
  have hre : ∫ x, x i ∂(ν.map A) = ∫ x, A x i ∂ν :=
    integral_map hAm.aemeasurable (continuous_apply i).aestronglyMeasurable
  have hsum : ∫ x, A x i ∂ν =
      ∑ j, LinearMap.toMatrix' A.linear i j * ∫ x, x j ∂ν + ν.real Set.univ * A 0 i := by
    rw [show (fun x => A x i) = fun x =>
        ∑ j, LinearMap.toMatrix' A.linear i j * x j + A 0 i from
        funext fun x => affine_apply_eq' A x i]
    rw [integral_add (integrable_finsetSum _ fun j _ => (hint j).const_mul _)
      (integrable_const _), integral_finsetSum _ fun j _ => (hint j).const_mul _,
      integral_const, smul_eq_mul]
    simp_rw [integral_const_mul]
  rw [affine_apply_eq' A _ i]
  simp only [mean]
  rw [hre, hsum, measureReal_univ_map, add_div, sum_div, mul_div_cancel_left₀ _ h0]
  simp only [mul_div_assoc]

/-- **Covariance under an affine map**: `Σ(A_*ν) = M Σ(ν) Mᵀ`, `M` the matrix of the linear
part of `A`. -/
theorem cov_map_affine [IsFiniteMeasure ν] (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ))
    (hν : ν Set.univ ≠ 0) (hint : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hint2 : ∀ i j, Integrable (fun x : Fin d → ℝ => x i * x j) ν) :
    cov (ν.map A) =
      LinearMap.toMatrix' A.linear * cov ν * (LinearMap.toMatrix' A.linear)ᵀ := by
  set M := LinearMap.toMatrix' A.linear
  set m := mean ν
  have hAm : Measurable A := A.continuous_of_finiteDimensional.measurable
  have hm : mean (ν.map A) = A m := mean_map_affine A hν hint
  have ig := integrable_centred_mul hint hint2 m
  ext i j
  have hre : ∫ x, (x i - mean (ν.map A) i) * (x j - mean (ν.map A) j) ∂(ν.map A) =
      ∫ x, (A x i - A m i) * (A x j - A m j) ∂ν := by
    rw [hm, integral_map hAm.aemeasurable (by fun_prop)]
  have hpt : ∀ x : Fin d → ℝ, (A x i - A m i) * (A x j - A m j) =
      ∑ a, ∑ b, M i a * M j b * ((x a - m a) * (x b - m b)) := by
    intro x
    rw [affine_sub_apply' A x m i, affine_sub_apply' A x m j, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hint3 : ∫ x, (A x i - A m i) * (A x j - A m j) ∂ν =
      ∑ a, ∑ b, M i a * M j b * ∫ x, (x a - m a) * (x b - m b) ∂ν := by
    simp_rw [hpt]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (ig a b).const_mul _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => (ig a b).const_mul _]
    simp_rw [integral_const_mul]
  simp only [cov, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [hre, hint3, measureReal_univ_map, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-- Mean and covariance are normalised by the mass, so they do not see a positive scalar. -/
theorem mean_smul_measure (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    mean (c • ν) = mean ν := by
  have hc : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩
  funext i
  simp only [mean, integral_smul_measure, smul_eq_mul, measureReal_def, Measure.smul_apply,
    ENNReal.toReal_mul]
  rw [mul_div_mul_left _ _ hc]

theorem cov_smul_measure (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    cov (c • ν) = cov ν := by
  have hc : c.toReal ≠ 0 := ENNReal.toReal_ne_zero.mpr ⟨hc0, hct⟩
  ext i j
  simp only [cov, Matrix.of_apply, mean_smul_measure c hc0 hct, integral_smul_measure,
    smul_eq_mul, measureReal_def, Measure.smul_apply, ENNReal.toReal_mul]
  rw [mul_div_mul_left _ _ hc]

end Generic

/-! ## The centroid of the corner simplex -/

section Corner

open KozVolume

variable {m : ℕ}

theorem isCompact_cornerSimplex (m : ℕ) : IsCompact (cornerSimplex m) :=
  ((Set.finite_range _).insert 0).isCompact_convexHull ℝ

theorem measurableSet_cornerSimplex (m : ℕ) : MeasurableSet (cornerSimplex m) :=
  (isCompact_cornerSimplex m).isClosed.measurableSet

instance (m : ℕ) : IsFiniteMeasure (volume.restrict (cornerSimplex m)) :=
  isFiniteMeasure_restrict.mpr (isCompact_cornerSimplex m).measure_lt_top.ne

theorem integrable_corner_of_continuous {F : (Fin m → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (volume.restrict (cornerSimplex m)) :=
  hF.continuousOn.integrableOn_compact (isCompact_cornerSimplex m)

/-- Permuting coordinates preserves the corner simplex, so all coordinate integrals agree. -/
theorem integral_corner_coord_eq (a b : Fin m) :
    ∫ y, y a ∂(volume.restrict (cornerSimplex m)) =
      ∫ y, y b ∂(volume.restrict (cornerSimplex m)) := by
  set σ := Equiv.swap a b
  let φ := MeasurableEquiv.piCongrLeft (fun _ : Fin m => ℝ) σ
  have hφ : ∀ y : Fin m → ℝ, ∀ i, φ y (σ i) = y i := fun y i =>
    MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin m => ℝ) σ y i
  have hφ' : ∀ y : Fin m → ℝ, ∀ i, φ y i = y (σ i) := by
    intro y i
    have := hφ y (σ i)
    rwa [Equiv.swap_apply_self] at this
  have hpre : φ ⁻¹' cornerSimplex m = cornerSimplex m := by
    ext y
    simp only [Set.mem_preimage, cornerSimplex_eq, lowerSimplex, Set.mem_ofPred_eq, hφ']
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun i => by simpa [σ] using h1 (σ i), ?_⟩
      rwa [Equiv.sum_comp σ (fun i => y i)] at h2
    · rintro ⟨h1, h2⟩
      exact ⟨fun i => h1 _, by rwa [Equiv.sum_comp σ (fun i => y i)]⟩
  have hmp := (volume_measurePreserving_piCongrLeft (fun _ : Fin m => ℝ) σ).restrict_preimage_emb
    φ.measurableEmbedding (cornerSimplex m)
  rw [hpre] at hmp
  have h2 : ∫ y, φ y a ∂(volume.restrict (cornerSimplex m)) =
      ∫ y, y a ∂(volume.restrict (cornerSimplex m)) := hmp.integral_comp' (f := φ) (fun y => y a)
  have h3 : ∀ y, φ y a = y b := fun y => by rw [hφ']; simp [σ]
  simp only [h3] at h2
  exact h2.symm

/-- `∫_{corner simplex of ℝ^m} (1 − ∑ y) dy = 1/(m+1)!` (the volume of the corner simplex one
dimension up, sliced over its last `m` coordinates). -/
theorem integral_corner_one_sub_sum (m : ℕ) :
    ∫ y, (1 - ∑ i, y i) ∂(volume.restrict (cornerSimplex m)) = 1 / (m + 1).factorial := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
  let S : Set (ℝ × (Fin m → ℝ)) := {p | 0 ≤ p.1 ∧ p.2 ∈ lowerSimplex m (1 - p.1)}
  have hS : MeasurableSet S := by
    have : S = {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1} ∩
        ((⋂ i, {p : ℝ × (Fin m → ℝ) | 0 ≤ p.2 i}) ∩ {p | ∑ i, p.2 i + p.1 ≤ 1}) := by
      ext p
      simp only [S, lowerSimplex, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by linarith⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨h1, h2, by linarith⟩
    rw [this]
    refine (measurableSet_le measurable_const measurable_fst).inter
      ((MeasurableSet.iInter fun i => measurableSet_le (f := fun _ => (0 : ℝ))
        (g := fun p : ℝ × (Fin m → ℝ) => p.2 i) measurable_const (by fun_prop)).inter
        (measurableSet_le (f := fun p : ℝ × (Fin m → ℝ) => ∑ i, p.2 i + p.1)
          (g := fun _ => 1) (by fun_prop) measurable_const))
  have hpre : lowerSimplex (m + 1) 1 = e ⁻¹' S := by
    ext x
    simp only [lowerSimplex, Set.mem_ofPred_eq, Set.mem_preimage, S, e,
      MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
      Fin.removeNth, Fin.succAbove_zero, Fin.sum_univ_succ, Fin.forall_fin_succ]
    constructor
    · rintro ⟨⟨h0, h1⟩, h2⟩; exact ⟨h0, h1, by linarith⟩
    · rintro ⟨h0, h1, h2⟩; exact ⟨⟨h0, h1⟩, by linarith⟩
  have hvol := volume_lowerSimplex (m + 1) 1
  rw [hpre, hmp.measure_preimage hS.nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_apply_symm hS] at hvol
  have hfib : ∀ y : Fin m → ℝ, volume ((fun t : ℝ => (t, y)) ⁻¹' S) =
      (cornerSimplex m).indicator (fun y => ENNReal.ofReal (1 - ∑ i, y i)) y := by
    intro y
    by_cases hy : ∀ i, 0 ≤ y i
    · have : (fun t : ℝ => (t, y)) ⁻¹' S = Set.Icc 0 (1 - ∑ i, y i) := by
        ext t
        simp only [S, lowerSimplex, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_Icc]
        constructor
        · rintro ⟨h1, -, h3⟩; exact ⟨h1, by linarith⟩
        · rintro ⟨h1, h3⟩; exact ⟨h1, hy, by linarith⟩
      rw [this, Real.volume_Icc, sub_zero]
      by_cases hs : ∑ i, y i ≤ 1
      · rw [Set.indicator_of_mem (by rw [cornerSimplex_eq]; exact ⟨hy, hs⟩)]
      · rw [Set.indicator_of_notMem (by rw [cornerSimplex_eq]; exact fun h => hs h.2),
          ENNReal.ofReal_of_nonpos (by linarith)]
    · have : (fun t : ℝ => (t, y)) ⁻¹' S = ∅ := by
        ext t
        simp only [S, lowerSimplex, Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
          iff_false, not_and]
        exact fun _ h _ => hy h
      rw [this, measure_empty, Set.indicator_of_notMem
        (by rw [cornerSimplex_eq]; exact fun h => hy h.1)]
  simp_rw [hfib] at hvol
  have hnn : 0 ≤ᵐ[volume.restrict (cornerSimplex m)] fun y : Fin m → ℝ => 1 - ∑ i, y i := by
    refine (ae_restrict_iff' (measurableSet_cornerSimplex m)).mpr
      (Filter.Eventually.of_forall fun y hy => ?_)
    rw [cornerSimplex_eq] at hy
    simp only [Pi.zero_apply, sub_nonneg]
    exact hy.2
  rw [lintegral_indicator (measurableSet_cornerSimplex m),
    ← ofReal_integral_eq_lintegral_ofReal (integrable_corner_of_continuous (by fun_prop)) hnn]
    at hvol
  simp only [zero_le_one, ↓reduceIte, one_pow] at hvol
  exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg_of_ae hnn) (by positivity)).mp hvol

theorem measureReal_corner (m : ℕ) :
    (volume.restrict (cornerSimplex m)).real Set.univ = 1 / m.factorial := by
  rw [measureReal_restrict_apply_univ, measureReal_def, volume_cornerSimplex,
    ENNReal.toReal_ofReal (by positivity)]

theorem corner_univ_ne_zero (m : ℕ) : volume.restrict (cornerSimplex m) Set.univ ≠ 0 := by
  rw [Measure.restrict_apply_univ, volume_cornerSimplex, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  positivity

/-- Each coordinate integrates to `1/(m+1)!` over the corner simplex of `ℝ^m`. -/
theorem integral_corner_coord (a : Fin m) :
    ∫ y, y a ∂(volume.restrict (cornerSimplex m)) = 1 / (m + 1).factorial := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fin.pos a).ne'
  have h1 := integral_corner_one_sub_sum m
  rw [integral_sub (integrable_const _)
      (integrable_finsetSum _ fun i _ => integrable_corner_of_continuous (continuous_apply i)),
    integral_finsetSum _ fun i _ => integrable_corner_of_continuous (continuous_apply i),
    integral_const, smul_eq_mul, mul_one, measureReal_corner] at h1
  simp_rw [integral_corner_coord_eq _ a] at h1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.factorial_succ,
    Nat.cast_mul] at h1
  rw [Nat.factorial_succ, Nat.cast_mul]
  have hf : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
  field_simp at h1 ⊢
  push_cast at h1 ⊢
  apply mul_left_cancel₀ hm
  linear_combination (-1 : ℝ) * h1

/-- **The centroid of the corner simplex** `conv{0, e₀, …, e_{m−1}}` is `(1/(m+1), …, 1/(m+1))`. -/
theorem mean_corner (m : ℕ) :
    mean (volume.restrict (cornerSimplex m)) = fun _ => 1 / ((m : ℝ) + 1) := by
  funext a
  rw [mean, integral_corner_coord, measureReal_corner, Nat.factorial_succ, Nat.cast_mul]
  have hf : (m.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_pos m).ne'
  push_cast
  field_simp

/-- **The centroid of a simplex is the average of its vertices**: for any affine map `A`, the
uniform measure on `A(corner simplex)` (the pushforward) has centroid
`(A 0 + ∑_b A e_b)/(m+1)`. (`A` need not be injective; if it is, this is the uniform measure on
the simplex `conv{A 0, A e₀, …}` up to a constant.) -/
theorem mean_map_corner {e : ℕ} (A : (Fin m → ℝ) →ᵃ[ℝ] (Fin e → ℝ)) :
    mean ((volume.restrict (cornerSimplex m)).map A) =
      (1 / ((m : ℝ) + 1)) • (A 0 + ∑ b, A (Pi.single b 1)) := by
  rw [mean_map_affine A (corner_univ_ne_zero m)
    (fun i => integrable_corner_of_continuous (continuous_apply i)), mean_corner]
  have hc : (fun _ : Fin m => 1 / ((m : ℝ) + 1)) =
      ∑ b, (1 / ((m : ℝ) + 1)) • (Pi.single b (1 : ℝ) -ᵥ (0 : Fin m → ℝ)) := by
    rw [← Finset.smul_sum]
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have hA : ∀ x : Fin m → ℝ, A x = A.linear (x -ᵥ 0) + A 0 := by
    intro x
    rw [AffineMap.linearMap_vsub, vsub_eq_sub, sub_add_cancel]
  rw [hA, vsub_eq_sub, sub_zero, hc, map_sum]
  simp_rw [map_smul, AffineMap.linearMap_vsub, vsub_eq_sub]
  have hm1 : (m : ℝ) + 1 ≠ 0 := by positivity
  funext i
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply,
    ← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

end Corner

/-! ## `prop-centroid-simplex` -/

section KozCentroid

open KozVolume BetaMeasure AlexanderCore

variable {n : ℕ}

theorem vdiff_det_ne_zero' : LinearMap.det (Matrix.toLin' (vdiff n)) ≠ 0 := by
  rw [LinearMap.det_toLin']; exact vdiff_det_ne_zero

/-- `kozMeasure n` is a positive multiple of the pushforward of Lebesgue measure on the corner
simplex under the affine map `lift ∘ vdiff`, which sends `0 ↦ F̃_1`, `e_b ↦ F̃_{b+2}`. -/
theorem kozMeasure_eq_smul_map (hn : 1 ≤ n) :
    kozMeasure n = ENNReal.ofReal |LinearMap.det (Matrix.toLin' (vdiff n))| •
      (volume.restrict (cornerSimplex (n - 1))).map
        ((lift n).comp (Matrix.toLin' (vdiff n)).toAffineMap) := by
  set L := Matrix.toLin' (vdiff n)
  have hdet : LinearMap.det L ≠ 0 := vdiff_det_ne_zero'
  let Le := (LinearMap.equivOfDetNeZero L hdet).toContinuousLinearEquiv
  have hLe : ⇑Le = ⇑L := rfl
  have hemb : MeasurableEmbedding L := hLe ▸ Le.toHomeomorph.measurableEmbedding
  have hinj : Function.Injective L := hLe ▸ Le.injective
  have h1 := hemb.restrict_map volume (L '' cornerSimplex (n - 1))
  rw [Set.preimage_image_eq _ hinj, Measure.map_linearMap_addHaar_eq_smul_addHaar volume hdet,
    Measure.restrict_smul] at h1
  have h2 : volume.restrict (L '' cornerSimplex (n - 1)) =
      ENNReal.ofReal |LinearMap.det L| • (volume.restrict (cornerSimplex (n - 1))).map L := by
    rw [← h1, smul_smul, ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul,
      mul_inv_cancel₀ hdet, abs_one, ENNReal.ofReal_one, one_smul]
  rw [kozMeasure, kozProj_eq hn, h2, Measure.map_smul _ continuous_lift.aemeasurable, Measure.map_map continuous_lift.measurable
    L.continuous_of_finiteDimensional.measurable]
  rfl

theorem lift_zero (hn : 1 ≤ n) : lift n 0 = skel n 1 := by
  rw [← freeProj_skel_one, ← coe_proj, lift_proj hn (skel_mem_plane hn le_rfl)]

theorem lift_vdiff_single (hn : 1 ≤ n) (b : Fin (n - 1)) :
    lift n (Matrix.toLin' (vdiff n) (Pi.single b 1)) = skel n (b.val + 2) := by
  rw [Matrix.toLin'_apply, Matrix.mulVec_single_one, ← freeProj_skel_col, ← coe_proj,
    lift_proj hn (skel_mem_plane hn (by omega))]

theorem sum_skel_eq (hn : 1 ≤ n) {M : Type*} [AddCommMonoid M] (g : ℕ → M) :
    g 1 + ∑ b : Fin (n - 1), g (b.val + 2) = ∑ j ∈ Icc 1 n, g j := by
  have hs : Icc 1 n = insert 1 (Icc 2 n) := by
    ext j; simp only [mem_Icc, mem_insert]; omega
  rw [hs, sum_insert (by simp), Fin.sum_univ_eq_sum_range (fun b => g (b + 2))]
  congr 1
  refine sum_nbij' (· + 2) (· - 2) (fun i hi => ?_) (fun j hj => ?_) (fun i hi => ?_)
    (fun j hj => ?_) (fun _ _ => rfl)
  all_goals simp only [mem_range, mem_Icc] at *; omega

/-- **`prop-centroid-simplex`, vertex-average form**: the centroid of the uniform measure on
`Koz(n)` is `(1/n) ∑_{j=1}^n F̃_j`. -/
theorem mean_kozMeasure (hn : 1 ≤ n) :
    mean (kozMeasure n) = (1 / (n : ℝ)) • ∑ j ∈ Icc 1 n, skel n j := by
  have hc : ENNReal.ofReal |LinearMap.det (Matrix.toLin' (vdiff n))| ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact abs_pos.mpr vdiff_det_ne_zero'
  rw [kozMeasure_eq_smul_map hn, mean_smul_measure _ hc ENNReal.ofReal_ne_top, mean_map_corner]
  simp only [AffineMap.comp_apply, LinearMap.coe_toAffineMap, map_zero, lift_zero hn,
    lift_vdiff_single hn]
  rw [sum_skel_eq hn (skel n), Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]

/-- Coordinate `k ≥ 1` of `∑_{j=1}^n F̃_j` is `(n − k + 1)·C(n,k)`. -/
theorem sum_skel_apply {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) :
    (∑ j ∈ Icc 1 n, skel n j) ⟨k, by omega⟩ = ((n : ℝ) - k + 1) * n.choose k := by
  rw [Finset.sum_apply]
  simp only [skel, show k ≠ 0 by omega, ↓reduceIte]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  congr 1
  have : (Icc 1 n).filter (fun j => k ≤ j) = Icc k n := by
    ext j; simp only [mem_filter, mem_Icc]; omega
  rw [this, Nat.card_Icc, Nat.cast_sub (by omega)]
  push_cast; ring

/-- **`prop-centroid-simplex`, LYM coordinates**: the centroid `c` of `Koz(n)` has
`μ_k(c) = (n − k + 1)/n` for `1 ≤ k ≤ n`. -/
theorem muOf_mean_kozMeasure (hn : 1 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk : k ≤ n) :
    muOf n (mean (kozMeasure n)) k = ((n : ℝ) - k + 1) / n := by
  rw [muOf_of_le hk, mean_kozMeasure hn, Pi.smul_apply, sum_skel_apply hk1 hk, smul_eq_mul]
  have hC : (n.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos hk).ne'
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **`prop-centroid-simplex`, barycentric coordinates**: `λ_j = μ_j − μ_{j+1} = 1/n` for every
`1 ≤ j ≤ n` (with `μ_{n+1} = 0`). -/
theorem bary_mean_kozMeasure (hn : 1 ≤ n) {j : ℕ} (hj1 : 1 ≤ j) (hj : j ≤ n) :
    muOf n (mean (kozMeasure n)) j - muOf n (mean (kozMeasure n)) (j + 1) = 1 / n := by
  rw [muOf_mean_kozMeasure hn hj1 hj]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rcases Nat.lt_or_ge j n with h | h
  · rw [muOf_mean_kozMeasure hn (by omega) h]
    push_cast; field_simp; ring
  · rw [muOf_of_gt (by omega), show j = n by omega]
    field_simp; ring

/-- Abel summation for the mean vertex index: `∑_{j=1}^N j (g_j − g_{j+1}) = ∑_{k=1}^N g_k − N g_{N+1}`. -/
theorem sum_mul_sub_succ (g : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ Icc 1 N, (j : ℝ) * (g j - g (j + 1)) = ∑ k ∈ Icc 1 N, g k - N * g (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), ih]
    push_cast; ring

/-- For every point, the mean vertex index `∑_j j λ_j` (`λ_j = μ_j − μ_{j+1}`) is
`∑_k μ_k = baryIndex`. -/
theorem sum_index_bary (x : Fin (n + 1) → ℝ) :
    ∑ j ∈ Icc 1 n, (j : ℝ) * (muOf n x j - muOf n x (j + 1)) = baryIndex n x := by
  rw [sum_mul_sub_succ, muOf_of_gt (by omega), mul_zero, sub_zero, baryIndex]

theorem sum_Icc_id (N : ℕ) : ∑ k ∈ Icc 1 N, (k : ℝ) = N * (N + 1) / 2 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_Icc_succ_top (by omega), ih]; push_cast; ring

/-- **`prop-centroid-simplex`, mean vertex index**: `∑_k μ_k(c) = (n+1)/2`. -/
theorem baryIndex_mean_kozMeasure (hn : 1 ≤ n) :
    baryIndex n (mean (kozMeasure n)) = ((n : ℝ) + 1) / 2 := by
  rw [baryIndex, Finset.sum_congr rfl fun k hk => muOf_mean_kozMeasure hn (mem_Icc.mp hk).1
    (mem_Icc.mp hk).2]
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simp_rw [sub_add_eq_add_sub, sub_div]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Icc, ← Finset.sum_div, sum_Icc_id]
  simp only [add_tsub_cancel_right, nsmul_eq_mul]
  field_simp
  ring

/-- `prop-centroid-simplex`, the same in the form `∑_j j λ_j = (n+1)/2`. -/
theorem sum_index_bary_mean_kozMeasure (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, (j : ℝ) * (muOf n (mean (kozMeasure n)) j -
      muOf n (mean (kozMeasure n)) (j + 1)) = ((n : ℝ) + 1) / 2 := by
  rw [sum_index_bary, baryIndex_mean_kozMeasure hn]

end KozCentroid

/-! ## `prop-pushforward` (1): independent sums -/

section IndepSum

open ProbabilityTheory

variable {D r : ℕ}

theorem measureReal_univ_map_of_measurable {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → (Fin D → ℝ)} (hf : Measurable f) : (μ.map f).real Set.univ = μ.real Set.univ := by
  rw [measureReal_def, measureReal_def, Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ]

/-- For a probability measure the centroid is the vector of coordinate integrals. -/
theorem mean_of_prob (ν : Measure (Fin D → ℝ)) [IsProbabilityMeasure ν] :
    mean ν = fun a => ∫ x, x a ∂ν := by
  funext a; rw [mean, probReal_univ, div_one]

theorem cov_of_prob (ν : Measure (Fin D → ℝ)) [IsProbabilityMeasure ν] :
    cov ν = Matrix.of fun a b => ∫ x, (x a - mean ν a) * (x b - mean ν b) ∂ν := by
  ext a b; simp only [cov, Matrix.of_apply, probReal_univ, div_one]

/-- The sum map `(x_1, …, x_r) ↦ ∑ x_i` on `(ℝ^D)^r`. -/
noncomputable def sumMap (D r : ℕ) : (Fin r → Fin D → ℝ) →ₗ[ℝ] (Fin D → ℝ) :=
  ∑ i, LinearMap.proj i

theorem sumMap_apply (x : Fin r → Fin D → ℝ) : sumMap D r x = ∑ i, x i := by
  simp [sumMap, LinearMap.sum_apply]

theorem measurable_sumMap : Measurable (sumMap D r) :=
  (sumMap D r).continuous_of_finiteDimensional.measurable

variable (ρ : Fin r → Measure (Fin D → ℝ)) [∀ i, IsProbabilityMeasure (ρ i)]

instance : IsProbabilityMeasure ((Measure.pi ρ).map (sumMap D r)) :=
  ⟨by rw [Measure.map_apply measurable_sumMap MeasurableSet.univ, Set.preimage_univ,
    measure_univ]⟩

theorem integral_comp_eval_pi (i : Fin r) {g : (Fin D → ℝ) → ℝ} (hg : Continuous g) :
    ∫ x, g (x i) ∂Measure.pi ρ = ∫ y, g y ∂ρ i := by
  have h := (measurePreserving_eval ρ i).map_eq
  conv_rhs => rw [← h]
  rw [integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable]

theorem integrable_comp_eval_pi (i : Fin r) {g : (Fin D → ℝ) → ℝ} (hg : Integrable g (ρ i)) :
    Integrable (fun x => g (x i)) (Measure.pi ρ) :=
  (measurePreserving_eval ρ i).integrable_comp_of_integrable hg

/-- **`prop-pushforward` (1), centroid, unshifted core**: the centroid of the law of a sum of
independent random vectors is the sum of their centroids. -/
theorem mean_indepSum (hint : ∀ i a, Integrable (fun x : Fin D → ℝ => x a) (ρ i)) :
    mean ((Measure.pi ρ).map (sumMap D r)) = ∑ i, mean (ρ i) := by
  rw [mean_of_prob]
  funext a
  rw [integral_map measurable_sumMap.aemeasurable (continuous_apply a).aestronglyMeasurable]
  simp_rw [sumMap_apply, Finset.sum_apply]
  rw [integral_finsetSum _ fun i _ => integrable_comp_eval_pi ρ i (hint i a)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_comp_eval_pi ρ i (continuous_apply a), mean_of_prob]

/-- **`prop-pushforward` (1), covariance, unshifted core**: by independence (`Measure.pi`), the
covariance of a sum of independent random vectors is the sum of their covariances. -/
theorem cov_indepSum (hint : ∀ i a, Integrable (fun x : Fin D → ℝ => x a) (ρ i))
    (hint2 : ∀ i a b, Integrable (fun x : Fin D → ℝ => x a * x b) (ρ i)) :
    cov ((Measure.pi ρ).map (sumMap D r)) = ∑ i, cov (ρ i) := by
  rw [cov_of_prob, mean_indepSum ρ hint]
  ext a b
  set c := fun i => mean (ρ i)
  let u : Fin r → Fin D → (Fin D → ℝ) → ℝ := fun i a y => y a - c i a
  have hu : ∀ i a, Continuous (u i a) := fun i a => (continuous_apply a).sub continuous_const
  have huint : ∀ i a, Integrable (u i a) (ρ i) := fun i a => (hint i a).sub (integrable_const _)
  have hu0 : ∀ i a, ∫ y, u i a y ∂ρ i = 0 := by
    intro i a
    rw [integral_sub (hint i a) (integrable_const _), integral_const, probReal_univ, one_smul]
    simp only [c, mean_of_prob, sub_self]
  have hind : iIndepFun (fun i (x : Fin r → Fin D → ℝ) => x i) (Measure.pi ρ) :=
    iIndepFun_pi (X := fun _ => id) fun _ => aemeasurable_id
  have hpair : ∀ i j a b, Integrable (fun x : Fin r → Fin D → ℝ => u i a (x i) * u j b (x j))
      (Measure.pi ρ) := by
    intro i j a b
    by_cases hij : i = j
    · subst hij
      exact integrable_comp_eval_pi ρ i (g := fun y => u i a y * u i b y)
        (integrable_centred_mul (hint i) (hint2 i) (c i) a b)
    · have hI : IndepFun (fun x : Fin r → Fin D → ℝ => u i a (x i))
          (fun x => u j b (x j)) (Measure.pi ρ) :=
        (hind.indepFun hij).comp (hu i a).measurable (hu j b).measurable
      exact hI.integrable_mul (integrable_comp_eval_pi ρ i (huint i a))
        (integrable_comp_eval_pi ρ j (huint j b))
  have hterm : ∀ i j, ∫ x, u i a (x i) * u j b (x j) ∂Measure.pi ρ =
      if i = j then ∫ y, u i a y * u i b y ∂ρ i else 0 := by
    intro i j
    split_ifs with hij
    · subst hij
      exact integral_comp_eval_pi ρ i ((hu i a).mul (hu i b))
    · have hI : IndepFun (fun x : Fin r → Fin D → ℝ => u i a (x i))
          (fun x => u j b (x j)) (Measure.pi ρ) :=
        (hind.indepFun hij).comp (hu i a).measurable (hu j b).measurable
      have := hI.integral_mul_eq_mul_integral
        ((hu i a).comp (continuous_apply i)).aestronglyMeasurable
        ((hu j b).comp (continuous_apply j)).aestronglyMeasurable
      simp only [Pi.mul_apply] at this
      rw [this, integral_comp_eval_pi ρ i (hu i a), hu0, zero_mul]
  simp only [Matrix.of_apply]
  rw [integral_map measurable_sumMap.aemeasurable (by fun_prop)]
  have hpt : ∀ x : Fin r → Fin D → ℝ, (sumMap D r x a - (∑ i, c i) a) *
      (sumMap D r x b - (∑ i, c i) b) = ∑ i, ∑ j, u i a (x i) * u j b (x j) := by
    intro x
    simp only [sumMap_apply, Finset.sum_apply]
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_mul_sum]
  simp_rw [hpt]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hpair i j a b,
    Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hpair i j a b]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, cov_of_prob, Matrix.of_apply]
  rfl

end IndepSum

/-! ## Shifted independent sums, the uniform probability measures, and the discrete case -/

section Shifted

open ProbabilityTheory

variable {n N r : ℕ}

/-- The sumset map `(x_1, …, x_r) ↦ ∑_i shift^{d_i} x_i`, `(ℝ^{n+1})^r → ℝ^{N+1}`. -/
noncomputable def sumShift (N : ℕ) (d : Fin r → ℕ) : (Fin r → Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ) :=
  ∑ i, (shiftIncl N (d i)).comp (LinearMap.proj i)

theorem sumShift_apply (d : Fin r → ℕ) (x : Fin r → Fin (n + 1) → ℝ) :
    sumShift N d x = ∑ i, shiftIncl N (d i) (x i) := by
  simp [sumShift, LinearMap.sum_apply]

theorem measurable_sumShift (d : Fin r → ℕ) : Measurable (sumShift (n := n) N d) :=
  (sumShift N d).continuous_of_finiteDimensional.measurable

/-- Integrability of coordinates passes to an affine pushforward. -/
theorem integrable_map_affine_coord {d e : ℕ} {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν]
    (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ))
    (hint : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν) (a : Fin e) :
    Integrable (fun z : Fin e → ℝ => z a) (ν.map A) := by
  rw [integrable_map_measure (continuous_apply a).aestronglyMeasurable
    A.continuous_of_finiteDimensional.measurable.aemeasurable]
  have : (fun z : Fin e → ℝ => z a) ∘ ⇑A = fun y =>
      ∑ j, LinearMap.toMatrix' A.linear a j * y j + A 0 a :=
    funext fun y => affine_apply_eq' A y a
  rw [this]
  exact (integrable_finsetSum _ fun j _ => (hint j).const_mul _).add (integrable_const _)

/-- Integrability of products of coordinates passes to an affine pushforward. -/
theorem integrable_map_affine_mul {d e : ℕ} {ν : Measure (Fin d → ℝ)} [IsFiniteMeasure ν]
    (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin e → ℝ))
    (hint : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hint2 : ∀ i j, Integrable (fun x : Fin d → ℝ => x i * x j) ν) (a b : Fin e) :
    Integrable (fun z : Fin e → ℝ => z a * z b) (ν.map A) := by
  rw [integrable_map_measure (by fun_prop : Continuous fun z : Fin e → ℝ => z a * z b).aestronglyMeasurable
    A.continuous_of_finiteDimensional.measurable.aemeasurable]
  have key : Integrable (fun y : Fin d → ℝ =>
      ∑ k, ∑ l, LinearMap.toMatrix' A.linear a k * LinearMap.toMatrix' A.linear b l * (y k * y l) +
        A 0 b * (∑ k, LinearMap.toMatrix' A.linear a k * y k) +
        A 0 a * (∑ l, LinearMap.toMatrix' A.linear b l * y l) + A 0 a * A 0 b) ν :=
    (((integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
      (hint2 k l).const_mul _).add ((integrable_finsetSum _ fun k _ =>
        (hint k).const_mul _).const_mul _)).add ((integrable_finsetSum _ fun l _ =>
        (hint l).const_mul _).const_mul _)).add (integrable_const _)
  refine key.congr (ae_of_all _ fun y => ?_)
  simp only [Function.comp_apply]
  rw [affine_apply_eq' A y a, affine_apply_eq' A y b, add_mul, mul_add, mul_add,
    Finset.sum_mul_sum]
  have h4 : ∀ k l, LinearMap.toMatrix' A.linear a k * y k * (LinearMap.toMatrix' A.linear b l * y l) =
      LinearMap.toMatrix' A.linear a k * LinearMap.toMatrix' A.linear b l * (y k * y l) :=
    fun _ _ => by ring
  have h5 : ∀ k, LinearMap.toMatrix' A.linear a k * y k * A 0 b =
      A 0 b * (LinearMap.toMatrix' A.linear a k * y k) := fun _ => by ring
  simp only [Finset.mul_sum, Finset.sum_mul, h4, h5]
  ring

variable (ν : Fin r → Measure (Fin (n + 1) → ℝ)) [∀ i, IsProbabilityMeasure (ν i)]

theorem map_sumShift_pi (d : Fin r → ℕ) :
    (Measure.pi ν).map (sumShift N d) =
      (Measure.pi fun i => (ν i).map (shiftIncl N (d i))).map (sumMap (N + 1) r) := by
  have hm : ∀ i, Measurable (shiftIncl (n := n) N (d i)) := fun i =>
    (shiftIncl N (d i)).continuous_of_finiteDimensional.measurable
  rw [← Measure.pi_map_pi (fun i => (hm i).aemeasurable), Measure.map_map measurable_sumMap
    (f := fun (x : Fin r → Fin (n + 1) → ℝ) i => shiftIncl N (d i) (x i))
    (measurable_pi_lambda _ fun i => (hm i).comp (measurable_pi_apply i))]
  congr 1
  funext x
  simp [sumShift_apply, sumMap_apply]

instance (d : ℕ) (i : Fin r) : IsProbabilityMeasure ((ν i).map (shiftIncl (n := n) N d)) :=
  ⟨by rw [Measure.map_apply (shiftIncl N d).continuous_of_finiteDimensional.measurable
    MeasurableSet.univ, Set.preimage_univ, measure_univ]⟩

/-- **`prop-pushforward` (1), centroid**: the law of `∑_i shift^{d_i} X_i`, the `X_i` independent
with laws `ν_i`, has centroid `∑_i shift^{d_i} c(ν_i)` (linearity of expectation). -/
theorem integrable_shift_coord (d : ℕ) {μ : Measure (Fin (n + 1) → ℝ)} [IsFiniteMeasure μ]
    (hint : ∀ a, Integrable (fun x : Fin (n + 1) → ℝ => x a) μ) (a : Fin (N + 1)) :
    Integrable (fun z : Fin (N + 1) → ℝ => z a) (μ.map (shiftIncl N d)) := by
  simpa using integrable_map_affine_coord (shiftIncl (n := n) N d).toAffineMap hint a

theorem integrable_shift_mul (d : ℕ) {μ : Measure (Fin (n + 1) → ℝ)} [IsFiniteMeasure μ]
    (hint : ∀ a, Integrable (fun x : Fin (n + 1) → ℝ => x a) μ)
    (hint2 : ∀ a b, Integrable (fun x : Fin (n + 1) → ℝ => x a * x b) μ) (a b : Fin (N + 1)) :
    Integrable (fun z : Fin (N + 1) → ℝ => z a * z b) (μ.map (shiftIncl N d)) := by
  simpa using integrable_map_affine_mul (shiftIncl (n := n) N d).toAffineMap hint hint2 a b

theorem mean_indepShiftSum (d : Fin r → ℕ)
    (hint : ∀ i a, Integrable (fun x : Fin (n + 1) → ℝ => x a) (ν i)) :
    mean ((Measure.pi ν).map (sumShift N d)) = ∑ i, shiftIncl N (d i) (mean (ν i)) := by
  rw [map_sumShift_pi, mean_indepSum _ fun i a => integrable_shift_coord (d i) (hint i) a]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using mean_map_affine (shiftIncl (n := n) N (d i)).toAffineMap (by simp) (hint i)

/-- **`prop-pushforward` (1), covariance**: by independence the covariance of
`∑_i shift^{d_i} X_i` is `∑_i P_i Σ(ν_i) P_iᵀ`, `P_i` the matrix of `shift^{d_i}` — the sum of
the shifted rank-one covariances. -/
theorem cov_indepShiftSum (d : Fin r → ℕ)
    (hint : ∀ i a, Integrable (fun x : Fin (n + 1) → ℝ => x a) (ν i))
    (hint2 : ∀ i a b, Integrable (fun x : Fin (n + 1) → ℝ => x a * x b) (ν i)) :
    cov ((Measure.pi ν).map (sumShift N d)) =
      ∑ i, LinearMap.toMatrix' (shiftIncl (n := n) N (d i)) * cov (ν i) *
        (LinearMap.toMatrix' (shiftIncl (n := n) N (d i)))ᵀ := by
  rw [map_sumShift_pi, cov_indepSum _ (fun i a => integrable_shift_coord (d i) (hint i) a)
    (fun i a b => integrable_shift_mul (d i) (hint i) (hint2 i) a b)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simpa using cov_map_affine (shiftIncl (n := n) N (d i)).toAffineMap (by simp) (hint i) (hint2 i)

end Shifted

/-! ## The uniform probability measures: on a finite set, and on `Koz(n)` -/

section Uniform

open Classical

variable {α : Type*} [MeasurableSpace α]

/-- The uniform probability measure on a finite set `L` (counting measure normalised). -/
noncomputable def unifF (L : Finset α) : Measure α := ((#L : ENNReal))⁻¹ • ∑ x ∈ L, Measure.dirac x

theorem unifF_apply (L : Finset α) {s : Set α} (hs : MeasurableSet s) :
    unifF L s = ((#L : ENNReal))⁻¹ * #({x ∈ L | x ∈ s}) := by
  rw [unifF, Measure.smul_apply, Measure.finsetSum_apply, smul_eq_mul]
  congr 1
  simp_rw [Measure.dirac_apply' _ hs, Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole]

variable [MeasurableSingletonClass α]

instance unifF_isProb (L : Finset α) [hL : Fact L.Nonempty] : IsProbabilityMeasure (unifF L) := by
  refine ⟨?_⟩
  rw [unifF_apply L MeasurableSet.univ]
  simp only [Set.mem_univ, Finset.filter_true]
  exact ENNReal.inv_mul_cancel (by simpa using hL.out.ne_empty) (ENNReal.natCast_ne_top _)

omit [MeasurableSingletonClass α] in
theorem unifF_empty : unifF (∅ : Finset α) = 0 := by simp [unifF]

instance isFiniteMeasure_unifF (L : Finset α) : IsFiniteMeasure (unifF L) := by
  rcases L.eq_empty_or_nonempty with h | h
  · rw [h, unifF_empty]; infer_instance
  · rw [unifF]
    have : ((#L : ENNReal))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr (by simpa using h.ne_empty)
    refine ⟨?_⟩
    rw [Measure.smul_apply, smul_eq_mul]
    exact ENNReal.mul_lt_top this.lt_top (measure_lt_top _ _)

theorem integrable_unifF (L : Finset α) {E : Type*} [NormedAddCommGroup E] (g : α → E) :
    Integrable g (unifF L) := by
  rcases L.eq_empty_or_nonempty with h | h
  · rw [h, unifF_empty]; exact integrable_zero_measure
  rw [unifF]
  refine Integrable.smul_measure ?_ (ENNReal.inv_ne_top.mpr (by simpa using h.ne_empty))
  rw [integrable_finsetSum_measure]
  exact fun x _ => integrable_dirac (by simp)

theorem integral_unifF (L : Finset α) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (g : α → E) : ∫ x, g x ∂unifF L = ((#L : ℝ))⁻¹ • ∑ x ∈ L, g x := by
  rw [unifF, integral_smul_measure, integral_finsetSum_measure fun x _ => integrable_dirac (by simp)]
  simp_rw [integral_dirac]
  simp

/-- The uniform measure on a product of finite sets is the product of the uniform measures. -/
theorem pi_unifF {r : ℕ} {β : Fin r → Type*} [∀ i, MeasurableSpace (β i)]
    [∀ i, MeasurableSingletonClass (β i)] (L : ∀ i, Finset (β i)) :
    Measure.pi (fun i => unifF (L i)) = unifF (Fintype.piFinset L) := by
  refine Measure.pi_eq fun t ht => ?_
  rw [unifF_apply _ (MeasurableSet.univ_pi ht)]
  simp_rw [unifF_apply _ (ht _)]
  rw [Finset.prod_mul_distrib, ← ENNReal.prod_inv_distrib (fun i _ j _ _ => Or.inr
    (ENNReal.natCast_ne_top _)), Fintype.card_piFinset, Nat.cast_prod]
  congr 1
  have : {x ∈ Fintype.piFinset L | x ∈ Set.univ.pi t} =
      Fintype.piFinset fun i => {y ∈ L i | y ∈ t i} := by
    ext x
    simp only [Finset.mem_filter, Fintype.mem_piFinset, Set.mem_univ_pi]
    exact ⟨fun h i => ⟨h.1 i, h.2 i⟩, fun h => ⟨fun i => (h i).1, fun i => (h i).2⟩⟩
  rw [this, Fintype.card_piFinset, Nat.cast_prod]

omit [MeasurableSingletonClass α] in
/-- Pushing the uniform measure forward along a map injective on `L` gives the uniform measure on
the image. -/
theorem map_unifF {γ : Type*} [MeasurableSpace γ] [MeasurableSingletonClass γ] [DecidableEq γ]
    (L : Finset α) {f : α → γ} (hf : Measurable f) (hinj : Set.InjOn f L) :
    (unifF L).map f = unifF (L.image f) := by
  ext s hs
  rw [Measure.map_apply hf hs, unifF_apply _ (hf hs), unifF_apply _ hs, Finset.card_image_of_injOn hinj]
  congr 2
  rw [Finset.filter_image, Finset.card_image_of_injOn (hinj.mono (fun x hx => by
    simp only [Finset.coe_filter, Set.mem_ofPred_eq] at hx; exact hx.1))]
  rfl

end Uniform

section UniformCoords

variable {D : ℕ}

theorem meanF_eq_mean (L : Finset (Fin D → ℝ)) [Fact L.Nonempty] :
    meanF L = mean (unifF L) := by
  rw [mean_of_prob]
  funext a
  rw [integral_unifF, meanF, smul_eq_mul, div_eq_inv_mul]

theorem covF_eq_cov (L : Finset (Fin D → ℝ)) [Fact L.Nonempty] :
    covF L = cov (unifF L) := by
  rw [cov_of_prob, ← meanF_eq_mean]
  ext a b
  rw [covF, Matrix.of_apply, Matrix.of_apply, integral_unifF, smul_eq_mul, div_eq_inv_mul]

end UniformCoords

section KozProb

open BetaMeasure

variable {n : ℕ}

/-- The uniform **probability** measure on `Koz(n)`: `kozMeasure n` normalised. -/
noncomputable def kozProb (n : ℕ) : Measure (Fin (n + 1) → ℝ) :=
  (kozMeasure n Set.univ)⁻¹ • kozMeasure n

theorem kozMeasure_univ_ne_top (hn : 1 ≤ n) : kozMeasure n Set.univ ≠ ⊤ := by
  have := isFiniteMeasure_kozMeasure (n := n) hn
  exact measure_ne_top _ _

theorem isProbabilityMeasure_kozProb (hn : 1 ≤ n) : IsProbabilityMeasure (kozProb n) :=
  ⟨by rw [kozProb, Measure.smul_apply, smul_eq_mul,
    ENNReal.inv_mul_cancel (kozMeasure_univ_ne_zero hn) (kozMeasure_univ_ne_top hn)]⟩

theorem mean_kozProb (hn : 1 ≤ n) : mean (kozProb n) = mean (kozMeasure n) :=
  mean_smul_measure _ (ENNReal.inv_ne_zero.mpr (kozMeasure_univ_ne_top hn))
    (ENNReal.inv_ne_top.mpr (kozMeasure_univ_ne_zero hn))

theorem cov_kozProb (hn : 1 ≤ n) : cov (kozProb n) = cov (kozMeasure n) :=
  cov_smul_measure _ (ENNReal.inv_ne_zero.mpr (kozMeasure_univ_ne_top hn))
    (ENNReal.inv_ne_top.mpr (kozMeasure_univ_ne_zero hn))

theorem integrable_kozProb_of_continuous (hn : 1 ≤ n) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : Continuous F) : Integrable F (kozProb n) :=
  (integrable_kozMeasure_of_continuous hn hF).smul_measure
    (ENNReal.inv_ne_top.mpr (kozMeasure_univ_ne_zero hn))

end KozProb

/-! ## `prop-pushforward`: the statements -/

section PushForward

open BetaMeasure KozVolume

variable {n N r : ℕ}

/-- **`prop-pushforward` (1), polytope point**: the centroid of a sum `∑_i shift^{d_i} X_i` of
independent uniform points `X_i` of `Koz(n)` is `∑_i shift^{d_i} c(Koz(n))`. -/
theorem mean_indepSum_koz (hn : 1 ≤ n) (d : Fin r → ℕ) :
    mean ((Measure.pi fun _ : Fin r => kozProb n).map (sumShift N d)) =
      ∑ i, shiftIncl N (d i) (mean (kozMeasure n)) := by
  have := isProbabilityMeasure_kozProb hn
  rw [mean_indepShiftSum _ d fun _ a => integrable_kozProb_of_continuous hn (continuous_apply a)]
  simp_rw [mean_kozProb hn]

/-- **`prop-pushforward` (1), polytope point, covariance**: `∑_i P_i Σ(Koz(n)) P_iᵀ`. -/
theorem cov_indepSum_koz (hn : 1 ≤ n) (d : Fin r → ℕ) :
    cov ((Measure.pi fun _ : Fin r => kozProb n).map (sumShift N d)) =
      ∑ i, LinearMap.toMatrix' (shiftIncl (n := n) N (d i)) * cov (kozMeasure n) *
        (LinearMap.toMatrix' (shiftIncl (n := n) N (d i)))ᵀ := by
  have := isProbabilityMeasure_kozProb hn
  rw [cov_indepShiftSum _ d (fun _ a => integrable_kozProb_of_continuous hn (continuous_apply a))
    (fun _ a b => integrable_kozProb_of_continuous hn
      ((continuous_apply a).mul (continuous_apply b)))]
  simp_rw [cov_kozProb hn]

/-- **`prop-pushforward` (1), finite version** (`L_i = S_n` gives the independent sum of the
`c(S_n)`, `L_i = 𝓛_n` that of the lattice-point centroids): the push-forward of the uniform
measure on `L_1 × ⋯ × L_r` under `(x_i) ↦ ∑ shift^{d_i} x_i` has centroid `∑ shift^{d_i} c(L_i)`
and covariance `∑ P_i Σ(L_i) P_iᵀ`. -/
theorem meanF_covF_indepSum (L : Fin r → Finset (Fin (n + 1) → ℝ)) (hL : ∀ i, (L i).Nonempty)
    (d : Fin r → ℕ) :
    mean ((unifF (Fintype.piFinset L)).map (sumShift N d)) =
        ∑ i, shiftIncl N (d i) (meanF (L i)) ∧
      cov ((unifF (Fintype.piFinset L)).map (sumShift N d)) =
        ∑ i, LinearMap.toMatrix' (shiftIncl (n := n) N (d i)) * covF (L i) *
          (LinearMap.toMatrix' (shiftIncl (n := n) N (d i)))ᵀ := by
  have : ∀ i, Fact (L i).Nonempty := fun i => ⟨hL i⟩
  rw [← pi_unifF]
  refine ⟨?_, ?_⟩
  · rw [mean_indepShiftSum _ d fun i a => integrable_unifF _ _]
    simp_rw [meanF_eq_mean]
  · rw [cov_indepShiftSum _ d (fun i a => integrable_unifF _ _) (fun i a b => integrable_unifF _ _)]
    simp_rw [covF_eq_cov]

/-- If the sumset map is a bijection `L_1 × ⋯ × L_r → F`, the uniform measure on `F` is the
push-forward of the uniform measure on the product. -/
theorem unifF_eq_map_of_bijOn (L : Fin r → Finset (Fin (n + 1) → ℝ)) (d : Fin r → ℕ)
    (F : Finset (Fin (N + 1) → ℝ))
    (h : Set.BijOn (sumShift N d) (Set.univ.pi fun i => (L i : Set (Fin (n + 1) → ℝ))) F) :
    unifF F = (unifF (Fintype.piFinset L)).map (sumShift N d) := by
  rw [map_unifF _ (measurable_sumShift d) (by rw [Fintype.coe_piFinset]; exact h.injOn)]
  congr 1
  apply Finset.coe_injective
  rw [Finset.coe_image, Fintype.coe_piFinset, h.image_eq]

/-- **`prop-pushforward` (2), finite clauses, against an explicit hypothesis**: if the sumset
map `(x_i) ↦ ∑ shift^{d_i} x_i` is a bijection from `L_1 × ⋯ × L_r` onto a finite set `F`, then
the centroid and covariance of `F` are the sums of the shifted rank-one ones. Instances:
`L_i = S_n`, `F = FF(n; d⃗)` (`meanF_covF_ff`), and `L_i = 𝓛_n`, `F` = the lattice points of
`Koz(n; d⃗)` (`meanF_covF_lattice`). -/
theorem meanF_covF_of_bijOn (L : Fin r → Finset (Fin (n + 1) → ℝ)) (hL : ∀ i, (L i).Nonempty)
    (d : Fin r → ℕ) (F : Finset (Fin (N + 1) → ℝ))
    (h : Set.BijOn (sumShift N d) (Set.univ.pi fun i => (L i : Set (Fin (n + 1) → ℝ))) F) :
    meanF F = ∑ i, shiftIncl N (d i) (meanF (L i)) ∧
      covF F = ∑ i, LinearMap.toMatrix' (shiftIncl (n := n) N (d i)) * covF (L i) *
        (LinearMap.toMatrix' (shiftIncl (n := n) N (d i)))ᵀ := by
  have hF : Fact F.Nonempty := by
    choose x hx using hL
    exact ⟨⟨_, h.mapsTo (show x ∈ Set.univ.pi fun i => (L i : Set _) from
      fun i _ => hx i)⟩⟩
  rw [meanF_eq_mean, covF_eq_cov, unifF_eq_map_of_bijOn L d F h]
  exact meanF_covF_indepSum L hL d

/-- `S_n` as a `Finset`. -/
noncomputable def SnF (n : ℕ) : Finset (Fin (n + 1) → ℝ) := (Sset_finite n).toFinset

theorem coe_SnF : (SnF n : Set (Fin (n + 1) → ℝ)) = Sset n := Set.Finite.coe_toFinset _

theorem SnF_nonempty (hn : 1 ≤ n) : (SnF n).Nonempty :=
  ⟨skel n 1, by rw [← Finset.mem_coe, coe_SnF]; exact skelSet_subset_Sset ⟨1, ⟨le_rfl, hn⟩, rfl⟩⟩

/-- The sumset map is always onto `FF(n; d⃗)` (`prop-sumset`, `ff_eq_sumset`). -/
theorem sumShift_surjOn_ff (d : Fin r → ℕ) :
    Set.SurjOn (sumShift N d) (Set.univ.pi fun _ => Sset n) (ffSet n N d) := by
  intro x hx
  rw [ff_eq_sumset, Set.mem_fintype_sum] at hx
  obtain ⟨g, hg, rfl⟩ := hx
  choose y hy hyg using hg
  exact ⟨y, fun i _ => hy i, by rw [sumShift_apply]; exact Finset.sum_congr rfl fun i _ => hyg i⟩

theorem sumShift_mapsTo_ff (d : Fin r → ℕ) :
    Set.MapsTo (sumShift N d) (Set.univ.pi fun _ => Sset n) (ffSet n N d) := by
  intro x hx
  rw [ff_eq_sumset, Set.mem_fintype_sum]
  exact ⟨fun i => shiftIncl N (d i) (x i), fun i => ⟨x i, hx i (Set.mem_univ _), rfl⟩,
    (sumShift_apply d x).symm⟩

/-- **`prop-pushforward` (2), the `FF` clause**: if the sumset map `S_n^r → FF(n; d⃗)` is
injective (in the product regime this is Part II Prop. 42, `|FF| = |S_n|^r`, together with
surjectivity, which holds always), then the centroid of `FF` is the independent sum
`∑ shift^{d_i} c(S_n)` and its covariance is `∑ P_i Σ(S_n) P_iᵀ`. -/
theorem meanF_covF_ff (hn : 1 ≤ n) (d : Fin r → ℕ) (F : Finset (Fin (N + 1) → ℝ))
    (hF : (F : Set (Fin (N + 1) → ℝ)) = ffSet n N d)
    (hinj : Set.InjOn (sumShift N d) (Set.univ.pi fun _ : Fin r => Sset n)) :
    meanF F = ∑ i, shiftIncl N (d i) (meanF (SnF n)) ∧
      covF F = ∑ i, LinearMap.toMatrix' (shiftIncl (n := n) N (d i)) * covF (SnF n) *
        (LinearMap.toMatrix' (shiftIncl (n := n) N (d i)))ᵀ := by
  refine meanF_covF_of_bijOn (fun _ => SnF n) (fun _ => SnF_nonempty hn) d F ?_
  simp only [coe_SnF, hF]
  exact ⟨sumShift_mapsTo_ff d, hinj, sumShift_surjOn_ff d⟩

/-- **`prop-pushforward` (2), the lattice-point clause, against an explicit hypothesis**: if the
sumset map is a bijection `𝓛_n^r → Koz(n; d⃗) ∩ ℤ^{N+1}` (in the product regime: the affine
bijection `Φ : Koz(n; d⃗) → Koz(n)^r`, inverse `(x_i) ↦ ∑ shift^{d_i} x_i`, matches lattice
points), the lattice-point centroid and covariance of `Koz(n; d⃗)` are the sums of the shifted
lattice-point centroids and covariances of `Koz(n)`. -/
theorem meanF_covF_lattice (hn : 3 ≤ n) (d : Fin r → ℕ) (Ln : Finset (Fin (n + 1) → ℝ))
    (hLn : (Ln : Set (Fin (n + 1) → ℝ)) = Beta.latticePts n) (F : Finset (Fin (N + 1) → ℝ))
    (hF : (F : Set (Fin (N + 1) → ℝ)) =
      {x | x ∈ convexHull ℝ (ffSet n N d) ∧ Beta.IsIntPt x})
    (h : Set.BijOn (sumShift N d) (Set.univ.pi fun _ : Fin r => Beta.latticePts n)
      {x | x ∈ convexHull ℝ (ffSet n N d) ∧ Beta.IsIntPt x}) :
    meanF F = ∑ i, shiftIncl N (d i) (meanF Ln) ∧
      covF F = ∑ i, LinearMap.toMatrix' (shiftIncl (n := n) N (d i)) * covF Ln *
        (LinearMap.toMatrix' (shiftIncl (n := n) N (d i)))ᵀ := by
  have hne : Ln.Nonempty := ⟨Beta.witness n, by
    rw [← Finset.mem_coe, hLn]; exact Beta.witness_mem_latticePts hn⟩
  refine meanF_covF_of_bijOn (fun _ => Ln) (fun _ => hne) d F ?_
  simp only [hLn, hF]
  exact h

end PushForward

/-! ## `prop-pushforward` (3): equal shifts -/

section EqualShifts

open BetaMeasure KozVolume
open scoped Pointwise

variable {n r : ℕ}

/-- `shift⁰` on `ℝ^{n+1}` (with `N = n`) is the identity. -/
theorem shiftIncl_zero : shiftIncl (n := n) n 0 = LinearMap.id := by
  apply LinearMap.ext
  intro x
  funext j
  rw [shiftIncl_apply, dite_eq_left ⟨Nat.zero_le _, by omega⟩]
  simp

/-- `r`-fold Minkowski sum of a non-empty convex set is its `r`-th dilate. -/
theorem sum_const_convex {E : Type*} [AddCommGroup E] [Module ℝ E] {K : Set E}
    (hK : Convex ℝ K) (hne : K.Nonempty) (r : ℕ) : ∑ _i : Fin r, K = (r : ℝ) • K := by
  induction r with
  | zero => simp [Set.zero_smul_set hne]
  | succ r ih =>
    rw [Fin.sum_univ_succ, ih, Nat.cast_succ, add_comm (r : ℝ), hK.add_smul zero_le_one
      (Nat.cast_nonneg r), one_smul]

/-- **`prop-pushforward` (3), the set**: `Koz(n; 0^r) = r · Koz(n)`. -/
theorem koz_zero_shifts (hn : 1 ≤ n) (r : ℕ) :
    ∑ _i : Fin r, shiftIncl (n := n) n 0 '' convexHull ℝ (skelSet n) =
      (r : ℝ) • convexHull ℝ (skelSet n) := by
  simp only [shiftIncl_zero, LinearMap.id_coe, Set.image_id]
  exact sum_const_convex (convex_convexHull ℝ _)
    (show (convexHull ℝ (skelSet n)).Nonempty from
      ⟨skel n 1, subset_convexHull ℝ _ ⟨1, ⟨le_rfl, hn⟩, rfl⟩⟩) r

/-- The dilation `x ↦ t·x`. -/
noncomputable def dil (D : ℕ) (t : ℝ) : (Fin D → ℝ) →ᵃ[ℝ] (Fin D → ℝ) :=
  (t • LinearMap.id).toAffineMap

theorem toMatrix'_dil (D : ℕ) (t : ℝ) :
    LinearMap.toMatrix' (dil D t).linear = t • (1 : Matrix (Fin D) (Fin D) ℝ) := by
  simp [dil, LinearMap.toMatrix'_id]

/-- **`prop-pushforward` (3), the polytope**: the uniform measure on `r·Koz(n)` (the push-forward
of that on `Koz(n)` by the dilation) has centroid `r·c(Koz(n))` and covariance
`r²·Σ(Koz(n))`. -/
theorem mean_cov_dilate (hn : 1 ≤ n) (r : ℕ) :
    mean ((kozMeasure n).map (dil (n + 1) r)) = (r : ℝ) • mean (kozMeasure n) ∧
      cov ((kozMeasure n).map (dil (n + 1) r)) = ((r : ℝ) ^ 2) • cov (kozMeasure n) := by
  have := isFiniteMeasure_kozMeasure (n := n) hn
  have hint := fun i : Fin (n + 1) => integrable_kozMeasure_of_continuous hn (continuous_apply i)
  refine ⟨?_, ?_⟩
  · rw [mean_map_affine _ (kozMeasure_univ_ne_zero hn) hint]
    simp [dil]
  · rw [cov_map_affine _ (kozMeasure_univ_ne_zero hn) hint fun i j =>
      integrable_kozMeasure_of_continuous hn ((continuous_apply i).mul (continuous_apply j)),
      toMatrix'_dil]
    simp [smul_smul, pow_two]

/-- **`prop-pushforward` (3), the independent sum**: for `d⃗ = 0^r` the sum of `r` independent
uniform points of `Koz(n)` has centroid `r·c(Koz(n))` too, but covariance `r·Σ(Koz(n))`. -/
theorem mean_cov_indepSum_zero (hn : 1 ≤ n) (r : ℕ) :
    mean ((Measure.pi fun _ : Fin r => kozProb n).map (sumShift n fun _ => 0)) =
        (r : ℝ) • mean (kozMeasure n) ∧
      cov ((Measure.pi fun _ : Fin r => kozProb n).map (sumShift n fun _ => 0)) =
        (r : ℝ) • cov (kozMeasure n) := by
  refine ⟨?_, ?_⟩
  · rw [mean_indepSum_koz hn]
    simp only [shiftIncl_zero, LinearMap.id_apply]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
  · rw [cov_indepSum_koz hn]
    simp only [shiftIncl_zero, LinearMap.toMatrix'_id, one_mul, Matrix.transpose_one, mul_one]
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]

end EqualShifts

/-! ## `prop-pushforward` (2), the polytope clause

A uniform measure on a set `K ⊆ ℝ^E` lying in an affine subspace is defined, in the style of
`kozMeasure`, through an injective affine chart: `IsUniformOn ρ K` says `ρ` is Lebesgue measure
on `φ⁻¹(K)` pushed forward by some injective affine `φ : ℝ^D → ℝ^E` with `K ⊆ range φ`.
(`kozMeasure n` is of this form, `kozMeasure_isUniformOn`.) Mean and covariance do not depend on
the chart (`chart_rigidity`). -/

section PolytopeProduct

/-- `ρ` is a (Lebesgue) uniform measure on `K`, via an injective affine chart. -/
def IsUniformOn {E : ℕ} (ρ : Measure (Fin E → ℝ)) (K : Set (Fin E → ℝ)) : Prop :=
  ∃ (D : ℕ) (φ : (Fin D → ℝ) →ᵃ[ℝ] (Fin E → ℝ)), Function.Injective φ ∧ K ⊆ Set.range φ ∧
    ρ = (volume.restrict (φ ⁻¹' K)).map φ

/-- **Rigidity of uniform measures under affine charts.** Let `T` be an affine map injective on
a set `P` with non-empty interior (in a finite-dimensional space with Haar measure `μ`), and let
`φ : ℝ^D → ℝ^E` be an injective affine chart whose range contains `T(P)`. If the chart's
Lebesgue measure on `T(P)` is not zero, then the push-forward `T_*(μ|_P)` is a positive finite
multiple of it: the uniform measure on an affine image does not depend on the chart. -/
theorem chart_rigidity {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {E D : ℕ}
    {P : Set V} (hP : (interior P).Nonempty) (T : V →ᵃ[ℝ] (Fin E → ℝ)) (hT : Set.InjOn T P)
    (φ : (Fin D → ℝ) →ᵃ[ℝ] (Fin E → ℝ)) (hφ : Function.Injective φ)
    (hK : T '' P ⊆ Set.range φ)
    (hρ0 : (volume.restrict (φ ⁻¹' (T '' P))).map φ ≠ 0) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      (μ.restrict P).map T = c • (volume.restrict (φ ⁻¹' (T '' P))).map φ := by
  -- an affine left inverse of `φ`
  obtain ⟨g, hg⟩ := φ.linear.exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr ((AffineMap.linear_injective_iff φ).mpr hφ))
  let ψ : V →ᵃ[ℝ] (Fin D → ℝ) := g.toAffineMap.comp (T -ᵥ AffineMap.const ℝ V (φ 0))
  have hψφ : ∀ x y, T x = φ y → ψ x = y := by
    intro x y h
    have : ψ x = g (φ.linear (y -ᵥ 0)) := by
      simp only [ψ, AffineMap.comp_apply, LinearMap.coe_toAffineMap, AffineMap.vsub_apply,
        AffineMap.const_apply, h, AffineMap.linearMap_vsub]
    rw [this, ← LinearMap.comp_apply, hg, LinearMap.id_apply, vsub_eq_sub, sub_zero]
  -- `T` takes values in the range of `φ`
  have hspan : affineSpan ℝ P = ⊤ :=
    affineSpan_eq_top_of_nonempty_interior (hP.mono (interior_mono (subset_convexHull ℝ P)))
  have hrange : ∀ x, ∃ y, φ y = T x := by
    intro x
    have hx : T x ∈ (affineSpan ℝ P).map T := AffineSubspace.mem_map.mpr ⟨x, by simp [hspan], rfl⟩
    rw [AffineSubspace.map_span] at hx
    have hle : affineSpan ℝ (T '' P) ≤ (⊤ : AffineSubspace ℝ (Fin D → ℝ)).map φ := by
      rw [affineSpan_le, AffineSubspace.coe_map, AffineSubspace.top_coe, Set.image_univ]
      exact hK
    obtain ⟨y, -, hy⟩ := AffineSubspace.mem_map.mp (hle hx)
    exact ⟨y, hy⟩
  have hTφψ : ∀ x, φ (ψ x) = T x := by
    intro x
    obtain ⟨y, hy⟩ := hrange x
    rw [hψφ x y hy.symm, hy]
  have hpre : φ ⁻¹' (T '' P) = ψ '' P := by
    ext y
    simp only [Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨x, hx, hxy⟩; exact ⟨x, hx, hψφ x y hxy⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨x, hx, (hTφψ x).symm⟩
  -- `ψ` is injective
  have hψinj : Function.Injective ψ.linear := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    obtain ⟨p, hp⟩ := hP
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, t • v +ᵥ p ∈ P ∧ t ≠ 0 := by
      refine Filter.Eventually.and ?_ self_mem_nhdsWithin
      apply nhdsWithin_le_nhds
      have hc : Continuous fun t : ℝ => t • v +ᵥ p := by fun_prop
      have := hc.tendsto 0
      simp only [zero_smul, zero_vadd] at this
      exact this (mem_interior_iff_mem_nhds.mp hp)
    obtain ⟨t, htP, ht0⟩ := hev.exists
    have hpP : p ∈ P := interior_subset hp
    have heq : ψ (t • v +ᵥ p) = ψ p := by
      rw [AffineMap.map_vadd, map_smul, hv, smul_zero, zero_vadd]
    have := hT htP hpP (by rw [← hTφψ, ← hTφψ, heq])
    rw [vadd_eq_add, add_eq_right, smul_eq_zero] at this
    exact this.resolve_left ht0
  -- `ψ` is surjective (else its range is null and `ρ = 0`)
  have hψsurj : Function.Surjective ψ.linear := by
    rw [AffineMap.linear_surjective_iff]
    by_contra hns
    have hne : (⊤ : AffineSubspace ℝ V).map ψ ≠ ⊤ := by
      intro h
      apply hns
      intro z
      have : z ∈ (⊤ : AffineSubspace ℝ V).map ψ := by rw [h]; trivial
      obtain ⟨x, -, hx⟩ := AffineSubspace.mem_map.mp this
      exact ⟨x, hx⟩
    have h0 := Measure.addHaar_affineSubspace volume _ hne
    rw [AffineSubspace.coe_map, AffineSubspace.top_coe, Set.image_univ] at h0
    apply hρ0
    rw [hpre, Measure.restrict_eq_zero.mpr (measure_mono_null (Set.image_subset_range _ _) h0),
      Measure.map_zero]
  -- `ψ` is an affine isomorphism, so it carries `μ` to a multiple of Lebesgue measure
  let e := LinearEquiv.ofBijective ψ.linear ⟨hψinj, hψsurj⟩
  let eC := e.toContinuousLinearEquiv
  have hdec : ⇑ψ = (fun z => z + ψ 0) ∘ ⇑eC := by
    funext x
    exact congrFun (AffineMap.decomp ψ) x
  have : (μ.map eC).IsAddHaarMeasure := eC.isAddHaarMeasure_map μ
  have hmapψ : μ.map ψ = μ.map eC := by
    rw [hdec, ← Measure.map_map (measurable_add_const _) eC.continuous.measurable,
      map_add_right_eq_self]
  set c := (μ.map eC).addHaarScalarFactor volume
  have hc : μ.map eC = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  have hcpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hemb : MeasurableEmbedding ψ := by
    rw [hdec]
    exact (eC.toHomeomorph.trans (Homeomorph.addRight (ψ 0))).measurableEmbedding
  have hψinj' : Function.Injective ψ := (AffineMap.linear_injective_iff ψ).mp hψinj
  have hres : (μ.restrict P).map ψ = c • volume.restrict (ψ '' P) := by
    have h := hemb.restrict_map μ (ψ '' P)
    rw [Set.preimage_image_eq _ hψinj', hmapψ, hc, Measure.restrict_smul] at h
    exact h.symm
  have hT : ⇑T = ⇑φ ∘ ⇑ψ := funext fun x => (hTφψ x).symm
  refine ⟨(c : ENNReal), by simpa using hcpos.ne', ENNReal.coe_ne_top, ?_⟩
  have h2 : (μ.restrict P).map T = ((μ.restrict P).map ψ).map φ := by
    rw [Measure.map_map φ.continuous_of_finiteDimensional.measurable hemb.measurable, ← hT]
  rw [h2, hres, Measure.map_smul _ φ.continuous_of_finiteDimensional.measurable.aemeasurable, hpre]
  rfl

open BetaMeasure KozVolume

variable {n N r : ℕ}

theorem lift_injective : Function.Injective (lift n) := fun a b h => by
  rw [← proj_lift a, h, proj_lift]

theorem lift_preimage_koz (hn : 1 ≤ n) : lift n ⁻¹' convexHull ℝ (skelSet n) = kozProj n := by
  ext y
  simp only [Set.mem_preimage, kozProj, Set.mem_image]
  constructor
  · intro h; exact ⟨lift n y, h, by rw [← coe_proj, proj_lift]⟩
  · rintro ⟨x, hx, rfl⟩
    rw [← coe_proj, lift_proj hn (convexHull_skelSet_subset_plane hn hx)]
    exact hx

theorem lift_image_kozProj (hn : 1 ≤ n) : lift n '' kozProj n = convexHull ℝ (skelSet n) := by
  rw [← lift_preimage_koz hn, Set.image_preimage_eq_of_subset]
  rw [range_lift hn]
  exact convexHull_skelSet_subset_plane hn

/-- `kozMeasure n` is a uniform measure on `Koz(n)` in the sense of `IsUniformOn`. -/
theorem kozMeasure_isUniformOn (hn : 1 ≤ n) :
    IsUniformOn (kozMeasure n) (convexHull ℝ (skelSet n)) :=
  ⟨n - 1, lift n, lift_injective, by rw [range_lift hn]; exact convexHull_skelSet_subset_plane hn,
    by rw [lift_preimage_koz hn]; rfl⟩

theorem interior_corner_nonempty (m : ℕ) : (interior (cornerSimplex m)).Nonempty := by
  let O : Set (Fin m → ℝ) := (⋂ i, {x | 0 < x i}) ∩ {x | ∑ i, x i < 1}
  have hO : IsOpen O := (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const
    (continuous_apply i)).inter (isOpen_lt (by fun_prop) continuous_const)
  have hOC : O ⊆ cornerSimplex m := by
    intro x hx
    rw [cornerSimplex_eq]
    simp only [O, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hx
    exact ⟨fun i => (hx.1 i).le, hx.2.le⟩
  refine ⟨fun _ => 1 / (2 * ((m : ℝ) + 1)), interior_maximal hOC hO ⟨?_, ?_⟩⟩
  · simp only [Set.mem_iInter, Set.mem_ofPred_eq]; intro i; positivity
  · simp only [Set.mem_ofPred_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    rw [mul_one_div, div_lt_one (by positivity)]
    linarith

theorem interior_kozProj_nonempty (hn : 1 ≤ n) : (interior (kozProj n)).Nonempty := by
  set L := Matrix.toLin' (vdiff n)
  let eC := (LinearMap.equivOfDetNeZero L vdiff_det_ne_zero').toContinuousLinearEquiv
  have hL : ⇑eC = ⇑L := rfl
  have h := eC.toHomeomorph.image_interior (cornerSimplex (n - 1))
  simp only [ContinuousLinearEquiv.coe_toHomeomorph] at h
  rw [kozProj_eq hn, ← hL, ← h]
  exact (interior_corner_nonempty _).image _

/-- The product chart `(y_i) ↦ (lift y_i)` of `Koz(n)^r`. -/
noncomputable def liftPi (n r : ℕ) :
    (Fin r → Fin (n - 1) → ℝ) →ᵃ[ℝ] (Fin r → Fin (n + 1) → ℝ) :=
  AffineMap.pi fun i => (lift n).comp (LinearMap.proj (R := ℝ) (φ := fun _ : Fin r =>
    Fin (n - 1) → ℝ) i).toAffineMap

theorem liftPi_apply (y : Fin r → Fin (n - 1) → ℝ) (i : Fin r) : liftPi n r y i = lift n (y i) := by
  simp [liftPi]

/-- The product of the uniform measures on `Koz(n)`, pushed forward by the sumset map, is the
push-forward of Lebesgue measure on `kozProj(n)^r` under the affine map `sumShift ∘ liftPi`. -/
theorem map_pi_kozMeasure (hn : 1 ≤ n) (d : Fin r → ℕ) :
    (Measure.pi fun _ : Fin r => kozMeasure n).map (sumShift N d) =
      ((volume : Measure (Fin r → Fin (n - 1) → ℝ)).restrict
        (Set.univ.pi fun _ => kozProj n)).map ((sumShift N d).toAffineMap.comp (liftPi n r)) := by
  have : IsFiniteMeasure ((volume.restrict (kozProj n)).map (lift n)) :=
    isFiniteMeasure_kozMeasure hn
  have : IsFiniteMeasure (volume.restrict (kozProj n)) :=
    isFiniteMeasure_restrict.mpr (isCompact_kozProj hn).measure_lt_top.ne
  have h1 : (Measure.pi fun _ : Fin r => kozMeasure n) =
      ((volume : Measure (Fin r → Fin (n - 1) → ℝ)).restrict
        (Set.univ.pi fun _ => kozProj n)).map (liftPi n r) := by
    have hv : (volume : Measure (Fin r → Fin (n - 1) → ℝ)).restrict
        (Set.univ.pi fun _ => kozProj n) = Measure.pi fun _ => volume.restrict (kozProj n) :=
      Measure.restrict_pi_pi (fun _ => (volume : Measure (Fin (n - 1) → ℝ))) _
    simp only [kozMeasure]
    rw [hv, ← Measure.pi_map_pi (fun _ => continuous_lift.aemeasurable)]
    congr 1
  rw [h1, Measure.map_map (measurable_sumShift d)
    (liftPi n r).continuous_of_finiteDimensional.measurable]
  rfl

/-- `Koz(n; d⃗) = conv FF(n; d⃗)` is the image of `kozProj(n)^r` under `sumShift ∘ liftPi`. -/
theorem image_kozProj_pi (hn : 1 ≤ n) (d : Fin r → ℕ) :
    (sumShift N d).toAffineMap.comp (liftPi n r) '' (Set.univ.pi fun _ => kozProj n) =
      convexHull ℝ (ffSet n N d) := by
  rw [main n N d]
  simp_rw [hull_Sset_eq hn, ← hull_skel_eq hn, ← lift_image_kozProj hn]
  ext x
  simp only [AffineMap.coe_comp, LinearMap.coe_toAffineMap, Set.mem_image, Function.comp_apply,
    Set.mem_univ_pi, Set.mem_fintype_sum]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨fun i => shiftIncl N (d i) (lift n (y i)), fun i => ⟨lift n (y i), ⟨y i, hy i, rfl⟩,
      rfl⟩, ?_⟩
    rw [sumShift_apply]
    simp only [liftPi_apply]
  · rintro ⟨g, hg, rfl⟩
    choose z hz hzg using hg
    choose y hy hyz using hz
    refine ⟨y, hy, ?_⟩
    rw [sumShift_apply]
    exact Finset.sum_congr rfl fun i _ => by rw [liftPi_apply, hyz, hzg]

theorem pi_smul_const {α : Type*} [MeasurableSpace α] (κ : Measure α) [IsFiniteMeasure κ]
    (a : ENNReal) (ha : a ≠ ⊤) :
    Measure.pi (fun _ : Fin r => a • κ) = a ^ r • Measure.pi fun _ : Fin r => κ := by
  have : IsFiniteMeasure (a • κ) := ⟨by
    rw [Measure.smul_apply, smul_eq_mul]; exact ENNReal.mul_lt_top ha.lt_top (measure_lt_top _ _)⟩
  refine Measure.pi_eq fun t ht => ?_
  rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem kozMeasure_eq_smul_kozProb (hn : 1 ≤ n) :
    kozMeasure n = kozMeasure n Set.univ • kozProb n := by
  rw [kozProb, smul_smul, ENNReal.mul_inv_cancel (kozMeasure_univ_ne_zero hn)
    (kozMeasure_univ_ne_top hn), one_smul]

/-- In the product regime the uniform measure on `Koz(n; d⃗)` is a positive multiple of the law of
`∑ shift^{d_i} X_i`, `X_i` independent uniform on `Koz(n)`. Hypotheses: `ρ` is a uniform measure
on `Koz(n; d⃗) = conv FF(n; d⃗)` in the chart sense (`IsUniformOn`), it is not zero (the chart has
the right dimension), and the sumset map is injective on `Koz(n)^r` (it is always onto
`Koz(n; d⃗)`, `image_kozProj_pi`, so this is the bijection `Φ⁻¹`). -/
theorem uniform_eq_smul_indepSum (hn : 1 ≤ n) (d : Fin r → ℕ) (ρ : Measure (Fin (N + 1) → ℝ))
    (hρ : IsUniformOn ρ (convexHull ℝ (ffSet n N d))) (hρ0 : ρ ≠ 0)
    (hinj : Set.InjOn (sumShift N d) (Set.univ.pi fun _ : Fin r => convexHull ℝ (skelSet n))) :
    ∃ c : ENNReal, c ≠ 0 ∧ c ≠ ⊤ ∧
      ρ = c • (Measure.pi fun _ : Fin r => kozProb n).map (sumShift N d) := by
  obtain ⟨D, φ, hφ, hKφ, rfl⟩ := hρ
  have : (volume : Measure (Fin r → Fin (n - 1) → ℝ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure _
  have := isProbabilityMeasure_kozProb hn
  set T := (sumShift N d).toAffineMap.comp (liftPi n r)
  have hP : (interior (Set.univ.pi fun _ : Fin r => kozProj n)).Nonempty := by
    rw [interior_pi_set Set.finite_univ]
    exact Set.univ_pi_nonempty_iff.mpr fun _ => interior_kozProj_nonempty hn
  have hmem : ∀ y ∈ Set.univ.pi (fun _ : Fin r => kozProj n),
      liftPi n r y ∈ Set.univ.pi fun _ : Fin r => convexHull ℝ (skelSet n) := by
    intro y hy i _
    rw [liftPi_apply, ← lift_image_kozProj hn]
    exact ⟨y i, hy i (Set.mem_univ _), rfl⟩
  have hT : Set.InjOn T (Set.univ.pi fun _ : Fin r => kozProj n) := by
    intro a ha b hb h
    have := hinj (hmem a ha) (hmem b hb) h
    funext i
    exact lift_injective (by rw [← liftPi_apply, ← liftPi_apply, this])
  have himg := image_kozProj_pi (N := N) hn d
  obtain ⟨c, hc0, hct, hc⟩ := chart_rigidity volume hP T hT φ hφ (by rw [himg]; exact hKφ)
    (by rw [himg]; exact hρ0)
  rw [himg, ← map_pi_kozMeasure hn d, kozMeasure_eq_smul_kozProb hn,
    pi_smul_const _ _ (kozMeasure_univ_ne_top hn), Measure.map_smul _
      (measurable_sumShift d).aemeasurable] at hc
  set M := kozMeasure n Set.univ
  refine ⟨c⁻¹ * M ^ r, ?_, ?_, ?_⟩
  · exact mul_ne_zero (ENNReal.inv_ne_zero.mpr hct) (pow_ne_zero _ (kozMeasure_univ_ne_zero hn))
  · exact ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hc0)
      (ENNReal.pow_ne_top (kozMeasure_univ_ne_top hn))
  · rw [mul_smul, hc, smul_smul, ENNReal.inv_mul_cancel hc0 hct, one_smul]

/-- **`prop-pushforward` (2), the polytope clause, against an explicit hypothesis**: if the
sumset map `(x_i) ↦ ∑ shift^{d_i} x_i` is injective on `Koz(n)^r` (the product regime: it is then
the inverse of an affine bijection `Φ : Koz(n; d⃗) → Koz(n)^r`), then for the uniform measure `ρ`
on `Koz(n; d⃗)` (any chart, `IsUniformOn`, non-degenerate) the centroid is the independent sum
`∑ shift^{d_i} c(Koz(n))` and the covariance is `∑ P_i Σ(Koz(n)) P_iᵀ`. -/
theorem mean_cov_uniform_productRegime (hn : 1 ≤ n) (d : Fin r → ℕ)
    (ρ : Measure (Fin (N + 1) → ℝ)) (hρ : IsUniformOn ρ (convexHull ℝ (ffSet n N d)))
    (hρ0 : ρ ≠ 0)
    (hinj : Set.InjOn (sumShift N d) (Set.univ.pi fun _ : Fin r => convexHull ℝ (skelSet n))) :
    mean ρ = ∑ i, shiftIncl N (d i) (mean (kozMeasure n)) ∧
      cov ρ = ∑ i, LinearMap.toMatrix' (shiftIncl (n := n) N (d i)) * cov (kozMeasure n) *
        (LinearMap.toMatrix' (shiftIncl (n := n) N (d i)))ᵀ := by
  obtain ⟨c, hc0, hct, rfl⟩ := uniform_eq_smul_indepSum hn d ρ hρ hρ0 hinj
  rw [mean_smul_measure c hc0 hct, cov_smul_measure c hc0 hct]
  exact ⟨mean_indepSum_koz hn d, cov_indepSum_koz hn d⟩

end PolytopeProduct

end Centroids
end ExteriorConvex
