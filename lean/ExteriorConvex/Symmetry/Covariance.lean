/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The covariance clauses of `thm-beta-continuous` and `thm-beta-lattice` (1)

Formalisation of the clause "its covariance matrix is β-invariant" in `thm-beta-continuous`
(uniform measure on `Koz(n)`, `n ≥ 3`) and "the lattice-point covariance is β-invariant" in
`thm-beta-lattice` (1) (`n` prime), `article/exterior-convex_article3_draft_4.org`; roadmap
item 2 of `working-notes/lean-roadmap-article3-2026-10-21.org`.

**Generic layer** (any `d`, any affine `A : ℝ^d → ℝ^d`, `M = LinearMap.toMatrix' A.linear`):
* `mean ν`, `cov ν`: centroid and covariance matrix of a measure `ν`, **normalised by the total
  mass** (i.e. those of the probability measure `ν/ν(ℝ^d)`, as in the paper's "uniform measure");
  `cov ν i j = (1/|ν|) ∫ (xᵢ − mᵢ)(xⱼ − mⱼ) dν`.
* `mean_fixed`: if `A_*ν = ν` (`ν` finite, non-zero, coordinates integrable) then `A(m) = m`.
* `cov_fixed`: if moreover the products `xᵢxⱼ` are integrable, then **`M Σ Mᵀ = Σ`**.
  (`M Σ Mᵀ` is the covariance of `A_*ν`, so this is "Σ is A-invariant".)
* `meanF L`, `covF L`, `meanF_fixed`, `covF_fixed`: the same for the uniform measure on a
  non-empty `Finset L`, under `Set.BijOn A L L`.

**Specialisation to β** (`Symmetry/Beta.lean`, `Symmetry/BetaMeasure.lean`), coordinates the
library's degree-0-inclusive `f`-coordinates `Fin (n + 1) → ℝ`:
* `beta_linear`: the linear part of `beta n` is `betaLin n`; `betaMatrix_apply` its matrix
  (row `i ∈ [2, n−2]` is `C(n,i)/n·e_{n−1} − e_{n−i}`, every other row `e_i`).
* `beta_mean_kozMeasure`: the centroid of `Koz(n)` is β-fixed (`n ≥ 3`).
* `cov_kozMeasure_beta`: **`thm-beta-continuous`, covariance clause**:
  `L Σ Lᵀ = Σ` for `Σ = cov (kozMeasure n)`, `n ≥ 3`. Integrability: continuous integrands on
  the compact chart (`integrable_kozMeasure_of_continuous`).
* `covF_beta`: the same for the uniform measure on any finite β-stable `L` (`∀ x ∈ L, β x ∈ L`).
* `covF_latticePts_beta_of_prime`: **`thm-beta-lattice` (1), covariance clause**, `n` prime,
  `n ≥ 3`, for any `Finset` `L` with `↑L = 𝓛_n` (non-emptiness from `witness_mem_latticePts`).

**Form of the statement.** The paper does not say in which form "β-invariant" is meant; the
Lean form is `L Σ Lᵀ = Σ` in `f`-coordinates. In μ-coordinates (`μ_k = f_k/C(n,k)`) the
covariance is `D Σ D` with `D = diag(1/C(n,k))` and β's linear part is `D L D⁻¹`, so the
μ-coordinate statement is the same identity conjugated by `D`; it is not stated separately.
The rows/columns 0 and 1 of `Σ` vanish (`f₀ = 1`, `f₁ = n` on `Koz(n)`) — harmless, not used.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Symmetry.BetaMeasure

open Finset MeasureTheory Matrix

namespace ExteriorConvex
namespace Covariance

variable {d : ℕ}

/-! ## Mean and covariance of a finite measure on `ℝ^d` -/

/-- The mean (centroid) of a measure `ν` on `ℝ^d`, normalised by the total mass. -/
noncomputable def mean (ν : Measure (Fin d → ℝ)) : Fin d → ℝ :=
  fun i => (∫ x, x i ∂ν) / ν.real Set.univ

/-- The covariance matrix of `ν`, normalised by the total mass (that of the probability
measure `ν / ν(ℝ^d)`): `Σᵢⱼ = (1/|ν|) ∫ (xᵢ − mᵢ)(xⱼ − mⱼ) dν`. -/
noncomputable def cov (ν : Measure (Fin d → ℝ)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => (∫ x, (x i - mean ν i) * (x j - mean ν j) ∂ν) / ν.real Set.univ

theorem affine_apply_eq (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (x : Fin d → ℝ) (i : Fin d) :
    A x i = ∑ j, LinearMap.toMatrix' A.linear i j * x j + A 0 i := by
  have h := congrFun (congrFun (AffineMap.decomp A) x) i
  rw [h]
  simp only [Pi.add_apply]
  congr 1
  rw [← LinearMap.toMatrix'_mulVec, Matrix.mulVec, dotProduct]

theorem affine_sub_apply (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (x y : Fin d → ℝ) (i : Fin d) :
    A x i - A y i = ∑ j, LinearMap.toMatrix' A.linear i j * (x j - y j) := by
  rw [affine_apply_eq A x, affine_apply_eq A y]
  simp only [mul_sub, sum_sub_distrib]
  ring

variable {ν : Measure (Fin d → ℝ)}

/-- An affine map preserving a finite measure (with integrable coordinates) fixes its mean. -/
theorem mean_fixed [IsFiniteMeasure ν] (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin d → ℝ))
    (hA : ν.map A = ν) (hν : ν Set.univ ≠ 0)
    (hint : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν) :
    A (mean ν) = mean ν := by
  have hAm : Measurable A := A.continuous_of_finiteDimensional.measurable
  have h0 : ν.real Set.univ ≠ 0 := by
    rw [measureReal_def]
    exact ENNReal.toReal_ne_zero.mpr ⟨hν, measure_ne_top ν _⟩
  funext i
  have hre : ∫ x, x i ∂ν = ∫ x, A x i ∂ν := by
    conv_lhs => rw [← hA]
    rw [integral_map hAm.aemeasurable
      (continuous_apply i).aestronglyMeasurable]
  have hsum : ∫ x, A x i ∂ν =
      ∑ j, LinearMap.toMatrix' A.linear i j * ∫ x, x j ∂ν + ν.real Set.univ * A 0 i := by
    rw [show (fun x => A x i) = fun x =>
        ∑ j, LinearMap.toMatrix' A.linear i j * x j + A 0 i from
        funext fun x => affine_apply_eq A x i]
    rw [integral_add (integrable_finsetSum _ fun j _ => (hint j).const_mul _)
      (integrable_const _), integral_finsetSum _ fun j _ => (hint j).const_mul _,
      integral_const, smul_eq_mul]
    simp_rw [integral_const_mul]
  rw [affine_apply_eq A _ i]
  simp only [mean]
  rw [hre, hsum, add_div, sum_div, mul_div_cancel_left₀ _ h0]
  simp only [mul_div_assoc]

theorem integrable_centred_mul [IsFiniteMeasure ν]
    (hint : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hint2 : ∀ i j, Integrable (fun x : Fin d → ℝ => x i * x j) ν) (m : Fin d → ℝ)
    (a b : Fin d) : Integrable (fun x : Fin d → ℝ => (x a - m a) * (x b - m b)) ν := by
  have e : (fun x : Fin d → ℝ => (x a - m a) * (x b - m b)) = fun x =>
      x a * x b - m b * x a - m a * x b + m a * m b := by
    funext x; ring
  rw [e]
  exact (((hint2 a b).sub ((hint a).const_mul _)).sub ((hint b).const_mul _)).add
    (integrable_const _)

/-- **Covariance is invariant under a measure-preserving affine map**: if `A` preserves the
finite non-zero measure `ν` (with square-integrable coordinates) and `M` is the matrix of the
linear part of `A`, then `M Σ Mᵀ = Σ`.  (`M Σ Mᵀ` is the covariance of the pushforward `A_*ν`,
so this is the statement "the covariance matrix is `A`-invariant".) -/
theorem cov_fixed [IsFiniteMeasure ν] (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin d → ℝ))
    (hA : ν.map A = ν) (hν : ν Set.univ ≠ 0)
    (hint : ∀ i, Integrable (fun x : Fin d → ℝ => x i) ν)
    (hint2 : ∀ i j, Integrable (fun x : Fin d → ℝ => x i * x j) ν) :
    LinearMap.toMatrix' A.linear * cov ν * (LinearMap.toMatrix' A.linear)ᵀ = cov ν := by
  set M := LinearMap.toMatrix' A.linear
  set m := mean ν
  have hAm : Measurable A := A.continuous_of_finiteDimensional.measurable
  have hfix : A m = m := mean_fixed A hA hν hint
  have ig := integrable_centred_mul hint hint2 m
  ext i j
  have hre : ∫ x, (x i - m i) * (x j - m j) ∂ν =
      ∫ x, (A x i - m i) * (A x j - m j) ∂ν := by
    conv_lhs => rw [← hA]
    rw [integral_map hAm.aemeasurable (by fun_prop)]
  have hpt : ∀ x : Fin d → ℝ, (A x i - m i) * (A x j - m j) =
      ∑ a, ∑ b, M i a * M j b * ((x a - m a) * (x b - m b)) := by
    intro x
    conv_lhs => rw [← hfix]
    rw [affine_sub_apply A x m i, affine_sub_apply A x m j, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have hint3 : ∫ x, (A x i - m i) * (A x j - m j) ∂ν =
      ∑ a, ∑ b, M i a * M j b * ∫ x, (x a - m a) * (x b - m b) ∂ν := by
    simp_rw [hpt]
    rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => (ig a b).const_mul _]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum _ fun b _ => (ig a b).const_mul _]
    simp_rw [integral_const_mul]
  simp only [cov, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [hre, hint3, Finset.sum_comm, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul, Finset.sum_div]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-! ## The discrete version: uniform measure on a finite set -/

/-- The mean (centroid) of a finite set `L ⊆ ℝ^d`, uniform weights. -/
noncomputable def meanF (L : Finset (Fin d → ℝ)) : Fin d → ℝ :=
  fun i => (∑ x ∈ L, x i) / #L

/-- The covariance matrix of the uniform measure on a finite set `L ⊆ ℝ^d`:
`Σᵢⱼ = (1/|L|) ∑_{x∈L} (xᵢ − mᵢ)(xⱼ − mⱼ)`. -/
noncomputable def covF (L : Finset (Fin d → ℝ)) : Matrix (Fin d) (Fin d) ℝ :=
  Matrix.of fun i j => (∑ x ∈ L, (x i - meanF L i) * (x j - meanF L j)) / #L

theorem sum_comp_of_bijOn {L : Finset (Fin d → ℝ)} {A : (Fin d → ℝ) → (Fin d → ℝ)}
    (hA : Set.BijOn A (L : Set (Fin d → ℝ)) L) (F : (Fin d → ℝ) → ℝ) :
    ∑ x ∈ L, F (A x) = ∑ x ∈ L, F x :=
  Finset.sum_nbij A (fun _ hx => hA.mapsTo hx) hA.injOn hA.surjOn (fun _ _ => rfl)

/-- An affine map permuting a non-empty finite set fixes its centroid. -/
theorem meanF_fixed {L : Finset (Fin d → ℝ)} (hL : L.Nonempty)
    (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (hA : Set.BijOn A (L : Set (Fin d → ℝ)) L) :
    A (meanF L) = meanF L := by
  have h0 : (#L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.card_pos.ne'
  funext i
  have hre : ∑ x ∈ L, x i = ∑ x ∈ L, A x i := (sum_comp_of_bijOn hA (fun x => x i)).symm
  have hsum : ∑ x ∈ L, A x i =
      ∑ j, LinearMap.toMatrix' A.linear i j * ∑ x ∈ L, x j + #L * A 0 i := by
    rw [Finset.sum_congr rfl fun x _ => affine_apply_eq A x i, Finset.sum_add_distrib,
      Finset.sum_const, nsmul_eq_mul, Finset.sum_comm]
    simp_rw [Finset.mul_sum]
  rw [affine_apply_eq A _ i]
  simp only [meanF]
  rw [hre, hsum, add_div, sum_div, mul_div_cancel_left₀ _ h0]
  simp only [mul_div_assoc]

/-- **Discrete covariance invariance**: an affine map `A` permuting a non-empty finite set
`L` satisfies `M Σ Mᵀ = Σ` for the covariance `Σ` of the uniform measure on `L`, `M` the
matrix of the linear part of `A`. -/
theorem covF_fixed {L : Finset (Fin d → ℝ)} (hL : L.Nonempty)
    (A : (Fin d → ℝ) →ᵃ[ℝ] (Fin d → ℝ)) (hA : Set.BijOn A (L : Set (Fin d → ℝ)) L) :
    LinearMap.toMatrix' A.linear * covF L * (LinearMap.toMatrix' A.linear)ᵀ = covF L := by
  set M := LinearMap.toMatrix' A.linear
  set m := meanF L
  have hfix : A m = m := meanF_fixed hL A hA
  ext i j
  have hre : ∑ x ∈ L, (x i - m i) * (x j - m j) = ∑ x ∈ L, (A x i - m i) * (A x j - m j) :=
    (sum_comp_of_bijOn hA (fun x => (x i - m i) * (x j - m j))).symm
  have hpt : ∀ x : Fin d → ℝ, (A x i - m i) * (A x j - m j) =
      ∑ a, ∑ b, M i a * M j b * ((x a - m a) * (x b - m b)) := by
    intro x
    conv_lhs => rw [← hfix]
    rw [affine_sub_apply A x m i, affine_sub_apply A x m j, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  have rhs : (∑ x ∈ L, (x i - m i) * (x j - m j)) / #L =
      ∑ a, ∑ b, M i a * M j b * ((∑ x ∈ L, (x a - m a) * (x b - m b)) / #L) := by
    rw [hre, Finset.sum_congr rfl fun x _ => hpt x, Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← Finset.mul_sum, mul_div_assoc]
  simp only [covF, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
  rw [rhs, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-! ## `thm-beta-continuous` and `thm-beta-lattice` (1): the covariance clauses -/

open Beta BetaMeasure

variable {n : ℕ}

theorem beta_linear : (beta n).linear = betaLin n := by
  ext x : 1
  simp [beta]

/-- The matrix of the linear part of `β` (in degree-0-inclusive `f`-coordinates):
row `i ∈ [2, n−2]` is `C(n,i)/n · e_{n−1} − e_{n−i}`, every other row is `e_i`. -/
theorem betaMatrix_apply (i j : Fin (n + 1)) :
    LinearMap.toMatrix' (betaLin n) i j =
      if 2 ≤ i.val ∧ i.val ≤ n - 2 then
        (n.choose i.val : ℝ) / n * (if j = penult n then 1 else 0) -
          (if j = refl n i then 1 else 0)
      else if j = i then 1 else 0 := by
  rw [LinearMap.toMatrix'_apply, betaLin_apply]
  split_ifs <;> simp_all [eq_comm]

theorem integrable_kozMeasure_of_continuous (hn : 1 ≤ n) {F : (Fin (n + 1) → ℝ) → ℝ}
    (hF : Continuous F) : Integrable F (kozMeasure n) := by
  rw [kozMeasure, (measurableEmbedding_lift hn).integrable_map_iff]
  exact (hF.comp continuous_lift).continuousOn.integrableOn_compact (isCompact_kozProj hn)

theorem kozMeasure_univ_ne_zero (hn : 1 ≤ n) : kozMeasure n Set.univ ≠ 0 := by
  rw [kozMeasure_univ hn, ne_eq, ENNReal.ofReal_eq_zero, not_le]
  refine div_pos (prod_pos fun j hj => ?_) (Nat.cast_pos.mpr (Nat.factorial_pos _))
  rw [mem_Icc] at hj
  exact Nat.cast_pos.mpr (Nat.choose_pos hj.2)

/-- `thm-beta-continuous`: the centroid of the uniform measure on `Koz(n)` is `β`-fixed. -/
theorem beta_mean_kozMeasure (hn : 3 ≤ n) :
    beta n (mean (kozMeasure n)) = mean (kozMeasure n) := by
  have := isFiniteMeasure_kozMeasure (n := n) (by omega)
  exact mean_fixed (beta n) (kozMeasure_map_beta hn) (kozMeasure_univ_ne_zero (by omega))
    (fun i => integrable_kozMeasure_of_continuous (by omega) (continuous_apply i))

/-- **`thm-beta-continuous`, covariance clause**: for `n ≥ 3` the covariance matrix `Σ` of the
uniform measure on `Koz(n)` is `β`-invariant, `L Σ Lᵀ = Σ` with `L` the matrix of the linear
part of `β` (`betaMatrix_apply`). -/
theorem cov_kozMeasure_beta (hn : 3 ≤ n) :
    LinearMap.toMatrix' (betaLin n) * cov (kozMeasure n) * (LinearMap.toMatrix' (betaLin n))ᵀ =
      cov (kozMeasure n) := by
  have := isFiniteMeasure_kozMeasure (n := n) (by omega)
  rw [← beta_linear]
  exact cov_fixed (beta n) (kozMeasure_map_beta hn) (kozMeasure_univ_ne_zero (by omega))
    (fun i => integrable_kozMeasure_of_continuous (by omega) (continuous_apply i))
    (fun i j => integrable_kozMeasure_of_continuous (by omega)
      ((continuous_apply i).mul (continuous_apply j)))

/-- Covariance invariance for any finite `β`-stable set (`β` is an involution, so mapping
`L` into itself already makes it a bijection of `L`). -/
theorem covF_beta (L : Finset (Fin (n + 1) → ℝ)) (hne : L.Nonempty)
    (hL : ∀ x ∈ L, beta n x ∈ L) :
    LinearMap.toMatrix' (betaLin n) * covF L * (LinearMap.toMatrix' (betaLin n))ᵀ = covF L := by
  have hbij : Set.BijOn (beta n) (L : Set (Fin (n + 1) → ℝ)) L :=
    ⟨fun x hx => hL x hx, beta_involutive.injective.injOn,
      fun y hy => ⟨beta n y, hL y hy, beta_beta y⟩⟩
  rw [← beta_linear]
  exact covF_fixed hne (beta n) hbij

/-- **`thm-beta-lattice` (1), covariance clause**: for `n` prime (`n ≥ 3`) the covariance of the
uniform measure on the lattice points `𝓛_n` (any `Finset` `L` enumerating them) is
`β`-invariant: `L Σ Lᵀ = Σ`. -/
theorem covF_latticePts_beta_of_prime (hp : n.Prime) (hn : 3 ≤ n)
    (L : Finset (Fin (n + 1) → ℝ)) (hL : (L : Set (Fin (n + 1) → ℝ)) = latticePts n) :
    LinearMap.toMatrix' (betaLin n) * covF L * (LinearMap.toMatrix' (betaLin n))ᵀ = covF L := by
  have hne : L.Nonempty := ⟨witness n, by
    rw [← Finset.mem_coe, hL]; exact witness_mem_latticePts hn⟩
  rw [← beta_linear]
  refine covF_fixed hne (beta n) ?_
  rw [hL]
  exact beta_bijOn_latticePts_of_prime hp hn

end Covariance
end ExteriorConvex

