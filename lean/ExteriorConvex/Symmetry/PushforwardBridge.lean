/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# `prop-pushforward` (2) in the product regime, unconditionally

Bridge between `Lattice/ProductRegime.lean` (`prop-product-regime`) and
`Symmetry/Centroids.lean` (`prop-pushforward`), article 3
(`article/exterior-convex_article3_draft_4.org`). `Centroids.lean` states the three clauses of
`prop-pushforward` (2) against explicit hypotheses on the sumset map
`sumShift N d x = ∑ᵢ shift^{dᵢ} xᵢ`; here they are discharged under `ProdGaps n d`
(every two shifts, in index order, at least `n − 1` apart), `1 ≤ n` and `dᵢ + n ≤ N`.

* `sumShift_eq_glue`: `sumShift N d` *is* `ProductRegime.glue N d` (as functions).
* `sumShift_injOn_koz`: in the product regime `sumShift` is injective on `Koz(n)^r`
  (`Koz(n) = conv S_n`), being the inverse of the block projection `Φ` (`invOn_glue_proj`).
* `sumShift_bijOn_lattice`: it maps `𝓛_n^r` (`Beta.latticePts`, the real-valued lattice
  points) bijectively onto `conv FF(n; d⃗) ∩ ℤ^{N+1}`; via `main` (`conv FF = ∑ shift Koz(n)`),
  `castR_glueZ` and `castR_proj` (Φ preserves integrality).
* `pushforward_ff_productRegime` (`meanF_covF_ff`), `pushforward_lattice_productRegime`
  (`meanF_covF_lattice`), `pushforward_koz_productRegime` (`mean_cov_uniform_productRegime`):
  centroid and covariance of `FF(n; d⃗)`, of the lattice points of `Koz(n; d⃗)`, and of the
  uniform measure on `Koz(n; d⃗)` are the shifted sums of the rank-one ones.

**Hypotheses.** Only `ProdGaps n d`, `dᵢ + n ≤ N`, and the dimension bound of each clause
(`1 ≤ n`; `3 ≤ n` for the lattice clause, inherited from `meanF_covF_lattice`, whose
non-emptiness witness needs it), plus the uniformity hypotheses on `ρ` for the polytope clause.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Lattice.ProductRegime
import ExteriorConvex.Lattice.BetaBridge
import ExteriorConvex.Symmetry.Centroids

open Finset MeasureTheory Matrix
open scoped Pointwise

namespace ExteriorConvex

namespace PushforwardBridge

open Covariance BetaMeasure KozVolume Centroids

variable {n N r : ℕ} {d : Fin r → ℕ}

/-- The sumset map of `Centroids.lean` is the glue map of `ProductRegime.lean`. -/
theorem sumShift_eq_glue (d : Fin r → ℕ) :
    ⇑(sumShift (n := n) N d) = ProductRegime.glue N d := by
  funext x
  rw [sumShift_apply]
  rfl

/-- In the product regime the sumset map is injective on `Koz(n)^r`. -/
theorem sumShift_injOn_koz (hn : 1 ≤ n) (hg : ProductRegime.ProdGaps n d)
    (hN : ∀ i, d i + n ≤ N) :
    Set.InjOn (sumShift N d) (Set.univ.pi fun _ : Fin r => convexHull ℝ (Sset n)) := by
  have hI := ProductRegime.invOn_glue_proj (N := N) hn hg hN (1 : ℝ)
  have := hI.2.injOn
  rw [sumShift_eq_glue]
  simpa only [_root_.one_smul] using this

/-- `conv(S_n) = conv(skelSet n)` (both are the LYM chain). -/
theorem hull_Sset_eq_hull_skel (hn : 1 ≤ n) :
    convexHull ℝ (Sset n) = convexHull ℝ (skelSet n) := by
  rw [hull_Sset_eq hn, hull_skel_eq hn]

/-- In the product regime the sumset map is a bijection from `𝓛_n^r` onto the lattice points
of `conv FF(n; d⃗) = Koz(n; d⃗)`. -/
theorem sumShift_bijOn_lattice (hn : 1 ≤ n) (hg : ProductRegime.ProdGaps n d)
    (hN : ∀ i, d i + n ≤ N) :
    Set.BijOn (sumShift N d) (Set.univ.pi fun _ : Fin r => Beta.latticePts n)
      {x | x ∈ convexHull ℝ (ffSet n N d) ∧ Beta.IsIntPt x} := by
  have hsub : Set.univ.pi (fun _ : Fin r => Beta.latticePts n) ⊆
      Set.univ.pi fun _ : Fin r => convexHull ℝ (Sset n) := fun p hp i _ => by
    rw [hull_Sset_eq_hull_skel hn]; exact (hp i (Set.mem_univ _)).1
  have hI := ProductRegime.invOn_glue_proj (N := N) hn hg hN (1 : ℝ)
  have hB := ProductRegime.bijOn_proj (N := N) hn hg hN (1 : ℝ)
  simp only [_root_.one_smul] at hI hB
  have hinjG := sumShift_injOn_koz (N := N) hn hg hN
  rw [sumShift_eq_glue] at hinjG
  rw [main, sumShift_eq_glue]
  refine ⟨?_, hinjG.mono hsub, ?_⟩
  · intro p hp
    refine ⟨?_, ?_⟩
    · rw [ProductRegime.sum_image_eq_glue_image]
      exact ⟨p, hsub hp, rfl⟩
    · have : ∀ i, ∃ z : Fin (n + 1) → ℤ, p i = Lattice.castR z := fun i => by
        choose z hz using (hp i (Set.mem_univ _)).2
        exact ⟨z, funext hz⟩
      choose z hz using this
      have : p = fun i => Lattice.castR (z i) := funext hz
      rw [this, ← ProductRegime.castR_glueZ]
      exact fun j => ⟨_, rfl⟩
  · rintro x ⟨hx, hint⟩
    choose w hw using hint
    have hxw : x = Lattice.castR w := funext hw
    refine ⟨ProductRegime.proj n d (1 : ℝ) x, fun i _ => ⟨?_, ?_⟩, hI.1 hx⟩
    · rw [← hull_Sset_eq_hull_skel hn]; exact hB.mapsTo hx i (Set.mem_univ _)
    · intro k
      refine ⟨ProductRegime.proj n d (1 : ℤ) w i k, ?_⟩
      have := congrFun (ProductRegime.castR_proj (n := n) (d := d) (1 : ℤ) w i) k
      rw [Lattice.castR_apply, Int.cast_one] at this
      rw [hxw, ← this]

/-- **`prop-pushforward` (2), the `FF` clause, product regime**: centroid and covariance of
`FF(n; d⃗)` are `∑ shift^{dᵢ} c(S_n)` and `∑ Pᵢ Σ(S_n) Pᵢᵀ`. -/
theorem pushforward_ff_productRegime (hn : 1 ≤ n) (hg : ProductRegime.ProdGaps n d)
    (hN : ∀ i, d i + n ≤ N) (F : Finset (Fin (N + 1) → ℝ))
    (hF : (F : Set (Fin (N + 1) → ℝ)) = ffSet n N d) :
    meanF F = ∑ i, shiftIncl N (d i) (meanF (Centroids.SnF n)) ∧
      covF F = ∑ i, LinearMap.toMatrix' (shiftIncl (n := n) N (d i)) * covF (Centroids.SnF n) *
        (LinearMap.toMatrix' (shiftIncl (n := n) N (d i)))ᵀ :=
  meanF_covF_ff hn d F hF ((sumShift_injOn_koz hn hg hN).mono
    (Set.pi_mono fun _ _ => subset_convexHull ℝ _))

/-- **`prop-pushforward` (2), the lattice-point clause, product regime**: the lattice-point
centroid and covariance of `Koz(n; d⃗)` are the shifted sums of those of `Koz(n)`. -/
theorem pushforward_lattice_productRegime (hn : 3 ≤ n) (hg : ProductRegime.ProdGaps n d)
    (hN : ∀ i, d i + n ≤ N) (Ln : Finset (Fin (n + 1) → ℝ))
    (hLn : (Ln : Set (Fin (n + 1) → ℝ)) = Beta.latticePts n) (F : Finset (Fin (N + 1) → ℝ))
    (hF : (F : Set (Fin (N + 1) → ℝ)) =
      {x | x ∈ convexHull ℝ (ffSet n N d) ∧ Beta.IsIntPt x}) :
    meanF F = ∑ i, shiftIncl N (d i) (meanF Ln) ∧
      covF F = ∑ i, LinearMap.toMatrix' (shiftIncl (n := n) N (d i)) * covF Ln *
        (LinearMap.toMatrix' (shiftIncl (n := n) N (d i)))ᵀ :=
  meanF_covF_lattice hn d Ln hLn F hF (sumShift_bijOn_lattice (by omega) hg hN)

/-- **`prop-pushforward` (2), the polytope clause, product regime**: for the uniform measure
`ρ` on `Koz(n; d⃗)` (any chart, non-degenerate) the centroid is `∑ shift^{dᵢ} c(Koz(n))` and the
covariance `∑ Pᵢ Σ(Koz(n)) Pᵢᵀ`. -/
theorem pushforward_koz_productRegime (hn : 1 ≤ n) (hg : ProductRegime.ProdGaps n d)
    (hN : ∀ i, d i + n ≤ N)
    (ρ : Measure (Fin (N + 1) → ℝ)) (hρ : IsUniformOn ρ (convexHull ℝ (ffSet n N d)))
    (hρ0 : ρ ≠ 0) :
    mean ρ = ∑ i, shiftIncl N (d i) (mean (kozMeasure n)) ∧
      cov ρ = ∑ i, LinearMap.toMatrix' (shiftIncl (n := n) N (d i)) * cov (kozMeasure n) *
        (LinearMap.toMatrix' (shiftIncl (n := n) N (d i)))ᵀ := by
  refine mean_cov_uniform_productRegime hn d ρ hρ hρ0 ?_
  have := sumShift_injOn_koz (N := N) hn hg hN
  rwa [hull_Sset_eq_hull_skel hn] at this

end PushforwardBridge

end ExteriorConvex
