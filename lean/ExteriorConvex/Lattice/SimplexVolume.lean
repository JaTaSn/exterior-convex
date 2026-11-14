/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The volume of the corner simplex, and the Euclidean volume of `Koz(n)`

Completes the stretch target left open in `Lattice/Volume.lean`: the Euclidean form of
`prop-simplex-volume` (`article/exterior-convex_article3_draft_4.org`) for `Koz(n)`,
`vol(Koz(n)) = ∏_{k=2}^n C(n,k) / (n−1)!`, cf. `working-notes/kozlov-polytope-volume-and-ehrhart.org`,
section "Volume".

* `lowerSimplex m c = {x ∈ ℝ^m : x ≥ 0, ∑ x ≤ c}`; `volume_lowerSimplex`:
  its Lebesgue measure is `c^m/m!` for `c ≥ 0` (and `0` for `c < 0`). Proof by induction on
  `m`, slicing off the coordinate `x₀` (`MeasurableEquiv.piFinSuccAbove`, Tonelli
  `Measure.prod_apply`) and `∫₀^c (c−t)^m/m! dt = c^{m+1}/(m+1)!`.
* `cornerSimplex_eq`: Volume.lean's `cornerSimplex m = conv{0, e₀, …, e_{m−1}}` equals
  `lowerSimplex m 1`; `volume_cornerSimplex`: `vol = 1/m!` (not in Mathlib).
* `volume_kozProj_eq`: `vol(kozProj n) = ∏_{k=2}^n C(n,k)/(n−1)!` (`n ≥ 1`), from
  `volume_kozProj`.
* `sum_sq_sub_freeProj`: on the plane `P = {x₀ = 1, x₁ = n}` the free projection preserves
  squared Euclidean distances, so `kozProj n` is an isometric copy of `Koz(n) ⊆ P`.

**What is certified.**  `vol` is Lebesgue measure on `ℝ^{n−1}` (free coordinates `f₂..fₙ`) of
the projected simplex; the isometry lemma says this is the Euclidean `(n−1)`-volume of `Koz(n)`
in its affine hull, but the statement "Hausdorff measure on `P` equals the pushforward" is not
formalised. Combined with `vdiff_det` this gives `vol = NV/(n−1)!` with `NV = ∏ C(n,k)`; the
notion of lattice-normalised volume itself is still not a Lean definition (see `Volume.lean`).

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Lattice.Volume

open Finset MeasureTheory

namespace ExteriorConvex

namespace KozVolume

variable {n : ℕ}

/-- The scaled corner simplex `{x ∈ ℝ^m : x ≥ 0, ∑ x ≤ c}`. -/
def lowerSimplex (m : ℕ) (c : ℝ) : Set (Fin m → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ c}

theorem measurableSet_lowerSimplex (m : ℕ) (c : ℝ) : MeasurableSet (lowerSimplex m c) := by
  have : lowerSimplex m c = (⋂ i, {x : Fin m → ℝ | 0 ≤ x i}) ∩ {x | ∑ i, x i ≤ c} := by
    ext x; simp [lowerSimplex]
  rw [this]
  refine (MeasurableSet.iInter fun i => measurableSet_le measurable_const
    (measurable_pi_apply i)).inter (measurableSet_le ?_ measurable_const)
  exact Finset.measurable_sum _ fun i _ => measurable_pi_apply i

theorem lowerSimplex_eq_empty {m : ℕ} {c : ℝ} (hc : c < 0) : lowerSimplex m c = ∅ := by
  ext x
  simp only [lowerSimplex, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and,
    not_le]
  intro h
  exact hc.trans_le (Finset.sum_nonneg fun i _ => h i)

theorem volume_lowerSimplex (m : ℕ) (c : ℝ) :
    volume (lowerSimplex m c) =
      if 0 ≤ c then ENNReal.ofReal (c ^ m / m.factorial) else 0 := by
  induction m generalizing c with
  | zero =>
    split_ifs with hc
    · have : lowerSimplex 0 c = Set.univ := by
        ext x; simp [lowerSimplex, hc]
      rw [this, volume_pi, Measure.pi_univ]; simp
    · rw [lowerSimplex_eq_empty (not_le.mp hc), measure_empty]
  | succ m ih =>
    split_ifs with hc
    swap
    · rw [lowerSimplex_eq_empty (not_le.mp hc), measure_empty]
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have hmp := volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    let S : Set (ℝ × (Fin m → ℝ)) := {p | 0 ≤ p.1 ∧ p.2 ∈ lowerSimplex m (c - p.1)}
    have hS : MeasurableSet S := by
      have : S = {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1} ∩
          ((⋂ i, {p : ℝ × (Fin m → ℝ) | 0 ≤ p.2 i}) ∩ {p | ∑ i, p.2 i + p.1 ≤ c}) := by
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
            (g := fun _ => c) (by fun_prop) measurable_const))
    have hpre : lowerSimplex (m + 1) c = e ⁻¹' S := by
      ext x
      simp only [lowerSimplex, Set.mem_ofPred_eq, Set.mem_preimage, S, e,
        MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        Fin.removeNth, Fin.succAbove_zero, Fin.sum_univ_succ, Fin.forall_fin_succ]
      constructor
      · rintro ⟨⟨h0, h1⟩, h2⟩; exact ⟨h0, h1, by linarith⟩
      · rintro ⟨h0, h1, h2⟩; exact ⟨⟨h0, h1⟩, by linarith⟩
    rw [hpre, hmp.measure_preimage hS.nullMeasurableSet]
    rw [Measure.volume_eq_prod, Measure.prod_apply hS]
    have hslice : ∀ t : ℝ, volume (Prod.mk t ⁻¹' S) =
        (Set.Icc 0 c).indicator (fun t => ENNReal.ofReal ((c - t) ^ m / m.factorial)) t := by
      intro t
      by_cases ht : 0 ≤ t
      · have : Prod.mk t ⁻¹' S = lowerSimplex m (c - t) := by
          ext y; simp [S, ht]
        rw [this, ih]
        by_cases htc : t ≤ c
        · rw [Set.indicator_of_mem (show t ∈ Set.Icc 0 c from ⟨ht, htc⟩)]
          simp only [show 0 ≤ c - t by linarith, ↓reduceIte]
        · rw [Set.indicator_of_notMem (fun h => htc h.2)]
          simp only [show ¬ 0 ≤ c - t by linarith, ↓reduceIte]
      · have : Prod.mk t ⁻¹' S = ∅ := by
          ext y; simp [S, ht]
        rw [this, measure_empty, Set.indicator_of_notMem (fun h => ht h.1)]
    simp_rw [hslice]
    rw [lintegral_indicator measurableSet_Icc]
    have hint : IntegrableOn (fun t : ℝ => (c - t) ^ m / m.factorial) (Set.Icc 0 c) :=
      (by fun_prop : Continuous fun t : ℝ => (c - t) ^ m / m.factorial).integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hint]
    swap
    · refine (ae_restrict_iff' measurableSet_Icc).mpr (Filter.Eventually.of_forall fun t ht => ?_)
      have : 0 ≤ c - t := by linarith [ht.2]
      positivity
    congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hc,
      intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left
        (fun t => t ^ m), integral_pow, Nat.factorial_succ]
    push_cast
    field_simp
    ring

theorem convex_lowerSimplex (m : ℕ) (c : ℝ) : Convex ℝ (lowerSimplex m c) := by
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ a b ha hb hab
  refine ⟨fun i => ?_, ?_⟩
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    have := hx0 i; have := hy0 i; positivity
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum]
    calc a * ∑ i, x i + b * ∑ i, y i ≤ a * c + b * c :=
          add_le_add (mul_le_mul_of_nonneg_left hx1 ha) (mul_le_mul_of_nonneg_left hy1 hb)
      _ = c := by rw [← add_mul, hab, one_mul]

/-- The corner simplex `conv{0, e₀, …, e_{m−1}}` (`cornerSimplex`, from `Lattice/Volume.lean`)
is `{x ≥ 0, ∑ x ≤ 1}`. -/
theorem cornerSimplex_eq (m : ℕ) : cornerSimplex m = lowerSimplex m 1 := by
  apply Set.Subset.antisymm
  · refine convexHull_min ?_ (convex_lowerSimplex m 1)
    rintro _ (rfl | ⟨b, rfl⟩)
    · exact ⟨fun _ => le_rfl, by simp⟩
    · refine ⟨fun i => ?_, by simp⟩
      by_cases h : i = b
      · subst h; simp
      · simp [h]
  · rintro x ⟨hx0, hx1⟩
    let w : Fin (m + 1) → ℝ := Fin.cons (1 - ∑ i, x i) x
    let z : Fin (m + 1) → (Fin m → ℝ) := Fin.cons 0 fun b => Pi.single b 1
    have hmem := (convex_convexHull ℝ (insert (0 : Fin m → ℝ)
      (Set.range fun b : Fin m => Pi.single b (1 : ℝ)))).sum_mem (t := Finset.univ) (w := w)
      (z := z) ?_ ?_ ?_
    · rw [cornerSimplex]
      convert hmem using 1
      rw [Fin.sum_univ_succ]
      ext j
      simp [w, z, Finset.sum_apply, Pi.single_apply]
    · intro i _
      refine Fin.cases ?_ (fun b => ?_) i
      · simp only [w, Fin.cons_zero]; linarith
      · simp only [w, Fin.cons_succ]; exact hx0 b
    · simp [w, Fin.sum_univ_succ]
    · intro i _
      refine Fin.cases ?_ (fun b => ?_) i
      · exact subset_convexHull ℝ _ (Set.mem_insert _ _)
      · exact subset_convexHull ℝ _ (Set.mem_insert_of_mem _ ⟨b, rfl⟩)

/-- **The volume of the corner simplex**: `vol{x ∈ ℝ^m : x ≥ 0, ∑ x ≤ 1} = 1/m!`. -/
theorem volume_cornerSimplex (m : ℕ) :
    volume (cornerSimplex m) = ENNReal.ofReal (1 / m.factorial) := by
  rw [cornerSimplex_eq, volume_lowerSimplex]
  simp

/-- **`prop-simplex-volume` for `Koz(n)`, Euclidean form**: the projection of `Koz(n)` to the
free coordinates `f₂, …, fₙ` has Lebesgue volume `∏_{k=2}^n C(n,k) / (n−1)!`. -/
theorem volume_kozProj_eq (hn : 1 ≤ n) :
    volume (kozProj n) =
      ENNReal.ofReal ((∏ k ∈ Icc 2 n, (n.choose k : ℝ)) / (n - 1).factorial) := by
  rw [volume_kozProj hn, volume_cornerSimplex, ← ENNReal.ofReal_mul
    (prod_nonneg fun _ _ => Nat.cast_nonneg _), mul_one_div]

/-! ## The free projection is an isometry of the plane -/

/-- A sum over `Fin (n + 1)` whose terms vanish at the coordinates `0` and `1` is a sum over
the free coordinates. -/
theorem sum_eq_sum_freeIdx {M : Type*} [AddCommMonoid M] (hn : 1 ≤ n) (g : Fin (n + 1) → M)
    (h0 : g 0 = 0) (h1 : g 1 = 0) : ∑ i, g i = ∑ a : Fin (n - 1), g (freeIdx n a) := by
  symm
  refine Fintype.sum_of_injective (freeIdx n) (fun a b h => Fin.ext ?_) _ _ ?_ fun _ => rfl
  · have := congrArg Fin.val h; simp only [freeIdx] at this; omega
  · intro i hi
    by_cases i0 : i.val = 0
    · rw [show i = 0 from Fin.ext i0, h0]
    by_cases i1 : i.val = 1
    · rw [show i = 1 from (Fin.ext i1).trans (fin_one_eq hn).symm, h1]
    exact absurd (exists_freeIdx i (by omega)) (by simpa using hi)

/-- **Dropping `f₀, f₁` is a Euclidean isometry of the plane `P`**: for `x, y ∈ P`,
`∑ᵢ (xᵢ − yᵢ)² = ∑ₐ (freeProj x − freeProj y)ₐ²`. So `kozProj n` is an isometric copy of
`Koz(n)` and `volume_kozProj_eq` is the `(n−1)`-dimensional Euclidean volume of `Koz(n)`
inside `P` (Hausdorff measure on `P` itself is not formalised). -/
theorem sum_sq_sub_freeProj (hn : 1 ≤ n) {x y : Fin (n + 1) → ℝ} (hx : x ∈ plane ℝ n)
    (hy : y ∈ plane ℝ n) :
    ∑ i, (x i - y i) ^ 2 = ∑ a, (freeProj n x a - freeProj n y a) ^ 2 :=
  sum_eq_sum_freeIdx hn (fun i => (x i - y i) ^ 2) (by simp [hx.1, hy.1])
    (by simp [hx.2, hy.2])

end KozVolume

end ExteriorConvex
