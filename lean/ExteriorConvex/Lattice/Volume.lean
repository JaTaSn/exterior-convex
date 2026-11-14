/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The normalised volume of the Kozlov simplex as a triangular determinant

Formalisation of the `Koz(n)` case of `prop-simplex-volume` in
`article/exterior-convex_article3_draft_4.org`,
`NV(Koz(n)) = ∏_{k=2}^n C(n,k)`, following
`working-notes/kozlov-polytope-volume-and-ehrhart.org`, section "Volume" (`#simplex-volume`) and
"Lean candidates", item 3.

**Coordinates.**  The vertices are the library's `skel n j` (`j = 1..n`), i.e. `F̃_j` in the
degree-0-inclusive space `Fin (n + 1) → ℝ`.  Coordinates `0` and `1` are constant on the
simplex (`f₀ = 1`, `f₁ = n`); the *free coordinates* are `f₂, …, fₙ`, indexed here by
`a : Fin (n - 1)` standing for the coordinate `a.val + 2` (`freeIdx`).  Vertex index `j = 2..n`
is likewise `b : Fin (n - 1)` standing for `j = b.val + 2`.

* `vdiff n` is the `(n−1)×(n−1)` matrix whose column `b` is `F̃_{b+2} − F̃_1` restricted to the
  free coordinates, defined from `skel` (entries not hand-coded); `vdiff_apply` computes the
  entry `(a, b)` as `C(n, a+2)` if `a ≤ b`, else `0`.
* `vdiff_isUpperTriangular`, `vdiff_det`: it is upper triangular, and its determinant is
  `∏_{k ∈ [2, n]} C(n, k)` (in `ℝ`; `vdiff_det_int` for the integer matrix `vdiffZ`).
* `freeProj_injOn_hull` / `freeProj_bijOn_int`: on the plane `P = {x₀ = 1, x₁ = n}` the
  projection to the free coordinates is injective, and it maps the integer points of `P`
  bijectively onto `ℤ^{n−1}` (`liftFree` is the inverse).  `skel_mem_plane`: every vertex lies
  on `P`.
* `affineIndependent_skel`: for `n ≥ 1` the vertices `F̃_1, …, F̃_n` are affinely independent
  — the "`(n−1)`-simplex" clause of `lem-mu` that `Spine/LYM.lean` deliberately left out.  With
  `n` points in the `(n−1)`-dimensional plane `P` this makes `P` the affine hull.

**What the formal statement certifies.**  The determinant identity is exact.  Together with the
plane lemmas it certifies the *ingredients* of `NV(Koz(n)) = ∏ C(n,k)`: the simplex is
non-degenerate in `P`, and `P ∩ ℤ^{n+1} → ℤ^{n−1}` (drop `f₀, f₁`) is a bijection of lattices
induced by an affine isomorphism `P → ℝ^{n−1}`, so the lattice-normalised volume of `Koz(n)` is
the normalised volume of the projected simplex, i.e. `|det vdiff n|`.  **What it does not
certify:** Mathlib has no notion of "normalised volume relative to a lattice", so the final
identification `NV = |det|` (a lattice simplex spanned by edge vectors `v₁,…,v_D` from one vertex
has `NV = |det(v₁,…,v_D)|` relative to `ℤ^D`) is the standard definition/fact and is not itself a
Lean theorem here.

* `convexHull_skelSet_subset_plane`: `Koz(n) ⊆ P` (from `hull_skel_eq`).
* Stretch, **reduced but not completed**: `kozProj_eq` shows the projected simplex
  `freeProj '' Koz(n)` is the image of the corner simplex `conv{0, e₀, …, e_{n−2}}`
  (`cornerSimplex`) under `vdiff n`, and `volume_kozProj` gives its Lebesgue measure in
  `ℝ^{n−1}` as `∏_{k=2}^n C(n,k) · vol(cornerSimplex (n−1))`.  The missing step
  `vol(cornerSimplex m) = 1/m!` is not in Mathlib and is not formalised, so
  `vol(Koz(n)) = (1/(n−1)!) ∏ C(n,k)` is not a Lean theorem here.  Note also that this `vol` is
  the measure of the *projection*; since `P` is parallel to the free-coordinate subspace, the
  projection is an isometry `P → ℝ^{n−1}`, which is the article's normalisation, but that
  isometry statement is not formalised either.

**Hypotheses.**  `n ≥ 1` where needed (`skel_mem_plane`, `freeProj_bijOn`,
`affineIndependent_skel`, `kozProj_eq`); for `n = 0` there are no vertices.  `vdiff_det` holds for
all `n` (empty matrix, empty product when `n ≤ 1`).

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Spine.LYM

open Finset

namespace ExteriorConvex

namespace KozVolume

variable {n : ℕ}

/-! ## The matrix of vertex differences -/

/-- The free coordinate `a.val + 2` of the inclusive space `Fin (n + 1) → ℝ`. -/
def freeIdx (n : ℕ) (a : Fin (n - 1)) : Fin (n + 1) := ⟨a.val + 2, by omega⟩

/-- The `(n−1)×(n−1)` matrix of vertex differences in the free coordinates: entry `(a, b)` is
coordinate `a+2` of `F̃_{b+2} − F̃_1`.  Columns are vertices, rows are coordinates. -/
noncomputable def vdiff (n : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℝ := fun a b =>
  skel n (b.val + 2) (freeIdx n a) - skel n 1 (freeIdx n a)

theorem vdiff_apply (a b : Fin (n - 1)) :
    vdiff n a b = if a ≤ b then (n.choose (a.val + 2) : ℝ) else 0 := by
  simp only [vdiff, skel, freeIdx, Fin.le_iff_val_le_val]
  by_cases h : a.val ≤ b.val
  · simp [h, show a.val + 2 ≤ b.val + 2 by omega]
  · simp [h, show ¬ a.val + 2 ≤ b.val + 2 by omega]

/-- The vertex-difference matrix is upper triangular. -/
theorem vdiff_isUpperTriangular : (vdiff n).IsUpperTriangular := by
  intro a b hba
  rw [vdiff_apply, ite_eq_right_iff]
  intro h
  exact absurd h (not_le.mpr hba)

theorem vdiff_diag (a : Fin (n - 1)) : vdiff n a a = (n.choose (a.val + 2) : ℝ) := by
  rw [vdiff_apply, ite_eq_left_iff]
  intro h
  exact absurd le_rfl h

/-- Reindexing `∏_{a < n-1} C(n, a+2) = ∏_{k ∈ [2, n]} C(n, k)`. -/
theorem prod_choose_shift {M : Type*} [CommMonoid M] (g : ℕ → M) :
    ∏ a : Fin (n - 1), g (a.val + 2) = ∏ k ∈ Icc 2 n, g k := by
  have hs : Ico (0 + 2) (n - 1 + 2) = Icc 2 n := by
    ext k
    simp only [mem_Ico, mem_Icc, zero_add]
    omega
  rw [Fin.prod_univ_eq_prod_range (fun a => g (a + 2)), range_eq_Ico, prod_Ico_add', hs]

/-- **`NV(Koz(n))` as a determinant**: the determinant of the vertex-difference matrix in the
free coordinates is `∏_{k=2}^n C(n,k)`. -/
theorem vdiff_det : (vdiff n).det = ∏ k ∈ Icc 2 n, (n.choose k : ℝ) := by
  rw [Matrix.det_of_isUpperTriangular vdiff_isUpperTriangular]
  simp_rw [vdiff_diag]
  exact prod_choose_shift (fun k => (n.choose k : ℝ))

theorem vdiff_det_ne_zero : (vdiff n).det ≠ 0 := by
  rw [vdiff_det]
  refine prod_ne_zero_iff.mpr fun k hk => ?_
  rw [mem_Icc] at hk
  exact Nat.cast_ne_zero.mpr (Nat.choose_pos hk.2).ne'

/-- The same matrix over `ℤ`, so that the determinant is visibly an integer. -/
def vdiffZ (n : ℕ) : Matrix (Fin (n - 1)) (Fin (n - 1)) ℤ := fun a b =>
  if a ≤ b then (n.choose (a.val + 2) : ℤ) else 0

theorem vdiffZ_cast : (vdiffZ n).map (Int.cast : ℤ → ℝ) = vdiff n := by
  ext a b
  rw [Matrix.map_apply, vdiff_apply, vdiffZ]
  split_ifs <;> simp

theorem vdiff_det_int : (vdiffZ n).det = ∏ k ∈ Icc 2 n, (n.choose k : ℤ) := by
  have : ((vdiffZ n).det : ℝ) = ∏ k ∈ Icc 2 n, (n.choose k : ℝ) := by
    rw [← vdiff_det, ← vdiffZ_cast]
    exact RingHom.map_det (Int.castRingHom ℝ) (vdiffZ n)
  exact_mod_cast this

/-! ## The plane `{x₀ = 1, x₁ = n}` and its lattice -/

/-- The plane `P = {x₀ = 1, x₁ = n}` containing `Koz(n)` (over any coefficient type; `R = ℝ`
for the plane itself, `R = ℤ` for its lattice points). -/
def plane (R : Type*) [One R] [NatCast R] (n : ℕ) : Set (Fin (n + 1) → R) :=
  {x | x 0 = 1 ∧ x 1 = (n : R)}

/-- Every vertex `F̃_j`, `1 ≤ j ≤ n`, lies on the plane. -/
theorem skel_mem_plane (hn : 1 ≤ n) {j : ℕ} (hj : 1 ≤ j) : skel n j ∈ plane ℝ n := by
  refine ⟨by simp [skel], ?_⟩
  rw [fin_one_eq hn]
  simp only [skel]
  rw [ite_eq_right one_ne_zero, ite_eq_left hj, Nat.choose_one_right]

/-- Projection onto the free coordinates `f₂, …, fₙ`. -/
def freeProj {R : Type*} (n : ℕ) (x : Fin (n + 1) → R) : Fin (n - 1) → R :=
  fun a => x (freeIdx n a)

/-- The inverse of `freeProj` on the plane: put `1, n` in front. -/
def liftFree {R : Type*} [Zero R] [One R] [NatCast R] (n : ℕ) (y : Fin (n - 1) → R) :
    Fin (n + 1) → R :=
  fun i => if i.val = 0 then 1 else if i.val = 1 then (n : R) else
    if h : i.val - 2 < n - 1 then y ⟨i.val - 2, h⟩ else 0

/-- Every coordinate `i ≥ 2` is a free coordinate. -/
theorem exists_freeIdx (i : Fin (n + 1)) (hi : 2 ≤ i.val) : ∃ a, freeIdx n a = i :=
  ⟨⟨i.val - 2, by omega⟩, Fin.ext (by simp only [freeIdx]; omega)⟩

/-- **A point with `x₀ = 1`, `x₁ = n` is determined by its free coordinates**: `freeProj` is
injective on the plane (over any coefficient type, in particular on integer points). -/
theorem freeProj_injOn {R : Type*} [One R] [NatCast R] (hn : 1 ≤ n) :
    Set.InjOn (freeProj (R := R) n) (plane R n) := by
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ h
  funext i
  by_cases i0 : i.val = 0
  · rw [show i = 0 from Fin.ext i0, hx0, hy0]
  by_cases i1 : i.val = 1
  · rw [show i = 1 from (Fin.ext i1).trans (fin_one_eq hn).symm, hx1, hy1]
  obtain ⟨a, rfl⟩ := exists_freeIdx i (by omega)
  exact congrFun h a

theorem liftFree_mem_plane {R : Type*} [Zero R] [One R] [NatCast R] (hn : 1 ≤ n)
    (y : Fin (n - 1) → R) : liftFree n y ∈ plane R n := by
  refine ⟨by simp [liftFree], ?_⟩
  rw [fin_one_eq hn]
  simp [liftFree]

theorem freeProj_liftFree {R : Type*} [Zero R] [One R] [NatCast R] (y : Fin (n - 1) → R) :
    freeProj n (liftFree n y) = y := by
  funext a
  simp [freeProj, liftFree, freeIdx]

/-- **Dropping `f₀, f₁` is a bijection** from the plane onto the free-coordinate space, over any
coefficient type: for `R = ℝ` an (affine-)linear isomorphism `P ≅ ℝ^{n−1}`, for `R = ℤ` a
bijection `P ∩ ℤ^{n+1} ≅ ℤ^{n−1}` of lattices. -/
theorem freeProj_bijOn {R : Type*} [Zero R] [One R] [NatCast R] (hn : 1 ≤ n) :
    Set.BijOn (freeProj (R := R) n) (plane R n) Set.univ :=
  ⟨fun _ _ => Set.mem_univ _, freeProj_injOn hn,
    fun y _ => ⟨liftFree n y, liftFree_mem_plane hn y, freeProj_liftFree y⟩⟩

/-- The real formulation of "the free projection loses nothing on lattice points": a point of
the real plane `P` is integral iff its free coordinates are. -/
theorem integral_iff_freeProj_integral (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (hx : x ∈ plane ℝ n) :
    (∀ i, ∃ z : ℤ, x i = z) ↔ (∀ a, ∃ z : ℤ, freeProj n x a = z) := by
  refine ⟨fun h a => h _, fun h i => ?_⟩
  by_cases i0 : i.val = 0
  · exact ⟨1, by rw [show i = 0 from Fin.ext i0, hx.1]; simp⟩
  by_cases i1 : i.val = 1
  · exact ⟨n, by rw [show i = 1 from (Fin.ext i1).trans (fin_one_eq hn).symm, hx.2]; simp⟩
  obtain ⟨a, rfl⟩ := exists_freeIdx i (by omega)
  exact h a

/-- The free projection of a real point is the cast of the projection of an integer point. -/
theorem freeProj_cast (x : Fin (n + 1) → ℤ) :
    freeProj n (fun i => (x i : ℝ)) = fun a => (freeProj (R := ℤ) n x a : ℝ) := rfl

/-! ## Affine independence of the vertices -/

/-- The columns of `vdiff n` are the free projections of the edge vectors `F̃_{b+2} − F̃_1`. -/
theorem vdiff_col (b : Fin (n - 1)) :
    (vdiff n).col b = freeProj n (skel n (b.val + 2) - skel n 1) := rfl

/-- **`Koz(n)` is an `(n−1)`-simplex**: for `n ≥ 1` the skeleta `F̃_1, …, F̃_n` (here
`j ↦ skel n (j.val + 1)`, `j : Fin n`) are affinely independent. -/
theorem affineIndependent_skel (hn : 1 ≤ n) :
    AffineIndependent ℝ (fun j : Fin n => skel n (j.val + 1)) := by
  rw [affineIndependent_iff_linearIndependent_vsub ℝ _ (⟨0, hn⟩ : Fin n)]
  let π : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n - 1) → ℝ) := LinearMap.funLeft ℝ ℝ (freeIdx n)
  apply LinearIndependent.of_comp π
  let e : Fin (n - 1) ≃ {x : Fin n // x ≠ ⟨0, hn⟩} :=
    { toFun := fun b => ⟨⟨b.val + 1, by omega⟩, fun h => by simpa using congrArg Fin.val h⟩
      invFun := fun i => ⟨i.val.val - 1, by
        have := i.val.isLt
        have h0 : i.val.val ≠ 0 := fun h => i.2 (Fin.ext h)
        omega⟩
      left_inv := fun b => by ext; simp
      right_inv := fun i => by
        have h0 : i.val.val ≠ 0 := fun h => i.2 (Fin.ext h)
        ext; simp; omega }
  rw [← linearIndependent_equiv e]
  have hc := Matrix.linearIndependent_cols_of_det_ne_zero (vdiff_det_ne_zero (n := n))
  have heq : (vdiff n).col = (⇑π ∘ fun i : {x : Fin n // x ≠ ⟨0, hn⟩} =>
      skel n (i.val.val + 1) -ᵥ skel n ((⟨0, hn⟩ : Fin n).val + 1)) ∘ ⇑e := by
    funext b a
    rfl
  rw [heq] at hc
  exact hc

/-- `Koz(n) = conv{F̃_1,…,F̃_n}` lies in the plane `P` (via `hull_skel_eq`). -/
theorem convexHull_skelSet_subset_plane (hn : 1 ≤ n) : convexHull ℝ (skelSet n) ⊆ plane ℝ n := by
  rw [hull_skel_eq hn]
  exact fun x hx => ⟨hx.1, hx.2.1⟩

/-! ## Euclidean volume, reduced to the corner simplex

Mathlib has no formula for the volume of a simplex, so the stretch target
`vol = |det| / (n−1)!` is reduced, not proved: the projected simplex is the image of the corner
simplex `conv{0, e₁, …, e_{n−1}}` under `vdiff n`, so its Lebesgue measure is
`∏ C(n,k) · vol(corner simplex)`.  The remaining fact `vol(corner simplex) = 1/(n−1)!` is
textbook but not in Mathlib, and is not formalised here. -/

/-- The corner simplex `conv{0, e₀, …, e_{m−1}}` in `ℝ^m`. -/
def cornerSimplex (m : ℕ) : Set (Fin m → ℝ) :=
  convexHull ℝ (insert 0 (Set.range fun b : Fin m => Pi.single b (1 : ℝ)))

/-- The free-coordinate projection of `Koz(n) = conv{F̃_1,…,F̃_n}`. -/
def kozProj (n : ℕ) : Set (Fin (n - 1) → ℝ) := freeProj n '' convexHull ℝ (skelSet n)

theorem freeProj_skel_one : freeProj n (skel n 1) = 0 := by
  funext a
  simp [freeProj, skel, freeIdx]

theorem freeProj_skel_col (b : Fin (n - 1)) : freeProj n (skel n (b.val + 2)) = (vdiff n).col b := by
  rw [vdiff_col]
  funext a
  have := congrFun (freeProj_skel_one (n := n)) a
  simp only [freeProj, Pi.zero_apply] at this
  simp [freeProj, this]

/-- The projected simplex is the image of the corner simplex under `vdiff n`. -/
theorem kozProj_eq (hn : 1 ≤ n) : kozProj n = Matrix.toLin' (vdiff n) '' cornerSimplex (n - 1) := by
  let π : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n - 1) → ℝ) := LinearMap.funLeft ℝ ℝ (freeIdx n)
  have hπ : (π : (Fin (n + 1) → ℝ) → (Fin (n - 1) → ℝ)) = freeProj n := rfl
  rw [kozProj, cornerSimplex, ← hπ, LinearMap.image_convexHull, LinearMap.image_convexHull]
  congr 1
  rw [Set.image_insert_eq, map_zero, ← Set.range_comp, hπ]
  ext y
  simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_range, Function.comp_apply,
    Matrix.toLin'_apply, Matrix.mulVec_single_one, skelSet, Set.mem_Icc]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    by_cases h1 : j = 1
    · left; rw [h1, freeProj_skel_one]
    · right
      refine ⟨⟨j - 2, by omega⟩, ?_⟩
      rw [← freeProj_skel_col]
      congr 2
      simp only
      omega
  · rintro (rfl | ⟨b, rfl⟩)
    · exact ⟨skel n 1, ⟨1, ⟨le_rfl, hn⟩, rfl⟩, freeProj_skel_one⟩
    · exact ⟨skel n (b.val + 2), ⟨b.val + 2, ⟨by omega, by omega⟩, rfl⟩, freeProj_skel_col b⟩

/-- **Volume, reduced**: the Lebesgue measure of the projected `Koz(n)` in `ℝ^{n−1}` is
`∏_{k=2}^n C(n,k)` times that of the corner simplex. -/
theorem volume_kozProj (hn : 1 ≤ n) :
    MeasureTheory.volume (kozProj n) =
      ENNReal.ofReal (∏ k ∈ Icc 2 n, (n.choose k : ℝ)) *
        MeasureTheory.volume (cornerSimplex (n - 1)) := by
  rw [kozProj_eq hn, MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin', vdiff_det,
    abs_of_nonneg (prod_nonneg fun _ _ => Nat.cast_nonneg _)]

end KozVolume

end ExteriorConvex
