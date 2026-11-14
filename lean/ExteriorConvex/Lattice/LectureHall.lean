/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The Kozlov simplex is a lecture hall simplex

Formalisation of `prop-lecture-hall` in `article/exterior-convex_article3_draft_4.org`.

**Convention.** For `s⃗ = (s₁, …, s_D)` of positive integers the `s⃗`-lecture hall simplex is
`P^{(s⃗)} = {λ ∈ ℝ^D : 0 ≤ λ₁/s₁ ≤ λ₂/s₂ ≤ ⋯ ≤ λ_D/s_D ≤ 1}`: all inequalities weak (closed
simplex), ratios *increasing* in the index. This is the paper's definition (citing
Savage–Schuster 2012 and Hibi–Olsen–Tsuchiya 2018), and it agrees with Hibi–Olsen–Tsuchiya
(arXiv 1608.03934, p. 2), Savage–Visontai (arXiv 1208.3831, §1) and Brändén–Solus
(arXiv 1911.12459, `P_n^s = {λ ∈ C_n^s : λ_n ≤ s_n}`), checked in `literature/`.
In Lean the indices are 0-based: `lectureHall s` for `s : Fin D → ℕ` is the set of
`l : Fin D → ℝ` with `0 ≤ l₀/s₀`, `l_i/s_i ≤ l_{i+1}/s_{i+1}`, `l_{D−1}/s_{D−1} ≤ 1`
(written with pairs of `Fin` indices; for `D = 0` it is all of `ℝ⁰`, one point).

**The map.** Degree-0-inclusive coordinates `Fin (n + 1)` as in `Spine/LYM.lean`. The paper's
`λ_i = p_{n+1−i}` (`i = 1, …, n−1`) is, 0-based, `lhMap n x i = x_{n−i}` (`i : Fin (n−1)`);
it is defined as `freeProj n x ∘ Fin.rev` (`Lattice/Volume.lean`'s projection onto
`f₂, …, fₙ`, followed by reversal), so it is the coordinate linear map `lhLinear n`
(`LinearMap.funLeft`). The paper's `s⃗ = (c_n, c_{n−1}, …, c₂)` is `sSeq c n i = c_{n−i}`; for
the Kozlov vector `kozS n i = C(n, n−i)`, i.e. `s⃗ = (C(n,n), …, C(n,2))`, as printed.

* `mem_legChain_iff`: for a general positive leg vector `c` (`ChainedGeneral.lean`'s
  `legChain`, the chain description of `∠(c⃗)`, `prop-rank-one-H`), `x ∈ legChain c n` iff
  `x₀ = c₀`, `x₁ = c₁` and `lhMap n x ∈ P^{(s⃗)}`.  `lhMap_bijOn_planeC`: `lhMap` is a bijection
  from the plane `{x₀ = c₀, x₁ = c₁}` onto `R^{n−1}` (any coefficient type: `ℝ` and `ℤ`), with
  inverse `liftC`.  **`prop_lecture_hall`**: `lhMap` maps `∠(c⃗)` bijectively onto `P^{(s⃗)}`
  (`Set.BijOn`), and `image_legSimplex`: `lhMap '' ∠(c⃗) = P^{(s⃗)}`.
* "Unimodularly": `lhMap` is linear (`lhMap_eq_lhLinear`), bijective plane → `ℝ^{n−1}`,
  commutes with `ℤ → ℝ` (`lhMap_castR`, `rfl`), and is a bijection plane ∩ `ℤ^{n+1}` → `ℤ^{n−1}`;
  so it induces a lattice isomorphism of the affine lattices. `lattice_bijOn`:
  `∠(c⃗) ∩ ℤ^{n+1}` (`latticePtsC`) → `P^{(s⃗)} ∩ ℤ^{n−1}` (`lhLattice`) is a bijection;
  `ncard_lhLattice` the count. (Mathlib has no notion "unimodular equivalence of polytopes";
  the above are its ingredients, as in `Volume.lean`.)
* **Kozlov case**: `koz_lecture_hall` (`lhMap` maps `Koz(n) = conv S_n` bijectively onto
  `P^{(kozS n)}`), `image_koz`, `koz_bijOn_plane` (bijection on `Volume.lean`'s `plane ℝ n`,
  derived from `freeProj_bijOn`), `koz_lattice_bijOn` (`𝓛_n ≅ P^{(s⃗)} ∩ ℤ^{n−1}`),
  `ncard_koz_lhLattice` (`#(P^{(s⃗)} ∩ ℤ^{n−1}) = #𝓛_n`), and the counts
  `ncard_koz_lhLattice_one … _five` = 1, 2, 5, 20, 162 (`n ≤ 4` from `LatticePoints.lean`'s
  kernel `decide`; `card_latticeFinset_five` = 162 is a new kernel `decide` here, ~30 s, with
  finite raised `maxRecDepth`/`maxHeartbeats`). Independently checked in Python for `n ≤ 5`:
  the image of `𝓛_n` equals the set of integer points of `P^{(s⃗)}`, and the reversal map
  carries those onto the integer points of `P^{(s⃗ reversed)}`.
* **Reversal** (the paper's map `λ_i ↦ s_{D+1−i} − λ_{D+1−i}`, for the Hibi–Olsen–Tsuchiya
  reversal equivalence): `lhRev_bijOn`, `lhRev` maps `P^{(s⃗)}` bijectively onto
  `P^{(s⃗ reversed)}`, is an involution (`lhRev_lhRev`) and preserves integrality; hence
  `koz_lecture_hall_rev`: `Koz(n)` is affinely-unimodularly equivalent to `P^{(C(n,2),…,C(n,n))}`.
* **Converse**: `cOf s` is `c⃗ = (1, 1, s_D, …, s₁)` (`n = D + 1`), `sSeq_cOf`: its `s⃗` is `s⃗`,
  and `lectureHall_eq_image`: `P^{(s⃗)} = lhMap '' ∠(cOf s)`.

**Deviations.** None in the statement; the indexing is 0-based as described. `1 ≤ n` is assumed
throughout (for `n = 0` there are no vertices), and `c` positive on `[0, n]`. Dilates and
`Koz(n; d⃗)` are not treated (the paper states the identification only for `∠(c⃗)`).

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Lattice.ChainedGeneral
import ExteriorConvex.Lattice.Volume

open Finset

namespace ExteriorConvex

namespace LectureHall

open _root_.ExteriorConvex.Lattice _root_.ExteriorConvex.Lattice.Leg KozVolume

variable {n : ℕ}

/-! ## Lecture hall simplices -/

/-- The `s⃗`-lecture hall simplex `{λ : 0 ≤ λ₁/s₁ ≤ ⋯ ≤ λ_D/s_D ≤ 1}`, 0-based. -/
def lectureHall {D : ℕ} (s : Fin D → ℕ) : Set (Fin D → ℝ) :=
  {l | (∀ i : Fin D, i.val = 0 → 0 ≤ l i / s i) ∧
    (∀ i j : Fin D, j.val = i.val + 1 → l i / s i ≤ l j / s j) ∧
    (∀ i : Fin D, i.val + 1 = D → l i / s i ≤ 1)}

/-- Its lattice points. -/
def lhLattice {D : ℕ} (s : Fin D → ℕ) : Set (Fin D → ℤ) :=
  {l | castR l ∈ lectureHall s}

/-! ## The coordinate map `λ_i = p_{n+1−i}` -/

/-- `λ = (p_n, p_{n−1}, …, p₂)`: drop `p₀, p₁` (`freeProj`) and reverse. -/
def lhMap {R : Type*} (n : ℕ) (x : Fin (n + 1) → R) : Fin (n - 1) → R :=
  fun i => freeProj n x (Fin.rev i)

/-- The index map underlying `lhMap`: `i ↦ n − i`. -/
def lhIdx (n : ℕ) (i : Fin (n - 1)) : Fin (n + 1) := freeIdx n (Fin.rev i)

theorem lhIdx_val (i : Fin (n - 1)) : (lhIdx n i).val = n - i.val := by
  simp only [lhIdx, freeIdx, Fin.val_rev]
  omega

theorem lhMap_apply {R : Type*} (x : Fin (n + 1) → R) (i : Fin (n - 1)) :
    lhMap n x i = x (lhIdx n i) := rfl

/-- `lhMap` as a linear map (a coordinate selection). -/
def lhLinear (R : Type*) [CommSemiring R] (n : ℕ) : (Fin (n + 1) → R) →ₗ[R] (Fin (n - 1) → R) :=
  LinearMap.funLeft R R (lhIdx n)

theorem lhMap_eq_lhLinear (R : Type*) [CommSemiring R] :
    lhMap (R := R) n = ⇑(lhLinear R n) := rfl

/-- `lhMap` commutes with the inclusion `ℤ → ℝ`. -/
theorem lhMap_castR (x : Fin (n + 1) → ℤ) : lhMap n (castR x) = castR (lhMap n x) := rfl

/-- The paper's `s⃗ = (c_n, c_{n−1}, …, c₂)`, 0-based: `sSeq c n i = c_{n−i}`. -/
def sSeq (c : ℕ → ℕ) (n : ℕ) : Fin (n - 1) → ℕ := fun i => c (n - i.val)

/-- The plane `{x₀ = c₀, x₁ = c₁}` containing `∠(c⃗)`. -/
def planeC (R : Type*) [NatCast R] (c : ℕ → ℕ) (n : ℕ) : Set (Fin (n + 1) → R) :=
  {x | x 0 = (c 0 : R) ∧ x 1 = (c 1 : R)}

/-- The inverse of `lhMap` on `planeC`: put `c₀, c₁` in front and reverse. -/
def liftC {R : Type*} [Zero R] [NatCast R] (c : ℕ → ℕ) (n : ℕ) (y : Fin (n - 1) → R) :
    Fin (n + 1) → R :=
  fun i => if i.val = 0 then (c 0 : R) else if i.val = 1 then (c 1 : R) else
    if h : n - i.val < n - 1 then y ⟨n - i.val, h⟩ else 0

theorem liftC_mem {R : Type*} [Zero R] [NatCast R] (c : ℕ → ℕ) (hn : 1 ≤ n)
    (y : Fin (n - 1) → R) : liftC c n y ∈ planeC R c n := by
  refine ⟨by simp [liftC], ?_⟩
  rw [fin_one_eq hn]
  simp [liftC]

theorem lhMap_liftC {R : Type*} [Zero R] [NatCast R] (c : ℕ → ℕ) (y : Fin (n - 1) → R) :
    lhMap n (liftC c n y) = y := by
  funext i
  rw [lhMap_apply, liftC]
  have h := lhIdx_val i
  have hi := i.isLt
  rw [ite_eq_right (by omega), ite_eq_right (by omega), dite_eq_left (by omega)]
  congr 1
  apply Fin.ext
  simp only [h]
  omega

theorem lhMap_injOn {R : Type*} [NatCast R] (c : ℕ → ℕ) (hn : 1 ≤ n) :
    Set.InjOn (lhMap (R := R) n) (planeC R c n) := by
  rintro x ⟨hx0, hx1⟩ y ⟨hy0, hy1⟩ h
  funext k
  by_cases k0 : k.val = 0
  · rw [show k = 0 from Fin.ext k0, hx0, hy0]
  by_cases k1 : k.val = 1
  · rw [show k = 1 from (Fin.ext k1).trans (fin_one_eq hn).symm, hx1, hy1]
  have hk := k.isLt
  have := congrFun h ⟨n - k.val, by omega⟩
  rw [lhMap_apply, lhMap_apply] at this
  have he : lhIdx n ⟨n - k.val, by omega⟩ = k := Fin.ext (by rw [lhIdx_val]; simp; omega)
  rwa [he] at this

/-- **Dropping `p₀, p₁` and reversing is a bijection** from the plane `{x₀ = c₀, x₁ = c₁}`
onto `R^{n−1}`, over any coefficient type (`ℝ`: the affine isomorphism; `ℤ`: the lattices). -/
theorem lhMap_bijOn_planeC {R : Type*} [Zero R] [NatCast R] (c : ℕ → ℕ) (hn : 1 ≤ n) :
    Set.BijOn (lhMap (R := R) n) (planeC R c n) Set.univ :=
  ⟨fun _ _ => Set.mem_univ _, lhMap_injOn c hn,
    fun y _ => ⟨liftC c n y, liftC_mem c hn y, lhMap_liftC c y⟩⟩

/-! ## The chain description becomes the lecture hall inequalities -/

theorem x_eq (x : Fin (n + 1) → ℝ) {a b : Fin (n + 1)} (h : a.val = b.val) : x a = x b := by
  rw [Fin.ext h]

section Pos

variable {c : ℕ → ℕ} (hc : ∀ k, k ≤ n → 0 < c k)
include hc

/-- **`prop-lecture-hall`, the inequalities**: `x ∈ legChain c n` (the chain description of
`∠(c⃗)`) iff `x₀ = c₀`, `x₁ = c₁` and `λ = (x_n, …, x₂)` lies in `P^{(c_n, …, c₂)}`. -/
theorem mem_legChain_iff (hn : 1 ≤ n) (x : Fin (n + 1) → ℝ) :
    x ∈ legChain c n ↔ x ∈ planeC ℝ c n ∧ lhMap n x ∈ lectureHall (sSeq c n) := by
  have hcp : ∀ k, k ≤ n → (0 : ℝ) < (c k : ℝ) := fun k hk => Nat.cast_pos.mpr (hc k hk)
  simp only [legChain, planeC, lectureHall, Set.mem_ofPred_eq, lhMap_apply, sSeq]
  constructor
  · rintro ⟨h0, h1, hch, hlast⟩
    refine ⟨⟨h0, h1⟩, ?_, ?_, ?_⟩
    · intro i hi
      have hv := lhIdx_val i
      rw [x_eq x (a := lhIdx n i) (b := Fin.last n) (by simp; omega), hi, Nat.sub_zero]
      exact div_nonneg hlast (hcp n le_rfl).le
    · intro i j hj
      have hjl := j.isLt
      have := hch (n - j.val) (by omega) (by omega)
      rw [x_eq x (a := lhIdx n i) (b := ⟨n - j.val + 1, by omega⟩) (by rw [lhIdx_val]; simp; omega),
        x_eq x (a := lhIdx n j) (b := ⟨n - j.val, by omega⟩) (by rw [lhIdx_val]),
        show n - i.val = n - j.val + 1 by omega]
      exact this
    · intro i hi
      have := hch 1 le_rfl (by omega)
      rw [show (⟨1, by omega⟩ : Fin (n + 1)) = 1 from (fin_one_eq hn).symm, h1,
        div_self (hcp 1 hn).ne'] at this
      rw [x_eq x (a := lhIdx n i) (b := ⟨1 + 1, by omega⟩) (by rw [lhIdx_val]; simp; omega),
        show n - i.val = 1 + 1 by omega]
      exact this
  · rintro ⟨⟨h0, h1⟩, hfirst, hmid, hlast⟩
    refine ⟨h0, h1, ?_, ?_⟩
    · intro j hj hjn
      rcases Nat.eq_or_lt_of_le hj with rfl | hj2
      · have := hlast ⟨n - 2, by omega⟩ (by simp; omega)
        rw [x_eq x (a := lhIdx n ⟨n - 2, _⟩) (b := ⟨1 + 1, by omega⟩) (by rw [lhIdx_val]; simp; omega),
          show n - (n - 2) = 1 + 1 by simp; omega] at this
        rw [show (⟨1, by omega⟩ : Fin (n + 1)) = 1 from (fin_one_eq hn).symm, h1,
          div_self (hcp 1 hn).ne']
        exact this
      · have := hmid ⟨n - 1 - j, by omega⟩ ⟨n - j, by omega⟩ (by simp; omega)
        rw [x_eq x (a := lhIdx n ⟨n - 1 - j, _⟩) (b := ⟨j + 1, by omega⟩) (by rw [lhIdx_val]; simp; omega),
          x_eq x (a := lhIdx n ⟨n - j, _⟩) (b := ⟨j, by omega⟩) (by rw [lhIdx_val]; simp; omega),
          show n - (n - 1 - j) = j + 1 by omega, show n - (n - j) = j by omega] at this
        exact this
    · rcases Nat.eq_or_lt_of_le hn with rfl | hn2
      · rw [show Fin.last 1 = 1 from rfl, h1]
        exact (hcp 1 le_rfl).le
      · have := hfirst ⟨0, by omega⟩ rfl
        rw [x_eq x (a := lhIdx n ⟨0, _⟩) (b := Fin.last n) (by rw [lhIdx_val]; simp),
          show n - (⟨0, by omega⟩ : Fin (n - 1)).val = n from rfl] at this
        exact (div_nonneg_iff.mp this).elim (fun h => h.1)
          (fun h => absurd h.2 (not_le.mpr (hcp n le_rfl)))

/-- **`prop-lecture-hall`** (general full leg vector): dropping `p₀, p₁` and setting
`λ_i = p_{n+1−i}` maps `∠(c⃗)` bijectively onto the `s⃗`-lecture hall simplex,
`s⃗ = (c_n, …, c₂)`. -/
theorem prop_lecture_hall (hn : 1 ≤ n) :
    Set.BijOn (lhMap n) (legSimplex c n) (lectureHall (sSeq c n)) := by
  rw [hull_legSkel_eq hc hn]
  refine ⟨fun x hx => ((mem_legChain_iff hc hn x).mp hx).2,
    (lhMap_injOn c hn).mono fun x hx => ((mem_legChain_iff hc hn x).mp hx).1, ?_⟩
  intro y hy
  refine ⟨liftC c n y, (mem_legChain_iff hc hn _).mpr ⟨liftC_mem c hn y, ?_⟩, lhMap_liftC c y⟩
  rwa [lhMap_liftC]

theorem image_legSimplex (hn : 1 ≤ n) :
    lhMap n '' legSimplex c n = lectureHall (sSeq c n) :=
  (prop_lecture_hall hc hn).image_eq

/-- **Lattice points**: `∠(c⃗) ∩ ℤ^{n+1}` is in bijection with `P^{(s⃗)} ∩ ℤ^{n−1}` via the
same map. -/
theorem lattice_bijOn (hn : 1 ≤ n) :
    Set.BijOn (lhMap n) (latticePtsC c n) (lhLattice (sSeq c n)) := by
  have hB := prop_lecture_hall hc hn
  refine ⟨fun x hx => ?_, fun x hx y hy h => ?_, fun l hl => ?_⟩
  · show castR (lhMap n x) ∈ lectureHall (sSeq c n)
    rw [← lhMap_castR]
    exact hB.mapsTo hx
  · apply castR_injective
    apply hB.injOn hx hy
    rw [lhMap_castR, lhMap_castR, h]
  · refine ⟨liftC c n l, ?_, lhMap_liftC c l⟩
    show castR (liftC c n l) ∈ legSimplex c n
    have hcast : castR (liftC c n l) = liftC c n (castR l) := by
      funext i
      simp only [castR_apply, liftC]
      split_ifs <;> simp
    rw [hcast, hull_legSkel_eq hc hn, mem_legChain_iff hc hn, lhMap_liftC]
    exact ⟨liftC_mem c hn _, hl⟩

theorem ncard_lhLattice (hn : 1 ≤ n) :
    (lhLattice (sSeq c n)).ncard = (latticePtsC c n).ncard :=
  (lattice_bijOn hc hn).image_eq ▸ (lattice_bijOn hc hn).injOn.ncard_image

end Pos

/-! ## The Kozlov simplex -/

/-- `s⃗ = (C(n,n), C(n,n−1), …, C(n,2))`, 0-based. -/
def kozS (n : ℕ) : Fin (n - 1) → ℕ := fun i => n.choose (n - i.val)

theorem sSeq_choose : sSeq (fun k => n.choose k) n = kozS n := rfl

/-- **`prop-lecture-hall` for `Koz(n)`**: `λ_i = p_{n+1−i}` maps `Koz(n) = conv S_n`
bijectively onto the lecture hall simplex `P^{(C(n,n), …, C(n,2))}`. -/
theorem koz_lecture_hall (hn : 1 ≤ n) :
    Set.BijOn (lhMap n) (convexHull ℝ (Sset n)) (lectureHall (kozS n)) := by
  rw [← legSimplex_choose hn]
  exact prop_lecture_hall (choose_pos' n) hn

theorem image_koz (hn : 1 ≤ n) : lhMap n '' convexHull ℝ (Sset n) = lectureHall (kozS n) :=
  (koz_lecture_hall hn).image_eq

/-- The same with `Koz(n)` as the hull of the skeleta (`hull_skel_eq`). -/
theorem image_hull_skel (hn : 1 ≤ n) :
    lhMap n '' convexHull ℝ (skelSet n) = lectureHall (kozS n) := by
  rw [hull_skel_eq hn, ← hull_Sset_eq hn, image_koz hn]

/-- On `Volume.lean`'s plane `{x₀ = 1, x₁ = n}` the map is a bijection onto `ℝ^{n−1}` (resp.
`ℤ^{n−1}`), obtained from `freeProj_bijOn` by composing with the reversal. -/
theorem koz_bijOn_plane {R : Type*} [Zero R] [One R] [NatCast R] (hn : 1 ≤ n) :
    Set.BijOn (lhMap (R := R) n) (plane R n) Set.univ := by
  have hF := freeProj_bijOn (R := R) hn
  refine ⟨fun _ _ => Set.mem_univ _, fun x hx y hy h => hF.injOn hx hy ?_, fun y _ => ?_⟩
  · funext a
    have := congrFun h (Fin.rev a)
    simpa [lhMap] using this
  · obtain ⟨x, hx, hxy⟩ := hF.surjOn (Set.mem_univ (fun a => y (Fin.rev a)))
    refine ⟨x, hx, funext fun i => ?_⟩
    simp only [lhMap, hxy, Fin.rev_rev]

/-- **Lattice points of `Koz(n)`**: `𝓛_n` is in bijection with the integer points of
`P^{(C(n,n), …, C(n,2))}`. -/
theorem koz_lattice_bijOn (hn : 1 ≤ n) :
    Set.BijOn (lhMap n) (latticePts n) (lhLattice (kozS n)) := by
  rw [← latticePtsC_choose hn]
  exact lattice_bijOn (choose_pos' n) hn

theorem ncard_koz_lhLattice (hn : 1 ≤ n) :
    (lhLattice (kozS n)).ncard = (latticePts n).ncard := by
  rw [← latticePtsC_choose hn]
  exact ncard_lhLattice (choose_pos' n) hn

/-! ### The counts `1, 2, 5, 20, 162` -/

theorem ncard_koz_lhLattice_eq_card (hn : 1 ≤ n) :
    (lhLattice (kozS n)).ncard = (latticeFinset n).card := by
  rw [ncard_koz_lhLattice hn, ← coe_latticeFinset hn, Set.ncard_coe_finset]

theorem ncard_koz_lhLattice_one : (lhLattice (kozS 1)).ncard = 1 := by
  rw [ncard_koz_lhLattice_eq_card le_rfl, card_latticeFinset_one]

theorem ncard_koz_lhLattice_two : (lhLattice (kozS 2)).ncard = 2 := by
  rw [ncard_koz_lhLattice_eq_card (by norm_num), card_latticeFinset_two]

theorem ncard_koz_lhLattice_three : (lhLattice (kozS 3)).ncard = 5 := by
  rw [ncard_koz_lhLattice_eq_card (by norm_num), card_latticeFinset_three]

theorem ncard_koz_lhLattice_four : (lhLattice (kozS 4)).ncard = 20 := by
  rw [ncard_koz_lhLattice_eq_card (by norm_num), card_latticeFinset_four]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 4000000 in
/-- `#𝓛₅ = 162`, by kernel `decide` (about 30 s; not in `LatticePoints.lean`). -/
theorem card_latticeFinset_five : (latticeFinset 5).card = 162 := by decide

theorem ncard_koz_lhLattice_five : (lhLattice (kozS 5)).ncard = 162 := by
  rw [ncard_koz_lhLattice_eq_card (by norm_num), card_latticeFinset_five]

/-! ## Reversal of `s⃗` -/

/-- The paper's reversal `λ_i ↦ s_{D+1−i} − λ_{D+1−i}`, 0-based. -/
def lhRev {R : Type*} [AddCommGroupWithOne R] {D : ℕ} (s : Fin D → ℕ) (l : Fin D → R) :
    Fin D → R :=
  fun i => (s (Fin.rev i) : R) - l (Fin.rev i)

theorem lhRev_lhRev {R : Type*} [AddCommGroupWithOne R] {D : ℕ} (s : Fin D → ℕ) (l : Fin D → R) :
    lhRev (s ∘ Fin.rev) (lhRev s l) = l := by
  funext i
  simp [lhRev]

theorem lhRev_castR {D : ℕ} (s : Fin D → ℕ) (l : Fin D → ℤ) :
    castR (lhRev s l) = lhRev s (castR l) := by
  funext i
  simp [lhRev]

theorem lhRev_mapsTo {D : ℕ} {s : Fin D → ℕ} (hs : ∀ i, 0 < s i) :
    Set.MapsTo (lhRev (R := ℝ) s) (lectureHall s) (lectureHall (s ∘ Fin.rev)) := by
  rintro l ⟨h0, hmid, hlast⟩
  have hr : ∀ i, lhRev s l i / ((s ∘ Fin.rev) i : ℝ) = 1 - l (Fin.rev i) / s (Fin.rev i) := by
    intro i
    simp only [lhRev, Function.comp_apply]
    rw [sub_div, div_self (Nat.cast_pos.mpr (hs _)).ne']
  refine ⟨fun i hi => ?_, fun i j hj => ?_, fun i hi => ?_⟩
  · rw [hr]
    have := hlast (Fin.rev i) (by simp [Fin.val_rev]; omega)
    linarith
  · rw [hr, hr]
    have := hmid (Fin.rev j) (Fin.rev i) (by simp [Fin.val_rev]; omega)
    linarith
  · rw [hr]
    have := h0 (Fin.rev i) (by simp [Fin.val_rev]; omega)
    linarith

/-- **Reversal**: `lhRev s` maps `P^{(s⃗)}` bijectively onto `P^{(s⃗ reversed)}`. -/
theorem lhRev_bijOn {D : ℕ} {s : Fin D → ℕ} (hs : ∀ i, 0 < s i) :
    Set.BijOn (lhRev (R := ℝ) s) (lectureHall s) (lectureHall (s ∘ Fin.rev)) := by
  have hs' : ∀ i, 0 < (s ∘ Fin.rev) i := fun i => hs _
  have hss : (s ∘ Fin.rev) ∘ Fin.rev = s := by funext i; simp
  refine Set.InvOn.bijOn (f' := lhRev (s ∘ Fin.rev)) ⟨fun l _ => lhRev_lhRev s l, fun l _ => ?_⟩
    (lhRev_mapsTo hs) (by have := lhRev_mapsTo hs'; rwa [hss] at this)
  have := lhRev_lhRev (s ∘ Fin.rev) l
  rwa [hss] at this

/-- The reversed Kozlov sequence is `(C(n,2), …, C(n,n))`. -/
theorem kozS_rev : kozS n ∘ Fin.rev = fun i : Fin (n - 1) => n.choose (i.val + 2) := by
  funext i
  simp only [Function.comp_apply, kozS, Fin.val_rev]
  congr 1
  have := i.isLt
  omega

/-- **`Koz(n)` and the reversed sequence**: `lhRev ∘ lhMap` maps `Koz(n)` bijectively onto
`P^{(C(n,2), …, C(n,n))}`; it is an affine map preserving integrality in both directions. -/
theorem koz_lecture_hall_rev (hn : 1 ≤ n) :
    Set.BijOn (lhRev (kozS n) ∘ lhMap n) (convexHull ℝ (Sset n))
      (lectureHall fun i : Fin (n - 1) => n.choose (i.val + 2)) := by
  rw [← kozS_rev]
  exact (lhRev_bijOn fun i => Nat.choose_pos (by omega)).comp (koz_lecture_hall hn)

/-! ## The converse: every lecture hall simplex is a right-angle simplex -/

/-- `c⃗ = (1, 1, s_D, …, s₁)`, with `n = D + 1` (value `1` beyond `n`, irrelevant). -/
def cOf {D : ℕ} (s : Fin D → ℕ) (k : ℕ) : ℕ :=
  if k ≤ 1 then 1 else if h : D + 1 - k < D then s ⟨D + 1 - k, h⟩ else 1

theorem cOf_pos {D : ℕ} {s : Fin D → ℕ} (hs : ∀ i, 0 < s i) (k : ℕ) : 0 < cOf s k := by
  unfold cOf
  split_ifs
  · exact one_pos
  · exact hs _
  · exact one_pos

theorem sSeq_cOf {D : ℕ} (s : Fin D → ℕ) : sSeq (cOf s) (D + 1) = s := by
  funext i
  have := i.isLt
  simp only [sSeq, cOf]
  rw [ite_eq_right (by omega), dite_eq_left (by omega)]
  congr 1
  apply Fin.ext
  simp
  omega

/-- **Converse of `prop-lecture-hall`**: `P^{(s⃗)}` is the image of `∠(1, 1, s_D, …, s₁)` under
`lhMap`. -/
theorem lectureHall_eq_image {D : ℕ} {s : Fin D → ℕ} (hs : ∀ i, 0 < s i) :
    lectureHall s = lhMap (D + 1) '' legSimplex (cOf s) (D + 1) := by
  rw [image_legSimplex (fun k _ => cOf_pos hs k) (by omega), sSeq_cOf]

end LectureHall

end ExteriorConvex
