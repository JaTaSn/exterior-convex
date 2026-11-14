/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)

# The bridge from `RA(κ⃗(n); d⃗)` to `Koz(n; d⃗)`

Article 3's `eq:koz-as-ra` (Part I §8):

    π(Koz(n; d⃗)) = RA(κ⃗(n); d⃗) + ∑_{p : d_p ≥ 1} e_{d_p},   f₀ = #{p : d_p = 0} on Koz(n; d⃗).

In the library the two sides live in different spaces and conventions:

* `Koz(n; d⃗)` is `convexHull ℝ (ffSet n N d)` (`Spine/Sumset.lean`, `main`), in the
  degree-0-inclusive space `Fin (N+1) → ℝ` (index `j` = degree `j`), shifts `d : Fin r → ℕ`;
* `RA(κ⃗(n); d⃗)` is `∑ p ∈ range r, angle (kozLeg n) N (d p) n` (`Facets/Chain.lean`,
  `Vertices/RankR.lean`), in the degree-0-dropped space `Fin N → ℝ` (index `c` = degree `c + 1`),
  shifts `d : ℕ → ℕ` read on `range r`.

Here the shifts are a single `d : ℕ → ℕ`, and `Koz` is taken at `fun i : Fin r => d i`.

* `kozMap N d r` is the injective affine map `x ↦ (0, x) + kv`, where `kv j = mult d r j` is the
  number of `p < r` with `d p = j`.  Its degree-0 entry is `#{p : d_p = 0}` and its other entries are
  `x + ∑_{p : d_p ≥ 1} e_{d_p}` (`kozMap_zero`, `kozMap_succ`): exactly `eq:koz-as-ra`.
* `koz_eq_image` (**`eq:koz-as-ra`**): `Koz(n; d⃗) = kozMap '' RA(κ⃗(n); d⃗)`, for `n ≥ 1` and
  `d p + n ≤ N` for all `p < r` (no ordering or `d 0 = 0` needed).  The engine is the
  summand-level identity `shiftIncl_skel`: `shift^d F̃_k = (0, ravA κ⃗(n) d k) + e_d`.
* `mem_koz_iff`: the same as a membership criterion, `f ∈ Koz ↔ f₀ = #{p : d_p = 0} ∧
  π(f) − ∑ e ∈ RA`; `proj_koz` is the literal `π(Koz) = RA + {∑ e}` form.
* Vertices: `extremePoints_koz` (`ext Koz = kozMap '' ext RA`); `vertex_iff_kozlov_koz`
  (Corollary `cor-kozlov-vertices`, last sentence: `∑ₚ shift^{d p} F̃_{j p}` is a vertex of
  `Koz(n; d⃗)` iff the Kozlov condition holds — the shifted skeleta in the inclusive space, i.e. the
  translated list); `extremePoints_koz_eq` (every vertex is of that form).
* H-description: `koz_hdesc` (`cor-koz-hdesc`, **restricted to the scope of `theoremB_kozlov`**:
  `0 = d 0 < d 1 < ⋯ < d (r−1)`, all gaps `≤ n − 1`, `N = d(r−1) + n`): `f ∈ Koz(n; d⃗)` iff `f₀ = 1`
  and `(f_c − mult d r c)_{c=1..N} ∈ Q_Θ(κ⃗(n); d⃗; 1)`.  With distinct shifts `mult d r c` is `1`
  at `c ∈ {d_1,…,d_{r−1}}` and `0` elsewhere, i.e. `∑_{p:d_p≥1} e_{d_p}`.

**Deviation from `cor-koz-hdesc`.**  The printed corollary is for arbitrary `0 = d_1 ≤ ⋯ ≤ d_r`,
via `cor-facets-every-d` (merging tied shifts, splitting into runs at gaps `≥ n`), and claims the
facet count `ns`.  Neither `cor-facets-every-d` nor any facet count is formalised, so `koz_hdesc`
covers only distinct shifts with gaps `≤ n − 1` (the case `s = r`, one run), as a set equality, with
no facet-count clause.  For general `d⃗` `mem_koz_iff` still transfers *any* description of `RA`.
-/
import Mathlib
import ExteriorConvex.Spine.Sumset
import ExteriorConvex.Vertices.RankR
import ExteriorConvex.Facets.ThetaForm

namespace ExteriorConvex
namespace KozBridge

open Finset Pointwise Facets

variable {n N r : ℕ}

/-! ## The affine map -/

/-- The multiplicity of the degree `c` among the first `r` shifts: `#{p < r : d p = c}`. -/
def mult (d : ℕ → ℕ) (r c : ℕ) : ℕ := ((range r).filter (fun p => d p = c)).card

/-- Insert a zero degree-0 coordinate: `x ↦ (0, x₁, …, x_N)`. -/
def incl (N : ℕ) : (Fin N → ℝ) →ₗ[ℝ] (Fin (N + 1) → ℝ) where
  toFun x := Fin.cons 0 x
  map_add' x y := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp
  map_smul' t x := by
    funext j
    refine Fin.cases ?_ (fun i => ?_) j <;> simp

@[simp] lemma incl_zero (x : Fin N → ℝ) : incl N x 0 = 0 := rfl
@[simp] lemma incl_succ (x : Fin N → ℝ) (i : Fin N) : incl N x i.succ = x i := rfl

lemma incl_injective : Function.Injective (incl N) := by
  intro x y h
  funext i
  have := congrFun h i.succ
  simpa using this

/-- The basis vector `e_c` of the inclusive space (`0` if `c > N`). -/
def ev (N c : ℕ) : Fin (N + 1) → ℝ := fun j => if j.val = c then 1 else 0

/-- The translation vector: `kv j = #{p < r : d p = j}`, i.e. `∑_{p<r} e_{d p}`. -/
def kv (N : ℕ) (d : ℕ → ℕ) (r : ℕ) : Fin (N + 1) → ℝ := fun j => (mult d r j.val : ℝ)

lemma kv_eq_sum (N : ℕ) (d : ℕ → ℕ) (r : ℕ) : kv N d r = ∑ p ∈ range r, ev N (d p) := by
  funext j
  simp only [kv, mult, ev, Finset.sum_apply]
  rw [Finset.sum_boole]
  simp only [eq_comm]

/-- **The affine map of `eq:koz-as-ra`**: `x ↦ (0, x) + ∑_{p<r} e_{d p}`. -/
noncomputable def kozMap (N : ℕ) (d : ℕ → ℕ) (r : ℕ) : (Fin N → ℝ) →ᵃ[ℝ] (Fin (N + 1) → ℝ) :=
  (incl N).toAffineMap + AffineMap.const ℝ (Fin N → ℝ) (kv N d r)

lemma kozMap_apply (d : ℕ → ℕ) (x : Fin N → ℝ) : kozMap N d r x = incl N x + kv N d r := rfl

/-- Degree-0 entry of the image: `#{p : d_p = 0}`, independent of `x`. -/
@[simp] lemma kozMap_zero (d : ℕ → ℕ) (x : Fin N → ℝ) :
    kozMap N d r x 0 = (mult d r 0 : ℝ) := by
  simp [kozMap_apply, kv]

/-- Entry `c = i + 1 ≥ 1`: `x_c + #{p : d_p = c}`. -/
@[simp] lemma kozMap_succ (d : ℕ → ℕ) (x : Fin N → ℝ) (i : Fin N) :
    kozMap N d r x i.succ = x i + (mult d r (i.val + 1) : ℝ) := by
  simp [kozMap_apply, kv]

lemma kozMap_injective (d : ℕ → ℕ) : Function.Injective (kozMap N d r) := by
  intro x y h
  rw [kozMap_apply, kozMap_apply] at h
  exact incl_injective (add_right_cancel h)

/-- Membership in the image of `kozMap`. -/
lemma mem_image_kozMap_iff (d : ℕ → ℕ) (S : Set (Fin N → ℝ)) (f : Fin (N + 1) → ℝ) :
    f ∈ kozMap N d r '' S ↔
      f 0 = (mult d r 0 : ℝ) ∧ (fun i : Fin N => f i.succ - (mult d r (i.val + 1) : ℝ)) ∈ S := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨kozMap_zero d x, ?_⟩
    convert hx using 1
    funext i
    simp
  · rintro ⟨h0, hS⟩
    refine ⟨_, hS, ?_⟩
    funext j
    refine Fin.cases ?_ (fun i => ?_) j
    · simp [h0]
    · simp

/-! ## One summand: the shifted skeleton is a translated `ravA` vertex -/

/-- `shift^d F̃_k = (0, ravA κ⃗(n) d k) + e_d`, for `k ≤ n` and `d + n ≤ N`. -/
theorem shiftIncl_skel {d k : ℕ} (hk : k ≤ n) (hdN : d + n ≤ N) :
    shiftIncl N d (skel n k) = incl N (ravA (kozLeg n) N d k) + ev N d := by
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · by_cases hd : d = 0
    · subst hd; simp [shiftIncl_apply, ev, skel]
    · have : ¬ (0 = d) := fun h => hd h.symm
      simp [shiftIncl_apply, ev, this, hd]
  · simp only [shiftIncl_apply, Fin.val_succ, Pi.add_apply, incl_succ, ev, ravA, skel]
    split_ifs <;> first | omega | simp_all [Facets.kozLeg_of_le]

/-- The per-summand affine map `x ↦ (0, x) + e_d`. -/
noncomputable def sMap (N d : ℕ) : (Fin N → ℝ) →ᵃ[ℝ] (Fin (N + 1) → ℝ) :=
  (incl N).toAffineMap + AffineMap.const ℝ (Fin N → ℝ) (ev N d)

lemma sMap_apply (d : ℕ) (x : Fin N → ℝ) : sMap N d x = incl N x + ev N d := rfl

/-- One summand of `thm-main`: `shift^d Koz(n) = (0, shift^d ∠(κ⃗(n))) + e_d`. -/
theorem shiftIncl_hull (hn : 1 ≤ n) {d : ℕ} (hdN : d + n ≤ N) :
    shiftIncl N d '' convexHull ℝ (Sset n) = sMap N d '' angle (kozLeg n) N d n := by
  rw [kozlov hn, LinearMap.image_convexHull, angle, AffineMap.image_convexHull]
  congr 1
  rw [skelSet, vsetA, Set.image_image, Set.image_image]
  refine Set.image_congr fun k hk => ?_
  rw [sMap_apply, shiftIncl_skel hk.2 hdN]

/-! ## The bridge -/

lemma sum_add_singleton {E : Type*} [AddCommMonoid E] (A : ℕ → Set E) (w : ℕ → E) (r : ℕ) :
    ∑ p ∈ range r, (A p + {w p}) = (∑ p ∈ range r, A p) + {∑ p ∈ range r, w p} := by
  induction r with
  | zero => simp; rfl
  | succ r ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, Finset.sum_range_succ,
        ← Set.singleton_add_singleton, add_add_add_comm]

lemma image_sMap (d : ℕ) (S : Set (Fin N → ℝ)) : sMap N d '' S = incl N '' S + {ev N d} := by
  rw [Set.add_singleton, Set.image_image]
  rfl

lemma image_kozMap (d : ℕ → ℕ) (S : Set (Fin N → ℝ)) :
    kozMap N d r '' S = incl N '' S + {kv N d r} := by
  rw [Set.add_singleton, Set.image_image]
  rfl

/-- **`eq:koz-as-ra`**: `Koz(n; d⃗)` is the image of `RA(κ⃗(n); d⃗)` under the injective affine
map `kozMap`, for `n ≥ 1` and every shift satisfying `d p + n ≤ N`. -/
theorem koz_eq_image (hn : 1 ≤ n) (d : ℕ → ℕ) (hN : ∀ p < r, d p + n ≤ N) :
    convexHull ℝ (ffSet n N (fun i : Fin r => d i)) =
      kozMap N d r '' ∑ p ∈ range r, angle (kozLeg n) N (d p) n := by
  rw [main, ← Finset.sum_range (fun p => shiftIncl N (d p) '' convexHull ℝ (Sset n))]
  rw [Finset.sum_congr rfl fun p hp => shiftIncl_hull hn (hN p (Finset.mem_range.mp hp))]
  simp only [image_sMap]
  rw [sum_add_singleton, image_kozMap, kv_eq_sum]
  congr 1
  exact (Set.image_finsetSum (incl N).toAddMonoidHom _ _).symm

/-- `eq:koz-as-ra` as a membership criterion. -/
theorem mem_koz_iff (hn : 1 ≤ n) (d : ℕ → ℕ) (hN : ∀ p < r, d p + n ≤ N)
    (f : Fin (N + 1) → ℝ) :
    f ∈ convexHull ℝ (ffSet n N (fun i : Fin r => d i)) ↔
      f 0 = (mult d r 0 : ℝ) ∧
        (fun i : Fin N => f i.succ - (mult d r (i.val + 1) : ℝ)) ∈
          ∑ p ∈ range r, angle (kozLeg n) N (d p) n := by
  rw [koz_eq_image hn d hN, mem_image_kozMap_iff]

/-- `eq:koz-as-ra` literally: `π(Koz(n; d⃗)) = RA(κ⃗(n); d⃗) + {t}` with `t_c = #{p : d_p = c}`,
`c = 1..N` (`= ∑_{p : d_p ≥ 1} e_{d_p}`), and `f₀ = #{p : d_p = 0}` on `Koz(n; d⃗)`. -/
theorem proj_koz (hn : 1 ≤ n) (d : ℕ → ℕ) (hN : ∀ p < r, d p + n ≤ N) :
    projIncl '' convexHull ℝ (ffSet n N (fun i : Fin r => d i)) =
        (∑ p ∈ range r, angle (kozLeg n) N (d p) n) +
          {fun i : Fin N => (mult d r (i.val + 1) : ℝ)} ∧
      ∀ f ∈ convexHull ℝ (ffSet n N (fun i : Fin r => d i)), f 0 = (mult d r 0 : ℝ) := by
  rw [koz_eq_image hn d hN]
  refine ⟨?_, ?_⟩
  · rw [Set.image_image, Set.add_singleton]
    refine Set.image_congr fun x _ => ?_
    funext i
    simp
  · rintro _ ⟨x, -, rfl⟩
    exact kozMap_zero d x

/-! ## Vertices -/

/-- An injective affine map carries extreme points onto extreme points of the image. -/
theorem extremePoints_image_of_injective {E F : Type*} [AddCommGroup E] [Module ℝ E]
    [AddCommGroup F] [Module ℝ F] (g : E →ᵃ[ℝ] F) (hg : Function.Injective g) (S : Set E) :
    Set.extremePoints ℝ (g '' S) = g '' Set.extremePoints ℝ S := by
  have hseg : ∀ x y, g '' openSegment ℝ x y = openSegment ℝ (g x) (g y) :=
    fun x y => image_openSegment ℝ g x y
  ext b
  constructor
  · rintro ⟨⟨a, ha, rfl⟩, hb⟩
    refine ⟨a, ⟨ha, fun x hx y hy hxy => ?_⟩, rfl⟩
    have := hb (Set.mem_image_of_mem g hx) (Set.mem_image_of_mem g hy)
      (by rw [← hseg]; exact Set.mem_image_of_mem g hxy)
    exact hg this
  · rintro ⟨a, ⟨ha, hext⟩, rfl⟩
    refine ⟨Set.mem_image_of_mem g ha, ?_⟩
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    rw [← hseg] at hxy
    obtain ⟨z, hz, hza⟩ := hxy
    rw [hg hza] at hz
    rw [hext hx hy hz]

/-- The vertices of `Koz(n; d⃗)` are the `kozMap`-images of the vertices of `RA(κ⃗(n); d⃗)`. -/
theorem extremePoints_koz (hn : 1 ≤ n) (d : ℕ → ℕ) (hN : ∀ p < r, d p + n ≤ N) :
    Set.extremePoints ℝ (convexHull ℝ (ffSet n N (fun i : Fin r => d i))) =
      kozMap N d r '' Set.extremePoints ℝ (∑ p ∈ range r, angle (kozLeg n) N (d p) n) := by
  rw [koz_eq_image hn d hN, extremePoints_image_of_injective _ (kozMap_injective d)]

/-- The translated vertex list: `kozMap (∑ₚ shift^{d p} v(j p)) = ∑ₚ shift^{d p} F̃_{j p}`, the sum
of the shifted skeleta in the inclusive space. -/
theorem kozMap_sum_ravA (d j : ℕ → ℕ) (hN : ∀ p < r, d p + n ≤ N) (hj : ∀ p < r, j p ≤ n) :
    kozMap N d r (∑ p ∈ range r, ravA (kozLeg n) N (d p) (j p)) =
      ∑ p ∈ range r, shiftIncl N (d p) (skel n (j p)) := by
  rw [kozMap_apply, map_sum, kv_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' := Finset.mem_range.mp hp
  rw [shiftIncl_skel (hj p hp') (hN p hp')]

/-- **`cor-kozlov-vertices` for `Koz(n; d⃗)` itself** (its last sentence): for sorted shifts and
`1 ≤ j p ≤ n`, the sum of shifted skeleta `∑ₚ shift^{d p} F̃_{j p}` is a vertex of `Koz(n; d⃗)` iff
the Kozlov condition holds at every consecutive pair. -/
theorem vertex_iff_kozlov_koz (hn : 1 ≤ n) {d j : ℕ → ℕ} (hd : Monotone d)
    (hN : ∀ p < r, d p + n ≤ N) (hj : ∀ p < r, 1 ≤ j p ∧ j p ≤ n) :
    ∑ p ∈ range r, shiftIncl N (d p) (skel n (j p)) ∈
        Set.extremePoints ℝ (convexHull ℝ (ffSet n N (fun i : Fin r => d i))) ↔
      ∀ p, p + 1 < r → Pairwise.KozCond n d j p := by
  rw [← kozMap_sum_ravA d j hN (fun p hp => (hj p hp).2), extremePoints_koz hn d hN,
    (kozMap_injective d).mem_set_image]
  exact vertex_iff_kozlov hd hN hj

/-- Every vertex of `Koz(n; d⃗)` is a sum of shifted skeleta; with `vertex_iff_kozlov_koz` this is
the complete vertex list of `cor-kozlov-vertices`. -/
theorem extremePoints_koz_eq (hn : 1 ≤ n) {d : ℕ → ℕ} (hd : Monotone d)
    (hN : ∀ p < r, d p + n ≤ N) :
    Set.extremePoints ℝ (convexHull ℝ (ffSet n N (fun i : Fin r => d i))) =
      {f | ∃ j : ℕ → ℕ, (∀ p < r, 1 ≤ j p ∧ j p ≤ n) ∧
        (∀ p, p + 1 < r → Pairwise.KozCond n d j p) ∧
        f = ∑ p ∈ range r, shiftIncl N (d p) (skel n (j p))} := by
  ext f
  constructor
  · intro hf
    have hf' := hf
    rw [extremePoints_koz hn d hN] at hf'
    obtain ⟨x, hx, rfl⟩ := hf'
    -- an extreme point of `RA` is a sum of generators
    have hsub : x ∈ ∑ p ∈ range r, vsetA (kozLeg n) N (d p) n := by
      have h1 : Set.extremePoints ℝ (∑ p ∈ range r, angle (kozLeg n) N (d p) n) ⊆
          ∑ p ∈ range r, vsetA (kozLeg n) N (d p) n := by
        simp only [angle]
        rw [← convexHull_sum]
        exact extremePoints_convexHull_subset
      exact h1 hx
    rw [Set.mem_finsetSum] at hsub
    obtain ⟨g, hg, hgx⟩ := hsub
    have hch : ∀ p ∈ range r, ∃ k, (1 ≤ k ∧ k ≤ n) ∧ ravA (kozLeg n) N (d p) k = g p := by
      intro p hp
      obtain ⟨k, hk, hkg⟩ := hg hp
      exact ⟨k, hk, hkg⟩
    classical
    let j : ℕ → ℕ := fun p => if hp : p ∈ range r then (hch p hp).choose else 1
    have hjp : ∀ p < r, (1 ≤ j p ∧ j p ≤ n) ∧ ravA (kozLeg n) N (d p) (j p) = g p := by
      intro p hp
      have hp' : p ∈ range r := Finset.mem_range.mpr hp
      simp only [j, hp', dite_true]
      exact (hch p hp').choose_spec
    have hxj : x = ∑ p ∈ range r, ravA (kozLeg n) N (d p) (j p) := by
      rw [← hgx]
      exact Finset.sum_congr rfl fun p hp => (hjp p (Finset.mem_range.mp hp)).2.symm
    refine ⟨j, fun p hp => (hjp p hp).1, ?_, ?_⟩
    · rw [hxj] at hx
      exact (vertex_iff_kozlov hd hN (fun p hp => (hjp p hp).1)).mp hx
    · rw [hxj, kozMap_sum_ravA d j hN (fun p hp => (hjp p hp).1.2)]
  · rintro ⟨j, hj, hK, rfl⟩
    exact (vertex_iff_kozlov_koz hn hd hN hj).mpr hK

/-! ## The H-description -/

lemma mult_zero_of_incr {d : ℕ → ℕ} (hr : 1 ≤ r) (h0 : d 0 = 0) (hd : Incr d r) :
    mult d r 0 = 1 := by
  rw [mult, Finset.card_eq_one]
  refine ⟨0, ?_⟩
  ext p
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨hp, hdp⟩
    by_contra hne
    have := hd.lt (Nat.pos_of_ne_zero hne) hp
    omega
  · rintro rfl
    exact ⟨by omega, h0⟩

/-- **`cor-koz-hdesc`, for distinct shifts from `0` with all gaps `≤ n − 1`** (the scope of
`theoremB_kozlov`; `N = d(r−1) + n`): `f ∈ Koz(n; d⃗)` iff `f₀ = 1` and
`(f_c − #{p : d_p = c})_{c=1..N}` (that is, `π(f) − ∑_{p:d_p≥1} e_{d_p}`) satisfies the
unit-weight Θ-form system of Theorem `thm-theta` for `κ⃗(n)`. -/
theorem koz_hdesc (hn : 1 ≤ n) (hr : 1 ≤ r) {d : ℕ → ℕ} (h0 : d 0 = 0) (hd : Incr d r)
    (hg : Gaps n d r) (f : Fin (d (r - 1) + n + 1) → ℝ) :
    f ∈ convexHull ℝ (ffSet n (d (r - 1) + n) (fun i : Fin r => d i)) ↔
      f 0 = 1 ∧
        (fun i : Fin (d (r - 1) + n) => f i.succ - (mult d r (i.val + 1) : ℝ)) ∈
          QTheta (kozLeg n) n d (fun _ => 1) r := by
  have hN : ∀ p < r, d p + n ≤ d (r - 1) + n := fun p hp => by
    have := hd.le (show p ≤ r - 1 by omega) (show r - 1 < r by omega)
    omega
  rw [mem_koz_iff hn d hN, theoremB_kozlov hn hr h0 hd hg, mult_zero_of_incr hr h0 hd,
    Nat.cast_one]

end KozBridge
end ExteriorConvex
