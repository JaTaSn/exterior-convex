/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The affine involution β of the Kozlov simplex, and its lattice points

Formalisation of `lem-beta` and `thm-beta-lattice` from
`article/exterior-convex_article3_draft_4.org` (= Lemma 3 and Theorem 5(a),(b) of
`working-notes/centroids-and-moments-discrete-vs-continuous.org`, section "Rank one: the
affine involution β").

Coordinates are the library's degree-0-inclusive ones, `Fin (n + 1) → ℝ`, entry `i` = `f_i`
(as in `Spine/LYM.lean`); `Koz(n)` is `convexHull ℝ (skelSet n)`, with vertices `skel n j`
(= `F̃_j` with the leading `1` kept).

* `beta n` (an `AffineMap`; `betaEquiv n` the same map as an `AffineEquiv`): fixes every
  coordinate outside `2 ≤ i ≤ n − 2` and sets `β(f)_i = C(n,i)·(1 + f_{n−1}/n) − f_{n−i}`
  inside. `beta_apply` is that formula; `muOf_beta` is the LYM form
  `μ_k ↦ 1 + μ_{n−1} − μ_{n−k}`. The definition makes sense for every `n` (for `n ≤ 3`
  it is the identity); the theorems carry the paper's `n ≥ 3` where it is used.
* `beta_beta` / `beta_involutive`: β is an involution (no hypothesis on `n`).
* `beta_skel_low`: `β(F̃_j) = F̃_{n−1−j}` for `1 ≤ j ≤ n − 2`; `beta_skel_high`:
  `β(F̃_j) = F̃_j` for `j ≥ n − 1` (so `F̃_{n−1}`, `F̃_n` fixed); `beta_image_skelSet`.
* `beta_image_koz`: `β '' Koz(n) = Koz(n)` (`lem-beta`), via `AffineMap.image_convexHull`.
* `latticePts n` = `𝓛_n = Koz(n) ∩ ℤ^{n+1}` (defined here; `IsIntPt` = all coordinates
  integers). `beta_bijOn_latticePts_of_prime`: `thm-beta-lattice` (1), the bijection
  statement, for `n` prime with `n ≥ 3` (the paper's standing hypothesis for β).
* `beta_not_mapsTo_latticePts_of_not_prime` / `not_mapsTo_latticePts_of_not_prime`:
  `thm-beta-lattice` (2), for composite `n ≥ 4`, with the paper's own witness
  (`witness n`: `f_k = C(n,k)` for `k ≤ n−2`, `f_{n−1} = 1`, `f_n = 0`) and `p = minFac n`;
  `beta_witness_apply`: `β(x)_p = C(n,p)/n`. The arithmetic is `not_dvd_choose_of_prime_dvd`
  (`n ∤ C(n,p)` for a prime `p ∣ n`, `p < n`), via `choose_pred_modEq_one`
  (`C(n−1,p−1) ≡ 1 mod p`, Lucas: Mathlib's `Choose.choose_modEq_choose_mod_mul_choose_div_nat`)
  — exactly the paper's argument, which checks out.
* Stretch: `lattice_centroid_identity_of_prime` (summed) and `..._avg` (averaged): for
  `n` prime and any `Finset` `L` with `↑L = 𝓛_n`, `∑_L (μ_k + μ_{n−k}) = ∑_L (1 + μ_{n−1})`,
  `1 ≤ k ≤ n − 1`. The general engine is `sum_mu_add_mu_reflect` (any finite `β`-stable
  `L ⊆ Koz(n)`). The "lattice-point covariance is β-invariant" clause of (1), the
  continuous `thm-beta-continuous`, and the Alexander-duality remark on the face `Φ` are not
  formalised.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Spine.LYM

open Finset

namespace ExteriorConvex
namespace Beta

variable {n : ℕ}

/-- The reflected coordinate `n − i`. -/
def refl (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) := ⟨n - i.val, by omega⟩

/-- The coordinate `n − 1`. -/
def penult (n : ℕ) : Fin (n + 1) := ⟨n - 1, by omega⟩

/-- The linear part of `β`. -/
noncomputable def betaLin (n : ℕ) : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun x i := if 2 ≤ i.val ∧ i.val ≤ n - 2 then
      (n.choose i.val : ℝ) / n * x (penult n) - x (refl n i) else x i
  map_add' x y := by
    funext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' c x := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

/-- The translation part of `β`. -/
noncomputable def betaConst (n : ℕ) : Fin (n + 1) → ℝ := fun i =>
  if 2 ≤ i.val ∧ i.val ≤ n - 2 then (n.choose i.val : ℝ) else 0

/-- `β` (`lem-beta`): the affine map of `ℝ^{n+1}` fixing `f_i` for `i ∉ [2, n−2]` and
sending `f_i ↦ C(n,i)·(1 + f_{n−1}/n) − f_{n−i}` for `2 ≤ i ≤ n − 2`. -/
noncomputable def beta (n : ℕ) : (Fin (n + 1) → ℝ) →ᵃ[ℝ] (Fin (n + 1) → ℝ) :=
  (betaLin n).toAffineMap + AffineMap.const ℝ _ (betaConst n)

theorem beta_apply (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    beta n x i = if 2 ≤ i.val ∧ i.val ≤ n - 2 then
      (n.choose i.val : ℝ) * (1 + x (penult n) / n) - x (refl n i) else x i := by
  simp only [beta, AffineMap.coe_add, LinearMap.coe_toAffineMap, AffineMap.coe_const,
    Pi.add_apply, Function.const_apply, betaLin, LinearMap.coe_mk, AddHom.coe_mk, betaConst]
  split_ifs <;> ring

theorem beta_apply_mid (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (h2 : 2 ≤ i.val)
    (h3 : i.val ≤ n - 2) :
    beta n x i = (n.choose i.val : ℝ) * (1 + x (penult n) / n) - x (refl n i) := by
  rw [beta_apply]; split_ifs with h
  · rfl
  · exact absurd ⟨h2, h3⟩ h

theorem beta_apply_not_mid (x : Fin (n + 1) → ℝ) (i : Fin (n + 1))
    (h : ¬ (2 ≤ i.val ∧ i.val ≤ n - 2)) : beta n x i = x i := by
  simp only [beta_apply, h, ite_false]

theorem beta_beta (x : Fin (n + 1) → ℝ) : beta n (beta n x) = x := by
  funext i
  by_cases h : 2 ≤ i.val ∧ i.val ≤ n - 2
  · rw [beta_apply_mid _ _ h.1 h.2, beta_apply_not_mid _ (penult n) (by simp [penult]; omega),
      beta_apply_mid _ (refl n i) (by simp [refl]; omega) (by simp [refl]; omega)]
    have hr : refl n (refl n i) = i := Fin.ext (by simp [refl]; omega)
    have hc : n.choose (refl n i).val = n.choose i.val := by
      simp only [refl]; exact Nat.choose_symm (by omega)
    rw [hr, hc]; ring
  · rw [beta_apply_not_mid _ _ h, beta_apply_not_mid _ _ h]

theorem beta_involutive : Function.Involutive (beta n) := beta_beta


theorem betaLin_apply (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    betaLin n x i = if 2 ≤ i.val ∧ i.val ≤ n - 2 then
      (n.choose i.val : ℝ) / n * x (penult n) - x (refl n i) else x i := rfl

theorem betaLin_involutive : Function.Involutive (betaLin n) := by
  intro x
  funext i
  by_cases h : 2 ≤ i.val ∧ i.val ≤ n - 2
  · have hp : ¬ (2 ≤ (penult n).val ∧ (penult n).val ≤ n - 2) := by simp [penult]; omega
    have hr : 2 ≤ (refl n i).val ∧ (refl n i).val ≤ n - 2 := by simp [refl]; omega
    have hrr : refl n (refl n i) = i := Fin.ext (by simp [refl]; omega)
    have hc : n.choose (refl n i).val = n.choose i.val := by
      simp only [refl]; exact Nat.choose_symm (by omega)
    simp only [betaLin_apply, h, hp, hr, hrr, hc, and_self, ite_true, ite_false]
    ring
  · simp only [betaLin_apply, h, ite_false]

/-- `β` as an affine automorphism of `ℝ^{n+1}`. -/
noncomputable def betaEquiv (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵃ[ℝ] (Fin (n + 1) → ℝ) where
  toEquiv := Function.Involutive.toPerm _ beta_involutive
  linear := LinearEquiv.ofInvolutive (betaLin n) betaLin_involutive
  map_vadd' p v := by
    show beta n (v + p) = betaLin n v + beta n p
    simp only [beta, AffineMap.coe_add, LinearMap.coe_toAffineMap, AffineMap.coe_const,
      Pi.add_apply, Function.const_apply, map_add]
    abel

theorem coe_betaEquiv : ⇑(betaEquiv n) = beta n := rfl

/-- In LYM coordinates: `μ_k(β x) = 1 + μ_{n−1}(x) − μ_{n−k}(x)` for `2 ≤ k ≤ n − 2`. -/
theorem muOf_beta (x : Fin (n + 1) → ℝ) {k : ℕ} (h2 : 2 ≤ k) (h3 : k ≤ n - 2) :
    muOf n (beta n x) k = 1 + muOf n x (n - 1) - muOf n x (n - k) := by
  have hCk : (n.choose k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (by omega)).ne'
  have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [muOf_of_le (by omega), muOf_of_le (by omega), muOf_of_le (by omega),
    beta_apply_mid _ _ h2 h3]
  have e1 : n.choose (n - 1) = n := by
    rw [Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right]
  have e2 : n.choose (n - k) = n.choose k := Nat.choose_symm (by omega)
  rw [e1, e2]
  have hp : penult n = ⟨n - 1, by omega⟩ := rfl
  have hr : refl n ⟨k, by omega⟩ = ⟨n - k, by omega⟩ := rfl
  rw [hp, hr]
  field_simp


/-! ## The vertices -/

/-- `lem-beta`, vertex part: `β(F̃_j) = F̃_{n−1−j}` for `1 ≤ j ≤ n − 2`. -/
theorem beta_skel_low {j : ℕ} (hj1 : 1 ≤ j) (hj2 : j ≤ n - 2) :
    beta n (skel n j) = skel n (n - 1 - j) := by
  funext i
  by_cases h : 2 ≤ i.val ∧ i.val ≤ n - 2
  · rw [beta_apply_mid _ _ h.1 h.2]
    have hc : n.choose (n - i.val) = n.choose i.val := Nat.choose_symm (by omega)
    simp only [skel, penult, refl]
    have a1 : ¬ n - 1 = 0 := by omega
    have a2 : ¬ n - 1 ≤ j := by omega
    have a3 : ¬ n - i.val = 0 := by omega
    have a4 : ¬ i.val = 0 := by omega
    rw [hc]
    by_cases hij : i.val ≤ n - 1 - j
    · have a5 : ¬ n - i.val ≤ j := by omega
      simp only [a1, a2, a3, a4, a5, hij, ite_false, ite_true]
      ring
    · have a5 : n - i.val ≤ j := by omega
      simp only [a1, a2, a3, a4, a5, hij, ite_false, ite_true]
      ring
  · rw [beta_apply_not_mid _ _ h]
    simp only [skel]
    split_ifs <;> first | omega | rfl

/-- `lem-beta`, vertex part: `F̃_{n−1}` and `F̃_n` (indeed every `F̃_j`, `j ≥ n − 1`) are fixed. -/
theorem beta_skel_high {j : ℕ} (hj : n - 1 ≤ j) :
    beta n (skel n j) = skel n j := by
  funext i
  by_cases h : 2 ≤ i.val ∧ i.val ≤ n - 2
  · rw [beta_apply_mid _ _ h.1 h.2]
    have hc : n.choose (n - i.val) = n.choose i.val := Nat.choose_symm (by omega)
    have e1 : n.choose (n - 1) = n := by
      rw [Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right]
    simp only [skel, penult, refl]
    have a1 : ¬ n - 1 = 0 := by omega
    have a2 : n - 1 ≤ j := hj
    have a3 : ¬ n - i.val = 0 := by omega
    have a4 : ¬ i.val = 0 := by omega
    have a5 : n - i.val ≤ j := by omega
    have a6 : i.val ≤ j := by omega
    have hn : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simp only [a1, a2, a3, a4, a5, a6, hc, e1, ite_false, ite_true]
    field_simp
    ring
  · rw [beta_apply_not_mid _ _ h]


/-- `lem-beta`, vertex part, as a set statement: `β` maps `{F̃_1, …, F̃_n}` onto itself. -/
theorem beta_image_skelSet (hn : 3 ≤ n) : beta n '' skelSet n = skelSet n := by
  apply Set.Subset.antisymm
  · rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    rw [Set.mem_Icc] at hj
    by_cases hjl : j ≤ n - 2
    · rw [beta_skel_low hj.1 hjl]
      exact ⟨n - 1 - j, Set.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩
    · rw [beta_skel_high (by omega)]
      exact ⟨j, Set.mem_Icc.mpr hj, rfl⟩
  · rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_Icc] at hj
    by_cases hjl : j ≤ n - 2
    · refine ⟨skel n (n - 1 - j), ⟨n - 1 - j, Set.mem_Icc.mpr ⟨by omega, by omega⟩, rfl⟩, ?_⟩
      rw [beta_skel_low (by omega) (by omega)]
      congr 1; omega
    · exact ⟨skel n j, ⟨j, Set.mem_Icc.mpr hj, rfl⟩, beta_skel_high (by omega)⟩

/-- `lem-beta`: `β(Koz(n)) = Koz(n)`, with `Koz(n) = conv{F̃_1, …, F̃_n}`. -/
theorem beta_image_koz (hn : 3 ≤ n) :
    beta n '' convexHull ℝ (skelSet n) = convexHull ℝ (skelSet n) := by
  rw [AffineMap.image_convexHull, beta_image_skelSet hn]

theorem beta_mapsTo_koz (hn : 3 ≤ n) :
    Set.MapsTo (beta n) (convexHull ℝ (skelSet n)) (convexHull ℝ (skelSet n)) := by
  intro x hx
  rw [← beta_image_koz hn]
  exact Set.mem_image_of_mem _ hx

/-! ## Lattice points -/

/-- A point of `ℝ^{n+1}` with all coordinates integers. -/
def IsIntPt (x : Fin (n + 1) → ℝ) : Prop := ∀ i, ∃ z : ℤ, x i = z

/-- `𝓛_n = Koz(n) ∩ ℤ^{n+1}`, in degree-0-inclusive coordinates. -/
def latticePts (n : ℕ) : Set (Fin (n + 1) → ℝ) :=
  {x | x ∈ convexHull ℝ (skelSet n) ∧ IsIntPt x}

/-- `thm-beta-lattice` (1): for `n` prime (`n ≥ 3`), `β` maps `𝓛_n` bijectively onto itself. -/
theorem beta_bijOn_latticePts_of_prime (hp : n.Prime) (hn : 3 ≤ n) :
    Set.BijOn (beta n) (latticePts n) (latticePts n) := by
  have hmaps : Set.MapsTo (beta n) (latticePts n) (latticePts n) := by
    rintro x ⟨hx, hxi⟩
    refine ⟨beta_mapsTo_koz hn hx, fun i => ?_⟩
    by_cases h : 2 ≤ i.val ∧ i.val ≤ n - 2
    · rw [beta_apply_mid _ _ h.1 h.2]
      obtain ⟨m, hm⟩ := hp.dvd_choose_self (by omega : i.val ≠ 0) (by omega : i.val < n)
      obtain ⟨a, ha⟩ := hxi (penult n)
      obtain ⟨b, hb⟩ := hxi (refl n i)
      refine ⟨n * m + m * a - b, ?_⟩
      have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      rw [ha, hb, hm]
      push_cast
      field_simp
    · rw [beta_apply_not_mid _ _ h]
      exact hxi i
  refine ⟨hmaps, beta_involutive.injective.injOn, fun y hy => ⟨beta n y, hmaps hy, beta_beta y⟩⟩


/-- If `p` is a prime divisor of `n`, then `C(n−1, p−1) ≡ 1 (mod p)` (Lucas). -/
theorem choose_pred_modEq_one {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hn : 0 < n) :
    (n - 1).choose (p - 1) ≡ 1 [MOD p] := by
  have := Fact.mk hp
  obtain ⟨m, rfl⟩ := hpn
  have hm : 1 ≤ m := by rcases m with _ | m <;> simp_all
  have hp1 := hp.one_lt
  have e : p * m - 1 = (p - 1) + p * (m - 1) := by
    rcases m with _ | m
    · omega
    · rw [Nat.mul_succ, Nat.add_sub_cancel]; zify [hp1.le, (by nlinarith : 1 ≤ p * m + p)]; ring
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := p * m - 1) (k := p - 1) (p := p)
  have hlt : p - 1 < p := by omega
  rw [e, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt, Nat.add_mul_div_left _ _ hp.pos,
    Nat.div_eq_of_lt hlt, Nat.choose_self, Nat.choose_zero_right, ← e] at h
  simpa using h

/-- For a prime divisor `p < n` of `n`: `n ∤ C(n, p)`. -/
theorem not_dvd_choose_of_prime_dvd {p : ℕ} (hp : p.Prime) (hpn : p ∣ n) (hlt : p < n) :
    ¬ n ∣ n.choose p := by
  rintro ⟨t, ht⟩
  have hp1 := hp.one_lt
  have key : n * (n - 1).choose (p - 1) = n.choose p * p := by
    have := Nat.add_one_mul_choose_eq (n - 1) (p - 1)
    rwa [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at this
  rw [ht, mul_assoc] at key
  have h2 : (n - 1).choose (p - 1) = t * p := Nat.eq_of_mul_eq_mul_left (by omega) key
  have h3 := choose_pred_modEq_one hp hpn (by omega)
  rw [h2] at h3
  have : 1 % p = 0 := by
    have := h3.symm
    unfold Nat.ModEq at this
    simpa [Nat.mul_mod_left] using this
  rw [Nat.mod_eq_of_lt hp1] at this
  omega


/-- The witness of `thm-beta-lattice` (2): `f_k = C(n,k)` for `k ≤ n − 2`, `f_{n−1} = 1`,
`f_n = 0`. -/
def witness (n : ℕ) : Fin (n + 1) → ℝ := fun i =>
  if i.val ≤ n - 2 then (n.choose i.val : ℝ) else if i.val = n - 1 then 1 else 0

theorem witness_mem_latticePts (hn : 3 ≤ n) : witness n ∈ latticePts n := by
  refine ⟨lymChain_subset_hull (by omega) ⟨?_, ?_, ?_, ?_⟩, fun i => ?_⟩
  · simp [witness]
  · rw [fin_one_eq (by omega)]
    have a : (1 : ℕ) ≤ n - 2 := by omega
    simp only [witness, a, ite_true, Nat.choose_one_right]
  · intro j hj hjn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
    have hCj : (0 : ℝ) < n.choose j := by exact_mod_cast Nat.choose_pos (by omega)
    have hCj1 : (0 : ℝ) < n.choose (j + 1) := by exact_mod_cast Nat.choose_pos (by omega)
    simp only [witness]
    by_cases h1 : j + 1 ≤ n - 2
    · have a : j ≤ n - 2 := by omega
      simp only [h1, a, ite_true, div_self hCj1.ne', div_self hCj.ne', le_refl]
    · by_cases h2 : j + 1 = n - 1
      · have a : j ≤ n - 2 := by omega
        have b : ¬ n - 1 ≤ n - 2 := by omega
        simp only [h2, a, b, ite_true, ite_false, div_self hCj.ne',
          Nat.choose_symm (by omega : 1 ≤ n), Nat.choose_one_right]
        rw [div_le_one hn0]; exact_mod_cast (by omega : 1 ≤ n)
      · simp only [h1, h2, ite_false, zero_div]
        split_ifs <;> positivity
  · simp only [witness, Fin.val_last]
    split_ifs <;> norm_num
  · simp only [witness]
    split_ifs
    · exact ⟨n.choose i.val, by simp⟩
    · exact ⟨1, by simp⟩
    · exact ⟨0, by simp⟩

theorem beta_witness_apply {p : ℕ} (h2 : 2 ≤ p) (h3 : p ≤ n - 2) :
    beta n (witness n) ⟨p, by omega⟩ = (n.choose p : ℝ) / n := by
  rw [beta_apply_mid _ _ h2 h3]
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have a1 : ¬ n - 1 ≤ n - 2 := by omega
  have a2 : n - p ≤ n - 2 := by omega
  have a3 : (refl n ⟨p, by omega⟩).val = n - p := rfl
  have a4 : (penult n).val = n - 1 := rfl
  simp only [witness, a3, a4, a1, a2, ite_true, ite_false, Nat.choose_symm (by omega : p ≤ n)]
  field_simp
  ring

/-- `thm-beta-lattice` (2): for composite `n ≥ 4`, `β` does not preserve `𝓛_n`.  The witness
is the note's: `x = witness n ∈ 𝓛_n` and `β(x)_p = C(n,p)/n ∉ ℤ` for the least prime `p ∣ n`. -/
theorem beta_not_mapsTo_latticePts_of_not_prime (hn : 4 ≤ n) (hnp : ¬ n.Prime) :
    witness n ∈ latticePts n ∧ ¬ IsIntPt (beta n (witness n)) := by
  refine ⟨witness_mem_latticePts (by omega), ?_⟩
  set p := n.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime (by omega)
  have hpn : p ∣ n := Nat.minFac_dvd n
  have hpne : p ≠ n := fun h => hnp (h ▸ hp)
  have hplt : p < n := lt_of_le_of_ne (Nat.minFac_le (by omega)) hpne
  have h2 : 2 ≤ p := hp.two_le
  have h3 : p ≤ n - 2 := by
    obtain ⟨m, hm⟩ := hpn
    have : 2 ≤ m := by
      rcases m with _ | _ | m
      · omega
      · simp at hm; omega
      · omega
    have : 2 * p ≤ n := by rw [hm]; exact Nat.mul_le_mul_left p this |>.trans_eq' (by ring)
    omega
  intro hint
  obtain ⟨z, hz⟩ := hint ⟨p, by omega⟩
  rw [beta_witness_apply h2 h3] at hz
  have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have : ((n.choose p : ℤ) : ℝ) = ((n * z : ℤ) : ℝ) := by
    push_cast; field_simp at hz; linarith
  have hZ : (n.choose p : ℤ) = n * z := by exact_mod_cast this
  apply not_dvd_choose_of_prime_dvd hp hpn hplt
  exact Int.natCast_dvd_natCast.mp ⟨z, hZ⟩

/-- Corollary form of `thm-beta-lattice` (2): `¬ MapsTo β 𝓛_n 𝓛_n`. -/
theorem not_mapsTo_latticePts_of_not_prime (hn : 4 ≤ n) (hnp : ¬ n.Prime) :
    ¬ Set.MapsTo (beta n) (latticePts n) (latticePts n) := fun h =>
  (beta_not_mapsTo_latticePts_of_not_prime hn hnp).2
    (h (beta_not_mapsTo_latticePts_of_not_prime hn hnp).1).2


/-! ## Stretch: the lattice-point centroid identity for `n` prime -/

/-- On `Koz(n)`, `μ_1 = 1`. -/
theorem muOf_one_of_mem_koz (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ}
    (hx : x ∈ convexHull ℝ (skelSet n)) : muOf n x 1 = 1 := by
  rw [hull_skel_eq hn] at hx
  rw [muOf_of_le hn, ← fin_one_eq hn, hx.2.1, Nat.choose_one_right,
    div_self (Nat.cast_ne_zero.mpr (by omega : n ≠ 0))]

/-- The centroid identity, summed form, for any finite set `L ⊆ Koz(n)` that `β` maps
bijectively onto itself: `∑_{x∈L} (μ_k(x) + μ_{n−k}(x)) = ∑_{x∈L} (1 + μ_{n−1}(x))`
for `1 ≤ k ≤ n − 1`. -/
theorem sum_mu_add_mu_reflect (hn : 3 ≤ n) (L : Finset (Fin (n + 1) → ℝ))
    (hLkoz : ∀ x ∈ L, x ∈ convexHull ℝ (skelSet n)) (hL : ∀ x ∈ L, beta n x ∈ L)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    ∑ x ∈ L, (muOf n x k + muOf n x (n - k)) = ∑ x ∈ L, (1 + muOf n x (n - 1)) := by
  by_cases hmid : 2 ≤ k ∧ k ≤ n - 2
  · have hre : ∑ x ∈ L, muOf n x (n - k) = ∑ x ∈ L, muOf n (beta n x) (n - k) :=
      Finset.sum_nbij' (beta n) (beta n) hL hL (fun a _ => beta_beta a)
        (fun a _ => beta_beta a) (fun a _ => by rw [beta_beta])
    rw [Finset.sum_add_distrib, hre, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [muOf_beta x (by omega) (by omega), show n - (n - k) = k by omega]
    ring
  · refine Finset.sum_congr rfl fun x hx => ?_
    have h1 := muOf_one_of_mem_koz (by omega) (hLkoz x hx)
    rcases (by omega : k = 1 ∨ k = n - 1) with rfl | rfl
    · rw [h1]
    · rw [show n - (n - 1) = 1 by omega, h1, add_comm]

/-- Stretch target of `thm-beta-lattice` (1): for `n` prime (`n ≥ 3`) and any `Finset`
enumerating `𝓛_n`, the lattice-point centroid satisfies `μ_k + μ_{n−k} = 1 + μ_{n−1}`,
in summed form. -/
theorem lattice_centroid_identity_of_prime (hp : n.Prime) (hn : 3 ≤ n)
    (L : Finset (Fin (n + 1) → ℝ)) (hL : (L : Set (Fin (n + 1) → ℝ)) = latticePts n)
    {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    ∑ x ∈ L, (muOf n x k + muOf n x (n - k)) = ∑ x ∈ L, (1 + muOf n x (n - 1)) := by
  have hmem : ∀ x, x ∈ L ↔ x ∈ latticePts n := fun x => by rw [← hL]; rfl
  refine sum_mu_add_mu_reflect hn L (fun x hx => ((hmem x).1 hx).1) (fun x hx => ?_) hk1 hk2
  exact (hmem _).2 ((beta_bijOn_latticePts_of_prime hp hn).mapsTo ((hmem x).1 hx))


/-- Averaged form of `lattice_centroid_identity_of_prime`: the centroid `c` of `𝓛_n`
(uniform measure) satisfies `μ_k(c) + μ_{n−k}(c) = 1 + μ_{n−1}(c)`, where `μ_k(c)` is the
average of `μ_k` over `𝓛_n` (`μ_k` is linear, so this is `μ_k` of the centroid). -/
theorem lattice_centroid_identity_of_prime_avg (hp : n.Prime) (hn : 3 ≤ n)
    (L : Finset (Fin (n + 1) → ℝ)) (hL : (L : Set (Fin (n + 1) → ℝ)) = latticePts n)
    (hne : L.Nonempty) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k ≤ n - 1) :
    (∑ x ∈ L, muOf n x k) / L.card + (∑ x ∈ L, muOf n x (n - k)) / L.card =
      1 + (∑ x ∈ L, muOf n x (n - 1)) / L.card := by
  have h := lattice_centroid_identity_of_prime hp hn L hL hk1 hk2
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    mul_one] at h
  have hc : (L.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hne.card_pos.ne'
  rw [← add_div, h, add_div, div_self hc]

end Beta
end ExteriorConvex
