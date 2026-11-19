/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Part IV: growth of the vertex count at gap one (`prop-gap-one`)

For a strictly log-concave leg vector `a⃗` and `n ≥ 2`, the rank-two extremal matrix `E(a⃗; 1)` has
largest eigenvalue modulus `ρ = 1 + 2 cos(2π/(n+4))`, and the number `V_r` of vertices of
`RA(a⃗; 0, 1, …, r−1)` satisfies `c ρ^r ≤ V_r ≤ C ρ^r` with constants depending on `n` only.

| paper | here |
|---|---|
| `E(a⃗;1)[i][j] = 1` iff `j ≥ i−1` and not (`j = i`, `2 ≤ i ≤ n−1`) | `Mext_one_eq_one_iff`, `Mext_one_apply` (0-based) |
| `θ`, `λ`, `q`, `S_j`, `x_j` | `theta`, `lam`, `qq`, `Ssum`, `xvec` |
| `x_j = q^{j+1} sin((j+1)θ)` (`j < n`), `x_n = q^n sin 2θ` | `xvec_eq_of_lt`, `xvec_last` |
| `x > 0` | `xvec_pos` |
| `M x = λ x` | `Mext_one_mulVec_xvec` |
| `λ` is the largest eigenvalue modulus | `eigenvalue_norm_le_lam` (and `lam` is an eigenvalue: `Mext_one_mulVec_xvec`, `xvec_pos`) |
| `λ^{r−1} 𝟙ᵀx / x_max ≤ 𝟙ᵀ M^{r−1} 𝟙 ≤ λ^{r−1} 𝟙ᵀx / x_min` | `count_bounds` (generic), `gapOne_power_bounds` |
| the proposition, for `RA(a⃗; 0,…,r−1)` and `Koz(n; 0,…,r−1)` | `gapOne_vertex_bounds`, `gapOne_vertex_bounds_koz`, existential form `exists_gapOne_vertex_bounds` |

The "spectral radius" is stated concretely (no `spectralRadius`): every complex eigenvalue `μ` of
the matrix has `‖μ‖ ≤ lam n`, and `lam n` itself is an eigenvalue with a positive eigenvector.

Changelog (newest first): 2026-11-18 created (Claude-Code agent, run `2026-11-18_lean-gap-one`)
-/
import Mathlib
import ExteriorConvex.Vertices.CountTransfer

namespace ExteriorConvex
namespace GapOne

open Finset Matrix CountTransfer
open scoped Pointwise

/-! ## (A) The entries of `E(a⃗; 1)` -/

section Entries

variable {a : ℕ → ℝ} {n : ℕ}

/-- **The entry formula at gap one** (strict log-concavity only): entry `(i, j)` (0-based) is `1`
iff `i ≤ j + 1` and it is not the case that `j = i` with `1 ≤ i`, `i + 2 ≤ n`. -/
theorem Mext_one_eq_one_iff (hslc : Pairwise.SLC a n) (i j : Fin n) :
    Mext a n 1 i j = 1 ↔ (i.val ≤ j.val + 1 ∧ ¬ (j = i ∧ 1 ≤ i.val ∧ i.val + 2 ≤ n)) := by
  rw [Mext_eq_one_iff_pairAdm]
  unfold PairAdm Pairwise.Locked
  constructor
  · rintro ⟨-, h2, h3⟩
    refine ⟨by omega, ?_⟩
    rintro ⟨rfl, h4, h5⟩
    apply h3
    refine ⟨by omega, by omega, by omega, ?_⟩
    intro c hc
    rw [Finset.mem_Ioc] at hc
    obtain rfl : c = 1 + (j.val + 1) := by omega
    rfl
  · rintro ⟨h1, h2⟩
    refine ⟨by simp, by omega, ?_⟩
    rintro ⟨l1, l2, l3, l4⟩
    by_cases hij : j = i
    · exact h2 ⟨hij, by omega, by subst hij; omega⟩
    · have hne : i.val ≠ j.val := fun h => hij (Fin.ext h.symm)
      have hc := l4 (j.val + 1) (by rw [Finset.mem_Ioc]; omega)
      have hs := hslc j.val (by omega) (by omega)
      rw [Nat.sub_zero, Nat.sub_zero, show 1 + (j.val + 1) - 1 = j.val + 1 by omega,
        show 1 + (j.val + 1) = j.val + 2 by omega, show j.val + 1 - 1 = j.val by omega] at hc
      nlinarith [hc, hs]

/-- The entry formula, as a value: the entry is `1` in the described positions and `0` otherwise. -/
theorem Mext_one_apply (hslc : Pairwise.SLC a n) (i j : Fin n) :
    Mext a n 1 i j =
      if i.val ≤ j.val + 1 ∧ ¬ (j = i ∧ 1 ≤ i.val ∧ i.val + 2 ≤ n) then 1 else 0 := by
  classical
  by_cases h : i.val ≤ j.val + 1 ∧ ¬ (j = i ∧ 1 ≤ i.val ∧ i.val + 2 ≤ n)
  · rw [ite_eq_left h]
    exact (Mext_one_eq_one_iff hslc i j).mpr h
  · rw [ite_eq_right h, Mext_apply, ite_eq_right]
    exact fun hp => h ((Mext_one_eq_one_iff hslc i j).mp ((Mext_eq_one_iff_pairAdm 1 i j).mpr hp))

end Entries

/-! ## Non-negative matrices with a positive eigenvector (generic) -/

section Perron

variable {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ} {x : Fin m → ℝ} {l : ℝ}

lemma pow_mulVec_eig (hx : A *ᵥ x = l • x) (k : ℕ) : A ^ k *ᵥ x = l ^ k • x := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ← mulVec_mulVec, hx, mulVec_smul, ih, smul_smul, pow_succ, mul_comm]

lemma pow_entries_nonneg (hA : ∀ i j, 0 ≤ A i j) (k : ℕ) : ∀ i j, 0 ≤ (A ^ k) i j := by
  induction k with
  | zero =>
    intro i j
    rw [pow_zero, Matrix.one_apply]
    split_ifs <;> norm_num
  | succ k ih =>
    intro i j
    rw [pow_succ, Matrix.mul_apply]
    exact Finset.sum_nonneg fun t _ => mul_nonneg (ih i t) (hA t j)

/-- **Every eigenvalue is at most `l` in modulus** when the non-negative matrix `A` has a positive
eigenvector for `l` (weighted sup norm `max_i |v_i| / x_i`). -/
theorem eig_norm_le (hA : ∀ i j, 0 ≤ A i j) (hxpos : ∀ j, 0 < x j) (hx : A *ᵥ x = l • x)
    (μ : ℂ) (v : Fin m → ℂ) (hv : v ≠ 0)
    (hμ : A.map (fun t : ℝ => (t : ℂ)) *ᵥ v = μ • v) : ‖μ‖ ≤ l := by
  obtain ⟨i0, hi0⟩ : ∃ i, v i ≠ 0 := Function.ne_iff.mp hv
  obtain ⟨i, -, hi⟩ := Finset.exists_max_image univ (fun i => ‖v i‖ / x i) ⟨i0, mem_univ _⟩
  have hvj : ∀ j, ‖v j‖ ≤ ‖v i‖ / x i * x j := fun j =>
    (div_le_iff₀ (hxpos j)).mp (hi j (mem_univ _))
  have ht0 : 0 < ‖v i‖ / x i :=
    lt_of_lt_of_le (div_pos (norm_pos_iff.mpr hi0) (hxpos i0)) (hi i0 (mem_univ _))
  have hvipos : 0 < ‖v i‖ := by
    have := mul_pos ht0 (hxpos i)
    rwa [div_mul_cancel₀ _ (hxpos i).ne'] at this
  have hrow : ∑ j, A i j * x j = l * x i := by
    simpa [mulVec, dotProduct] using congrFun hx i
  have h1 : ‖μ‖ * ‖v i‖ ≤ l * ‖v i‖ := by
    calc ‖μ‖ * ‖v i‖ = ‖(μ • v) i‖ := by simp
      _ = ‖∑ j, (A i j : ℂ) * v j‖ := by rw [← hμ]; simp [mulVec, dotProduct]
      _ ≤ ∑ j, ‖(A i j : ℂ) * v j‖ := norm_sum_le _ _
      _ = ∑ j, A i j * ‖v j‖ := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hA i j)]
      _ ≤ ∑ j, A i j * (‖v i‖ / x i * x j) :=
          Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hvj j) (hA i j)
      _ = ‖v i‖ / x i * ∑ j, A i j * x j := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = l * ‖v i‖ := by
          rw [hrow]
          field_simp [(hxpos i).ne']
  exact le_of_mul_le_mul_right h1 hvipos

/-- **The entry sum of the powers** of a non-negative matrix with eigenvector `lo ≤ x ≤ hi`:
`l^k 𝟙ᵀx / hi ≤ 𝟙ᵀ A^k 𝟙 ≤ l^k 𝟙ᵀx / lo`. -/
theorem count_bounds (hA : ∀ i j, 0 ≤ A i j) (hx : A *ᵥ x = l • x) {lo hi : ℝ} (hlo : 0 < lo)
    (hhi : 0 < hi) (hlox : ∀ j, lo ≤ x j) (hhix : ∀ j, x j ≤ hi) (k : ℕ) :
    l ^ k * (∑ j, x j) / hi ≤ (fun _ => (1 : ℝ)) ⬝ᵥ (A ^ k *ᵥ fun _ => 1) ∧
      (fun _ => (1 : ℝ)) ⬝ᵥ (A ^ k *ᵥ fun _ => 1) ≤ l ^ k * (∑ j, x j) / lo := by
  have hB := pow_entries_nonneg hA k
  have hrow : ∀ i, ∑ j, (A ^ k) i j * x j = l ^ k * x i := fun i => by
    simpa [mulVec, dotProduct] using congrFun (pow_mulVec_eig hx k) i
  have hsum : (fun _ => (1 : ℝ)) ⬝ᵥ (A ^ k *ᵥ fun _ => 1) = ∑ i, ∑ j, (A ^ k) i j := by
    simp [dotProduct, mulVec]
  rw [hsum]
  constructor
  · calc l ^ k * (∑ j, x j) / hi = ∑ i, ∑ j, (A ^ k) i j * x j / hi := by
          rw [Finset.mul_sum, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by rw [← hrow i, Finset.sum_div]
      _ ≤ ∑ i, ∑ j, (A ^ k) i j := Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
          rw [div_le_iff₀ hhi]
          exact mul_le_mul_of_nonneg_left (hhix j) (hB i j)
  · calc ∑ i, ∑ j, (A ^ k) i j ≤ ∑ i, ∑ j, (A ^ k) i j * x j / lo :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
            rw [le_div_iff₀ hlo]
            exact mul_le_mul_of_nonneg_left (hlox j) (hB i j)
      _ = l ^ k * (∑ j, x j) / lo := by
          rw [Finset.mul_sum, Finset.sum_div]
          exact Finset.sum_congr rfl fun i _ => by rw [← hrow i, Finset.sum_div]

/-- Casting the natural-number count `𝟙ᵀ M^k 𝟙` to `ℝ`. -/
lemma cast_count (M : Matrix (Fin m) (Fin m) ℕ) (k : ℕ) :
    (((fun _ => 1) ⬝ᵥ (M ^ k *ᵥ fun _ => 1) : ℕ) : ℝ) =
      (fun _ => (1 : ℝ)) ⬝ᵥ ((M.map (Nat.cast : ℕ → ℝ)) ^ k *ᵥ fun _ => 1) := by
  have h : (M.map (Nat.cast : ℕ → ℝ)) ^ k = (M ^ k).map (Nat.cast : ℕ → ℝ) := by
    have := map_pow (Nat.castRingHom ℝ).mapMatrix M k
    simpa [RingHom.mapMatrix_apply] using this.symm
  rw [h]
  simp [dotProduct, mulVec]

end Perron

/-! ## (B) The eigenvector -/

/-- `θ = π / (n + 4)`. -/
noncomputable def theta (n : ℕ) : ℝ := Real.pi / (n + 4)

/-- `λ = 1 + 2 cos 2θ`, the paper's `ρ_{n,1}`. -/
noncomputable def lam (n : ℕ) : ℝ := 1 + 2 * Real.cos (2 * theta n)

/-- `q = 1 / (2 cos θ)`. -/
noncomputable def qq (n : ℕ) : ℝ := 1 / (2 * Real.cos (theta n))

/-- `S_j = q^j sin((j+2)θ)` for `j ≤ n`, and `0` beyond (the paper's `S_{n+1} = 0`). -/
noncomputable def Ssum (n j : ℕ) : ℝ :=
  if j ≤ n then qq n ^ j * Real.sin (((j : ℝ) + 2) * theta n) else 0

/-- `x_j = S_j − S_{j+1}` (index `j : Fin n` stands for the paper's `j + 1`). -/
noncomputable def xvec (n : ℕ) : Fin n → ℝ := fun j => Ssum n (j.val + 1) - Ssum n (j.val + 2)

section Trig

variable (n : ℕ)

lemma theta_pos : 0 < theta n := by unfold theta; positivity

lemma theta_mul : (n : ℝ) * theta n = Real.pi - 4 * theta n := by
  unfold theta; field_simp; ring

lemma theta_le : theta n ≤ Real.pi / 4 := by
  have h1 := theta_mul n
  have h2 : 0 ≤ (n : ℝ) * theta n := mul_nonneg (Nat.cast_nonneg n) (theta_pos n).le
  linarith

lemma cos_theta_pos : 0 < Real.cos (theta n) :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [theta_pos n, Real.pi_pos],
    by linarith [theta_le n, Real.pi_pos]⟩

lemma qq_pos : 0 < qq n := by
  unfold qq; have := cos_theta_pos n; positivity

lemma qq_mul_cos : qq n * Real.cos (theta n) = 1 / 2 := by
  unfold qq; have := (cos_theta_pos n).ne'; field_simp

lemma one_le_lam : 1 ≤ lam n := by
  unfold lam
  have : 0 ≤ Real.cos (2 * theta n) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [theta_pos n, Real.pi_pos],
      by linarith [theta_le n]⟩
  linarith

lemma lam_pos : 0 < lam n := lt_of_lt_of_le one_pos (one_le_lam n)

lemma lam_eq : lam n = 4 * Real.cos (theta n) ^ 2 - 1 := by
  unfold lam; rw [Real.cos_two_mul]; ring

variable {n}

lemma Ssum_of_le {j : ℕ} (h : j ≤ n) :
    Ssum n j = qq n ^ j * Real.sin (((j : ℝ) + 2) * theta n) := ite_eq_left h

lemma Ssum_of_lt {j : ℕ} (h : n < j) : Ssum n j = 0 := ite_eq_right (by omega)

/-- `x_j = q^{j+1} sin((j+1)θ)` for `j < n` (paper's indexing). -/
lemma xvec_eq_of_lt (j : Fin n) (h : j.val + 2 ≤ n) :
    xvec n j = qq n ^ (j.val + 2) * Real.sin (((j.val : ℝ) + 2) * theta n) := by
  unfold xvec
  rw [Ssum_of_le (by omega), Ssum_of_le h]
  push_cast
  have e1 : ((j.val : ℝ) + 1 + 2) * theta n = ((j.val : ℝ) + 3) * theta n := by ring
  have e2 : ((j.val : ℝ) + 2 + 2) * theta n = ((j.val : ℝ) + 3) * theta n + theta n := by ring
  have e3 : ((j.val : ℝ) + 2) * theta n = ((j.val : ℝ) + 3) * theta n - theta n := by ring
  rw [e1, e2, e3, Real.sin_add, Real.sin_sub]
  have hq := qq_mul_cos n
  have hp : qq n ^ (j.val + 2) = qq n ^ (j.val + 1) * qq n := pow_succ _ _
  rw [hp]
  linear_combination (-2 * qq n ^ (j.val + 1) * Real.sin (((j.val : ℝ) + 3) * theta n)) * hq

/-- `x_n = q^n sin 2θ` (paper's indexing). -/
lemma xvec_last (j : Fin n) (h : j.val + 1 = n) :
    xvec n j = qq n ^ (j.val + 1) * Real.sin (2 * theta n) := by
  unfold xvec
  rw [Ssum_of_le (by omega), Ssum_of_lt (by omega), sub_zero]
  have hc : (j.val : ℝ) + 1 = n := by exact_mod_cast h
  have e : (((j.val + 1 : ℕ) : ℝ) + 2) * theta n = Real.pi - 2 * theta n := by
    push_cast
    linear_combination theta_mul n + theta n * hc
  rw [e, Real.sin_pi_sub]

/-- **Positivity of the eigenvector.** -/
theorem xvec_pos (j : Fin n) : 0 < xvec n j := by
  have hθ := theta_pos n
  have hπ := theta_mul n
  by_cases h : j.val + 2 ≤ n
  · rw [xvec_eq_of_lt j h]
    refine mul_pos (pow_pos (qq_pos n) _) (Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_)
    have : (j.val : ℝ) + 2 ≤ n := by exact_mod_cast h
    nlinarith
  · rw [xvec_last j (by omega)]
    exact mul_pos (pow_pos (qq_pos n) _)
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [theta_le n]))

end Trig

/-! ### The eigenvector equation -/

lemma sum_range_tail (f : ℕ → ℝ) (m k : ℕ) (hk : k ≤ m) :
    ∑ j ∈ range m, (if k ≤ j then f (j + 1) - f (j + 2) else 0) = f (k + 1) - f (m + 1) := by
  induction m with
  | zero => obtain rfl : k = 0 := by omega
            simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    by_cases h : k ≤ m
    · rw [ih h, ite_eq_left h]; ring
    · obtain rfl : k = m + 1 := by omega
      rw [ite_eq_right h, Finset.sum_eq_zero, add_zero, sub_self]
      intro j hj
      rw [Finset.mem_range] at hj
      rw [ite_eq_right (by omega)]

lemma sum_xvec_tail (n k : ℕ) (hk : k ≤ n) :
    ∑ j : Fin n, (if k ≤ j.val then xvec n j else 0) = Ssum n (k + 1) := by
  have := sum_range_tail (Ssum n) n k hk
  rw [Ssum_of_lt (Nat.lt_succ_self n), sub_zero] at this
  rw [← this, ← Fin.sum_univ_eq_sum_range (fun j => if k ≤ j then Ssum n (j + 1) - Ssum n (j + 2)
    else 0) n]
  rfl

section Eigen

variable {a : ℕ → ℝ} {n : ℕ}

/-- A row of `E(a⃗; 1) x`: the tail sum `S_{i−1}`, less `x_i` in the middle rows. -/
lemma row_mulVec_xvec (hslc : Pairwise.SLC a n) (i : Fin n) :
    ((Mext a n 1).map (Nat.cast : ℕ → ℝ) *ᵥ xvec n) i =
      Ssum n (i.val - 1 + 1) - (if 1 ≤ i.val ∧ i.val + 2 ≤ n then xvec n i else 0) := by
  have hterm : ∀ j : Fin n, ((Mext a n 1 i j : ℕ) : ℝ) * xvec n j =
      (if i.val - 1 ≤ j.val then xvec n j else 0) -
        (if j = i then (if 1 ≤ i.val ∧ i.val + 2 ≤ n then xvec n i else 0) else 0) := by
    intro j
    rw [Mext_one_apply hslc]
    by_cases h1 : i.val ≤ j.val + 1
    · have h1' : i.val - 1 ≤ j.val := by omega
      by_cases h2 : j = i
      · subst h2
        by_cases h3 : 1 ≤ j.val ∧ j.val + 2 ≤ n
        · simp [h3]
        · simp [h3]
      · simp [h1, h1', h2]
    · have h1' : ¬ i.val - 1 ≤ j.val := by omega
      have h2 : j ≠ i := fun h => h1 (by subst h; omega)
      simp [h1, h1', h2]
  simp only [mulVec, dotProduct, Matrix.map_apply]
  rw [Finset.sum_congr rfl fun j _ => hterm j, Finset.sum_sub_distrib,
    sum_xvec_tail n (i.val - 1) (by omega), Finset.sum_ite_eq' univ i, ite_eq_left (mem_univ _)]

/-- **The eigenvector equation** `E(a⃗; 1) x = λ x`. -/
theorem Mext_one_mulVec_xvec (hslc : Pairwise.SLC a n) (hn : 2 ≤ n) :
    (Mext a n 1).map (Nat.cast : ℕ → ℝ) *ᵥ xvec n = lam n • xvec n := by
  funext i
  rw [row_mulVec_xvec hslc i, Pi.smul_apply, smul_eq_mul, lam_eq]
  have hq := qq_mul_cos n
  have hsc := Real.sin_sq_add_cos_sq (theta n)
  have hπ := theta_mul n
  have h2θ : Real.sin (2 * theta n) = 2 * Real.sin (theta n) * Real.cos (theta n) :=
    Real.sin_two_mul _
  have h3θ : Real.sin (3 * theta n) = 3 * Real.sin (theta n) - 4 * Real.sin (theta n) ^ 3 :=
    Real.sin_three_mul _
  rcases Nat.eq_zero_or_pos i.val with h0 | h0
  · -- first row
    rw [ite_eq_right (by omega), sub_zero, h0, xvec_eq_of_lt i (by omega), h0,
      Ssum_of_le (by omega)]
    have e1 : (((0 + 1 : ℕ) : ℝ) + 2) * theta n = 3 * theta n := by push_cast; ring
    have e2 : (((0 : ℕ) : ℝ) + 2) * theta n = 2 * theta n := by push_cast; ring
    rw [e1, e2, h2θ, h3θ]
    linear_combination (-(4 * Real.cos (theta n) ^ 2 - 1) * qq n * Real.sin (theta n) * 2) * hq
      + (-4 * qq n * Real.sin (theta n)) * hsc
  · by_cases hmid : i.val + 2 ≤ n
    · -- middle rows
      rw [ite_eq_left ⟨h0, hmid⟩, xvec_eq_of_lt i hmid, show i.val - 1 + 1 = i.val by omega,
        Ssum_of_le (by omega)]
      have hp : qq n ^ (i.val + 2) = qq n ^ i.val * qq n ^ 2 := pow_add _ _ _
      rw [hp]
      linear_combination (-(4 * qq n ^ i.val * Real.sin (((i.val : ℝ) + 2) * theta n)) *
        (qq n * Real.cos (theta n) + 1 / 2)) * hq
    · -- last row
      have hlast : i.val + 1 = n := by have := i.isLt; omega
      rw [ite_eq_right (by omega), sub_zero, xvec_last i hlast, show i.val - 1 + 1 = i.val by omega,
        Ssum_of_le (by omega)]
      have hc : (i.val : ℝ) + 1 = n := by exact_mod_cast hlast
      have e : ((i.val : ℝ) + 2) * theta n = Real.pi - 3 * theta n := by
        linear_combination hπ + theta n * hc
      rw [e, Real.sin_pi_sub, h2θ, h3θ, pow_succ]
      linear_combination
        (-(4 * Real.cos (theta n) ^ 2 - 1) * qq n ^ i.val * Real.sin (theta n) * 2) * hq
          + (-4 * qq n ^ i.val * Real.sin (theta n)) * hsc

lemma Mext_cast_nonneg (i j : Fin n) : 0 ≤ ((Mext a n 1).map (Nat.cast : ℕ → ℝ)) i j := by
  rw [Matrix.map_apply]; exact Nat.cast_nonneg _

/-! ## (C) The spectral statement -/

/-- **`λ` is the largest eigenvalue modulus of `E(a⃗; 1)`**: every complex eigenvalue `μ` has
`‖μ‖ ≤ λ` (and `λ` is an eigenvalue, by `Mext_one_mulVec_xvec` and `xvec_pos`). -/
theorem eigenvalue_norm_le_lam (hslc : Pairwise.SLC a n) (hn : 2 ≤ n) (μ : ℂ) (v : Fin n → ℂ)
    (hv : v ≠ 0) (hμ : (Mext a n 1).map (Nat.cast : ℕ → ℂ) *ᵥ v = μ • v) : ‖μ‖ ≤ lam n := by
  refine eig_norm_le (A := (Mext a n 1).map (Nat.cast : ℕ → ℝ)) Mext_cast_nonneg xvec_pos
    (Mext_one_mulVec_xvec hslc hn) μ v hv ?_
  rw [← hμ]
  congr 1

end Eigen

/-! ## (D) Two-sided bounds for the entry sums of the powers -/

/-- The smallest entry of the eigenvector (`1` in the degenerate case `n = 0`). -/
noncomputable def xmin (n : ℕ) : ℝ :=
  if h : 0 < n then
    univ.inf' (show (univ : Finset (Fin n)).Nonempty from ⟨⟨0, h⟩, mem_univ _⟩) (xvec n)
  else 1

/-- The largest entry of the eigenvector (`1` in the degenerate case `n = 0`). -/
noncomputable def xmax (n : ℕ) : ℝ :=
  if h : 0 < n then
    univ.sup' (show (univ : Finset (Fin n)).Nonempty from ⟨⟨0, h⟩, mem_univ _⟩) (xvec n)
  else 1

/-- The lower constant `c = 𝟙ᵀx / (λ x_max)`. -/
noncomputable def gapc (n : ℕ) : ℝ := (∑ j, xvec n j) / (lam n * xmax n)

/-- The upper constant `C = 𝟙ᵀx / (λ x_min)`. -/
noncomputable def gapC (n : ℕ) : ℝ := (∑ j, xvec n j) / (lam n * xmin n)

section Bounds

variable {a : ℕ → ℝ} {n : ℕ}

lemma xmin_le (j : Fin n) : xmin n ≤ xvec n j := by
  unfold xmin
  rw [dite_eq_left (by have := j.isLt; omega)]
  exact Finset.inf'_le _ (mem_univ j)

lemma le_xmax (j : Fin n) : xvec n j ≤ xmax n := by
  unfold xmax
  rw [dite_eq_left (by have := j.isLt; omega)]
  exact Finset.le_sup' _ (mem_univ j)

lemma xmin_pos (n : ℕ) : 0 < xmin n := by
  unfold xmin
  split_ifs with h
  · rw [Finset.lt_inf'_iff]
    exact fun j _ => xvec_pos j
  · exact one_pos

lemma xmax_pos (n : ℕ) : 0 < xmax n := by
  unfold xmax
  split_ifs with h
  · exact lt_of_lt_of_le (xvec_pos ⟨0, h⟩) (Finset.le_sup' _ (mem_univ _))
  · exact one_pos

lemma xmin_le_xmax (hn : 0 < n) : xmin n ≤ xmax n :=
  (xmin_le ⟨0, hn⟩).trans (le_xmax ⟨0, hn⟩)

lemma sum_xvec_pos (hn : 0 < n) : 0 < ∑ j, xvec n j :=
  Finset.sum_pos (fun j _ => xvec_pos j) ⟨⟨0, hn⟩, mem_univ _⟩

lemma gapc_pos (hn : 0 < n) : 0 < gapc n :=
  div_pos (sum_xvec_pos hn) (mul_pos (lam_pos n) (xmax_pos n))

lemma gapc_le_gapC (hn : 0 < n) : gapc n ≤ gapC n :=
  div_le_div_of_nonneg_left (sum_xvec_pos hn).le (mul_pos (lam_pos n) (xmin_pos n))
    (mul_le_mul_of_nonneg_left (xmin_le_xmax hn) (lam_pos n).le)

/-- **Two-sided bound for `𝟙ᵀ E(a⃗; 1)^{r−1} 𝟙`**, `r ≥ 1`, with the explicit constants. -/
theorem gapOne_power_bounds (hslc : Pairwise.SLC a n) (hn : 2 ≤ n) {r : ℕ} (hr : 1 ≤ r) :
    gapc n * lam n ^ r ≤ (((fun _ => 1) ⬝ᵥ (Mext a n 1 ^ (r - 1) *ᵥ fun _ => 1) : ℕ) : ℝ) ∧
      (((fun _ => 1) ⬝ᵥ (Mext a n 1 ^ (r - 1) *ᵥ fun _ => 1) : ℕ) : ℝ) ≤ gapC n * lam n ^ r := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [Nat.add_sub_cancel, cast_count]
  have h := count_bounds (A := (Mext a n 1).map (Nat.cast : ℕ → ℝ)) Mext_cast_nonneg
    (Mext_one_mulVec_xvec hslc hn) (xmin_pos n) (xmax_pos n) xmin_le le_xmax k
  have hl := (lam_pos n).ne'
  have h1 := (xmin_pos n).ne'
  have h2 := (xmax_pos n).ne'
  have e1 : gapc n * lam n ^ (k + 1) = lam n ^ k * (∑ j, xvec n j) / xmax n := by
    unfold gapc; field_simp; ring
  have e2 : gapC n * lam n ^ (k + 1) = lam n ^ k * (∑ j, xvec n j) / xmin n := by
    unfold gapC; field_simp; ring
  rw [e1, e2]
  exact h

/-! ## (E) The vertex counts -/

/-- **Proposition (gap one), the bounds**: for a positive strictly log-concave leg vector, `n ≥ 2`
and `r ≥ 1`, the number `V_r` of vertices of `RA(a⃗; 0, 1, …, r−1)` satisfies
`c λ^r ≤ V_r ≤ C λ^r` (any ambient `N ≥ r − 1 + n`). -/
theorem gapOne_vertex_bounds (hpos : ∀ s, 0 < a s) (hslc : Pairwise.SLC a n) (hn : 2 ≤ n)
    {r N : ℕ} (hr : 1 ≤ r) (hN : r + n ≤ N + 1) :
    gapc n * lam n ^ r ≤
        ((Set.extremePoints ℝ (∑ p ∈ range r, convexHull ℝ (vsetA a N p n))).ncard : ℝ) ∧
      ((Set.extremePoints ℝ (∑ p ∈ range r, convexHull ℝ (vsetA a N p n))).ncard : ℝ) ≤
        gapC n * lam n ^ r := by
  rw [cor_vertex_count (d := fun p => p) hpos hslc.wlc hr (fun _ _ h => h) (fun p hp => by omega),
    transferProd_id]
  exact gapOne_power_bounds hslc hn hr

/-- **Proposition (gap one), for `Koz(n; 0, 1, …, r−1)` itself.** -/
theorem gapOne_vertex_bounds_koz (hn : 2 ≤ n) {r N : ℕ} (hr : 1 ≤ r) (hN : r + n ≤ N + 1) :
    gapc n * lam n ^ r ≤
        ((Set.extremePoints ℝ (convexHull ℝ (ffSet n N (fun i : Fin r => (i : ℕ))))).ncard : ℝ) ∧
      ((Set.extremePoints ℝ (convexHull ℝ (ffSet n N (fun i : Fin r => (i : ℕ))))).ncard : ℝ) ≤
        gapC n * lam n ^ r := by
  rw [cor_vertex_count_koz (d := fun p => p) (by omega) hr (fun _ _ h => h)
    (fun p hp => by omega), transferProd_id]
  exact gapOne_power_bounds (kozLeg_slc n) hn hr

/-- **Proposition (gap one)**, existential form: constants `0 < c ≤ C` depending on `n` only. -/
theorem exists_gapOne_vertex_bounds (hn : 2 ≤ n) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ a : ℕ → ℝ, (∀ s, 0 < a s) → Pairwise.SLC a n →
      ∀ r N : ℕ, 1 ≤ r → r + n ≤ N + 1 →
        c * lam n ^ r ≤
            ((Set.extremePoints ℝ (∑ p ∈ range r, convexHull ℝ (vsetA a N p n))).ncard : ℝ) ∧
          ((Set.extremePoints ℝ (∑ p ∈ range r, convexHull ℝ (vsetA a N p n))).ncard : ℝ) ≤
            C * lam n ^ r :=
  ⟨gapc n, gapC n, gapc_pos (by omega), gapc_le_gapC (by omega),
    fun _ hpos hslc _ _ hr hN => gapOne_vertex_bounds hpos hslc hn hr hN⟩

end Bounds

end GapOne
end ExteriorConvex
