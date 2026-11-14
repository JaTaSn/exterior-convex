/-
2026-11-09 - Claude-Code (jts-mini) subagent: bounded Lean attempt for Kupreyeva's limit
  (working-notes/kupreyeva-limit-proof-2026-11-09.org, section 9).  Standalone, imports only Mathlib;
  check with  `cd LEAN && lake build ExteriorConvex.Kupreyeva.VolumeRatio`.
2026-11-09 - Claude-Code (jts-mini), coordinator: moved here from code/oneoff/kupreyeva_limit_lean_check.lean
  and wired into the library (namespace ExteriorConvex.Kupreyeva); Part III's lem-rho is marked partial.
What is here: (i) q_3 = 4/5 as a ratio of Lebesgue measures (Kupreyeva's area argument, rigorous);
(ii) the one-step integral of Lemma D for general k; (iii) the closed form of
rho(a,b) = prod_{k=a}^{b-1} 2k/((b-k+1)(b+k)) and q_n = (n-1)! rho(2,n) = (n+1)!/(2 (2n-1)!!).
NOT here: the volume of R_n for general n as a measure, the pseudo-power estimate, the counting lemma.
-/
import Mathlib

open MeasureTheory Set

noncomputable section

namespace ExteriorConvex.Kupreyeva

/-! ### (i) n = 3: the region under t^{3/2} against the triangle -/

/-- The region `R_3 = {0 ≤ μ₂ ≤ 1, 0 < μ₃ < μ₂^{3/2}}` (open in the second coordinate, which
changes nothing) has area 2/5. -/
theorem area_R3 :
    (volume : Measure (ℝ × ℝ)) (regionBetween (fun _ => (0 : ℝ)) (fun x => x ^ ((3 : ℝ) / 2))
      (Icc 0 1)) = ENNReal.ofReal (2 / 5) := by
  rw [Measure.volume_eq_prod, volume_regionBetween_eq_integral]
  · congr 1
    simp only [Pi.sub_apply, sub_zero]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_rpow (Or.inl (by norm_num))]
    norm_num
  · exact integrableOn_const (by simp)
  · exact (Real.continuous_rpow_const (by norm_num)).integrableOn_Icc
  · exact measurableSet_Icc
  · intro x hx
    exact Real.rpow_nonneg hx.1 _

/-- The order simplex `{0 ≤ μ₃ ≤ μ₂ ≤ 1}` (open in the second coordinate) has area 1/2. -/
theorem area_Delta3 :
    (volume : Measure (ℝ × ℝ)) (regionBetween (fun _ => (0 : ℝ)) (fun x => x) (Icc 0 1)) =
      ENNReal.ofReal (1 / 2) := by
  rw [Measure.volume_eq_prod, volume_regionBetween_eq_integral]
  · congr 1
    simp only [Pi.sub_apply, sub_zero]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
      integral_id]
    norm_num
  · exact integrableOn_const (by simp)
  · exact continuous_id.integrableOn_Icc
  · exact measurableSet_Icc
  · intro x hx
    exact hx.1

/-- Kupreyeva's `q_3 = 4/5`, as a ratio of Lebesgue measures. -/
theorem q3_area_ratio :
    ((volume : Measure (ℝ × ℝ)) (regionBetween (fun _ => (0 : ℝ)) (fun x => x ^ ((3 : ℝ) / 2))
        (Icc 0 1))).toReal /
      ((volume : Measure (ℝ × ℝ)) (regionBetween (fun _ => (0 : ℝ)) (fun x => x)
        (Icc 0 1))).toReal = 4 / 5 := by
  rw [area_R3, area_Delta3, ENNReal.toReal_ofReal (by norm_num),
    ENNReal.toReal_ofReal (by norm_num)]
  norm_num

/-! ### (ii) the integration step of Lemma D -/

/-- One step of the iterated integral: integrating `C u^{E/(k+1)}` over `[0, t^{(k+1)/k}]`
gives `C (k+1)/(E+k+1) t^{(E+k+1)/k}`. -/
theorem integral_step (k E C t : ℝ) (hk : 0 < k) (hE : 0 ≤ E) (ht : 0 ≤ t) :
    ∫ u in (0 : ℝ)..t ^ ((k + 1) / k), C * u ^ (E / (k + 1)) =
      C * (k + 1) / (E + k + 1) * t ^ ((E + k + 1) / k) := by
  have hk1 : 0 < k + 1 := by linarith
  have hexp : 0 ≤ E / (k + 1) := div_nonneg hE hk1.le
  rw [intervalIntegral.integral_const_mul,
    integral_rpow (Or.inl (by linarith))]
  have h0 : (0 : ℝ) ^ (E / (k + 1) + 1) = 0 := Real.zero_rpow (by linarith)
  rw [h0, sub_zero, ← Real.rpow_mul ht]
  have hmul : (k + 1) / k * (E / (k + 1) + 1) = (E + k + 1) / k := by
    field_simp
    ring
  rw [hmul]
  have hne : E / (k + 1) + 1 ≠ 0 := by linarith
  have hne2 : E + k + 1 ≠ 0 := by linarith
  field_simp
  ring

/-! ### (iii) the closed form of rho and of q_n -/

/-- The factor of `rho(a,b)` at `k`. -/
def fac (b k : ℕ) : ℚ := (2 * k : ℚ) / (((b : ℚ) - k + 1) * ((b : ℚ) + k))

/-- `rho(a,b) = prod_{k=a}^{b-1} 2k/((b-k+1)(b+k))`. -/
def rho (a b : ℕ) : ℚ := ∏ k ∈ Finset.Ico a b, fac b k

/-- Closed form, written with `a = c + 2`, `b = c + 2 + m` to avoid natural subtraction:
`rho(a,b) = 2^{b-a} (b-1)! (a+b-1)! / ((a-1)! (b-a+1)! (2b-1)!)`. -/
theorem rho_closed (m c : ℕ) :
    rho (c + 2) (c + 2 + m) =
      (2 : ℚ) ^ m * (c + m + 1).factorial * (2 * c + m + 3).factorial /
        ((c + 1).factorial * (m + 1).factorial * (2 * c + 2 * m + 3).factorial) := by
  induction m generalizing c with
  | zero =>
    have h3 : ((c + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h5 : ((2 * c + 3).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    simp only [rho, add_zero, Finset.Ico_self, Finset.prod_empty, pow_zero, one_mul, mul_zero,
      zero_add, Nat.factorial_one, Nat.cast_one, mul_one]
    rw [div_self (mul_ne_zero h3 h5)]
  | succ m ih =>
    have hsplit : rho (c + 2) (c + 2 + (m + 1)) =
        fac (c + 2 + (m + 1)) (c + 2) * rho (c + 1 + 2) (c + 1 + 2 + m) := by
      unfold rho
      rw [Finset.prod_eq_prod_Ico_succ_bot (by omega)]
      congr 1
      rw [show c + 2 + 1 = c + 1 + 2 by ring, show c + 2 + (m + 1) = c + 1 + 2 + m by ring]
    rw [hsplit, ih (c + 1)]
    unfold fac
    rw [show c + 1 + m + 1 = c + (m + 1) + 1 by ring,
      show 2 * (c + 1) + m + 3 = (2 * c + (m + 1) + 3) + 1 by ring,
      show 2 * (c + 1) + 2 * m + 3 = 2 * c + 2 * (m + 1) + 3 by ring,
      show (m + 1 + 1) = (m + 1) + 1 by ring]
    rw [Nat.factorial_succ (2 * c + (m + 1) + 3), Nat.factorial_succ (c + 1),
      Nat.factorial_succ (m + 1)]
    push_cast
    have h1 : ((c + (m + 1) + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h2 : ((2 * c + (m + 1) + 3).factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have h3 : ((c + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h4 : ((m + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
    have h5 : ((2 * c + 2 * (m + 1) + 3).factorial : ℚ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero _
    have h6 : ((c : ℚ) + 2 + (m + 1) - (c + 2) + 1) ≠ 0 := by
      have : ((c : ℚ) + 2 + (m + 1) - (c + 2) + 1) = m + 2 := by ring
      rw [this]; positivity
    have h7 : ((c : ℚ) + 2 + (m + 1) + (c + 2)) ≠ 0 := by positivity
    field_simp
    ring

/-- `q_n = (n-1)! rho(2,n) = (n+1)!/(2 (2n-1)!!)`, written with `n = m + 2`. -/
theorem qn_closed (m : ℕ) :
    ((m + 1).factorial : ℚ) * rho 2 (m + 2) =
      ((m + 3).factorial : ℚ) / (2 * ((2 * m + 3).doubleFactorial : ℚ)) := by
  have h := rho_closed m 0
  simp only [zero_add, mul_zero] at h
  rw [show 2 + m = m + 2 by ring] at h
  rw [h]
  -- (2m+3)! = (2m+3)!! * (2m+2)!! = (2m+3)!! * 2^(m+1) * (m+1)!
  have hf : (2 * m + 3).factorial = (2 * m + 3).doubleFactorial * (2 ^ (m + 1) * (m + 1).factorial) := by
    rw [show 2 * m + 3 = (2 * m + 2) + 1 by ring, Nat.factorial_eq_mul_doubleFactorial,
      show 2 * m + 2 = 2 * (m + 1) by ring, Nat.doubleFactorial_two_mul]
  rw [show m + 1 + 1 = m + 2 by ring] at *
  rw [show 2 * m + 3 = 2 * m + 3 by rfl, hf]
  push_cast
  have h1 : ((m + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have h2 : ((2 * m + 3).doubleFactorial : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.doubleFactorial_pos _).ne'
  rw [Nat.factorial_succ (m + 2), Nat.factorial_succ (m + 1)]
  push_cast
  field_simp
  ring

/-- Sanity: `q_3 = 4/5`, `q_4 = 4/7`, `q_5 = 8/21`. -/
example : ((1 + 1).factorial : ℚ) * rho 2 3 = 4 / 5 := by
  simp [rho, fac, Nat.factorial]; norm_num

end ExteriorConvex.Kupreyeva

end

#print axioms ExteriorConvex.Kupreyeva.q3_area_ratio
#print axioms ExteriorConvex.Kupreyeva.integral_step
#print axioms ExteriorConvex.Kupreyeva.rho_closed
#print axioms ExteriorConvex.Kupreyeva.qn_closed
