/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Lattice points and the Ehrhart polynomial of the Kozlov simplex by transfer matrix

Formalisation of `working-notes/kozlov-polytope-volume-and-ehrhart.org`, §"Corollary: counting
lattice points and Ehrhart polynomials by transfer matrix" (the counting corollary, the
unipotency of `T₀`, Corollary (a)) and "Lean candidates" item 4; article 3
(`article/exterior-convex_article3_draft_4.org`), the transfer-matrix corollary of
§"Lattice points: the canonical chained decomposition".

**Normalisation.** As in `Lattice/LatticePoints.lean` / `ChainedExistence.lean`:
degree-0-inclusive coordinates, `Koz(n) = convexHull ℝ (Sset n)`, `𝓛_n = latticeFinset n`,
`Koz(n; d⃗) = ∑ᵢ shiftIncl N (dᵢ) '' Koz(n)` with `d : Fin (r+1) → ℕ` sorted (rank `r+1`) and
`dᵢ + n ≤ N`. `top`/`indeg` are article 2's `tp`/`indeg` on `toN x`.

* **Part A, the matrix-algebra core** (Lean candidate 4). `pow_eq_sum_choose`: an upper
  unitriangular `T` satisfies `T^k = ∑_{j<m} C(k,j) 𝒩^j`, `𝒩 = offDiag T = T − I`
  (`Commute.add_pow`, `𝒩^m = 0`). `pow_top_apply`: `𝒩^m` (size `m+1`) has the single entry
  `∏ superdiagonal` at `(0, m)`. `unitriangular_poly`: `u·T^{t−1}·v` is, for `t ≥ 1`, the value
  of the explicit polynomial `ehrPoly = ∑_{j≤m} (u·𝒩^j·v)·C(t−1, j)` (`binomPoly j` is
  `C(X−1, j)`, via `descPochhammer`), of degree `≤ m`, with `t^m` coefficient
  `u₀·(∏ s_l)·v_m / m!`.
* **Part B, the transfer count for any finite state set** (`card_chainG`): article 2's
  rearrangement (`Counting/Transfer.lean`, `card_chainedTuples`) re-proved for an arbitrary
  `Finset`, state map and transition predicate — the note's "uses nothing about `S_n`" made
  literal. `Transfer.lean`'s `uVec`/`Tmat` are *not* reused: they are built from `Amat` over
  `𝓕_n` and indexed by `Fin (n+2)`. Its `gaps` is reused.
* **Part C, the lattice transfer matrix** `uL`, `TL δ` (the note's `u^L`, `T^L(δ)`), with
  states `τ ∈ {1,…,n}` encoded as `τ−1 ∈ Fin n` (`stL`; every lattice point has `tp ≥ 1`,
  `one_le_top`) and transition `condL δ k x : (k+1) − δ < indeg x`, i.e.
  `T^L(δ)[τ][τ'] = #{x ∈ 𝓛_n : tp(x) = τ', indeg(x) + δ > τ}` exactly as printed.
  - `ncard_kozLattice` (**the counting corollary**): `#(Koz(n; d⃗) ∩ ℤ^{N+1}) =
    u^L·T^L(δ₂)⋯T^L(δ_{r+1})·𝟙`. Proof as in the note: the bijection with chained tuples of
    `𝓛_n` (`waterFill_spec`, `chained_unique`; `chained_of_chainedR` and `chained_iff_chainG`
    translate the three chaining conditions), then `card_chainG`.
  - `ncard_dilateLattice`: `#(t·Koz(n) ∩ ℤ^{n+1}) = u^L·T₀^{t−1}·𝟙` for `t ≥ 1` (via
    `t·Koz(n) = Koz(n; 0,…,0)`).
  - `TL0_lower`, `TL0_diag`, `TL0_sup` (**`T₀` unipotent upper triangular**, superdiagonal
    `T₀[τ][τ+1] = C(n, τ+1)`), `uL_zero` (`u^L[1] = 1`); the witnesses are the staircase
    vectors `stair`.
* **Stretch, the Ehrhart polynomial** (Corollary (a)): `ehrhart_koz`, a `P ∈ ℚ[t]` of degree
  `≤ n−1`, `P(t) = #(t·Koz(n) ∩ ℤ^{n+1})` for all `t ≥ 1`, `[t^{n−1}]P = ∏_{k=2}^n C(n,k)/(n−1)!`;
  `ehrhart_koz_exact`: degree exactly `n−1`, leading coefficient `det(vdiffZ n)/(n−1)!`, the
  determinant of `Lattice/Volume.lean` (`vdiff_det_int`).

**Deviations.** Hypothesis `[NeZero n]` (i.e. `n ≥ 1`) throughout Part C. The polynomial
identity is claimed for `t ≥ 1` only, which is what the transfer formula gives (`T₀^{t−1}`);
`P(0) = 1` (Ehrhart's constant term) is not proved here. The rank-`r` Ehrhart formula
`L_{Koz(n;d⃗)}(t) = u^L T₀^{t−1} T(δ₂) T₀^{t−1} ⋯ 𝟙` (the note's second display) and part (b)
(the `f`-vector analogue `a(r) = u^S (T₀^S)^{r−1} 𝟙`) are **not formalised**: the first needs
`t·Koz(n;d⃗) = Koz(n; d⃗^{(t)})` with the gaps of `d⃗^{(t)}` computed, the second article 2's
`thm-chaining` surjectivity, which is open in Lean (`Transfer.lean`, C2b).

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Lattice.ChainedExistence
import ExteriorConvex.Counting.Transfer
import ExteriorConvex.Lattice.Volume

open Finset Matrix Polynomial
open scoped Pointwise

namespace ExteriorConvex

namespace TransferEhrhart

/-! ## Part A: the matrix-algebra core -/

section Algebra

variable {R : Type*} [CommSemiring R] {m : ℕ}

/-- The strictly-upper (off-diagonal) part of a matrix: `T` with its diagonal
replaced by `0`. For an upper unitriangular `T` this is `𝒩 = T − I`. -/
def offDiag (T : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j => if i = j then 0 else T i j

theorem one_add_offDiag {T : Matrix (Fin m) (Fin m) R} (hdiag : ∀ i, T i i = 1) :
    1 + offDiag T = T := by
  ext i j
  by_cases h : i = j
  · subst h; simp [offDiag, hdiag]
  · simp [offDiag, h, Matrix.one_apply_ne h]

/-- Powers of a strictly upper triangular matrix: `(N^k) i j = 0` unless
`j ≥ i + k`. -/
theorem pow_apply_eq_zero {N : Matrix (Fin m) (Fin m) R}
    (hN : ∀ i j : Fin m, j ≤ i → N i j = 0) (k : ℕ) (i j : Fin m)
    (h : j.val < i.val + k) : (N ^ k) i j = 0 := by
  induction k generalizing j with
  | zero =>
    have : j ≠ i := fun e => by subst e; omega
    simp [Matrix.one_apply_ne' this]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    rcases lt_or_ge l.val (i.val + k) with hl | hl
    · rw [ih l hl, zero_mul]
    · rw [hN l j (Fin.le_def.mpr (by omega)), mul_zero]

theorem pow_eq_zero_of_le {N : Matrix (Fin m) (Fin m) R}
    (hN : ∀ i j : Fin m, j ≤ i → N i j = 0) {k : ℕ} (hk : m ≤ k) : N ^ k = 0 := by
  ext i j
  exact pow_apply_eq_zero hN k i j (by have := j.isLt; omega)

/-- The superdiagonal of a matrix on `Fin (m+1)`, as a total function of the
row index: `sup T l = T[l][l+1]` for `l < m`, and `0` beyond. -/
def sup (T : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (l : ℕ) : R :=
  if h : l + 1 < m + 1 then T ⟨l, by omega⟩ ⟨l + 1, h⟩ else 0

/-- The entry `(0, k)` of `N^k`: the product of the first `k` superdiagonal
entries. -/
theorem pow_apply_zero_diag {N : Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    (hN : ∀ i j, j ≤ i → N i j = 0) (k : ℕ) (hk : k < m + 1) :
    (N ^ k) 0 ⟨k, hk⟩ = ∏ l ∈ range k, sup N l := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply, Finset.prod_range_succ, ← ih (by omega)]
    rw [Finset.sum_eq_single (⟨k, by omega⟩ : Fin (m + 1))]
    · simp [sup, show k + 1 < m + 1 from hk]
    · intro l _ hl
      rcases lt_or_ge l.val k with h1 | h1
      · rw [pow_apply_eq_zero hN k 0 l (by simpa using h1), zero_mul]
      · have : k < l.val := lt_of_le_of_ne h1 (fun e => hl (Fin.ext e.symm))
        rw [hN l ⟨k + 1, hk⟩ (Fin.le_def.mpr (by simp; omega)), mul_zero]
    · simp

/-- The top power `N^m` of a strictly upper triangular `(m+1)×(m+1)` matrix
has a single possibly-nonzero entry, at `(0, m)`. -/
theorem pow_top_apply {N : Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    (hN : ∀ i j, j ≤ i → N i j = 0) (i j : Fin (m + 1)) :
    (N ^ m) i j = if i = 0 ∧ j = Fin.last m then ∏ l ∈ range m, sup N l else 0 := by
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    exact pow_apply_zero_diag hN m (by omega)
  · refine pow_apply_eq_zero hN m i j ?_
    have hi := i.isLt; have hj := j.isLt
    by_contra hc
    apply h
    refine ⟨Fin.ext ?_, Fin.ext ?_⟩
    · rw [Fin.val_zero]; omega
    · rw [Fin.val_last]; omega

/-- **Binomial expansion of a unitriangular power.** If `T` is upper
unitriangular of size `m`, then `T^k = ∑_{j<m} C(k,j) 𝒩^j` with `𝒩 = T − I`,
for every `k` (the terms `j ≥ m` vanish because `𝒩^m = 0`). -/
theorem pow_eq_sum_choose {T : Matrix (Fin m) (Fin m) R}
    (hlow : ∀ i j, j < i → T i j = 0) (hdiag : ∀ i, T i i = 1) (k : ℕ) :
    T ^ k = ∑ j ∈ range m, (k.choose j : R) • offDiag T ^ j := by
  have hN : ∀ i j : Fin m, j ≤ i → offDiag T i j = 0 := by
    intro i j hji
    rcases eq_or_lt_of_le hji with h | h
    · simp [offDiag, h]
    · simp [offDiag, hlow i j h, (ne_of_lt h).symm]
  have hc : Commute (offDiag T) (1 : Matrix (Fin m) (Fin m) R) := Commute.one_right _
  have hT : T ^ k = (offDiag T + 1) ^ k := by rw [add_comm, one_add_offDiag hdiag]
  rw [hT, hc.add_pow]
  have e : ∀ j, offDiag T ^ j * 1 ^ (k - j) * (k.choose j : Matrix (Fin m) (Fin m) R) =
      (k.choose j : R) • offDiag T ^ j := by
    intro j
    rw [one_pow, mul_one, Nat.cast_smul_eq_nsmul, nsmul_eq_mul']
  simp_rw [e]
  have hsub1 : range (k + 1) ⊆ range (k + 1 + m) := range_subset_range.mpr (by omega)
  have hsub2 : range m ⊆ range (k + 1 + m) := range_subset_range.mpr (by omega)
  rw [Finset.sum_subset hsub1, ← Finset.sum_subset hsub2]
  · intro j _ hjm
    simp only [mem_range, not_lt] at hjm
    rw [pow_eq_zero_of_le hN hjm, smul_zero]
  · intro j _ hjk
    simp only [mem_range, not_lt] at hjk
    rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_smul]

/-- The scalar form: `u · T^k · v = ∑_{j<m} C(k,j) · (u · 𝒩^j · v)`. -/
theorem dotProduct_pow_mulVec {T : Matrix (Fin m) (Fin m) R}
    (hlow : ∀ i j, j < i → T i j = 0) (hdiag : ∀ i, T i i = 1) (u v : Fin m → R) (k : ℕ) :
    u ⬝ᵥ (T ^ k *ᵥ v) =
      ∑ j ∈ range m, (k.choose j : R) * (u ⬝ᵥ (offDiag T ^ j *ᵥ v)) := by
  rw [pow_eq_sum_choose hlow hdiag k, Matrix.sum_mulVec, dotProduct_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]

theorem sup_offDiag (T : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (l : ℕ) :
    sup (offDiag T) l = sup T l := by
  unfold sup
  split_ifs with h
  · simp [offDiag, Fin.ext_iff]
  · rfl

/-- The top coefficient `u · 𝒩^m · v` for a unitriangular `(m+1)×(m+1)`
matrix: `u₀ · (∏ superdiagonal) · v_m`. -/
theorem dotProduct_offDiag_pow_top {T : Matrix (Fin (m + 1)) (Fin (m + 1)) R}
    (hlow : ∀ i j, j < i → T i j = 0) (u v : Fin (m + 1) → R) :
    u ⬝ᵥ (offDiag T ^ m *ᵥ v) = u 0 * (∏ l ∈ range m, sup T l) * v (Fin.last m) := by
  have hN : ∀ i j : Fin (m + 1), j ≤ i → offDiag T i j = 0 := by
    intro i j hji
    rcases eq_or_lt_of_le hji with h | h
    · simp [offDiag, h]
    · simp [offDiag, hlow i j h, (ne_of_lt h).symm]
  simp only [dotProduct, Matrix.mulVec, pow_top_apply hN, ite_mul, zero_mul, sup_offDiag]
  rw [Finset.sum_eq_single (0 : Fin (m + 1))]
  · rw [Finset.sum_eq_single (Fin.last m)]
    · simp [mul_assoc]
    · intro j _ hj; simp [hj]
    · simp
  · intro i _ hi
    simp [hi]
  · simp

end Algebra

/-! ### The polynomials `t ↦ C(t−1, j)` -/

/-- `binomPoly j = C(X − 1, j) = (X−1)(X−2)⋯(X−j)/j!`, as a polynomial over `ℚ`. -/
noncomputable def binomPoly (j : ℕ) : ℚ[X] :=
  C ((j.factorial : ℚ)⁻¹) * (descPochhammer ℚ j).comp (X - 1)

theorem binomPoly_eval (j k : ℕ) : (binomPoly j).eval ((k : ℚ) + 1) = k.choose j := by
  rw [binomPoly, eval_mul, eval_C, eval_comp, eval_sub, eval_X, eval_one, add_sub_cancel_right,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  push_cast
  field_simp

theorem natDegree_comp_X_sub_one (j : ℕ) :
    ((descPochhammer ℚ j).comp (X - 1)).natDegree = j := by
  rw [natDegree_comp, descPochhammer_natDegree, ← C_1, natDegree_X_sub_C, mul_one]

theorem binomPoly_natDegree_le (j : ℕ) : (binomPoly j).natDegree ≤ j := by
  unfold binomPoly
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_comp_X_sub_one]

theorem binomPoly_coeff_self (j : ℕ) : (binomPoly j).coeff j = (j.factorial : ℚ)⁻¹ := by
  rw [binomPoly, coeff_C_mul]
  have h := natDegree_comp_X_sub_one j
  have hlc : ((descPochhammer ℚ j).comp (X - 1)).leadingCoeff = 1 := by
    rw [← C_1, leadingCoeff_comp (by rw [natDegree_X_sub_C]; exact one_ne_zero),
      (monic_descPochhammer ℚ j).leadingCoeff, leadingCoeff_X_sub_C, one_pow, mul_one]
  rw [leadingCoeff, h] at hlc
  rw [hlc, mul_one]

/-- The interpolating polynomial `∑_{j ≤ m} a_j · C(X − 1, j)`. -/
noncomputable def ehrPoly (m : ℕ) (a : ℕ → ℚ) : ℚ[X] :=
  ∑ j ∈ range (m + 1), C (a j) * binomPoly j

theorem ehrPoly_natDegree_le (m : ℕ) (a : ℕ → ℚ) : (ehrPoly m a).natDegree ≤ m := by
  unfold ehrPoly
  refine natDegree_sum_le_of_forall_le _ _ fun j hj => ?_
  refine (natDegree_C_mul_le _ _).trans ((binomPoly_natDegree_le j).trans ?_)
  simp only [mem_range] at hj; omega

theorem ehrPoly_coeff_top (m : ℕ) (a : ℕ → ℚ) :
    (ehrPoly m a).coeff m = a m / (m.factorial : ℚ) := by
  unfold ehrPoly
  rw [finsetSum_coeff, Finset.sum_range_succ, Finset.sum_eq_zero, zero_add, coeff_C_mul,
    binomPoly_coeff_self, div_eq_mul_inv]
  intro j hj
  simp only [mem_range] at hj
  rw [coeff_C_mul, coeff_eq_zero_of_natDegree_lt ((binomPoly_natDegree_le j).trans_lt hj),
    mul_zero]

theorem ehrPoly_eval (m : ℕ) (a : ℕ → ℚ) (k : ℕ) :
    (ehrPoly m a).eval ((k : ℚ) + 1) = ∑ j ∈ range (m + 1), (k.choose j : ℚ) * a j := by
  unfold ehrPoly
  rw [eval_finsetSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, binomPoly_eval, mul_comm]

/-- **Target 1, the matrix-algebra core** (note, Lean candidate 4).  Let `T` be an
upper unitriangular `(m+1)×(m+1)` matrix over `ℚ`, with superdiagonal
`s_l = T[l][l+1]` (`sup T l`).  Then there is a polynomial `P` of degree `≤ m`
with `P(t) = u · T^{t−1} · v` for every integer `t ≥ 1`, and its `t^m`
coefficient is `u₀ · s₀ s₁ ⋯ s_{m−1} · v_m / m!`.  `P` is explicit:
`∑_{j≤m} (u · 𝒩^j · v) · C(t−1, j)`, `𝒩 = T − I`. -/
theorem unitriangular_poly {T : Matrix (Fin (m + 1)) (Fin (m + 1)) ℚ}
    (hlow : ∀ i j, j < i → T i j = 0) (hdiag : ∀ i, T i i = 1) (u v : Fin (m + 1) → ℚ) :
    ∃ P : ℚ[X], P.natDegree ≤ m ∧
      P.coeff m = u 0 * (∏ l ∈ range m, sup T l) * v (Fin.last m) / (m.factorial : ℚ) ∧
      ∀ k : ℕ, P.eval ((k : ℚ) + 1) = u ⬝ᵥ (T ^ k *ᵥ v) := by
  refine ⟨ehrPoly m fun j => u ⬝ᵥ (offDiag T ^ j *ᵥ v), ehrPoly_natDegree_le _ _, ?_, ?_⟩
  · rw [ehrPoly_coeff_top, dotProduct_offDiag_pow_top hlow]
  · intro k
    rw [ehrPoly_eval, dotProduct_pow_mulVec hlow hdiag]


/-! ## Part B: the transfer-matrix count, for an arbitrary finite state set

Article 2's rearrangement (`Counting/Transfer.lean`, `card_chainedTuples`) is
stated for `𝓕_n` and its `Amat`; the note's remark that it "uses nothing about
`S_n`" is made literal here: any finite set `X`, any state map `σ : X → Fin m`,
and any transition predicate `cond δ k x` that depends on the previous element
only through its state `k`. -/

section Generic

variable {α : Type*} {m : ℕ} (X : Finset α) (σ : α → Fin m)
  (cond : ℤ → Fin m → α → Prop) [∀ δ k x, Decidable (cond δ k x)]

/-- Initial vector: `uG[k] = #{x ∈ X : σ x = k}`. -/
def uG : Fin m → ℕ := fun k => #(X.filter fun x => σ x = k)

/-- Transfer matrix: `TG δ [k][k'] = #{x ∈ X : σ x = k', cond δ k x}`; the row is
the previous state, the column the current one. -/
def TG (δ : ℤ) : Matrix (Fin m) (Fin m) ℕ :=
  Matrix.of fun k k' => #(X.filter fun x => σ x = k' ∧ cond δ k x)

/-- The ordered product `TG(g 0) ⋯ TG(g (r−1))`. -/
def TprodG : (r : ℕ) → (Fin r → ℤ) → Matrix (Fin m) (Fin m) ℕ
  | 0, _ => 1
  | r + 1, g => TprodG r (g ∘ Fin.castSucc) * TG X σ cond (g (Fin.last r))

/-- A chained `(r+1)`-tuple: consecutive elements satisfy the transition. -/
def ChainG {r : ℕ} (g : Fin r → ℤ) (q : Fin (r + 1) → α) : Prop :=
  ∀ i : Fin r, cond (g i) (σ (q i.castSucc)) (q i.succ)

instance {r : ℕ} (g : Fin r → ℤ) (q : Fin (r + 1) → α) : Decidable (ChainG σ cond g q) := by
  unfold ChainG; infer_instance

/-- The chained tuples over `X`, as a `Finset`. -/
def chainG (r : ℕ) (g : Fin r → ℤ) : Finset (Fin (r + 1) → α) :=
  (Fintype.piFinset fun _ => X).filter (ChainG σ cond g)

/-- Chained tuples refined by the state of their last element. -/
def chainTopG (r : ℕ) (g : Fin r → ℤ) (k : Fin m) : ℕ :=
  #((chainG X σ cond r g).filter fun q => σ (q (Fin.last r)) = k)

variable {X σ cond}

omit [∀ δ k x, Decidable (cond δ k x)] in
theorem chainG_snoc_iff {r : ℕ} {g : Fin (r + 1) → ℤ} {q : Fin (r + 1) → α} {x : α} :
    ChainG σ cond g (Fin.snoc q x) ↔
      ChainG σ cond (g ∘ Fin.castSucc) q ∧ cond (g (Fin.last r)) (σ (q (Fin.last r))) x := by
  have e : ∀ i : Fin r, (i.castSucc.succ : Fin (r + 2)) = i.succ.castSucc := fun i => Fin.ext rfl
  unfold ChainG
  rw [Fin.forall_fin_succ']
  simp only [Function.comp_apply, Fin.snoc_castSucc, e, Fin.succ_last, Fin.snoc_last]

theorem chainTopG_zero (g : Fin 0 → ℤ) (k : Fin m) : chainTopG X σ cond 0 g k = uG X σ k := by
  unfold chainTopG uG chainG
  refine Finset.card_bij' (fun q _ => q 0) (fun x _ => fun _ => x) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [mem_filter, Fintype.mem_piFinset] at hq ⊢
    exact ⟨hq.1.1 0, hq.2⟩
  · intro x hx
    simp only [mem_filter, Fintype.mem_piFinset] at hx ⊢
    exact ⟨⟨fun _ => hx.1, fun i => i.elim0⟩, hx.2⟩
  · intro q _
    funext i
    rw [show i = 0 from Fin.ext (by have := i.isLt; simp)]
  · intro x _; rfl

theorem chainTopG_succ (r : ℕ) (g : Fin (r + 1) → ℤ) (k' : Fin m) :
    chainTopG X σ cond (r + 1) g k' =
      ∑ k, chainTopG X σ cond r (g ∘ Fin.castSucc) k * TG X σ cond (g (Fin.last r)) k k' := by
  unfold chainTopG
  rw [Finset.card_eq_sum_card_fiberwise (f := fun q => σ (q (Fin.last r).castSucc))
    (t := univ) (fun _ _ => mem_univ _)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [TG, Matrix.of_apply, ← Finset.card_product]
  refine Finset.card_bij' (fun q _ => (Fin.init q, q (Fin.last (r + 1))))
    (fun p _ => Fin.snoc p.1 p.2) ?_ ?_ ?_ ?_
  · intro q hq
    simp only [chainG, mem_filter, Fintype.mem_piFinset] at hq
    obtain ⟨⟨⟨hX, hc⟩, hlast⟩, hk⟩ := hq
    rw [← Fin.snoc_init_self q] at hc
    obtain ⟨hc', hl⟩ := chainG_snoc_iff.mp hc
    simp only [chainG, mem_product, mem_filter, Fintype.mem_piFinset]
    refine ⟨⟨⟨fun i => hX _, hc'⟩, hk⟩, hX _, hlast, ?_⟩
    have : Fin.init q (Fin.last r) = q (Fin.last r).castSucc := rfl
    rw [this, hk] at hl
    exact hl
  · rintro ⟨q', x⟩ hp
    simp only [chainG, mem_product, mem_filter, Fintype.mem_piFinset] at hp
    obtain ⟨⟨⟨hX, hc⟩, hk⟩, hx, hxk, hcx⟩ := hp
    simp only [chainG, mem_filter, Fintype.mem_piFinset, Fin.snoc_last, Fin.snoc_castSucc]
    refine ⟨⟨⟨fun i => ?_, chainG_snoc_iff.mpr ⟨hc, by rw [hk]; exact hcx⟩⟩, hxk⟩, hk⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [Fin.snoc_last]; exact hx
    · rw [Fin.snoc_castSucc]; exact hX j
  · intro q _; exact Fin.snoc_init_self q
  · rintro ⟨q', x⟩ _
    simp only [Fin.init_snoc, Fin.snoc_last]

theorem chainTopG_eq (r : ℕ) (g : Fin r → ℤ) :
    chainTopG X σ cond r g = uG X σ ᵥ* TprodG X σ cond r g := by
  induction r with
  | zero =>
    funext k
    rw [TprodG, Matrix.vecMul_one, chainTopG_zero]
  | succ r ih =>
    funext k'
    rw [chainTopG_succ, TprodG, ← Matrix.vecMul_vecMul, ← ih]
    rfl

/-- **The generic transfer-matrix count**: `#(chained tuples) = u · TG(g₀)⋯TG(g_{r−1}) · 𝟙`. -/
theorem card_chainG (r : ℕ) (g : Fin r → ℤ) :
    #(chainG X σ cond r g) = uG X σ ᵥ* TprodG X σ cond r g ⬝ᵥ (fun _ => 1) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun q => σ (q (Fin.last r)))
    (t := univ) (fun _ _ => mem_univ _), ← chainTopG_eq]
  simp [dotProduct, chainTopG]

/-- With a constant gap the product is a power. -/
theorem TprodG_const (r : ℕ) (δ : ℤ) :
    TprodG X σ cond r (fun _ => δ) = TG X σ cond δ ^ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [TprodG, pow_succ]
    exact congrArg (· * _) ih

end Generic

/-! ## Part C: the lattice-point transfer matrix of `Koz(n)`

States are the tops `τ ∈ {1, …, n}` of lattice points of `Koz(n)` (every lattice
point has `x₁ = n > 0`, so `tp ≥ 1`), encoded as `τ − 1 ∈ Fin n`. -/

open _root_.ExteriorConvex.Lattice

section LatticeT

variable {n : ℕ}

/-- The state of a lattice point: `tp(x) − 1 ∈ Fin n` (clamped, so the definition is
total; on lattice points the clamp is inactive, `stL_val`). -/
def stL (n : ℕ) [NeZero n] (x : Fin (n + 1) → ℤ) : Fin n :=
  ⟨min ((top (toN x)).toNat - 1) (n - 1), by have := NeZero.pos n; omega⟩

/-- The transition of `def-uT` read off the note's `T(δ)[τ][τ'] = #{x : tp(x) = τ',
indeg(x) + δ > τ}`: previous state `k` (top `k+1`), current point `x`. -/
def condL (n : ℕ) (δ : ℤ) (k : Fin n) (x : Fin (n + 1) → ℤ) : Prop :=
  (k.val : ℤ) + 1 - δ < (indeg (toN x) : ℤ)

instance (n : ℕ) (δ : ℤ) (k : Fin n) (x : Fin (n + 1) → ℤ) : Decidable (condL n δ k x) := by
  unfold condL; infer_instance

/-- The note's `u^L`: `uL[τ−1] = #{x ∈ 𝓛_n : tp(x) = τ}`. -/
abbrev uL (n : ℕ) [NeZero n] : Fin n → ℕ := uG (latticeFinset n) (stL n)

/-- The note's `T^L(δ)`. -/
abbrev TL (n : ℕ) [NeZero n] (δ : ℤ) : Matrix (Fin n) (Fin n) ℕ :=
  TG (latticeFinset n) (stL n) (condL n) δ

/-- The ordered product `T^L(δ₂) ⋯ T^L(δ_r)`. -/
abbrev TprodL (n : ℕ) [NeZero n] (r : ℕ) (g : Fin r → ℤ) : Matrix (Fin n) (Fin n) ℕ :=
  TprodG (latticeFinset n) (stL n) (condL n) r g

theorem one_le_of_neZero [NeZero n] : 1 ≤ n := NeZero.one_le

theorem toN_one (hn : 1 ≤ n) {x : Fin (n + 1) → ℤ} (hx : x ∈ latticePts n) :
    toN x ⟨1, by omega⟩ = n := by
  rw [latticePts_eq_intLYM hn] at hx
  have h1 : x ⟨1, by omega⟩ = n := by
    have := hx.2.1
    rwa [show (1 : Fin (n + 1)) = ⟨1, by omega⟩ from Fin.ext (by simp; omega)] at this
  simp [toN, h1]

theorem toN_zero' (hn : 1 ≤ n) {x : Fin (n + 1) → ℤ} (hx : x ∈ latticePts n) :
    toN x 0 = 1 := by
  rw [latticePts_eq_intLYM hn] at hx
  simp [toN, hx.1]

theorem one_le_top (hn : 1 ≤ n) {x : Fin (n + 1) → ℤ} (hx : x ∈ latticePts n) :
    1 ≤ top (toN x) := by
  have := le_top_of_pos (s := toN x) (j := ⟨1, by omega⟩) (by rw [toN_one hn hx]; omega)
  simpa using this

theorem two_le_indeg (hn : 1 ≤ n) {x : Fin (n + 1) → ℤ} (hx : x ∈ latticePts n) :
    2 ≤ indeg (toN x) := by
  rw [le_indeg_iff (by omega)]
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
  · have : j = 0 := Fin.ext (by simpa using h)
    subst this; rw [toN_zero' hn hx]; simp
  · have : j = ⟨1, by omega⟩ := Fin.ext h
    rw [this, toN_one hn hx]; simp

theorem stL_val [NeZero n] {x : Fin (n + 1) → ℤ} (hx : x ∈ latticePts n) :
    ((stL n x).val : ℤ) + 1 = top (toN x) := by
  have h1 := one_le_top one_le_of_neZero hx
  have h2 := top_le (toN x)
  simp only [stL]
  omega

theorem stL_eq_iff [NeZero n] {x : Fin (n + 1) → ℤ} (hx : x ∈ latticePts n) (k : Fin n) :
    stL n x = k ↔ top (toN x) = (k.val : ℤ) + 1 := by
  rw [← stL_val hx, Fin.ext_iff]
  omega

/-- On lattice tuples, article 2's absolute chaining condition `Chained` (as used
by `chained_unique`) is exactly the generic transition chain with the
ℤ-gaps `δᵢ = d_{i+1} − d_i`. -/
theorem chained_iff_chainG [NeZero n] {r : ℕ} (d : Fin (r + 1) → ℕ)
    {q : Fin (r + 1) → Fin (n + 1) → ℤ} (hq : ∀ i, q i ∈ latticePts n) :
    Chained d (fun i => toN (q i)) ↔ ChainG (stL n) (condL n) (gaps d) q := by
  unfold Chained ChainG condL gaps hatTop hatIndeg
  beta_reduce
  constructor
  · intro h i
    have := h (i := i.castSucc) (j := i.succ) (by simp)
    have e := stL_val (hq i.castSucc)
    omega
  · intro h i j hij
    have hi : i.val < r := by have := j.isLt; omega
    have h1 := h ⟨i.val, hi⟩
    have ei : (⟨i.val, hi⟩ : Fin r).castSucc = i := Fin.ext rfl
    have ej : (⟨i.val, hi⟩ : Fin r).succ = j := Fin.ext (by simp; omega)
    rw [ei, ej] at h1
    have e := stL_val (hq i)
    omega

/-- `thm-chained`'s real chaining `ChainedR` implies article 2's `Chained` on
lattice tuples, for sorted `d`. -/
theorem chained_of_chainedR (hn : 1 ≤ n) {r : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    {q : Fin r → Fin (n + 1) → ℤ} (hq : ∀ i, q i ∈ latticePts n)
    (hc : ChainedR d fun i => castR (q i)) : Chained d fun i => toN (q i) := by
  intro i j hij
  unfold hatTop hatIndeg
  beta_reduce
  by_contra hcon
  obtain ⟨m, hm, hpos⟩ := exists_apply_pos_of_top_nonneg
    (le_trans (by norm_num) (one_le_top hn (hq i)))
  have hposR : 0 < castR (q i) m := by
    have := toN_cast hn (hq i) m
    simp only [castR_apply]
    have : 0 < q i m := by omega
    exact_mod_cast this
  have hdij : d i ≤ d j := hd (Fin.le_def.mpr (by omega))
  rcases le_or_gt (indeg (toN (q j))) n with hle | hgt
  · obtain ⟨m', hm', hlt⟩ := exists_apply_lt_choose_of_indeg_le hle
    have := hc hij m m' hposR (by omega)
    simp only [castR_apply] at this
    have h2 : q j m' = n.choose m'.val := by exact_mod_cast this
    have h3 := toN_cast hn (hq j) m'
    omega
  · have := top_le (toN (q i))
    have := indeg_le (toN (q j))
    omega

/-- The lattice points of `Koz(n; d⃗)` (in `ℤ^{N+1}`), as a set. -/
def kozLattice (n : ℕ) {r N : ℕ} (d : Fin r → ℕ) : Set (Fin (N + 1) → ℤ) :=
  {z | castR z ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)}

theorem mem_chainG_lattice [NeZero n] {r : ℕ} {g : Fin r → ℤ}
    {q : Fin (r + 1) → Fin (n + 1) → ℤ} :
    q ∈ chainG (latticeFinset n) (stL n) (condL n) r g ↔
      (∀ i, q i ∈ latticePts n) ∧ ChainG (stL n) (condL n) g q := by
  simp [chainG, Fintype.mem_piFinset, mem_latticeFinset one_le_of_neZero]

/-- **Target 2, the transfer corollary** (note, "Corollary: counting lattice points
and Ehrhart polynomials by transfer matrix", first display):
`#(Koz(n; d⃗) ∩ ℤ) = u^L · T^L(δ₂) ⋯ T^L(δ_r) · 𝟙`, for sorted `d⃗` (rank `r+1`
here, gaps `δ_{i+1} = d_{i+1} − d_i` as `gaps d`).  The proof is the note's: the
bijection with chained tuples of `𝓛_n` (`existsUnique_chained_lattice`, via
`waterFill_spec` and `chained_unique`), then article 2's rearrangement
(`card_chainG`). -/
theorem ncard_kozLattice [NeZero n] {r N : ℕ} (d : Fin (r + 1) → ℕ) (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) :
    (kozLattice n (N := N) d).ncard = uL n ᵥ* TprodL n r (gaps d) ⬝ᵥ (fun _ => 1) := by
  have hn : 1 ≤ n := one_le_of_neZero
  set C := chainG (latticeFinset n) (stL n) (condL n) r (gaps d)
  let S : (Fin (r + 1) → Fin (n + 1) → ℤ) → (Fin (N + 1) → ℤ) :=
    fun q => ∑ i, shiftZ N (d i) (q i)
  have hcast : ∀ q : Fin (r + 1) → Fin (n + 1) → ℤ,
      castR (S q) = ∑ i, shiftIncl N (d i) (castR (q i)) := by
    intro q
    simp only [S, castR_sum, castR_shiftZ]
  have himg : kozLattice n (N := N) d = S '' (C : Set _) := by
    ext z
    constructor
    · intro hz
      obtain ⟨hmem, hc, hsum⟩ := waterFill_spec hn hd hN hz
      refine ⟨waterFill n d z, ?_, hsum⟩
      rw [Finset.mem_coe, mem_chainG_lattice]
      exact ⟨hmem, (chained_iff_chainG d hmem).mp (chained_of_chainedR hn hd hmem hc)⟩
    · rintro ⟨q, hq, rfl⟩
      rw [Finset.mem_coe, mem_chainG_lattice] at hq
      show castR (S q) ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)
      rw [hcast]
      refine Set.finsetSum_mem_finsetSum _ _ _ fun i _ => ?_
      rw [hull_Sset_eq hn]
      exact Set.mem_image_of_mem _ ((mem_latticePts_iff hn _).mp (hq.1 i))
  have hinj : Set.InjOn S (C : Set _) := by
    intro p hp q hq hpq
    rw [Finset.mem_coe, mem_chainG_lattice] at hp hq
    refine chained_unique hn d hN hp.1 hq.1 ((chained_iff_chainG d hp.1).mpr hp.2)
      ((chained_iff_chainG d hq.1).mpr hq.2) ?_
    rw [← hcast, ← hcast, hpq]
  rw [himg, hinj.ncard_image, Set.ncard_coe_finset, card_chainG]

/-- The lattice points of the dilate `t·Koz(n)`, `t ∈ ℕ`. -/
def dilateLattice (n t : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {z | castR z ∈ (t : ℝ) • convexHull ℝ (Sset n)}

theorem shiftIncl_zero_eq : (shiftIncl n 0 : (Fin (n + 1) → ℝ) → _) = id := by
  funext x j
  rw [shiftIncl_apply, dite_eq_left ⟨Nat.zero_le _, by omega⟩]
  rfl

/-- `(k+1)·Koz(n) = Koz(n; 0, …, 0)` (`k+1` zeros, `N = n`). -/
theorem dilateLattice_eq (hn : 1 ≤ n) (k : ℕ) :
    dilateLattice n (k + 1) = kozLattice n (N := n) (fun _ : Fin (k + 1) => 0) := by
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  ext z
  simp only [dilateLattice, kozLattice, Set.mem_ofPred_eq, shiftIncl_zero_eq, Set.image_id,
    hull_Sset_eq hn, sum_lymChain hn, smul_lymChain hpos]

/-- **The Ehrhart corollary, counting half** (note, Corollary (a), first clause):
`L_{Koz(n)}(t) = #(t·Koz(n) ∩ ℤ) = u^L · T₀^{t−1} · 𝟙`, `T₀ = T^L(0)`, for `t ≥ 1`. -/
theorem ncard_dilateLattice [NeZero n] (k : ℕ) :
    (dilateLattice n (k + 1)).ncard = uL n ᵥ* TL n 0 ^ k ⬝ᵥ (fun _ => 1) := by
  rw [dilateLattice_eq one_le_of_neZero, ncard_kozLattice _ (fun _ _ _ => le_rfl)
    (fun _ => by omega)]
  have : gaps (fun _ : Fin (k + 1) => (0 : ℕ)) = fun _ => (0 : ℤ) := by
    funext i; simp [gaps]
  rw [this, TprodL, TprodG_const]

/-! ### The shape of `T₀ = T^L(0)`: upper unitriangular, superdiagonal `C(n, τ+1)` -/

/-- The staircase vector: full (`C(n,m)`) in degrees `m ≤ p`, the value `v` in
degree `p+1`, zero beyond. -/
def stair (n p : ℕ) (v : ℤ) : Fin (n + 1) → ℤ := fun m =>
  if m.val ≤ p then (n.choose m.val : ℤ) else if m.val = p + 1 then v else 0

theorem stair_of_le {p : ℕ} {v : ℤ} {m : Fin (n + 1)} (h : m.val ≤ p) :
    stair n p v m = n.choose m.val := by simp [stair, h]

theorem stair_of_eq {p : ℕ} {v : ℤ} {m : Fin (n + 1)} (h : m.val = p + 1) :
    stair n p v m = v := by simp [stair, h]

theorem stair_of_gt {p : ℕ} {v : ℤ} {m : Fin (n + 1)} (h : p + 1 < m.val) :
    stair n p v m = 0 := by
  simp only [stair]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

theorem stair_nonneg {p : ℕ} {v : ℤ} (hv0 : 0 ≤ v) (m : Fin (n + 1)) : 0 ≤ stair n p v m := by
  rcases le_or_gt m.val p with h | h
  · rw [stair_of_le h]; positivity
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
    · rw [stair_of_eq h'.symm]; exact hv0
    · rw [stair_of_gt h']

theorem stair_le {p : ℕ} {v : ℤ} (hv : v ≤ (n.choose (p + 1) : ℤ)) (m : Fin (n + 1)) :
    stair n p v m ≤ n.choose m.val := by
  rcases le_or_gt m.val p with h | h
  · rw [stair_of_le h]
  · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
    · rw [stair_of_eq h'.symm, ← h']; exact hv
    · rw [stair_of_gt h']; positivity

theorem stair_mem (hn : 1 ≤ n) {p : ℕ} (hp : 1 ≤ p) {v : ℤ} (hv0 : 0 ≤ v)
    (hv : v ≤ (n.choose (p + 1) : ℤ)) : stair n p v ∈ latticePts n := by
  rw [← mem_latticeFinset hn]
  simp only [latticeFinset, mem_filter, Fintype.mem_piFinset, Finset.mem_Icc]
  refine ⟨fun m => ⟨stair_nonneg hv0 m, stair_le hv m⟩, ?_, ?_, ?_, stair_nonneg hv0 _⟩
  · rw [stair_of_le (by simp)]; simp
  · have : ((1 : Fin (n + 1)) : ℕ) = 1 := by
      rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
    rw [stair_of_le (by omega), this]; simp
  · intro j k hk hj
    rcases le_or_gt k.val p with h | h
    · rw [stair_of_le h, stair_of_le (by omega), mul_comm]
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
      · rw [stair_of_eq h'.symm, stair_of_le (by omega), mul_comm]
        have : k.val = p + 1 := h'.symm
        rw [this]
        exact mul_le_mul_of_nonneg_left hv (by positivity)
      · rw [stair_of_gt h', zero_mul]
        exact mul_nonneg (stair_nonneg hv0 j) (by positivity)

theorem toN_stair (n p : ℕ) {v : ℤ} (hv0 : 0 ≤ v) (m : Fin (n + 1)) :
    ((toN (stair n p v) m : ℕ) : ℤ) = stair n p v m :=
  Int.toNat_of_nonneg (stair_nonneg hv0 m)

theorem top_eq_of {s : Fin (n + 1) → ℕ} (T : Fin (n + 1)) (hT : 0 < s T)
    (hz : ∀ j : Fin (n + 1), T.val < j.val → s j = 0) : top s = T.val := by
  have h1 := le_top_of_pos hT
  by_contra hne
  obtain ⟨j, hj, hpos⟩ := exists_apply_pos_of_top_nonneg (s := s) (by omega)
  have := hz j (by omega)
  omega

theorem top_stair_pos {p : ℕ} (hp : p + 1 ≤ n) {v : ℤ} (hv : 0 < v) :
    top (toN (stair n p v)) = (p : ℤ) + 1 := by
  have := top_eq_of (s := toN (stair n p v)) ⟨p + 1, by omega⟩ ?_ ?_
  · rw [this]; simp
  · have h := toN_stair n p hv.le ⟨p + 1, by omega⟩
    rw [stair_of_eq rfl] at h
    omega
  · intro j hj
    have h := toN_stair n p hv.le j
    rw [stair_of_gt (by simpa using hj)] at h
    omega

theorem top_stair_zero {p : ℕ} (hp : p ≤ n) : top (toN (stair n p 0)) = p := by
  have := top_eq_of (s := toN (stair n p 0)) ⟨p, by omega⟩ ?_ ?_
  · rw [this]
  · have h := toN_stair n p le_rfl ⟨p, by omega⟩
    rw [stair_of_le (show (⟨p, by omega⟩ : Fin (n + 1)).val ≤ p from le_rfl)] at h
    simp only at h
    have : 0 < n.choose p := Nat.choose_pos hp
    omega
  · intro j hj
    have hj' : p < j.val := by simpa using hj
    have h := toN_stair n p le_rfl j
    rcases eq_or_lt_of_le (Nat.succ_le_of_lt hj') with h' | h'
    · rw [stair_of_eq h'.symm] at h; omega
    · rw [stair_of_gt h'] at h; omega

theorem le_indeg_stair {p : ℕ} (hp : p ≤ n) {v : ℤ} (hv0 : 0 ≤ v) :
    p + 1 ≤ indeg (toN (stair n p v)) := by
  rw [le_indeg_iff (by omega)]
  intro j hj
  have h := toN_stair n p hv0 j
  rw [stair_of_le (by omega)] at h
  omega

/-- A lattice point that is full up to degree `p` and has top `≤ p+1` is a staircase. -/
theorem eq_stair_of (hn : 1 ≤ n) {x : Fin (n + 1) → ℤ} (hx : x ∈ latticePts n) {p : ℕ}
    (hfull : p + 1 ≤ indeg (toN x)) (htop : top (toN x) ≤ (p : ℤ) + 1) {v : ℤ}
    (hv : ∀ m : Fin (n + 1), m.val = p + 1 → x m = v) : x = stair n p v := by
  funext m
  unfold stair
  split_ifs with h1 h2
  · have h3 := choose_le_of_lt_indeg (s := toN x) (j := m) (by omega)
    have h4 := toN_le_choose hn hx m
    rw [← toN_cast hn hx m]
    exact_mod_cast le_antisymm h4 h3
  · exact hv m h2
  · have := apply_eq_zero_of_top_lt (s := toN x) (j := m) (by omega)
    rw [← toN_cast hn hx m, this]; rfl

variable [NeZero n]

theorem TL_apply (δ : ℤ) (a b : Fin n) :
    TL n δ a b = #((latticeFinset n).filter fun x => stL n x = b ∧ condL n δ a x) := rfl

/-- `T₀` is upper triangular. -/
theorem TL0_lower {a b : Fin n} (h : b < a) : TL n 0 a b = 0 := by
  rw [TL_apply, card_eq_zero, filter_eq_empty_iff]
  rintro x hx ⟨hst, hc⟩
  rw [mem_latticeFinset one_le_of_neZero] at hx
  rw [stL_eq_iff hx] at hst
  have := indeg_le_top_add_one (toN x)
  unfold condL at hc
  have : b.val < a.val := h
  omega

/-- `T₀` has unit diagonal: the only lattice point with `tp = τ` and `indeg > τ` is
the vertex `F̃_τ`. -/
theorem TL0_diag (a : Fin n) : TL n 0 a a = 1 := by
  have hn : 1 ≤ n := one_le_of_neZero
  rw [TL_apply, card_eq_one]
  refine ⟨stair n (a.val + 1) 0, Finset.ext fun x => ?_⟩
  rw [Finset.mem_filter]
  simp only [Finset.mem_singleton, condL]
  constructor
  · rintro ⟨hx, hst, hc⟩
    rw [mem_latticeFinset hn] at hx
    rw [stL_eq_iff hx] at hst
    refine eq_stair_of hn hx (by omega) (by omega) fun m hm => ?_
    have := apply_eq_zero_of_top_lt (s := toN x) (j := m) (by omega)
    rw [← toN_cast hn hx m, this]; rfl
  · rintro rfl
    have hmem := stair_mem hn (p := a.val + 1) (by omega) le_rfl (by positivity)
    have hp : a.val + 1 ≤ n := a.isLt
    refine ⟨(mem_latticeFinset hn _).mpr hmem, ?_, ?_⟩
    · rw [stL_eq_iff hmem, top_stair_zero hp]; push_cast; ring
    · have := le_indeg_stair (n := n) hp (le_refl (0 : ℤ))
      omega

/-- The superdiagonal of `T₀`: `T₀[τ][τ+1] = C(n, τ+1)` (here `τ = a+1`). -/
theorem TL0_sup (a : Fin n) (ha : a.val + 1 < n) :
    TL n 0 a ⟨a.val + 1, ha⟩ = n.choose (a.val + 2) := by
  have hn : 1 ≤ n := one_le_of_neZero
  rw [TL_apply]
  have himg : (latticeFinset n).filter (fun x => stL n x = ⟨a.val + 1, ha⟩ ∧ condL n 0 a x) =
      (Finset.Icc (1 : ℤ) (n.choose (a.val + 2))).image (stair n (a.val + 1)) := by
    refine Finset.ext fun x => ?_
    rw [Finset.mem_filter]
    simp only [Finset.mem_image, Finset.mem_Icc, condL]
    constructor
    · rintro ⟨hx, hst, hc⟩
      rw [mem_latticeFinset hn] at hx
      rw [stL_eq_iff hx] at hst
      simp only at hst
      set m0 : Fin (n + 1) := ⟨a.val + 2, by omega⟩
      have hpos : 0 < x m0 := by
        obtain ⟨j, hj, hjp⟩ := exists_apply_pos_of_top_nonneg (s := toN x) (by omega)
        have : j = m0 := Fin.ext (by simp [m0]; omega)
        rw [this] at hjp
        have := toN_cast hn hx m0
        omega
      have hle := (box_of_mem_latticePts hn hx m0).2
      refine ⟨x m0, ⟨hpos, hle⟩, ?_⟩
      refine (eq_stair_of hn hx (by omega) (by omega) fun m hm => ?_).symm
      rw [show m = m0 from Fin.ext hm]
    · rintro ⟨v, ⟨hv1, hv2⟩, rfl⟩
      have hmem := stair_mem hn (p := a.val + 1) (by omega) (by omega) hv2
      refine ⟨(mem_latticeFinset hn _).mpr hmem, ?_, ?_⟩
      · rw [stL_eq_iff hmem, top_stair_pos (by omega) (by omega)]
      · have := le_indeg_stair (n := n) (p := a.val + 1) (by omega) (by omega : (0 : ℤ) ≤ v)
        omega
  rw [himg, card_image_of_injOn, Int.card_Icc]
  · omega
  · intro v _ w _ hvw
    have := congrFun hvw ⟨a.val + 2, by omega⟩
    simpa [stair] using this

/-- `u^L` is the first row of `T₀`, since every lattice point has `indeg ≥ 2`. -/
theorem uL_eq_row (k : Fin n) : uL n k = TL n 0 ⟨0, NeZero.pos n⟩ k := by
  have hn : 1 ≤ n := one_le_of_neZero
  rw [TL_apply]
  unfold uL uG
  congr 1
  refine Finset.filter_congr fun x hx => ?_
  rw [mem_latticeFinset hn] at hx
  have := two_le_indeg hn hx
  simp only [condL]
  constructor
  · intro h; exact ⟨h, by omega⟩
  · exact fun h => h.1

/-- `u^L[τ = 1] = 1`: the only lattice point with `tp = 1` is `(1, n, 0, …, 0)`. -/
theorem uL_zero : uL n ⟨0, NeZero.pos n⟩ = 1 := by
  rw [uL_eq_row, TL0_diag]

/-! ## Stretch: the Ehrhart polynomial of `Koz(n)` -/

/-- The cast of `T₀` to `ℚ`. -/
noncomputable def T0Q (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℚ :=
  (Nat.castRingHom ℚ).mapMatrix (TL n 0)

theorem cast_count (k : ℕ) :
    ((uL n ᵥ* TL n 0 ^ k ⬝ᵥ (fun _ => 1) : ℕ) : ℚ) =
      (fun i => (uL n i : ℚ)) ⬝ᵥ (T0Q n ^ k *ᵥ fun _ => 1) := by
  rw [T0Q, ← map_pow, ← Matrix.dotProduct_mulVec]
  simp [dotProduct, Matrix.mulVec, RingHom.mapMatrix_apply]

/-- **Stretch target: the Ehrhart polynomial of `Koz(n)`** (note, Corollary (a)):
there is a polynomial `L ∈ ℚ[t]` of degree `≤ n − 1` with `L(t) = #(t·Koz(n) ∩ ℤ^{n+1})`
for every integer `t ≥ 1`, whose `t^{n−1}` coefficient is
`∏_{k=2}^{n} C(n,k) / (n−1)!` — i.e. `NV(Koz(n))/(n−1)!`, with `NV` the
determinant of `Lattice/Volume.lean` (`ehrhart_koz_leading_eq_det`).
Since that coefficient is nonzero, the degree is exactly `n − 1`
(`ehrhart_koz_exact`). -/
theorem ehrhart_koz (n : ℕ) [NeZero n] :
    ∃ P : ℚ[X], P.natDegree ≤ n - 1 ∧
      P.coeff (n - 1) = (∏ k ∈ Icc 2 n, (n.choose k : ℚ)) / ((n - 1).factorial : ℚ) ∧
      ∀ t : ℕ, 1 ≤ t → P.eval (t : ℚ) = (dilateLattice n t).ncard := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := NeZero.pos n; omega⟩
  have hlow : ∀ i j : Fin (m + 1), j < i → T0Q (m + 1) i j = 0 := by
    intro i j h; simp [T0Q, RingHom.mapMatrix_apply, TL0_lower h]
  have hdiag : ∀ i : Fin (m + 1), T0Q (m + 1) i i = 1 := by
    intro i; simp [T0Q, RingHom.mapMatrix_apply, TL0_diag]
  obtain ⟨P, hdeg, hcoeff, heval⟩ :=
    unitriangular_poly hlow hdiag (fun i => (uL (m + 1) i : ℚ)) (fun _ => 1)
  refine ⟨P, by simpa using hdeg, ?_, ?_⟩
  · rw [show m + 1 - 1 = m from rfl, hcoeff]
    have hu : (uL (m + 1) 0 : ℚ) = 1 := by
      have := uL_zero (n := m + 1); exact_mod_cast this
    have hsup : ∀ l ∈ range m, sup (T0Q (m + 1)) l = ((m + 1).choose (l + 2) : ℚ) := by
      intro l hl
      rw [mem_range] at hl
      simp only [sup, show l + 1 < m + 1 by omega, dite_true, T0Q, RingHom.mapMatrix_apply,
        Matrix.map_apply, eq_natCast]
      have := TL0_sup (n := m + 1) ⟨l, by omega⟩ (by simp; omega)
      simp only at this
      rw [this]
    rw [hu, Finset.prod_congr rfl hsup, one_mul, mul_one]
    congr 1
    have := KozVolume.prod_choose_shift (n := m + 1) (fun k => ((m + 1).choose k : ℚ))
    rw [← this, Fin.prod_univ_eq_prod_range (fun a => ((m + 1).choose (a + 2) : ℚ))]
    rfl
  · intro t ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    rw [Nat.cast_add, Nat.cast_one, heval, ncard_dilateLattice, cast_count]

/-- The Ehrhart polynomial with its exact degree `n − 1` and leading coefficient
`NV(Koz(n))/(n−1)!`, `NV` being the vertex-difference determinant
`KozVolume.vdiffZ` of `Lattice/Volume.lean` (`vdiff_det_int`: `= ∏_{k=2}^n C(n,k)`). -/
theorem ehrhart_koz_exact (n : ℕ) [NeZero n] :
    ∃ P : ℚ[X], P.natDegree = n - 1 ∧
      P.leadingCoeff = ((KozVolume.vdiffZ n).det : ℚ) / ((n - 1).factorial : ℚ) ∧
      ∀ t : ℕ, 1 ≤ t → P.eval (t : ℚ) = (dilateLattice n t).ncard := by
  obtain ⟨P, hdeg, hcoeff, heval⟩ := ehrhart_koz n
  have hne : P.coeff (n - 1) ≠ 0 := by
    rw [hcoeff]
    refine div_ne_zero (prod_ne_zero_iff.mpr fun k hk => ?_) ?_
    · rw [mem_Icc] at hk; exact_mod_cast (Nat.choose_pos hk.2).ne'
    · exact_mod_cast (Nat.factorial_pos _).ne'
  have hd : P.natDegree = n - 1 := le_antisymm hdeg (le_natDegree_of_ne_zero hne)
  refine ⟨P, hd, ?_, heval⟩
  rw [leadingCoeff, hd, hcoeff, KozVolume.vdiff_det_int]
  push_cast; rfl

end LatticeT

end TransferEhrhart

end ExteriorConvex
