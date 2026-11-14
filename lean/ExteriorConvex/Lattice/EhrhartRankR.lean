/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The rank-`r` Ehrhart polynomial of `Koz(n; d⃗)`: display, `P(0) = 1`, linear coefficient

Formalisation of article 3 (`article/exterior-convex_article3_draft_4.org`),
§"Lattice points and Ehrhart polynomials by transfer matrix" and §"Rank two and higher":
the second display of `cor-transfer`, the constant term of the Ehrhart polynomials of
`cor-zero-shift` / `obs-dilates`, and `prop-linear-coeff` (roadmap
`working-notes/lean-roadmap-article3-2026-10-21.org`, items 7 and 8). Builds on
`Lattice/TransferEhrhart.lean` (`ncard_kozLattice`, `TL`, `TprodL`, `unitriangular_poly`'s
`binomPoly`, `pow_eq_sum_choose`, `TL0_*`, `uL_eq_row`).

**Normalisation.** As in `TransferEhrhart.lean`: degree-0-inclusive coordinates, `[NeZero n]`,
`d : Fin (r+1) → ℕ` sorted (`Monotone d`), i.e. **Lean's `r+1` is the paper's rank `r`**, gaps
`δ_{i+1} = d_{i+1} − d_i` as `gaps d : Fin r → ℤ`, `dᵢ + n ≤ N`. The dilate's lattice points are
`dilKozLattice n t d = {z ∈ ℤ^{N+1} : z ∈ t·Koz(n; d⃗)}`.

* `dRep k d` = `d⃗^{(k+1)}` (each shift repeated `k+1` times, indexed through
  `Fin (r+1) × Fin (k+1) ≃ Fin ((r+1)(k+1))`), `smul_koz_eq` / `dilKozLattice_eq`:
  `t·Koz(n; d⃗) = Koz(n; d⃗^{(t)})`; `gaps_dRep_natAdd` (the gaps of `d⃗^{(t)}`: `δᵢ` between
  blocks, `0` inside), `TprodL_dRep` (the transfer product of `d⃗^{(t)}` is the display product
  `dispProd`).
* `ehrhart_display` — **`cor-transfer`, second display**, exactly as printed:
  `#(t·Koz(n;d⃗) ∩ ℤ) = u^L T₀^{t−1} T^L(δ₂) T₀^{t−1} ⋯ T^L(δ_r) T₀^{t−1} 𝟙`, `t ≥ 1`.
* Polynomiality: `ehrPolyR` replaces `T₀^{t−1}` by `M(t) = ∑_j C(t−1, j) 𝒩^j` (`MQ`,
  `MQ_eval`); `ehrhart_rankR` (agreement for `t ≥ 1`), `ehrhart_rankR_all` (every `t ∈ ℕ`,
  `t = 0` included). Not obviously polynomial in the printed form; the binomial expansion of
  each of the `r` copies of `T₀^{t−1}` is the whole argument. No degree bound is claimed here.
* `P(0) = 1`: `M(0) = T₀^{−1}` (`T0Q_mul_M0`, via `C(−1, j) = (−1)^j`), `u^L = e₀T₀`
  (`uQ_eq`), and the **row shift** `TL_row_shift`: for `δ ≥ 0`, row `τ` of `T^L(δ)` is row
  `max(τ−δ, 1)` of `T₀`. Hence `u^L M(0) A M(0) ⋯ = e₀` (`uQ_dispProd_M0`).
  `ehrhart_rankR_eval_zero` (rank `r`), `ehrhart_koz_eval_zero` / `ehrhart_koz'` (the
  `P` of `TransferEhrhart.ehrhart_koz`).
* `prop_linear_coeff` — **`prop-linear-coeff`**: `[t¹]P = (r+1)·[t¹]Q` for any `P`, `Q`
  agreeing with the counts of `t·Koz(n;d⃗)` and `t·Koz(n)` for `t ≥ 1`.

**Deviation from the paper's proof of `prop-linear-coeff`.** The paper cites McMullen's
mixed-Ehrhart polynomiality; Mathlib has no McMullen. The proof here is internal to the
transfer matrix: with `M(t) = M₀ + M₁t + ⋯`, the linear coefficient of
`u M A₁ M ⋯ A_r M 𝟙` is a sum over the `r+1` positions of `M₁`, and each term reduces to
`u M₁ 𝟙` by `u M₀ A M₀ ⋯ = e₀`, `e₀A = e₀T₀ = u` (left side) and `A M₀ 𝟙 = 𝟙` (right side,
`TQ_M0_one`) — both consequences of the row shift. Sortedness (`δ ≥ 0`) is used; the paper's
"every `d⃗`" is read as every sorted `d⃗` (the Minkowski sum does not depend on the order).

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Lattice.TransferEhrhart

open Finset Matrix Polynomial
open scoped Pointwise

namespace ExteriorConvex

namespace EhrhartRankR

open _root_.ExteriorConvex.Lattice _root_.ExteriorConvex.TransferEhrhart

/-! ## Part 1: the repeated shift vector `d⃗^{(t)}`, `t = k+1` -/

/-- `rk k r = (r+1)(k+1) − 1`, defined by recursion so that
`Fin (rk k (r+1)) = Fin (rk k r + (k+1))` definitionally. -/
def rk (k : ℕ) : ℕ → ℕ
  | 0 => k
  | r + 1 => rk k r + (k + 1)

theorem rk_eq (k r : ℕ) : rk k r = r * (k + 1) + k := by
  induction r with
  | zero => simp [rk]
  | succ r ih => rw [rk, ih]; ring

theorem rk_succ_eq (k r : ℕ) : rk k r + 1 = (r + 1) * (k + 1) := by
  rw [rk_eq]; ring

/-- The block decomposition `Fin (r+1) × Fin (k+1) ≃ Fin ((r+1)(k+1))`. -/
def blkEquiv (k r : ℕ) : Fin (r + 1) × Fin (k + 1) ≃ Fin (rk k r + 1) :=
  finProdFinEquiv.trans (finCongr (rk_succ_eq k r).symm)

theorem blkEquiv_symm_fst (k r : ℕ) (j : Fin (rk k r + 1)) :
    ((blkEquiv k r).symm j).1.val = j.val / (k + 1) := by
  simp [blkEquiv, finProdFinEquiv_symm_apply, Fin.coe_divNat]

/-- `d⃗^{(k+1)}`: each shift `dᵢ` repeated `k+1` times. -/
def dRep (k : ℕ) {r : ℕ} (d : Fin (r + 1) → ℕ) : Fin (rk k r + 1) → ℕ :=
  fun j => d ((blkEquiv k r).symm j).1

theorem div_lt_of_le_rk {k r j : ℕ} (hj : j < rk k r + 1) : j / (k + 1) < r + 1 := by
  rw [Nat.div_lt_iff_lt_mul (by omega), ← rk_succ_eq]; exact hj

theorem dRep_apply (k : ℕ) {r : ℕ} (d : Fin (r + 1) → ℕ) (j : Fin (rk k r + 1)) :
    dRep k d j = d ⟨j.val / (k + 1), div_lt_of_le_rk j.isLt⟩ := by
  unfold dRep; congr 1

theorem dRep_blk (k : ℕ) {r : ℕ} (d : Fin (r + 1) → ℕ) (i : Fin (r + 1)) (s : Fin (k + 1)) :
    dRep k d (blkEquiv k r (i, s)) = d i := by
  simp [dRep]

theorem dRep_monotone (k : ℕ) {r : ℕ} {d : Fin (r + 1) → ℕ} (hd : Monotone d) :
    Monotone (dRep k d) := by
  intro a b hab
  rw [dRep_apply, dRep_apply]
  exact hd (Fin.le_def.mpr (Nat.div_le_div_right (Fin.le_def.mp hab)))

/-! ## Part 2: `t·Koz(n; d⃗) = Koz(n; d⃗^{(t)})` -/

variable {n : ℕ}

/-- **The dilate** (`cor-transfer`'s proof, first sentence):
`(k+1)·Koz(n; d⃗) = Koz(n; d⃗^{(k+1)})` as subsets of `ℝ^{N+1}`. -/
theorem smul_koz_eq (hn : 1 ≤ n) {r N : ℕ} (d : Fin (r + 1) → ℕ) (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) • ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n) =
      ∑ j, shiftIncl N (dRep k d j) '' convexHull ℝ (Sset n) := by
  have hpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
  rw [smul_sum, ← (blkEquiv k r).sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun i _ => ?_
  simp only [dRep_blk]
  have h := image_smul_setₛₗ (shiftIncl N (d i)) ((k + 1 : ℕ) : ℝ) (convexHull ℝ (Sset n))
  rw [RingHom.id_apply] at h
  rw [← h, hull_Sset_eq hn, smul_lymChain hpos, ← sum_lymChain hn, Set.image_finsetSum]

/-- The lattice points of the dilate `t·Koz(n; d⃗)`, in `ℤ^{N+1}`. -/
def dilKozLattice (n : ℕ) {r N : ℕ} (t : ℕ) (d : Fin r → ℕ) : Set (Fin (N + 1) → ℤ) :=
  {z | castR z ∈ (t : ℝ) • ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)}

theorem dilKozLattice_eq (hn : 1 ≤ n) {r N : ℕ} (d : Fin (r + 1) → ℕ) (k : ℕ) :
    dilKozLattice n (N := N) (k + 1) d = kozLattice n (N := N) (dRep k d) := by
  ext z
  simp only [dilKozLattice, kozLattice, Set.mem_ofPred_eq]
  rw [smul_koz_eq hn]

/-! ## Part 3: the gaps of `d⃗^{(t)}` and the display product -/

section Disp

variable {R : Type*} [Semiring R] {m : ℕ}

/-- The display product `M · A(g₀) · M · A(g₁) ⋯ M · A(g_{r−1}) · M`, with `r+1`
copies of `M`. With `M = T₀^{t−1}`, `A = T^L` it is the matrix of `cor-transfer`'s
second display. -/
def dispProd (M : Matrix (Fin m) (Fin m) R) (A : ℤ → Matrix (Fin m) (Fin m) R) :
    (r : ℕ) → (Fin r → ℤ) → Matrix (Fin m) (Fin m) R
  | 0, _ => M
  | r + 1, g => dispProd M A r (g ∘ Fin.castSucc) * A (g (Fin.last r)) * M

theorem dispProd_map {S : Type*} [Semiring S] (f : R →+* S) (M : Matrix (Fin m) (Fin m) R)
    (A : ℤ → Matrix (Fin m) (Fin m) R) (r : ℕ) (g : Fin r → ℤ) :
    (dispProd M A r g).map f = dispProd (M.map f) (fun δ => (A δ).map f) r g := by
  induction r with
  | zero => rfl
  | succ r ih => simp only [dispProd, Matrix.map_mul, ih]

end Disp

section Generic

variable {α : Type*} {m : ℕ} {X : Finset α} {σ : α → Fin m}
  {cond : ℤ → Fin m → α → Prop} [∀ δ k x, Decidable (cond δ k x)]

/-- Splitting an ordered transfer product. -/
theorem TprodG_add (a : ℕ) : ∀ (b : ℕ) (g : Fin (a + b) → ℤ),
    TprodG X σ cond (a + b) g =
      TprodG X σ cond a (fun i => g (Fin.castAdd b i)) *
        TprodG X σ cond b (fun j => g (Fin.natAdd a j))
  | 0, g => by simp [TprodG]
  | b + 1, g => by
    rw [show TprodG X σ cond (a + (b + 1)) g =
      TprodG X σ cond (a + b) (g ∘ Fin.castSucc) * TG X σ cond (g (Fin.last (a + b))) from rfl,
      TprodG_add a b, TprodG, mul_assoc]
    rfl

/-- A block `T(δ) · T(0)^k`: one gap `δ` followed by `k` zero gaps. -/
theorem TprodG_head (δ : ℤ) : ∀ (k : ℕ) (g : Fin (k + 1) → ℤ), g 0 = δ →
    (∀ j : Fin (k + 1), j ≠ 0 → g j = 0) →
    TprodG X σ cond (k + 1) g = TG X σ cond δ * TG X σ cond 0 ^ k
  | 0, g, h0, _ => by
    rw [TprodG, TprodG, one_mul, pow_zero, mul_one]
    rw [show Fin.last 0 = 0 from rfl, h0]
  | k + 1, g, h0, hj => by
    rw [TprodG, TprodG_head δ k (g ∘ Fin.castSucc) (by simpa using h0)
      (fun j hj' => hj _ (by simpa using hj')), hj _ (Fin.last_pos.ne'), pow_succ, mul_assoc]

end Generic

theorem div_eq_of_bounds {q k m : ℕ} (h1 : q * (k + 1) ≤ m) (h2 : m < q * (k + 1) + (k + 1)) :
    m / (k + 1) = q := by
  exact Nat.div_eq_of_lt_le h1 (by rw [add_mul, one_mul]; exact h2)

/-- The gaps of `d⃗^{(k+1)}` inside the first `r+1` blocks are those of
`(d₀, …, d_r)^{(k+1)}`. -/
theorem gaps_dRep_castAdd (k : ℕ) {r : ℕ} (d : Fin (r + 2) → ℕ) (i : Fin (rk k r)) :
    gaps (dRep k d) (Fin.castAdd (k + 1) i) = gaps (dRep k (d ∘ Fin.castSucc)) i := by
  simp only [gaps, dRep_apply, Function.comp_apply]
  rfl

/-- The gaps of `d⃗^{(k+1)}` in the last block: `δ = d_{r+1} − d_r` once, then `k` zeros. -/
theorem gaps_dRep_natAdd (k : ℕ) {r : ℕ} (d : Fin (r + 2) → ℕ) (j : Fin (k + 1)) :
    gaps (dRep k d) (Fin.natAdd (rk k r) j) = if j = 0 then gaps d (Fin.last r) else 0 := by
  have hr := rk_eq k r
  have hj := j.isLt
  simp only [gaps, dRep_apply]
  split_ifs with h0
  · subst h0
    have e1 : (rk k r + 0 + 1) / (k + 1) = r + 1 :=
      div_eq_of_bounds (by rw [hr, add_mul, one_mul]; omega) (by rw [hr, add_mul, one_mul]; omega)
    have e2 : (rk k r + 0) / (k + 1) = r :=
      div_eq_of_bounds (by rw [hr]; omega) (by rw [hr]; omega)
    congr 2 <;> congr 1 <;> exact Fin.ext (by simpa using by first | exact e1 | exact e2)
  · have hj1 : 1 ≤ j.val := by
      rcases Nat.eq_zero_or_pos j.val with h | h
      · exact absurd (Fin.ext h) h0
      · exact h
    have e1 : (rk k r + j.val + 1) / (k + 1) = r + 1 :=
      div_eq_of_bounds (by rw [hr, add_mul, one_mul]; omega) (by rw [hr, add_mul, one_mul]; omega)
    have e2 : (rk k r + j.val) / (k + 1) = r + 1 :=
      div_eq_of_bounds (by rw [hr, add_mul, one_mul]; omega) (by rw [hr, add_mul, one_mul]; omega)
    have : (⟨((Fin.natAdd (rk k r) j).succ : Fin _).val / (k + 1), div_lt_of_le_rk (Fin.isLt _)⟩ :
        Fin (r + 2)) = ⟨((Fin.natAdd (rk k r) j).castSucc : Fin _).val / (k + 1),
          div_lt_of_le_rk (Fin.isLt _)⟩ := Fin.ext (by simp [e1, e2])
    exact sub_eq_zero.mpr (congrArg (fun x => ((d x : ℕ) : ℤ)) this)

variable [NeZero n]

/-- **The gap computation**: the transfer product of `d⃗^{(k+1)}` is the display
product `T₀^k T(δ₁) T₀^k ⋯ T(δ_r) T₀^k`. -/
theorem TprodL_dRep (k : ℕ) : ∀ (r : ℕ) (d : Fin (r + 1) → ℕ),
    TprodL n (rk k r) (gaps (dRep k d)) = dispProd (TL n 0 ^ k) (TL n) r (gaps d)
  | 0, d => by
    have : gaps (dRep k d) = fun _ => 0 := by
      funext i
      simp only [gaps, dRep_apply]
      rw [show (⟨(i.succ : Fin (rk k 0 + 1)).val / (k + 1), div_lt_of_le_rk (Fin.isLt _)⟩ :
        Fin 1) = ⟨(i.castSucc : Fin (rk k 0 + 1)).val / (k + 1), div_lt_of_le_rk (Fin.isLt _)⟩
        from Subsingleton.elim _ _, sub_self]
    rw [this, TprodL, TprodG_const]
    rfl
  | r + 1, d => by
    show TprodG (latticeFinset n) (stL n) (condL n) (rk k r + (k + 1)) (gaps (dRep k d)) = _
    rw [TprodG_add, dispProd]
    rw [mul_assoc]
    congr 1
    · rw [← gaps_comp_castSucc, ← TprodL_dRep k r]
      congr 1
    · refine TprodG_head (gaps d (Fin.last r)) k (fun j => gaps (dRep k d) (Fin.natAdd (rk k r) j))
        ?_ ?_
      · show gaps (dRep k d) (Fin.natAdd (rk k r) 0) = _
        rw [gaps_dRep_natAdd]; simp
      · intro j hj
        show gaps (dRep k d) (Fin.natAdd (rk k r) j) = _
        rw [gaps_dRep_natAdd]; simp [hj]

/-! ## Part 4: the rank-`r` Ehrhart display -/

/-- **`cor-transfer`, second display** (the rank-`r` Ehrhart formula): for sorted `d⃗`
(rank `r+1`) and `t = k+1 ≥ 1`,
`L_{Koz(n;d⃗)}(t) = #(t·Koz(n;d⃗) ∩ ℤ^{N+1}) = u^L T₀^{t−1} T^L(δ₁) T₀^{t−1} ⋯ T^L(δ_r) T₀^{t−1} 𝟙`. -/
theorem ehrhart_display {r N : ℕ} (d : Fin (r + 1) → ℕ) (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) (k : ℕ) :
    (dilKozLattice n (N := N) (k + 1) d).ncard =
      uL n ᵥ* dispProd (TL n 0 ^ k) (TL n) r (gaps d) ⬝ᵥ (fun _ => 1) := by
  rw [dilKozLattice_eq one_le_of_neZero, ncard_kozLattice _ (dRep_monotone k hd)
    (fun j => by rw [dRep_apply]; exact hN _), TprodL_dRep]

/-! ## Part 5: polynomiality -/

/-- `T^L(δ)` over `ℚ`. -/
noncomputable def TQ (n : ℕ) [NeZero n] (δ : ℤ) : Matrix (Fin n) (Fin n) ℚ :=
  (Nat.castRingHom ℚ).mapMatrix (TL n δ)

theorem TQ_zero : TQ n 0 = T0Q n := rfl

theorem T0Q_lower : ∀ i j : Fin n, j < i → T0Q n i j = 0 := by
  intro i j h; simp [T0Q, RingHom.mapMatrix_apply, TL0_lower h]

theorem T0Q_diag : ∀ i : Fin n, T0Q n i i = 1 := by
  intro i; simp [T0Q, RingHom.mapMatrix_apply, TL0_diag]

/-- The polynomial matrix `M(t) = ∑_j C(t−1, j) 𝒩^j`, `𝒩 = T₀ − I`: `M(t) = T₀^{t−1}`
for `t ≥ 1` (`MQ_eval`). -/
noncomputable def MQ (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℚ[X] :=
  ∑ j ∈ range n, binomPoly j • (offDiag (T0Q n) ^ j).map C

theorem MQ_apply (a b : Fin n) :
    MQ n a b = ∑ j ∈ range n, binomPoly j * C ((offDiag (T0Q n) ^ j) a b) := by
  simp [MQ, Matrix.sum_apply]

theorem MQ_eval (k : ℕ) : (MQ n).map (eval ((k : ℚ) + 1)) = T0Q n ^ k := by
  ext a b
  rw [Matrix.map_apply, MQ_apply, eval_finsetSum,
    pow_eq_sum_choose T0Q_lower T0Q_diag k, Matrix.sum_apply]
  refine sum_congr rfl fun j _ => ?_
  rw [eval_mul, eval_C, binomPoly_eval, Matrix.smul_apply, smul_eq_mul]

/-- The rank-`r` Ehrhart polynomial, as the display with `T₀^{t−1}` replaced by `M(t)`. -/
noncomputable def ehrPolyR (n : ℕ) [NeZero n] (r : ℕ) (g : Fin r → ℤ) : ℚ[X] :=
  (fun i => C (uL n i : ℚ)) ⬝ᵥ
    (dispProd (MQ n) (fun δ => (TQ n δ).map C) r g *ᵥ fun _ => 1)

theorem cast_vecMul_dot {m : ℕ} (u : Fin m → ℕ) (D : Matrix (Fin m) (Fin m) ℕ) :
    ((u ᵥ* D ⬝ᵥ (fun _ => 1) : ℕ) : ℚ) =
      (fun i => (u i : ℚ)) ⬝ᵥ ((Nat.castRingHom ℚ).mapMatrix D *ᵥ fun _ => 1) := by
  rw [← Matrix.dotProduct_mulVec]
  simp [dotProduct, Matrix.mulVec, RingHom.mapMatrix_apply]

theorem ehrPolyR_eval (r : ℕ) (g : Fin r → ℤ) (k : ℕ) :
    (ehrPolyR n r g).eval ((k : ℚ) + 1) =
      ((uL n ᵥ* dispProd (TL n 0 ^ k) (TL n) r g ⬝ᵥ (fun _ => 1) : ℕ) : ℚ) := by
  rw [cast_vecMul_dot, RingHom.mapMatrix_apply, dispProd_map, Matrix.map_pow]
  have h := RingHom.map_dotProduct (evalRingHom ((k : ℚ) + 1)) (fun i => C (uL n i : ℚ))
    (dispProd (MQ n) (fun δ => (TQ n δ).map C) r g *ᵥ fun _ => 1)
  have h2 : ⇑(evalRingHom ((k : ℚ) + 1)) ∘
      (dispProd (MQ n) (fun δ => (TQ n δ).map C) r g *ᵥ fun _ => 1) =
      (dispProd (MQ n) (fun δ => (TQ n δ).map C) r g).map (evalRingHom ((k : ℚ) + 1)) *ᵥ
        (⇑(evalRingHom ((k : ℚ) + 1)) ∘ fun _ => 1) :=
    funext fun i => RingHom.map_mulVec _ _ _ i
  rw [h2, dispProd_map] at h
  rw [ehrPolyR, ← coe_evalRingHom, h]
  have hM : (MQ n).map (evalRingHom ((k : ℚ) + 1)) = T0Q n ^ k := MQ_eval k
  have hA : (fun δ => ((TQ n δ).map C).map (evalRingHom ((k : ℚ) + 1))) =
      fun δ => (TL n δ).map (Nat.castRingHom ℚ) := by
    funext δ; ext a b; simp [TQ, RingHom.mapMatrix_apply]
  rw [hM, hA]
  simp [T0Q, RingHom.mapMatrix_apply, Function.comp_def]

/-- **Polynomiality** (`cor-transfer`, with `obs-dilates`): for sorted `d⃗`, the lattice
count of `t·Koz(n; d⃗)` agrees for every `t ≥ 1` with the polynomial `ehrPolyR`. -/
theorem ehrhart_rankR {r N : ℕ} (d : Fin (r + 1) → ℕ) (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) (t : ℕ) (ht : 1 ≤ t) :
    (ehrPolyR n r (gaps d)).eval (t : ℚ) = (dilKozLattice n (N := N) t d).ncard := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  rw [Nat.cast_add, Nat.cast_one, ehrPolyR_eval, ehrhart_display d hd hN]

/-- Two polynomials over `ℚ` agreeing at every integer `t ≥ 1` are equal. -/
theorem poly_eq_of_eval_eq {P Q : ℚ[X]} (h : ∀ t : ℕ, 1 ≤ t → P.eval (t : ℚ) = Q.eval (t : ℚ)) :
    P = Q := by
  refine eq_of_infinite_eval_eq P Q ?_
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => ((k + 1 : ℕ) : ℚ)) ?_ ?_
  · intro a b hab; simpa using hab
  · intro k; exact h (k + 1) (by omega)

/-! ## Part 6: `P(0) = 1` -/

theorem descPochhammer_eval_neg_one (j : ℕ) :
    (descPochhammer ℚ j).eval (-1) = (-1) ^ j * (j.factorial : ℚ) := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [descPochhammer_succ_eval, ih, Nat.factorial_succ]
    push_cast; ring

theorem binomPoly_coeff_zero (j : ℕ) : (binomPoly j).coeff 0 = (-1) ^ j := by
  rw [coeff_zero_eq_eval_zero, binomPoly, eval_mul, eval_C, eval_comp, eval_sub, eval_X,
    eval_one, zero_sub, descPochhammer_eval_neg_one]
  have : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  field_simp

/-- `M(0)`: the constant terms of `M(t)`. -/
noncomputable def M0 (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℚ :=
  (MQ n).map fun p => p.coeff 0

/-- `M(t)`'s linear terms. -/
noncomputable def M1 (n : ℕ) [NeZero n] : Matrix (Fin n) (Fin n) ℚ :=
  (MQ n).map fun p => p.coeff 1

theorem offDiag_T0Q_lower : ∀ i j : Fin n, j ≤ i → offDiag (T0Q n) i j = 0 := by
  intro i j hji
  rcases eq_or_lt_of_le hji with h | h
  · simp [TransferEhrhart.offDiag, h]
  · simp [TransferEhrhart.offDiag, T0Q_lower i j h, (ne_of_lt h).symm]

theorem neg_pow_eq_smul {m : ℕ} (N : Matrix (Fin m) (Fin m) ℚ) (j : ℕ) :
    (-N) ^ j = ((-1 : ℚ) ^ j) • N ^ j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, ih, pow_succ, pow_succ, smul_mul_assoc, mul_neg, smul_neg,
      ← neg_smul, mul_neg_one]

theorem M0_eq : M0 n = ∑ j ∈ range n, (-offDiag (T0Q n)) ^ j := by
  ext a b
  simp only [M0, Matrix.map_apply, MQ_apply, finsetSum_coeff, coeff_mul_C,
    binomPoly_coeff_zero, Matrix.sum_apply, neg_pow_eq_smul, Matrix.smul_apply, smul_eq_mul]

/-- `T₀ · M(0) = I`: `M(0) = T₀^{−1}`, the polynomial `M(t) = T₀^{t−1}` at `t = 0`. -/
theorem T0Q_mul_M0 : T0Q n * M0 n = 1 := by
  have hT : T0Q n = 1 - -offDiag (T0Q n) := by
    rw [sub_neg_eq_add, one_add_offDiag T0Q_diag]
  rw [M0_eq]
  nth_rewrite 1 [hT]
  rw [mul_neg_geom_sum, neg_pow, pow_eq_zero_of_le offDiag_T0Q_lower le_rfl,
    mul_zero, sub_zero]

/-- `u^L` over `ℚ`. -/
noncomputable def uQ (n : ℕ) [NeZero n] : Fin n → ℚ := fun i => (uL n i : ℚ)

/-- Evaluation of `ehrPolyR` at an arbitrary point. -/
theorem ehrPolyR_eval_gen (r : ℕ) (g : Fin r → ℤ) (x : ℚ) :
    (ehrPolyR n r g).eval x =
      uQ n ⬝ᵥ (dispProd ((MQ n).map (eval x)) (TQ n) r g *ᵥ fun _ => 1) := by
  have h := RingHom.map_dotProduct (evalRingHom x) (fun i => C (uL n i : ℚ))
    (dispProd (MQ n) (fun δ => (TQ n δ).map C) r g *ᵥ fun _ => 1)
  have h2 : ⇑(evalRingHom x) ∘
      (dispProd (MQ n) (fun δ => (TQ n δ).map C) r g *ᵥ fun _ => 1) =
      (dispProd (MQ n) (fun δ => (TQ n δ).map C) r g).map (evalRingHom x) *ᵥ
        (⇑(evalRingHom x) ∘ fun _ => 1) :=
    funext fun i => RingHom.map_mulVec _ _ _ i
  rw [h2, dispProd_map] at h
  rw [ehrPolyR, ← coe_evalRingHom, h]
  have hA : (fun δ => ((TQ n δ).map C).map (evalRingHom x)) = TQ n := by
    funext δ; ext a b; simp
  rw [hA]
  simp [Function.comp_def]
  rfl

theorem MQ_map_eval_zero : (MQ n).map (eval 0) = M0 n := by
  ext a b; simp [M0, coeff_zero_eq_eval_zero]

/-- The row vector `e₀` selecting the state `τ = 1`. -/
noncomputable def e0 (n : ℕ) [NeZero n] : Fin n → ℚ := Pi.single ⟨0, NeZero.pos n⟩ 1

theorem e0_vecMul (M : Matrix (Fin n) (Fin n) ℚ) : e0 n ᵥ* M = M ⟨0, NeZero.pos n⟩ := by
  funext b
  simp [e0, vecMul, dotProduct, Pi.single_apply]

/-- **Row shift.** For `δ ≥ 0`, row `τ` of `T^L(δ)` is row `max(τ − δ, 1)` of `T₀`
(the transition `indeg(x) + δ > τ` only sees `τ − δ`, and `indeg ≥ 2` on `𝓛_n`). -/
theorem TL_row_shift (δ : ℤ) (hδ : 0 ≤ δ) (a b : Fin n) :
    TL n δ a b = TL n 0 ⟨a.val - δ.toNat, by omega⟩ b := by
  rw [TL_apply, TL_apply]
  congr 1
  refine Finset.filter_congr fun x hx => ?_
  rw [mem_latticeFinset one_le_of_neZero] at hx
  have := two_le_indeg one_le_of_neZero hx
  simp only [condL]
  constructor <;> rintro ⟨h1, h2⟩ <;> refine ⟨h1, ?_⟩ <;> omega

theorem TQ_row_shift (δ : ℤ) (hδ : 0 ≤ δ) (a b : Fin n) :
    TQ n δ a b = T0Q n ⟨a.val - δ.toNat, by omega⟩ b := by
  simp [TQ, T0Q, RingHom.mapMatrix_apply, TL_row_shift δ hδ a b]

theorem uQ_eq : uQ n = e0 n ᵥ* T0Q n := by
  rw [e0_vecMul]
  funext k
  simp [uQ, T0Q, RingHom.mapMatrix_apply, uL_eq_row]

theorem e0_vecMul_TQ (δ : ℤ) (hδ : 0 ≤ δ) : e0 n ᵥ* TQ n δ = e0 n ᵥ* T0Q n := by
  rw [e0_vecMul, e0_vecMul]
  funext b
  rw [TQ_row_shift δ hδ]
  congr 1
  exact Fin.ext (by simp)

theorem TQ_mulVec (δ : ℤ) (hδ : 0 ≤ δ) (w : Fin n → ℚ) (a : Fin n) :
    (TQ n δ *ᵥ w) a = (T0Q n *ᵥ w) ⟨a.val - δ.toNat, by omega⟩ := by
  simp only [Matrix.mulVec, dotProduct, TQ_row_shift δ hδ]

/-- `T(δ) · T₀^{−1} · 𝟙 = 𝟙` for `δ ≥ 0`. -/
theorem TQ_M0_one (δ : ℤ) (hδ : 0 ≤ δ) : TQ n δ *ᵥ (M0 n *ᵥ fun _ => 1) = fun _ => 1 := by
  funext a
  rw [TQ_mulVec δ hδ, Matrix.mulVec_mulVec, T0Q_mul_M0, Matrix.one_mulVec]

/-- `u^L · M(0) A(δ₁) M(0) ⋯ M(0) = e₀`, for non-negative gaps. -/
theorem uQ_dispProd_M0 : ∀ (r : ℕ) (g : Fin r → ℤ), (∀ i, 0 ≤ g i) →
    uQ n ᵥ* dispProd (M0 n) (TQ n) r g = e0 n
  | 0, _, _ => by
    rw [dispProd, uQ_eq, Matrix.vecMul_vecMul, T0Q_mul_M0, Matrix.vecMul_one]
  | r + 1, g, hg => by
    rw [dispProd, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
      uQ_dispProd_M0 r (g ∘ Fin.castSucc) (fun i => hg _), e0_vecMul_TQ _ (hg _), Matrix.vecMul_vecMul,
      T0Q_mul_M0, Matrix.vecMul_one]

/-- `P(0) = 1` for the explicit polynomial, every non-negative gap vector. -/
theorem ehrPolyR_eval_zero (r : ℕ) (g : Fin r → ℤ) (hg : ∀ i, 0 ≤ g i) :
    (ehrPolyR n r g).eval 0 = 1 := by
  rw [ehrPolyR_eval_gen, MQ_map_eval_zero, Matrix.dotProduct_mulVec, uQ_dispProd_M0 r g hg]
  simp [e0, dotProduct, Pi.single_apply]

theorem gaps_nonneg {r : ℕ} {d : Fin (r + 1) → ℕ} (hd : Monotone d) (i : Fin r) :
    0 ≤ gaps d i := by
  have := hd (Fin.castSucc_le_succ i)
  simp only [gaps]; omega

/-! ## Part 7: `P(0) = 1` and the linear coefficient, for *the* Ehrhart polynomial -/

/-- **`P(0) = 1`, rank `r`**: every polynomial agreeing with `L_{Koz(n;d⃗)}(t)` for `t ≥ 1`
takes the value `1` at `t = 0`. -/
theorem ehrhart_rankR_eval_zero {r N : ℕ} (d : Fin (r + 1) → ℕ) (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) (P : ℚ[X])
    (hP : ∀ t : ℕ, 1 ≤ t → P.eval (t : ℚ) = (dilKozLattice n (N := N) t d).ncard) :
    P.eval 0 = 1 := by
  have : P = ehrPolyR n r (gaps d) := poly_eq_of_eval_eq fun t ht => by
    rw [hP t ht, ehrhart_rankR d hd hN t ht]
  rw [this, ehrPolyR_eval_zero _ _ (gaps_nonneg hd)]

/-- The rank-one case of `ehrPolyR` is the Ehrhart polynomial of `Koz(n)` itself
(`TransferEhrhart.dilateLattice`, in `ℤ^{n+1}`). -/
theorem ehrPolyR_zero_eval (g : Fin 0 → ℤ) (t : ℕ) (ht : 1 ≤ t) :
    (ehrPolyR n 0 g).eval (t : ℚ) = (dilateLattice n t).ncard := by
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  rw [Nat.cast_add, Nat.cast_one, ehrPolyR_eval, ncard_dilateLattice]
  rfl

/-- **`P(0) = 1` for `ehrhart_koz`**: every polynomial agreeing with `L_{Koz(n)}(t)` for
`t ≥ 1` (in particular the `P` of `TransferEhrhart.ehrhart_koz`) has `P(0) = 1`. -/
theorem ehrhart_koz_eval_zero (P : ℚ[X])
    (hP : ∀ t : ℕ, 1 ≤ t → P.eval (t : ℚ) = (dilateLattice n t).ncard) : P.eval 0 = 1 := by
  have : P = ehrPolyR n 0 Fin.elim0 := poly_eq_of_eval_eq fun t ht => by
    rw [hP t ht, ehrPolyR_zero_eval _ t ht]
  rw [this, ehrPolyR_eval_zero _ _ (fun i => i.elim0)]

/-- `ehrhart_koz` with the constant term: degree `≤ n−1`, the leading coefficient, agreement
for `t ≥ 1`, and `P(0) = 1`. -/
theorem ehrhart_koz' (n : ℕ) [NeZero n] :
    ∃ P : ℚ[X], P.natDegree ≤ n - 1 ∧
      P.coeff (n - 1) = (∏ k ∈ Icc 2 n, (n.choose k : ℚ)) / ((n - 1).factorial : ℚ) ∧
      (∀ t : ℕ, 1 ≤ t → P.eval (t : ℚ) = (dilateLattice n t).ncard) ∧ P.eval 0 = 1 := by
  obtain ⟨P, h1, h2, h3⟩ := ehrhart_koz n
  exact ⟨P, h1, h2, h3, ehrhart_koz_eval_zero P h3⟩

/-! ### The linear coefficient (`prop-linear-coeff`) -/

theorem map_coeff_zero_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℚ[X]) :
    (A * B).map (fun p => p.coeff 0) = A.map (fun p => p.coeff 0) * B.map (fun p => p.coeff 0) := by
  ext i j
  simp [Matrix.mul_apply, finsetSum_coeff, coeff_mul]

theorem map_coeff_one_mul {m : ℕ} (A B : Matrix (Fin m) (Fin m) ℚ[X]) :
    (A * B).map (fun p => p.coeff 1) =
      A.map (fun p => p.coeff 0) * B.map (fun p => p.coeff 1) +
        A.map (fun p => p.coeff 1) * B.map (fun p => p.coeff 0) := by
  ext i j
  simp [Matrix.mul_apply, finsetSum_coeff, coeff_mul, Finset.Nat.antidiagonal_succ,
    Finset.sum_add_distrib]

/-- The polynomial display matrix `D_r(t)`. -/
noncomputable def Dpoly (n : ℕ) [NeZero n] (r : ℕ) (g : Fin r → ℤ) :
    Matrix (Fin n) (Fin n) ℚ[X] :=
  dispProd (MQ n) (fun δ => (TQ n δ).map C) r g

theorem Dpoly_coeff_zero (r : ℕ) (g : Fin r → ℤ) :
    (Dpoly n r g).map (fun p => p.coeff 0) = dispProd (M0 n) (TQ n) r g := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [Dpoly, dispProd] at ih ⊢
    rw [map_coeff_zero_mul, map_coeff_zero_mul, ih]
    congr 2
    ext a b; simp

theorem Dpoly_coeff_one_succ (r : ℕ) (g : Fin (r + 1) → ℤ) :
    (Dpoly n (r + 1) g).map (fun p => p.coeff 1) =
      dispProd (M0 n) (TQ n) r (g ∘ Fin.castSucc) * TQ n (g (Fin.last r)) * M1 n +
        (Dpoly n r (g ∘ Fin.castSucc)).map (fun p => p.coeff 1) * TQ n (g (Fin.last r)) * M0 n := by
  simp only [Dpoly, dispProd]
  rw [map_coeff_one_mul, map_coeff_zero_mul, map_coeff_one_mul]
  have h0 : ((TQ n (g (Fin.last r))).map C).map (fun p => p.coeff 0) = TQ n (g (Fin.last r)) := by
    ext a b; simp
  have h1 : ((TQ n (g (Fin.last r))).map C).map (fun p => p.coeff 1) = 0 := by
    ext a b; simp
  have h2 := Dpoly_coeff_zero (n := n) r (g ∘ Fin.castSucc)
  simp only [Dpoly] at h2
  rw [h0, h1, h2]
  simp [M0, M1]

theorem ehrPolyR_coeff_one (r : ℕ) (g : Fin r → ℤ) :
    (ehrPolyR n r g).coeff 1 = uQ n ⬝ᵥ ((Dpoly n r g).map (fun p => p.coeff 1) *ᵥ fun _ => 1) := by
  simp [ehrPolyR, dotProduct, Matrix.mulVec, finsetSum_coeff, uQ, Dpoly]

theorem uQ_Dpoly_coeff_one : ∀ (r : ℕ) (g : Fin r → ℤ), (∀ i, 0 ≤ g i) →
    uQ n ⬝ᵥ ((Dpoly n r g).map (fun p => p.coeff 1) *ᵥ fun _ => 1) =
      ((r : ℚ) + 1) * (uQ n ⬝ᵥ (M1 n *ᵥ fun _ => 1))
  | 0, _, _ => by simp [Dpoly, dispProd, M1]
  | r + 1, g, hg => by
    rw [Dpoly_coeff_one_succ, Matrix.add_mulVec, dotProduct_add]
    have hA : 0 ≤ g (Fin.last r) := hg _
    have e1 : uQ n ⬝ᵥ ((dispProd (M0 n) (TQ n) r (g ∘ Fin.castSucc) * TQ n (g (Fin.last r)) *
        M1 n) *ᵥ fun _ => 1) = uQ n ⬝ᵥ (M1 n *ᵥ fun _ => 1) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul,
        uQ_dispProd_M0 r (g ∘ Fin.castSucc) (fun i => hg _), e0_vecMul_TQ _ hA, ← uQ_eq,
        ← Matrix.dotProduct_mulVec]
    have e2 : uQ n ⬝ᵥ (((Dpoly n r (g ∘ Fin.castSucc)).map (fun p => p.coeff 1) *
        TQ n (g (Fin.last r)) * M0 n) *ᵥ fun _ => 1) =
        uQ n ⬝ᵥ ((Dpoly n r (g ∘ Fin.castSucc)).map (fun p => p.coeff 1) *ᵥ fun _ => 1) := by
      rw [Matrix.mul_assoc, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, TQ_M0_one _ hA]
    rw [e1, e2, uQ_Dpoly_coeff_one r (g ∘ Fin.castSucc) (fun i => hg _)]
    push_cast; ring

/-- **`prop-linear-coeff`**: `[t¹] L_{Koz(n;d⃗)}(t) = r · [t¹] L_{Koz(n)}(t)` for every
sorted `d⃗` of rank `r` (here `r+1`, `d : Fin (r+1) → ℕ`). Stated for *any* polynomials
`P`, `Q` agreeing with the two lattice counts for `t ≥ 1` — they are the Ehrhart
polynomials, by `ehrhart_rankR`, `ehrhart_koz` and uniqueness. -/
theorem prop_linear_coeff {r N : ℕ} (d : Fin (r + 1) → ℕ) (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) (P Q : ℚ[X])
    (hP : ∀ t : ℕ, 1 ≤ t → P.eval (t : ℚ) = (dilKozLattice n (N := N) t d).ncard)
    (hQ : ∀ t : ℕ, 1 ≤ t → Q.eval (t : ℚ) = (dilateLattice n t).ncard) :
    P.coeff 1 = ((r : ℚ) + 1) * Q.coeff 1 := by
  have hP' : P = ehrPolyR n r (gaps d) := poly_eq_of_eval_eq fun t ht => by
    rw [hP t ht, ehrhart_rankR d hd hN t ht]
  have hQ' : Q = ehrPolyR n 0 Fin.elim0 := poly_eq_of_eval_eq fun t ht => by
    rw [hQ t ht, ehrPolyR_zero_eval _ t ht]
  rw [hP', hQ', ehrPolyR_coeff_one, ehrPolyR_coeff_one, uQ_Dpoly_coeff_one r _ (gaps_nonneg hd),
    uQ_Dpoly_coeff_one 0 _ (fun i => i.elim0)]
  simp

/-! ### `t = 0`: the Ehrhart identity for every `t ∈ ℕ` -/

omit [NeZero n] in
/-- At `t = 0` the dilate is the single point `0`. -/
theorem dilKozLattice_zero {r N : ℕ} (d : Fin r → ℕ) :
    dilKozLattice n (N := N) 0 d = {0} := by
  have hne : (∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)).Nonempty := by
    exact ⟨∑ i, shiftIncl N (d i) (Sset_nonempty n).some, Set.finsetSum_mem_finsetSum _ _ _ fun i _ =>
        Set.mem_image_of_mem _ (subset_convexHull ℝ _ (Sset_nonempty n).some_mem)⟩
  ext z
  simp only [dilKozLattice, Set.mem_ofPred_eq, Nat.cast_zero, Set.zero_smul_set hne,
    Set.mem_zero, Set.mem_singleton_iff]
  constructor
  · intro h; funext j; have := congrFun h j; simpa using this
  · rintro rfl; funext j; simp

/-- **The rank-`r` Ehrhart polynomial, every `t ∈ ℕ`**: `ehrPolyR` agrees with
`#(t·Koz(n; d⃗) ∩ ℤ^{N+1})` for all `t ≥ 0`, `t = 0` included (`P(0) = 1 = #{0}`). -/
theorem ehrhart_rankR_all {r N : ℕ} (d : Fin (r + 1) → ℕ) (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) (t : ℕ) :
    (ehrPolyR n r (gaps d)).eval (t : ℚ) = (dilKozLattice n (N := N) t d).ncard := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [dilKozLattice_zero, Set.ncard_singleton, Nat.cast_zero, Nat.cast_one,
      ehrPolyR_eval_zero _ _ (gaps_nonneg hd)]
  · exact ehrhart_rankR d hd hN t ht

end EhrhartRankR

end ExteriorConvex
