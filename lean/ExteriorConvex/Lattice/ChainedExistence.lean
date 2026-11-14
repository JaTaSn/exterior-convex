/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Existence of chained decompositions, and lattice-point additivity

Formalisation of `article/exterior-convex_article3_draft_4.org`, §"Lattice points: the
canonical chained decomposition": `thm-chained` (1) existence, (2) uniqueness with the
water-filling formula, (3) integrality, for the **Kozlov vector** and **every sorted shift
vector** `d⃗`; then `cor-additivity` (as a set equality, plus the bijection with chained
tuples) and `cor-idp` for every `d⃗`. Complements `Lattice/LatticePoints.lean` (integer
uniqueness `chained_unique`, and the `d⃗ = 0` case).

**Normalisation.** As in `LatticePoints.lean`: degree-0-inclusive coordinates,
`Koz(n) = convexHull ℝ (Sset n)` (`= lymChain n` by `hull_Sset_eq`, `n ≥ 1`),
`Koz(n; d⃗) = ∑ᵢ shiftIncl N (dᵢ) '' Koz(n)` (`Spine/Sumset.lean`'s `main`), summands indexed
by `Fin r` (0-based), `d : Fin r → ℕ` with `Monotone d` (the paper's "sorted"), and the
ambient-size hypothesis `dᵢ + n ≤ N` for the paper's `N = n + d_r`.

* `ChainedR d p` is `def-chained-points` for real points: for adjacent `i, i+1`, wherever
  `p_i(m) > 0`, `p_{i+1}(m') = C(n,m')` for all `m' + d_{i+1} ≤ m + d_i`. For points of
  `Koz(n)` and sorted `d⃗` this is the paper's `tp(p_i) + d_i ≤ fl(p_{i+1}) + d_{i+1}` (the
  LYM ratios decrease, so "full at one degree" = "full at all lower ones").
  `ChainedR.full_of_lt`: it propagates to all pairs `i < j` (needs sortedness).
* **Existence** (`thm-chained`(1)): `exists_chained_lym` / `exists_chained`.
  The proof is the paper's (as rewritten 2026-10-21 to follow this file): a maximiser
  (`IsCompact.exists_isMaxOn`) of the single **linear** functional `F(p) = ∑ᵢ i · |shift^{dᵢ} pᵢ|₁`.
  The exchange moves the *same* raw mass `ε·M` (`M = ∑_{j∈block} C(n,j)`) out of summand `i`
  and into summand `i+1` (`shift_blk_transfer`), so it raises `F` by exactly `ε·M > 0`.
  `lower_mem` lowers the LYM ratios of summand `i` on `[s+δ, T]`, `T = tp(p_i)`; `raise_mem`
  raises summand `i+1` on `[s, T−δ]` by `η_m = ε C(n,m+δ)/C(n,m)`, where `μ_{s−1} > μ_s` is a
  strict drop in `[2, m']` (the paper takes `s = fl(p_{i+1}) + 1`; any strict drop works).
  Log-concavity enters only in `raise_mem`, through `choose_ratio_le`
  (`C(n,j+1+δ)/C(n,j+1) ≤ C(n,j+δ)/C(n,j)`, from `choose_succ_mul_le`, proved here from
  `Nat.choose_succ_right_eq`).
* **Uniqueness and formula** (`thm-chained`(2), no log-concavity): `chainedR_formula`,
  `p_i(m) = max(0, min(C(n,m), x_{m+d_i} − ∑_{l>i} c_{m+d_i−d_l}))`, with `capAt` the
  capacity `c_{k−d_l}` (zero outside `[0,n]`). `waterFill_eq_Q`: this is the paper's
  `Q_i − Q_{i−1}` (`Qwf`). `chainedR_unique`: real chained decompositions are unique.
* **Integrality** (`thm-chained`(3)): `chainedR_integral`, `pᵢ = castR (waterFill n d z i)`.
* **`cor-additivity`**: `cor_additivity`, `{z ∈ ℤ^{N+1} | z ∈ Koz(n; d⃗)} = ∑ᵢ shiftZ N dᵢ '' 𝓛_n`
  (`shiftZ` = integer `shift^{d}`); `existsUnique_chained_lattice` is the bijection with
  chained tuples of `𝓛_n`; `waterFill_spec` names the witness. The "in particular"
  `FF(n; d⃗) ⊆ …` is not restated.
* **`cor-idp`**, every sorted `d⃗`: `cor_idp`, via `d⃗^{(t)}` indexed by
  `Fin r × Fin t ≃ Fin (r·t)` (`finProdFinEquiv`), as in the paper.

**Scope.** Only the Kozlov vector `c = (C(n,0), …, C(n,n))`; the general full leg vector
with `(c₂,…,c_n)` log-concave is not formalised, though the proof is verbatim the same with
`choose_ratio_le` replaced by the log-concavity hypothesis (the binomial box is the only
other input). Numerically, the functional `F` above was checked (exact LP over ℚ, Sage/PPL)
to have chained maximisers for Koz(4; 0,1,3), Koz(5; 0,2,2,3), Koz(6; 0,1,4), and to fail
for the paper's `c = (1,2,1,3,1,3)`, `d⃗ = (0,1)` (40 of 60 random points), as it must.

Changelog (newest first): 2026-10-21 `cor_idp` no longer routes through `sum_lymChain`
(`t • shift(kᵢ)` is written directly as `t` copies of `shift(kᵢ)`, as in `ChainedGeneral`'s
`cor_idpC`) (Claude-Code agent, housekeeping); 2026-10-21 header updated after the paper's existence proof was
rewritten to match (coordinator); 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Lattice.LatticePoints

open Finset
open scoped Pointwise

namespace ExteriorConvex

namespace Lattice

variable {n : ℕ}

/-! ## Binomial log-concavity, in ratio form -/

/-- The ratios `C(n,k+1)/C(n,k)` decrease, written without division:
`C(n,a+1)·C(n,b) ≤ C(n,a)·C(n,b+1)` for `b ≤ a`. -/
theorem choose_succ_mul_le (n a b : ℕ) (hba : b ≤ a) :
    n.choose (a + 1) * n.choose b ≤ n.choose a * n.choose (b + 1) := by
  have h1 := Nat.choose_succ_right_eq n a
  have h2 := Nat.choose_succ_right_eq n b
  have key : n.choose (a + 1) * n.choose b * ((a + 1) * (b + 1)) ≤
      n.choose a * n.choose (b + 1) * ((a + 1) * (b + 1)) := by
    calc n.choose (a + 1) * n.choose b * ((a + 1) * (b + 1))
        = (n.choose (a + 1) * (a + 1)) * (n.choose b * (b + 1)) := by ring
      _ = n.choose a * (n - a) * (n.choose b * (b + 1)) := by rw [h1]
      _ = n.choose a * n.choose b * ((n - a) * (b + 1)) := by ring
      _ ≤ n.choose a * n.choose b * ((n - b) * (a + 1)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul (Nat.sub_le_sub_left hba n) (by omega)
      _ = n.choose a * (n.choose b * (n - b)) * (a + 1) := by ring
      _ = n.choose a * (n.choose (b + 1) * (b + 1)) * (a + 1) := by rw [h2]
      _ = n.choose a * n.choose (b + 1) * ((a + 1) * (b + 1)) := by ring
  exact Nat.le_of_mul_le_mul_right key (by positivity)

/-- The inside-block inequality `η_m ≥ η_{m+1}` of the proof of
`thm-chained`: `C(n,j+1+δ)/C(n,j+1) ≤ C(n,j+δ)/C(n,j)`. -/
theorem choose_ratio_le {j : ℕ} (δ : ℕ) (hj1 : j + 1 ≤ n) :
    (n.choose (j + 1 + δ) : ℝ) / n.choose (j + 1) ≤
      (n.choose (j + δ) : ℝ) / n.choose j := by
  have hC : ∀ k, k ≤ n → (0 : ℝ) < (n.choose k : ℝ) := fun k hk =>
    Nat.cast_pos.mpr (Nat.choose_pos hk)
  rw [div_le_div_iff₀ (hC _ hj1) (hC _ (by omega))]
  have := choose_succ_mul_le n (j + δ) j (by omega)
  rw [show j + δ + 1 = j + 1 + δ by omega] at this
  exact_mod_cast this

/-! ## The two block perturbations of the exchange step -/

/-- The block vector: `C(n, m+δ)` on the indices `s ≤ m ≤ t`, zero elsewhere.
With `δ = 0` it is the binomial profile of a block; with `δ` the gap it is
the profile by which the next summand is raised. -/
noncomputable def blk (n s t δ : ℕ) : Fin (n + 1) → ℝ := fun m =>
  if s ≤ m.val ∧ m.val ≤ t then (n.choose (m.val + δ) : ℝ) else 0

theorem blk_nonneg (n s t δ : ℕ) (m : Fin (n + 1)) : 0 ≤ blk n s t δ m := by
  unfold blk; split_ifs <;> positivity

theorem blk_of_lt {s t δ : ℕ} {m : Fin (n + 1)} (h : m.val < s) : blk n s t δ m = 0 := by
  unfold blk; split_ifs with h'
  · omega
  · rfl

/-- **Lowering a block.** If `x ∈ Koz(n)` has its last non-zero entry at
`T`, lowering the LYM ratios `μ_j` on `[s, T]` (`s ≥ 2`) by `ε ≤ μ_T`
stays in `Koz(n)`. -/
theorem lower_mem (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (hx : x ∈ lymChain n)
    {s T : ℕ} (hs : 2 ≤ s) (hT : T ≤ n)
    (hzero : ∀ j : Fin (n + 1), T < j.val → x j = 0) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε ≤ muOf n x T) : x - ε • blk n s T 0 ∈ lymChain n := by
  obtain ⟨hx0, hx1, hxc, hxn⟩ := hx
  have hC : ∀ k, k ≤ n → (0 : ℝ) < (n.choose k : ℝ) := fun k hk =>
    Nat.cast_pos.mpr (Nat.choose_pos hk)
  rw [muOf_of_le hT] at hε
  refine ⟨?_, ?_, fun j hj hjn => ?_, ?_⟩
  · rw [Pi.sub_apply, Pi.smul_apply, blk_of_lt (by simp; omega), smul_zero, sub_zero, hx0]
  · rw [fin_one_eq hn] at hx1 ⊢
    rw [Pi.sub_apply, Pi.smul_apply, blk_of_lt (by simp; omega), smul_zero, sub_zero, hx1]
  · have h := hxc j hj hjn
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, blk, add_zero]
    have hc1 := hC (j + 1) (by omega)
    have hc0 := hC j (by omega)
    by_cases h1 : s ≤ j + 1 ∧ j + 1 ≤ T <;> by_cases h2 : s ≤ j ∧ j ≤ T <;>
      simp only [h1, h2, and_self, ↓reduceIte, mul_zero, sub_zero]
    · rw [sub_div, sub_div, mul_div_assoc, mul_div_assoc, div_self hc1.ne',
        div_self hc0.ne']
      linarith
    · rw [sub_div, mul_div_assoc, div_self hc1.ne']
      linarith
    · have hjT : j = T := by omega
      subst hjT
      rw [hzero ⟨j + 1, by omega⟩ (by simp), zero_div, sub_div, mul_div_assoc,
        div_self hc0.ne']
      linarith
    · exact h
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, blk, Fin.val_last, add_zero]
    by_cases h : s ≤ n ∧ n ≤ T
    · simp only [h, and_self, ↓reduceIte]
      have hTn : T = n := by omega
      subst hTn
      rw [Nat.choose_self, Nat.cast_one, div_one] at hε
      rw [Nat.choose_self, Nat.cast_one, mul_one]
      have : x ⟨T, by omega⟩ = x (Fin.last T) := rfl
      linarith
    · simp only [h, ↓reduceIte, mul_zero, sub_zero]; exact hxn

/-- **Raising a block** (where log-concavity enters). If `y ∈ Koz(n)` has a
strict drop `μ_{s−1} > μ_s` (`s ≥ 2`), raising `μ_m` by
`η_m = ε·C(n,m+δ)/C(n,m)` on `[s, t]` stays in `Koz(n)` for `ε ≥ 0` small
enough that the left end keeps its drop; inside the block the chain needs
`η_m ≥ η_{m+1}`, which is `choose_ratio_le`. -/
theorem raise_mem (hn : 1 ≤ n) {y : Fin (n + 1) → ℝ} (hy : y ∈ lymChain n)
    {s t δ : ℕ} (hs : 2 ≤ s) (hsn : s ≤ n) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ε * ((n.choose (s + δ) : ℝ) / n.choose s) ≤
      muOf n y (s - 1) - muOf n y s) :
    y + ε • blk n s t δ ∈ lymChain n := by
  obtain ⟨hy0, hy1, hyc, hyn⟩ := hy
  have hC : ∀ k, k ≤ n → (0 : ℝ) < (n.choose k : ℝ) := fun k hk =>
    Nat.cast_pos.mpr (Nat.choose_pos hk)
  rw [muOf_of_le (by omega), muOf_of_le hsn] at hε
  refine ⟨?_, ?_, fun j hj hjn => ?_, ?_⟩
  · rw [Pi.add_apply, Pi.smul_apply, blk_of_lt (by simp; omega), smul_zero, add_zero, hy0]
  · rw [fin_one_eq hn] at hy1 ⊢
    rw [Pi.add_apply, Pi.smul_apply, blk_of_lt (by simp; omega), smul_zero, add_zero, hy1]
  · have h := hyc j hj hjn
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, blk]
    have hc1 := hC (j + 1) (by omega)
    have hc0 := hC j (by omega)
    by_cases h1 : s ≤ j + 1 ∧ j + 1 ≤ t <;> by_cases h2 : s ≤ j ∧ j ≤ t <;>
      simp only [h1, h2, and_self, ↓reduceIte, mul_zero, add_zero]
    · rw [add_div, add_div, mul_div_assoc, mul_div_assoc]
      have := mul_le_mul_of_nonneg_left (choose_ratio_le (n := n) (j := j) δ (by omega)) hε0
      linarith
    · have hjs : j + 1 = s := by omega
      subst hjs
      rw [add_div, mul_div_assoc]
      have e : ∀ (a b : Fin (n + 1)), a.val = b.val → y a = y b := fun a b h =>
        congrArg y (Fin.ext h)
      rw [e ⟨j + 1 - 1, by omega⟩ ⟨j, by omega⟩ (by simp)] at hε
      simp only [Nat.add_sub_cancel] at hε
      linarith
    · rw [add_div, mul_div_assoc]
      have := mul_nonneg hε0 (div_nonneg (Nat.cast_nonneg (n.choose (j + δ))) hc0.le)
      linarith
    · exact h
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact add_nonneg hyn (mul_nonneg hε0 (blk_nonneg _ _ _ _ _))

/-- **The transfer identity.** Lowering summand `i` on its own indices
`[s+δ, t+δ]` by `C(n,·)` and raising summand `i+1` on `[s, t]` by
`C(n, ·+δ)` move the same amount in every global degree, when
`d_{i+1} = d_i + δ`. -/
theorem shift_blk_transfer (N di δ s t : ℕ) (ht : t + δ ≤ n) :
    shiftIncl (n := n) N di (blk n (s + δ) (t + δ) 0) =
      shiftIncl N (di + δ) (blk n s t δ) := by
  funext k
  simp only [shiftIncl_apply, blk]
  by_cases h : s + δ + di ≤ k.val ∧ k.val ≤ t + δ + di
  · rw [dite_eq_left (by omega), dite_eq_left (by omega)]
    simp only [show s + δ ≤ k.val - di ∧ k.val - di ≤ t + δ by omega,
      show s ≤ k.val - (di + δ) ∧ k.val - (di + δ) ≤ t by omega, and_self, ↓reduceIte]
    rw [show k.val - di + 0 = k.val - (di + δ) + δ by omega]
  · have e1 : (if h' : di ≤ k.val ∧ k.val - di ≤ n then
        (if s + δ ≤ k.val - di ∧ k.val - di ≤ t + δ then
          (n.choose (k.val - di + 0) : ℝ) else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exfalso; omega
      · rfl
      · rfl
    have e2 : (if h' : di + δ ≤ k.val ∧ k.val - (di + δ) ≤ n then
        (if s ≤ k.val - (di + δ) ∧ k.val - (di + δ) ≤ t then
          (n.choose (k.val - (di + δ) + δ) : ℝ) else 0) else 0) = 0 := by
      split_ifs with h1 h2
      · exfalso; omega
      · rfl
      · rfl
    rw [e1, e2]

/-! ## Chained tuples of real points -/

/-- **`def-chained-points`**, for real points of `Koz(n)` (degree-0-inclusive
coordinates). The tuple `(p_i)` is chained for `d` if, for adjacent
`i, j = i+1`, wherever summand `i` is non-zero (`p_i(m) > 0`, global degree
`m + d_i`), summand `j` is full (`p_j(m') = C(n,m')`) in every global degree
`m' + d_j ≤ m + d_i`. For points of `Koz(n)` and sorted `d` this is the
paper's `tp(p_i) + d_i ≤ fl(p_j) + d_j`: the LYM ratios decrease, so being
full at the single own degree `tp(p_i) + d_i − d_j` (when it is `≥ 0`; when it
is `> n` the paper's inequality forbids it and so does this, as
`d_i + n ≤ d_j + n`) is the same as being full at every lower one. -/
def ChainedR {r : ℕ} (d : Fin r → ℕ) (p : Fin r → Fin (n + 1) → ℝ) : Prop :=
  ∀ ⦃i j : Fin r⦄, i.val + 1 = j.val → ∀ m m' : Fin (n + 1), 0 < p i m →
    m'.val + d j ≤ m.val + d i → p j m' = n.choose m'.val

/-- The binomial box on `Koz(n)`, every coordinate including `0`. -/
theorem box_lymChain (hn : 1 ≤ n) {x : Fin (n + 1) → ℝ} (hx : x ∈ lymChain n)
    (m : Fin (n + 1)) : 0 ≤ x m ∧ x m ≤ (n.choose m.val : ℝ) := by
  rcases Nat.eq_zero_or_pos m.val with h0 | hpos
  · have hm : m = 0 := Fin.ext h0
    subst hm
    rw [hx.1]; simp
  · have hx' : x ∈ lymChainAt n 1 := by rw [lymChainAt_one]; exact hx
    have := box_of_mem_lymChainAt hn hx' m hpos
    simpa using this

/-- Chaining propagates along the whole tuple (sorted `d`): wherever summand
`i` is non-zero, every later summand is full in that global degree. -/
theorem ChainedR.full_of_lt {r : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    {p : Fin r → Fin (n + 1) → ℝ} (hc : ChainedR d p) :
    ∀ ⦃i j : Fin r⦄, i < j → ∀ m m' : Fin (n + 1), 0 < p i m →
      m'.val + d j ≤ m.val + d i → p j m' = n.choose m'.val := by
  suffices H : ∀ g : ℕ, ∀ i j : Fin r, j.val = i.val + g + 1 →
      ∀ m m' : Fin (n + 1), 0 < p i m → m'.val + d j ≤ m.val + d i →
        p j m' = n.choose m'.val by
    intro i j hij m m' hm hle
    have := Fin.lt_def.mp hij
    exact H (j.val - i.val - 1) i j (by omega) m m' hm hle
  intro g
  induction g with
  | zero => intro i j hij m m' hm hle; exact hc (by omega) m m' hm hle
  | succ g ih =>
    intro i j hij m m' hm hle
    let l : Fin r := ⟨i.val + 1, by omega⟩
    have hlj : d l ≤ d j := hd (Fin.le_def.mpr (by simp only [l]; omega))
    let m₁ : Fin (n + 1) := ⟨m.val + d i - d l, by
      have := hd (Fin.le_def.mpr (by simp only [l]; omega) : i ≤ l); omega⟩
    have h1 : p l m₁ = n.choose m₁.val :=
      hc (i := i) (j := l) rfl m m₁ hm (by simp only [m₁]; omega)
    have hpos : 0 < p l m₁ := by
      rw [h1]; exact_mod_cast Nat.choose_pos (by omega)
    exact ih l j (by simp only [l]; omega) m₁ m' hpos (by simp only [m₁]; omega)

/-! ## Existence: a maximiser of the weighted mass is chained -/

theorem isCompact_lymChain (hn : 1 ≤ n) : IsCompact (lymChain n) := by
  rw [← hull_skel_eq hn]
  exact ((Set.finite_Icc 1 n).image _).isCompact_convexHull ℝ

/-- A strict drop somewhere: if `f a > f b` with `a ≤ b`, there is `s ∈ (a, b]`
with `f s < f (s−1)`. -/
theorem exists_drop (f : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) (h : f b < f a) :
    ∃ s, a < s ∧ s ≤ b ∧ f s < f (s - 1) := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd h (lt_irrefl _)
  | succ b hab ih =>
    by_cases hb : f b < f a
    · obtain ⟨s, h1, h2, h3⟩ := ih hb
      exact ⟨s, h1, by omega, h3⟩
    · exact ⟨b + 1, by omega, le_rfl, by simp only [Nat.add_sub_cancel]; linarith⟩

/-- **`thm-chained`(1), existence, for the Kozlov vector, in `lymChain` form.**
Every point of `∑ᵢ shift^{dᵢ}(Koz(n))` (sorted `d`, ambient `ℝ^{N+1}` large
enough, `dᵢ + n ≤ N`) is `∑ᵢ shift^{dᵢ}(pᵢ)` for a chained tuple of points
`pᵢ ∈ Koz(n)`.

Proof: the representations form a non-empty compact set; take a maximiser of
the weighted mass `F(p) = ∑ᵢ i · |shift^{dᵢ} pᵢ|₁`. If it were not chained at
`(i, i+1)`, the exchange of the paper's proof (lower summand `i` on the block
`[s+δ, T]`, raise summand `i+1` on `[s, T−δ]`) keeps the sum, stays in
`Koz(n)^r` (`lower_mem`, `raise_mem`), and moves mass `ε·M > 0` from summand
`i` to summand `i+1`, so `F` grows by `ε·M`. This replaces the paper's
lexicographic minimiser by one linear functional (see the file header). -/
theorem exists_chained_lym (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {x : Fin (N + 1) → ℝ}
    (hx : x ∈ ∑ i, shiftIncl N (d i) '' lymChain n) :
    ∃ p : Fin r → Fin (n + 1) → ℝ, (∀ i, p i ∈ lymChain n) ∧ ChainedR d p ∧
      ∑ i, shiftIncl N (d i) (p i) = x := by
  set R : Set (Fin r → Fin (n + 1) → ℝ) :=
    (Set.univ.pi fun _ => lymChain n) ∩
      (fun p => ∑ i, shiftIncl N (d i) (p i)) ⁻¹' {x} with hR
  have hl : ∀ i, Continuous (shiftIncl (n := n) N (d i)) := fun i =>
    LinearMap.continuous_of_finiteDimensional _
  have hcont : Continuous
      (fun p : Fin r → Fin (n + 1) → ℝ => ∑ i, shiftIncl N (d i) (p i)) :=
    continuous_finsetSum _ fun i _ => (hl i).comp (continuous_apply i)
  have hRc : IsCompact R :=
    (isCompact_univ_pi fun _ => isCompact_lymChain hn).inter_right
      (isClosed_singleton.preimage hcont)
  have hRne : R.Nonempty := by
    rw [Set.mem_fintype_sum] at hx
    obtain ⟨g, hg, hsum⟩ := hx
    choose p hp hpg using hg
    refine ⟨p, fun i _ => hp i, ?_⟩
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [← hsum]
    exact sum_congr rfl fun i _ => hpg i
  let F : (Fin r → Fin (n + 1) → ℝ) → ℝ := fun p =>
    ∑ i, (i.val : ℝ) * ∑ k, shiftIncl N (d i) (p i) k
  have hFc : Continuous F := by
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    refine continuous_finsetSum _ fun k _ => ?_
    exact (continuous_apply k).comp ((hl i).comp (continuous_apply i))
  obtain ⟨p, hpR, hmax⟩ := hRc.exists_isMaxOn hRne hFc.continuousOn
  have hpl : ∀ l, p l ∈ lymChain n := fun l => hpR.1 l (Set.mem_univ _)
  have hpsum : ∑ i, shiftIncl N (d i) (p i) = x := hpR.2
  refine ⟨p, hpl, ?_, hpsum⟩
  intro i j hij m m' hm hle
  by_contra hne
  have hij' : i < j := Fin.lt_def.mpr (by omega)
  have hijne : i ≠ j := hij'.ne
  have hdij : d i ≤ d j := hd hij'.le
  set δ := d j - d i with hδ
  have hdj : d j = d i + δ := by omega
  have hC : ∀ k, k ≤ n → (0 : ℝ) < (n.choose k : ℝ) := fun k hk =>
    Nat.cast_pos.mpr (Nat.choose_pos hk)
  -- summand `j` is not full at `m'`, and `m' ≥ 2`
  have hlt : p j m' < n.choose m'.val := lt_of_le_of_ne (box_lymChain hn (hpl j) m').2 hne
  have hm'2 : 2 ≤ m'.val := by
    by_contra h
    rcases (show m'.val = 0 ∨ m'.val = 1 by omega) with h0 | h1
    · have : m' = 0 := Fin.ext h0
      rw [this, (hpl j).1] at hlt
      simp at hlt
    · have : m' = 1 := by rw [fin_one_eq hn]; exact Fin.ext h1
      rw [this, (hpl j).2.1, fin_one_eq hn] at hlt
      simp at hlt
  -- a strict drop of `μ(p_j)` at some `s ∈ [2, m']`
  have hpj1 : p j ∈ lymChainAt n 1 := by rw [lymChainAt_one]; exact hpl j
  have hmu1 : muOf n (p j) 1 = 1 := muOf_one hn hpj1
  have hmum' : muOf n (p j) m'.val < 1 := by
    rw [muOf_of_le (by omega), div_lt_one (hC _ (by omega))]
    exact hlt
  obtain ⟨s, hs1, hsm, hdrop⟩ := exists_drop (muOf n (p j)) (show 1 ≤ m'.val by omega)
    (by rw [hmu1]; exact hmum')
  -- the top `T` of summand `i`
  set S := univ.filter fun k : Fin (n + 1) => 0 < p i k with hS
  have hSne : S.Nonempty := ⟨m, by simp [S, hm]⟩
  set T := S.max' hSne with hT
  have hTpos : 0 < p i T := (mem_filter.mp (S.max'_mem hSne)).2
  have hmT : m ≤ T := S.le_max' m (by simp [S, hm])
  have hzero : ∀ k : Fin (n + 1), T.val < k.val → p i k = 0 := by
    intro k hk
    refine le_antisymm (not_lt.mp fun h => ?_) (box_lymChain hn (hpl i) k).1
    have := S.le_max' k (by simp [S, h])
    exact absurd (Fin.le_def.mp this) (by omega)
  have hmT' := Fin.le_def.mp hmT
  have hsT : s + δ ≤ T.val := by omega
  set t := T.val - δ with ht
  have htT : t + δ = T.val := by omega
  have hTn : T.val ≤ n := T.is_le
  -- the step size
  set ρ : ℝ := (n.choose (s + δ) : ℝ) / n.choose s with hρ
  have hρpos : 0 < ρ := div_pos (hC _ (by omega)) (hC _ (by omega))
  have hmuT : 0 < muOf n (p i) T.val := by
    rw [muOf_of_le hTn]; exact div_pos hTpos (hC _ hTn)
  set ε : ℝ := min (muOf n (p i) T.val) ((muOf n (p j) (s - 1) - muOf n (p j) s) / ρ)
    with hε
  have hεpos : 0 < ε := lt_min hmuT (div_pos (by linarith) hρpos)
  -- the perturbed tuple
  set a := blk n (s + δ) T.val 0 with ha
  set b := blk n s t δ with hb
  let q : Fin r → Fin (n + 1) → ℝ := fun l =>
    if l = i then p i - ε • a else if l = j then p j + ε • b else p l
  have hqi : q i = p i - ε • a := by simp [q]
  have hqj : q j = p j + ε • b := by simp [q, hijne.symm]
  have hqmem : ∀ l, q l ∈ lymChain n := by
    intro l
    by_cases hli : l = i
    · subst hli; rw [hqi]
      exact lower_mem hn (hpl l) (by omega) hTn hzero hεpos.le (min_le_left _ _)
    · by_cases hlj : l = j
      · subst hlj; rw [hqj]
        refine raise_mem hn (hpl l) (by omega) (by omega) hεpos.le ?_
        have := min_le_right (muOf n (p i) T.val)
          ((muOf n (p l) (s - 1) - muOf n (p l) s) / ρ)
        exact (le_div_iff₀ hρpos).mp this
      · simp [q, hli, hlj, hpl l]
  -- the transfer: both moves are the same vector `A` in `ℝ^{N+1}`
  set A := shiftIncl N (d i) a with hA
  have hAB : shiftIncl N (d j) b = A := by
    rw [hA, ha, hb, hdj, ← htT]
    exact (shift_blk_transfer N (d i) δ s t (by omega)).symm
  have hqshift : ∀ l, shiftIncl N (d l) (q l) = shiftIncl N (d l) (p l) +
      ((if l = i then -(ε • A) else 0) + (if l = j then ε • A else 0)) := by
    intro l
    by_cases hli : l = i
    · subst hli
      rw [hqi, map_sub, map_smul]
      simp [hijne, hA, sub_eq_add_neg]
    · by_cases hlj : l = j
      · subst hlj
        rw [hqj, map_add, map_smul, hAB]
        simp [hli]
      · simp [q, hli, hlj]
  have hqsum : ∑ l, shiftIncl N (d l) (q l) = x := by
    simp only [hqshift, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte, hpsum]
    abel
  have hqR : q ∈ R := ⟨fun l _ => hqmem l, hqsum⟩
  -- the mass `M` moved is positive
  set M := ∑ k, A k with hM
  have hMpos : 0 < M := by
    have hk0 : T.val + d i < N + 1 := by have := hN i; omega
    have hval : A ⟨T.val + d i, hk0⟩ = n.choose T.val := by
      rw [hA, shiftIncl_apply, dite_eq_left (by simp; omega)]
      simp only [ha, blk, Nat.add_sub_cancel, add_zero]
      simp [hsT]
    have hnn : ∀ k, 0 ≤ A k := by
      intro k
      rw [hA, shiftIncl_apply]
      split_ifs
      · exact blk_nonneg _ _ _ _ _
      · exact le_rfl
    calc (0 : ℝ) < n.choose T.val := hC _ hTn
      _ = A ⟨T.val + d i, hk0⟩ := hval.symm
      _ ≤ M := single_le_sum (fun k _ => hnn k) (mem_univ _)
  -- `F` grows by `ε·M`
  have hFq : F q = F p + ε * M := by
    have : ∀ l : Fin r, (l.val : ℝ) * ∑ k, shiftIncl N (d l) (q l) k =
        (l.val : ℝ) * ∑ k, shiftIncl N (d l) (p l) k +
          ((if l = i then -((i.val : ℝ) * (ε * M)) else 0) +
            (if l = j then (j.val : ℝ) * (ε * M) else 0)) := by
      intro l
      rw [hqshift l]
      by_cases hli : l = i
      · subst hli
        simp [hijne, sum_add_distrib, ← mul_sum, hM, mul_add]
      · by_cases hlj : l = j
        · subst hlj
          simp [hli, sum_add_distrib, ← mul_sum, hM, mul_add]
        · simp [hli, hlj]
    simp only [F, this, sum_add_distrib, sum_ite_eq', mem_univ, ↓reduceIte]
    have hj : (j.val : ℝ) = i.val + 1 := by rw [← hij]; push_cast; ring
    rw [hj]; ring
  have := hmax hqR
  simp only [Set.mem_ofPred_eq] at this
  rw [hFq] at this
  nlinarith [mul_pos hεpos hMpos]

/-! ## The water-filling formula: uniqueness and integrality -/

/-- Entry `k` of a vector of `ℝ^{N+1}`, read as `0` beyond `N`. -/
def getR {N : ℕ} (x : Fin (N + 1) → ℝ) (k : ℕ) : ℝ :=
  if h : k ≤ N then x ⟨k, Nat.lt_succ_of_le h⟩ else 0

/-- Entry `k` of a vector of `ℤ^{N+1}`, read as `0` beyond `N`. -/
def getZ {N : ℕ} (x : Fin (N + 1) → ℤ) (k : ℕ) : ℤ :=
  if h : k ≤ N then x ⟨k, Nat.lt_succ_of_le h⟩ else 0

theorem getR_castR {N : ℕ} (x : Fin (N + 1) → ℤ) (k : ℕ) :
    getR (castR x) k = (getZ x k : ℝ) := by
  unfold getR getZ; split_ifs <;> simp

/-- The capacity `c_{k−d}` of a summand shifted by `d` in global degree `k`:
`C(n, k−d)` when `d ≤ k ≤ d+n`, else `0`. -/
def capAt (n dl k : ℕ) : ℤ := if dl ≤ k ∧ k - dl ≤ n then (n.choose (k - dl) : ℤ) else 0

/-- **The water-filling map** on integer vectors (`thm-chained`(2)):
`(p_i)_m = max(0, min(C(n,m), x_{m+d_i} − ∑_{l>i} c_{m+d_i−d_l}))`. This is the
paper's `Q_i(m+d_i) − Q_{i−1}(m+d_i)` (`waterFill_eq_Q`). -/
def waterFill (n : ℕ) {r N : ℕ} (d : Fin r → ℕ) (x : Fin (N + 1) → ℤ) (i : Fin r) :
    Fin (n + 1) → ℤ := fun m =>
  max 0 (min (n.choose m.val : ℤ)
    (getZ x (m.val + d i) - ∑ l ∈ univ.filter (fun l => i < l), capAt n (d l) (m.val + d i)))

/-- Splitting a sum over `Fin r` at `i`. -/
theorem sum_split_at {r : ℕ} (f : Fin r → ℝ) (i : Fin r) :
    ∑ l, f l = ∑ l ∈ univ.filter (fun l => l < i), f l + f i +
      ∑ l ∈ univ.filter (fun l => i < l), f l := by
  have h : ∀ l, f l = (if l < i then f l else 0) + (if i = l then f l else 0) +
      (if i < l then f l else 0) := by
    intro l
    rcases lt_trichotomy l i with h | h | h
    · simp [h, h.ne', not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne, not_lt.mpr h.le]
  conv_lhs => rw [sum_congr rfl fun l _ => h l]
  rw [sum_add_distrib, sum_add_distrib, sum_ite_eq, ite_eq_left_of_eq_true _ _ (eq_true (mem_univ _)), sum_filter,
    sum_filter]

/-- A shifted point of `Koz(n)`, read in global degree `k`, lies between `0`
and the capacity. -/
theorem shift_box (hn : 1 ≤ n) {N dl : ℕ} {y : Fin (n + 1) → ℝ} (hy : y ∈ lymChain n)
    (k : Fin (N + 1)) :
    0 ≤ shiftIncl N dl y k ∧ shiftIncl N dl y k ≤ (capAt n dl k.val : ℝ) := by
  rw [shiftIncl_apply, capAt]
  split_ifs
  · simpa using box_lymChain hn hy ⟨k.val - dl, _⟩
  · simp

/-- **`thm-chained`(2), the water-filling formula, for real points.** If the
tuple `(p_i)` of points of `Koz(n)` is chained for sorted `d`, every
coordinate of every part is determined by the sum `x = ∑ᵢ shift^{dᵢ}(pᵢ)`:
`p_i(m) = max(0, min(C(n,m), x_{m+d_i} − ∑_{l>i} c_{m+d_i−d_l}))`.
No log-concavity is used. -/
theorem chainedR_formula (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {p : Fin r → Fin (n + 1) → ℝ} (hp : ∀ i, p i ∈ lymChain n)
    (hc : ChainedR d p) (i : Fin r) (m : Fin (n + 1)) :
    p i m = max 0 (min (n.choose m.val : ℝ)
      (getR (∑ l, shiftIncl N (d l) (p l)) (m.val + d i) -
        ∑ l ∈ univ.filter (fun l => i < l), (capAt n (d l) (m.val + d i) : ℝ))) := by
  have hkN : m.val + d i ≤ N := by have := hN i; omega
  set kF : Fin (N + 1) := ⟨m.val + d i, Nat.lt_succ_of_le hkN⟩ with hkF
  set v : Fin r → ℝ := fun l => shiftIncl N (d l) (p l) kF with hv
  have hget : getR (∑ l, shiftIncl N (d l) (p l)) (m.val + d i) = ∑ l, v l := by
    rw [getR, dite_eq_left hkN, Finset.sum_apply]
  have hvi : v i = p i m := by
    simp only [hv, kF, shiftIncl_apply]
    rw [dite_eq_left (by omega)]
    congr 1; ext; simp
  have hbox : ∀ l, 0 ≤ v l ∧ v l ≤ (capAt n (d l) (m.val + d i) : ℝ) := fun l =>
    shift_box hn (hp l) kF
  have hfull : 0 < p i m → ∀ l, i < l → v l = (capAt n (d l) (m.val + d i) : ℝ) := by
    intro hpos l hil
    simp only [hv, kF, shiftIncl_apply, capAt]
    split_ifs with h1
    · rw [hc.full_of_lt hd hil m ⟨m.val + d i - d l, _⟩ hpos (by simp; omega)]
      simp
    · simp
  have hzero : ∀ l, l < i → 0 < v l → p i m = n.choose m.val := by
    intro l hli hvl
    simp only [hv, kF, shiftIncl_apply] at hvl
    split_ifs at hvl with h1
    · exact hc.full_of_lt hd hli ⟨m.val + d i - d l, _⟩ m hvl (by simp; omega)
    · exact absurd hvl (lt_irrefl 0)
  rw [hget, sum_split_at v i, hvi]
  set A := ∑ l ∈ univ.filter (fun l => l < i), v l with hA
  set B := ∑ l ∈ univ.filter (fun l => i < l), v l with hB
  set Tc := ∑ l ∈ univ.filter (fun l => i < l), (capAt n (d l) (m.val + d i) : ℝ) with hTc
  have hA0 : 0 ≤ A := sum_nonneg fun l _ => (hbox l).1
  have hB0 : 0 ≤ B := sum_nonneg fun l _ => (hbox l).1
  have hBT : B ≤ Tc := sum_le_sum fun l _ => (hbox l).2
  have hBfull : 0 < p i m → B = Tc := fun hpos =>
    sum_congr rfl fun l hl => hfull hpos l (mem_filter.mp hl).2
  have hAz : A = 0 ∨ p i m = n.choose m.val := by
    by_cases h : ∃ l, l < i ∧ 0 < v l
    · obtain ⟨l, hl, hvl⟩ := h
      exact Or.inr (hzero l hl hvl)
    · push Not at h
      left
      exact sum_eq_zero fun l hl => le_antisymm (h l (mem_filter.mp hl).2) (hbox l).1
  have hpbox := box_lymChain hn (hp i) m
  have hCpos : (0 : ℝ) < n.choose m.val := Nat.cast_pos.mpr (Nat.choose_pos m.is_le)
  rcases hpbox.1.lt_or_eq with hpos | hzero'
  · rw [hBfull hpos]
    rcases hAz with hA' | hA'
    · rw [hA', show (0 : ℝ) + p i m + Tc - Tc = p i m by ring, min_eq_right hpbox.2,
        max_eq_right hpos.le]
    · rw [hA', min_eq_left (by linarith), max_eq_right hCpos.le]
  · rcases hAz with hA' | hA'
    · rw [hA', ← hzero', min_eq_right (by linarith), max_eq_left (by linarith)]
    · exfalso; linarith

/-- **Uniqueness** (`thm-chained`(2), real points, every sorted `d`): two
chained tuples of points of `Koz(n)` with the same shifted sum are equal. -/
theorem chainedR_unique (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {p q : Fin r → Fin (n + 1) → ℝ}
    (hp : ∀ i, p i ∈ lymChain n) (hq : ∀ i, q i ∈ lymChain n)
    (hcp : ChainedR d p) (hcq : ChainedR d q)
    (h : ∑ i, shiftIncl N (d i) (p i) = ∑ i, shiftIncl N (d i) (q i)) : p = q := by
  funext i m
  rw [chainedR_formula hn hd hN hp hcp, chainedR_formula hn hd hN hq hcq, h]

/-- **`thm-chained`(3), integrality.** If the sum of a chained tuple of points of
`Koz(n)` is an integer vector `z`, every part is integral: `pᵢ` is the integer
water-filling slice `waterFill n d z i`. -/
theorem chainedR_integral (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {p : Fin r → Fin (n + 1) → ℝ} (hp : ∀ i, p i ∈ lymChain n)
    (hc : ChainedR d p) {z : Fin (N + 1) → ℤ}
    (hz : ∑ i, shiftIncl N (d i) (p i) = castR z) (i : Fin r) :
    p i = castR (waterFill n d z i) := by
  funext m
  rw [chainedR_formula hn hd hN hp hc, hz, getR_castR, castR_apply, waterFill]
  push_cast
  rfl

/-- The paper's clamps `Q_c(k) = max(0, x_k − ∑_{l>c} c_{k−d_l})` (paper, 1-based
`l`). Lean's summands are 0-based, so "`l > c`, 1-based" is "`c ≤ l`, 0-based", and
`Qwf c` *is* the paper's `Q_c`; `waterFill_eq_Q` is then the paper's
`(p_i)_m = Q_i(m+d_i) − Q_{i−1}(m+d_i)` at 1-based `i = i' + 1`. (The paper's
`Q_0 ≡ 0` is `Qwf 0 = max(0, x_k − total capacity)`, which vanishes on
`Koz(n; d⃗)`; it is not needed, since the identity holds for every `x`.) -/
def Qwf (n : ℕ) {r N : ℕ} (d : Fin r → ℕ) (x : Fin (N + 1) → ℤ) (c k : ℕ) : ℤ :=
  max 0 (getZ x k - ∑ l ∈ univ.filter (fun l : Fin r => c ≤ l.val), capAt n (d l) k)

theorem waterFill_eq_Q {r N : ℕ} (d : Fin r → ℕ) (x : Fin (N + 1) → ℤ) (i : Fin r)
    (m : Fin (n + 1)) :
    waterFill n d x i m = Qwf n d x (i.val + 1) (m.val + d i) - Qwf n d x i.val (m.val + d i) := by
  have hset : univ.filter (fun l : Fin r => i.val ≤ l.val) =
      insert i (univ.filter fun l : Fin r => i < l) := by
    ext l
    simp only [mem_filter, mem_univ, true_and, mem_insert, Fin.lt_def]
    constructor
    · intro h; rcases h.lt_or_eq with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h.symm)
    · rintro (rfl | h) <;> omega
  have hset' : univ.filter (fun l : Fin r => i.val + 1 ≤ l.val) =
      univ.filter fun l : Fin r => i < l := by
    ext l; simp only [mem_filter, mem_univ, true_and, Fin.lt_def]; omega
  have hcap : capAt n (d i) (m.val + d i) = n.choose m.val := by
    rw [capAt, ite_eq_left_of_eq_true _ _ (eq_true ⟨by omega, by omega⟩), Nat.add_sub_cancel]
  have hnot : i ∉ univ.filter fun l : Fin r => i < l := by simp
  simp only [waterFill, Qwf, hset, hset', sum_insert hnot, hcap]
  have h0 : (0 : ℤ) ≤ n.choose m.val := Nat.cast_nonneg _
  generalize (n.choose m.val : ℤ) = c at h0 ⊢
  generalize getZ x (m.val + d i) = y
  generalize ∑ l ∈ univ.filter (fun l : Fin r => i < l), capAt n (d l) (m.val + d i) = T
  omega

/-! ## Koz(n; d⃗) itself, and the lattice points -/

/-- **`thm-chained`(1), existence**, stated on `Koz(n; d⃗) = ∑ᵢ shift^{dᵢ}(conv S_n)`
exactly as `Spine/Sumset.lean`'s `main` writes it. -/
theorem exists_chained (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {x : Fin (N + 1) → ℝ}
    (hx : x ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)) :
    ∃ p : Fin r → Fin (n + 1) → ℝ, (∀ i, p i ∈ convexHull ℝ (Sset n)) ∧ ChainedR d p ∧
      ∑ i, shiftIncl N (d i) (p i) = x := by
  simp only [hull_Sset_eq hn] at hx ⊢
  exact exists_chained_lym hn hd hN hx

/-- The integer shift `ℤ^{n+1} → ℤ^{N+1}`, `shift^{d}` on lattice points. -/
def shiftZ (N dk : ℕ) (q : Fin (n + 1) → ℤ) : Fin (N + 1) → ℤ := fun j =>
  if h : dk ≤ j.val ∧ j.val - dk ≤ n then q ⟨j.val - dk, Nat.lt_succ_of_le h.2⟩ else 0

theorem castR_shiftZ (N dk : ℕ) (q : Fin (n + 1) → ℤ) :
    castR (shiftZ N dk q) = shiftIncl N dk (castR q) := by
  funext j
  simp only [castR_apply, shiftZ, shiftIncl_apply]
  split_ifs <;> simp

/-- **Existence and integrality for lattice points**: for an integer point `z`
of `Koz(n; d⃗)`, the water-filling slices are lattice points of `Koz(n)`, form a
chained tuple, and sum to `z`. -/
theorem waterFill_spec (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {z : Fin (N + 1) → ℤ}
    (hz : castR z ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)) :
    (∀ i, waterFill n d z i ∈ latticePts n) ∧
      ChainedR d (fun i => castR (waterFill n d z i)) ∧
      ∑ i, shiftZ N (d i) (waterFill n d z i) = z := by
  rw [hull_Sset_eq hn] at hz
  obtain ⟨p, hp, hc, hsum⟩ := exists_chained_lym hn hd hN hz
  have hpw : (fun i => castR (waterFill n d z i)) = p :=
    funext fun i => (chainedR_integral hn hd hN hp hc hsum i).symm
  refine ⟨fun i => ?_, by rw [hpw]; exact hc, ?_⟩
  · rw [mem_latticePts_iff hn]
    have := congrFun hpw i
    rw [this]; exact hp i
  · apply castR_injective
    rw [castR_sum, ← hsum]
    refine sum_congr rfl fun i _ => ?_
    rw [castR_shiftZ]
    exact congrArg _ (congrFun hpw i)

/-- **`cor-additivity`** (Kozlov vector, every sorted `d⃗`): the lattice points
of `Koz(n; d⃗)` are the Minkowski sum of the shifted lattice points of `Koz(n)`,
`Koz(n; d⃗) ∩ ℤ^{N+1} = ∑ᵢ shift^{dᵢ}(𝓛_n)`. -/
theorem cor_additivity (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) :
    {z : Fin (N + 1) → ℤ | castR z ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)} =
      ∑ i, shiftZ N (d i) '' latticePts n := by
  ext z
  rw [Set.mem_ofPred_eq]
  constructor
  · intro hz
    obtain ⟨hmem, -, hsum⟩ := waterFill_spec hn hd hN hz
    rw [Set.mem_fintype_sum]
    exact ⟨fun i => shiftZ N (d i) (waterFill n d z i), fun i => ⟨_, hmem i, rfl⟩, hsum⟩
  · rw [Set.mem_fintype_sum]
    rintro ⟨g, hg, rfl⟩
    choose q hq hqg using hg
    rw [castR_sum]
    refine Set.finsetSum_mem_finsetSum _ _ _ fun i _ => ?_
    rw [← hqg i, castR_shiftZ]
    exact Set.mem_image_of_mem _ (hq i)

/-- **`cor-additivity`, the bijection**: every lattice point of `Koz(n; d⃗)` is
the shifted sum of exactly one chained tuple of lattice points of `Koz(n)`
(namely the water-filling tuple). -/
theorem existsUnique_chained_lattice (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ}
    (hd : Monotone d) (hN : ∀ i, d i + n ≤ N) {z : Fin (N + 1) → ℤ}
    (hz : castR z ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)) :
    ∃! q : Fin r → Fin (n + 1) → ℤ, (∀ i, q i ∈ latticePts n) ∧
      ChainedR d (fun i => castR (q i)) ∧ ∑ i, shiftZ N (d i) (q i) = z := by
  refine ⟨waterFill n d z, waterFill_spec hn hd hN hz, ?_⟩
  rintro q ⟨hq, hcq, hsq⟩
  obtain ⟨hw, hcw, hsw⟩ := waterFill_spec hn hd hN hz
  have hmem : ∀ (q : Fin r → Fin (n + 1) → ℤ), (∀ i, q i ∈ latticePts n) →
      ∀ i, castR (q i) ∈ lymChain n := fun q hq i => (mem_latticePts_iff hn _).mp (hq i)
  have hs : ∀ (q : Fin r → Fin (n + 1) → ℤ),
      ∑ i, shiftIncl N (d i) (castR (q i)) = castR (∑ i, shiftZ N (d i) (q i)) := by
    intro q; rw [castR_sum]; exact sum_congr rfl fun i _ => (castR_shiftZ _ _ _).symm
  have := chainedR_unique hn hd hN (hmem q hq) (hmem _ hw) hcq hcw
    (by rw [hs, hs, hsq, hsw])
  funext i
  exact castR_injective (congrFun this i)

/-! ## Stretch: the integer decomposition property for every `d⃗` (`cor-idp`) -/

/-- **`cor-idp`** (Kozlov vector, every sorted `d⃗`): for `t ≥ 1`, an integer
point of the dilate `t·Koz(n; d⃗)` is a sum of `t` lattice points of
`Koz(n; d⃗)`, and conversely. The proof is the paper's: `t·Koz(n; d⃗)` is
`Koz(n; d⃗^{(t)})` with each `dᵢ` repeated `t` times (indexed by
`Fin r × Fin t ≃ Fin (r·t)`), `cor-additivity` there, and regrouping. -/
theorem cor_idp (hn : 1 ≤ n) {r N : ℕ} {d : Fin r → ℕ} (hd : Monotone d)
    (hN : ∀ i, d i + n ≤ N) {t : ℕ} (ht : 0 < t) (z : Fin (N + 1) → ℤ) :
    castR z ∈ (t : ℝ) • ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n) ↔
      ∃ y : Fin t → Fin (N + 1) → ℤ,
        (∀ s, castR (y s) ∈ ∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)) ∧
          ∑ s, y s = z := by
  have htR : (0 : ℝ) < t := Nat.cast_pos.mpr ht
  constructor
  · intro hz
    obtain ⟨w, hw, hwz⟩ := Set.mem_smul_set.mp hz
    rw [hull_Sset_eq hn, Set.mem_fintype_sum] at hw
    obtain ⟨g, hg, hgw⟩ := hw
    choose k hk hkg using hg
    -- the repeated shift vector; `t • shift(kᵢ)` is `t` copies of `shift(kᵢ)`
    let e : Fin r × Fin t ≃ Fin (r * t) := finProdFinEquiv
    let d' : Fin (r * t) → ℕ := fun j => d (e.symm j).1
    have hd'e : ∀ i s, d' (e (i, s)) = d i := by intro i s; simp [d']
    have hd' : Monotone d' := by
      intro a b hab
      apply hd
      simp only [e, finProdFinEquiv_symm_apply, Fin.le_def, Fin.coe_divNat]
      exact Nat.div_le_div_right (Fin.le_def.mp hab)
    have hN' : ∀ j, d' j + n ≤ N := fun j => hN _
    have hz' : castR z ∈ ∑ j, shiftIncl N (d' j) '' convexHull ℝ (Sset n) := by
      rw [hull_Sset_eq hn, Set.mem_fintype_sum]
      refine ⟨fun j => shiftIncl N (d' j) (k (e.symm j).1),
        fun j => Set.mem_image_of_mem _ (hk _), ?_⟩
      rw [← hwz, ← hgw, ← e.sum_comp, Fintype.sum_prod_type, smul_sum]
      refine sum_congr rfl fun i _ => ?_
      simp only [Equiv.symm_apply_apply, d']
      rw [sum_const, card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ, hkg i]
    obtain ⟨hq, -, hqs⟩ := waterFill_spec hn hd' hN' hz'
    set q := waterFill n d' z with hqdef
    refine ⟨fun s => ∑ i, shiftZ N (d i) (q (e (i, s))), fun s => ?_, ?_⟩
    · rw [castR_sum]
      refine Set.finsetSum_mem_finsetSum _ _ _ fun i _ => ?_
      rw [castR_shiftZ]
      exact Set.mem_image_of_mem _ (hq _)
    · rw [← hqs, ← e.sum_comp, Fintype.sum_prod_type, sum_comm]
      refine sum_congr rfl fun s _ => sum_congr rfl fun i _ => ?_
      rw [hd'e]
  · rintro ⟨y, hy, rfl⟩
    have hconv : Convex ℝ (∑ i, shiftIncl N (d i) '' convexHull ℝ (Sset n)) := by
      rw [← main n N d]; exact convex_convexHull ℝ _
    refine Set.mem_smul_set.mpr ⟨∑ s, (1 / (t : ℝ)) • castR (y s), ?_, ?_⟩
    · refine hconv.sum_mem (fun s _ => by positivity) ?_ (fun s _ => hy s)
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    · rw [smul_sum, castR_sum]
      refine sum_congr rfl fun s _ => ?_
      rw [smul_smul, mul_one_div_cancel htR.ne', one_smul]

end Lattice

end ExteriorConvex
