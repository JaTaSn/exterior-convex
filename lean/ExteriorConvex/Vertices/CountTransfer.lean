/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Part IV: the number of vertices as a transfer-matrix product (`cor-vertex-count`)

Part IV, Corollary `cor-vertex-count` (`article/exterior-convex_article4_draft_1.org`): for a positive
weakly log-concave leg vector `a⃗` and shifts `0 = d₁ ≤ ⋯ ≤ d_r` (`r ≥ 1`) with gaps
`δ_p = d_p − d_{p−1}`,

    #vertices of RA(a⃗; d⃗) = 𝟙ᵀ · E(a⃗; δ₂) ⋯ E(a⃗; δ_r) · 𝟙,

`E(a⃗; δ)` the rank-two extremal matrix of the shift vector `(0, δ)`.

| paper | here |
|---|---|
| "the pair `(i, j)` is admissible for shifts `(0, δ)`" (Theorem `thm-vdesc`'s (i)–(iii), `r = 2`) | `PairAdm`; `pairAdm_iff_CF` (it is `Pairwise.CF` for `shift2 δ`, `choice2 i j`) |
| `E(a⃗; δ)` | `Mext a n δ : Matrix (Fin n) (Fin n) ℕ` (row `i`, column `j` stand for the choices `i+1`, `j+1`) |
| `E(a⃗; δ)[i][j] = 1` iff `v_i + shift^δ v_j` is a vertex of `∠(a⃗) + shift^δ ∠(a⃗)` | `Mext_eq_one_iff` (uses `vertex_rank2_iff_CF`, positivity and weak log-concavity) |
| "`E(a⃗; 0)` is the identity" | `Mext_zero` (no hypotheses) |
| "`E(a⃗; δ)` is all ones for `δ ≥ n − 1`" | `Mext_all_ones` (no hypotheses) |
| proof, first sentence: `E^{(p−1,p)} = E(a⃗; δ_p)` (translation invariance) | `locked_translate`, `CF_iff_pairAdm` |
| the ordered product `E(δ₂) ⋯ E(δ_r)` | `transferProd a n d (r − 1)`; as a list product, `transferProd_eq_list_prod` |
| the path sum `∑_𝐣 ∏_p E(δ_p)[j_{p−1}][j_p] = 𝟙ᵀ ∏ E 𝟙` | `card_paths` (generic: any family of 0/1 matrices), via `sum_pathWt_last` |
| **`cor-vertex-count`** | **`cor_vertex_count`** |
| its last sentence, `Koz(n; d⃗)` | `cor_vertex_count_koz` (through `KozBridge.extremePoints_koz`, `eq:koz-as-ra`) |
| equally spaced shifts: `𝟙ᵀ E(a⃗; δ)^{r−1} 𝟙` | `transferProd_const`, `transferProd_id` |
| `ex-vertex-count` / `ex-rank3-vertices` | `ex_vertex_count_matrix` (the displayed `E(κ⃗(4); 1)`, entrywise), `ex_vertex_count_row_sums` (`E𝟙 = (4,3,2,2)`, `E²𝟙 = (11,8,5,4)`), `ex_vertex_count_rank_two` (11), `ex_vertex_count_rank_three` (28), `ex_vertex_count_koz_rank_three` (28, for `Koz(4; 0,1,2)` itself), and the brute-force cross-check `ex_rank3_vertices_direct` (28 by enumerating all 64 tuples, not through the matrix) |

Normalisation as in `RankTwoCorollary.lean`: the polytope is `∑_{p<r} conv(vsetA a N (d p) n)` in
`Fin N → ℝ` for any `N` with `d p + n ≤ N` (`p < r`); `a` positive everywhere; weak log-concavity
is `Pairwise.WLC`; shifts are any `Monotone d : ℕ → ℕ` (the paper's `d₁ = 0` is not needed: only
the gaps enter).  Indices: the paper's summands `p = 1, …, r` are `p = 0, …, r−1` here, so its
`δ_p = d_p − d_{p−1}` (`2 ≤ p ≤ r`) is `d (p+1) − d p` (`p + 1 < r`).

`r ≥ 1` is needed and is in the paper: for `r = 0` the polytope is the point `{0}` (one vertex)
while `𝟙ᵀ I 𝟙 = n`.

The numeric anchors are by kernel `decide` only (no `native_decide`), via `WorkedCounts.cf_cast_iff`
for natural-number leg vectors.

Changelog (newest first): 2026-11-17 created (Claude-Code agent, run `2026-11-17_lean-parts-4-5`)
-/
import Mathlib
import ExteriorConvex.Vertices.WorkedCounts
import ExteriorConvex.Facets.KozBridge

namespace ExteriorConvex
namespace CountTransfer

open Finset Matrix
open scoped Pointwise

/-! ## Rank-two admissibility depends only on the gap -/

/-- **Rank-two admissibility** of the choices `(i, j)` for two summands with shifts `(0, δ)`:
Theorem `thm-vdesc`'s conditions (i)–(iii) for the pair, written out (chosen points `i`, `δ + j`). -/
def PairAdm (a : ℕ → ℝ) (n δ i j : ℕ) : Prop :=
  (δ = 0 → i = j) ∧ i ≤ δ + j ∧ ¬ Pairwise.Locked a n 0 δ i (δ + j)

variable {a : ℕ → ℝ} {n : ℕ}

/-- `PairAdm` is `Pairwise.CF` for the rank-two system with shifts `(0, δ)`. -/
theorem pairAdm_iff_CF (δ i j : ℕ) :
    PairAdm a n δ i j ↔ Pairwise.CF a n (shift2 δ) (choice2 i j) 0 := by
  simp only [PairAdm, Pairwise.CF, shift2, choice2, zero_mul, one_mul, zero_add, one_ne_zero,
    ↓reduceIte]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun h => by rw [← h, zero_add]; exact h1 h.symm, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun h => by have := h1 h.symm; omega, h2, h3⟩

/-- **Translation invariance of locking**: shifting both summands by `dp` changes nothing. -/
theorem locked_translate (dp δ i j : ℕ) :
    Pairwise.Locked a n dp (dp + δ) (dp + i) (dp + δ + j) ↔
      Pairwise.Locked a n 0 δ i (δ + j) := by
  unfold Pairwise.Locked
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by omega, by omega, by omega, fun c hc => ?_⟩
    rw [Finset.mem_Ioc] at hc
    have := h4 (dp + c) (by rw [Finset.mem_Ioc]; omega)
    rw [show dp + c - dp = c by omega, show dp + δ + j - (dp + δ) = j by omega,
      show dp + δ + j - dp = δ + j by omega, show dp + c - (dp + δ) = c - δ by omega] at this
    rw [Nat.sub_zero, Nat.sub_zero, show δ + j - δ = j by omega]
    exact this
  · rintro ⟨h1, h2, h3, h4⟩
    refine ⟨by omega, by omega, by omega, fun c hc => ?_⟩
    rw [Finset.mem_Ioc] at hc
    obtain ⟨c', rfl⟩ : ∃ c', c = dp + c' := ⟨c - dp, by omega⟩
    have := h4 c' (by rw [Finset.mem_Ioc]; omega)
    rw [Nat.sub_zero, Nat.sub_zero, show δ + j - δ = j by omega] at this
    rw [show dp + c' - dp = c' by omega, show dp + δ + j - (dp + δ) = j by omega,
      show dp + δ + j - dp = δ + j by omega, show dp + c' - (dp + δ) = c' - δ by omega]
    exact this

/-- **The pair `(p, p+1)` of a rank-`r` system is the rank-two system with shifts
`(0, d (p+1) − d p)`** (the proof of `cor-vertex-count`, first sentence, in window-system form). -/
theorem CF_iff_pairAdm {d J : ℕ → ℕ} {p : ℕ} (hd : d p ≤ d (p + 1)) :
    Pairwise.CF a n d J p ↔ PairAdm a n (d (p + 1) - d p) (J p) (J (p + 1)) := by
  obtain ⟨δ, hδ⟩ : ∃ δ, d (p + 1) = d p + δ := ⟨d (p + 1) - d p, by omega⟩
  unfold Pairwise.CF PairAdm
  rw [hδ, show d p + δ - d p = δ by omega, locked_translate]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun h => by have := h1 (by omega); omega, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun h => by have := h1 (by omega); omega, by omega, h3⟩

/-! ## The rank-two extremal matrix -/

open Classical in
/-- **The rank-two extremal matrix `E(a⃗; δ)`** of the shift vector `(0, δ)`, as a `0/1` matrix
over `ℕ`: entry `(i, j)` (choices `i+1`, `j+1`) is `1` iff the pair is admissible. -/
noncomputable def Mext (a : ℕ → ℝ) (n δ : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j => if PairAdm a n δ (i.val + 1) (j.val + 1) then 1 else 0

open Classical in
lemma Mext_apply (δ : ℕ) (i j : Fin n) :
    Mext a n δ i j = if PairAdm a n δ (i.val + 1) (j.val + 1) then 1 else 0 := rfl

lemma Mext_eq_one_iff_pairAdm (δ : ℕ) (i j : Fin n) :
    Mext a n δ i j = 1 ↔ PairAdm a n δ (i.val + 1) (j.val + 1) := by
  classical
  rw [Mext_apply]
  split_ifs with h <;> simp [h]

/-- **`Mext` is the rank-two extremal matrix of the polytope**: entry `(i, j)` is `1` iff
`v_{i+1} + shift^δ v_{j+1}` is a vertex of `∠(a⃗) + shift^δ ∠(a⃗)` (for any ambient `N ≥ δ + n`). -/
theorem Mext_eq_one_iff {N : ℕ} (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {δ : ℕ}
    (hN : δ + n ≤ N) (i j : Fin n) :
    Mext a n δ i j = 1 ↔
      ravA a N 0 (i.val + 1) + ravA a N δ (j.val + 1) ∈
        Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N δ n)) := by
  rw [Mext_eq_one_iff_pairAdm, vertex_rank2_iff_CF hpos hlc hN ⟨by omega, by omega⟩
    ⟨by omega, by omega⟩, pairAdm_iff_CF]

/-- "`E(a⃗; 0)` is the identity matrix" (no hypotheses on `a⃗`). -/
theorem Mext_zero : Mext a n 0 = 1 := by
  classical
  ext i j
  rw [Mext_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst hij
    rw [ite_eq_left rfl, ite_eq_left]
    exact ⟨fun _ => rfl, by omega, fun h => by obtain ⟨h1, -⟩ := h; omega⟩
  · rw [ite_eq_right hij, ite_eq_right]
    rintro ⟨h1, -, -⟩
    exact hij (Fin.ext (by have := h1 rfl; omega))

/-- "`E(a⃗; δ)` is the all-ones matrix for `δ ≥ n − 1`" (no hypotheses on `a⃗`). -/
theorem Mext_all_ones {δ : ℕ} (hδ : n ≤ δ + 1) : Mext a n δ = Matrix.of fun _ _ => 1 := by
  classical
  ext i j
  rw [Mext_apply, Matrix.of_apply, ite_eq_left]
  have hi := i.isLt
  have hj := j.isLt
  refine ⟨fun h => by subst h; omega, by omega, ?_⟩
  rintro ⟨h1, h2, h3, -⟩
  omega

/-! ## Paths through a sequence of matrices -/

section Paths

variable {m : ℕ} (T : ℕ → Matrix (Fin m) (Fin m) ℕ)

/-- The ordered product `T 0 · T 1 ⋯ T (k−1)`. -/
def tprod : ℕ → Matrix (Fin m) (Fin m) ℕ
  | 0 => 1
  | k + 1 => tprod k * T k

/-- The weight of a path `K 0 → K 1 → ⋯ → K k`: the product of the entries it crosses. -/
def pathWt (k : ℕ) (K : Fin (k + 1) → Fin m) : ℕ :=
  ∏ p : Fin k, T p (K p.castSucc) (K p.succ)

lemma pathWt_snoc (k : ℕ) (K : Fin (k + 1) → Fin m) (x : Fin m) :
    pathWt T (k + 1) (Fin.snoc K x) = pathWt T k K * T k (K (Fin.last k)) x := by
  unfold pathWt
  rw [Fin.prod_univ_castSucc]
  congr 1
  · refine Finset.prod_congr rfl fun p _ => ?_
    have e : (p.castSucc.succ : Fin (k + 2)) = p.succ.castSucc := Fin.ext rfl
    simp only [Fin.val_castSucc, Fin.snoc_castSucc, e]
  · have e : ((Fin.last k).succ : Fin (k + 2)) = Fin.last (k + 1) := Fin.ext rfl
    simp only [Fin.val_last, Fin.snoc_castSucc, e, Fin.snoc_last]

lemma sum_snoc {k : ℕ} (f : (Fin (k + 1) → Fin m) → ℕ) :
    ∑ K : Fin (k + 1) → Fin m, f K = ∑ K : Fin k → Fin m, ∑ x : Fin m, f (Fin.snoc K x) := by
  rw [← (Fin.snocEquiv fun _ => Fin m).sum_comp, Fintype.sum_prod_type_right]
  rfl

/-- **Paths ending in a given state**: summing the weights of the paths of length `k` that end at
`s` gives the `s`-th entry of `𝟙ᵀ · T 0 ⋯ T (k−1)`. -/
theorem sum_pathWt_last (k : ℕ) (s : Fin m) :
    ∑ K : Fin (k + 1) → Fin m, (if K (Fin.last k) = s then pathWt T k K else 0) =
      ∑ i, tprod T k i s := by
  induction k generalizing s with
  | zero =>
    rw [sum_snoc]
    simp only [Fin.snoc_last]
    simp [pathWt, tprod, Matrix.one_apply]
  | succ k ih =>
    rw [sum_snoc]
    simp_rw [Fin.snoc_last, pathWt_snoc, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have h : ∀ K : Fin (k + 1) → Fin m, pathWt T k K * T k (K (Fin.last k)) s =
        ∑ t, (if K (Fin.last k) = t then pathWt T k K else 0) * T k t s := by
      intro K
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
    rw [Finset.sum_congr rfl fun K _ => h K, Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ih]
    simp only [tprod, Matrix.mul_apply, Finset.sum_mul]
    exact Finset.sum_comm

/-- **The generic transfer-matrix count**: the number of state sequences `K 0, …, K k` in which
every step `K p → K (p+1)` satisfies `R p`, is `𝟙ᵀ · T 0 ⋯ T (k−1) · 𝟙` for the `0/1` matrices
`T p` of the relations `R p`. -/
theorem card_paths (R : ℕ → Fin m → Fin m → Prop) [∀ p i j, Decidable (R p i j)] (k : ℕ) :
    #(univ.filter fun K : Fin (k + 1) → Fin m => ∀ p : Fin k, R p (K p.castSucc) (K p.succ)) =
      (fun _ => 1) ⬝ᵥ
        (tprod (fun p => Matrix.of fun i j => if R p i j then 1 else 0) k *ᵥ fun _ => 1) := by
  set T : ℕ → Matrix (Fin m) (Fin m) ℕ := fun p => Matrix.of fun i j => if R p i j then 1 else 0
  have hw : ∀ K : Fin (k + 1) → Fin m,
      pathWt T k K = if ∀ p : Fin k, R p (K p.castSucc) (K p.succ) then 1 else 0 := by
    intro K
    simp only [pathWt, T, Matrix.of_apply]
    rw [Fintype.prod_boole]
    congr 1
  rw [Finset.card_filter]
  simp_rw [← hw]
  have hsplit : ∀ K : Fin (k + 1) → Fin m,
      pathWt T k K = ∑ s, if K (Fin.last k) = s then pathWt T k K else 0 := by
    intro K
    rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
  rw [Finset.sum_congr rfl fun K _ => hsplit K, Finset.sum_comm]
  simp_rw [sum_pathWt_last]
  simp only [dotProduct, mulVec, one_mul, mul_one]
  exact Finset.sum_comm

end Paths

/-! ## The ordered product of the gap matrices -/

/-- **The ordered product `E(a⃗; d 1 − d 0) ⋯ E(a⃗; d k − d (k−1))`** of the first `k` gap
matrices (the identity for `k = 0`). -/
noncomputable def transferProd (a : ℕ → ℝ) (n : ℕ) (d : ℕ → ℕ) (k : ℕ) :
    Matrix (Fin n) (Fin n) ℕ :=
  tprod (fun p => Mext a n (d (p + 1) - d p)) k

lemma transferProd_zero (d : ℕ → ℕ) : transferProd a n d 0 = 1 := rfl

lemma transferProd_succ (d : ℕ → ℕ) (k : ℕ) :
    transferProd a n d (k + 1) = transferProd a n d k * Mext a n (d (k + 1) - d k) := rfl

/-- The same product as a `List.prod`. -/
theorem transferProd_eq_list_prod (d : ℕ → ℕ) (k : ℕ) :
    transferProd a n d k = ((List.range k).map fun p => Mext a n (d (p + 1) - d p)).prod := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [transferProd_succ, ih, List.range_succ, List.map_append, List.prod_append]
    simp

/-! ## Admissible tuples are paths -/

open Classical in
/-- The admissible tuples of length `k + 1` are in bijection with the paths of length `k` through
the gap relations. -/
theorem card_admissible {d : ℕ → ℕ} (hd : Monotone d) (k : ℕ) :
    (admissible a n d (k + 1)).card =
      #(univ.filter fun K : Fin (k + 1) → Fin n => ∀ p : Fin k,
        PairAdm a n (d (p.val + 1) - d p.val) ((K p.castSucc).val + 1) ((K p.succ).val + 1)) := by
  classical
  symm
  refine Finset.card_bij (fun K _ => fun p => (K p).val + 1) ?_ ?_ ?_
  · intro K hK
    rw [Finset.mem_filter] at hK
    rw [mem_admissible]
    have hext : ∀ p (hp : p < k + 1), extTuple (fun p => (K p).val + 1) p = (K ⟨p, hp⟩).val + 1 :=
      fun p hp => by simp [extTuple, hp]
    refine ⟨fun p hp => by rw [hext p hp]; have := (K ⟨p, hp⟩).isLt; omega, fun p hp => ?_⟩
    rw [CF_iff_pairAdm (hd (Nat.le_succ p)), hext p (by omega), hext (p + 1) hp]
    exact hK.2 ⟨p, by omega⟩
  · intro K _ K' _ h
    funext p
    exact Fin.ext (by have := congrFun h p; simpa using this)
  · intro J hJ
    rw [mem_admissible] at hJ
    have hb : ∀ p : Fin (k + 1), 1 ≤ J p ∧ J p ≤ n := fun p => by
      have := hJ.1 p.val p.isLt
      simpa [extTuple, p.isLt] using this
    refine ⟨fun p => ⟨J p - 1, by have := hb p; omega⟩, ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, fun p => ?_⟩
      have h := hJ.2 p.val (by omega)
      rw [CF_iff_pairAdm (hd (Nat.le_succ p.val))] at h
      have e1 : extTuple J p.val = J p.castSucc := by
        simp [extTuple, p.isLt.trans (Nat.lt_succ_self k)]; rfl
      have e2 : extTuple J (p.val + 1) = J p.succ := by
        simp [extTuple, show p.val + 1 < k + 1 by omega]; rfl
      rw [e1, e2] at h
      have h1 := hb p.castSucc
      have h2 := hb p.succ
      simp only
      rw [show J p.castSucc - 1 + 1 = J p.castSucc by omega,
        show J p.succ - 1 + 1 = J p.succ by omega]
      exact h
    · funext p
      simp only
      have := hb p
      omega

/-! ## `cor-vertex-count` -/

variable {N : ℕ}

/-- **`cor-vertex-count`** (Part IV): for a positive weakly log-concave leg vector and monotone
shifts, `r ≥ 1`, the number of vertices of `RA(a⃗; d⃗) = ∑_{p<r} shift^{d p} ∠(a⃗)` is
`𝟙ᵀ · E(a⃗; d 1 − d 0) ⋯ E(a⃗; d (r−1) − d (r−2)) · 𝟙`. -/
theorem cor_vertex_count (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {r : ℕ} (hr : 1 ≤ r)
    {d : ℕ → ℕ} (hd : Monotone d) (hN : ∀ p < r, d p + n ≤ N) :
    (Set.extremePoints ℝ (∑ p ∈ range r, convexHull ℝ (vsetA a N (d p) n))).ncard =
      (fun _ => 1) ⬝ᵥ (transferProd a n d (r - 1) *ᵥ fun _ => 1) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  rw [ncard_extremePoints hpos hlc hd hN, card_admissible hd k,
    card_paths (fun p i j => PairAdm a n (d (p + 1) - d p) (i.val + 1) (j.val + 1)) k,
    Nat.add_sub_cancel]
  rfl

/-- **`cor-vertex-count`, last sentence**: for `a⃗ = κ⃗(n)` the same product counts the vertices of
`Koz(n; d⃗)` itself (`eq:koz-as-ra`, through `KozBridge.extremePoints_koz`). -/
theorem cor_vertex_count_koz (hn : 1 ≤ n) {r : ℕ} (hr : 1 ≤ r) {d : ℕ → ℕ} (hd : Monotone d)
    (hN : ∀ p < r, d p + n ≤ N) :
    (Set.extremePoints ℝ (convexHull ℝ (ffSet n N (fun i : Fin r => d i)))).ncard =
      (fun _ => 1) ⬝ᵥ (transferProd (kozLeg n) n d (r - 1) *ᵥ fun _ => 1) := by
  rw [KozBridge.extremePoints_koz hn d hN,
    Set.ncard_image_of_injective _ (KozBridge.kozMap_injective d)]
  exact cor_vertex_count (kozLeg_pos n) (kozLeg_slc n).wlc hr hd hN

/-- With a constant gap the product is a power: `𝟙ᵀ E(a⃗; δ)^{r−1} 𝟙`. -/
theorem transferProd_const (δ : ℕ) (k : ℕ) :
    transferProd a n (fun p => p * δ) k = Mext a n δ ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [transferProd_succ, ih, pow_succ]
    congr 2
    rw [Nat.add_mul, one_mul, Nat.add_sub_cancel_left]

/-- Equally spaced shifts `0, 1, 2, …` give the powers of `E(a⃗; 1)`. -/
theorem transferProd_id (k : ℕ) : transferProd a n (fun p => p) k = Mext a n 1 ^ k := by
  have := transferProd_const (a := a) (n := n) 1 k
  simpa using this

/-! ## Numeric anchors: `ex-vertex-count` and `ex-rank3-vertices` (kernel `decide`) -/

section Anchors

open WorkedCounts

/-- `E(a⃗; δ)` for a natural-number leg vector, decidably (Theorem 2's conditions read in `ℕ`). -/
def MextN (a : ℕ → ℕ) (n δ : ℕ) : Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j => if CFN a n (shift2 δ) (choice2 (i.val + 1) (j.val + 1)) 0 then 1 else 0

/-- **The decidable form is faithful.** -/
theorem Mext_cast (a : ℕ → ℕ) (n δ : ℕ) : Mext (fun s => (a s : ℝ)) n δ = MextN a n δ := by
  classical
  ext i j
  rw [Mext_apply, MextN, Matrix.of_apply, pairAdm_iff_CF, cf_cast_iff]
  congr 1

/-- The Kozlov leg vector `κ⃗(4) = (4, 6, 4, 1)` is weakly log-concave. -/
theorem kozlov4_wlc : Pairwise.WLC (kozLeg 4) 4 := (kozLeg_slc 4).wlc

/-- **`ex-vertex-count`, the displayed matrix**: `E(κ⃗(4); 1)`, entry by entry. -/
theorem ex_vertex_count_matrix :
    Mext (kozLeg 4) 4 1 = !![1, 1, 1, 1; 1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 1] := by
  rw [kozLeg_eq, Mext_cast]
  decide

/-- **`ex-vertex-count`, the displayed vectors**: `E𝟙 = (4, 3, 2, 2)`, `E²𝟙 = (11, 8, 5, 4)`. -/
theorem ex_vertex_count_row_sums :
    Mext (kozLeg 4) 4 1 *ᵥ (fun _ => 1) = ![4, 3, 2, 2] ∧
      Mext (kozLeg 4) 4 1 ^ 2 *ᵥ (fun _ => 1) = ![11, 8, 5, 4] := by
  rw [ex_vertex_count_matrix]
  decide

/-- **`ex-vertex-count`: `RA(κ⃗(4); 0, 1)` has `11` vertices**, read off the transfer matrix (any
ambient `N ≥ 5`). -/
theorem ex_vertex_count_rank_two {N : ℕ} (hN : 5 ≤ N) :
    (Set.extremePoints ℝ
        (∑ p ∈ range 2, convexHull ℝ (vsetA (kozLeg 4) N p 4))).ncard = 11 := by
  rw [cor_vertex_count (kozLeg_pos 4) kozlov4_wlc (by norm_num) (fun _ _ h => h)
    (fun p hp => by omega), transferProd_id, ex_vertex_count_matrix]
  decide

/-- **`ex-vertex-count` / `ex-rank3-vertices`: `RA(κ⃗(4); 0, 1, 2)` has `28` vertices**, read off
the transfer matrix (any ambient `N ≥ 6`). -/
theorem ex_vertex_count_rank_three {N : ℕ} (hN : 6 ≤ N) :
    (Set.extremePoints ℝ
        (∑ p ∈ range 3, convexHull ℝ (vsetA (kozLeg 4) N p 4))).ncard = 28 := by
  rw [cor_vertex_count (kozLeg_pos 4) kozlov4_wlc (by norm_num) (fun _ _ h => h)
    (fun p hp => by omega), transferProd_id, ex_vertex_count_matrix]
  decide

/-- **`ex-rank3-vertices`, the same `28` by brute force**: enumerating all `4³ = 64` tuples
against Theorem 2's conditions (`ncard_extremePoints_nat`), independently of the transfer matrix. -/
theorem ex_rank3_vertices_direct {N : ℕ} (hN : 6 ≤ N) :
    (Set.extremePoints ℝ
        (∑ p ∈ range 3, convexHull ℝ (vsetA (kozLeg 4) N p 4))).ncard = 28 := by
  rw [kozLeg_eq, ncard_extremePoints_nat (kozNat_pos 4) (kozLeg_eq 4 ▸ kozlov4_wlc)
    (fun _ _ h => h) (fun p hp => by omega)]
  decide

/-- **`ex-vertex-count`, for `Koz(4; 0, 1, 2)` itself**: `28` vertices (`eq:koz-as-ra`). -/
theorem ex_vertex_count_koz_rank_three :
    (Set.extremePoints ℝ (convexHull ℝ (ffSet 4 6 (fun i : Fin 3 => (i : ℕ))))).ncard = 28 := by
  rw [cor_vertex_count_koz (d := fun p => p) (by norm_num) (by norm_num) (fun _ _ h => h)
    (fun p hp => by omega), transferProd_id, ex_vertex_count_matrix]
  decide

end Anchors

end CountTransfer

end ExteriorConvex
