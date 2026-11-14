/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Module Kruskal–Katona: the greedy split (Proposition 4, `prop-greedy`)

Formalisation of Proposition 4 of
`working-notes/module-kruskal-katona-greedy-proof-2026-10-20.org` (article 3: `prop-greedy`),
built on Proposition 3 (`prop-PQ`: `sig_P`, `sig_Q` in `ModuleKK/GreedyPQ.lean`).

* `greedy C ks T` is the greedy vector `t*`: `t*₁ = min(T, C₁)`, `t*₂ = min(T − t*₁, C₂)`, ….
  Vectors are `List ℕ`, degree vectors `List ι`, a list `ks` with `ks.Pairwise (· ≥ ·)` being the
  note's `k₁ ≥ ⋯ ≥ k_r`.
* `greedy_le_of_exchange` is the abstract statement: for any capacities `C`, costs `c` and a
  relation `rel` (for us `≥` on degrees) satisfying the two-component *block exchange* inequality
  `Exchange` (= P and Q together), the greedy vector has the smallest total cost among all
  feasible vectors with the same sum. The proof is not the note's "lexicographically largest
  minimiser" descent but the equivalent direct induction on `r`: absorb the tail into the first
  component block by block (`absorb`, one application of P or Q per component), then recurse.
* `capZ n k`, `costZ n k` are the note's `Cᵢ = C(n,kᵢ)` and `cᵢ = σₙ(kᵢ,·)` for an *integer*
  degree `k` (`0` when `k < 0`; for `k > n` both are automatically `0`, as `sig n k 0 = 0`).
  `exchange_sig` derives the exchange inequality from `sig_P`, `sig_Q`.
* `prop_greedy` is Proposition 4 as stated in the note: integer degrees of any sign,
  `k₁ ≥ ⋯ ≥ k_r`, any `0 ≤ tᵢ ≤ Cᵢ` with `∑ tᵢ = T`: `∑ cᵢ(t*ᵢ) ≤ ∑ cᵢ(tᵢ)`.
  `greedy_feasible` and `greedy_sum` say that `t*` is itself admissible (`t*ᵢ ≤ Cᵢ`, and
  `∑ t*ᵢ = T` whenever `T ≤ ∑ Cᵢ`).

Here `σₙ` is the recursively defined `sig` of `GreedyPQ.lean`; that it *is* the lex upper-shadow
size is proved in `ModuleKK/LexShadow.lean`.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.ModuleKK.GreedyPQ

namespace ExteriorConvex
namespace ModuleKK

section Abstract

variable {ι : Type*}

/-- The greedy vector: fill the components in order, each to capacity `C k` or until `T` runs out. -/
def greedy (C : ι → ℕ) : List ι → ℕ → List ℕ
  | [], _ => []
  | k :: ks, T => min T (C k) :: greedy C ks (T - min T (C k))

/-- Total cost `∑ᵢ c kᵢ tᵢ` of a vector `ts` for the degree list `ks`. -/
def cost (c : ι → ℕ → ℕ) (ks : List ι) (ts : List ℕ) : ℕ := (List.zipWith c ks ts).sum

/-- Feasibility: same length as `ks` and `tᵢ ≤ C kᵢ`. -/
def Feasible (C : ι → ℕ) (ks : List ι) (ts : List ℕ) : Prop :=
  List.Forall₂ (fun k t => t ≤ C k) ks ts

/-- The two-component block-exchange inequality (Proposition 3, P and Q together): for
`rel k' k` (degree of the second component ≤ degree of the first), moving as much as possible
from the second component into the first does not increase the cost. -/
def Exchange (rel : ι → ι → Prop) (C : ι → ℕ) (c : ι → ℕ → ℕ) : Prop :=
  ∀ k k' x y, rel k' k → x ≤ C k → y ≤ C k' →
    c k (min (x + y) (C k)) + c k' (x + y - min (x + y) (C k)) ≤ c k x + c k' y

@[simp] lemma cost_nil (c : ι → ℕ → ℕ) (ts : List ℕ) : cost c [] ts = 0 := by simp [cost]

@[simp] lemma cost_cons (c : ι → ℕ → ℕ) (k : ι) (ks : List ι) (t : ℕ) (ts : List ℕ) :
    cost c (k :: ks) (t :: ts) = c k t + cost c ks ts := by simp [cost]

lemma greedy_feasible (C : ι → ℕ) (ks : List ι) (T : ℕ) : Feasible C ks (greedy C ks T) := by
  induction ks generalizing T with
  | nil => exact List.Forall₂.nil
  | cons k ks ih => exact List.Forall₂.cons (min_le_right _ _) (ih _)

lemma greedy_sum (C : ι → ℕ) (ks : List ι) (T : ℕ) :
    (greedy C ks T).sum = min T (ks.map C).sum := by
  induction ks generalizing T with
  | nil => simp [greedy]
  | cons k ks ih =>
    simp only [greedy, List.sum_cons, ih, List.map_cons]
    omega

lemma Feasible.sum_le {C : ι → ℕ} {ks : List ι} {ts : List ℕ} (h : Feasible C ks ts) :
    ts.sum ≤ (ks.map C).sum := by
  induction h with
  | nil => simp
  | cons h _ ih => simp only [List.sum_cons, List.map_cons]; omega

variable {rel : ι → ι → Prop} {C : ι → ℕ} {c : ι → ℕ → ℕ}

/-- Absorption: the first component (degree `k`, content `x`) can swallow the tail `ts` up to its
capacity without increasing the cost, leaving a feasible tail `ts'` with the remaining mass. -/
lemma absorb (hE : Exchange rel C c) (k : ι) :
    ∀ (ks : List ι) (ts : List ℕ) (x : ℕ), x ≤ C k → (∀ k' ∈ ks, rel k' k) →
      Feasible C ks ts →
      ∃ ts', Feasible C ks ts' ∧ ts'.sum = x + ts.sum - min (x + ts.sum) (C k) ∧
        c k (min (x + ts.sum) (C k)) + cost c ks ts' ≤ c k x + cost c ks ts := by
  intro ks ts x hx hrel hF
  induction hF generalizing x with
  | nil => exact ⟨[], List.Forall₂.nil, by simp [min_eq_left hx], by simp [min_eq_left hx]⟩
  | @cons k' y ks ys hy hF ih =>
    have hrel' : ∀ k'' ∈ ks, rel k'' k := fun k'' h => hrel k'' (List.mem_cons_of_mem _ h)
    set x₁ := min (x + y) (C k) with hx₁
    obtain ⟨ys', hF', hsum, hcost⟩ := ih x₁ (min_le_right _ _) hrel'
    have hex := hE k k' x y (hrel k' List.mem_cons_self) hx hy
    rw [← hx₁] at hex
    refine ⟨(x + y - x₁) :: ys', List.Forall₂.cons (by omega) hF', ?_, ?_⟩
    · simp only [List.sum_cons] at hsum ⊢; omega
    · have e : min (x₁ + ys.sum) (C k) = min (x + (y :: ys).sum) (C k) := by
        simp only [List.sum_cons]; omega
      simp only [cost_cons, ← e]
      omega

/-- **Greedy optimality, abstract form.** If the block-exchange inequality holds and the degrees
are sorted (`ks.Pairwise (fun a b => rel b a)`), the greedy vector with the same total minimises
the cost among all feasible vectors. -/
theorem greedy_le_of_exchange (hE : Exchange rel C c) :
    ∀ (ks : List ι), ks.Pairwise (fun a b => rel b a) → ∀ ts, Feasible C ks ts →
      cost c ks (greedy C ks ts.sum) ≤ cost c ks ts := by
  intro ks hs
  induction ks with
  | nil => intro ts _; simp
  | cons k ks ih =>
    intro ts hF
    rcases hF with _ | ⟨hx, hF⟩
    rename_i x ts
    rw [List.pairwise_cons] at hs
    obtain ⟨ts', hF', hsum, hcost⟩ := absorb hE k ks ts x hx hs.1 hF
    have h2 := ih hs.2 ts' hF'
    simp only [greedy, List.sum_cons, cost_cons]
    rw [← hsum] at *
    rw [hsum] at h2
    rw [hsum]
    omega

end Abstract

/-! ### The instance: integer degrees, lex-shadow costs -/

/-- Capacity `C(n,k)` of a component of (integer) exterior degree `k`; `0` if `k < 0`. -/
def capZ (n : ℕ) (k : ℤ) : ℕ := if 0 ≤ k then n.choose k.toNat else 0

/-- Cost `cᵢ(t) = σₙ(k,t)` of a component of (integer) exterior degree `k`; `0` if `k < 0`. -/
def costZ (n : ℕ) (k : ℤ) (t : ℕ) : ℕ := if 0 ≤ k then sig n k.toNat t else 0

/-- Proposition 3 (P and Q), repackaged as the block-exchange inequality on integer degrees. -/
lemma exchange_sig (n : ℕ) : Exchange (fun k' k : ℤ => k' ≤ k) (capZ n) (costZ n) := by
  intro k k' x y hk hx hy
  by_cases hk' : 0 ≤ k'
  · have hk0 : 0 ≤ k := le_trans hk' hk
    simp only [capZ, costZ, hk0, hk', ↓reduceIte] at hx hy ⊢
    have hkk : k'.toNat ≤ k.toNat := by omega
    rcases le_or_gt (x + y) (n.choose k.toNat) with h | h
    · rw [min_eq_left h, Nat.sub_self, sig_zero, add_zero]
      exact sig_P n _ _ x y hkk h hy
    · rw [min_eq_right h.le, sig_full]
      exact sig_Q n _ _ x y hkk hx hy h.le
  · have hy0 : y = 0 := by simp only [capZ, hk', ↓reduceIte] at hy; omega
    subst hy0
    simp [min_eq_left hx]

/-- **Proposition 4 (`prop-greedy`), greedy split.** Let `k₁ ≥ ⋯ ≥ k_r` be integers (any sign),
`Cᵢ = capZ n kᵢ`, `cᵢ = costZ n kᵢ`. For every `(t₁,…,t_r)` with `0 ≤ tᵢ ≤ Cᵢ` and `∑ tᵢ = T`,
`∑ᵢ cᵢ(t*ᵢ) ≤ ∑ᵢ cᵢ(tᵢ)`, `t*` the greedy vector. -/
theorem prop_greedy (n : ℕ) (ks : List ℤ) (hks : ks.Pairwise (· ≥ ·)) (ts : List ℕ)
    (hts : Feasible (capZ n) ks ts) :
    cost (costZ n) ks (greedy (capZ n) ks ts.sum) ≤ cost (costZ n) ks ts :=
  greedy_le_of_exchange (exchange_sig n) ks hks ts hts

/-- The greedy vector is admissible: `t*ᵢ ≤ Cᵢ`, and `∑ t*ᵢ = T` for `T ≤ ∑ Cᵢ`. -/
theorem greedy_admissible (n : ℕ) (ks : List ℤ) (T : ℕ) (hT : T ≤ (ks.map (capZ n)).sum) :
    Feasible (capZ n) ks (greedy (capZ n) ks T) ∧ (greedy (capZ n) ks T).sum = T :=
  ⟨greedy_feasible _ _ _, by rw [greedy_sum, min_eq_left hT]⟩

end ModuleKK
end ExteriorConvex
