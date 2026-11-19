/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The Macaulay operator `a^{(k)}` and the "Moreover" clause of Theorem KK

Formalisation, for article 5 (`article/exterior-convex_article5_draft_1.org`), of

* Definition `def-B`, the part defining the Macaulay operator: for `k ≥ 1` and `a ≥ 1`,
  `a^{(k)} = C(a_k, k+1) + C(a_{k-1}, k) + ⋯ + C(a_s, s+1)`, where
  `a = C(a_k, k) + C(a_{k-1}, k-1) + ⋯ + C(a_s, s)` with `a_k > a_{k-1} > ⋯ > a_s ≥ s ≥ 1` is the
  `k`-th Macaulay representation of `a`; and `0^{(k)} = 0`.
* The "Moreover" clause of Theorem `thm-kk-rank1`: for `k ≥ 1` and `0 ≤ a < C(n,k)`,
  `C(n, k+1) − ωₙ(k, C(n,k) − a) = a^{(k)}`.

Mathlib has no Macaulay (cascade) representation: `Combinatorics/SetFamily/KruskalKatona.lean`
lists "define the `k`-cascade representation" as a TODO. So it is built here.

* `macaulayUp k a` : the operator, computably, by the greedy algorithm: `macTop k a` is the largest
  `m` with `C(m,k) ≤ a`; `macaulayUp (k+1) a = C(m, k+2) + macaulayUp k (a − C(m, k+1))`,
  `macaulayUp 0 a = 0`.
* `IsMacaulayRep k a s A` : the printed representation, literally: `1 ≤ s ≤ k`,
  `A k > A (k-1) > ⋯ > A s ≥ s`, `a = ∑_{i=s}^{k} C(A i, i)`.
  `exists_macaulayRep` (existence for `k, a ≥ 1`), `macaulayRep_unique` (uniqueness of `s` and of
  `A` on `[s, k]`), `macaulayUp_eq_sum` (`macaulayUp k a = ∑_{i=s}^{k} C(A i, i+1)` for every
  representation). `macaulayPrinted` is the printed definition read as a Lean `def` (choose the
  representation), and `macaulayPrinted_eq` says it is `macaulayUp`.
* `macaulay_sig` : `C(n,k+1) − sig n k (C(n,k) − a) = macaulayUp k a` for `k ≥ 1`,
  `a ≤ C(n,k)` (one more value of `a` than printed). `thm_kk_rank1_moreover` is the printed
  range `a < C(n,k)`, `thm_kk_rank1_moreover_rep` the same with the right side written through
  the representation, and `thm_kk_rank1_moreover_lex` the same with `sig` replaced by the size of
  the upper shadow of an actual lex-initial family (via `lexInit_upShadow`, `LexShadow.lean`).

Proof of `macaulay_sig`: induction on `n`, through the recursion of `sig` (Lemma `lem-lex-rank1`
(2)). With `g n k a = C(n,k+1) − sig n k (C(n,k) − a)`, that recursion becomes
`g (n+1) (k+1) a = g n (k+1) a` for `a ≤ C(n,k+1)` and
`g (n+1) (k+1) a = C(n,k+2) + g n k (a − C(n,k+1))` for `C(n,k+1) < a < C(n+1,k+1)`; the greedy
step of `macaulayUp (k+1) a` on that range takes `m = n`, which is the same second equation.

Changelog (newest first): 2026-11-17 created (Claude-Code agent, Lean parts 4–5 run)
-/
import Mathlib
import ExteriorConvex.ModuleKK.LexShadow

open Finset
open scoped FinsetFamily

namespace ExteriorConvex
namespace ModuleKK

/-! ### The greedy operator -/

/-- The top index of the greedy step: the largest `m` with `C(m,k) ≤ a` (searched below `a + k`,
which suffices for `k ≥ 1` by `lt_choose_add`). -/
def macTop (k a : ℕ) : ℕ := Nat.findGreatest (fun m => m.choose k ≤ a) (a + k)

/-- **The Macaulay operator `a^{(k)}`** (Definition `def-B`), computed greedily: take the largest
`m` with `C(m,k) ≤ a`, contribute `C(m,k+1)`, and recurse on `a − C(m,k)` with `k − 1`.
`macaulayUp_eq_sum` ties it to the printed definition. -/
def macaulayUp : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, a =>
      (macTop (k + 1) a).choose (k + 2) + macaulayUp k (a - (macTop (k + 1) a).choose (k + 1))

/-- `C(a+k, k) > a` for `k ≥ 1`. -/
lemma lt_choose_add (a k : ℕ) (hk : 1 ≤ k) : a < (a + k).choose k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  induction a with
  | zero => simp
  | succ a ih =>
    rw [show a + 1 + (j + 1) = (a + (j + 1)) + 1 by omega, Nat.choose_succ_succ']
    have : 0 < (a + (j + 1)).choose j := Nat.choose_pos (by omega)
    omega

/-- The greedy step finds the bracket `C(m,k) ≤ a < C(m+1,k)`. -/
lemma macTop_spec (k a : ℕ) (hk : 1 ≤ k) :
    (macTop k a).choose k ≤ a ∧ a < (macTop k a + 1).choose k := by
  have h0 : (0 : ℕ).choose k ≤ a := by rw [Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _
  have hspec : (macTop k a).choose k ≤ a :=
    Nat.findGreatest_spec (P := fun m => m.choose k ≤ a) (Nat.zero_le _) h0
  refine ⟨hspec, ?_⟩
  by_contra hlt
  rw [not_lt] at hlt
  have hle : macTop k a ≤ a + k := Nat.findGreatest_le _
  rcases Nat.lt_or_ge (macTop k a) (a + k) with h | h
  · exact Nat.findGreatest_is_greatest (P := fun m => m.choose k ≤ a) (n := a + k)
      (Nat.lt_succ_self _) h hlt
  · have hm : macTop k a = a + k := le_antisymm hle h
    have := lt_choose_add a k hk
    rw [hm] at hspec
    omega

/-- The bracket `C(m,k) ≤ a < C(m+1,k)` determines `m`. -/
lemma bracket_unique {k a m m' : ℕ} (h1 : m.choose k ≤ a) (h2 : a < (m + 1).choose k)
    (h1' : m'.choose k ≤ a) (h2' : a < (m' + 1).choose k) : m = m' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := Nat.choose_le_choose k (show m + 1 ≤ m' by omega); omega
  · have := Nat.choose_le_choose k (show m' + 1 ≤ m by omega); omega

lemma macTop_eq {k a m : ℕ} (hk : 1 ≤ k) (h1 : m.choose k ≤ a) (h2 : a < (m + 1).choose k) :
    macTop k a = m :=
  bracket_unique (macTop_spec k a hk).1 (macTop_spec k a hk).2 h1 h2

/-- One greedy step, with the top index named. -/
lemma macaulayUp_succ_of {k a m : ℕ} (h1 : m.choose (k + 1) ≤ a)
    (h2 : a < (m + 1).choose (k + 1)) :
    macaulayUp (k + 1) a = m.choose (k + 2) + macaulayUp k (a - m.choose (k + 1)) := by
  rw [macaulayUp, macTop_eq (by omega) h1 h2]

@[simp] lemma macaulayUp_zero_left (a : ℕ) : macaulayUp 0 a = 0 := rfl

/-- `0^{(k)} = 0`. -/
@[simp] lemma macaulayUp_zero_right (k : ℕ) : macaulayUp k 0 = 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [macaulayUp_succ_of (m := k) (by rw [Nat.choose_eq_zero_of_lt (by omega)])
      (by rw [Nat.choose_self]; omega), Nat.choose_eq_zero_of_lt (by omega : k < k + 2),
      Nat.choose_eq_zero_of_lt (by omega : k < k + 1), Nat.sub_zero, ih]

/-- `C(N,k)^{(k)} = C(N,k+1)` for `k ≥ 1`. -/
lemma macaulayUp_choose (N k : ℕ) (hk : 1 ≤ k) : macaulayUp k (N.choose k) = N.choose (k + 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  by_cases hN : j + 1 ≤ N
  · have hpos : 0 < N.choose j := Nat.choose_pos (by omega)
    rw [macaulayUp_succ_of (m := N) le_rfl (by rw [Nat.choose_succ_succ']; omega), Nat.sub_self,
      macaulayUp_zero_right, add_zero]
  · rw [Nat.choose_eq_zero_of_lt (by omega : N < j + 1), Nat.choose_eq_zero_of_lt (by omega),
      macaulayUp_zero_right]

/-! ### The printed definition: the `k`-th Macaulay representation -/

/-- **`k`-th Macaulay representation** (Definition `def-B`): `(s, A)` represents `a` when
`1 ≤ s ≤ k`, `a_k > a_{k-1} > ⋯ > a_s ≥ s` (with `a_i = A i`), and
`a = C(a_k, k) + C(a_{k-1}, k-1) + ⋯ + C(a_s, s)`. Only the values of `A` on `[s, k]` matter. -/
def IsMacaulayRep (k a s : ℕ) (A : ℕ → ℕ) : Prop :=
  1 ≤ s ∧ s ≤ k ∧ (∀ i, s ≤ i → i < k → A i < A (i + 1)) ∧ s ≤ A s ∧
    a = ∑ i ∈ Icc s k, (A i).choose i

namespace IsMacaulayRep

variable {k a s : ℕ} {A : ℕ → ℕ}

lemma one_le (h : IsMacaulayRep k a s A) : 1 ≤ a := by
  obtain ⟨hs1, hsk, -, hsA, hsum⟩ := h
  have h1 : (A s).choose s ≤ a := by
    rw [hsum]
    exact single_le_sum (f := fun i => (A i).choose i) (fun _ _ => Nat.zero_le _)
      (mem_Icc.mpr ⟨le_rfl, hsk⟩)
  have := Nat.choose_pos hsA
  omega

lemma top {k a : ℕ} {A : ℕ → ℕ} (h : IsMacaulayRep (k + 1) a (k + 1) A) :
    a = (A (k + 1)).choose (k + 1) := by
  rw [h.2.2.2.2, Icc_self, sum_singleton]

lemma restrict {k a s : ℕ} {A : ℕ → ℕ} (h : IsMacaulayRep (k + 1) a s A) (hs : s ≤ k) :
    IsMacaulayRep k (a - (A (k + 1)).choose (k + 1)) s A ∧ (A (k + 1)).choose (k + 1) ≤ a := by
  obtain ⟨hs1, -, hinc, hsA, hsum⟩ := h
  rw [sum_Icc_succ_top (by omega)] at hsum
  refine ⟨⟨hs1, hs, fun i h1 h2 => hinc i h1 (by omega), hsA, by omega⟩, by omega⟩

/-- The top coefficient brackets `a`: `C(a_k, k) ≤ a < C(a_k + 1, k)`. This is what makes the
greedy algorithm find the representation. -/
lemma bracket : ∀ {k a s : ℕ} {A : ℕ → ℕ}, IsMacaulayRep k a s A →
    (A k).choose k ≤ a ∧ a < (A k + 1).choose k
  | 0, _, _, _, h => absurd h.2.1 (by have := h.1; omega)
  | k + 1, a, s, A, h => by
    by_cases hs : s ≤ k
    · obtain ⟨hr, hle⟩ := h.restrict hs
      have ih := bracket hr
      have hinc : A k < A (k + 1) := h.2.2.1 k hs (by omega)
      have hmono := Nat.choose_le_choose k (show A k + 1 ≤ A (k + 1) by omega)
      rw [Nat.choose_succ_succ']
      omega
    · have hs' : s = k + 1 := by have := h.2.1; omega
      subst hs'
      have ha := h.top
      have hpos : 0 < (A (k + 1)).choose k := Nat.choose_pos (by have := h.2.2.2.1; omega)
      rw [Nat.choose_succ_succ']
      omega

end IsMacaulayRep

/-- **The greedy operator is the printed one**: for every `k`-th Macaulay representation
`a = ∑_{i=s}^{k} C(a_i, i)`, `macaulayUp k a = ∑_{i=s}^{k} C(a_i, i+1)`. -/
theorem macaulayUp_eq_sum : ∀ {k a s : ℕ} {A : ℕ → ℕ}, IsMacaulayRep k a s A →
    macaulayUp k a = ∑ i ∈ Icc s k, (A i).choose (i + 1)
  | 0, _, _, _, h => absurd h.2.1 (by have := h.1; omega)
  | k + 1, a, s, A, h => by
    obtain ⟨h1, h2⟩ := h.bracket
    rw [macaulayUp_succ_of h1 h2]
    by_cases hs : s ≤ k
    · rw [macaulayUp_eq_sum (h.restrict hs).1, sum_Icc_succ_top (by omega), add_comm]
    · have hs' : s = k + 1 := by have := h.2.1; omega
      subst hs'
      rw [← h.top, Nat.sub_self, macaulayUp_zero_right, Icc_self, sum_singleton, add_zero]

/-- **Existence** of the `k`-th Macaulay representation, for `k ≥ 1` and `a ≥ 1`. -/
theorem exists_macaulayRep : ∀ {k a : ℕ}, 1 ≤ k → 1 ≤ a → ∃ s A, IsMacaulayRep k a s A
  | 0, _, hk, _ => absurd hk (by omega)
  | k + 1, a, _, ha => by
    obtain ⟨h1, h2⟩ := macTop_spec (k + 1) a (by omega)
    set m := macTop (k + 1) a with hm
    have hmk : k + 1 ≤ m := by
      by_contra hlt
      have := Nat.choose_le_choose (k + 1) (show m + 1 ≤ k + 1 by omega)
      rw [Nat.choose_self] at this
      omega
    rw [Nat.choose_succ_succ'] at h2
    by_cases ha' : a - m.choose (k + 1) = 0
    · refine ⟨k + 1, fun _ => m, by omega, le_rfl, fun i h1 h2 => by omega, hmk, ?_⟩
      rw [Icc_self, sum_singleton]
      show a = m.choose (k + 1)
      omega
    · have hk1 : 1 ≤ k := by
        by_contra hk0
        have : k = 0 := by omega
        subst this
        rw [Nat.choose_zero_right] at h2
        omega
      obtain ⟨s, A', hA'⟩ := exists_macaulayRep hk1 (show 1 ≤ a - m.choose (k + 1) by omega)
      have hb := hA'.bracket
      have hAk : A' k < m := by
        by_contra hle
        have := Nat.choose_le_choose k (show m ≤ A' k by omega)
        omega
      obtain ⟨hs1, hsk, hinc, hsA, hsum⟩ := hA'
      refine ⟨s, fun i => if i = k + 1 then m else A' i, hs1, by omega, fun i hi1 hi2 => ?_,
        by simp only [show s ≠ k + 1 by omega, ↓reduceIte]; exact hsA, ?_⟩
      · rcases Nat.lt_or_ge i k with hik | hik
        · simp only [show i ≠ k + 1 by omega, show i + 1 ≠ k + 1 by omega, ↓reduceIte]
          exact hinc i hi1 hik
        · have : i = k := by omega
          subst this
          simp only [show i ≠ i + 1 by omega, ↓reduceIte]
          exact hAk
      · rw [sum_Icc_succ_top (by omega)]
        have e1 : ∑ i ∈ Icc s k, ((fun i => if i = k + 1 then m else A' i) i).choose i =
            ∑ i ∈ Icc s k, (A' i).choose i := by
          refine sum_congr rfl fun i hi => ?_
          have : i ≠ k + 1 := by have := (mem_Icc.mp hi).2; omega
          simp only [this, ↓reduceIte]
        have e2 : ((fun i => if i = k + 1 then m else A' i) (k + 1)).choose (k + 1) =
            m.choose (k + 1) := by simp only [↓reduceIte]
        rw [e1, e2, ← hsum]
        omega

/-- **Uniqueness** of the `k`-th Macaulay representation: the same `s`, and the same `a_i` for
`s ≤ i ≤ k`. -/
theorem macaulayRep_unique : ∀ {k a s s' : ℕ} {A A' : ℕ → ℕ}, IsMacaulayRep k a s A →
    IsMacaulayRep k a s' A' → s = s' ∧ ∀ i ∈ Icc s k, A i = A' i
  | 0, _, _, _, _, _, h, _ => absurd h.2.1 (by have := h.1; omega)
  | k + 1, a, s, s', A, A', h, h' => by
    obtain ⟨b1, b2⟩ := h.bracket
    obtain ⟨b1', b2'⟩ := h'.bracket
    have htop : A (k + 1) = A' (k + 1) := bracket_unique b1 b2 b1' b2'
    by_cases hs : s ≤ k <;> by_cases hs' : s' ≤ k
    · have ih := macaulayRep_unique (h.restrict hs).1 (htop ▸ (h'.restrict hs').1)
      refine ⟨ih.1, fun i hi => ?_⟩
      rcases Nat.lt_or_ge i (k + 1) with hik | hik
      · exact ih.2 i (mem_Icc.mpr ⟨(mem_Icc.mp hi).1, by omega⟩)
      · rw [show i = k + 1 by have := (mem_Icc.mp hi).2; omega]; exact htop
    · have hs'' : s' = k + 1 := by have := h'.2.1; omega
      subst hs''
      have h0 := h'.top
      have := (h.restrict hs).1.one_le
      rw [htop] at this
      omega
    · have hs'' : s = k + 1 := by have := h.2.1; omega
      subst hs''
      have h0 := h.top
      have := (h'.restrict hs').1.one_le
      rw [← htop] at this
      omega
    · have e1 : s = k + 1 := by have := h.2.1; omega
      have e2 : s' = k + 1 := by have := h'.2.1; omega
      subst e1; subst e2
      refine ⟨rfl, fun i hi => ?_⟩
      rw [Icc_self, mem_singleton] at hi
      rw [hi]; exact htop

/-- The printed definition `def-B`, read literally as a Lean definition: for `k ≥ 1` and `a ≥ 1`,
choose the `k`-th Macaulay representation `a = ∑_{i=s}^{k} C(a_i, i)` and return
`∑_{i=s}^{k} C(a_i, i+1)`; otherwise `0` (the printed `0^{(k)} = 0`; for `k = 0`, `a ≥ 1` the
manuscript defines nothing, and the value `0` is a convention that never arises there). -/
noncomputable def macaulayPrinted (k a : ℕ) : ℕ :=
  if h : 1 ≤ k ∧ 1 ≤ a then
    ∑ i ∈ Icc (exists_macaulayRep h.1 h.2).choose k,
      ((exists_macaulayRep h.1 h.2).choose_spec.choose i).choose (i + 1)
  else 0

/-- The printed operator and the greedy one agree everywhere. -/
theorem macaulayPrinted_eq (k a : ℕ) : macaulayPrinted k a = macaulayUp k a := by
  unfold macaulayPrinted
  split_ifs with h
  · exact (macaulayUp_eq_sum (exists_macaulayRep h.1 h.2).choose_spec.choose_spec).symm
  · rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk; rfl
    · have : a = 0 := by omega
      subst this; rw [macaulayUp_zero_right]

/-! ### The identity with the lex shadow -/

/-- The lex shadow of `t ≤ C(n,k)` sets of size `k` has at most `C(n,k+1)` elements. -/
lemma sig_le_choose : ∀ (n k t : ℕ), t ≤ n.choose k → sig n k t ≤ n.choose (k + 1)
  | 0, k, t, _ => by simp [sig]
  | n + 1, 0, t, ht => by
    rw [Nat.choose_zero_right] at ht
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
    · rw [sig_zero]; exact Nat.zero_le _
    · rw [sig_n0_one, Nat.choose_one_right]
  | n + 1, k + 1, t, ht => by
    rw [Nat.choose_succ_succ'] at ht
    rw [Nat.choose_succ_succ' n (k + 1)]
    by_cases h : t ≤ n.choose k
    · rw [sig_R1 h]
      have := sig_le_choose n k t h
      omega
    · rw [sig_R2 (by omega)]
      have := sig_le_choose n (k + 1) (t - n.choose k) (by omega)
      omega

/-- **`C(n,k+1) − ωₙ(k, C(n,k) − a) = a^{(k)}`** for `k ≥ 1` and `0 ≤ a ≤ C(n,k)`, with
`ωₙ = sig` and `a^{(k)} = macaulayUp k a`. The right side does not depend on `n`. -/
theorem macaulay_sig : ∀ (n k a : ℕ), 1 ≤ k → a ≤ n.choose k →
    n.choose (k + 1) - sig n k (n.choose k - a) = macaulayUp k a
  | 0, k, a, hk, ha => by
    rw [Nat.choose_eq_zero_of_lt (by omega : 0 < k)] at ha
    rw [Nat.le_zero.mp ha, macaulayUp_zero_right, Nat.choose_eq_zero_of_lt (by omega)]
    simp [sig]
  | n + 1, k, a, hk, ha => by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    have pk := Nat.choose_succ_succ' n j
    have pk1 := Nat.choose_succ_succ' n (j + 1)
    rcases Nat.lt_or_ge a ((n + 1).choose (j + 1)) with hlt | hge
    · rcases le_or_gt a (n.choose (j + 1)) with h1 | h1
      · -- `a ≤ C(n, j+1)`: the lex segment contains all sets through `0`
        rw [sig_R2 (by omega), show (n + 1).choose (j + 1) - a - n.choose j =
          n.choose (j + 1) - a by omega]
        have ih := macaulay_sig n (j + 1) a hk h1
        have hle := sig_le_choose n (j + 1) (n.choose (j + 1) - a) (by omega)
        omega
      · -- `C(n, j+1) < a < C(n+1, j+1)`: the greedy step takes `m = n`
        rw [sig_R1 (by omega), macaulayUp_succ_of (m := n) h1.le hlt,
          show (n + 1).choose (j + 1) - a = n.choose j - (a - n.choose (j + 1)) by omega]
        rcases Nat.eq_zero_or_pos j with hj | hj
        · -- `j = 0` cannot occur here: `C(n,1) < a < C(n,0) + C(n,1)`
          subst hj
          rw [Nat.choose_zero_right] at pk
          omega
        · have ih := macaulay_sig n j (a - n.choose (j + 1)) hj (by omega)
          have hle := sig_le_choose n j (n.choose j - (a - n.choose (j + 1))) (by omega)
          have e : (n + 1).choose (j + 1 + 1) = n.choose (j + 1) + n.choose (j + 2) :=
            Nat.choose_succ_succ' n (j + 1)
          omega
    · -- `a = C(n+1, j+1)`
      have : a = (n + 1).choose (j + 1) := le_antisymm ha hge
      subst this
      rw [Nat.sub_self, sig_zero, Nat.sub_zero, macaulayUp_choose _ _ hk]

/-- **Theorem `thm-kk-rank1`, "Moreover" clause, as printed**: for `k ≥ 1` and `0 ≤ a < C(n,k)`,
`C(n, k+1) − ωₙ(k, C(n,k) − a) = a^{(k)}`. -/
theorem thm_kk_rank1_moreover (n k a : ℕ) (hk : 1 ≤ k) (ha : a < n.choose k) :
    n.choose (k + 1) - sig n k (n.choose k - a) = macaulayUp k a :=
  macaulay_sig n k a hk ha.le

/-- The same, with `a^{(k)}` written through the `k`-th Macaulay representation of `a ≥ 1`. -/
theorem thm_kk_rank1_moreover_rep {n k a s : ℕ} {A : ℕ → ℕ} (hk : 1 ≤ k) (ha : a < n.choose k)
    (hrep : IsMacaulayRep k a s A) :
    n.choose (k + 1) - sig n k (n.choose k - a) = ∑ i ∈ Icc s k, (A i).choose (i + 1) := by
  rw [thm_kk_rank1_moreover n k a hk ha, macaulayUp_eq_sum hrep]

/-- The same, with `ωₙ(k, C(n,k) − a)` the size of the upper shadow of an actual lex-initial family
of `C(n,k) − a` sets of size `k` (`lexInit_upShadow`): the `(k+1)`-sets outside the shadow of the
first `C(n,k) − a` sets in lex order number `a^{(k)}`. -/
theorem thm_kk_rank1_moreover_lex {n k a : ℕ} {𝒜 : Finset (Finset (Fin n))}
    (h𝒜 : IsLexInit 𝒜 k) (hk : 1 ≤ k) (ha : a < n.choose k) (hc : #𝒜 = n.choose k - a) :
    n.choose (k + 1) - #(∂⁺ 𝒜) = macaulayUp k a := by
  rw [(lexInit_upShadow n k 𝒜 h𝒜).1, hc]
  exact thm_kk_rank1_moreover n k a hk ha

/-! ### Numerical anchors, entrywise -/

-- the operator, value by value (hand computation: 3 = C(3,2) ↦ C(3,3) = 1; 5 = C(3,2) + C(2,1)
-- ↦ C(3,3) + C(2,2) = 2; 6 = C(4,2) ↦ C(4,3) = 4; 7 = C(4,3) + C(3,2) ↦ C(4,4) + C(3,3) = 2)
example : macaulayUp 2 1 = 0 := by decide
example : macaulayUp 2 2 = 0 := by decide
example : macaulayUp 2 3 = 1 := by decide
example : macaulayUp 1 2 = 1 := by decide
example : macaulayUp 2 4 = 1 := by decide
example : macaulayUp 2 5 = 2 := by decide
example : macaulayUp 2 6 = 4 := by decide
example : macaulayUp 3 7 = 2 := by decide

-- the representation of 7 at k = 3 is (s, a₃, a₂) = (2, 4, 3), and the sum formula gives 2
example : IsMacaulayRep 3 7 2 (fun i => if i = 3 then 4 else 3) := by
  refine ⟨by omega, by omega, fun i h1 h2 => ?_, by decide, by decide⟩
  interval_cases i; decide
example : macaulayUp 3 7 = ∑ i ∈ Icc 2 3, ((fun i => if i = 3 then 4 else 3) i).choose (i + 1) := by
  decide

-- the identity, entrywise over all a < C(n,k): both sides as lists
example : (List.range (Nat.choose 6 2)).map (fun a => Nat.choose 6 3 - sig 6 2 (Nat.choose 6 2 - a))
    = [0, 0, 0, 1, 1, 2, 4, 4, 5, 7, 10, 10, 11, 13, 16] := by decide
example : (List.range 15).map (macaulayUp 2) = [0, 0, 0, 1, 1, 2, 4, 4, 5, 7, 10, 10, 11, 13, 16] :=
  by decide
example : (List.range (Nat.choose 5 3)).map (fun a => Nat.choose 5 4 - sig 5 3 (Nat.choose 5 3 - a))
    = [0, 0, 0, 0, 1, 1, 1, 2, 2, 3] := by decide
example : (List.range 10).map (macaulayUp 3) = [0, 0, 0, 0, 1, 1, 1, 2, 2, 3] := by decide
example : (List.range (Nat.choose 4 1)).map (fun a => Nat.choose 4 2 - sig 4 1 (Nat.choose 4 1 - a))
    = [0, 0, 1, 3] := by decide
example : (List.range 4).map (macaulayUp 1) = [0, 0, 1, 3] := by decide
example : sig 5 3 3 = 3 := by decide

-- why `macaulay_sig` assumes `1 ≤ k`: at `k = 0` the extra value `a = C(n,0) = 1` fails
-- (left side `C(3,1) − ω₃(0,0) = 3`, while `macaulayUp 0 1 = 0`); the printed range `a < C(n,0)`
-- leaves only `a = 0`, where both sides are `0`
example : Nat.choose 3 1 - sig 3 0 (Nat.choose 3 0 - 1) = 3 := by decide
example : Nat.choose 3 1 - sig 3 0 (Nat.choose 3 0 - 0) = 0 := by decide

end ModuleKK
end ExteriorConvex
