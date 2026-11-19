# Macaulay operator and the "Moreover" clause of `thm-kk-rank1` — STATUS

2026-11-17 21:59 — Claude-Code (jts-mini), Lean parts 4–5 run, Macaulay sub-task.

**Status: done.** The "Moreover" identity of Theorem `thm-kk-rank1` (article 5) is proved as
printed. The Macaulay operator of Definition `def-B` is defined and tied to the printed
definition by existence, uniqueness and a value theorem. No `sorry`, no `native_decide`, no
edits to existing files, nothing committed.

File: `20-projects/exterior-convex/LEAN/ExteriorConvex/ModuleKK/Macaulay.lean` (423 lines),
namespace `ExteriorConvex.ModuleKK`, imports `Mathlib` and `ExteriorConvex.ModuleKK.LexShadow`
(which brings in `GreedyPQ`). It compiles cleanly, with no errors and no warnings:
`systemd-run --user --scope -q -p MemoryMax=7G lake env lean ExteriorConvex/ModuleKK/Macaulay.lean`.
It is **not** yet imported by `ExteriorConvex.lean`; the coordinator adds that line.

## Mathlib search

Mathlib has no Macaulay or cascade representation. The header of
`Mathlib/Combinatorics/SetFamily/KruskalKatona.lean` lists *"Define the `k`-cascade
representation of a natural and prove the corresponding version of [Kruskal–Katona]"* as a
TODO. Grepping Mathlib for `cascade`, `macaulay`, `pseudo`, `combinadic` and
`binomial representation` finds nothing else. `Colex.lean` has no counting results of this
kind. So the operator is built here.

## How the operator is defined, and how it is tied to the printed definition

The greedy operator is computable:

- `def macTop (k a : ℕ) : ℕ := Nat.findGreatest (fun m => m.choose k ≤ a) (a + k)` gives the
  largest `m` with `C(m,k) ≤ a`. The bound `a + k` is enough because
  `lt_choose_add : 1 ≤ k → a < (a+k).choose k`.
- `def macaulayUp : ℕ → ℕ → ℕ`, defined by
  `macaulayUp 0 _ = 0` and
  `macaulayUp (k+1) a = (macTop (k+1) a).choose (k+2) + macaulayUp k (a - (macTop (k+1) a).choose (k+1))`.

The printed representation is defined literally. `IsMacaulayRep k a s A` means `1 ≤ s ≤ k`,
`A i < A (i+1)` for `s ≤ i < k` (that is, a_k > … > a_s), `s ≤ A s`, and
`a = ∑ i ∈ Icc s k, (A i).choose i`. Only the values of `A` on [s,k] matter.

Three theorems tie the two together:

- `exists_macaulayRep : ∀ {k a : ℕ}, 1 ≤ k → 1 ≤ a → ∃ s A, IsMacaulayRep k a s A`
- `macaulayRep_unique : ∀ {k a s s' : ℕ} {A A' : ℕ → ℕ}, IsMacaulayRep k a s A → IsMacaulayRep k a s' A' → s = s' ∧ ∀ i ∈ Icc s k, A i = A' i`
- `macaulayUp_eq_sum : ∀ {k a s : ℕ} {A : ℕ → ℕ}, IsMacaulayRep k a s A → macaulayUp k a = ∑ i ∈ Icc s k, (A i).choose (i + 1)`

The printed definition is also written out as a Lean definition,
`noncomputable def macaulayPrinted (k a : ℕ) : ℕ`. For k ≥ 1 and a ≥ 1 it chooses the
representation through `exists_macaulayRep` and returns Σ C(a_i, i+1); otherwise it returns 0.
Then `macaulayPrinted_eq : ∀ (k a : ℕ), macaulayPrinted k a = macaulayUp k a` holds.

The key lemma behind all of this is `IsMacaulayRep.bracket`: the top coefficient satisfies
`C(a_k,k) ≤ a < C(a_k+1,k)`. Two further lemmas: `macaulayUp_zero_right` (0^{(k)} = 0) and
`macaulayUp_choose` (C(N,k)^{(k)} = C(N,k+1) for k ≥ 1).

## The identity

- **`macaulay_sig : ∀ (n k a : ℕ), 1 ≤ k → a ≤ n.choose k → n.choose (k + 1) - sig n k (n.choose k - a) = macaulayUp k a`**
  (Macaulay.lean:326). This covers one more value of `a` than the paper prints.
- **`thm_kk_rank1_moreover : ∀ (n k a : ℕ), 1 ≤ k → a < n.choose k → n.choose (k + 1) - sig n k (n.choose k - a) = macaulayUp k a`**
  (Macaulay.lean:364). This is the printed statement.
- `thm_kk_rank1_moreover_rep : 1 ≤ k → a < n.choose k → IsMacaulayRep k a s A → n.choose (k + 1) - sig n k (n.choose k - a) = ∑ i ∈ Icc s k, (A i).choose (i + 1)`
  (Macaulay.lean:369). The right side here is the printed formula.
- `thm_kk_rank1_moreover_lex : IsLexInit 𝒜 k → 1 ≤ k → a < n.choose k → #𝒜 = n.choose k - a → n.choose (k + 1) - #(∂⁺ 𝒜) = macaulayUp k a`
  (Macaulay.lean:377). Here ω_n is the size of an actual lex shadow, through `lexInit_upShadow`.

The right side does not involve `n`, so `n`-independence is part of what is proved. Helper:
`sig_le_choose : t ≤ C(n,k) → sig n k t ≤ C(n,k+1)`.

**Proof.** Induction on n through the recursion of `sig` (`lem-lex-rank1`(2)). Put
g(n,k,a) = C(n,k+1) − σ_n(k, C(n,k) − a). Then:

- g(n+1, k+1, a) = g(n, k+1, a) for a ≤ C(n,k+1);
- g(n+1, k+1, a) = C(n,k+2) + g(n, k, a − C(n,k+1)) for C(n,k+1) < a < C(n+1,k+1). The greedy
  step of `macaulayUp` takes m = n on exactly this range.

The value a = C(n+1,k+1) is handled by `macaulayUp_choose`. When k = 0, the middle range is
empty.

## `#print axioms`

All of the following give `[propext, Classical.choice, Quot.sound]`: `thm_kk_rank1_moreover`,
`macaulay_sig`, `thm_kk_rank1_moreover_rep`, `thm_kk_rank1_moreover_lex`, `macaulayUp_eq_sum`,
`exists_macaulayRep`, `macaulayRep_unique`, `macaulayPrinted_eq`. This was checked on a scratch
copy with the `#print axioms` lines appended. The file itself carries no `#print` commands.

## Numerical anchors (kernel `decide`, all entrywise)

- Single values: 1^{(2)} = 0, 2^{(2)} = 0, 3^{(2)} = 1, 2^{(1)} = 1, 4^{(2)} = 1, 5^{(2)} = 2,
  6^{(2)} = 4, 7^{(3)} = 2.
  - By hand: 7 = C(4,3) + C(3,2), so 7^{(3)} = C(4,4) + C(3,3) = 2. A set-level check agrees:
    among the colex-first 7 three-sets, 1234 and 1235 are the only four-sets all of whose
    three-subsets lie in the family.
- The representation `IsMacaulayRep 3 7 2 (a₃ = 4, a₂ = 3)` is proved, and its Σ C(a_i, i+1)
  equals `macaulayUp 3 7`.
- Both sides of the identity, as lists over all a < C(n,k), equal the hand/Python values:
  - n = 6, k = 2: `[0,0,0,1,1,2,4,4,5,7,10,10,11,13,16]`
  - n = 5, k = 3: `[0,0,0,0,1,1,1,2,2,3]`
  - n = 4, k = 1: `[0,0,1,3]`
  - Also σ₅(3,3) = 3.
- An independent Python check (σ by recursion, operator by greedy) agrees for all
  n ≤ 11, all k, and all 0 ≤ a ≤ C(n,k). The only exceptions are the k = 0, a = 1 cases
  described under Findings.

## Findings / deviations from the printed statement

1. **The printed statement is correct as printed.** It needs no extra hypothesis. The edge cases
   behave as follows:
   - a = 0: covered, since 0^{(k)} = 0.
   - k > n: vacuous, since C(n,k) = 0.
   - n = 0: vacuous for k ≥ 1.
2. **The identity also holds at a = C(n,k)** when k ≥ 1: `macaulay_sig` is stated for
   a ≤ C(n,k). Both sides then equal C(n,k+1).
3. **The hypothesis k ≥ 1 is genuinely needed, but only for that extra value.** At k = 0, the
   printed range a < C(n,0) = 1 leaves only a = 0, where the identity holds (both sides are 0).
   At a = 1 = C(n,0), the left side is n and 0^{(0)} is undefined in the paper (`macaulayUp`
   gives 0). The file records this as two `decide` examples. The paper never meets this case,
   since k_ℓ = 0 forces a = 0 there.
4. **`macaulayPrinted` and the case k = 0, a ≥ 1.** `def-B` defines a^{(k)} only for k ≥ 1,
   a ≥ 1, and for a = 0. `macaulayPrinted` and `macaulayUp` both give 0 for k = 0, a ≥ 1. This
   is a junk-value convention, documented in the docstring. It is never used by the theorem.
5. **For the article.** The margin note at article5 line 553 says the "Moreover" identity is
   *"not formalised anywhere in ModuleKK/"*. Once this file is in the library, that note and the
   `\leanpartial` mark on `thm-kk-rank1` can be updated. The same applies to the intro wording
   at lines 249–255 ("the inequality of Theorem thm-kk-rank1"). These are not changed here
   (house rule: no edits to `article/`).

## Stuck

Nothing.
