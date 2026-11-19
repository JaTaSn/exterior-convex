# Subspace half of Module Kruskal–Katona — status (2026-11-17)

File: `LEAN/ExteriorConvex/ModuleKK/Subspace.lean` (646 lines, new; imports `Mathlib` and
`ExteriorConvex.ModuleKK.LexShadow`). Namespace `ExteriorConvex.ModuleKK`.

Compiles with
`systemd-run --user --scope -q -p MemoryMax=7G lake env lean ExteriorConvex/ModuleKK/Subspace.lean`:
no errors, no warnings, no `sorry`, no `native_decide`. No existing file was edited. **The file is
not yet imported from `ExteriorConvex.lean`** (I was told not to touch it), so `lake build` of the
library does not see it yet. Add `import ExteriorConvex.ModuleKK.Subspace` there.

## Status of the four targets

- **Target 1 (leading monomials, `#in(W) = dim W`): done.** `card_inn`.
- **Target 2 (`lem-monomial`): done.** `isLead_ex`, `shad_inn_subset`, `lem_monomial`. Extra: the
  monomial case holds with equality (`E1_monoSpan`, `finrank_E1_monoSpan`).
- **Target 3 (inequality of `thm-module-kk` for subspaces): done.** `thm_module_kk_ineq`.
- **Target 4 (`cor-prop41`, inequality): done**, in three forms: `cor_prop41_local`, `cor_prop41`
  (graded family), `cor_prop41_submodule` (an E-stable subspace and its Hilbert function). Also
  `finrank_Fdeg` (dim F_j = ∑ᵢ C(n, j − dᵢ)).
- **Not done (not requested):** the equality clause of `cor-prop41`; identifying the greedy cost
  with |Shad L| and with B (another agent's job); identifying the model with Mathlib's
  `ExteriorAlgebra`.

## Modelling choices

- **Monomials:** `abbrev Mon (r n : ℕ) := Fin r × Finset (Fin n)`. The pair (i, σ) is e_σ gᵢ. The
  ground set is `Fin n` = {0,…,n−1}, the paper's [n] shifted as in `LexShadow.lean`.
- **Vectors:** `abbrev FMod (K) (r n) := Mon r n → K`, over an arbitrary `[Field K]`. This is the
  whole of F as a K-vector space (all degrees at once, dimension r·2ⁿ). Every subspace of it is
  finite-dimensional automatically.
- **Graded pieces:** `Fdeg K n d j : Submodule K (FMod K r n)`, for generator degrees
  `d : Fin r → ℤ` and `j : ℤ`. These are the vectors v with `v m ≠ 0 → (#m.2 : ℤ) = j − d m.1`.
  So component i has exterior degree kᵢ = j − dᵢ, and it has no monomials when kᵢ < 0 or kᵢ > n.
  `Fdeg_eq_monoSpan` identifies it with the span of `monDeg n d j` = Mon_j(F).
- **Why d and j rather than a list ks:** F_j and F_{j+1} have to live in one ambient space, with
  e_x mapping one into the other. The degree list that connects to `module_shadow_ge_greedy` is
  `List.ofFn fun i => j - d i`. The paper's d₁ ≤ ⋯ ≤ d_r is the hypothesis `Monotone d`, which
  gives `(List.ofFn …).Pairwise (· ≥ ·)` through `List.pairwise_ofFn`. The components of in(V) are
  passed as `List.ofFn (comp (inn V))`, with a small helper `forall₂_ofFn`; `List.Forall₂ Component`
  then comes from `component_comp_inn`.
- **The sign:** `extSign x σ : K := (-1) ^ #(σ.filter (· < x))`. This is ε(x,σ) = (−1)^{#{y ∈ σ : y < x}}.
- **The action:** `ex x : FMod K r n →ₗ[K] FMod K r n`, defined by
  `(ex x v) (i, τ) = if x ∈ τ then extSign x (τ.erase x) * v (i, τ.erase x) else 0`.
  - `ex_single`: on basis vectors this is e_x·(e_σ gᵢ) = ε(x,σ) e_{σ∪{x}} gᵢ if x ∉ σ, and 0 if
    x ∈ σ.
  - Sanity checks on the sign: `ex_ex_self` (e_x e_x = 0) and `ex_comm` (e_x e_y = −e_y e_x for
    x ≠ y). So the operators really satisfy the exterior relations.
  - An E-submodule is modelled as a K-subspace closed under every `ex x`.
- **E₁V:** `E1 V := Submodule.span K {w | ∃ x, ∃ v ∈ V, ex x v = w}`.
- **lexF:** `LexFGT m m' := m.1 < m'.1 ∨ (m.1 = m'.1 ∧ LexLT m.2 m'.2)`. This is m >_lexF m',
  exactly the paper's definition. The proofs go through a sort key,
  `lexFKey m := toLex (m.1, toColex (phi m.2))` in `Fin r ×ₗ Colex (Finset (Fin n))`.
  `lexFGT_iff_key` says that m >_lexF m' iff key m < key m' (via `lexLT_iff_colex`), and
  `lexFKey_injective` holds. So lexF is a strict total order on all of `Mon r n`. Within one degree
  it is the paper's order; across sizes it is an extension that is never used for v ∈ F_j.
- **Leading monomials:**
  - `IsLead v m := v m ≠ 0 ∧ ∀ m', v m' ≠ 0 → m' ≠ m → LexFGT m m'`.
  - `lead v (hv : v ≠ 0)` is in(v) as a function, characterised by `isLead_iff_lead_eq`.
  - `inn W := univ.filter fun m => ∃ w ∈ W, IsLead w m`. `mem_inn_iff_lead` shows this is
    {in(w) : 0 ≠ w ∈ W}.
- **Shadows:**
  - `comp 𝒜 i` is the family 𝒜ᵢ.
  - `Shad 𝒜 := univ.filter fun m => m.2 ∈ ∂⁺ (comp 𝒜 m.1)`, i.e. ⊔ᵢ (∇𝒜ᵢ) gᵢ.
  - `mem_Shad_iff`: Shad 𝒜 is the set of e_x m with x ∉ m.
  - `card_Shad`: |Shad 𝒜| = ∑ᵢ |∇𝒜ᵢ|.
- **Monomial subspaces:** `monoSpan K 𝒜` is the set of vectors supported on 𝒜.
  `monoSpan_eq_span` proves it equals `Submodule.span K (Pi.single · 1 '' 𝒜)`.
- **Hilbert function:** `hilbQ d M j := finrank K (Fdeg K n d j) - finrank K ↥(M ⊓ Fdeg K n d j)`.
  This is the paper's H_{F/M}(j) = dim F_j − dim M_j.

## Proof route for target 1 (not Gaussian elimination)

Mathlib has nothing reusable for leading terms of vectors under an arbitrary order on the index
type, so I proved it directly, in two short steps:

- `linearIndependent_of_isLead`: a family with injective leading monomials is linearly
  independent. In a dependency, look at the lexF-largest leading monomial that carries a non-zero
  coefficient: only one vector contributes there. This gives `#in(W) ≤ dim W`
  (`card_inn_le_finrank`).
- `finrank_le_card_inn`: restricting coordinates, W → K^{in(W)}, is injective, because a non-zero
  w has w(in(w)) ≠ 0 and in(w) ∈ in(W). This gives `dim W ≤ #in(W)`.

## Headline signatures

The common context is `{K : Type u_1} [Field K] {r n : ℕ}`.

```
theorem card_inn (W : Submodule K (FMod K r n)) : #(inn W) = finrank K ↥W

theorem isLead_ex {v : FMod K r n} {i : Fin r} {σ : Finset (Fin n)} (h : IsLead v (i, σ))
    {x : Fin n} (hx : x ∉ σ) : IsLead (ex x v) (i, insert x σ)

theorem shad_inn_subset (V : Submodule K (FMod K r n)) : Shad (inn V) ⊆ inn (E1 V)

theorem lem_monomial :
    (∀ W : Submodule K (FMod K r n), #(inn W) = finrank K ↥W) ∧
      ∀ V : Submodule K (FMod K r n), #(Shad (inn V)) ≤ finrank K ↥(E1 V)

theorem E1_monoSpan (𝒜 : Finset (Mon r n)) : E1 (monoSpan K 𝒜) = monoSpan K (Shad 𝒜)
theorem finrank_E1_monoSpan (𝒜 : Finset (Mon r n)) : finrank K ↥(E1 (monoSpan K 𝒜)) = #(Shad 𝒜)

theorem thm_module_kk_ineq (d : Fin r → ℤ) (hd : Monotone d) (j : ℤ)
    (V : Submodule K (FMod K r n)) (hV : V ≤ Fdeg K n d j) :
    cost (costZ n) (List.ofFn fun i => j - d i)
        (greedy (capZ n) (List.ofFn fun i => j - d i) (finrank K ↥V)) ≤ finrank K ↥(E1 V)

theorem finrank_Fdeg (d : Fin r → ℤ) (j : ℤ) : finrank K ↥(Fdeg K n d j) = ∑ i, capZ n (j - d i)
lemma finrank_Fdeg_eq_sum_capZ (d : Fin r → ℤ) (j : ℤ) :
    finrank K ↥(Fdeg K n d j) = ((List.ofFn fun i => j - d i).map (capZ n)).sum

theorem cor_prop41_local (d : Fin r → ℤ) (hd : Monotone d) (j : ℤ)
    {V W : Submodule K (FMod K r n)} (hV : V ≤ Fdeg K n d j) (hVW : E1 V ≤ W) :
    finrank K ↥(Fdeg K n d (j + 1)) - finrank K ↥W ≤
      finrank K ↥(Fdeg K n d (j + 1)) - cost (costZ n) (List.ofFn fun i => j - d i)
        (greedy (capZ n) (List.ofFn fun i => j - d i) (finrank K ↥V))

theorem cor_prop41 (d : Fin r → ℤ) (hd : Monotone d) (M : ℤ → Submodule K (FMod K r n))
    (hM : ∀ j, M j ≤ Fdeg K n d j) (hE : ∀ j, E1 (M j) ≤ M (j + 1)) (j : ℤ) :
    finrank K ↥(Fdeg K n d (j + 1)) - finrank K ↥(M (j + 1)) ≤
      finrank K ↥(Fdeg K n d (j + 1)) - cost (costZ n) (List.ofFn fun i => j - d i)
        (greedy (capZ n) (List.ofFn fun i => j - d i) (finrank K ↥(M j)))

theorem cor_prop41_submodule (d : Fin r → ℤ) (hd : Monotone d) (M : Submodule K (FMod K r n))
    (hM : ∀ x, ∀ v ∈ M, ex x v ∈ M) (j : ℤ) :
    hilbQ d M (j + 1) ≤
      finrank K ↥(Fdeg K n d (j + 1)) - cost (costZ n) (List.ofFn fun i => j - d i)
        (greedy (capZ n) (List.ofFn fun i => j - d i) (finrank K ↥(Fdeg K n d j) - hilbQ d M j))
```

Line numbers in `Subspace.lean`:

- `card_inn` 218
- `isLead_ex` 400, `shad_inn_subset` 422, `lem_monomial` 430
- `E1_monoSpan` 499, `finrank_E1_monoSpan` 506
- `thm_module_kk_ineq` 541
- `finrank_Fdeg` 578
- `cor_prop41_local` 602, `cor_prop41` 614, `cor_prop41_submodule` 629
- `ex_single` 248, `ex_comm` 303

## `#print axioms`

The check was run on a scratch copy of the file with `#print axioms` lines appended. Every one of
these reports `[propext, Classical.choice, Quot.sound]` and nothing else:

- `card_inn`, `linearIndependent_of_isLead`
- `isLead_ex`, `shad_inn_subset`, `lem_monomial`
- `E1_monoSpan`, `finrank_E1_monoSpan`, `monoSpan_eq_span`
- `thm_module_kk_ineq`
- `finrank_Fdeg`, `finrank_Fdeg_eq_sum_capZ`
- `cor_prop41_local`, `cor_prop41`, `cor_prop41_submodule`
- `ex_single`, `ex_ex_self`, `ex_comm`

## Findings and deviations from the printed statements

No defect was found in `lem-monomial`, `thm-module-kk` (inequality half) or `cor-prop41`
(inequality half). The paper's d₁ ≤ ⋯ ≤ d_r assumption is genuinely used. Everything else
differs from the printed statements only by being *more* general or by taking a different proof
route:

1. **`lem-monomial` needs no grading hypothesis.** The paper states it for V ⊆ F_j. In Lean,
   `card_inn` and `shad_inn_subset` hold for every subspace of F. This generalises the statement;
   it does not weaken it.
2. **The Gaussian-elimination step is replaced** by the two-inequality argument above. The paper's
   proof is fine as written; the Lean route is just shorter.
3. **`lexLT_insert` needs only x ∉ σ.** The paper's compatibility argument,
   (u∪{x}) △ (u′∪{x}) = u △ u′, assumes x is in neither set. For the direction used,
   σ >lex τ ⟹ σ∪{x} >lex τ∪{x}, only x ∉ σ is needed. This is a remark, not an error.
4. **The ordering hypothesis is needed, and is the paper's standing assumption.**
   `thm_module_kk_ineq` takes `Monotone d`, the Setup's d₁ ≤ ⋯ ≤ d_r. It cannot be dropped from
   the cost(greedy) form. Counterexample: n = 2, d = (1, 0), j = 1, so ks = [0, 1]. Take
   V = span{e₀ g₁}. Then dim E₁V = 1, but the greedy split of 1 in list order is (1, 0), which
   costs σ₂(0,1) = |∇{∅}| = 2 > 1. Not a defect: the paper assumes the ordering throughout.
5. **`cor-prop41` does not need gradedness.** The paper states it for graded submodules M. The
   proof uses only E₁M_j ⊆ M_{j+1}. So `cor_prop41_submodule` is stated for any E-stable subspace
   M, with M_j := M ∩ F_j; for a graded M, `hilbQ` is H_{F/M}. The right-hand side is
   dim F_{j+1} − cost(greedy(dim F_j − H(j))). This is the paper's B(H(j), j) *only after* the
   other agent's identification of the cost with |Shad L| and with B.
6. **The Setup's "equivalently" claim is now proved.** The Setup says Shad 𝒜 is "the set of
   monomials of E₁·span 𝒜" (lines 458 and 466–467). This is `E1_monoSpan`. Together with the other
   agent's |Shad L| = cost(greedy), it supplies the dimension count that the equality clause of
   `cor-prop41` needs. That clause is not formalised: it would also need the degree-(j+1) piece of
   the E-submodule generated by span L, which is E₁·span L, and that is not done.

## Stuck items

None. Nothing was left half-done or removed.
