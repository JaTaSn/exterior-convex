# LexF.lean — status (2026-11-17, Claude-Code agent, lean-parts-4-5 run)

File: `LEAN/ExteriorConvex/ModuleKK/LexF.lean` (1131 lines, namespace `ExteriorConvex.ModuleKK`,
imports `Mathlib` plus `ModuleKK/GreedyPQ`, `ModuleKK/Greedy`, `ModuleKK/LexShadow`). No existing file
was edited; `ExteriorConvex.lean` was not touched, so the file is not yet part of the library build.

Check, as run (about 10 s, well under the memory cap):

    cd LEAN && systemd-run --user --scope -q -p MemoryMax=7G lake env lean ExteriorConvex/ModuleKK/LexF.lean

Result: exit 0, no errors, no warnings. The only output is the 17 `#print axioms` lines at the end of
the file. `grep -w 'sorry\|native_decide\|admit'` finds nothing. All numerical anchors are kernel
`decide`.

## Summary of status

- Target 1 (lexF segments, existence and uniqueness): **proved**. Also proved: the paper's
  order-theoretic definition (an initial segment of `Mon_j(F)` for `>_lexF`) is equivalent to the
  concrete one.
- Target 2 (`lem-lexF-shadow`, both sentences): **proved**.
- Target 3 (`def-B` in ω-form; formula half of `thm-module-kk`): **proved**, with a glue lemma
  for the Macaulay identity.
- Target 4 (inequality half for monomial families): **proved**.
- Target 5 (`thm-ac42` for monomial submodules: (1_mon) ⇒ (2) ⇒ (3) ⇒ (1_mon), uniqueness, TFAE):
  **proved**.
- Target 6 (`cor-initial`): **proved**. The result is in fact stronger: it holds for every `j₀`
  and for every Macaulay term vanishing at `a = 0`, so it covers `def-B` itself, not only the
  ω-form.
- Anchors: `ex-lexF-n3` (numbers *and* the actual set families), `ex-kk-n3-d01`, `ex-ac-smallest`.
- Nothing is stuck. No `sorry` was ever needed.

## Representation

As instructed: exterior degrees `ks : List ℤ` with `ks.Pairwise (· ≥ ·)` (`kᵢ = j − dᵢ`), and a
monomial family `𝒜s : List (Finset (Finset (Fin n)))` with `List.Forall₂ Component ks 𝒜s`. The
degree-`j+1` list is `ks.map (· + 1)`. Generator degrees `ds : List ℤ` with
`ds.Pairwise (· ≤ ·)`, `extDeg ds j = ds.map (j - ·)`.

## Target 1 — lexF segments: proved

```lean
def IsLexFSeg (n : ℕ) (ks : List ℤ) (t : ℕ) (𝒜s : List (Finset (Finset (Fin n)))) : Prop :=
  List.Forall₂ (fun k 𝒜 => Component k 𝒜 ∧ IsLexInit 𝒜 k.toNat) ks 𝒜s ∧
    𝒜s.map card = greedy (capZ n) ks t

theorem exists_isLexFSeg (n : ℕ) (ks : List ℤ) (t : ℕ) : ∃ 𝒜s, IsLexFSeg n ks t 𝒜s

theorem isLexFSeg_unique {ks : List ℤ} {t : ℕ} {𝒜s ℬs : List (Finset (Finset (Fin n)))}
    (h𝒜 : IsLexFSeg n ks t 𝒜s) (hℬ : IsLexFSeg n ks t ℬs) : 𝒜s = ℬs

lemma IsLexFSeg.card_sum {ks : List ℤ} {t : ℕ} {𝒜s : List (Finset (Finset (Fin n)))}
    (h : IsLexFSeg n ks t 𝒜s) : (𝒜s.map card).sum = min t (tailCap n ks 0)

theorem isLexFSeg_unique' {ks : List ℤ} {t t' : ℕ} {𝒜s ℬs : List (Finset (Finset (Fin n)))}
    (h𝒜 : IsLexFSeg n ks t 𝒜s) (hℬ : IsLexFSeg n ks t' ℬs)
    (hc : (𝒜s.map card).sum = (ℬs.map card).sum) : 𝒜s = ℬs

theorem IsLexFSeg.forall₂_subset {ks : List ℤ} {t t' : ℕ}
    {𝒜s ℬs : List (Finset (Finset (Fin n)))} (h𝒜 : IsLexFSeg n ks t 𝒜s)
    (hℬ : IsLexFSeg n ks t' ℬs) (hle : (𝒜s.map card).sum ≤ (ℬs.map card).sum) :
    List.Forall₂ (· ⊆ ·) 𝒜s ℬs
```

Extra, for faithfulness to §`sec-lex`. The paper *defines* a lexF segment as an initial segment of
`Mon_j(F)` for the position-over-term order, and gives the greedy/lex-initial description only as
"Concretely, …". That description is now a theorem, not an assumption:

```lean
def IsLexFInitial (n : ℕ) (ks : List ℤ) (𝒜s : List (Finset (Finset (Fin n)))) : Prop :=
  List.Forall₂ Component ks 𝒜s ∧
    ∀ ⦃i l : ℕ⦄ ⦃u v : Finset (Fin n)⦄, v ∈ 𝒜s.getD l ∅ →
      i < ks.length → 0 ≤ ks.getD i 0 → #u = (ks.getD i 0).toNat →
      (i < l ∨ (i = l ∧ LexLT u v)) → u ∈ 𝒜s.getD i ∅

theorem isLexFInitial_iff {ks : List ℤ} {𝒜s : List (Finset (Finset (Fin n)))} :
    IsLexFInitial n ks 𝒜s ↔ IsLexFSeg n ks (𝒜s.map card).sum 𝒜s

theorem isLexFInitial_iff_exists {ks : List ℤ} {𝒜s : List (Finset (Finset (Fin n)))} :
    IsLexFInitial n ks 𝒜s ↔ ∃ t, IsLexFSeg n ks t 𝒜s
```

Neither direction needs `ks` sorted.

## Target 2 — `lem-lexF-shadow`: proved

```lean
theorem lem_lexF_shadow {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·)) {t : ℕ}
    {𝒜s : List (Finset (Finset (Fin n)))} (h : IsLexFSeg n ks t 𝒜s) :
    IsLexFSeg n (ks.map (· + 1)) (cost (costZ n) ks (greedy (capZ n) ks t))
      (𝒜s.map upShadow)

lemma IsLexFSeg.shadow_sum {ks : List ℤ} {t : ℕ} {𝒜s : List (Finset (Finset (Fin n)))}
    (h : IsLexFSeg n ks t 𝒜s) :
    (𝒜s.map (fun 𝒜 => #(∂⁺ 𝒜))).sum = cost (costZ n) ks (greedy (capZ n) ks t)

theorem lem_lexF_shadow_subset {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·)) {t t' : ℕ}
    {𝒜s ℬs : List (Finset (Finset (Fin n)))} (hL : IsLexFSeg n ks t 𝒜s)
    (hL' : IsLexFSeg n (ks.map (· + 1)) t' ℬs)
    (hle : (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum ≤ (ℬs.map card).sum) :
    List.Forall₂ (fun 𝒜 ℬ => ∂⁺ 𝒜 ⊆ ℬ) 𝒜s ℬs
```

Edge cases, handled with no hypothesis beyond sortedness:

- `kᵢ = −1`: the component is empty in degree `j` and has capacity 1 in degree `j+1`.
- `kᵢ > n`: the component is empty in both degrees.
- `kᵢ = n`: capacity 1, then 0, so "full shadow" is the empty family.

The numerical core is `greedyShape_shadow`: the shadow-size vector is "greedy-shaped" for the
new capacities. Sortedness enters exactly where the paper uses it. A component with `kᵢ < 0`
before position ℓ forces everything after it to be empty, so the capacity-1 components with
`kᵢ = −1` receive nothing. Without sortedness the statement is false; for example `ks = [-1, 2]`.
The paper assumes `k₁ ≥ ⋯ ≥ k_r` throughout, so this is not a finding.

## Target 3 — `def-B` in ω-form, and the formula: proved

The definitions follow `def-B` literally: `ℓ` is a `Nat.find` minimum, `a = h − T_ℓ(j)`, and
`k_ℓ = ks[ℓ−1]` (1-indexed ℓ, as in the paper). The Macaulay term is a **separate summand,
abstracted as a function `M k a`**.

```lean
def tailCap (n : ℕ) (ks : List ℤ) (ℓ : ℕ) : ℕ := ((ks.drop ℓ).map (capZ n)).sum   -- T_ℓ(j)
def ellB (n : ℕ) (ks : List ℤ) (h : ℕ) : ℕ := Nat.find (exists_tailCap_le n ks h)  -- ℓ
def remB (n : ℕ) (ks : List ℤ) (h : ℕ) : ℕ := h - tailCap n ks (ellB n ks h)       -- a
def kB (n : ℕ) (ks : List ℤ) (h : ℕ) : ℤ := ks.getD (ellB n ks h - 1) 0            -- k_ℓ
def macShadow (n k a : ℕ) : ℕ := n.choose (k + 1) - sig n k (n.choose k - a)
def growthB (M : ℕ → ℕ → ℕ) (n : ℕ) (ks : List ℤ) (h : ℕ) : ℕ :=
  tailCap n (ks.map (· + 1)) (ellB n ks h) +
    (if ellB n ks h = 0 then 0 else M (kB n ks h).toNat (remB n ks h))
def Bω (n : ℕ) (ks : List ℤ) (h : ℕ) : ℕ := growthB (macShadow n) n ks h
def Bωj (n : ℕ) (ds : List ℤ) (h : ℕ) (j : ℤ) : ℕ := Bω n (extDeg ds j) h          -- B(h,j)

lemma kB_remB_of_pos {ks : List ℤ} {h : ℕ} (hh : h ≤ tailCap n ks 0) (hℓ : ellB n ks h ≠ 0) :
    0 ≤ kB n ks h ∧ remB n ks h < n.choose (kB n ks h).toNat

theorem growthB_congr {M M' : ℕ → ℕ → ℕ} {ks : List ℤ} {h : ℕ}
    (hM : ∀ k a, a < n.choose k → M k a = M' k a) (hh : h ≤ tailCap n ks 0) :
    growthB M n ks h = growthB M' n ks h

theorem cost_greedy_add_Bω (ks : List ℤ) (hks : ks.Pairwise (· ≥ ·)) (t : ℕ)
    (ht : t ≤ tailCap n ks 0) :
    cost (costZ n) ks (greedy (capZ n) ks t) + Bω n ks (tailCap n ks 0 - t) =
      tailCap n (ks.map (· + 1)) 0

theorem thm_module_kk_formula {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·)) {t : ℕ}
    {𝒜s : List (Finset (Finset (Fin n)))} (hL : IsLexFSeg n ks t 𝒜s) :
    tailCap n (ks.map (· + 1)) 0 - (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum =
      Bω n ks (tailCap n ks 0 - (𝒜s.map card).sum)

lemma Bω_le {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·)) {h : ℕ} (hh : h ≤ tailCap n ks 0) :
    Bω n ks h ≤ tailCap n (ks.map (· + 1)) 0
```

`kB_remB_of_pos` proves the paper's remark after `def-B`: in the domain, with `ℓ ≥ 1`,
`0 ≤ k_ℓ` and `a < C(n,k_ℓ)`. Hence `k_ℓ ≤ n`, and `a = 0` when `k_ℓ = 0`. These are exactly the
hypotheses of the Macaulay identity.

**Glue to `ModuleKK/Macaulay.lean`.** That file was written concurrently by another agent; I read
it but did not import it, since it is not built. It has `macaulayUp k a` and

```lean
theorem thm_kk_rank1_moreover (n k a : ℕ) (hk : 1 ≤ k) (ha : a < n.choose k) :
    n.choose (k + 1) - sig n k (n.choose k - a) = macaulayUp k a
```

Its left-hand side is *literally* `macShadow n k a`. So `def-B` proper is
`growthB (fun k a => macaulayUp k a)`, and one application of `growthB_congr` gives
`Bω n ks h = growthB macaulayUp n ks h` for `h ≤ dim F_j`. The `k = 0` case needs `a = 0`, and
there `macShadow_zero` and `macaulayUp 0 _ = 0` (by definition) agree. The following is
**untested** (not compiled):

```lean
theorem Bω_eq_defB {ks : List ℤ} {h : ℕ} (hh : h ≤ tailCap n ks 0) :
    Bω n ks h = growthB macaulayUp n ks h :=
  growthB_congr (fun k a ha => by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · obtain rfl : a = 0 := by simpa using ha
      simp [macShadow_zero, macaulayUp]
    · exact thm_kk_rank1_moreover n k a hk ha) hh
```

Every `Bω`/`Bωj` statement below then transfers to `def-B` by that one rewrite.
`cor_initial_growthB` is already stated for any `M` with `M k 0 = 0`.

## Target 4 — the inequality for monomial families: proved

```lean
theorem thm_module_kk_ineq_mon {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·))
    {𝒜s ℒs : List (Finset (Finset (Fin n)))} (h𝒜 : List.Forall₂ Component ks 𝒜s) {t : ℕ}
    (hL : IsLexFSeg n ks t ℒs) (hsz : (ℒs.map card).sum = (𝒜s.map card).sum) :
    (ℒs.map fun ℒ => #(∂⁺ ℒ)).sum ≤ (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum

theorem thm_module_kk_bound_mon {ks : List ℤ} (hks : ks.Pairwise (· ≥ ·))
    {𝒜s : List (Finset (Finset (Fin n)))} (h𝒜 : List.Forall₂ Component ks 𝒜s) :
    tailCap n (ks.map (· + 1)) 0 - (𝒜s.map fun 𝒜 => #(∂⁺ 𝒜)).sum ≤
      Bω n ks (tailCap n ks 0 - (𝒜s.map card).sum)
```

**Name clash avoided.** I first called these `thm_module_kk_ineq` and `thm_module_kk_bound`. The
concurrent `ModuleKK/Subspace.lean` declares `thm_module_kk_ineq` (the subspace version) in the same
namespace, so mine carry the suffix `_mon`. I compared all other declaration names against
`Macaulay.lean` and `Subspace.lean` as they stood at the end of my run: no other collisions.

## Target 5 — `thm-ac42` for monomial submodules: proved

```lean
def extDeg (ds : List ℤ) (j : ℤ) : List ℤ := ds.map (j - ·)
def dimF (n : ℕ) (ds : List ℤ) (j : ℤ) : ℕ := tailCap n (extDeg ds j) 0
structure IsMonSubmodule (n : ℕ) (ds : List ℤ) (A : ℤ → List (Finset (Finset (Fin n)))) :
    Prop where
  comp : ∀ j, List.Forall₂ Component (extDeg ds j) (A j)
  shad : ∀ j, List.Forall₂ (fun 𝒜 ℬ => ∂⁺ 𝒜 ⊆ ℬ) (A j) (A (j + 1))
def quotHF (n : ℕ) (ds : List ℤ) (A : ℤ → List (Finset (Finset (Fin n)))) (j : ℤ) : ℕ :=
  dimF n ds j - ((A j).map card).sum
def IsLexSubmodule (n : ℕ) (ds : List ℤ) (L : ℤ → List (Finset (Finset (Fin n)))) : Prop :=
  IsMonSubmodule n ds L ∧ ∀ j, ∃ t, IsLexFSeg n (extDeg ds j) t (L j)

theorem cor_prop41_mon {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·))
    {A : ℤ → List (Finset (Finset (Fin n)))} (hA : IsMonSubmodule n ds A) (j : ℤ) :
    quotHF n ds A (j + 1) ≤ Bωj n ds (quotHF n ds A j) j

theorem lexSeq_isLexSubmodule {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·)) (h : ℤ → ℕ)
    (hdim : ∀ j, h j ≤ dimF n ds j) (hB : ∀ j, h (j + 1) ≤ Bωj n ds (h j) j) :
    IsLexSubmodule n ds (lexSeq n ds h) ∧ ∀ j, quotHF n ds (lexSeq n ds h) j = h j

theorem thm_ac42_two_three {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·)) {d₁ dr : ℤ} (h : ℤ → ℕ)
    (hsupp : ∀ j, j < d₁ ∨ dr + n < j → h j = 0)
    (hB : ∀ j, d₁ - 1 ≤ j → j ≤ dr + n - 1 → h (j + 1) ≤ Bωj n ds (h j) j) :
    ∃ L, IsLexSubmodule n ds L ∧ ∀ j, quotHF n ds L j = h j

theorem thm_ac42_unique {ds : List ℤ} {L L' : ℤ → List (Finset (Finset (Fin n)))}
    (hL : IsLexSubmodule n ds L) (hL' : IsLexSubmodule n ds L')
    (hh : ∀ j, quotHF n ds L j = quotHF n ds L' j) : L = L'

theorem thm_ac42_mon {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·)) {d₁ dr : ℤ}
    (_hd₁ : ds.head? = some d₁) (_hdr : ds.getLast? = some dr) (h : ℤ → ℕ)
    (hsupp : ∀ j, j < d₁ ∨ dr + n < j → h j = 0) :
    List.TFAE [∃ A, IsMonSubmodule n ds A ∧ ∀ j, quotHF n ds A j = h j,
      ∀ j, d₁ - 1 ≤ j → j ≤ dr + n - 1 → h (j + 1) ≤ Bωj n ds (h j) j,
      ∃ L, IsLexSubmodule n ds L ∧ ∀ j, quotHF n ds L j = h j]
```

The proof follows the paper:

- (1_mon) ⇒ (2) is `cor_prop41_mon` at each `j`, and it holds for *every* `j ∈ ℤ`.
- (2) ⇒ (3) first proves `h_j ≤ dim F_j` by induction from `h_{d₁−1} = 0`, using `Bω_le`.
- It then takes `L_j` = the lexF segment of size `dim F_j − h_j` and gets `Shad L_j ⊆ L_{j+1}`
  from `lem_lexF_shadow_subset` and `cost_greedy_add_Bω`.
- Outside the window, condition (2) is automatic because `h_{j+1} = 0`.

**Glue to `ModuleKK/Subspace.lean`, not done here.** That file proves, for arbitrary graded
families of subspaces, `H(j+1) ≤ dim F_{j+1} − cost(greedy(dim F_j − H(j)))` (its `cor_prop41`).
Adding `cost_greedy_add_Bω` with `t = dim F_j − H(j)` turns that into `H(j+1) ≤ Bω(H(j), j)`: the
full `cor-prop41`, and hence `thm-ac42` (1) ⇒ (2) for arbitrary graded submodules. The bridge
between the two encodings:

- `Subspace.lean` writes the degree list as `List.ofFn (fun i => j - d i)` for `d : Fin r → ℤ`.
  Here it is `extDeg (List.ofFn d) j`. The two are equal by `List.map_ofFn`.
- Its `finrank_Fdeg` must also be matched to `tailCap … 0`.

## Target 6 — `cor-initial`: proved (in a stronger form)

```lean
theorem growthB_count {M : ℕ → ℕ → ℕ} (hM0 : ∀ k, M k 0 = 0) : ∀ (ks : List ℤ),
    ks.Pairwise (· ≥ ·) → ∀ h, h ≤ ks.count 0 → growthB M n ks h = n * h + ks.count (-1)

theorem cor_initial_growthB {M : ℕ → ℕ → ℕ} (hM0 : ∀ k, M k 0 = 0) {ds : List ℤ}
    (hds : ds.Pairwise (· ≤ ·)) (j₀ : ℤ) :
    growthB M n (extDeg ds (j₀ - 1)) 0 = ds.count j₀ ∧
      ∀ h, 1 ≤ h → h ≤ ds.count j₀ →
        growthB M n (extDeg ds j₀) h = n * h + ds.count (j₀ + 1)

theorem cor_initial {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·)) (j₀ : ℤ) :
    Bωj n ds 0 (j₀ - 1) = ds.count j₀ ∧
      ∀ h, 1 ≤ h → h ≤ ds.count j₀ → Bωj n ds h j₀ = n * h + ds.count (j₀ + 1)

theorem cor_initial_instances {ds : List ℤ} (hds : ds.Pairwise (· ≤ ·)) (h : ℤ → ℕ) (j₀ : ℤ)
    (h0 : h (j₀ - 1) = 0) (h1 : 1 ≤ h j₀) :
    (h j₀ ≤ Bωj n ds (h (j₀ - 1)) (j₀ - 1) ↔ h j₀ ≤ ds.count j₀) ∧
      (h j₀ ≤ ds.count j₀ →
        (h (j₀ + 1) ≤ Bωj n ds (h j₀) j₀ ↔ h (j₀ + 1) ≤ n * h j₀ + ds.count (j₀ + 1)))
```

Here `r̃₀ = ds.count j₀` and `r̃₁ = ds.count (j₀ + 1)`. The Macaulay term vanishes because `a = 0`
throughout. So `cor_initial_growthB` holds for *any* Macaulay term with `M k 0 = 0`. That includes
the ω-form (`macShadow_zero`) and the printed `a^{(k)}` (convention `0^{(k)} = 0`). The ω-form
therefore suffices, and `def-B` itself is covered without the Macaulay glue.

## Numerical anchors (entrywise, kernel `decide`)

`ex-lexF-n3` (`n = 3`, `d = (0,1)`, `j = 2`):

- `extDeg [0,1] 2 = [2,1]`; `dimF 3 [0,1] 2 = 6`.
- `greedy (capZ 3) [2,1] 4 = [3,1]`.
- Component shadow sizes: `zipWith (costZ 3) [2,1] [3,1] = [1,2]`; `|Shad L| = 3`.
- `greedy (capZ 3) [3,2] 3 = [1,2]`; `dimF 3 [0,1] 3 = 4`.
- `ℓ = 2`, `a = 2`, `k_ℓ = 1`, and `Bωj 3 [0,1] 2 2 = 1`.
- The sets themselves:
  - `∂⁺ {{0,1},{0,2},{1,2}} = {{0,1,2}}` and `∂⁺ {{0}} = {{0,1},{0,2}}`.
  - `IsLexFSeg 3 (extDeg [0,1] 2) 4 [{{0,1},{0,2},{1,2}}, {{0}}]`.
  - `IsLexFSeg 3 (extDeg [0,1] 3) 3 [{{0,1,2}}, {{0,1},{0,2}}]`.
  - These are checked by `decide` on the definitions (`LexLT`, `IsLexInit`), not through the
    lemmas.

`ex-kk-n3-d01`:

- `n = 3`, `d = (0,1)`: `dimF` for `j = 0..4` is `[1,4,6,4,1]`.
- `B(4,2) = 3`, with `ℓ = 1`, `a = 1`.
- `B(3,3) = 1`, with `ℓ = 1`, `a = 0`.
- `n = 4`, `d = (0,1)`: `dimF 4 [0,1] 2 = 10` and `B(6,2) = 6`, with `ℓ = 1`, `a = 2`.

`ex-ac-smallest` (`n = 1`, `d = (0,0)`):

- `B(0,−1) = 2 = r̃₀`.
- `B(1,0) = 1 = n·1 + r̃₁`, which is `< 2`, as the example says.

## `#print axioms` (verbatim output)

```
'ExteriorConvex.ModuleKK.exists_isLexFSeg' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.isLexFSeg_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.isLexFInitial_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.lem_lexF_shadow' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.lem_lexF_shadow_subset' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.growthB_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.cost_greedy_add_Bω' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.thm_module_kk_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.thm_module_kk_ineq_mon' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.thm_module_kk_bound_mon' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.cor_prop41_mon' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.thm_ac42_two_three' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.thm_ac42_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.thm_ac42_mon' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.cor_initial_growthB' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.cor_initial' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.ModuleKK.cor_initial_instances' depends on axioms: [propext, Classical.choice, Quot.sound]
```

(This is the output of the final compile, after the `_mon` rename: exit 0, nothing else printed.)

## Deviations from the printed statements

1. **Monomial level only.** No subspaces, no `lem-monomial`. Consequences:
   - `thm-module-kk` is stated for monomial families; `V` is replaced by `𝒜`, and `dim E₁V` by
     `|Shad 𝒜|`.
   - `thm-ac42`'s condition (1) is restricted to monomial submodules ("(1_mon)").
   - `cor-prop41`'s "with equality for the submodule generated by the lexF segment" is not stated
     as a submodule statement. Its content is the formula `thm_module_kk_formula`.
2. **ω-form of `B`**, as instructed. The Macaulay term `a^{(k_ℓ)}` is replaced by
   `macShadow n k_ℓ a`, as a separate summand of `growthB M`. `growthB_congr` is the glue.
3. **Out of domain.** `growthB`/`Bω` are total functions. For `h > dim F_j` they return junk
   (`ℓ = 0`, so `B = dim F_{j+1}`). Every theorem uses them only in the domain `h ≤ dim F_j`, or
   proves `h_j ≤ dim F_j` first.
4. **Indexing.** `k_ℓ` is `(ks.getD (ℓ−1) 0).toNat`. The `toNat` is harmless: `k_ℓ ≥ 0` in the
   domain (`kB_remB_of_pos`). `ℓ` keeps the paper's meaning: the number of leading components
   not in the tail, with `T_ℓ` the sum over `ks.drop ℓ`.
5. **lexF segment definition.** The task's concrete form (`IsLexFSeg`, greedy sizes plus
   lex-initial components) is the working definition. The paper's order-theoretic definition is
   `IsLexFInitial`, proved equivalent. For `t > dim F_j`, `IsLexFSeg n ks t` is all of `Mon_j(F)`.
   Existence and uniqueness are proved for every `t`, which is stronger than `t ≤ dim F_j`.
6. **`thm_ac42_mon` unused hypotheses.** It carries `_hd₁ : ds.head? = some d₁` and
   `_hdr : ds.getLast? = some dr`, to say which window the paper means. The proof never uses them
   (see observation 2 below); the underscores keep the unused-variable linter quiet.
7. **`cor-initial` scope.** Stated for every `j₀ ∈ ℤ`, with `r̃` written as `ds.count`. The
   paper's `j₀ = min{j : h_j ≠ 0}` enters only in `cor_initial_instances`, as `h (j₀−1) = 0`
   and `1 ≤ h j₀`.

## Findings

**No defect found** in `def-B`, `lem-lexF-shadow`, `thm-module-kk` (formula, inequality),
`cor-prop41`, `thm-ac42` or `cor-initial`. No statement needed a hypothesis the paper does not
state. Observations, all of them strengthenings rather than errors:

1. **`cor-initial` holds for every integer `j₀`, not only the initial degree.**
   `B(0, j₀−1) = r̃₀` and `B(h, j₀) = n·h + r̃₁` for `0 ≤ h ≤ r̃₀`, so the second identity holds at
   `h = 0` too. Proof: `growthB_count`. The initial-degree hypothesis matters only for reading these
   as "the instances `j = j₀−1`, `j₀` of condition (2)".
2. **`thm-ac42`'s equivalence holds for any window `[d₁, d_r + n]` containing the support of `h`.**
   The proof uses neither `d₁ = min d` nor `d_r = max d`. (1) ⇒ (2) holds for every `j ∈ ℤ`
   (`cor_prop41_mon`, as `cor-prop41` says). For (2) ⇒ (3), (2) outside the window is automatic
   because `h_{j+1} = 0` there.
3. **The convention `0^{(k)} = 0` is automatic in shadow form** (`macShadow_zero`). So is the
   remark after `def-B` that `0 ≤ k_ℓ ≤ n`, `0 ≤ a < C(n,k_ℓ)`, and `a = 0` when `k_ℓ = 0`
   (`kB_remB_of_pos`).
4. **Sortedness is genuinely needed in `lem-lexF-shadow`.** The counterexample is
   `ks = [-1, 2]`. The paper always assumes it, so this is not a gap.
5. **The paper's "Concretely" description of lexF segments is correct**, and needs no
   sortedness (`isLexFInitial_iff`).

## Stuck items

None.
