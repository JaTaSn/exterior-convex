# Lean formalisation of Proposition gap-one — STATUS

2026-11-18 07:21, Claude-Code agent (Fable 5.2). One new file, nothing else touched, nothing committed:

`20-projects/exterior-convex/LEAN/ExteriorConvex/Vertices/GapOne.lean` (namespace `ExteriorConvex.GapOne`)

Compiled alone with
`systemd-run --user --scope -q -p MemoryMax=7G lake env lean ExteriorConvex/Vertices/GapOne.lean`:
no errors, no warnings, empty output. No `sorry`, `admit`, `native_decide`, or axioms.
The file is NOT imported by `ExteriorConvex.lean` (I was told not to edit it), so a `lake build`
will not pick it up until someone adds `import ExteriorConvex.Vertices.GapOne`.

## Done: all of (A)–(E)

Definitions (0-based `Fin n`; index `j` stands for the paper's `j+1`):

```lean
noncomputable def theta (n : ℕ) : ℝ := Real.pi / (n + 4)
noncomputable def lam (n : ℕ) : ℝ := 1 + 2 * Real.cos (2 * theta n)
noncomputable def qq (n : ℕ) : ℝ := 1 / (2 * Real.cos (theta n))
noncomputable def Ssum (n j : ℕ) : ℝ :=
  if j ≤ n then qq n ^ j * Real.sin (((j : ℝ) + 2) * theta n) else 0
noncomputable def xvec (n : ℕ) : Fin n → ℝ := fun j => Ssum n (j.val + 1) - Ssum n (j.val + 2)
noncomputable def xmin (n : ℕ) : ℝ :=   -- univ.inf' of xvec n   (1 if n = 0)
noncomputable def xmax (n : ℕ) : ℝ :=   -- univ.sup' of xvec n   (1 if n = 0)
noncomputable def gapc (n : ℕ) : ℝ := (∑ j, xvec n j) / (lam n * xmax n)
noncomputable def gapC (n : ℕ) : ℝ := (∑ j, xvec n j) / (lam n * xmin n)
```

### (A) entry formula

```lean
theorem Mext_one_eq_one_iff (hslc : Pairwise.SLC a n) (i j : Fin n) :
    Mext a n 1 i j = 1 ↔ (i.val ≤ j.val + 1 ∧ ¬ (j = i ∧ 1 ≤ i.val ∧ i.val + 2 ≤ n))

theorem Mext_one_apply (hslc : Pairwise.SLC a n) (i j : Fin n) :
    Mext a n 1 i j =
      if i.val ≤ j.val + 1 ∧ ¬ (j = i ∧ 1 ≤ i.val ∧ i.val + 2 ≤ n) then 1 else 0
```

The paper's description is correct, for every `n` (no `n ≥ 2` and no positivity needed here).

### (B) positive eigenvector

```lean
theorem xvec_pos (j : Fin n) : 0 < xvec n j

theorem Mext_one_mulVec_xvec (hslc : Pairwise.SLC a n) (hn : 2 ≤ n) :
    (Mext a n 1).map (Nat.cast : ℕ → ℝ) *ᵥ xvec n = lam n • xvec n
```

Also `xvec_eq_of_lt` (x_j = q^{j+1} sin((j+1)θ) for j < n, paper indexing), `xvec_last`
(x_n = q^n sin 2θ), `lam_eq` (λ = 4cos²θ − 1), `one_le_lam`.

### (C) spectral statement

```lean
theorem eigenvalue_norm_le_lam (hslc : Pairwise.SLC a n) (hn : 2 ≤ n) (μ : ℂ) (v : Fin n → ℂ)
    (hv : v ≠ 0) (hμ : (Mext a n 1).map (Nat.cast : ℕ → ℂ) *ᵥ v = μ • v) : ‖μ‖ ≤ lam n
```

Together with (B) (`lam n` is an eigenvalue, eigenvector `xvec n ≠ 0`) this is "spectral radius
= lam n", without Mathlib's `spectralRadius`. Generic lemma behind it: `eig_norm_le`.

### (D) two-sided bound for the powers

```lean
theorem gapOne_power_bounds (hslc : Pairwise.SLC a n) (hn : 2 ≤ n) {r : ℕ} (hr : 1 ≤ r) :
    gapc n * lam n ^ r ≤ (((fun _ => 1) ⬝ᵥ (Mext a n 1 ^ (r - 1) *ᵥ fun _ => 1) : ℕ) : ℝ) ∧
      (((fun _ => 1) ⬝ᵥ (Mext a n 1 ^ (r - 1) *ᵥ fun _ => 1) : ℕ) : ℝ) ≤ gapC n * lam n ^ r
```

with `gapc_pos (hn : 0 < n) : 0 < gapc n` and `gapc_le_gapC (hn : 0 < n) : gapc n ≤ gapC n`.
Generic lemma: `count_bounds`.

### (E) vertex counts

```lean
theorem gapOne_vertex_bounds (hpos : ∀ s, 0 < a s) (hslc : Pairwise.SLC a n) (hn : 2 ≤ n)
    {r N : ℕ} (hr : 1 ≤ r) (hN : r + n ≤ N + 1) :
    gapc n * lam n ^ r ≤
        ((Set.extremePoints ℝ (∑ p ∈ range r, convexHull ℝ (vsetA a N p n))).ncard : ℝ) ∧
      ((Set.extremePoints ℝ (∑ p ∈ range r, convexHull ℝ (vsetA a N p n))).ncard : ℝ) ≤
        gapC n * lam n ^ r

theorem gapOne_vertex_bounds_koz (hn : 2 ≤ n) {r N : ℕ} (hr : 1 ≤ r) (hN : r + n ≤ N + 1) :
    gapc n * lam n ^ r ≤
        ((Set.extremePoints ℝ (convexHull ℝ (ffSet n N (fun i : Fin r => (i : ℕ))))).ncard : ℝ) ∧
      ((Set.extremePoints ℝ (convexHull ℝ (ffSet n N (fun i : Fin r => (i : ℕ))))).ncard : ℝ) ≤
        gapC n * lam n ^ r

theorem exists_gapOne_vertex_bounds (hn : 2 ≤ n) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ a : ℕ → ℝ, (∀ s, 0 < a s) → Pairwise.SLC a n →
      ∀ r N : ℕ, 1 ≤ r → r + n ≤ N + 1 →
        c * lam n ^ r ≤
            ((Set.extremePoints ℝ (∑ p ∈ range r, convexHull ℝ (vsetA a N p n))).ncard : ℝ) ∧
          ((Set.extremePoints ℝ (∑ p ∈ range r, convexHull ℝ (vsetA a N p n))).ncard : ℝ) ≤
            C * lam n ^ r
```

`hN : r + n ≤ N + 1` is the ambient-dimension condition `∀ p < r, p + n ≤ N` of
`cor_vertex_count` for shifts `d p = p`.

## Axioms

`#print axioms` was run on nine theorems and the lines then removed. Output, verbatim:

```
'ExteriorConvex.GapOne.Mext_one_eq_one_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.GapOne.Mext_one_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.GapOne.xvec_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.GapOne.Mext_one_mulVec_xvec' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.GapOne.eigenvalue_norm_le_lam' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.GapOne.gapOne_power_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.GapOne.gapOne_vertex_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.GapOne.gapOne_vertex_bounds_koz' depends on axioms: [propext, Classical.choice, Quot.sound]
'ExteriorConvex.GapOne.exists_gapOne_vertex_bounds' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## The paper's proof: findings

No step of the written proof was found false; the Lean proof follows it line by line
(entry formula, telescoping tail sums S_i, the three row cases, weighted sup norm, sandwich
x_min 𝟙 ≤ x ≤ x_max 𝟙). No extra hypothesis was needed. Remarks:

- **Positivity of `a` is a silent hypothesis of the proposition.** The statement says only
  "strictly log-concave"; the Setting makes every leg vector positive. In Lean, (A)–(D) need
  strict log-concavity alone (the entry formula at gap one never uses positivity); positivity
  enters only in (E), through `cor_vertex_count`. Worth saying "positive" in the statement if it
  is read on its own.
- **Where `n ≥ 2` is used:** only in the eigenvector equation (row 1 needs x_1 given by the
  `j < n` formula). The entry formula and positivity of x hold for all n. For n = 1 the matrix is
  (1) while the formula gives 1 + 2cos(2π/5) ≈ 1.618, so `n ≥ 2` is genuinely needed.
- **Strictness is used in exactly one place:** an off-diagonal entry `i < j` could only be locked
  if a_j · a_{j+2} = a_{j+1}² (paper indexing shifted by one), which SLC forbids.
- The constants are those of the paper rewritten: λ^{r−1}·𝟙ᵀx/x_max = (𝟙ᵀx/(λ x_max))·λ^r.
- "Spectral radius" is formalised as: λ is an eigenvalue and every complex eigenvalue has modulus
  ≤ λ. The Gelfand-formula remark in the preceding text is not formalised (not needed: the
  two-sided bound gives V_r^{1/r} → λ directly).

## Not done

Nothing among (A)–(E). Not attempted, because out of scope: wiring the file into
`ExteriorConvex.lean`, and a statement in terms of Mathlib's `spectralRadius`.
