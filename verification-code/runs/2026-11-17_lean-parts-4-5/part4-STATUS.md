# Part IV Lean extension — status (2026-11-17, Claude-Code agent)

Paper: `article/exterior-convex_article4_draft_1.org`. Lean project: `LEAN/` (library `ExteriorConvex`).
Four new files, no existing file edited, nothing committed, `ExteriorConvex.lean` untouched (the
new files are therefore **not yet imported by the library root**; add them there to have them in
`lake build`):

| file | lines | target |
|---|---|---|
| `LEAN/ExteriorConvex/Vertices/CountTransfer.lean` | ~430 | A |
| `LEAN/ExteriorConvex/Facets/Tight.lean` | ~435 | B |
| `LEAN/ExteriorConvex/Vertices/SecondProof.lean` | ~1390 | C (all of it, including the optional part) |
| `LEAN/ExteriorConvex/Facets/Irredundant.lean` | ~565 | D, rank two only |

Each compiles with `lake env lean <file>` under `MemoryMax=7G`, **no errors, no warnings, no `sorry`,
no `native_decide`**. `SecondProof.lean` and `Irredundant.lean` import `Facets/Tight.lean`, so
`Tight`'s olean was built with the targeted `lake build ExteriorConvex.Facets.Tight` (one module,
~20 s). Import order for the root: `Facets.Tight` before `Vertices.SecondProof` and
`Facets.Irredundant`; `Vertices.CountTransfer` needs `Vertices.WorkedCounts` and `Facets.KozBridge`.
(`git status` shows `ExteriorConvex.lean` modified: that is the concurrent ModuleKK run adding its
four `ModuleKK.*` imports, not this run.)

Every headline theorem below was checked with `#print axioms` (lines appended temporarily, then
removed): all show exactly `[propext, Classical.choice, Quot.sound]`, except `lem_tight_edge_one`,
which shows `[propext, Quot.sound]`.

---

## A. Vertex count as a transfer-matrix product — DONE

`ExteriorConvex/Vertices/CountTransfer.lean`, namespace `ExteriorConvex.CountTransfer`. Paper label:
`cor-vertex-count` (now in the draft, lines ~816–863, with `ex-vertex-count`).

Definitions:
- `PairAdm a n δ i j : Prop := (δ = 0 → i = j) ∧ i ≤ δ + j ∧ ¬ Pairwise.Locked a n 0 δ i (δ + j)`
  (thm-vdesc (i)–(iii) for shifts `(0, δ)`); `pairAdm_iff_CF : PairAdm a n δ i j ↔ Pairwise.CF a n (shift2 δ) (choice2 i j) 0`.
- `Mext a n δ : Matrix (Fin n) (Fin n) ℕ := Matrix.of fun i j => if PairAdm a n δ (i+1) (j+1) then 1 else 0` (classical).
- `transferProd a n d k := tprod (fun p => Mext a n (d (p + 1) - d p)) k`, with `tprod T 0 = 1`,
  `tprod T (k+1) = tprod T k * T k`; `transferProd_eq_list_prod` gives the `List.prod` form.

Main results (exact signatures):
```lean
theorem cor_vertex_count (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {r : ℕ} (hr : 1 ≤ r)
    {d : ℕ → ℕ} (hd : Monotone d) (hN : ∀ p < r, d p + n ≤ N) :
    (Set.extremePoints ℝ (∑ p ∈ range r, convexHull ℝ (vsetA a N (d p) n))).ncard =
      (fun _ => 1) ⬝ᵥ (transferProd a n d (r - 1) *ᵥ fun _ => 1)

theorem cor_vertex_count_koz (hn : 1 ≤ n) {r : ℕ} (hr : 1 ≤ r) {d : ℕ → ℕ} (hd : Monotone d)
    (hN : ∀ p < r, d p + n ≤ N) :
    (Set.extremePoints ℝ (convexHull ℝ (ffSet n N (fun i : Fin r => d i)))).ncard =
      (fun _ => 1) ⬝ᵥ (transferProd (kozLeg n) n d (r - 1) *ᵥ fun _ => 1)

theorem Mext_eq_one_iff {N : ℕ} (hpos : ∀ s, 0 < a s) (hlc : Pairwise.WLC a n) {δ : ℕ}
    (hN : δ + n ≤ N) (i j : Fin n) :
    Mext a n δ i j = 1 ↔ ravA a N 0 (i.val + 1) + ravA a N δ (j.val + 1) ∈
        Set.extremePoints ℝ (convexHull ℝ (vsetA a N 0 n) + convexHull ℝ (vsetA a N δ n))

theorem Mext_zero : Mext a n 0 = 1
theorem Mext_all_ones {δ : ℕ} (hδ : n ≤ δ + 1) : Mext a n δ = Matrix.of fun _ _ => 1
theorem locked_translate (dp δ i j : ℕ) :
    Pairwise.Locked a n dp (dp + δ) (dp + i) (dp + δ + j) ↔ Pairwise.Locked a n 0 δ i (δ + j)
theorem CF_iff_pairAdm {d J : ℕ → ℕ} {p : ℕ} (hd : d p ≤ d (p + 1)) :
    Pairwise.CF a n d J p ↔ PairAdm a n (d (p + 1) - d p) (J p) (J (p + 1))
theorem card_paths (R : ℕ → Fin m → Fin m → Prop) [∀ p i j, Decidable (R p i j)] (k : ℕ) :
    #(univ.filter fun K : Fin (k + 1) → Fin m => ∀ p : Fin k, R p (K p.castSucc) (K p.succ)) =
      (fun _ => 1) ⬝ᵥ (tprod (fun p => Matrix.of fun i j => if R p i j then 1 else 0) k *ᵥ fun _ => 1)
theorem transferProd_const (δ k : ℕ) : transferProd a n (fun p => p * δ) k = Mext a n δ ^ k
```
Numeric anchors (kernel `decide` via a decidable `MextN` and `WorkedCounts.cf_cast_iff`;
`Mext_cast : Mext (fun s => (a s : ℝ)) n δ = MextN a n δ`):
```lean
theorem ex_vertex_count_matrix :
    Mext (kozLeg 4) 4 1 = !![1, 1, 1, 1; 1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 1]
theorem ex_vertex_count_row_sums :
    Mext (kozLeg 4) 4 1 *ᵥ (fun _ => 1) = ![4, 3, 2, 2] ∧
      Mext (kozLeg 4) 4 1 ^ 2 *ᵥ (fun _ => 1) = ![11, 8, 5, 4]
theorem ex_vertex_count_rank_two {N : ℕ} (hN : 5 ≤ N) :
    (Set.extremePoints ℝ (∑ p ∈ range 2, convexHull ℝ (vsetA (kozLeg 4) N p 4))).ncard = 11
theorem ex_vertex_count_rank_three {N : ℕ} (hN : 6 ≤ N) :
    (Set.extremePoints ℝ (∑ p ∈ range 3, convexHull ℝ (vsetA (kozLeg 4) N p 4))).ncard = 28
theorem ex_rank3_vertices_direct {N : ℕ} (hN : 6 ≤ N) : … = 28   -- brute force over all 64 tuples, not via the matrix
theorem ex_vertex_count_koz_rank_three :
    (Set.extremePoints ℝ (convexHull ℝ (ffSet 4 6 (fun i : Fin 3 => (i : ℕ))))).ncard = 28
```

Notes / deviations (none of substance):
- Shifts are any `Monotone d : ℕ → ℕ` (the paper's `d_1 = 0` is not needed; only gaps enter).
  Windows are indexed from `0`, so the paper's `δ_p = d_p − d_{p−1}` (`2 ≤ p ≤ r`) is
  `d (p+1) − d p` (`p + 1 < r`) and the product is `transferProd a n d (r − 1)`.
- `r ≥ 1` is needed, as printed: for `r = 0` the polytope is `{0}` (1 vertex) but `𝟙ᵀ I 𝟙 = n`.
- Translation invariance (the proof's first sentence) is proved in window-system form
  (`locked_translate`, `CF_iff_pairAdm`), which is what the count uses.
- `Mext_all_ones` confirms the draft's "all ones for `δ ≥ n − 1`" with **no** hypothesis on `a⃗`
  (`cor-rank2-lc` states "for `d ≥ n`"; `δ = n − 1` is also all ones, both are consistent).

## B. Tightness, the implied row, the value table — DONE

`ExteriorConvex/Facets/Tight.lean`, namespace `ExteriorConvex.Facets`.

`lem-value-table` was **not** present as a standalone statement (the validity proofs use its
multiplied-out sign consequences inline: `window_L`, `window_R` in `ThetaForm.lean`, and inline in
`RankTwo.validity`). It is now:
```lean
theorem value_table (a : ℕ → ℝ) {N : ℕ} (d k c j : ℕ) (hk : 1 ≤ k) (hc : 1 ≤ c) (hcN : c + 1 ≤ N) :
    co (ravA a N d k) (c + 1) / a (j + 1) - co (ravA a N d k) c / a j =
      if d + k < c then 0
      else if c = d + k then -(a (c - d) / a j)
      else Aof a d (c + 1) / a (j + 1) - Aof a d c / a j
noncomputable def Vt (a : ℕ → ℝ) (ℓ j : ℕ) : ℝ := a (ℓ + 1) / a (j + 1) - a ℓ / a j
theorem Vt_nonpos (hpos) (hlc : LogConcaveOn a n) (hj : 1 ≤ j) (hjl : j < ℓ) (hl : ℓ + 1 ≤ n) : Vt a ℓ j ≤ 0
theorem Vt_self (hpos) (j : ℕ) : Vt a j j = 0
theorem Vt_nonneg (hpos) (hlc : LogConcaveOn a n) (hl : 1 ≤ ℓ) (hlj : ℓ < j) (hj : j + 1 ≤ n) : 0 ≤ Vt a ℓ j
```
(`ℓ = c − d` may be `≤ 0`; `k < ℓ` is `d + k < c`, `k = ℓ` is `c = d + k`; `Aof a d c` is the paper's `A_{c−d}`, `a_s = 0` for `s ≤ 0`.)

(i) `thm-hrep2`(1), each row of `Qsys a n d 1` tight on `R2 a n d := angle a (n+d) 0 n + angle a (n+d) d n`:
```lean
theorem thm_hrep2_tight (hd : 1 ≤ d) (hdn : d < n) :
    (∀ j, 1 ≤ j → j < n → ∃ x ∈ R2 a n d,
        (co x (j + 1) - Aof a d (j + 1)) * a j = (co x j - Aof a d j) * a (j + 1)) ∧
      (∀ j, 1 ≤ j → j < n → ∃ x ∈ R2 a n d, co x (d + j + 1) * a j = co x (d + j) * a (j + 1)) ∧
      (∃ x ∈ R2 a n d, a 1 = co x (d + 1)) ∧
      (∃ x ∈ R2 a n d, co x (n + 1) = a (n - d + 1)) ∧
      (∃ x ∈ R2 a n d, 0 = co x (n + d))
```
(components `tight_Ch1`, `tight_Ch2`, `tight_C`, `tight_D`, `tight_F`; witnesses `v_n + shift^d v_n`,
`v_1 + shift^d v_n`, `v_1 + shift^d v_1`). "Valid and tight", i.e. the bound is the support value:
`support_Ch1 … : IsGreatest ((fun x => co x (j+1) * a j - co x j * a (j+1)) '' R2 a n d)
(Aof a d (j+1) * a j - Aof a d j * a (j+1))`, and likewise `support_Ch2` (`IsGreatest … 0`),
`support_C` (`IsLeast (co · (d+1)) (a 1)`), `support_D` (`IsGreatest (co · (n+1)) (a (n-d+1))`),
`support_F` (`IsLeast (co · (n+d)) 0`), each under `hpos`, `LogConcaveOn a n`, `1 ≤ d < n`.

(ii) `thm-hrep2`(2), first clause:
```lean
theorem thm_hrep2_ch2_one_implied (hpos : ∀ s, 0 < a s) (hlc : LogConcaveOn a n) (hd : 1 ≤ d)
    (hdn : d < n) {x : Fin (n + d) → ℝ} (hx : x ∈ Qsys a n d 2) :
    co x (d + 1 + 1) * a 1 ≤ co x (d + 1) * a (1 + 1)
```
(`completeness` then `validity`, as the paper says.)

(iii) `thm-theta`, each row tight on `Rsum a N n d lam r`:
```lean
theorem thm_theta_tight (hn : 2 ≤ n) (hd : Incr d r) (hN : d (r - 1) + n ≤ N) :
    (∀ p j, p < r → 1 ≤ j → j < n → ∃ x ∈ Rsum a N n d lam r,
        (co x (d p + j + 1) - roof a n d lam r p (d p + j + 1)) * a j =
          (co x (d p + j) - roof a n d lam r p (d p + j)) * a (j + 1)) ∧
      (∀ p, p + 1 < r → ∃ x ∈ Rsum a N n d lam r, lam (p + 1) * a 1 = co x (d (p + 1) + 1)) ∧
      (∀ p, p + 1 < r → ∃ x ∈ Rsum a N n d lam r,
        co x (d p + n + 1) = roof a n d lam r p (d p + n + 1)) ∧
      (∃ x ∈ Rsum a N n d lam r, 0 = co x (d (r - 1) + n))
```
(components `tightB_I`, `tightB_C`, `tightB_D`, `tightB_F`), and the support-value forms
`supportB_I` (rows of the system: `j ≥ 1` for `p = 0`, `j ≥ 2` for `p ≥ 1`), `supportB_C`,
`supportB_D`, `supportB_F`, under `hpos`, `LogConcaveOn a n`, `Incr d r`, `d (r−1) + n ≤ N`,
`∀ p, 0 ≤ lam p` (and `1 ≤ n` / `2 ≤ n`, `1 ≤ r` where needed).

Notes:
- Tightness as attainment needs **no log-concavity, no positivity, no gap bound and no sign on the
  weights**; only the support-value (`IsGreatest`) forms use validity and hence the paper's hypotheses.
- `(F)` needs `n ≥ 2` (for `n = 1`, `x_N = λ_r a_1 > 0` on all of `R`). This is the facet section's
  standing assumption, so not a finding against the paper; recorded in the docstrings.
- `(I; p)` is proved tight for every `1 ≤ j < n`, which includes the system's rows.

## C. The second proof — DONE (core and the optional part), plus the assembled second proof

`ExteriorConvex/Vertices/SecondProof.lean`, namespace `ExteriorConvex.SecondProof`.

```lean
def TightAt (R : Set (Fin N → ℝ)) (x u : Fin N → ℝ) : Prop := ∀ y ∈ R, u ⬝ᵥ y ≤ u ⬝ᵥ x
noncomputable def certFun (R) (x) (U : Finset (Fin N → ℝ)) := ∑ u ∈ U.filter (TightAt R x), u

theorem lem_certificate {ι : Type*} [DecidableEq ι] (s : Finset ι) (P : ι → Set (Fin N → ℝ))
    (xp : ι → Fin N → ℝ) (hxp : ∀ p ∈ s, xp p ∈ P p) (e : Fin N → ℝ)
    (he : ∀ y ∈ ∑ p ∈ s, P p, e ⬝ᵥ y = e ⬝ᵥ ∑ p ∈ s, xp p) (U : Finset (Fin N → ℝ))
    (hspan : Submodule.span ℝ
      (insert e (U.filter (TightAt (∑ p ∈ s, P p) (∑ p ∈ s, xp p)) : Set (Fin N → ℝ))) = ⊤) :
    (∀ y ∈ ∑ p ∈ s, P p, y ≠ ∑ p ∈ s, xp p → certFun … U ⬝ᵥ y < certFun … U ⬝ᵥ ∑ p ∈ s, xp p) ∧
      (∀ p ∈ s, ∀ z ∈ P p, z ≠ xp p → certFun … U ⬝ᵥ z < certFun … U ⬝ᵥ xp p) ∧
      ∑ p ∈ s, xp p ∈ Set.extremePoints ℝ (∑ p ∈ s, P p)
```
(`lem_certificate_e1`: the printed form with `e = Pi.single 0 1` and `y 0` constant on `R`.)

```lean
def IsAnchorAt (v : Fin N → ℝ) (c : ℕ) : Prop := 1 ≤ c ∧ c ≤ N ∧ co v c ≠ 0 ∧ ∀ c', c' ≠ c → co v c' = 0
def IsLinkAt (v : Fin N → ℝ) (c : ℕ) : Prop :=
  1 ≤ c ∧ c + 1 ≤ N ∧ co v c ≠ 0 ∧ co v (c + 1) ≠ 0 ∧ ∀ c', c' ≠ c → c' ≠ c + 1 → co v c' = 0
def Edge S c := ∃ v ∈ S, IsLinkAt v c
def Joined S s c := s ≤ c ∧ ∀ e, s ≤ e → e < c → Edge S e
def IsStart S s := 1 ≤ s ∧ s ≤ N ∧ ¬ Edge S (s - 1)
def Anchored S s := ∃ c, Joined S s c ∧ ((∃ v ∈ S, IsAnchorAt v c) ∨
    ∃ v ∈ S, ∃ w ∈ S, IsLinkAt v c ∧ IsLinkAt w c ∧ LinearIndependent ℝ ![v, w])
def freeStarts S := (Finset.Icc 1 N).filter fun s => IsStart S s ∧ ¬ Anchored S s

theorem lem_path_rank (hS : ∀ v ∈ S, (∃ c, IsAnchorAt v c) ∨ ∃ c, IsLinkAt v c) :
    Module.finrank ℝ (Submodule.span ℝ (S : Set (Fin N → ℝ))) = N - (freeStarts S).card
```
(Components of `G` are indexed by their first coordinates; proof on the annihilator, `ker_equiv_bijective`.)

Optional part (`lem-tight`, `lem-tight-edge`, `prop-certified-span`), with
`RAsum a N n d r = ∑ p ∈ range r, convexHull ℝ (vsetA a N (d p) n)`, `xJ a N d r J = ∑ p ∈ range r, ravA a N (d p) (J p)`,
`linkU a N e c` (= `e_{c+1}/a_{c+1−e} − e_c/a_{c−e}`), `eVec N c` (= `e_c`):
```lean
theorem tightAt_iff (hJ : ∀ p < r, 1 ≤ J p ∧ J p ≤ n) (u : Fin N → ℝ) :
    TightAt (RAsum a N n d r) (xJ a N d r J) u ↔
      ∀ q < r, ∀ k, 1 ≤ k → k ≤ n → u ⬝ᵥ ravA a N (d q) k ≤ u ⬝ᵥ ravA a N (d q) (J q)
theorem lem_tight_link (hpos) (hlc : LogConcaveOn a n) (hd : Incr d r) (hN : d (r - 1) + n ≤ N) (hJ)
    (hp : p < r) (hc1 : d p + 1 ≤ c) (hc2 : c + 1 ≤ d p + n) (hm : d p + J p ≠ c)
    (hlt : ∀ q < p, d q + J q ≤ c - 1) (hgt : ∀ q, p < q → q < r → c + 1 ≤ d q + J q) :
    TightAt (RAsum a N n d r) (xJ a N d r J) (linkU a N (d p) c)
theorem lem_tight_C (hpos) (hd) (hN) (hJ) (hp0 : 0 < p) (hp : p < r) :
    TightAt … (-eVec N (d p + 1)) ↔ ∀ q < p, d q + J q ≤ d p
theorem lem_tight_D (hpos) (hd) (hN) (hJ) (hp0 : 0 < p) (hp : p < r) :
    TightAt … (eVec N (d (p - 1) + n + 1)) ↔ ∀ q, p ≤ q → q < r → d (p - 1) + n + 1 ≤ d q + J q
theorem lem_tight_F (hpos) (hd) (hr : 1 ≤ r) (hn : 2 ≤ n) (hN : d (r - 1) + n = N) (hJ) :
    TightAt … (-eVec N N) ↔ d (r - 1) + J (r - 1) ≤ N - 1
theorem lem_tight_edge_one (hc1 : 1 ≤ c) (hc : ∃ q < r, d q + J q = c) : ∀ p < r, ¬ CertLink d J r p c
theorem lem_tight_edge_two (h0 : d 0 = 0) (hmono : MonoM d J r) (hJ) (hc1 : 1 ≤ c)
    (hc : ∀ q < r, d q + J q ≠ c) (hp : p < r) :
    CertLink d J r p c ∧ InList n d p c ↔
      (p + 1 = cnt d J r c ∧ c + 1 ≤ d p + n) ∨ (p = cnt d J r c ∧ (p = 0 ∨ d p + 2 ≤ c))
theorem prop_certified_span (hpos) (h0 : d 0 = 0) (hr : 1 ≤ r) (hd : Incr d r) (hg : Gaps n d r)
    (hN : d (r - 1) + n = N) (hJ) (hmono : MonoM d J r)
    (hlock : ∀ p, p + 1 < r →
      ¬ Pairwise.Locked a n (d p) (d (p + 1)) (d p + J p) (d (p + 1) + J (p + 1))) :
    Submodule.span ℝ (insert (eVec N 1) (certSet a N n d J r) : Set (Fin N → ℝ)) = ⊤
theorem second_proof_vertex (hpos) (hlc : LogConcaveOn a n) (h0) (hr) (hd) (hg) (hN) (hJ) (hmono) (hlock) :
    (…φ uniquely maximised on R at x(𝐣)…) ∧ (…and on every summand at its chosen vertex…) ∧
      xJ a N d r J ∈ Set.extremePoints ℝ (RAsum a N n d r)
```
(`CertLink d J r p c := m_p ≠ c ∧ (∀ q < p, m_q ≤ c − 1) ∧ ∀ q, p < q → q < r → c + 1 ≤ m_q`;
`InList n d p c := d p + 1 ≤ c ∧ c + 1 ≤ d p + n ∧ (0 < p → d p + 2 ≤ c)`;
`cnt d J r c = #{q < r : m_q < c}`; `certSet` = certified links of the list ∪ certified anchors.)

**Findings / deviations in C:**
1. **`lem-tight`(4) is false for `n = 1`** (minor edge case). The second-proof section has no
   standing `n ≥ 2`; with `n = 1` the gap bound forces `r = 1`, `R` is the point `a_1 e_1`, `u^F = −e_N`
   is tight, but `m_r = 1 = N`, so "tight iff `m_r ≤ N − 1`" fails. `lem_tight_F` assumes `2 ≤ n`.
   Suggested fix: add "`n ≥ 2`" to the section's standing assumptions (the facet section already has it).
2. `lem-certificate` is proved for arbitrary sets `P_p`, points `x^(p) ∈ P_p` and any `e` with `e·y`
   constant on `R` (generalisation; the printed `e_1` form is `lem_certificate_e1`).
3. `lem-tight`(1) is proved for every link with `c, c+1 ∈ W_p` (the list restricts `c ≥ d_p + 2` for
   `p ≥ 2`); no part of `lem-tight` uses the gap bound or `d_1 = 0`.
4. `lem-tight-edge`(2) needs `d_1 = 0` for the clause "`u(k+1; c)` is in the list iff `k = 0` or …"
   when `k = 0` (the paper has `d_1 = 0` standing, so not a finding).
5. `prop-certified-span`'s hypothesis is stated as `¬ Pairwise.Locked` for each consecutive pair,
   which is literally the printed condition. Log-concavity is not used by the proposition (only by
   `lem-tight`).
6. `second_proof_vertex` assembles the paper's "Second proof of sufficiency in thm-vdesc" for the
   reduced case (distinct shifts, gaps ≤ n − 1). The reduction of ties and of gaps ≥ n is not
   formalised (the first proof, `vertex_iff_CF`, needs neither).

## D. Irredundancy, witness form (stretch) — `thm-hrep2`(3) DONE; `thm-theta` NOT ATTEMPTED

`ExteriorConvex/Facets/Irredundant.lean`, namespace `ExteriorConvex.Facets`.

The rows are encoded as `inductive Row2 | ch1 (j) | ch2 (j) | C | D | F` with `Row2.Holds a n d x`
(the multiplied-out rows of `Qsys`) and `Row2.InSys n` (`ch1 j`: `1 ≤ j < n`; `ch2 j`: `2 ≤ j < n`;
`C`, `D`, `F`: always), i.e. exactly the `2n` rows of the system without `(Ch2; 1)`;
`mem_Qsys_two_iff : x ∈ Qsys a n d 2 ↔ co x 1 = a 1 ∧ ∀ ρ, ρ.InSys n → ρ.Holds a n d x`.
```lean
theorem thm_hrep2_irredundant (hpos : ∀ s, 0 < a s) (hslc : Pairwise.SLC a n) (hd : 1 ≤ d)
    (hdn : d < n) (ρ : Row2) (hρ : ρ.InSys n) :
    ∃ x : Fin (n + d) → ℝ, co x 1 = a 1 ∧ (∀ σ : Row2, σ.InSys n → σ ≠ ρ → σ.Holds a n d x) ∧
      ¬ ρ.Holds a n d x
```
`#print axioms`: `[propext, Classical.choice, Quot.sound]`.

Witnesses: a sum of two summand vertices `y` (which satisfies every row by `validity`) moved in one
coordinate (`witness_of`): `(Ch1; j ≤ d)`: `T + e_{j+1}`; `(Ch1; j ≥ d+1)`:
`T + δ e_{j+1}`, `δ a_{j−d} = a_j a_{j−d+1} − a_{j+1} a_{j−d}`; `(Ch2; j)`, `d+j+1 ≤ n`:
`v_d + shift^d v_j − (a_{j+1} a_{d+j}/a_{d+j+1}) e_{d+j}`; `(Ch2; j)`, `d+j ≥ n`:
`v_1 + shift^d v_n − e_{d+j}`; `(C)`: `v_d + shift^d v_1 − (a_2 a_{d+1}/a_{d+2}) e_{d+1}`; `(D)`:
`T + (a_n a_{m+1}/a_m) e_{n+1}`; `(F)`: `v_1 + shift^d v_1 − e_N` (`T = v_n + shift^d v_n`).
Strict log-concavity (`Pairwise.SLC`, globalised as `slc_glob`) is used exactly for `(Ch1; j)`,
`j ≥ d + 1`, and `(Ch2; j)`, `d + j + 1 ≤ n` — the pairs of rows on one edge that coincide on a
plateau, as the paper says. The facet *count* `2n` and "pairwise distinct facets" (dimension
statements) are not formalised, as instructed.

**`thm-theta` irredundancy: not attempted.** Reason (for whoever picks it up): the one-coordinate
scheme that works at rank two does not carry over. For a row `(I; p)` on an edge `c` that also lies
in windows `p − 1` and `p + 1`, no single sum of vertices is tight for `(I; p)` and slack for both
`(I; p−1)` and `(I; p+1)` on the same edge: slackness of the former needs `m_p ≤ c − 1`, of the
latter `m_p ≥ c + 1` (from `lem-tight`'s argmax sets under strict log-concavity). A witness needs
the midpoint of two vertex sums as base point, and explicit weighted slacks for every row reading
the moved coordinate, including the `(D; q)` anchors. That is a separate, larger job.

## Summary of findings

1. `lem-tight`(4) fails for `n = 1` (then `r = 1`, `R` a point, `u^F` tight but `m_r = N`); add
   `n ≥ 2` to the second-proof section's standing assumptions. (`lem_tight_F` assumes it.)
2. No other printed statement needed an unstated hypothesis. Several were proved with fewer
   hypotheses than printed (tightness without log-concavity; `lem-tight` without the gap bound;
   `lem-certificate` for arbitrary sets; `cor-vertex-count` without `d_1 = 0`;
   `E(a⃗; δ)` all ones for `δ ≥ n − 1` without any hypothesis on `a⃗`).
3. `lem-value-table` was not previously in the library as a statement (only its sign consequences,
   inside `window_L`/`window_R`/`validity`); it now is (`value_table`, `Vt_*`).
4. `README.md`'s Part IV table can now point `lem-certificate`, `lem-path-rank`, `lem-tight`,
   `lem-tight-edge`, `prop-certified-span`, `lem-value-table`, `cor-vertex-count`, and
   `thm-hrep2`(1) tightness / (2) first clause / (3) irredundancy at the declarations above (not
   edited here, per instructions).
