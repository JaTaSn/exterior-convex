/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Article 3: the consecutive pairwise reduction for weakly log-concave leg vectors

Formalisation of `working-notes/kozlov-pairwise-reduction-direct-2026-10-20.org` (reviewed in
`working-notes/review-pairwise-direct-2026-10-20.org`), in the *window-system* form: no polytopes,
only finite sums.  `RankR.lean` carries the result over to extreme points of `RA(a; d⃗)`.

## Set-up

A leg vector `a : ℕ → ℝ`, positive on `[1,n]` (`Pos`), weakly log-concave in the cross-multiplied,
division-free form `a i · a (i+2) ≤ a (i+1)²` for `1 ≤ i`, `i+2 ≤ n` (`WLC`; this is the note's
`a(i)² ≥ a(i−1)a(i+1)`, `2 ≤ i ≤ n−1`, with `i` shifted by one).  Summands are indexed by `p : ℕ`
(only `p < r` matters), with shift `d p` and choice `j p ∈ [1,n]`.  `Expose a n d j φ` says that the
value sequence `F(l) = ∑_{i ∈ [1,l]} a i · φ (d + i)` has its strict maximum over `l ∈ [1,n]` at
`l = j`; `Feasible a n d j S` says that one `φ : ℕ → ℝ` does this for every summand in `S`.

## Correspondence with the note

| note | here |
|---|---|
| vertex criterion, (L_p)/(R_p) | `expose_iff` (`LCond`, `RCond`, global coordinates, chosen point `m = d + j`) |
| Lemma 1 (ratios) | `lc_cross`, `lc_glob` (cross-multiplied, no division) |
| Lemma 2(a), 2(b) (Abel, two signs) | `abel_prefix`/`abel_prefix_neg`, `abel_suffix`/`abel_suffix_pos` |
| Lemma 5 (domination), the two directions | `transfer_prefix`, `transfer_suffix` |
| Lemma 3 (chosen points non-decreasing) | `chosen_mono` |
| Lemma 6 (gluing) | `glue_step` + `glued` — see the remark below |
| Theorem 1 (1 ⟺ 3) | `pairwise_reduction`, `feasible_iff_consecutive` |
| Lemma 4 (locked step fatal) | `locked_infeasible` |
| Theorem 2 (explicit V-description) | `feasible_iff_CF`; the rank-two sufficiency (Cases A/B/C) is `pair_feasible_of_CF` |
| Corollary (strictly log-concave / Kozlov) | `locked_iff_unit`, `CF_iff_KozCond` |

**Remark on the proof route (a simplification found while formalising).**  The note glues gadgets
on the gaps between *distinct* chosen points after a tie reduction to distinct shifts.  Here the
gluing is done by induction on the number of summands instead: if `φ'` exposes summands `0..q` and
`ψ` exposes the pair `(q, q+1)`, then `φ = φ'` on `[.., m q]` and `φ = ψ` on `(m q, ..]` exposes
`0..q+1` (`glue_step`).  The two estimates needed are exactly the note's Lemma 5, applied with the
junction pair `(q, q+1)` against an earlier window `p ≤ q` (Abel 2(a)) and against the new window
`q+1` (Abel 2(b)); both hold verbatim for *weakly* sorted shifts, so **no tie reduction is needed**,
and the tie clause of Lemma 3 is not used by Theorem 1 at all.  The resulting functional is the
note's glued functional (on each gap `(m q, m (q+1)]` it is the junction witness).

**Finding.**  Theorem 2's condition (i) is implied by (ii) and (iii): if `d p = d (p+1)` and
`m p < m (p+1)`, the step is automatically locked (ratio `≡ 1`, both points in the common window).
See `tie_of_not_locked`.

Index conventions: global coordinates are natural numbers `c`, window `p` occupies
`[d p + 1, d p + n]`; sums are over `Finset.Ioc`.
-/
import Mathlib

namespace ExteriorConvex.Pairwise

open Finset

/-! ## Definitions -/

/-- Positivity of the leg vector on `[1,n]`. -/
def Pos (a : ℕ → ℝ) (n : ℕ) : Prop := ∀ i, 1 ≤ i → i ≤ n → 0 < a i

/-- Weak log-concavity, cross-multiplied: `a i · a (i+2) ≤ a (i+1)²` for `1 ≤ i ≤ n − 2`. -/
def WLC (a : ℕ → ℝ) (n : ℕ) : Prop := ∀ i, 1 ≤ i → i + 2 ≤ n → a i * a (i + 2) ≤ a (i + 1) ^ 2

/-- Summand `(d, j)` has its strict maximum at `j`: the local form of the vertex criterion. -/
def Expose (a : ℕ → ℝ) (n d j : ℕ) (φ : ℕ → ℝ) : Prop :=
  ∀ l, 1 ≤ l → l ≤ n → l ≠ j →
    ∑ i ∈ Icc 1 l, a i * φ (d + i) < ∑ i ∈ Icc 1 j, a i * φ (d + i)

/-- One functional exposes every summand in `S` at its chosen vertex. -/
def Feasible (a : ℕ → ℝ) (n : ℕ) (d j : ℕ → ℕ) (S : Finset ℕ) : Prop :=
  ∃ φ : ℕ → ℝ, ∀ p ∈ S, Expose a n (d p) (j p) φ

/-- (R): the after-peak prefix sums of the window with shift `d` and chosen point `m` are
negative. -/
def RCond (a : ℕ → ℝ) (n d m : ℕ) (φ : ℕ → ℝ) : Prop :=
  ∀ y, m < y → y ≤ d + n → ∑ c ∈ Ioc m y, a (c - d) * φ c < 0

/-- (L): the before-peak suffix sums are positive.  `Ioc x m` is the note's `[x+1, m]`, so the
lower limit `x ≥ d + 1` is the note's `x ≥ d + 2`: a window never constrains its first
coordinate. -/
def LCond (a : ℕ → ℝ) (d m : ℕ) (φ : ℕ → ℝ) : Prop :=
  ∀ x, d + 1 ≤ x → x < m → 0 < ∑ c ∈ Ioc x m, a (c - d) * φ c

/-! ## The vertex criterion in global coordinates -/

lemma sum_shift (a : ℕ → ℝ) (d s t : ℕ) (φ : ℕ → ℝ) :
    ∑ i ∈ Ioc s t, a i * φ (d + i) = ∑ c ∈ Ioc (d + s) (d + t), a (c - d) * φ c := by
  rw [← map_add_left_Ioc, sum_map]
  simp

lemma Icc_one_eq (l : ℕ) : Icc 1 l = Ioc 0 l := by
  ext x; simp only [mem_Icc, mem_Ioc]; omega

/-- **The vertex criterion, (L)/(R) form** (note §1, *Derivation*). -/
theorem expose_iff (a : ℕ → ℝ) (n : ℕ) {d j : ℕ} (φ : ℕ → ℝ) (hjn : j ≤ n) :
    Expose a n d j φ ↔ RCond a n d (d + j) φ ∧ LCond a d (d + j) φ := by
  have key : ∀ s t, s ≤ t → ∑ i ∈ Icc 1 t, a i * φ (d + i)
      = ∑ i ∈ Icc 1 s, a i * φ (d + i) + ∑ c ∈ Ioc (d + s) (d + t), a (c - d) * φ c := by
    intro s t hst
    rw [Icc_one_eq, Icc_one_eq, ← sum_shift, sum_Ioc_consecutive _ (Nat.zero_le s) hst]
  constructor
  · intro h
    refine ⟨fun y hy hyn => ?_, fun x hx hxm => ?_⟩
    · obtain ⟨l, rfl⟩ : ∃ l, y = d + l := ⟨y - d, by omega⟩
      have := h l (by omega) (by omega) (by omega)
      rw [key j l (by omega)] at this
      linarith
    · obtain ⟨l, rfl⟩ : ∃ l, x = d + l := ⟨x - d, by omega⟩
      have := h l (by omega) (by omega) (by omega)
      rw [key l j (by omega)] at this
      linarith
  · rintro ⟨hR, hL⟩ l hl hln hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · rw [key l j hlt.le]
      have := hL (d + l) (by omega) (by omega)
      linarith
    · rw [key j l hgt.le]
      have := hR (d + l) (by omega) (by omega)
      linarith

/-! ## Lemma 2: Abel summation, two signs -/

/-- Lemma 2(a), non-strict core: with non-positive prefix sums and `ρ` weakly decreasing, the
weighted sum is at most `ρ t` times the plain one. -/
lemma abel_prefix (z ρ : ℕ → ℝ) (s : ℕ) :
    ∀ t, s ≤ t → (∀ l, s < l → l ≤ t → ∑ c ∈ Ioc s l, z c ≤ 0) →
      (∀ c, s < c → c < t → ρ (c + 1) ≤ ρ c) →
      ∑ c ∈ Ioc s t, ρ c * z c ≤ ρ t * ∑ c ∈ Ioc s t, z c := by
  intro t
  induction t with
  | zero =>
      intro h _ _
      obtain rfl : s = 0 := by omega
      simp
  | succ t ih =>
      intro hst hB hρ
      rcases Nat.eq_or_lt_of_le hst with h | h
      · subst h; simp
      · have hst' : s ≤ t := by omega
        rw [sum_Ioc_succ_top hst', sum_Ioc_succ_top hst']
        have h1 := ih hst' (fun l h1 h2 => hB l h1 (by omega)) (fun c h1 h2 => hρ c h1 (by omega))
        have h2 : ρ t * ∑ c ∈ Ioc s t, z c ≤ ρ (t + 1) * ∑ c ∈ Ioc s t, z c := by
          rcases Nat.eq_or_lt_of_le hst' with h3 | h3
          · subst h3; simp
          · have hB' := hB t h3 (by omega)
            have hρ' := hρ t h3 (by omega)
            nlinarith
        rw [mul_add]
        linarith

/-- **Lemma 2(a).** -/
lemma abel_prefix_neg (z ρ : ℕ → ℝ) {s t : ℕ} (hst : s < t)
    (hB : ∀ l, s < l → l ≤ t → ∑ c ∈ Ioc s l, z c < 0)
    (hρ : ∀ c, s < c → c < t → ρ (c + 1) ≤ ρ c) (hpos : 0 < ρ t) :
    ∑ c ∈ Ioc s t, ρ c * z c < 0 := by
  have h1 := abel_prefix z ρ s t hst.le (fun l h1 h2 => (hB l h1 h2).le) hρ
  have h2 := mul_neg_of_pos_of_neg hpos (hB t hst le_rfl)
  linarith

lemma sum_Ioc_bot (f : ℕ → ℝ) {s e : ℕ} (h : s < e) :
    ∑ c ∈ Ioc s e, f c = f (s + 1) + ∑ c ∈ Ioc (s + 1) e, f c := by
  rw [← sum_Ioc_consecutive f (Nat.le_succ s) h]
  simp

/-- Lemma 2(b), non-strict core, by induction on the length `k` of the range. -/
lemma abel_suffix (z ρ : ℕ → ℝ) (e : ℕ) :
    ∀ k s, s + k = e → (∀ l, s ≤ l → l < e → 0 ≤ ∑ c ∈ Ioc l e, z c) →
      (∀ c, s < c → c < e → ρ c ≤ ρ (c + 1)) →
      ρ (s + 1) * ∑ c ∈ Ioc s e, z c ≤ ∑ c ∈ Ioc s e, ρ c * z c := by
  intro k
  induction k with
  | zero => intro s hs _ _; subst hs; simp
  | succ k ih =>
      intro s hs hS hρ
      have hse : s < e := by omega
      rw [sum_Ioc_bot _ hse, sum_Ioc_bot (fun c => ρ c * z c) hse]
      have h1 := ih (s + 1) (by omega) (fun l h1 h2 => hS l (by omega) h2)
        (fun c h1 h2 => hρ c (by omega) h2)
      have h2 : ρ (s + 1) * ∑ c ∈ Ioc (s + 1) e, z c ≤ ρ (s + 1 + 1) * ∑ c ∈ Ioc (s + 1) e, z c := by
        rcases Nat.eq_or_lt_of_le (show s + 1 ≤ e by omega) with h3 | h3
        · rw [← h3]; simp
        · have hS' := hS (s + 1) (by omega) h3
          have hρ' := hρ (s + 1) (by omega) h3
          nlinarith
      rw [mul_add]
      linarith

/-- **Lemma 2(b).** -/
lemma abel_suffix_pos (z ρ : ℕ → ℝ) {s e : ℕ} (hse : s < e)
    (hS : ∀ l, s ≤ l → l < e → 0 < ∑ c ∈ Ioc l e, z c)
    (hρ : ∀ c, s < c → c < e → ρ c ≤ ρ (c + 1)) (hpos : 0 < ρ (s + 1)) :
    0 < ∑ c ∈ Ioc s e, ρ c * z c := by
  have h1 := abel_suffix z ρ e (e - s) s (by omega) (fun l h1 h2 => (hS l h1 h2).le) hρ
  have h2 := mul_pos hpos (hS s le_rfl hse)
  linarith

/-! ## Lemma 1: ratios -/

variable {a : ℕ → ℝ} {n : ℕ}

/-- **Lemma 1**, cross-multiplied: `a(u+1+h)/a(u+1) ≤ a(u+h)/a(u)`. -/
lemma lc_cross (hpos : Pos a n) (hlc : WLC a n) :
    ∀ h u, 1 ≤ u → u + 1 + h ≤ n → a (u + 1 + h) * a u ≤ a (u + h) * a (u + 1) := by
  intro h
  induction h with
  | zero => intro u _ _; simp [mul_comm]
  | succ h ih =>
      intro u hu hun
      have hIH := ih u hu (by omega)
      have hLC := hlc (u + h) (by omega) (by omega)
      have hA0 : 0 < a (u + h) := hpos _ (by omega) (by omega)
      have hA1 : 0 < a (u + h + 1) := hpos _ (by omega) (by omega)
      have hu0 : 0 < a u := hpos _ hu (by omega)
      have e1 : u + 1 + (h + 1) = u + h + 2 := by omega
      have e2 : u + (h + 1) = u + h + 1 := by omega
      have e3 : u + 1 + h = u + h + 1 := by omega
      rw [e1, e2]
      rw [e3] at hIH
      have hA : a (u + h) * (a (u + h + 2) * a u) ≤ a (u + h) * (a (u + h + 1) * a (u + 1)) := by
        nlinarith [mul_le_mul_of_nonneg_right hLC hu0.le,
          mul_le_mul_of_nonneg_left hIH hA1.le]
      exact le_of_mul_le_mul_left hA hA0

/-- **Lemma 1** in global coordinates: for shifts `e ≤ d`, the ratio
`c ↦ a(c−e)/a(c−d)` weakly decreases from `c` to `c+1`, cross-multiplied. -/
lemma lc_glob (hpos : Pos a n) (hlc : WLC a n) {e d c : ℕ} (hed : e ≤ d) (hc : d + 1 ≤ c)
    (hcn : c + 1 - e ≤ n) : a (c + 1 - e) * a (c - d) ≤ a (c - e) * a (c + 1 - d) := by
  have := lc_cross hpos hlc (d - e) (c - d) (by omega) (by omega)
  have e1 : c - d + 1 + (d - e) = c + 1 - e := by omega
  have e2 : c - d + (d - e) = c - e := by omega
  have e3 : c - d + 1 = c + 1 - d := by omega
  rwa [e1, e2, e3] at this

/-! ## Lemma 5: the junction pair dominates (both directions) -/

/-- **Lemma 5, (E) direction / Lemma 3's estimate.**  If the window with the *larger* shift `dq`
has negative after-peak prefix sums on `(m, y]`, so does any window with smaller shift `dp`, as long
as `y` stays in the latter's window. -/
lemma transfer_prefix (hpos : Pos a n) (hlc : WLC a n) {dp dq m y : ℕ} {φ : ℕ → ℝ}
    (hd : dp ≤ dq) (hm : dq + 1 ≤ m) (hmy : m < y) (hy : y ≤ dp + n)
    (hR : ∀ l, m < l → l ≤ y → ∑ c ∈ Ioc m l, a (c - dq) * φ c < 0) :
    ∑ c ∈ Ioc m y, a (c - dp) * φ c < 0 := by
  have key := abel_prefix_neg (fun c => a (c - dq) * φ c) (fun c => a (c - dp) / a (c - dq)) hmy hR
    (fun c h1 h2 => by
      rw [div_le_div_iff₀ (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega))]
      exact lc_glob hpos hlc hd (c := c) (by omega) (by omega))
    (div_pos (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega)))
  have eq : ∑ c ∈ Ioc m y, a (c - dp) / a (c - dq) * (a (c - dq) * φ c)
      = ∑ c ∈ Ioc m y, a (c - dp) * φ c := by
    refine sum_congr rfl fun c hc => ?_
    rw [mem_Ioc] at hc
    have : a (c - dq) ≠ 0 := (hpos _ (by omega) (by omega)).ne'
    field_simp
  rw [← eq]
  exact key

/-- **Lemma 5, (Λ) direction.**  If the window with the *smaller* shift `e` has positive
before-peak suffix sums on `(l, M]` for every `l ∈ [x, M)`, so does any window with larger shift `d`
whose constrained range contains `x`. -/
lemma transfer_suffix (hpos : Pos a n) (hlc : WLC a n) {e d x M : ℕ} {φ : ℕ → ℝ}
    (hed : e ≤ d) (hx : d + 1 ≤ x) (hxM : x < M) (hM : M ≤ e + n)
    (hL : ∀ l, x ≤ l → l < M → 0 < ∑ c ∈ Ioc l M, a (c - e) * φ c) :
    0 < ∑ c ∈ Ioc x M, a (c - d) * φ c := by
  have key := abel_suffix_pos (fun c => a (c - e) * φ c) (fun c => a (c - d) / a (c - e)) hxM hL
    (fun c h1 h2 => by
      rw [div_le_div_iff₀ (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega))]
      have := lc_glob hpos hlc hed (c := c) (by omega) (by omega)
      linarith [mul_comm (a (c + 1 - e)) (a (c - d)), mul_comm (a (c - e)) (a (c + 1 - d))])
    (div_pos (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega)))
  have eq : ∑ c ∈ Ioc x M, a (c - d) / a (c - e) * (a (c - e) * φ c)
      = ∑ c ∈ Ioc x M, a (c - d) * φ c := by
    refine sum_congr rfl fun c hc => ?_
    rw [mem_Ioc] at hc
    have : a (c - e) ≠ 0 := (hpos _ (by omega) (by omega)).ne'
    field_simp
  rw [← eq]
  exact key

/-! ## Lemma 3: chosen points are non-decreasing -/

/-- **Lemma 3.**  If one functional satisfies (R) for the later summand `q` and (L) for the earlier
summand `p` (shifts `dp ≤ dq`, ties allowed), then the chosen points satisfy `mp ≤ mq`. -/
theorem chosen_mono (hpos : Pos a n) (hlc : WLC a n) {dp dq mp mq : ℕ} {φ : ℕ → ℝ}
    (hd : dp ≤ dq) (hmq : dq + 1 ≤ mq) (hmp : mp ≤ dp + n)
    (hR : RCond a n dq mq φ) (hL : LCond a dp mp φ) : mp ≤ mq := by
  by_contra hlt
  rw [not_le] at hlt
  have h1 := hL mq (by omega) hlt
  have h2 := transfer_prefix hpos hlc hd hmq hlt hmp (fun l h1 h2 => hR l h1 (by omega))
  linarith

/-- **Lemma 3, tie clause.**  Equal shifts force equal chosen points. -/
theorem chosen_eq_of_tie (hpos : Pos a n) (hlc : WLC a n) {dp mp mq : ℕ} {φ : ℕ → ℝ}
    (hmp : dp + 1 ≤ mp) (hmp' : mp ≤ dp + n) (hmq : dp + 1 ≤ mq) (hmq' : mq ≤ dp + n)
    (hRp : RCond a n dp mp φ) (hLp : LCond a dp mp φ)
    (hRq : RCond a n dp mq φ) (hLq : LCond a dp mq φ) : mp = mq :=
  le_antisymm (chosen_mono hpos hlc le_rfl hmq hmp' hRq hLp)
    (chosen_mono hpos hlc le_rfl hmp hmq' hRp hLq)

/-! ## Lemma 6: gluing, by induction on the number of summands -/

/-- The glued functional: `φ'` up to the cut `M`, `ψ` after it. -/
def glue (M : ℕ) (φ' ψ : ℕ → ℝ) : ℕ → ℝ := fun c => if c ≤ M then φ' c else ψ c

lemma sum_glue_left {M s t : ℕ} (ht : t ≤ M) {w φ' ψ : ℕ → ℝ} :
    ∑ c ∈ Ioc s t, w c * glue M φ' ψ c = ∑ c ∈ Ioc s t, w c * φ' c :=
  sum_congr rfl fun c hc => by
    rw [mem_Ioc] at hc
    simp [glue, show c ≤ M by omega]

lemma sum_glue_right {M s t : ℕ} (hs : M ≤ s) {w φ' ψ : ℕ → ℝ} :
    ∑ c ∈ Ioc s t, w c * glue M φ' ψ c = ∑ c ∈ Ioc s t, w c * ψ c :=
  sum_congr rfl fun c hc => by
    rw [mem_Ioc] at hc
    simp [glue, show ¬ c ≤ M by omega]

/-- **Lemma 6 (gluing), inductive step.**  `φ'` exposes summands `0, …, q`; `ψ` satisfies (R) for
`q` and (R), (L) for `q+1`.  Then cutting at the chosen point `m q` exposes `0, …, q+1`.  Only
weak sortedness of the shifts is used. -/
theorem glue_step (hpos : Pos a n) (hlc : WLC a n) (d m : ℕ → ℕ) (q : ℕ)
    (hdq : ∀ p ≤ q, d p ≤ d q) (hdq1 : d q ≤ d (q + 1))
    (hwin : ∀ p ≤ q + 1, d p + 1 ≤ m p ∧ m p ≤ d p + n)
    (hmq : ∀ p ≤ q, m p ≤ m q) (hmq1 : m q ≤ m (q + 1))
    {φ' ψ : ℕ → ℝ} (h' : ∀ p ≤ q, RCond a n (d p) (m p) φ' ∧ LCond a (d p) (m p) φ')
    (hRq : RCond a n (d q) (m q) ψ) (hRq1 : RCond a n (d (q + 1)) (m (q + 1)) ψ)
    (hLq1 : LCond a (d (q + 1)) (m (q + 1)) ψ) :
    ∀ p ≤ q + 1, RCond a n (d p) (m p) (glue (m q) φ' ψ) ∧
      LCond a (d p) (m p) (glue (m q) φ' ψ) := by
  intro p hp
  rcases Nat.lt_or_ge p (q + 1) with hpq | hpq
  · have hpq' : p ≤ q := by omega
    obtain ⟨hR', hL'⟩ := h' p hpq'
    have hmp := hmq p hpq'
    have hdp := hdq p hpq'
    obtain ⟨hw1, hw2⟩ := hwin p hp
    obtain ⟨hwq1, hwq2⟩ := hwin q (by omega)
    refine ⟨fun y hy hyn => ?_, fun x hx hxm => ?_⟩
    · by_cases hyq : y ≤ m q
      · rw [sum_glue_left hyq]; exact hR' y hy hyn
      · rw [not_le] at hyq
        rw [← sum_Ioc_consecutive _ hmp hyq.le, sum_glue_left le_rfl, sum_glue_right le_rfl]
        have h1 : ∑ c ∈ Ioc (m p) (m q), a (c - d p) * φ' c ≤ 0 := by
          rcases Nat.eq_or_lt_of_le hmp with h | h
          · rw [h]; simp
          · exact (hR' (m q) h (by omega)).le
        have h2 := transfer_prefix hpos hlc hdp hwq1 hyq hyn (fun l h1 h2 => hRq l h1 (by omega))
        linarith
    · rw [sum_glue_left (by omega)]; exact hL' x hx hxm
  · obtain rfl : p = q + 1 := by omega
    obtain ⟨hw1, hw2⟩ := hwin (q + 1) le_rfl
    obtain ⟨hR', hL'⟩ := h' q le_rfl
    obtain ⟨hwq1, hwq2⟩ := hwin q (by omega)
    refine ⟨fun y hy hyn => ?_, fun x hx hxm => ?_⟩
    · rw [sum_glue_right (by omega)]; exact hRq1 y hy hyn
    · by_cases hxq : m q ≤ x
      · rw [sum_glue_right hxq]; exact hLq1 x hx hxm
      · rw [not_le] at hxq
        rw [← sum_Ioc_consecutive _ hxq.le hmq1, sum_glue_left le_rfl, sum_glue_right le_rfl]
        have h2 : 0 ≤ ∑ c ∈ Ioc (m q) (m (q + 1)), a (c - d (q + 1)) * ψ c := by
          rcases Nat.eq_or_lt_of_le hmq1 with h | h
          · rw [h]; simp
          · exact (hLq1 (m q) (by omega) h).le
        have h1 := transfer_suffix hpos hlc hdq1 hx hxq hwq2 (fun l h1 h2 => hL' l (by omega) h2)
        linarith

/-- The threshold functional `+1` up to `m`, `−1` after it, exposes a single summand. -/
lemma single_witness (hpos : Pos a n) {d m : ℕ} (hm : d + 1 ≤ m) (hm' : m ≤ d + n) :
    RCond a n d m (glue m (fun _ => 1) (fun _ => -1)) ∧
      LCond a d m (glue m (fun _ => 1) (fun _ => -1)) := by
  refine ⟨fun y hy hyn => ?_, fun x hx hxm => ?_⟩
  · rw [sum_glue_right le_rfl]
    refine sum_neg (fun c hc => ?_) ⟨y, by simp [mem_Ioc]; omega⟩
    rw [mem_Ioc] at hc
    have := hpos (c - d) (by omega) (by omega)
    linarith
  · rw [sum_glue_left le_rfl]
    refine sum_pos (fun c hc => ?_) ⟨m, by simp [mem_Ioc]; omega⟩
    rw [mem_Ioc] at hc
    have := hpos (c - d) (by omega) (by omega)
    linarith

/-- **Lemma 6 + Theorem 1 (3 ⟹ 1), global form.**  Monotone shifts, chosen points in their
windows, and a witness for every consecutive pair give one functional for all `r` summands. -/
theorem glued (hpos : Pos a n) (hlc : WLC a n) (d m : ℕ → ℕ) (r : ℕ) (hd : Monotone d)
    (hwin : ∀ p < r, d p + 1 ≤ m p ∧ m p ≤ d p + n)
    (hcons : ∀ p, p + 1 < r → ∃ ψ : ℕ → ℝ, RCond a n (d p) (m p) ψ ∧ LCond a (d p) (m p) ψ ∧
        RCond a n (d (p + 1)) (m (p + 1)) ψ ∧ LCond a (d (p + 1)) (m (p + 1)) ψ) :
    ∃ φ : ℕ → ℝ, ∀ p < r, RCond a n (d p) (m p) φ ∧ LCond a (d p) (m p) φ := by
  -- Lemma 3 on consecutive pairs: `m` is non-decreasing on `[0, r)`.
  have hstep : ∀ p, p + 1 < r → m p ≤ m (p + 1) := by
    intro p hp
    obtain ⟨ψ, _, hL, hR, _⟩ := hcons p hp
    exact chosen_mono hpos hlc (hd (show p ≤ p + 1 by omega)) (hwin (p + 1) hp).1
      (hwin p (by omega)).2 hR hL
  have hmono : ∀ q, q < r → ∀ p ≤ q, m p ≤ m q := by
    intro q
    induction q with
    | zero => intro _ p hp; obtain rfl : p = 0 := by omega
              exact le_rfl
    | succ q ih =>
        intro hq p hp
        rcases Nat.lt_or_ge p (q + 1) with h | h
        · exact (ih (by omega) p (by omega)).trans (hstep q hq)
        · obtain rfl : p = q + 1 := by omega
          exact le_rfl
  rcases Nat.eq_zero_or_pos r with hr | hr
  · exact ⟨fun _ => 0, fun p hp => by omega⟩
  have main : ∀ k, k < r → ∃ φ : ℕ → ℝ, ∀ p ≤ k, RCond a n (d p) (m p) φ ∧
      LCond a (d p) (m p) φ := by
    intro k
    induction k with
    | zero =>
        intro h0
        refine ⟨glue (m 0) (fun _ => 1) (fun _ => -1), fun p hp => ?_⟩
        obtain rfl : p = 0 := by omega
        exact single_witness hpos (hwin 0 h0).1 (hwin 0 h0).2
    | succ k ih =>
        intro hk
        obtain ⟨φ', h'⟩ := ih (by omega)
        obtain ⟨ψ, hRq, _, hRq1, hLq1⟩ := hcons k hk
        exact ⟨_, glue_step hpos hlc d m k (fun p hp => hd hp) (hd (Nat.le_succ k))
          (fun p hp => hwin p (by omega)) (hmono k (by omega)) (hstep k hk) h' hRq hRq1 hLq1⟩
  obtain ⟨φ, hφ⟩ := main (r - 1) (by omega)
  exact ⟨φ, fun p hp => hφ p (by omega)⟩

/-! ## Theorem 1 -/

lemma feasible_mono {d j : ℕ → ℕ} {S T : Finset ℕ} (hST : S ⊆ T) :
    Feasible a n d j T → Feasible a n d j S := fun ⟨φ, h⟩ => ⟨φ, fun p hp => h p (hST hp)⟩

/-- **Theorem 1 (3 ⟹ 1), the consecutive pairwise reduction.**  For a positive weakly
log-concave leg vector and weakly sorted shifts, if every consecutive pair of summands is
simultaneously exposable then all `r` summands are. -/
theorem pairwise_reduction (hpos : Pos a n) (hlc : WLC a n) {d j : ℕ → ℕ} {r : ℕ}
    (hd : Monotone d) (hj : ∀ p < r, 1 ≤ j p ∧ j p ≤ n)
    (hcons : ∀ p, p + 1 < r → Feasible a n d j {p, p + 1}) :
    Feasible a n d j (range r) := by
  obtain ⟨φ, hφ⟩ := glued hpos hlc d (fun p => d p + j p) r hd
    (fun p hp => ⟨by have := (hj p hp).1; omega, by have := (hj p hp).2; omega⟩)
    (fun p hp => by
      obtain ⟨ψ, hψ⟩ := hcons p hp
      have h0 := (expose_iff a n ψ (hj p (by omega)).2).mp (hψ p (by simp))
      have h1 := (expose_iff a n ψ (hj (p + 1) hp).2).mp (hψ (p + 1) (by simp))
      exact ⟨ψ, h0.1, h0.2, h1.1, h1.2⟩)
  refine ⟨φ, fun p hp => ?_⟩
  rw [mem_range] at hp
  exact (expose_iff a n φ (hj p hp).2).mpr (hφ p hp)

/-- **Theorem 1 (1 ⟺ 2 ⟺ 3).** -/
theorem feasible_iff_consecutive (hpos : Pos a n) (hlc : WLC a n) {d j : ℕ → ℕ} {r : ℕ}
    (hd : Monotone d) (hj : ∀ p < r, 1 ≤ j p ∧ j p ≤ n) :
    (Feasible a n d j (range r) ↔ ∀ p q, p < r → q < r → Feasible a n d j {p, q}) ∧
      (Feasible a n d j (range r) ↔ ∀ p, p + 1 < r → Feasible a n d j {p, p + 1}) := by
  refine ⟨⟨fun h p q hp hq => feasible_mono (fun x hx => ?_) h, fun h => ?_⟩,
    ⟨fun h p hp => feasible_mono (fun x hx => ?_) h, pairwise_reduction hpos hlc hd hj⟩⟩
  · simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa
  · exact pairwise_reduction hpos hlc hd hj (fun p hp => h p (p + 1) (by omega) hp)
  · simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp <;> omega

/-! ## Lemma 4 and Theorem 2 -/

/-- The step from chosen point `mp` (shift `dp`) to `mq` (shift `dq`) is **locked** (note, Lemma 4):
`mp < mq`, `dq < mp`, `mq ≤ dp + n`, and the ratio `a(c−dp)/a(c−dq)` is constant on `(mp, mq]` —
stated division-free, as equality with its value at `mq`. -/
def Locked (a : ℕ → ℝ) (n dp dq mp mq : ℕ) : Prop :=
  mp < mq ∧ dq < mp ∧ mq ≤ dp + n ∧
    ∀ c ∈ Ioc mp mq, a (c - dp) * a (mq - dq) = a (mq - dp) * a (c - dq)

/-- Theorem 2's conditions (i)–(iii) for the consecutive pair `(p, p+1)`. -/
def CF (a : ℕ → ℝ) (n : ℕ) (d j : ℕ → ℕ) (p : ℕ) : Prop :=
  (d p = d (p + 1) → d p + j p = d (p + 1) + j (p + 1)) ∧
    d p + j p ≤ d (p + 1) + j (p + 1) ∧
    ¬ Locked a n (d p) (d (p + 1)) (d p + j p) (d (p + 1) + j (p + 1))

/-- **Lemma 4 (a locked step is fatal; positivity only).** -/
theorem locked_infeasible (hpos : Pos a n) {dp dq mp mq : ℕ} {φ : ℕ → ℝ} (hd : dp ≤ dq)
    (hl : Locked a n dp dq mp mq) (hR : RCond a n dp mp φ) (hL : LCond a dq mq φ) : False := by
  obtain ⟨hlt, hdm, hmn, hconst⟩ := hl
  have h1 := hR mq hlt hmn
  have h2 := hL mp (by omega) hlt
  have hq : 0 < a (mq - dq) := hpos _ (by omega) (by omega)
  have hp : 0 < a (mq - dp) := hpos _ (by omega) (by omega)
  have key : (∑ c ∈ Ioc mp mq, a (c - dp) * φ c) * a (mq - dq)
      = a (mq - dp) * ∑ c ∈ Ioc mp mq, a (c - dq) * φ c := by
    rw [sum_mul, mul_sum]
    refine sum_congr rfl fun c hc => ?_
    have := hconst c hc
    linear_combination φ c * this
  have : (∑ c ∈ Ioc mp mq, a (c - dp) * φ c) * a (mq - dq) < 0 := mul_neg_of_neg_of_pos h1 hq
  have : 0 < a (mq - dp) * ∑ c ∈ Ioc mp mq, a (c - dq) * φ c := mul_pos hp h2
  linarith

/-- **Finding: condition (i) is implied by (ii) and (iii).**  Equal shifts with a strict climb
give a locked step automatically. -/
theorem tie_of_not_locked {dp dq mp mq : ℕ} (hdd : dp = dq) (hp1 : dp + 1 ≤ mp)
    (hq2 : mq ≤ dq + n) (hm : mp ≤ mq) (hnl : ¬ Locked a n dp dq mp mq) : mp = mq := by
  subst hdd
  by_contra hne
  exact hnl ⟨by omega, by omega, hq2, fun c _ => by ring⟩

/-- Chaining a weakly decreasing step condition. -/
lemma chain_anti (ρ : ℕ → ℝ) (s : ℕ) :
    ∀ t, s ≤ t → (∀ c, s ≤ c → c < t → ρ (c + 1) ≤ ρ c) → ρ t ≤ ρ s := by
  intro t
  induction t with
  | zero => intro h _; obtain rfl : s = 0 := by omega
            exact le_rfl
  | succ t ih =>
      intro h hρ
      rcases Nat.eq_or_lt_of_le h with h1 | h1
      · rw [h1]
      · exact (hρ t (by omega) (by omega)).trans (ih (by omega) fun c h2 h3 => hρ c h2 (by omega))
lemma sum_sparse (w : ℕ → ℝ) {s M x y : ℕ} (hsM : s + 1 < M) (hx : s ≤ x) (hxy : x < y)
    (hy : y ≤ M) (u v : ℝ) :
    ∑ c ∈ Ioc x y, w c * (if c = s + 1 then u else if c = M then v else 0)
      = (if x = s then w (s + 1) * u else 0) + (if y = M then w M * v else 0) := by
  have h : ∀ c, w c * (if c = s + 1 then u else if c = M then v else 0)
      = (if c = s + 1 then w c * u else 0) + (if c = M then w c * v else 0) := by
    intro c
    by_cases h1 : c = s + 1
    · have h2 : c ≠ M := by omega
      rw [if_pos h1, if_pos h1, if_neg h2, add_zero]
    · by_cases h2 : c = M
      · rw [if_neg h1, if_neg h1, if_pos h2, if_pos h2, zero_add]
      · rw [if_neg h1, if_neg h1, if_neg h2, if_neg h2, mul_zero, add_zero]
  simp only [h, sum_add_distrib, sum_ite_eq', mem_Ioc]
  congr 1
  · by_cases h1 : x = s
    · rw [if_pos (show x < s + 1 ∧ s + 1 ≤ y by omega), if_pos h1]
    · rw [if_neg (show ¬(x < s + 1 ∧ s + 1 ≤ y) by omega), if_neg h1]
  · by_cases h1 : y = M
    · rw [if_pos (show x < M ∧ M ≤ y by omega), if_pos h1]
    · rw [if_neg (show ¬(x < M ∧ M ≤ y) by omega), if_neg h1]

/-- A *gadget* on the gap `(mp, mq]` (note §3: the after-peak half of `(R_p)` and the before-peak
half of `(L_q)`, restricted to the gap), glued with `+1` before and `−1` after, witnesses the
pair. -/
lemma gadget_glue (hpos : Pos a n) {dp dq mp mq : ℕ} (hd : dp ≤ dq)
    (hp1 : dp + 1 ≤ mp) (hp2 : mp ≤ dp + n) (hq1 : dq + 1 ≤ mq) (hq2 : mq ≤ dq + n)
    (hm : mp ≤ mq) {g : ℕ → ℝ}
    (hE : ∀ y, mp < y → y ≤ mq → y ≤ dp + n → ∑ c ∈ Ioc mp y, a (c - dp) * g c < 0)
    (hΛ : ∀ x, mp ≤ x → dq + 1 ≤ x → x < mq → 0 < ∑ c ∈ Ioc x mq, a (c - dq) * g c) :
    RCond a n dp mp (glue mp (fun _ => 1) (glue mq g (fun _ => -1))) ∧
      LCond a dp mp (glue mp (fun _ => 1) (glue mq g (fun _ => -1))) ∧
      RCond a n dq mq (glue mp (fun _ => 1) (glue mq g (fun _ => -1))) ∧
      LCond a dq mq (glue mp (fun _ => 1) (glue mq g (fun _ => -1))) := by
  refine ⟨fun y hy hyn => ?_, fun x hx hxm => ?_, fun y hy hyn => ?_, fun x hx hxm => ?_⟩
  · rw [sum_glue_right le_rfl]
    by_cases hyq : y ≤ mq
    · rw [sum_glue_left hyq]; exact hE y hy hyq hyn
    · rw [not_le] at hyq
      rw [← sum_Ioc_consecutive _ hm hyq.le, sum_glue_left le_rfl, sum_glue_right le_rfl]
      have h1 : ∑ c ∈ Ioc mp mq, a (c - dp) * g c ≤ 0 := by
        rcases Nat.eq_or_lt_of_le hm with h | h
        · rw [h]; simp
        · exact (hE mq h le_rfl (by omega)).le
      have h2 : ∑ c ∈ Ioc mq y, a (c - dp) * (fun _ => (-1 : ℝ)) c < 0 := by
        refine sum_neg (fun c hc => ?_) ⟨y, by simp [mem_Ioc]; omega⟩
        rw [mem_Ioc] at hc; have := hpos (c - dp) (by omega) (by omega); simp; linarith
      linarith
  · rw [sum_glue_left le_rfl]
    refine sum_pos (fun c hc => ?_) ⟨mp, by simp [mem_Ioc]; omega⟩
    rw [mem_Ioc] at hc; have := hpos (c - dp) (by omega) (by omega); simp; linarith
  · rw [sum_glue_right (by omega : mp ≤ mq), sum_glue_right le_rfl]
    refine sum_neg (fun c hc => ?_) ⟨y, by simp [mem_Ioc]; omega⟩
    rw [mem_Ioc] at hc; have := hpos (c - dq) (by omega) (by omega); simp; linarith
  · by_cases hxp : mp ≤ x
    · rw [sum_glue_right hxp, sum_glue_left le_rfl]; exact hΛ x hxp hx hxm
    · rw [not_le] at hxp
      rw [← sum_Ioc_consecutive _ hxp.le hm, sum_glue_left le_rfl, sum_glue_right le_rfl,
        sum_glue_left le_rfl]
      have h1 : 0 < ∑ c ∈ Ioc x mp, a (c - dq) * (fun _ => (1 : ℝ)) c := by
        refine sum_pos (fun c hc => ?_) ⟨mp, by simp [mem_Ioc]; omega⟩
        rw [mem_Ioc] at hc; have := hpos (c - dq) (by omega) (by omega); simp; linarith
      have h2 : 0 ≤ ∑ c ∈ Ioc mp mq, a (c - dq) * g c := by
        rcases Nat.eq_or_lt_of_le hm with h | h
        · rw [h]; simp
        · exact (hΛ mp le_rfl (by omega) h).le
      linarith

/-- **Theorem 2, Case A** (`mp ≤ dq`): the gadget `−Λ` at `mp+1`, `+1` after it. -/
lemma gadget_caseA (hpos : Pos a n) {dp dq mp mq : ℕ}
    (hp1 : dp + 1 ≤ mp) (hq2 : mq ≤ dq + n) (hA : mp ≤ dq) :
    ∃ g : ℕ → ℝ,
      (∀ y, mp < y → y ≤ mq → y ≤ dp + n → ∑ c ∈ Ioc mp y, a (c - dp) * g c < 0) ∧
      (∀ x, mp ≤ x → dq + 1 ≤ x → x < mq → 0 < ∑ c ∈ Ioc x mq, a (c - dq) * g c) := by
  set T := ∑ c ∈ Ioc (mp + 1) (dp + n), a (c - dp)
  set Λ := (T + 1) / a (mp + 1 - dp)
  refine ⟨fun c => if c = mp + 1 then -Λ else 1, fun y hy hyq hyn => ?_, fun x hx hxd hxm => ?_⟩
  · dsimp only
    have ha : 0 < a (mp + 1 - dp) := hpos _ (by omega) (by omega)
    rw [sum_Ioc_bot _ hy, if_pos rfl]
    have hrest : ∑ c ∈ Ioc (mp + 1) y, a (c - dp) * (if c = mp + 1 then -Λ else 1)
        = ∑ c ∈ Ioc (mp + 1) y, a (c - dp) := by
      refine sum_congr rfl fun c hc => ?_
      rw [mem_Ioc] at hc
      rw [if_neg (by omega), mul_one]
    have hle : ∑ c ∈ Ioc (mp + 1) y, a (c - dp) ≤ T := by
      refine sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_right hyn) fun c hc _ => ?_
      rw [mem_Ioc] at hc
      exact (hpos _ (by omega) (by omega)).le
    have hΛ : a (mp + 1 - dp) * -Λ = -(T + 1) := by
      simp only [Λ]; field_simp
    rw [hrest, hΛ]
    linarith
  · dsimp only
    refine sum_pos (fun c hc => ?_) ⟨mq, by simp [mem_Ioc]; omega⟩
    rw [mem_Ioc] at hc
    rw [if_neg (by omega), mul_one]
    exact hpos _ (by omega) (by omega)

/-- **Theorem 2, Case B** (`dq < mp`, `dp + n < mq`): `−1` on the gap, `Λ` at `mq`. -/
lemma gadget_caseB (hpos : Pos a n) {dp dq mp mq : ℕ}
    (hq2 : mq ≤ dq + n) (hB1 : dq < mp) (hB2 : dp + n < mq) :
    ∃ g : ℕ → ℝ,
      (∀ y, mp < y → y ≤ mq → y ≤ dp + n → ∑ c ∈ Ioc mp y, a (c - dp) * g c < 0) ∧
      (∀ x, mp ≤ x → dq + 1 ≤ x → x < mq → 0 < ∑ c ∈ Ioc x mq, a (c - dq) * g c) := by
  obtain ⟨M, rfl⟩ : ∃ M, mq = M + 1 := ⟨mq - 1, by omega⟩
  set T := ∑ c ∈ Ioc mp M, a (c - dq)
  set Λ := (T + 1) / a (M + 1 - dq)
  refine ⟨fun c => if c = M + 1 then Λ else -1, fun y hy hyq hyn => ?_, fun x hx hxd hxm => ?_⟩
  · dsimp only
    refine sum_neg (fun c hc => ?_) ⟨y, by simp [mem_Ioc]; omega⟩
    rw [mem_Ioc] at hc
    rw [if_neg (by omega)]
    have := hpos (c - dp) (by omega) (by omega)
    linarith
  · dsimp only
    have ha : 0 < a (M + 1 - dq) := hpos _ (by omega) (by omega)
    rw [sum_Ioc_succ_top (by omega), if_pos rfl]
    have hrest : ∑ c ∈ Ioc x M, a (c - dq) * (if c = M + 1 then Λ else -1)
        = -∑ c ∈ Ioc x M, a (c - dq) := by
      rw [← sum_neg_distrib]
      refine sum_congr rfl fun c hc => ?_
      rw [mem_Ioc] at hc
      rw [if_neg (by omega)]; ring
    have hle : ∑ c ∈ Ioc x M, a (c - dq) ≤ T := by
      refine sum_le_sum_of_subset_of_nonneg (Ioc_subset_Ioc_left hx) fun c hc _ => ?_
      rw [mem_Ioc] at hc
      exact (hpos _ (by omega) (by omega)).le
    have hΛ : a (M + 1 - dq) * Λ = T + 1 := by
      simp only [Λ]; field_simp
    rw [hrest, hΛ]
    linarith

/-- **Theorem 2, Case C** (`dq < mp`, `mq ≤ dp + n`, step not locked): `prop-gapK`'s functional
cut down to the gap. -/
lemma gadget_caseC (hpos : Pos a n) (hlc : WLC a n) {dp dq mp mq : ℕ} (hd : dp ≤ dq)
    (hlt : mp < mq) (hq2 : mq ≤ dq + n) (hC1 : dq < mp) (hC2 : mq ≤ dp + n)
    (hnl : ¬ Locked a n dp dq mp mq) :
    ∃ g : ℕ → ℝ,
      (∀ y, mp < y → y ≤ mq → y ≤ dp + n → ∑ c ∈ Ioc mp y, a (c - dp) * g c < 0) ∧
      (∀ x, mp ≤ x → dq + 1 ≤ x → x < mq → 0 < ∑ c ∈ Ioc x mq, a (c - dq) * g c) := by
  -- the ratio, weakly decreasing on the gap (Lemma 1)
  set ρ : ℕ → ℝ := fun c => a (c - dp) / a (c - dq) with hρdef
  have hstep : ∀ c, mp + 1 ≤ c → c < mq → ρ (c + 1) ≤ ρ c := by
    intro c h1 h2
    simp only [hρdef]
    rw [div_le_div_iff₀ (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega))]
    exact lc_glob hpos hlc hd (c := c) (by omega) (by omega)
  -- non-constancy from "not locked"
  obtain ⟨c0, hc0, hne⟩ : ∃ c0 ∈ Ioc mp mq,
      a (c0 - dp) * a (mq - dq) ≠ a (mq - dp) * a (c0 - dq) := by
    by_contra hcon
    push Not at hcon
    exact hnl ⟨hlt, hC1, hC2, hcon⟩
  rw [mem_Ioc] at hc0
  have hc0q : c0 ≠ mq := by rintro rfl; exact hne (by ring)
  have hρne : ρ c0 ≠ ρ mq := by
    simp only [hρdef]
    rw [Ne, div_eq_div_iff (hpos _ (by omega) (by omega)).ne' (hpos _ (by omega) (by omega)).ne']
    exact hne
  have hA : ρ mq ≤ ρ c0 := chain_anti ρ c0 mq hc0.2 fun c h1 h2 => hstep c (by omega) h2
  have hB : ρ c0 ≤ ρ (mp + 1) := chain_anti ρ (mp + 1) c0 (by omega)
    fun c h1 h2 => hstep c h1 (by omega)
  have hρlt : ρ mq < ρ (mp + 1) := lt_of_lt_of_le (lt_of_le_of_ne hA (Ne.symm hρne)) hB
  have hgap : mp + 1 < mq := by omega
  have hρq : 0 < ρ mq := div_pos (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega))
  set β : ℝ := (ρ mq + ρ (mp + 1)) / (2 * ρ mq) with hβ
  have hβ1 : 1 < β := by
    rw [hβ, one_lt_div (by positivity)]; linarith
  have hβ2 : β * ρ mq < ρ (mp + 1) := by
    have : β * ρ mq = (ρ mq + ρ (mp + 1)) / 2 := by rw [hβ]; field_simp
    rw [this]; linarith
  have ha1 : a (mp + 1 - dq) ≠ 0 := (hpos _ (by omega) (by omega)).ne'
  have ha2 : a (mq - dq) ≠ 0 := (hpos _ (by omega) (by omega)).ne'
  refine ⟨fun c => if c = mp + 1 then -1 / a (mp + 1 - dq) else
      if c = mq then β / a (mq - dq) else 0, fun y hy hyq hyn => ?_, fun x hx hxd hxm => ?_⟩
  · dsimp only
    rw [sum_sparse _ hgap le_rfl hy hyq, if_pos rfl]
    have e1 : a (mp + 1 - dp) * (-1 / a (mp + 1 - dq)) = -ρ (mp + 1) := by
      simp only [hρdef]; ring
    have e2 : a (mq - dp) * (β / a (mq - dq)) = β * ρ mq := by
      simp only [hρdef]; ring
    rw [e1, e2]
    have hρ1 : 0 < ρ (mp + 1) := hρq.trans hρlt
    split_ifs <;> linarith
  · dsimp only
    rw [sum_sparse _ hgap hx hxm le_rfl, if_pos rfl]
    have e1 : a (mp + 1 - dq) * (-1 / a (mp + 1 - dq)) = -1 := by field_simp
    have e2 : a (mq - dq) * (β / a (mq - dq)) = β := by field_simp
    rw [e1, e2]
    split_ifs <;> linarith

/-- **Theorem 2, sufficiency at rank two.**  (ii) and (iii) give a witness for the pair; (i) is not
needed (see `tie_of_not_locked`). -/
theorem pair_feasible_of_CF (hpos : Pos a n) (hlc : WLC a n) {dp dq mp mq : ℕ} (hd : dp ≤ dq)
    (hp1 : dp + 1 ≤ mp) (hp2 : mp ≤ dp + n) (hq1 : dq + 1 ≤ mq) (hq2 : mq ≤ dq + n)
    (hm : mp ≤ mq) (hnl : ¬ Locked a n dp dq mp mq) :
    ∃ ψ : ℕ → ℝ, RCond a n dp mp ψ ∧ LCond a dp mp ψ ∧ RCond a n dq mq ψ ∧ LCond a dq mq ψ := by
  have hg : ∃ g : ℕ → ℝ,
      (∀ y, mp < y → y ≤ mq → y ≤ dp + n → ∑ c ∈ Ioc mp y, a (c - dp) * g c < 0) ∧
      (∀ x, mp ≤ x → dq + 1 ≤ x → x < mq → 0 < ∑ c ∈ Ioc x mq, a (c - dq) * g c) := by
    rcases Nat.eq_or_lt_of_le hm with heq | hlt
    · exact ⟨0, fun y h1 h2 _ => by omega, fun x h1 _ h3 => by omega⟩
    rcases Nat.lt_or_ge dq mp with hC1 | hA
    · rcases Nat.lt_or_ge (dp + n) mq with hB2 | hC2
      · exact gadget_caseB hpos hq2 hC1 hB2
      · exact gadget_caseC hpos hlc hd hlt hq2 hC1 hC2 hnl
    · exact gadget_caseA hpos hp1 hq2 hA
  obtain ⟨g, hE, hΛ⟩ := hg
  exact ⟨_, gadget_glue hpos hd hp1 hp2 hq1 hq2 hm hE hΛ⟩

/-- **Theorem 2 (explicit V-description), window form.**  For a positive weakly log-concave leg
vector and weakly sorted shifts, all `r` summands are simultaneously exposable iff every
consecutive pair satisfies (i)–(iii). -/
theorem feasible_iff_CF (hpos : Pos a n) (hlc : WLC a n) {d j : ℕ → ℕ} {r : ℕ}
    (hd : Monotone d) (hj : ∀ p < r, 1 ≤ j p ∧ j p ≤ n) :
    Feasible a n d j (range r) ↔ ∀ p, p + 1 < r → CF a n d j p := by
  constructor
  · rintro ⟨φ, hφ⟩ p hp
    have hp0 := (expose_iff a n φ (hj p (by omega)).2).mp (hφ p (by simp; omega))
    have hp1 := (expose_iff a n φ (hj (p + 1) hp).2).mp (hφ (p + 1) (by simpa using hp))
    have hjp := hj p (by omega)
    have hjq := hj (p + 1) hp
    have hdd := hd (show p ≤ p + 1 by omega)
    refine ⟨fun heq => ?_, chosen_mono hpos hlc hdd (by omega) (by omega) hp1.1 hp0.2,
      fun hl => locked_infeasible hpos hdd hl hp0.1 hp1.2⟩
    rw [← heq] at hp1 ⊢
    exact chosen_eq_of_tie hpos hlc (by omega) (by omega) (by omega) (by omega)
      hp0.1 hp0.2 hp1.1 hp1.2
  · intro h
    refine pairwise_reduction hpos hlc hd hj fun p hp => ?_
    obtain ⟨-, hm, hnl⟩ := h p hp
    have hjp := hj p (by omega)
    have hjq := hj (p + 1) hp
    obtain ⟨ψ, h1, h2, h3, h4⟩ := pair_feasible_of_CF hpos hlc (hd (show p ≤ p + 1 by omega))
      (by omega) (by omega) (by omega) (by omega) hm hnl
    refine ⟨ψ, fun q hq => ?_⟩
    simp only [mem_insert, mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact (expose_iff a n ψ hjp.2).mpr ⟨h1, h2⟩
    · exact (expose_iff a n ψ hjq.2).mpr ⟨h3, h4⟩

/-! ## Strict log-concavity: the Kozlov form of Theorem 2 -/

/-- Strict log-concavity, cross-multiplied. -/
def SLC (a : ℕ → ℝ) (n : ℕ) : Prop := ∀ i, 1 ≤ i → i + 2 ≤ n → a i * a (i + 2) < a (i + 1) ^ 2

lemma SLC.wlc (h : SLC a n) : WLC a n := fun i h1 h2 => (h i h1 h2).le

/-- Lemma 1, strict: for shift difference `h + 1 ≥ 1` the ratio decreases strictly. -/
lemma slc_cross (hpos : Pos a n) (hslc : SLC a n) :
    ∀ h u, 1 ≤ u → u + 2 + h ≤ n → a (u + 2 + h) * a u < a (u + 1 + h) * a (u + 1) := by
  intro h
  induction h with
  | zero =>
      intro u hu hun
      have := hslc u hu (by omega)
      simp only [add_zero]
      linarith [mul_comm (a u) (a (u + 2)), sq (a (u + 1))]
  | succ h ih =>
      intro u hu hun
      have hIH := ih u hu (by omega)
      have hS := hslc (u + 1 + h) (by omega) (by omega)
      have hA0 : 0 < a (u + 1 + h) := hpos _ (by omega) (by omega)
      have hA2 : 0 < a (u + 2 + h) := hpos _ (by omega) (by omega)
      have hu0 : 0 < a u := hpos _ hu (by omega)
      have e1 : u + 2 + (h + 1) = u + 1 + h + 2 := by omega
      have e2 : u + 1 + (h + 1) = u + 1 + h + 1 := by omega
      have e3 : u + 2 + h = u + 1 + h + 1 := by omega
      rw [e1, e2]
      rw [e3] at hIH hA2
      have hA : a (u + 1 + h) * (a (u + 1 + h + 2) * a u)
          < a (u + 1 + h) * (a (u + 1 + h + 1) * a (u + 1)) := by
        nlinarith [mul_lt_mul_of_pos_right hS hu0, mul_lt_mul_of_pos_left hIH hA2]
      exact lt_of_mul_lt_mul_left hA hA0.le

lemma lc_glob_strict (hpos : Pos a n) (hslc : SLC a n) {e d c : ℕ} (hed : e < d) (hc : d + 1 ≤ c)
    (hcn : c + 1 - e ≤ n) : a (c + 1 - e) * a (c - d) < a (c - e) * a (c + 1 - d) := by
  have := slc_cross hpos hslc (d - e - 1) (c - d) (by omega) (by omega)
  have e1 : c - d + 2 + (d - e - 1) = c + 1 - e := by omega
  have e2 : c - d + 1 + (d - e - 1) = c - e := by omega
  have e3 : c - d + 1 = c + 1 - d := by omega
  rwa [e1, e2, e3] at this

/-- **Strict log-concavity: a locked step is a unit step inside the overlap** (note, Corollary "the
Kozlov polytope at every rank"). -/
theorem locked_iff_unit (hpos : Pos a n) (hslc : SLC a n) {dp dq mp mq : ℕ} (hd : dp < dq)
    (hmq : mq ≤ dq + n) :
    Locked a n dp dq mp mq ↔ mq = mp + 1 ∧ dq < mp ∧ mp < dp + n := by
  constructor
  · rintro ⟨hlt, hdm, hmn, hconst⟩
    refine ⟨?_, hdm, by omega⟩
    by_contra hne
    have h2 : mp + 2 ≤ mq := by omega
    set ρ : ℕ → ℝ := fun c => a (c - dp) / a (c - dq) with hρdef
    have hstep : ∀ c, mp + 2 ≤ c → c < mq → ρ (c + 1) ≤ ρ c := by
      intro c h1 h3
      simp only [hρdef]
      rw [div_le_div_iff₀ (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega))]
      exact lc_glob hpos hslc.wlc hd.le (c := c) (by omega) (by omega)
    have hs : ρ (mp + 1 + 1) < ρ (mp + 1) := by
      simp only [hρdef]
      rw [div_lt_div_iff₀ (hpos _ (by omega) (by omega)) (hpos _ (by omega) (by omega))]
      exact lc_glob_strict hpos hslc hd (c := mp + 1) (by omega) (by omega)
    have hA := chain_anti ρ (mp + 2) mq h2 hstep
    have hc := hconst (mp + 1) (by rw [mem_Ioc]; omega)
    have heq : ρ (mp + 1) = ρ mq := by
      simp only [hρdef]
      rw [div_eq_div_iff (hpos _ (by omega) (by omega)).ne' (hpos _ (by omega) (by omega)).ne']
      exact hc
    linarith
  · rintro ⟨rfl, h1, h2⟩
    refine ⟨by omega, h1, by omega, fun c hc => ?_⟩
    rw [mem_Ioc] at hc
    obtain rfl : c = mp + 1 := by omega
    ring

/-- The Kozlov-type condition: chosen points climb weakly, equal shifts force equal points, and
a climb by exactly one happens only across a window boundary. -/
def KozCond (n : ℕ) (d j : ℕ → ℕ) (p : ℕ) : Prop :=
  (d p = d (p + 1) → d p + j p = d (p + 1) + j (p + 1)) ∧
    d p + j p ≤ d (p + 1) + j (p + 1) ∧
    ¬ (d (p + 1) + j (p + 1) = d p + j p + 1 ∧ d (p + 1) < d p + j p ∧ d p + j p < d p + n)

/-- For strictly log-concave `a`, Theorem 2's (i)–(iii) are the Kozlov condition. -/
theorem CF_iff_KozCond (hpos : Pos a n) (hslc : SLC a n) {d j : ℕ → ℕ} {p : ℕ}
    (hd : d p ≤ d (p + 1)) (hjq : j (p + 1) ≤ n) : CF a n d j p ↔ KozCond n d j p := by
  rcases Nat.lt_or_eq_of_le hd with hlt | heq
  · simp only [CF, KozCond, locked_iff_unit hpos hslc hlt (by omega : d (p + 1) + j (p + 1) ≤ _)]
  · constructor
    · rintro ⟨h1, h2, -⟩
      have := h1 heq
      exact ⟨h1, h2, fun h => by omega⟩
    · rintro ⟨h1, h2, -⟩
      have := h1 heq
      exact ⟨h1, h2, fun h => by obtain ⟨h, -⟩ := h; omega⟩

end ExteriorConvex.Pairwise
