/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# The centroid of the ff-vectors of a dilate: the abstract half of `cor-centroid-dilation`

Formalisation of the finite-set and asymptotic skeleton of Corollary `cor-centroid-dilation` of
`article/exterior-convex_article3_latest.org` (it was Conjecture `conj-centroid-dilation`):
`c(FF(n;0^r))/r → c(Koz(n))` as `r → ∞`, with error `O(1/r)`. The proof is written out in
`working-notes/centroid-dilation-corollary-2026-11-09.org`. Written 2026-11-09 by
Claude-Code (jts-mini), subagent; Mathlib only, not yet wired into `ExteriorConvex.lean`.

**Proved here (no hypotheses beyond those stated):**
* `avg`, `centroid`, `cov`: uniform average over a `Finset`, centroid and covariance of a
  finite set of points of `Fin m → ℝ`.
* `abs_avg_sub_avg_le` (**the mixing lemma**): for finite `A ⊆ B`, `A ≠ ∅`, and `g` with values
  in `[m, M]` on `B`, `|avg_A g − avg_B g| ≤ (1 − |A|/|B|)(M − m)`.
* `abs_centroid_sub_centroid_le`, `abs_secondMoment_sub_le`, `abs_cov_sub_cov_le`: the same for
  each centroid coordinate (bound `(1 − f) M_k`), each second moment (`(1 − f) M_k M_l`) and each
  covariance entry (`3 (1 − f) M_k M_l`), when every point of `B` lies in the box `∏ [0, M_k]`.
* `tendsto_centroid_div`: if `A_r ⊆ B_r`, the points of `B_r` lie in `∏ [0, r M_k]`,
  `|A_r|/|B_r| → 1` and `c(B_r)_k / r → c_k`, then `c(A_r)_k / r → c_k`.
* `abs_centroid_div_sub_le`: the same with rates, for one `r`.
* `centroid_dilation_rate`, `centroid_dilation_tendsto`: if moreover `|A_r| = a(r)`,
  `|B_r| = L(r)` and `∑_{x ∈ B_r} x_k = S_k(r)` for real polynomials with
  `deg (X·(L − a)) ≤ deg L` and `deg (S_k − c_k·X·L) ≤ deg L`, then
  `|c(A_r)_k / r − c_k| ≤ K / r` for all large `r`, and so `c(A_r)_k / r → c_k`.

**Enters as hypotheses (not formalised here):** that `A_r = FF(n;0^r)` lies inside
`B_r = rKoz(n) ∩ ℤ^{n+1}` and that `B_r` lies in the box `∏ [0, r·C(n,k)]` (elementary);
the polynomiality of `a(r)` and `L(r)` with `deg (L − a) ≤ n − 2 < n − 1 = deg L`
(`cor-zero-shift`, its `FF` half being Part II, Theorem 36); and the polynomiality of
`S_k(r) = ∑_{x ∈ B_r} x_k` with `S_k − c_k·r·L(r)` of degree `≤ n − 1` (Ehrhart's theorem for the
lattice polytopes `Q_k = {(x, z) : x ∈ Koz(n), 0 ≤ z ≤ x_k}`, see the note).
-/
import Mathlib

namespace ExteriorConvex
namespace CentroidDilation

open Finset Filter Topology Polynomial

variable {α : Type*}

/-- The uniform average of `g` over the finite set `s` (`0` when `s = ∅`). -/
noncomputable def avg (s : Finset α) (g : α → ℝ) : ℝ := (∑ x ∈ s, g x) / s.card

lemma card_mul_le_sum {s : Finset α} {g : α → ℝ} {m : ℝ} (h : ∀ x ∈ s, m ≤ g x) :
    (s.card : ℝ) * m ≤ ∑ x ∈ s, g x := by
  simpa [nsmul_eq_mul] using card_nsmul_le_sum s g m h

lemma sum_le_card_mul {s : Finset α} {g : α → ℝ} {M : ℝ} (h : ∀ x ∈ s, g x ≤ M) :
    ∑ x ∈ s, g x ≤ (s.card : ℝ) * M := by
  simpa [nsmul_eq_mul] using sum_le_card_nsmul s g M h

/-- An average of values in `[m, M]` lies in `[m, M]`. -/
lemma avg_mem_Icc {s : Finset α} {g : α → ℝ} {m M : ℝ} (hs : s.Nonempty)
    (hlo : ∀ x ∈ s, m ≤ g x) (hhi : ∀ x ∈ s, g x ≤ M) : m ≤ avg s g ∧ avg s g ≤ M := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have h1 := card_mul_le_sum hlo
  have h2 := sum_le_card_mul hhi
  unfold avg
  constructor
  · rw [le_div_iff₀ hc]; linarith
  · rw [div_le_iff₀ hc]; linarith

/-- **The mixing lemma.** For finite `A ⊆ B` with `A` non-empty and `g` with values in `[m, M]`
on `B`, the averages of `g` over `A` and over `B` differ by at most `(1 − |A|/|B|)(M − m)`. -/
theorem abs_avg_sub_avg_le [DecidableEq α] {A B : Finset α} {g : α → ℝ} {m M : ℝ}
    (hA : A.Nonempty) (hAB : A ⊆ B) (hlo : ∀ x ∈ B, m ≤ g x) (hhi : ∀ x ∈ B, g x ≤ M) :
    |avg A g - avg B g| ≤ (1 - (A.card : ℝ) / B.card) * (M - m) := by
  have hB : B.Nonempty := hA.mono hAB
  have ha : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  have hab : (A.card : ℝ) ≤ B.card := by exact_mod_cast card_le_card hAB
  have hcard : ((B \ A).card : ℝ) = B.card - A.card := by
    rw [card_sdiff_of_subset hAB, Nat.cast_sub (card_le_card hAB)]
  have hsum : ∑ x ∈ B, g x = ∑ x ∈ B \ A, g x + ∑ x ∈ A, g x := (sum_sdiff hAB).symm
  have hA1 : (A.card : ℝ) * m ≤ ∑ x ∈ A, g x := card_mul_le_sum fun x hx => hlo x (hAB hx)
  have hA2 : ∑ x ∈ A, g x ≤ (A.card : ℝ) * M := sum_le_card_mul fun x hx => hhi x (hAB hx)
  have hC1 : ((B \ A).card : ℝ) * m ≤ ∑ x ∈ B \ A, g x :=
    card_mul_le_sum fun x hx => hlo x (mem_sdiff.1 hx).1
  have hC2 : ∑ x ∈ B \ A, g x ≤ ((B \ A).card : ℝ) * M :=
    sum_le_card_mul fun x hx => hhi x (mem_sdiff.1 hx).1
  rw [hcard] at hC1 hC2
  unfold avg
  rw [hsum]
  generalize ∑ x ∈ A, g x = SA at *
  generalize ∑ x ∈ B \ A, g x = SC at *
  generalize (A.card : ℝ) = a at *
  generalize (B.card : ℝ) = b at *
  have ha0 : a ≠ 0 := ha.ne'
  have hb0 : b ≠ 0 := hb.ne'
  have key : SA / a - (SC + SA) / b = ((b - a) * SA - a * SC) / (a * b) := by
    field_simp
    ring
  have hfac : (1 - a / b) * (M - m) = (a * (b - a) * (M - m)) / (a * b) := by
    field_simp
  have hab' : 0 < a * b := mul_pos ha hb
  have hba : 0 ≤ b - a := sub_nonneg.2 hab
  rw [key, hfac, abs_le]
  constructor
  · rw [← neg_div, div_le_div_iff_of_pos_right hab']
    nlinarith [mul_le_mul_of_nonneg_left hA1 hba, mul_le_mul_of_nonneg_left hC2 ha.le]
  · rw [div_le_div_iff_of_pos_right hab']
    nlinarith [mul_le_mul_of_nonneg_left hA2 hba, mul_le_mul_of_nonneg_left hC1 ha.le]

/-! ### Centroids, second moments and covariances of finite point sets -/

variable {m : ℕ}

/-- The centroid of a finite set of points of `ℝ^m`, coordinatewise. -/
noncomputable def centroid (s : Finset (Fin m → ℝ)) : Fin m → ℝ := fun k => avg s (fun x => x k)

/-- The covariance matrix of the uniform measure on a finite set of points of `ℝ^m`. -/
noncomputable def cov (s : Finset (Fin m → ℝ)) (k l : Fin m) : ℝ :=
  avg s (fun x => x k * x l) - centroid s k * centroid s l

lemma centroid_mem_Icc {s : Finset (Fin m → ℝ)} {M : Fin m → ℝ} (hs : s.Nonempty)
    (hbox : ∀ x ∈ s, ∀ k, 0 ≤ x k ∧ x k ≤ M k) (k : Fin m) :
    0 ≤ centroid s k ∧ centroid s k ≤ M k :=
  avg_mem_Icc hs (fun x hx => (hbox x hx k).1) (fun x hx => (hbox x hx k).2)

/-- The mixing lemma for one coordinate of the centroid. -/
theorem abs_centroid_sub_centroid_le {A B : Finset (Fin m → ℝ)} {M : Fin m → ℝ}
    (hA : A.Nonempty) (hAB : A ⊆ B) (hbox : ∀ x ∈ B, ∀ k, 0 ≤ x k ∧ x k ≤ M k) (k : Fin m) :
    |centroid A k - centroid B k| ≤ (1 - (A.card : ℝ) / B.card) * M k := by
  classical
  have := abs_avg_sub_avg_le (g := fun x : Fin m → ℝ => x k) (m := 0) (M := M k) hA hAB
    (fun x hx => (hbox x hx k).1) (fun x hx => (hbox x hx k).2)
  simpa [centroid] using this

/-- The mixing lemma for one second moment. -/
theorem abs_secondMoment_sub_le {A B : Finset (Fin m → ℝ)} {M : Fin m → ℝ}
    (hA : A.Nonempty) (hAB : A ⊆ B) (hbox : ∀ x ∈ B, ∀ k, 0 ≤ x k ∧ x k ≤ M k) (k l : Fin m) :
    |avg A (fun x => x k * x l) - avg B (fun x => x k * x l)| ≤
      (1 - (A.card : ℝ) / B.card) * (M k * M l) := by
  classical
  have := abs_avg_sub_avg_le (g := fun x : Fin m → ℝ => x k * x l) (m := 0) (M := M k * M l)
    hA hAB (fun x hx => mul_nonneg (hbox x hx k).1 (hbox x hx l).1)
    (fun x hx => mul_le_mul (hbox x hx k).2 (hbox x hx l).2 (hbox x hx l).1
      ((hbox x hx k).1.trans (hbox x hx k).2))
  simpa using this

/-- The mixing lemma for one covariance entry, with constant `3`. -/
theorem abs_cov_sub_cov_le {A B : Finset (Fin m → ℝ)} {M : Fin m → ℝ}
    (hA : A.Nonempty) (hAB : A ⊆ B) (hbox : ∀ x ∈ B, ∀ k, 0 ≤ x k ∧ x k ≤ M k) (k l : Fin m) :
    |cov A k l - cov B k l| ≤ 3 * (1 - (A.card : ℝ) / B.card) * (M k * M l) := by
  have hB : B.Nonempty := hA.mono hAB
  have hboxA : ∀ x ∈ A, ∀ k, 0 ≤ x k ∧ x k ≤ M k := fun x hx => hbox x (hAB hx)
  have h2 := abs_secondMoment_sub_le hA hAB hbox k l
  have hk := abs_centroid_sub_centroid_le hA hAB hbox k
  have hl := abs_centroid_sub_centroid_le hA hAB hbox l
  have cAk := centroid_mem_Icc hA hboxA k
  have cBl := centroid_mem_Icc hB hbox l
  have hMk : 0 ≤ M k := cAk.1.trans cAk.2
  have hMl : 0 ≤ M l := cBl.1.trans cBl.2
  set f := 1 - (A.card : ℝ) / B.card
  have hY : |centroid A k * (centroid A l - centroid B l)| ≤ M k * (f * M l) := by
    rw [abs_mul, abs_of_nonneg cAk.1]
    exact mul_le_mul cAk.2 hl (abs_nonneg _) hMk
  have hZ : |centroid B l * (centroid A k - centroid B k)| ≤ M l * (f * M k) := by
    rw [abs_mul, abs_of_nonneg cBl.1]
    exact mul_le_mul cBl.2 hk (abs_nonneg _) hMl
  have e : cov A k l - cov B k l =
      (avg A (fun x => x k * x l) - avg B (fun x => x k * x l)) -
        (centroid A k * (centroid A l - centroid B l) +
          centroid B l * (centroid A k - centroid B k)) := by
    unfold cov; ring
  rw [e]
  calc _ ≤ |avg A (fun x => x k * x l) - avg B (fun x => x k * x l)| +
        (|centroid A k * (centroid A l - centroid B l)| +
          |centroid B l * (centroid A k - centroid B k)|) :=
        (abs_sub _ _).trans (add_le_add le_rfl (abs_add_le _ _))
    _ ≤ f * (M k * M l) + (M k * (f * M l) + M l * (f * M k)) :=
        add_le_add h2 (add_le_add hY hZ)
    _ = 3 * f * (M k * M l) := by ring

/-! ### Dilation limits -/

/-- **Abstract dilation limit.** If `A_r ⊆ B_r`, every point of `B_r` lies in `∏ [0, r M_k]`, the
fill rate `|A_r|/|B_r|` tends to `1` and `c(B_r)_k / r → c_k`, then `c(A_r)_k / r → c_k`. -/
theorem tendsto_centroid_div (A B : ℕ → Finset (Fin m → ℝ)) (M c : Fin m → ℝ)
    (hA : ∀ r, (A r).Nonempty) (hAB : ∀ r, A r ⊆ B r)
    (hbox : ∀ r : ℕ, ∀ x ∈ B r, ∀ k, 0 ≤ x k ∧ x k ≤ r * M k)
    (hfill : Tendsto (fun r => ((A r).card : ℝ) / (B r).card) atTop (𝓝 1))
    (k : Fin m) (hB : Tendsto (fun r : ℕ => centroid (B r) k / r) atTop (𝓝 (c k))) :
    Tendsto (fun r : ℕ => centroid (A r) k / r) atTop (𝓝 (c k)) := by
  have hbound : Tendsto (fun r => (1 - ((A r).card : ℝ) / (B r).card) * M k) atTop (𝓝 0) := by
    simpa using ((tendsto_const_nhds (x := (1 : ℝ))).sub hfill).mul_const (M k)
  have hdiff : Tendsto (fun r : ℕ => centroid (A r) k / r - centroid (B r) k / r) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hbound
    filter_upwards [eventually_ge_atTop 1] with r hr
    have hr' : (0 : ℝ) < r := by exact_mod_cast hr
    have h := abs_centroid_sub_centroid_le (M := fun j => (r : ℝ) * M j) (hA r) (hAB r)
      (hbox r) k
    rw [Real.norm_eq_abs, ← sub_div, abs_div, abs_of_pos hr', div_le_iff₀ hr']
    calc _ ≤ _ := h
      _ = _ := by ring
  simpa using hdiff.add hB

/-- **Abstract dilation estimate, one `r`.** If `1 − |A|/|B| ≤ K/r` and `|c(B)_k/r − c_k| ≤ K'/r`,
and every point of `B` lies in `∏ [0, r M_k]`, then `|c(A)_k/r − c_k| ≤ (K M_k + K')/r`. -/
theorem abs_centroid_div_sub_le {A B : Finset (Fin m → ℝ)} {M c : Fin m → ℝ} {r K K' : ℝ}
    (hr : 0 < r) (hA : A.Nonempty) (hAB : A ⊆ B) (hbox : ∀ x ∈ B, ∀ k, 0 ≤ x k ∧ x k ≤ r * M k)
    (k : Fin m) (hfill : 1 - (A.card : ℝ) / B.card ≤ K / r)
    (hBk : |centroid B k / r - c k| ≤ K' / r) :
    |centroid A k / r - c k| ≤ (K * M k + K') / r := by
  obtain ⟨x, hx⟩ := hA
  have hMk : 0 ≤ M k := by
    have h := hbox x (hAB hx) k
    exact nonneg_of_mul_nonneg_right (h.1.trans h.2) hr
  have h := abs_centroid_sub_centroid_le (M := fun j => r * M j) ⟨x, hx⟩ hAB hbox k
  have h1 : |centroid A k / r - centroid B k / r| ≤ K * M k / r := by
    rw [← sub_div, abs_div, abs_of_pos hr, div_le_div_iff_of_pos_right hr]
    calc _ ≤ (1 - (A.card : ℝ) / B.card) * (r * M k) := h
      _ = r * ((1 - (A.card : ℝ) / B.card) * M k) := by ring
      _ ≤ r * (K / r * M k) := by gcongr
      _ = K * M k := by field_simp
  calc _ = |(centroid A k / r - centroid B k / r) + (centroid B k / r - c k)| := by ring_nf
    _ ≤ |centroid A k / r - centroid B k / r| + |centroid B k / r - c k| := abs_add_le _ _
    _ ≤ K * M k / r + K' / r := add_le_add h1 hBk
    _ = (K * M k + K') / r := by ring

/-- A polynomial of degree at most that of `Q` is eventually bounded by a constant times `|Q|`,
along the natural numbers. -/
lemma exists_bound_of_degree_le {P Q : ℝ[X]} (h : P.degree ≤ Q.degree) :
    ∃ K : ℝ, ∀ᶠ r : ℕ in atTop, |P.eval (r : ℝ)| ≤ K * |Q.eval (r : ℝ)| := by
  obtain ⟨K, hK⟩ := (Polynomial.isBigO_atTop_of_degree_le P Q h).bound
  exact ⟨K, (tendsto_natCast_atTop_atTop.eventually hK).mono fun r hr => by
    simpa [Real.norm_eq_abs] using hr⟩

/-- **The dilation estimate from polynomial counts.** Let `A_r ⊆ B_r` be finite non-empty sets of
points of `ℝ^m`, with every point of `B_r` in `∏ [0, r M_k]`. Suppose `|A_r| = a(r)`,
`|B_r| = L(r)` and `∑_{x ∈ B_r} x_k = S_k(r)` for real polynomials `a`, `L`, `S_k` with
`deg (X·(L − a)) ≤ deg L` (so `1 − fill = O(1/r)`) and `deg (S_k − c_k·X·L) ≤ deg L`
(so `c(B_r)_k / r = c_k + O(1/r)`). Then `|c(A_r)_k / r − c_k| ≤ K/r` for all large `r`. -/
theorem centroid_dilation_rate (A B : ℕ → Finset (Fin m → ℝ)) (M c : Fin m → ℝ)
    (hA : ∀ r, (A r).Nonempty) (hAB : ∀ r, A r ⊆ B r)
    (hbox : ∀ r : ℕ, ∀ x ∈ B r, ∀ k, 0 ≤ x k ∧ x k ≤ r * M k)
    (a L : ℝ[X]) (ha : ∀ r : ℕ, ((A r).card : ℝ) = a.eval (r : ℝ))
    (hL : ∀ r : ℕ, ((B r).card : ℝ) = L.eval (r : ℝ))
    (haL : (X * (L - a)).degree ≤ L.degree)
    (S : Fin m → ℝ[X]) (hS : ∀ r : ℕ, ∀ k, ∑ x ∈ B r, x k = (S k).eval (r : ℝ))
    (hSL : ∀ k, (S k - C (c k) * X * L).degree ≤ L.degree) (k : Fin m) :
    ∃ K : ℝ, ∀ᶠ r : ℕ in atTop, |centroid (A r) k / r - c k| ≤ K / r := by
  obtain ⟨K₁, hK₁⟩ := exists_bound_of_degree_le haL
  obtain ⟨K₂, hK₂⟩ := exists_bound_of_degree_le (hSL k)
  refine ⟨K₁ * M k + K₂, ?_⟩
  filter_upwards [hK₁, hK₂, eventually_ge_atTop 1] with r h1 h2 hr
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hLpos : (0 : ℝ) < L.eval (r : ℝ) := by
    rw [← hL r]; exact_mod_cast ((hA r).mono (hAB r)).card_pos
  simp only [eval_mul, eval_X, eval_sub, eval_C] at h1 h2
  rw [abs_of_pos hLpos] at h1 h2
  apply abs_centroid_div_sub_le hr' (hA r) (hAB r) (hbox r) k
  · -- the fill rate: `1 − a/L = (L − a)/L ≤ K₁/r`
    rw [ha r, hL r, one_sub_div hLpos.ne', div_le_div_iff₀ hLpos hr']
    have := (le_abs_self _).trans h1
    nlinarith
  · -- the centroid of `B_r`: `|S/(L r) − c| = |S − c r L|/(r L) ≤ K₂/r`
    have hc : centroid (B r) k = (S k).eval (r : ℝ) / L.eval (r : ℝ) := by
      simp only [centroid, avg]; rw [hS r k, hL r]
    rw [hc]
    have e : (S k).eval (r : ℝ) / L.eval (r : ℝ) / r - c k =
        ((S k).eval (r : ℝ) - c k * r * L.eval (r : ℝ)) / L.eval (r : ℝ) / r := by
      field_simp
    rw [e, abs_div, abs_div, abs_of_pos hLpos, abs_of_pos hr',
      div_le_div_iff_of_pos_right hr', div_le_iff₀ hLpos]
    exact h2

/-- The limit statement of `cor-centroid-dilation`, from polynomial counts. -/
theorem centroid_dilation_tendsto (A B : ℕ → Finset (Fin m → ℝ)) (M c : Fin m → ℝ)
    (hA : ∀ r, (A r).Nonempty) (hAB : ∀ r, A r ⊆ B r)
    (hbox : ∀ r : ℕ, ∀ x ∈ B r, ∀ k, 0 ≤ x k ∧ x k ≤ r * M k)
    (a L : ℝ[X]) (ha : ∀ r : ℕ, ((A r).card : ℝ) = a.eval (r : ℝ))
    (hL : ∀ r : ℕ, ((B r).card : ℝ) = L.eval (r : ℝ))
    (haL : (X * (L - a)).degree ≤ L.degree)
    (S : Fin m → ℝ[X]) (hS : ∀ r : ℕ, ∀ k, ∑ x ∈ B r, x k = (S k).eval (r : ℝ))
    (hSL : ∀ k, (S k - C (c k) * X * L).degree ≤ L.degree) (k : Fin m) :
    Tendsto (fun r : ℕ => centroid (A r) k / r) atTop (𝓝 (c k)) := by
  obtain ⟨K, hK⟩ := centroid_dilation_rate A B M c hA hAB hbox a L ha hL haL S hS hSL k
  have h0 : Tendsto (fun r : ℕ => K / (r : ℝ)) atTop (𝓝 0) :=
    tendsto_const_div_atTop_nhds_zero_nat K
  have hd : Tendsto (fun r : ℕ => centroid (A r) k / r - c k) atTop (𝓝 0) :=
    squeeze_zero_norm' (hK.mono fun r hr => by simpa [Real.norm_eq_abs] using hr) h0
  simpa using hd.add_const (c k)

end CentroidDilation
end ExteriorConvex

#print axioms ExteriorConvex.CentroidDilation.abs_avg_sub_avg_le
#print axioms ExteriorConvex.CentroidDilation.abs_centroid_sub_centroid_le
#print axioms ExteriorConvex.CentroidDilation.abs_secondMoment_sub_le
#print axioms ExteriorConvex.CentroidDilation.abs_cov_sub_cov_le
#print axioms ExteriorConvex.CentroidDilation.tendsto_centroid_div
#print axioms ExteriorConvex.CentroidDilation.abs_centroid_div_sub_le
#print axioms ExteriorConvex.CentroidDilation.centroid_dilation_rate
#print axioms ExteriorConvex.CentroidDilation.centroid_dilation_tendsto
