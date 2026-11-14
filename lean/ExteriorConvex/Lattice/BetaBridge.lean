/-
Copyright (c) 2026 Jan Snellman. All rights reserved.

# Reconciling the two definitions of `𝓛_n`

Two files define the lattice points `𝓛_n = Koz(n) ∩ ℤ^{n+1}` of article 3 (§`sec-setup`),
in the same degree-0-inclusive coordinates:

* `Lattice.latticePts n : Set (Fin (n + 1) → ℤ)` (`Lattice/LatticePoints.lean`): integer
  vectors whose real image lies in `conv(S_n)`;
* `Beta.latticePts n : Set (Fin (n + 1) → ℝ)` (`Symmetry/Beta.lean`): real points of
  `conv(skelSet n)` all of whose coordinates are integers.

`beta_latticePts_eq_image` says they agree for `n ≥ 1`: the second is the image of the first
under the cast `castR`, which is injective (`castR_injective`). The only mathematical input
is `kozlov` (`conv(S_n) = conv{F̃_j}`).

Kept in its own file so that neither `LatticePoints.lean` nor `Beta.lean` imports the other.

Changelog (newest first): 2026-10-21 created (Claude-Code agent)
-/
import Mathlib
import ExteriorConvex.Lattice.LatticePoints
import ExteriorConvex.Symmetry.Beta

namespace ExteriorConvex

namespace Lattice

variable {n : ℕ}

/-- The two definitions of `𝓛_n` agree: `Beta.latticePts n = castR '' latticePts n`. -/
theorem beta_latticePts_eq_image (hn : 1 ≤ n) :
    Beta.latticePts n = castR '' latticePts n := by
  ext x
  constructor
  · rintro ⟨hx, hint⟩
    choose z hz using hint
    have hxz : x = castR z := funext fun i => hz i
    refine ⟨z, ?_, hxz.symm⟩
    show castR z ∈ convexHull ℝ (Sset n)
    rw [kozlov hn, ← hxz]
    exact hx
  · rintro ⟨z, hz, rfl⟩
    refine ⟨?_, fun i => ⟨z i, rfl⟩⟩
    have : castR z ∈ convexHull ℝ (Sset n) := hz
    rwa [kozlov hn] at this

/-- Membership form: an integer vector is in `Lattice.latticePts n` iff its cast is in
`Beta.latticePts n`. -/
theorem castR_mem_beta_latticePts_iff (hn : 1 ≤ n) (z : Fin (n + 1) → ℤ) :
    castR z ∈ Beta.latticePts n ↔ z ∈ latticePts n := by
  rw [beta_latticePts_eq_image hn]
  exact castR_injective.mem_set_image

end Lattice

end ExteriorConvex
