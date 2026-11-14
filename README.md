# Hilbert functions over the exterior algebra and *f*-vectors in higher rank

This is a series of research articles by Jan Snellman (Department of Mathematics, Linköping
University; ORCID [0009-0002-6676-5068](https://orcid.org/0009-0002-6676-5068)). The repository
holds:

- the articles themselves;
- a **Lean 4 formalization** of their combinatorial core, with no `sorry` and no axioms beyond
  Lean's standard three;
- the **verification code** behind every computational claim in the articles, with recorded
  output;
- for each article, a **reference certificate** showing that every work it cites exists and says
  what it is cited for.

## What the series is about

Let E = ⋀(kⁿ) be the exterior algebra on n generators, and let F = E g₁ ⊕ ⋯ ⊕ E gᵣ be a graded
free E-module with deg gᵢ = dᵢ. The series studies the Hilbert functions of the quotients F/M,
where M runs over the proper monomial submodules of Amata and Crupi.

Their convex hull turns out to be a Minkowski sum of r copies of one and the same simplex Koz(n),
the i-th copy shifted dᵢ steps in degree. Koz(n) is the **Kozlov simplex**: the (n−1)-simplex
that Kozlov proved in 1997 to be the convex hull of the *f*-vectors of simplicial complexes on n
vertices. At r = 1 the statement *is* Kozlov's theorem, so the series generalizes that theorem to
rank r.

- **Part I** proves this, self-contained. Along the way it gives a short proof of Kozlov's theorem
  from the local Lubell–Yamamoto–Meshalkin (LYM) inequality, and a facet description of Koz(n)
  that appears not to be recorded in the literature.
- **Part II** counts the Hilbert functions. For r = 1 the count is Linusson's; at every rank it is
  a product of transfer matrices whose entries come from Linusson's refined counts.
- **Part III** studies the lattice points of the polytope. Koz(n) is a lecture hall simplex, the
  polytope has the integer decomposition property, and its lattice-point counts and Ehrhart
  polynomials are again products of transfer matrices.

## The articles

**Part I.** *Hilbert functions over the exterior algebra and f-vectors in higher rank, I:
Amata–Crupi monomial modules, Kozlov polytopes, and r-vectors of simplicial complexes.*

- arXiv: [2609.23605](https://arxiv.org/abs/2609.23605) (math.CO, cross-listed to math.AC).
- Also published as report LiTH-MAT-R 2026:04, in the report series of the Department of
  Mathematics, Linköping University (Linköping University Electronic Press, ISSN 0348-2960),
  DOI [10.3384/LiTH-MAT-R-2026-04](https://doi.org/10.3384/LiTH-MAT-R-2026-04). The full text is
  open access through
  [DiVA](https://liu.diva-portal.org/smash/record.jsf?pid=diva2%3A2102721), Linköping
  University's publication database.
- Sources here: [`articles/article-1/`](articles/article-1/).

**Part II.** *Hilbert functions over the exterior algebra and f-vectors in higher rank, II:
Generalizing Linusson's count to sumsets of f-vectors.*

- arXiv: [2610.14985](https://arxiv.org/abs/2610.14985) (math.CO).
- Sources here: [`articles/article-2/`](articles/article-2/).

**Part III.** *Hilbert functions over the exterior algebra and f-vectors in higher rank, III:
Lattice points of the Kozlov polytope.*

- Not yet released. It will appear on arXiv and in the LiTH-MAT-R series shortly.
- [`articles/article-3/`](articles/article-3/) holds the pre-release version. Its PDF still
  carries proof-reading labels in the margin, which the released version will not have.

**Parts IV and V** are in preparation. Part IV treats the vertices and facets of the Kozlov
polytope at every rank.

The arXiv versions are the ones to read and cite. For Parts I and II, the package exactly as
submitted to arXiv is in `articles/article-N/arxiv-submission/`, and it builds with pdfLaTeX.

### How to cite

```bibtex
@techreport{Snellman2026ExtI,
  author      = {Snellman, Jan},
  title       = {Hilbert functions over the exterior algebra and $f$-vectors in higher rank,
                 {I}: {A}mata--{C}rupi monomial modules, {K}ozlov polytopes, and $r$-vectors of
                 simplicial complexes},
  institution = {Link{\"o}ping University Electronic Press},
  type        = {LiTH-MAT-R},
  number      = {2026:04},
  year        = {2026},
  doi         = {10.3384/LiTH-MAT-R-2026-04},
  eprint      = {2609.23605},
  eprinttype  = {arxiv}
}

@misc{Snellman2026ExtII,
  author      = {Snellman, Jan},
  title       = {Hilbert functions over the exterior algebra and $f$-vectors in higher rank,
                 {II}: Generalizing {L}inusson's count to sumsets of $f$-vectors},
  year        = {2026},
  eprint      = {2610.14985},
  eprinttype  = {arxiv},
  eprintclass = {math.CO}
}
```

## What is in this repository

- [`articles/`](articles/): one directory per article. Each holds the Org source, which is where
  the text is written, together with the LaTeX generated from it and the built PDF.
- [`lean/`](lean/): the Lean 4 + Mathlib formalization ([below](#the-lean-formalization)).
- [`verification-code/`](verification-code/): the SageMath, Macaulay2 and Python checks, with
  their recorded output in `verification-code/runs/` ([below](#the-verification-code)).
- [`references/`](references/): the BibTeX database, and one reference certificate per article
  ([below](#reference-certificates)).
- [`STRUCTURE.md`](STRUCTURE.md): the detailed file layout, and how this repository is produced
  from the author's working copy. You only need it if you want to know where a particular file
  comes from.

## The Lean formalization

[`lean/`](lean/) is a standalone Lake project: **sixty files, about 25,500 lines, no `sorry`, no
custom axioms.** It is organized by theme rather than by article, because the same core serves
every part. **[`lean/README.md`](lean/README.md) is the authoritative record** of what is and is
not proved: it maps each numbered statement in the articles to its Lean declaration. Part III
also prints that record in its own margin: a disc beside each numbered result says whether it is
formalized fully, under a cited hypothesis, in part, or not at all.

What it covers:

- **The combinatorial core** (Part I, §§4–6): the local LYM inequality; the chain description of
  the Kozlov simplex; **Kozlov's theorem** itself; the sumset identity in its combinatorial form;
  the **main theorem** at every rank; and the variant under the permissive convention, in full.
- **The rank-two vertex structure** (Part I, §9 and Appendix A): the vertex criterion, the
  extremal matrix for both the all-ones and the Kozlov leg vector, and the vertex count.
- **The counting layer** (Part II, §§4–9): the two statistics and the matrix of their joint
  distribution, Alexander duality and persymmetry, the chaining and transfer results, the exact
  degrees at δ = 0, the proper variant, and the constant-gap recurrence.
- **Lattice points and symmetry** (Part III): the lattice points of the Kozlov polytope and of
  its dilates, the volume, the involution and the centroids. Two results are formalized in part:
  the limit of the centroid under dilation, and the volume side of Kupreyeva's limit.
- **Vertices and facets at every rank, and a Kruskal–Katona theorem for modules**: material for
  Parts IV and V.

**The printed proofs and the formal ones are the same proofs**, deliberately. Where the
formalization found a shorter route, the article was rewritten to take it. Remark
`rem-no-support-functions` in Part I records one such case, where formalizing made a citation
unnecessary.

**What is not formalized is stated explicitly**, in `lean/README.md` and in each file's header.
In particular:

- the two conjectured H-descriptions (they are conjectures, and would need the Minkowski–Weyl
  theorem, which Mathlib lacks);
- the three propositions about degenerate cases;
- the affine-independence halves of two lemmas, and hence the claims of two statements that
  certain inequalities define facets (the inequalities themselves *are* proved);
- the projected forms of the statements in Part I, §§4–6 (the formalization works throughout in
  coordinates that include degree 0);
- the algebraic half of the sumset identity. So the formal main theorem is the combinatorial
  identity, not the statement about modules.

### Checking it yourself

You need [`elan`](https://github.com/leanprover/elan). It fetches the Lean toolchain named in
`lean/lean-toolchain` automatically.

```sh
cd lean
lake exe cache get     # download Mathlib's prebuilt files; minutes, not hours
lake build
```

A clean build ends with `Build completed successfully` and no `error:`. The warnings are Mathlib
deprecations (mostly `if_pos`/`if_neg`) and linter notes (unused `simp` arguments and variables).
None is an error, and none concerns `sorry`. Last checked 2026-11-14: 8,865 jobs, 0 errors.

To confirm that nothing is hidden:

```sh
grep -rn sorry ExteriorConvex/          # expect no matches
```

For the axiom check, run the following in `lake env lean` or in an editor. The declarations live
in the `ExteriorConvex` namespace: `kozlov` is Kozlov's theorem, `main` the main theorem at rank
r, and `permissive_fibres` the result under the permissive convention.

```lean
import ExteriorConvex
#print axioms ExteriorConvex.kozlov
#print axioms ExteriorConvex.main
#print axioms ExteriorConvex.permissive_fibres
```

Each should print exactly `[propext, Classical.choice, Quot.sound]`: Lean's three standard
foundational axioms, and nothing else. **In particular `Lean.ofReduceBool` must never appear.**
It is the axiom that the `native_decide` tactic introduces. A single use of that tactic anywhere
in the import graph would invalidate the axiom claim for the whole development, and its use is
forbidden here (see `ExteriorConvex/Spine/Permissive.lean`).

## The verification code

[`verification-code/`](verification-code/) holds every SageMath, Macaulay2 and Python script
behind a computational claim in the articles, with the recorded output of each run under
`verification-code/runs/`. These are the informal checks: exact polyhedral computation,
exhaustive enumeration of small cases, brute force. They were run alongside the Lean
formalization and the proofs, and often ahead of them. The Lean development is the
machine-checked core; this is everything around it.

**Start from the article, not from the scripts.** Each article has a section that maps its
computational claims to the code:

- Part I, §10, *Methods*;
- Part II, §10, *Verification, tables, and open problems*;
- Part III, §9, *Methods and verification*.

Each of these states, claim by claim, what was checked, over what range, and by which script.

In `verification-code/`, the top level holds the reusable modules (`right_angle_simplex.py`,
`minkowski_tensor.py`, …), and `oneoff/` holds the single-purpose scripts, each named for what it
checks (e.g. `close_gap3_explicit_functional.sage`). `runs/` is organized into one subdirectory
per series of runs, and [`runs/README.md`](verification-code/runs/README.md) says what is where.
Comments and READMEs inside `verification-code/` call the directory `code/`, its name in the
author's working copy.

Each script is standalone and prints its own PASS/FAIL summary. To run them:

```sh
# Python-only checks (no special mathematical software needed):
python3 verification-code/<script>.py

# SageMath checks (exact polytopes, face lattices); needs a Sage installation:
sage verification-code/oneoff/<script>.sage

# Macaulay2 checks (Hilbert functions of exterior monomial modules); needs Macaulay2
# with Amata and Crupi's ExteriorIdeals/ExteriorModules packages, which ship with it:
M2 --script verification-code/oneoff/<script>.m2
```

The recorded outputs in `verification-code/runs/` let you compare against a known-good run
without executing anything. A few of the heavier Sage jobs (enumerating face lattices) need a lot
of memory and are best run one at a time.

## Reference certificates

[`references/`](references/) holds one certificate per article:

- [`REFERENCE-CERTIFICATE.md`](references/REFERENCE-CERTIFICATE.md) for Part I;
- [`REFERENCE-CERTIFICATE-article2.md`](references/REFERENCE-CERTIFICATE-article2.md) for Part II;
- [`REFERENCE-CERTIFICATE-article3.md`](references/REFERENCE-CERTIFICATE-article3.md) for Part III.

For every work the article cites, a certificate gives the full bibliographic entry and the claim
it supports. It then either quotes the source verbatim, with page or theorem number, from a copy
the author holds, or says plainly that no copy was available and records the check made instead
against the DOI and the bibliographic databases.

The articles were written with substantial AI assistance, disclosed in their acknowledgements.
arXiv treats fabricated references as grounds for banning a submitter. So it is part of the work
to show, checkably, that every reference is a real publication that says what it is cited for.
Parts I and II carry their certificates on arXiv as ancillary files, and Part III will too.

## What is not here

- **The cited literature.** The certificates quote from it, but the PDFs are left out for
  copyright reasons.
- **Work towards later parts that is not yet written up**, such as the fibres of the sum map.

## Licence

Copyright © 2026 Jan Snellman. Two licences, split the usual way:

- **Code**: the Lean formalization (`lean/`) and the verification code (`verification-code/`,
  including the copies in the arXiv packages' `anc/` directories) are under the **MIT License**;
  see [`LICENSE`](LICENSE).
- **Text**: the articles (`articles/`), the reference certificates and the READMEs are under
  **Creative Commons Attribution 4.0 International (CC BY 4.0)**; see
  [`LICENSE-CC-BY-4.0`](LICENSE-CC-BY-4.0).

The passages that the certificates quote from cited works remain their authors' and publishers'.
They are quoted only as evidence of what each work says.
