# exterior-convex

**Hilbert functions over the exterior algebra and $f$-vectors in higher rank** — a series of
articles (Parts I–III here; Parts IV and V are in preparation), the Lean 4 formalization of their
combinatorial core, the code behind every computational claim, and a reference certificate for each
part.

Let $E=\bigwedge(k^n)$ be the exterior algebra on $n$ generators and $F=\bigoplus_{i=1}^{r}Eg_i$ a
graded free $E$-module with $\deg g_i=d_i$. The series determines the convex hull of the set of
Hilbert functions of the quotients $F/M$, where $M$ runs over the monomial submodules of Amata and
Crupi. The hull is a Minkowski sum

$$\mathrm{Koz}(n;d_1,\dots,d_r)\;=\;\sum_{i=1}^{r}\mathrm{shift}^{d_i}\bigl(\mathrm{Koz}(n)\bigr)$$

of $r$ shifted copies of one and the same **Kozlov simplex** $\mathrm{Koz}(n)$ — the $(n-1)$-simplex
that Kozlov proved in 1997 to be the convex hull of the $f$-vectors of simplicial complexes on $n$
vertices. At $r=1$ the statement *is* Kozlov's theorem, so the series is a rank-$r$ generalization of
it, and Part I gives a self-contained proof including a short proof of Kozlov's theorem from the local
Lubell–Yamamoto–Meshalkin inequality and a facet description of $\mathrm{Koz}(n)$ that appears not to
be recorded in the literature.

## Published versions

Parts I and II are published, open access, both on arXiv and as technical reports in Linköping
University's mathematics report series (LiTH-MAT-R, ISSN 0348-2960, Linköping University Electronic
Press).

**Part I.** Jan Snellman, *Hilbert functions over the exterior algebra and $f$-vectors in higher
rank I: Amata–Crupi monomial modules, Kozlov polytopes, and $r$-vectors of simplicial complexes.*

- LiTH-MAT-R No. 2026:04, 2026-09-18. DOI:
  [10.3384/LiTH-MAT-R-2026-04](https://doi.org/10.3384/LiTH-MAT-R-2026-04); full text via the DiVA
  record [urn:nbn:se:liu:diva-227730](https://urn.kb.se/resolve?urn=urn:nbn:se:liu:diva-227730)
  ([record page](https://liu.diva-portal.org/smash/record.jsf?pid=diva2%3A2102721)).
- arXiv: [2609.23605](https://arxiv.org/abs/2609.23605) (math.CO, cross-listed to math.AC). The
  submitted package is in [`articles/article-1/arxiv-submission/`](articles/article-1/arxiv-submission/).

**Part II.** Jan Snellman, *Hilbert functions over the exterior algebra and $f$-vectors in higher
rank II: Generalizing Linusson's count to sumsets of $f$-vectors.*

- arXiv: [2610.14985](https://arxiv.org/abs/2610.14985) (math.CO), submitted 2026-10-10. The
  submitted package is in [`articles/article-2/arxiv-submission/`](articles/article-2/arxiv-submission/).
- LiTH-MAT-R: REPORT-NUMBER-PENDING. Part II went to arXiv first, so the report cites the arXiv
  version rather than the other way round.

**Part III**, *III: Lattice points of the Kozlov polytope*, is finished in draft and will be released
the same way shortly; the version here (`articles/article-3/`) is the pre-release one, and its PDF
still carries the proof-reading labels in the margin.

## Layout

| directory | contents |
|---|---|
| `articles/article-1/` | *I: Amata–Crupi monomial modules, Kozlov polytopes, and $r$-vectors of simplicial complexes.* The Org source, the exported LaTeX, and the built PDF. The `.org` is the source of truth; the `.tex` is generated from it. |
| `articles/article-2/` | *II: Generalizing Linusson's count to sumsets of $f$-vectors.* `_latest`, the version prepared for arXiv: Org source, LaTeX and PDF; `arxiv-submission/`, the arXiv package (pdfLaTeX, with `anc/` holding the Lean development, the verification code and CSV tables of the counts); and `ARXIV-SUBMISSION-METADATA.md`, the form fields. |
| `articles/article-3/` | *III: Lattice points of the Kozlov polytope.* `_latest`, the pre-release version: Org source, LaTeX and PDF, with the figures in `img/`. The `.tex` builds in place (`xelatex`, `biber`, `xelatex` twice). The margin carries two kinds of mark: a disc beside each numbered result says whether it is formalised in Lean (the legend is in §1), and the boxed labels are proof-reading aids that the released version drops. |
| `lean/` | the Lean 4 + Mathlib formalization — see below |
| `verification-code/` | every SageMath, Macaulay2 and Python script behind a computational claim, with the recorded output of the runs under `verification-code/runs/` |
| `references/` | the BibTeX database; the certificates of existence for every citation, one per part: **`REFERENCE-CERTIFICATE.md`** (Part I), **`REFERENCE-CERTIFICATE-article2.md`** and **`REFERENCE-CERTIFICATE-article3.md`** (see below); and `CITATIONS-TO-VERIFY.md`, the discharged worklist the first grew from |

Each article's methods section (Part I §10, *Methods*; Part II §10, *Verification, tables, and open
problems*; Part III §9, *Methods and verification*) is the index
into `verification-code/`: it states, claim by claim, what was checked, over what range, and by which
script. Read that before reading the scripts.

## The Lean formalization

`lean/` is a standalone Lake project: **sixty files, about 25,500 lines, no `sorry`, no custom
axioms.** It is organized thematically rather than per article, since the spine serves every part;
`lean/README.md` carries the declaration-by-declaration correspondence to the manuscripts' numbered
statements. That file, not this one, is the authoritative record of what is and is not proved. In
Part III the same record is printed in the margin: each numbered result carries a disc saying whether
it is formalised fully, under a cited hypothesis, in part, or not at all.

- **The combinatorial spine** (article 1, §§4–6 and §5.1): local LYM; the chain description of the
  Kozlov simplex; **Kozlov's theorem** itself; the sumset identity in its combinatorial form; the
  **main theorem** at every rank; and the permissive-convention variant in full.
- **The rank-two vertex structure** (§9 and Appendix A): the vertex criterion, the extremal matrix for
  both the all-ones and the Kozlov leg vector, and the vertex count.
- **The counting layer** (article 2, §§4–9): the two statistics and their joint-distribution matrix,
  Alexander duality and persymmetry, the chaining/transfer layer, the exact `δ = 0` degrees, the
  proper variant, and the constant-gap recurrence.
- **Lattice points and symmetry** (article 3; `Lattice/`, `Symmetry/`, `Centroid/`, `Kupreyeva/`):
  the lattice points of the Kozlov polytope and their dilates, the volume, the involution and the
  centroids, the dilation limit of the centroid (in part), and the volume side of Kupreyeva's limit
  (in part).
- **Vertices and facets at every rank, and the module Kruskal–Katona theorem** (`Vertices/`,
  `Facets/`, `AllOnes/`, `ModuleKK/`): material of Parts IV and V, which are in preparation.

Two things are worth knowing before reading it.

**The printed proofs and the formal ones are the same proofs**, deliberately. Where the formalization
found a shorter route, the manuscript was rewritten to take it — `rem-no-support-functions` in article
1 records one such case, where formalizing removed a citation the printed proof no longer needs.

**What is not formalized is stated explicitly**, in `lean/README.md` and in each file's header. In
particular: the two H-description conjectures (they are conjectures, and would need Minkowski–Weyl,
which Mathlib lacks); the three degenerate-regime propositions; the affine-independence halves of two
lemmas, hence the *facet-status* halves of two statements whose halfspace descriptions *are* proved;
the projected forms of the §§4–6 statements, the formalization working throughout in
degree-$0$-inclusive coordinates; and the algebraic half of the sumset identity — so the formal main
theorem is the combinatorial identity, not the module-theoretic one.

### Checking it yourself

You need [`elan`](https://github.com/leanprover/elan); it will fetch the toolchain named in
`lean/lean-toolchain` automatically.

```sh
cd lean
lake exe cache get     # download Mathlib's prebuilt oleans -- minutes, not hours
lake build
```

A clean build ends with `Build completed successfully` and no `error:`. The warnings are Mathlib
deprecations (mostly `if_pos`/`if_neg`) and linter notes (unused `simp` arguments and variables);
none is an error, and none concerns `sorry`. Last checked 2026-11-14: 8,865 jobs, 0 errors.

To confirm there is nothing hidden in it:

```sh
grep -rn sorry ExteriorConvex/          # expect no matches
```

and, for the axiom check, in `lake env lean` or an editor (the declarations live in the
`ExteriorConvex` namespace; `kozlov` is Kozlov's theorem, `main` the rank-$r$ main theorem, and
`permissive_fibres` the permissive-convention prize):

```lean
import ExteriorConvex
#print axioms ExteriorConvex.kozlov
#print axioms ExteriorConvex.main
#print axioms ExteriorConvex.permissive_fibres
```

Each should print exactly `[propext, Classical.choice, Quot.sound]` — Lean's three standard
foundational axioms, and nothing else. **In particular `Lean.ofReduceBool` must never appear**: it is
the axiom `native_decide` introduces, and a single use of that tactic anywhere in the import graph
would invalidate the axiom claim for the whole development. There is a standing prohibition on it,
recorded in `ExteriorConvex/Spine/Permissive.lean`.

## The verification code

`verification-code/` holds every SageMath, Macaulay2 and Python script behind a computational claim
in the articles, with the recorded output of each run under `verification-code/runs/`. These are the
*informal* checks — exact polyhedral computation, exhaustive small-case enumeration, brute force —
that were run alongside (and often ahead of) the Lean formalization and the paper's proofs; the Lean
development is the machine-checked core, and this is everything around it.

**The map from claim to script is each article's *Methods* section** — read that first: it states,
claim by claim, what was checked, over what range, and by which script. `verification-code/oneoff/`
holds the single-purpose scripts (each named for what it checks, e.g.
`close_gap3_explicit_functional.sage`), and the top level holds the reusable modules
(`right_angle_simplex.py`, `minkowski_tensor.py`, …). Since 2026-11-08 `verification-code/runs/` is
organised into subdirectories, one per series of runs, with single runs left at the top;
`verification-code/runs/README.md` says what is where.

Each script is standalone and prints its own PASS/FAIL summary; none needs the others. What you need
to run them:

```sh
# Python-only checks (no special maths software):
python3 verification-code/<script>.py

# SageMath checks (exact polytopes, OEIS lookups, face lattices) — needs a Sage install:
sage verification-code/oneoff/<script>.sage

# Macaulay2 checks (Hilbert functions of exterior monomial modules) — needs M2 + the
# Amata–Crupi ExteriorIdeals/ExteriorModules packages, which ship with Macaulay2:
M2 --script verification-code/oneoff/<script>.m2
```

The recorded outputs in `verification-code/runs/` let you compare against a known-good run without
re-executing anything; a few of the heavier Sage jobs (face-lattice enumeration) are memory-hungry
and are best run one at a time.

## Reference certificates

There is one certificate per part: **`references/REFERENCE-CERTIFICATE.md`** for Part I (written
2026-09-20), **`REFERENCE-CERTIFICATE-article2.md`** for Part II (2026-10-08 to 10) and
**`REFERENCE-CERTIFICATE-article3.md`** for Part III (2026-11-14). Each is the certificate itself:
for every key the article cites, the full bibliographic entry, the claim it supports with a line number
in the source, and either a verbatim quotation with a locator from a held copy or an explicit
no-copy statement plus the registry verification done instead. The point is not bookkeeping. The
manuscripts were written with substantial AI assistance, disclosed in their own Acknowledgements,
and arXiv's policy treats hallucinated or fabricated references as grounds for a submission ban;
so being able to show, plainly and checkably, that every reference is a real and locatable
publication is part of the work rather than an afterthought. **Each certificate ships with its
arXiv submission as an ancillary file**: the generators (working home
`code/make_arxiv_submission.py`, `code/make_arxiv_submission_article2.py`) copy it into the
package's `anc/` fresh at each build. See `articles/article-1/arxiv-submission/README.md` for the arXiv-safe submission
(pdfLaTeX, inlined bibliography, no fonts to upload).

`references/CITATIONS-TO-VERIFY.md` was the worklist the certificate grew from (the works cited
with no local copy, and what needed checking about each); it is kept as the record of that check,
marked discharged.

## Provenance

The working home of this project — the logbook, the working notes, the review rounds, the
correspondence — is the `20-projects/exterior-convex/` subtree of a separate, private repository. This
repository holds the publishable artefacts only, and is a copy rather than a move: material flows into
it, not out of it.

Literature PDFs are deliberately **not** included here, for copyright reasons. Nor is work towards
later parts that is not yet written up (the fibres of the sum map, for instance).
