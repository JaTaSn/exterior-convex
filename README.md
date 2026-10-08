# exterior-convex

**Hilbert functions over the exterior algebra and $f$-vectors in higher rank** — a series of three
articles, the Lean 4 formalization of their combinatorial core, the code behind every computational
claim, and a reference certificate.

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

## Published version (Part I)

Part I is published, open access, as a technical report in Linköping University's mathematics
report series:

> Jan Snellman, *Hilbert functions over the exterior algebra and $f$-vectors in higher rank I:
> Amata–Crupi monomial modules, Kozlov polytopes, and $r$-vectors of simplicial complexes.*
> LiTH-MAT-R, ISSN 0348-2960, No. 2026:04. Linköping University Electronic Press, 2026.
> DOI: [10.3384/LiTH-MAT-R-2026-04](https://doi.org/10.3384/LiTH-MAT-R-2026-04)

Full text via the DiVA record:
[urn:nbn:se:liu:diva-227730](https://urn.kb.se/resolve?urn=urn:nbn:se:liu:diva-227730)
(DiVA id `diva2:2102721`;
[record page](https://liu.diva-portal.org/smash/record.jsf?pid=diva2%3A2102721)). An arXiv
preprint is in preparation — see [`articles/article-1/arxiv-submission/`](articles/article-1/arxiv-submission/).

**Parts II and III are unpublished drafts** at this stage (`articles/article-2/`,
`articles/article-3/`); the Lean formalization in `lean/` already covers Part II's counting layer.

## Layout

| directory | contents |
|---|---|
| `articles/article-1/` | *I: Amata–Crupi monomial modules, Kozlov polytopes, and $r$-vectors of simplicial complexes.* The Org source, the exported LaTeX, and the built PDF. The `.org` is the source of truth; the `.tex` is generated from it. |
| `articles/article-2/` | *II: Generalizing Linusson's count to sumsets of $f$-vectors.* Draft 7, the version prepared for arXiv: Org source, LaTeX and PDF; `arxiv-submission/`, the arXiv package (pdfLaTeX, with `anc/` holding the Lean development, the verification code and CSV tables of the counts); and `ARXIV-SUBMISSION-METADATA.md`, the form fields. |
| `articles/article-3/` | *III: Lattice points of the Kozlov polytope, and a corrected Kruskal–Katona theorem.* Partial draft. |
| `lean/` | the Lean 4 + Mathlib formalization — see below |
| `verification-code/` | every SageMath, Macaulay2 and Python script behind a computational claim, with the recorded output of the runs under `verification-code/runs/` |
| `references/` | the BibTeX database; **`REFERENCE-CERTIFICATE.md`**, the certificate of existence for every citation in article 1 (see below); and `CITATIONS-TO-VERIFY.md`, the discharged worklist it grew from |

Article 1's §10, *Methods*, is the index into `verification-code/`: it states, claim by claim, what
was checked, over what range, and by which script. Read that before reading the scripts.

## The Lean formalization

`lean/` is a standalone Lake project: **twenty-five files, about 9,200 lines, no `sorry`, no custom
axioms.** It is organized thematically — `Spine/`, `Vertices/`, `Counting/` — rather than per
article, since the spine serves Parts I and II alike; it formalizes three layers of the series, and
`lean/README.md` carries the declaration-by-declaration correspondence to the manuscripts' numbered
statements. That file, not this one, is the authoritative record of what is and is not proved.

- **The combinatorial spine** (article 1, §§4–6 and §5.1): local LYM; the chain description of the
  Kozlov simplex; **Kozlov's theorem** itself; the sumset identity in its combinatorial form; the
  **main theorem** at every rank; and the permissive-convention variant in full.
- **The rank-two vertex structure** (§9 and Appendix A): the vertex criterion, the extremal matrix for
  both the all-ones and the Kozlov leg vector, and the vertex count.
- **The counting layer** (article 2, §§4–9): the two statistics and their joint-distribution matrix,
  Alexander duality and persymmetry, the chaining/transfer layer, the exact `δ = 0` degrees, the
  proper variant, and the constant-gap recurrence.

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

A clean build ends with `Build completed successfully` and no `error:`. The only warnings are
`if_pos`/`if_neg` deprecations under `ExteriorConvex/Vertices/` (`Count.lean`, `Simplex.lean`,
`ExtremalMatrix.lean`).

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

**The map from claim to script is article 1's §10, *Methods*** — read that first: it states, claim by
claim, what was checked, over what range, and by which script. `verification-code/oneoff/` holds the
single-purpose scripts (each named for what it checks, e.g.
`close_gap3_explicit_functional.sage`), and the top level holds the reusable modules
(`right_angle_simplex.py`, `minkowski_tensor.py`, …).

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

## Reference certificate

**`references/REFERENCE-CERTIFICATE.md`** (written 2026-09-20) is the certificate itself: for
every key article 1 cites, the full bibliographic entry, the claim it supports with a line number
in the source, and either a verbatim quotation with a locator from a held copy or an explicit
no-copy statement plus the registry verification done instead. The point is not bookkeeping. The
manuscripts were written with substantial AI assistance, disclosed in their own Acknowledgements,
and arXiv's policy treats hallucinated or fabricated references as grounds for a submission ban;
so being able to show, plainly and checkably, that every reference is a real and locatable
publication is part of the work rather than an afterthought. **The certificate ships with the
arXiv submission as an ancillary file** — the generator (working home
`code/make_arxiv_submission.py`) copies it into `articles/article-1/arxiv-submission/anc/` fresh
each build. See `articles/article-1/arxiv-submission/README.md` for the arXiv-safe submission
(pdfLaTeX, inlined bibliography, no fonts to upload).

`references/CITATIONS-TO-VERIFY.md` was the worklist the certificate grew from (the works cited
with no local copy, and what needed checking about each); it is kept as the record of that check,
marked discharged.

## Provenance

The working home of this project — the logbook, the working notes, the review rounds, the
correspondence — is the `20-projects/exterior-convex/` subtree of a separate, private repository. This
repository holds the publishable artefacts only, and is a copy rather than a move: material flows into
it, not out of it.

Literature PDFs are deliberately **not** included here, for copyright reasons.
