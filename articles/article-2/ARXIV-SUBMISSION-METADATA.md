# arXiv submission metadata — article 2

Prepared 2026-10-08, last regenerated 2026-10-09, against `exterior-convex_article2_latest.org`
(51 pp. in the xelatex draft, **52 pp. in the pdfLaTeX arXiv build** since 2026-10-09, when the
Linusson preprint gained its own bibliography entry). Like
article 1, article 2 now has a standing `_latest` name instead of a draft number.
Copy-paste source for the arXiv form. The abstract follows arXiv's conventions: `$…$` delimiters
for inline mathematics (arXiv renders those on the HTML abstract page), no project macros, less
notation than the manuscript's own abstract. Decisions still open for Jan are marked **[Jan]**.

**Partly reviewed.** The 2026-10-08 review
(`20-projects/exterior-convex/working-notes/review-article2-draft7-2026-10-08.org` in the working
home) had 12 must-fix items. Done the same day: 1–7 (notation leftovers, three false statements
about tables) and 12 (margin labels). **Still open: 8–11**, the verification account, the code
identifier (commit, toolchain, or a Zenodo DOI), and the responsibility paragraph. If those change
what the paper claims, the abstract and Comments below must change with them.

## Title

```
Hilbert functions over the exterior algebra and f-vectors in higher rank II: Generalizing Linusson's count to sumsets of f-vectors
```

## Authors

```
Jan Snellman
```

ORCID `0009-0002-6676-5068` (attached through the arXiv account). Affiliation: Department of
Mathematics (MAI), Linköping University.

## Abstract

```
Let $E$ be the exterior algebra on $n$ generators over a field, and let $F$ be a graded free $E$-module with $r$ generators of degrees $d_1 \le \dots \le d_r$. The Hilbert function of a quotient $F/M$, where $M$ is a monomial submodule in the sense of Amata and Crupi, is a sum of shifted $f$-vectors of simplicial complexes, and a companion paper determines the convex hull of the set of these Hilbert functions. Here we count them. For $r=1$ the count is the number of $f$-vectors of simplicial complexes on $n$ vertices, which Linusson computed in 1999 by a recursion through compressed complexes. We show that no new recursion is needed in higher rank: the number of Hilbert functions is a product of $r-1$ transfer matrices, one for each gap $d_{i+1}-d_i$ between consecutive generator degrees, whose entries are differences of Linusson's own refined counts. The rank therefore enters only as the length of a matrix product. The key step, proved using Amata and Crupi's lex submodules, replaces the size of a sumset by a count of tuples of $f$-vectors subject to a nearest-neighbour constraint. We prove the same result for the proper variant from which the companion paper's polytope is built, and derive consequences: a linear recurrence in $r$ for constant gaps, polynomiality in $r$ when all gaps vanish, the exact gap beyond which the count is a plain power, and polynomiality in the number of vertices.
```

1,413 characters (arXiv's limit is 1,920). Deliberate differences from the manuscript's abstract:
the exterior algebra is `$E$` on `$n$` generators rather than `\Ext` on an `n`-dimensional `V`;
`E^p(n,k)` is described ("Linusson's own refined counts") rather than named; the two statistics
(top degree, initial degree) are left to the paper; `[cite:@SnellmanArticle1]` becomes "a
companion paper", identified in the Comments field. Every claim in it is one the manuscript's
abstract already makes.

## Categories — [Jan]

Recommended, following the series plan recorded for Part I ("Part II is math.CO-first"):

```
math.CO (Primary) math.AC (cross-list)
```

## MSC class (2020)

```
05A15, 13F55 (Primary) 05E40, 13D40, 06A07 (Secondary)
```

As printed in the manuscript's front matter. All five checked to be real MSC2020 codes: 05A15
exact enumeration problems, generating functions; 13F55 monomial ideals, Stanley–Reisner rings;
05E40 combinatorial aspects of commutative algebra; 13D40 Hilbert functions, Poincaré series;
06A07 combinatorics of partially ordered sets. (Part I also carried 15A75, exterior algebra. It
would fit here too, but only if the manuscript's front matter is changed to match.)

## Keywords

The arXiv form has no keyword field; these are the manuscript's, for journals and DiVA:

```
exterior algebra; Hilbert function; f-vector; simplicial complex; enumeration; transfer matrix; lex submodule; Kruskal-Katona theorem
```

## Comments field

```
52 pages. Part II of a series; Part I is report LiTH-MAT-R-2026/04, Linkoping University, DOI 10.3384/LiTH-MAT-R-2026-04, arXiv:2609.23605. Most of the combinatorial content is formalised in Lean 4 + Mathlib (no sorry, no extra axioms; the paper states exactly what is not). The formalisation, the verification code and computed tables of the counts are in the anc directory and at https://gitlab.liu.se/jansn19/exterior-convex .
```

Plain ASCII on purpose ("Linkoping"). Update the page count if the review changes it.

## Report number — [Jan]

Jan's standing order (2026-09-14) is report series first, arXiv afterwards. **No LiTH-MAT-R
number for article 2 is recorded anywhere in the workspace.** If one is taken, put it here and in
the Comments, and cite it as article 1's arXiv version cites its report.

## DOI field

Empty, as for Part I (the field is for a journal version of record).

## License — [Jan]

Per-submission choice, as for Part I.

## Pre-submission checklist

- [ ] **Act on the review** (above), then regenerate:
      `python3 20-projects/exterior-convex/code/make_arxiv_submission_article2.py` in the working
      home. It re-derives the arXiv `.org` from the current draft (drops the showkeys margin
      labels, inserts §10.2 *Code, formalisation and tables*), inlines the bibliography,
      rebuilds `anc/`, compiles three times with pdfLaTeX and refuses to finish on any error,
      undefined reference or missing character. **It also freezes the date** (`\today` would
      print whatever day arXiv recompiles on) -- `ARXIV_DATE=...` overrides the default of the
      build day, and the chosen date is printed in the run summary. Last run 2026-10-09:
      52 pp., 0 errors, 0 undefined, 0 missing characters, 0 overfull boxes, dated
      "October 9, 2026".
- [ ] **Reference certificate** (`93-CONVENTIONS/manuscript-style.md`, "The reference
      certificate"): Part I has `references/REFERENCE-CERTIFICATE.md`; **Part II has none**, and
      its references were located with a language model's help. Open item in the project TODO.
- [ ] **arXiv rate limits**: two submissions per calendar month, three active at once. Count this
      month's before submitting.
- [ ] Re-verify the arXiv LLM policy against the live page.
- [ ] Pack: `cd arxiv-submission && ./make-tarball.sh` → `../arxiv-submission.tar.gz`. Needs only
      `tar`. To submit without the ancillary trees, delete `anc/lean` and `anc/verification-code`
      first; §10.2 then over-promises, so drop that subsection from `AVAILABILITY_ORG` too.
