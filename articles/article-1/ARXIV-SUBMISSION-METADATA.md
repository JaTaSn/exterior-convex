# arXiv submission metadata — article 1

Prepared 2026-09-20, against the `.org` of the same date (53 pp. build). Copy-paste source for
the arXiv submission form; every field is in the form the form wants it, and the abstract obeys
arXiv's conventions ($…$ delimiters, no project-internal macros, minimal math). Decisions still
open for Jan are marked **[Jan]**.

## Title

```
Hilbert functions over the exterior algebra and f-vectors in higher rank I: Amata-Crupi monomial modules, Kozlov polytopes, and r-vectors of simplicial complexes
```

(Series title + subtitle joined, per the manuscript's `#+title:`/`#+subtitle:`. Plain-text
"f-vectors"/"r-vectors" — arXiv titles are best kept free of math markup.)

## Authors

```
Jan Snellman
```

ORCID `0009-0002-6676-5068` (attach via the arXiv account, not the field). Affiliation:
Department of Mathematics (MAI), Linköping University.

## Abstract

```
Let $E$ be the exterior algebra on $n$ generators over a field, and let $F$ be a graded free
$E$-module with $r$ generators, of degrees $d_1 \le \dots \le d_r$. We determine the convex hull
of the set of Hilbert functions of the quotients $F/M$, where $M$ runs over the monomial
submodules of Amata and Crupi. The hull is the Minkowski sum of $r$ shifted copies of one and the
same simplex: the Kozlov simplex, which Kozlov proved in 1997 to be the convex hull of the
$f$-vectors of simplicial complexes on $n$ vertices. For $r=1$ the statement is Kozlov's theorem,
so this is a rank-$r$ generalization of it. We give a self-contained proof, including a short
proof of Kozlov's theorem from the local Lubell-Yamamoto-Meshalkin inequality, and an explicit
facet description of the Kozlov simplex that appears not to be recorded in the literature. Along
the way we isolate the class of submodules for which the argument works, the ideal-direct-sum
modules, and show by example that the Hilbert function of a graded submodule outside that class
need not be a shifted sum of $f$-vectors at all. The combinatorial content is stated separately,
in language that uses no algebra, as a result on $r$-vectors of simplicial complexes and their
$ff$-vectors. Finally we describe the vertex structure of the Minkowski sum -- which sums of
vertices of the summands survive as vertices -- proving the answer for the all-ones leg vector at
every rank and for the Kozlov leg vector at rank two. The combinatorial core of the paper is
formalized in Lean 4 with Mathlib, with no sorry and no extra axioms; the formalization and all
verification code accompany the paper.
```

(Differences from the manuscript abstract, deliberate: `\Koz`/`\shift` macros and the displayed
equation removed; the citation `[cite:@Kozlov1997]` inlined as "in 1997"; one sentence added
naming the Lean formalization, which the manuscript's abstract leaves to §10 — **[Jan]** cut
that last sentence if it should not be in the abstract.)

## Categories

**[Jan]** Suggestion: **math.AC** (primary), cross-list **math.CO**. The MSC choices below
point the same way; math.CO could equally be primary — the main theorem is stated both
algebraically and purely combinatorially.

## MSC class (2020)

```
13F55, 52B12 (Primary) 05E40, 13D40, 15A75 (Secondary)
```

Taken verbatim from the manuscript's front matter. **All five checked well-formed and real
MSC2020 codes** (13F55 Stanley–Reisner rings / monomial ideals; 52B12 special polytopes; 05E40
combinatorial aspects of commutative algebra; 13D40 Hilbert functions/Poincaré series; 15A75
exterior algebra) — checked deliberately, because the lattice-line-covers submission went out
with the malformed code `11431` (for `11H31`) and arXiv MSC fields are not revisable without a
replacement.

## Report number

```
LiTH-MAT-R-2026/04
```

## Comments field

```
53 pages. Also published as report LiTH-MAT-R-2026/04, Linköping University,
DOI 10.3384/LiTH-MAT-R-2026-04. Lean 4/Mathlib formalization (no sorry, no extra axioms) and
all verification code included with the source.
```

**[Jan]** If the external repo gets a public remote before submission, add its URL here.

## DOI field — [Jan], with a recommendation

The report already has DOI `10.3384/LiTH-MAT-R-2026-04`. arXiv's DOI field is documented as
being for the DOI of the *published version* of record. A numbered institutional report series
with an ISSN (0348-2960) is a publication; on the other hand, if this paper is later published
in a journal, that DOI is the one that should end up here, and the field is easiest to set once.
**Recommendation: leave the DOI field empty at submission, keep the report DOI in the Comments
(as above), and set the DOI field if and when a journal version exists.** The report remains
fully findable through the Comments and Report-no fields either way.

## The report's full identifier block (for reference, not for arXiv fields)

| identifier | value |
|---|---|
| URN | `urn:nbn:se:liu:diva-227730` |
| DOI | `10.3384/LiTH-MAT-R-2026-04` |
| OAI | `oai:DiVA.org:liu-227730` |
| DiVA id | `diva2:2102721` |
| DiVA record | <https://liu.diva-portal.org/smash/record.jsf?pid=diva2%3A2102721> |
| ISSN (series) | 0348-2960 |

(Note: the URN/OAI number `227730` and the DiVA id `2102721` are different identifiers; neither
is derivable from the other. All four supplied by Jan, 2026-09-18, and recorded in the `.bib`'s
`SnellmanReport2026` entry.)

## License — [Jan]

arXiv requires choosing at submission (arXiv nonexclusive license v1.0, or a CC license).
DiVA's record of the report carries its own terms; the arXiv choice is independent. No
recommendation recorded here — this has been Jan's per-submission call.

## Pre-submission checklist (from `93-CONVENTIONS/manuscript-style.md` + this project)

- [ ] `REFERENCE-CERTIFICATE.md` (this directory's sibling under `references/`) is current
      against the submitted version — it is, as of 2026-09-20.
- [ ] AI-disclosure section present (it is; Jan's rev2 note about amending its wording —
      "began from a manual human draft" — is still open, his to word).
- [ ] Run the generator (working home
      `20-projects/exterior-convex/code/make_arxiv_submission.py`) → `arxiv-submission/` +
      `arxiv-submission.tar.gz`. It self-verifies (pdfLaTeX ×3, asserts 0 errors / 0 undefined)
      and is **pdfLaTeX + inlined bibliography** — no XeLaTeX, no fonts to upload, no biber.
      This replaces the earlier XeLaTeX package, which arXiv rejected on fonts + biblatex
      (2026-09-20). See `arxiv-submission/README.md`.
- [ ] **From any clone (e.g. jts-yoga):** `cd arxiv-submission && ./make-tarball.sh` → uploads as
      `../arxiv-submission.tar.gz`. Needs only `tar`, no LaTeX. Upload that tarball.
      **Compiler:** arXiv auto-detects pdfLaTeX from the magic comment; no font upload. To submit
      without the Lean/verification-code ancillary, delete `anc/lean` and `anc/verification-code`
      before packing (the paper is unaffected; the full formalization is public in the repo).
- [ ] Re-verify the arXiv LLM policy against the live page before submitting
      (per `reference_arxiv_llm_policy`; last verified 2026-05 clarification).
