# arXiv submission metadata — article 2

Prepared 2026-10-08, last regenerated 2026-10-09, against `exterior-convex_article2_latest.org`
(**52 pp. in both builds** as of 2026-10-10, when the tables gained captions; the two had briefly
differed, 51 against 52, after the Linusson preprint gained its own bibliography entry). Like
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

## Abstract — full length (1,413 characters)

```
Let $E$ be the exterior algebra on $n$ generators over a field, and let $F$ be a graded free $E$-module with $r$ generators of degrees $d_1 \le \dots \le d_r$. The Hilbert function of a quotient $F/M$, where $M$ is a monomial submodule in the sense of Amata and Crupi, is a sum of shifted $f$-vectors of simplicial complexes, and a companion paper determines the convex hull of the set of these Hilbert functions. Here we count them. For $r=1$ the count is the number of $f$-vectors of simplicial complexes on $n$ vertices, which Linusson computed in 1999 by a recursion through compressed complexes. We show that no new recursion is needed in higher rank: the number of Hilbert functions is a product of $r-1$ transfer matrices, one for each gap $d_{i+1}-d_i$ between consecutive generator degrees, whose entries are differences of Linusson's own refined counts. The rank therefore enters only as the length of a matrix product. The key step, proved using Amata and Crupi's lex submodules, replaces the size of a sumset by a count of tuples of $f$-vectors subject to a nearest-neighbour constraint. We prove the same result for the proper variant from which the companion paper's polytope is built, and derive consequences: a linear recurrence in $r$ for constant gaps, polynomiality in $r$ when all gaps vanish, the exact gap beyond which the count is a plain power, and polynomiality in the number of vertices.
```

1,413 characters (arXiv's limit is 1,920). Deliberate differences from the manuscript's abstract:
the exterior algebra is `$E$` on `$n$` generators rather than `\Ext` on an `n`-dimensional `V`;
`E^p(n,k)` is described ("Linusson's own refined counts") rather than named; the two statistics
(top degree, initial degree) are left to the paper; `[cite:@SnellmanArticle1]` becomes "a
companion paper", identified in the Comments field. Every claim in it is one the manuscript's
abstract already makes.

## Abstract — a three-quarter abridgement, added 2026-10-10 at Jan's request

Jan asked for a version at three quarters of the manuscript abstract's length. The manuscript's is
**266 words**; this is **202**, against a target of 199, counted the same way on both
(whitespace-separated tokens, math included). It is shorter than the block above and drops
different things, so **the two are alternatives, not a revision** — pick one at submission.

What this one cuts, none of which is a claim: the bridge theorem, the
lexification-preserves-properness lemma, and the clause explaining that Linusson's \(r = 1\) count
comes from a recursion through compressed complexes. Everything the manuscript abstract *asserts*
is still asserted.

```
Let $E$ be the exterior algebra of an $n$-dimensional vector space over a field, let $F$ be a
graded free $E$-module with $r$ generators of degrees $d_1 \le \dots \le d_r$, and let $M$ range
over the monomial submodules of Amata and Crupi. The Hilbert function of $F/M$ is a shifted sum of
$f$-vectors of simplicial complexes; the companion paper determines the convex hull of such sums,
and here we count them. For $r = 1$ the count is Linusson's (1999); we show that no new recursion
is needed for general $r$. Using two statistics of an $f$-vector -- its top nonvanishing degree
and the initial degree of the corresponding ideal -- we prove that the number of achievable
Hilbert functions is a product of $r-1$ transfer matrices, one per generator-degree gap, with
entries differences of Linusson's refined counts $E^p(n,k)$. The rank enters only as the length of
a matrix product. The same holds for the proper variant. Consequences: a linear recurrence in $r$
for constant gaps, with exact exponential asymptotics $K \lambda^r$ when the gap is positive;
polynomiality in $r$ when all gaps vanish; a threshold beyond which the count is a plain power;
and polynomiality in the number of vertices.
```

**Note the difference in substance, not only length:** the longer block above predates
2026-10-10 and says "a linear recurrence in $r$ for constant gaps" with no asymptotic constant. The
paper now *proves* $a_r = K\lambda^r + O(\varrho^r)$ for every positive gap
(Proposition 47), so the longer abstract **understates the paper** and needs that clause adding if
it is the one used.

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
56 pages. Part II of a series; Part I is report LiTH-MAT-R-2026/04, Linkoping University, DOI 10.3384/LiTH-MAT-R-2026-04, arXiv:2609.23605. Most of the combinatorial content is formalised in Lean 4 + Mathlib (no sorry, no extra axioms; the paper states exactly what is not). The formalisation, the verification code and computed tables of the counts are in the anc directory and at https://gitlab.liu.se/jansn19/exterior-convex .
```

Plain ASCII on purpose ("Linkoping"). **56 pages**, as the arXiv version builds on 2026-10-10 — up
from 52. Mind the one-page gap between the two builds, which is not an error: the draft build is
**55 pp.**, and the generator adds §10.2 *Code, formalisation and tables*, which exists only in the
arXiv version. **The number here must be the arXiv one**, and the generator prints it.

## Report number — SETTLED 2026-10-10: leave it empty, arXiv goes first

**Decided by Jan on 2026-10-10: for this paper, arXiv first and the LiTH-MAT-R report afterwards.**
That reverses his own standing order of 2026-09-14 — report series first, arXiv afterwards — which
article 1 followed exactly (report 2026-09-18 as LiTH-MAT-R 2026/04, arXiv 2609.23605 two days
later). **It is an exception for article 2, not a new general rule.**

The reason is external and has nothing to do with the paper: the person who signs off on the report
series is off sick, which is also holding up Jan's report on the zero locus of iterated
commutators. Waiting would have delayed a finished paper on someone else's illness.

```
(leave the Report-no field empty)
```

**What this costs, and the one thing to remember.** Article 1's arXiv version carries its report
number in the Comments field; article 2's cannot, because there is no number yet. So the citation
runs the other way: **when the report is eventually taken, it should cite this paper's arXiv id**,
and the arXiv entry can be updated with the report number later — the Report-no field is revisable
on a replacement, unlike the MSC field. Tracked at `80-QUEUE/TODO/lith-report-signoff-blocked.md`
in the working repository.

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
      build day, and the chosen date is printed in the run summary. Last run **2026-10-10**:
      **55 pp.**, 0 errors, 0 undefined, 0 missing characters, 0 overfull boxes, dated
      "October 10, 2026" — **56 pp. for the arXiv build**, against 55 for the draft, the difference
      being §10.2, which only the arXiv version carries. Two things since the 2026-10-09 run: Lemma 44 and Proposition 47 (the
      asymptotic remark became a proposition, and everything after Proposition 45 renumbered by
      two), and §10.1 rewritten once the Lean side caught up. **The generator also gained a guard
      that day**: it used to count errors in the log only, and reported `ok: ? pages, 0 errors`
      for a run that produced no PDF at all. It now asserts the artefact exists.
- [x] **Reference certificate — done, and extended twice.**
      `references/REFERENCE-CERTIFICATE-article2.md` was written 2026-10-08, extended 2026-10-09
      when Jan supplied Horn–Johnson and Linusson's published version (findings 5 and 6, **both
      real defects**: every Linusson locator was wrong for the version the `.bib` names, and
      "Theorem 8.4.5" is an equality theorem that had been cited for a strict inequality), and
      extended again 2026-10-10 for the two new Horn–Johnson locators (5.7.10 p. 372, 8.3.1
      p. 529) and the new `FlajoletSedgewick2009` (Theorem V.7 p. 343, Note V.31(iii) p. 342),
      all four read in the primary sources and quoted. That pass also found one more manuscript
      defect: §1.4's table still said "Linusson's Thm. 5.3", the *preprint's* number, where the
      other eight references say 3.3 — corrected. **All seventeen cited keys now have an entry**;
      the one locator-level gap left is `Stanley1996`, never supplied, whose single claim carries
      no locator.
- [x] **The ancillary directory is 455 kB, not 16.6 MB** (2026-10-10). It had reached 231 MB on
      disk because it copied the published `verification-code/` wholesale, and a bulk sync had put
      23 raw JSON dumps into `runs/` — article-1-era polytope computations, 218 MB, the largest
      40.9 MB each, none of them backing a claim in this paper. The generator now works from an
      **explicit include list** — `.sage`, `.py`, `.m2`, `.jl`, `.maple`, plus the one `.md` that
      documents the scripts — and prints everything it leaves out. `runs/` is not shipped at all,
      and neither are Amata and Crupi's two vendored Macaulay2 packages, which are theirs and in
      any case ship with Macaulay2 itself (`needsPackage "ExteriorModules"`, verified against
      1.26.06). §10.2 and `anc/README.md` both say so plainly and point at the repository. Result:
      101 scripts, 639 kB; `anc/` 1.6 MB on disk; **tarball 455 kB**, against article 1's shipped
      824 kB.
- [x] **arXiv rate limits — not a constraint.** Two submissions per calendar month, three active
      at once. The workspace's own record (`50-writing/preprints-publications/ARXIV-PREPRINTS.md`)
      shows **one** recent submission, 2609.23605, announced **2026-09-20** — last month — and
      nothing at all in October 2026. Worth one glance at the arXiv account page to confirm, since
      that record is ours and not arXiv's.
- [x] **The repository URL is reachable by the world** — checked by Jan in a fresh browser,
      2026-10-10: `gitlab.liu.se/jansn19/exterior-convex` loads for an anonymous visitor. That
      matters because both §10.2 and the Comments field print it, and a URL in a published paper
      that 404s is worse than no URL. (The check was meaningful rather than vacuous: a private
      sibling repository was confirmed *not* reachable in the same browser.) The only other
      external links in the `.tex` are macaulay2.com, oeis.org, orcid.org and sagemath.org.
- [ ] Re-verify the arXiv LLM policy against the live page.
- [ ] Pack: `cd arxiv-submission && ./make-tarball.sh` → `../arxiv-submission.tar.gz`. Needs only
      `tar`. To submit without the ancillary trees, delete `anc/lean` and `anc/verification-code`
      first; §10.2 then over-promises, so drop that subsection from `AVAILABILITY_ORG` too.
