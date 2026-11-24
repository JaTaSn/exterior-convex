# arXiv replacement metadata: Part I, version 2 (2609.23605)

Prepared 2026-11-24. Only the fields that change are given in full; title, authors, categories,
MSC class and licence stay as in version 1 (`../../ARXIV-SUBMISSION-METADATA.md`).

## Abstract

```
Let $E$ be the exterior algebra on $n$ generators over a field, and let $F$ be a graded free
$E$-module with $r$ generators, of degrees $d_1 \le \dots \le d_r$. We determine the convex hull
of the set of Hilbert functions of the quotients $F/M$, where $M$ runs over the monomial
submodules of Amata and Crupi. The hull is the Minkowski sum of $r$ shifted copies of one and the
same simplex: the Kozlov simplex, which Kozlov proved in 1997 to be the convex hull of the
$f$-vectors of simplicial complexes on $n$ vertices. For $r=1$ the statement is Kozlov's theorem,
so this is a rank-$r$ generalization of it. We give a self-contained proof, including a proof of
Kozlov's theorem from the local Lubell-Yamamoto-Meshalkin inequality, which is in essence Kozlov's
own second proof, and the facet description of the Kozlov simplex that this proof contains. Along
the way we isolate the class of submodules for which the argument works, the ideal-direct-sum
modules, and show by example that the Hilbert function of a graded submodule outside that class
need not be a shifted sum of $f$-vectors at all. The combinatorial content is stated separately,
in language that uses no algebra, as a result on $r$-vectors of simplicial complexes and their
$ff$-vectors. Finally we determine the vertices of the Minkowski sum at rank two: which sums of
vertices of the summands survive as vertices. The facet descriptions at rank two, conjectured in
the first version of this paper, and the vertex and facet descriptions at every rank are proved in
Part IV of this series.
```

## Comments

```
53 pages. v2: the facet description of the Kozlov simplex is attributed to Kozlov's second proof; the two rank-two facet conjectures are now theorems, proved in Part IV; Section 10 rewritten, with marginal marks for results proved in Lean and for results checked by computation; no change in the numbering of statements. Lean 4 formalization and verification code: https://github.com/JaTaSn/exterior-convex (mirror of https://gitlab.liu.se/jansn19/exterior-convex), archived at https://doi.org/10.5281/zenodo.24288404; ancillary files with v1
```

## Report number

```
LiTH-MAT-R 2026:04
```

The report is version 1 and is not changed. Giving its number here is still right: the field says
which report the paper appeared as.

## Version 1's abstract and comments

Version 1's abstract ended "proving the answer for the all-ones leg vector at every rank and for
the Kozlov leg vector at rank two". The body of Part I proves the vertex description at rank two
only, so the new abstract says rank two.
