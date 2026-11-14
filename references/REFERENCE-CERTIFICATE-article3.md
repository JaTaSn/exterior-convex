# Certificate of Existence — references cited in article 3

*(`ai-workspace/20-projects/exterior-convex/article/exterior-convex_article3_latest.org`, at
commit `405899e2` of 2026-11-14; written 2026-11-14 by Claude (Claude Code, on jts-pc), at Jan
Snellman's request. Line numbers refer to that `.org` source, which is the source of truth; the
built PDF beside it (63 pp., built 2026-11-14 17:36) was used only to confirm which keys are
printed. The bibliography checked is `literature/exterior-convex-references.bib` in the same
project, as it stood at that commit.)*

*Updated the same evening, after Jan supplied three of the missing sources: McMullen 1977 (entry 21)
and Savage–Schuster 2012 (entry 22) are now verified against the text, and Ceballos–Padrol–Sarmiento
(entry 9) against the JCTA version. Findings 8 and 10 and the two lists at the end are updated to
match. Each passage added was extracted from the supplied PDF.*

## Purpose

Same purpose as the certificates for articles 1 and 2 (`REFERENCE-CERTIFICATE.md` and
`REFERENCE-CERTIFICATE-article2.md` beside this file). arXiv's 2026 enforcement policy treats
hallucinated or fabricated references as evidence of unchecked LLM output, and this series was
written with substantial AI assistance. For every key that Part III prints, this document records
the bibliographic entry as checked; each place the article relies on the work, with its `.org`
line and the locator it uses; and *either* the passage relied on, quoted from a held copy with a
page or statement number, plus a verdict, *or* a plain statement that no copy was available and
what registry check was done instead.

## Method, stated once

- **Which keys.** The 32 keys printed in the bibliography of the built PDF, found in the `.org`
  with `grep -n "cite[^]]*@KEY"`, every hit read in its sentence. Citations inside Org comment
  lines (`.org:71`, `119`, `1133`, `3465`, `3477`) are not printed and are not covered;
  `NilssonSnellman2003`, cited only at `.org:3477`, a comment, is not in the printed bibliography.
  One citation spans two lines (`.org:1342–1343`).
- **Quotations** come from `pdftotext -layout` extractions of the held PDFs. Where the extraction
  garbled the mathematics, the page was rendered and read by eye (Linusson pp. 262–263;
  Hibi–Olsen–Tsuchiya p. 2). Mathematics is transcribed into Unicode; the words are verbatim.
  Nothing was supplied from memory or from secondary descriptions. Where a passage is quoted from an
  arXiv version and the `.bib` names the published version, the entry says so.
- **Sources consulted, in order:** `20-projects/exterior-convex/literature/` (including
  `subscription/`), then the author's private `math-library` (a local clone) (file tree and `math-library.bib`,
  searched by author, title and key), then Jan's own papers: Parts I and II as the arXiv v1 PDFs in
  `ai-workspace/50-writing/preprints-publications/preprints/` (`2609.23605_…pdf`, 53 pp.;
  `2610.14985_…pdf`, 56 pp.), Parts IV and V as the drafts `article/exterior-convex_article4_draft_1.{org,pdf}`
  and `article/exterior-convex_article5_draft_1.org`. Page numbers for Parts I and II are the printed
  ones, which coincide with the PDF page numbers.
- **Network, all on 2026-11-14, metadata only except as stated:** Crossref
  (`api.crossref.org/works/<doi>`) for every DOI in the 32 entries, twenty in all, plus Beck–Robins
  by its DOI; the arXiv API for every arXiv identifier; Unpaywall (with a placeholder address) for
  the works not held and for the published versions of those held only as preprints; OpenAlex for
  Savage–Schuster; and OEIS searches, through its JSON interface, for the sequence that `.org:1916`
  says is absent. Six open-access copies were downloaded (listed near the end). Each went into an
  empty scratch directory and was accepted only after its content type and first bytes (`%PDF`) were
  checked.
- **Reuse.** Where an article 1 or 2 certificate entry covers the same statement, the passage was
  re-extracted here and the entry says so; where Part III relies on something different, it was
  checked afresh.

## Findings worth reading first

1. **Every DOI is right this time.** All twenty DOIs in the 32 entries resolve in Crossref to the
   work the `.bib` describes, with matching authors, title, volume and pages. (Article 2 found three
   that did not.) Two small notes: Crossref has no page range for `HibiOlsenTsuchiya2018`; the `.bib`'s
   667–679 agree with the DOI suffix and with the arXiv journal reference. `BeckRobins2015` carries no
   DOI; Crossref's record is `10.1007/978-1-4939-2969-6` (Springer New York 2015, UTM), if one is
   wanted.

2. **Every locator into Parts I and II is correct against the published v1 PDFs** (30 printed
   citations, 27 with a locator, 23 distinct locators; table in entry 4). The header's PENDING note
   (`.org:238–240`) can be closed. **Part II Theorem 54 is not cited anywhere in the printed text**
   at `405899e2`. The Kupreyeva section cites Part II's Theorem 60 and Section 9, and both are
   right.

3. **`.org:3749`, `(Linusson's \(N\))`: Linusson uses no N.** Neither the published Combinatorica
   version nor the preprint uses a letter for C(n+1, 2). Both write the binomial coefficient every
   time; there is no standalone N anywhere in either text. The parenthesis looks like a leftover of
   the round-4 rename N → M in this remark (header, `.org:91`). **Suggested fix:** delete
   `(Linusson's \(N\))`, or write `(Linusson writes \(\binom{n+1}2\))`.

4. **`.org:2695–2703` (`ex-centroid-n3`): the sentence citing Kupreyeva's Table 4.2 is attached to
   the wrong centroid.** "This is Kupreyeva's row p = 3 of [Table 4.2]" follows directly after the
   centroid of the *triangle* Koz(3), "(2, 1/3) … barycentric (1/3, 1/3, 1/3)". Table 4.2 prints for
   p = 3 "(1.80, 0.20)" and "(0.4000, 0.4000, 0.2000)", which is the centroid (9/5, 1/5) of *S₃*
   with barycentric (2/5, 2/5, 1/5), given two sentences earlier. A reader who checks the table
   against the nearest number will think the citation wrong. "since her T³₃ is S₃" is also loose:
   her T³₃ is the triangle, and the table is the centre of mass of the f-points in it. **Suggested
   fix:** move the Kupreyeva sentence to follow `\((2/5,2/5,1/5)\)`, and write "since the f-points of
   her T³₃ are S₃".

5. **`.org:3094–3096`: Brion–Vergne's Theorem 2.15 is for *simple* lattice polytopes.** The sentence
   reads "For polynomial weights in general, the corresponding statement follows from the
   Euler–Maclaurin formula of Brion and Vergne [Theorem 2.15]", directly after a paragraph about an
   arbitrary lattice polytope P. The theorem is stated for "a simple lattice polytope in V". The use
   made of it, for Koz(n), is covered, since a simplex is simple. **Suggested fix:** "For polynomial
   weights, and P simple, as Koz(n) is, the corresponding statement follows …".

6. **`.org:1893–1897` (`rem-hstar-misprint`): the claim checks out against the arXiv version, but
   (a) the published version was not seen, and (b) the comparison needs an orientation.**
   (a) Hibi–Olsen–Tsuchiya arXiv v2, p. 2, prints "with the convention that e₀ = 1 and s₀ = 1" before
   their Lemma 1.1, and Savage–Visontai print "with the convention that e₀ = 0 (and s₀ = 1)", so the
   misprint is real in the text that was read. The remark is a claim about the *printed* Moscow Math.
   J. paper, though, and a misprint can be corrected between arXiv and print. **Jan should look at
   Lemma 1.1 in the MMJ version** before the remark goes out. (b) The figures "(14,10) instead of
   (1,16,7) at n = 4" hold for s = (6,4,1). For s = (1,4,6), the orientation of
   `prop-lecture-hall`, e₁ = 0 always, the convention has no effect, and both readings give
   (1,16,7). (Checked here by enumerating the 24 residue vectors in each orientation; this is
   arithmetic, not a citation check.) **Suggested fix:** "at n = 4, with s = (6,4,1)".

7. **`.org:2045–2047` and `.org:2073–2075`: two statements about Part II's T′ₙ(0) and u′ₙ hold
   only on the principal block.** Part II indexes both by τ ∈ {−1, 0, 1, …, n} (Definition 28,
   (61)). There "the two columns τ′ = −1 and τ′ = 0 vanish identically" in T′ₙ(δ) (Lemma 44, p. 32),
   and the vector of row sums "vanishes at τ = −1, 0" (proof of Theorem 60, p. 43, stated for every
   p ≥ n and so for p = n). So on Part II's index set T′ₙ(0) has
   diagonal entries 0 at τ = −1, 0 and is not unitriangular, and the first entry of u′ₙ is 0. Both of
   Part III's statements ("The same holds for Part II's T′ₙ(0)"; "Part II's u′ₙ ha[s] first entry 1")
   are true on the block τ ∈ {1, …, n}, which is the block Part II itself confines the product to. The
   proof is unaffected. **Suggested fix:** add "on the principal block τ ∈ [1, n] (Part II, Lemma
   44)" once, at `.org:2046`.

8. ~~**McMullen (1977) is attributed but not verified, and nothing held ties the theorem to that
   paper.**~~ **Resolved the same evening: the theorem is McMullen's Theorem 6 (p. 121)**, applied
   to the lattice-point enumerator, which his §6 (p. 127) shows is a ℤᵈ-valuation. Quotations in
   entry 21. `thm-mcmullen` is quoted from Haase–Juhnke-Kubitzke–Sanyal–Theobald, Theorem 2.3
   (entry 11), which credits "Bernstein and McMullen; see [13, Theorem 19.4]", [13] being Gruber's
   book, and does not cite McMullen 1977 itself. **Suggested fix:** the Org comment at
   `.org:2233–2238` says McMullen's theorem number is unchecked; it can now say
   "[McMullen1977, Theorem 6]".

9. **`Stanley1996` is still unverified, and the one held source that names a theorem points to a
   different Stanley work.** `.org:1858–1859` says "by a theorem of Stanley" h*-palindromicity is
   equivalent to the Ehrhart ring being Gorenstein, and cites *Combinatorics and Commutative
   Algebra*. Hibi–Olsen–Tsuchiya (p. 2) attribute the Gorenstein ⇔ symmetric-h* equivalence to
   "[14] R. P. Stanley, Hilbert functions of graded algebras, Advances in Math. 28 (1978), 57–83".
   The book is in neither `literature/` nor `math-library`, so whether and where it states the
   theorem is unchecked. **Either supply the book's locator, or cite the 1978 paper as HOT do.**

10. **Several locators were read only in arXiv versions, while the `.bib` names the published
    version.** These are Ceballos–Padrol–Sarmiento (Example 2.2, Section 2; arXiv v1 only, the
    project TODO), Hibi–Olsen–Tsuchiya (Lemma 1.1; see finding 6), Liu–Solus (Theorem 4.3),
    Chen–Li–Sam (Theorem 1.4), Savage–Visontai (no locator used) and Santos (Theorem 1.4, §1.4;
    arXiv v3, which its own comment calls the accepted version). ~~**The JCTA numbering of
    Ceballos–Padrol–Sarmiento could not be checked.**~~ **Checked the same evening, in the JCTA
    copy Jan saved from a browser: Example 2.2 and the Cayley trick in §2 keep their numbers**
    (entry 9). Beck–Robins was checked in the authors' 2020 draft of the second edition (in
    `math-library`), not in the 2015 Springer printing.

11. **Optional tightenings** (the claims are all supported as they stand):
    - `.org:2347`, "[Ziegler1995 Chapter 2]": the statement is Lemma 2.9 (p. 60).
    - `.org:1880`, "[BeckRobins2015 Chapter 3]": Corollary 3.11 (pp. 71–72).
    - `.org:2949`, "Ehrhart's theorem [BeckRobins2015]": Theorem 3.8 with Corollary 3.20.
    - `.org:3084`: Theorem 5.6 gives only the second coefficient; "the leading coefficient is the
      relative volume" is the paragraph before it in §5.4 (p. 108).
    - `.org:647`, "[SnellmanArticle1 Section 8]": the identity is Part I's eq. (47), p. 23.
    - `.org:1615`, "[SnellmanArticle2 Section 9]": the convention is stated after Definition 53,
      p. 39.
    - `.org:1641`: Part II defines FF⁽ᵖ⁾_pr at (92), just before Theorem 60.
    - `.org:699`, "LYM coordinates of Part I": Part I calls them *LYM ratios* (Definition 12).
    - `.org:1174–1175`, "proved there by the same triangular determinant": Kupreyeva's proof is an
      upper-triangular determinant (her (6.4)), Part III's a diagonal map on a unimodular order
      simplex; same product, different argument. "by a triangular determinant with the same
      diagonal" would be exact.
    - `.org:2000`, "first exhibited by Liu and Solus": no source read here says "first", though
      Caicedo–Juhnke–Poullot present Liu–Solus as the prior result.

---

## A. Primary source held — quoted

### 1. Amata & Crupi (2020), An. Şt. Univ. Ovidius Constanţa — `AmataCrupi2020KK`

**Citation:** L. Amata, M. Crupi, *A generalization of Kruskal–Katona's theorem*, An. Şt. Univ.
Ovidius Constanţa **28**(2) (2020), 35–51, DOI `10.2478/auom-2020-0018`. Crossref confirms every
field (issued 2020-07-01).

**Claims supported:** `.org:445–447` and `.org:983–984`: "the module version of the
Kruskal–Katona theorem due to Amata and Crupi [Theorem 4.2]", "a growth condition on the sequence
itself, valid for all graded submodules of F".

**Quotation** (re-extracted; the same passage as article 2's entry 3), pp. 43–44: "Theorem 4.2.
Let (f₁, f₂, …, f_r) ∈ ℤʳ be an r–tuple such that f₁ ≤ f₂ ≤ ··· ≤ f_r and let (h_{f₁}, h_{f₁+1}, …,
h_{f_r+n}) be a sequence of nonnegative integers. … Then the following conditions are equivalent:
(a) ∑_{i=s}^{f_r+n} hᵢtⁱ is the Hilbert series of a graded E-module F/M, with F = ⊕ᵢ₌₁ʳ Egᵢ finitely
generated graded free E-module with the basis elements gᵢ of degrees fᵢ; (b) h_s ≤ r̃₀, h_{s+1} ≤
nr̃₀ + r̃₁, hᵢ = ∑_{j=N+1}^r C(n, i−f_j) + a, … and h_{i+1} ≤ ∑_{j=N+1}^r C(n, i−f_j+1) + a^{(i−f_N)},
i = s+1, …, f_r+n; (c) there exists a unique lexicographic submodule L …". p. 35, abstract: "We
characterize the Hilbert functions of graded E–modules of the type F/M, with M graded submodule of F."

**Verdict:** a growth condition, (b), equivalent to being a Hilbert function of F/M for *any* graded
submodule M, (a). **Says what is claimed.** (Article 2's findings 3–4 on the literal wording of (b)
do not bear on Part III, which does not restate (b).)

### 2. Amata & Crupi (2021) — `AmataCrupi2021`

**Citation:** L. Amata, M. Crupi, *ExteriorModules: a package for computing monomial modules over
an exterior algebra*, J. Softw. Algebra Geom. **11** (2021), 71–81, DOI `10.2140/jsag.2021.11.71`.
Crossref confirms every field (issue 1, issued 2021-12-31); the held PDF's header reads "JSAG 11
(2021), 71–81", whatever its filename says (article 1's finding 5).

**Claim supported:** `.org:3932–3934`, "Luca Amata and Marilena Crupi's Macaulay2 package … was used
throughout". A use, not a claim about the paper.

**Quotation** (re-extracted; a different passage from article 2's), p. 71, abstract: "We present a
Macaulay2 package to manage some classes of monomial submodules of F. … This package also includes
some methods to check whether a sequence of nonnegative integers is the Hilbert function of a graded
E-module of the form F/M, with M a graded submodule of F." **Status: verified.**

### 3. Beck & Robins (2015) — `BeckRobins2015`

**Citation:** M. Beck, S. Robins, *Computing the Continuous Discretely*, 2nd ed., Undergraduate Texts
in Mathematics, Springer, New York, 2015. No DOI in the `.bib`. Crossref, `10.1007/978-1-4939-2969-6`:
title and subtitle as cited, authors Beck and Robins, Springer New York, 2015, ISBNs 9781493929689 /
9781493929696.

**Copy checked:** `math-library/textbooks/combinatorics/beck-robins-computing-the-continuous-discretely.pdf`,
the authors' draft of the second edition, dated June 19, 2020, whose preface describes the second
edition. It is **not** the 2015 Springer printing. Page numbers below are the draft's. (The other
copy, `…-discretely-2.pdf`, is a February 2006 draft of the first edition and was not used.)

**Claims supported and verdicts:**

- `.org:1835–1838` and `.org:1840–1857`, "[Chapters 3 and 4, in particular Theorems 4.1, 4.4 and
  4.5]": degree of L_P, h*-nonnegativity, reciprocity in both forms, and codegree = D+1−s.
  - p. 90: "Theorem 4.1 (Ehrhart–Macdonald reciprocity). Suppose P is a convex rational polytope.
    Then the evaluation of the quasipolynomial L_P at negative integers yields L_P(−t) =
    (−1)^{dim P} L_{P°}(t)."
  - p. 93: "Theorem 4.4. Suppose P is a convex rational polytope. Then the evaluation of the rational
    function Ehr_P at 1/z yields Ehr_P(1/z) = (−1)^{dim P+1} Ehr_{P°}(z)."
  - p. 94: "Theorem 4.5. Suppose P is an integral d-polytope with Ehrhart series
    (h*_d z^d + h*_{d−1} z^{d−1} + ··· + h*₁z + 1)/(1−z)^{d+1}. Then h*_d = h*_{d−1} = ··· = h*_{k+1}
    = 0 and h*_k ≠ 0 if and only if (d−k+1)P is the smallest integer dilate of P that contains an
    interior lattice point."
  - p. 72: "Theorem 3.12 (Stanley's nonnegativity theorem). … Then h*₀, h*₁, …, h*_d are nonnegative
    integers."

  Part III's series form of reciprocity (eq:reciprocity) follows from Theorem 4.4 with
  Ehr_P = h*_P/(1−z)^{D+1}. **Supported.**
- `.org:1879–1880`, "[Chapter 3]" for "h*_i is the number of lattice points at height i in Π".
  pp. 71–72: "Corollary 3.11. Suppose Δ is an integral d-simplex with vertices v₁, v₂, …, v_{d+1}, and
  let w_j = (v_j, 1). Then Ehr_Δ(z) = 1 + ∑_{t≥1} L_Δ(t)zᵗ = (h*_d z^d + ··· + h*₁z + h*₀)/(1−z)^{d+1},
  where h*_k equals the number of integer points in {λ₁w₁ + ··· + λ_{d+1}w_{d+1} : 0 ≤ λ₁, …,
  λ_{d+1} < 1} with last coordinate equal to k." **Supported**; Corollary 3.11 is the exact
  locator.
- `.org:2949`, "By Ehrhart's theorem [BeckRobins2015]" (Q_k and K full-dimensional lattice
  polytopes, leading coefficient the volume). p. 68: "Theorem 3.8 (Ehrhart's theorem). If P is an
  integral convex d-polytope, then L_P(t) is a polynomial in t of degree d." p. 77: "Corollary 3.20.
  Suppose P ⊂ ℝ^d is an integral convex d-polytope with Ehrhart polynomial c_d t^d + c_{d−1}t^{d−1} +
  ··· + c₁t + 1. Then c_d = vol P." **Supported.**
- `.org:3082–3084`, "leading coefficient the relative volume of P, and next coefficient half the
  sum of the relative volumes of its facets [Theorem 5.6]". pp. 107–108: "Henceforth, when we write vol S
  we refer to the relative volume of S. … The relative volume of P is the leading term of the
  corresponding counting function L_P." "Theorem 5.6. Suppose L_P(t) = c_d t^d + c_{d−1}t^{d−1} +
  ··· + c₀ is the Ehrhart polynomial of the integral polytope P. Then c_{d−1} = ½ ∑_{F a facet of P}
  vol F." **Supported**; the leading-coefficient half is the paragraph before Theorem 5.6.

**Status: verified against the authors' 2020 draft of the second edition; numbering in the 2015
printing not checked** (the printing is not held).

### 4. Snellman, Parts I and II — `SnellmanArticle1`, `SnellmanArticle2`

**Citations.** Part I: J. Snellman, *Hilbert functions over the exterior algebra and f-vectors in
higher rank, I: Amata–Crupi monomial modules, Kozlov polytopes, and r-vectors of simplicial
complexes*, LiTH-MAT-R 2026/04, Linköping University Electronic Press, DOI
`10.3384/LiTH-MAT-R-2026-04`, arXiv:2609.23605. Crossref: report, this title, issued 2026-09-18. arXiv
API: v1 only, submitted 2026-09-20, same title. Part II: *…, II: Generalizing Linusson's count to
sumsets of f-vectors*, arXiv:2610.14985. arXiv API: v1 only, submitted 2026-10-10, same title; the
`.bib` gives no DOI, correctly.

**Copies checked:** the arXiv v1 PDFs (Part I 53 pp., Part II 56 pp.), **not** the drafts or `.aux`
files the header says the numbers were first read from (`.org:238–240`).

**Every locator, against the published v1:**

| .org line | Part III cites | in the published v1 | verdict |
|---|---|---|---|
| 389 | Part I (no locator) | Thm 39, p. 23 | correct |
| 396 | I, Theorem 39 | Thm 39, p. 23: Minkowski sum of r shifted Koz(n) | correct |
| 397 | I, Section 9 | §9, p. 27: vertices at rank two (Thms 51, 54), facets conjectured (Conjs 52, 55) | correct |
| 399 | I, Section 9.3 | §9.3, p. 34: "Ranks beyond the second are not settled here" | correct |
| 401 | I, Conjectures 52 and 55 | Conj 52, p. 32; Conj 55, p. 34; both facet descriptions | correct |
| 561 | I, Definition 10 | Def 10, p. 10: proper iff h₁ = n | correct |
| 571 | I, Proposition 35 | Prop 35, p. 21: the sumset (43) | correct |
| 640 | I, Definition 36 | Def 36, p. 22: integer leg vector, in ℝⁿ | correct, both "changes" accurate |
| 647 | I, Section 8 | eq. (47), p. 23, in §8 | correct |
| 664 | I, Proposition 45 | Prop 45, p. 26: the dimension formula (56) | correct |
| 676 | I, Lemma 13 and Corollary 16 | Lemma 13, p. 12; Cor 16, p. 13 | correct |
| 397 | Part II (no locator) | Thms 29 and 41: transfer-matrix product | correct |
| 520 | Part II (no locator) | §3.1, p. 9: bold for tuples, Part I uses an arrow | correct |
| 712 | II, Section 5 | §5, Def 8, p. 12: indeg and top | correct |
| 847 | II, Definition 19 | Def 19, p. 17: chaining condition (46) | correct |
| 974, 3424 | II, Theorems 23 and 41, with Lemma 40 | pp. 19, 31, 30 | correct |
| 1469, 2781 | II, Proposition 42 | Prop 42, p. 31: FF_pr = Sₙʳ iff gaps ≥ n−1 | correct |
| 1615 | II, Section 9 | after Def 53, p. 39: p vertices, n bounds faces | correct |
| 1641, 3840 | II, Theorem 60 | Thm 60, p. 42; set defined at (92) | correct |
| 2012 | II, Definition 28 and Theorem 41 | Def 28, p. 23; Thm 41, p. 31 | correct |
| 2038 | II, Section 7 | Thm 29's proof, p. 24 | correct |
| 2065, 2079 | II, Theorem 36 | Thm 36, p. 27: degree n−1, coefficient as stated | correct |
| 2070 | II, Theorem 41 | Thm 41, (72), p. 31 | correct |
| 2574 | II, Definition 13 | Def 13, (35), p. 14 | correct |
| 2654 | II, Lemma 14 | Lemma 14, (36), p. 14 | correct |
| 3558 | II, Lemma 24 | Lemma 24, p. 20; "water-filling", p. 21 | correct |

**Quotations for the substantive ones:**

- Part I, p. 23: "Theorem 39. Let n ≥ 1, r ≥ 1, and 0 = d₁ ≤ d₂ ≤ ··· ≤ d_r, and let F = ⊕ᵢ₌₁ʳ Egᵢ,
  deg gᵢ = dᵢ. Then, in the degree-0-inclusive coordinates of Definition 34, conv{H_{F/M} : M proper
  monomial} = ∑ᵢ₌₁ʳ shift^{dᵢ}(Koz(n)) = Koz(n; d₁, …, d_r), a Minkowski sum of r shifted copies of
  one and the same Kozlov simplex". Definition 15, p. 12: "The Kozlov simplex is Koz(n) := conv(Sₙ)".
- Part I, p. 34 (end of §9.3): "The vertex count settles the vertex set of the rank-two Kozlov
  polytope outright. Ranks beyond the second are not settled here; see the corresponding remark in
  Part III." Conjecture 52, p. 32: "the polytope RA(a; 0, d) is cut out in ℝᴺ by a single equation
  together with one capped, weakly decreasing chain of inequalities". Conjecture 55, p. 34: "Then
  RA(a; 0, d) is cut out in ℝᴺ by the equation x₁ = n, the first chain with its offsets, …".
- Part I, p. 10: "Definition 10. A Hilbert function (1, h₁, …, hₙ) of E/I is proper if h₁ = n,
  equivalently if I has no minimal generator of degree ≤ 1, equivalently if the corresponding Δ uses
  the full vertex set."
- Part I, p. 22: "Definition 36. Let a = (a₁, …, aₙ) be a vector of positive integers, called a leg
  vector. The right-angle simplex ∠(a) is the convex hull of the n points v_j = (a₁, …, a_j, 0, …, 0),
  j = 1, …, n." p. 23, (47): "π(Koz(n)) = ∠(κ(n)), π(Koz(n; d₁, …, d_r)) = RA(κ(n); d₁, …, d_r) +
  ∑_{i : dᵢ≥1} e_{dᵢ}."
- Part I, p. 26: "Proposition 45. Let n ≥ 1, r ≥ 1 and 0 ≤ d₁ ≤ ··· ≤ d_r. Then dim Koz(n; d₁, …, d_r)
  = |⋃ᵢ₌₁ʳ {dᵢ + 2, dᵢ + 3, …, dᵢ + n}|."
- Part I, p. 13: "Corollary 16. The Kozlov simplex has the description π(Koz(n)) = {x ∈ ℝⁿ : x₁ = n,
  x₁/C(n,1) ≥ x₂/C(n,2) ≥ ··· ≥ xₙ/C(n,n) ≥ 0}, and for n ≥ 2 these n inequalities are exactly its
  facets."
- Part II, p. 31: "Theorem 41. Fix n ≥ 1, r ≥ 1 and a sorted d. Let A′ₙ be Aₙ with the columns ρ = 0
  and ρ = 1 set to zero, u′ₙ its row sums, and T′ₙ(δ) built from A′ₙ as in Definition 28. Then
  |FF_pr(n; d)| = |CT_pr(n; d)| = u′ₙ · T′ₙ(δ₂) ··· T′ₙ(δ_r) · 1ₙ." p. 30: "Lemma 40. Let x =
  ∑ᵢ shift^{dᵢ}(sᵢ) with every sᵢ ∈ Sₙ. Then the unique lex submodule L with HF(F/L) = x is proper."
- Part II, p. 27: "Theorem 36. (The exact degrees at δ = 0.) Let n ≥ 1. Then |FF(n; 0, …, 0)| is a
  polynomial in r of degree exactly n + 1, and |FF_pr(n; 0, …, 0)| one of degree exactly n − 1, with
  leading coefficients (1/(n+1)!) ∏_{j=0}^n C(n,j) and (1/(n−1)!) ∏_{j=2}^n C(n,j) respectively."
  This matches Part III's ∏_{k≥2} C(n,k)/(n−1)! in `cor-zero-shift`.
- Part II, p. 31: "Proposition 42. For n ≥ 1, |FF_pr(n; d)| = |Sₙ|ʳ if and only if every gap
  satisfies δᵢ ≥ n − 1."
- Part II, p. 39: "Definition 53. For p ≥ n, let F_n^{(p)} be the set of f-vectors with f₁ ≤ p and
  f_j = 0 for j > n, and FF^{(p)}(n; d) the corresponding sumset. From here to the end of this
  section the exterior algebra is on p generators, so p is the number of vertices, and n bounds the
  size of a face." p. 42, (92): "S_n^{(p)} = {s ∈ F_n^{(p)} : indeg(s) ≥ 2}, … let FF_pr^{(p)}(n; d) be
  the corresponding sumset". Theorem 60 then gives |FF_pr^{(p)}(n; d)| as a transfer-matrix product,
  (94). Part III's S_n^{(p)} ("complexes on [p] that use every vertex and have no face of more than
  n elements") is the same set.
- Part II, p. 14: "Dₙ(s)(j) = C(n,j) − s(n−j) (0 ≤ j ≤ n)" (35), and "Lemma 14. (Alexander duality on
  f-vectors.) … Consequently Dₙ restricts to an involution of Fₙ".
- Part II, p. 20: "Lemma 24. (The explicit inverse.) … If (s₁, …, s_r) ∈ CT(n; d) and Σ_d(s₁, …, s_r)
  = x, then (s₁, …, s_r) = Φ_d(x)." p. 21: "the effect is a water-filling from the last component".

**Status: verified.** All locators correct. See finding 7 for the block-indexing precision at
`.org:2046` and `.org:2074`, and finding 11 for the optional tightenings at `.org:647`, `699`, `1615`
and `1641`.

### 5. Snellman, Parts IV and V (unpublished) — `SnellmanArticle4`, `SnellmanArticle5`

**Citations:** *…, IV: Vertices and facets of the Kozlov polytope at every rank* and *…, V: Module
Kruskal–Katona*, both `@misc` with `pubstate = inpreparation`, both correctly described as
forthcoming. **Neither is published.** No arXiv identifier or report number exists for either.

**Copies checked:** Part IV, `article/exterior-convex_article4_draft_1.pdf` (built 2026-11-09) with
its `.org`; Part V, `article/exterior-convex_article5_draft_1.org`.

- `.org:399–401` (Part IV determines "the vertices at every rank" and "the facets at every rank",
  and "proves Part I's two facet conjectures"). Part IV draft, abstract: "Here we describe the
  polytope completely at every rank. On the vertex side we prove that, for every weakly log-concave
  leg vector, the extremal tensor of the Minkowski sum is the conjunction of its consecutive rank-two
  restrictions, and we list the vertices of Koz(n; d) explicitly … On the facet side we prove the
  rank-two H-description conjectured in Part I and a weighted generalisation at every rank". Its
  status table: "Thm. 28, Part I's Conjecture 55, and Cor. 30, its Conjecture 52 — proved;
  verified". **Supported.** *Aside, outside this certificate's scope:* in that PDF, Corollary 30
  prints the raw string "[cite:@SnellmanArticle1 Conjecture 52]", a citation that did not export.
- `.org:658–659` ("The vertex and facet descriptions of Part I and of [Part IV] are stated in Part I's
  coordinates"). Part IV draft, §2.3: "the right-angle polytope in the degree-0-dropped space ℝᴺ, with
  coordinates x₁, …, x_N: the same names with x₀ forgotten, as in Part I. … Sections 3 and 4 work in
  RA." **Supported.**
- `.org:447–449` and `.org:984–985` (Part V gives "A new proof of [AC Theorem 4.2], with a complete
  proof of the step in which the free generators of largest degree are filled first"). Part V draft,
  abstract: "We give a new proof of their theorem, along the same lines as theirs. What is new is a
  complete proof of the greedy step on which it rests: among all ways of distributing a family of
  monomials over the components of F, the one that fills the components of largest exterior degree
  first has the smallest shadow." `.org:225–226` of that draft: "on the quotient side, filling the
  generators of largest degree first is what lets the quotient grow fastest." **Supported**; Part
  III uses the quotient-side wording.

**Status: the cited content exists in the drafts as described; both works are unpublished.**

### 6. Brändén & Solus (2020) — `BrandenSolus2020`

**Citation:** P. Brändén, L. Solus, *Some algebraic properties of lecture hall polytopes*, Sém.
Lothar. Combin. **84B** (2020), Article 25 (FPSAC 2020), arXiv:1911.12459. No DOI in the `.bib`.
The held SLC PDF's header reads "Séminaire Lotharingien de Combinatoire 84B (2020) … Article #25,
12 pp." The arXiv API has v1 only.

**Copies checked:** the SLC version, `literature/branden-solus-2020-fpsac-slc84B25.pdf`, which is the
version the `.bib` names; and arXiv v1, for the numbering remark.

**Claims supported and verdicts:**

- `.org:1127–1129`, the IDP of lecture hall simplices, "which Hibi, Olsen and Tsuchiya had … conjectured
  in general". SLC p. 4: "when P is the n-chain O(P, s) = P_n^s. In [7], it is conjectured that all
  s-lecture hall simplices are IDP. We now prove a more general (and stronger) statement." p. 5,
  after Theorem 2.1: "It follows from Theorem 2.1 that all s-lecture hall order polytopes are IDP."
  ([7] is Hibi–Olsen–Tsuchiya.) **Supported.**
- `.org:3553–3557`, "[Theorem 2.1] (Theorem 1 in the arXiv version)", the relation ⊴ and the
  decomposition. SLC pp. 4–5: "Let λ, γ ∈ O(P, s) ∩ ℤⁿ. We write λ ⊴ γ provided that 1. λᵢ ≤ γᵢ for
  all i ∈ [n], and 2. if λᵢ ≠ 0, then γᵢ = sᵢ. Theorem 2.1. Let P = ([n], ⪯) be a naturally labeled
  poset and let s = (s₁, …, sₙ) be a sequence of positive integers. If λ ∈ kO(P, s) ∩ ℤⁿ for k ∈ ℤ_{>0},
  then there are unique elements λ⁽¹⁾, …, λ⁽ᵏ⁾ ∈ O(P, s) ∩ ℤⁿ such that λ⁽¹⁾ ⊴ λ⁽²⁾ ⊴ ··· ⊴ λ⁽ᵏ⁾ and
  λ = λ⁽¹⁾ + λ⁽²⁾ + ··· + λ⁽ᵏ⁾. … Proof. … write λ = λ ∧ s + (λ − s) ∨ 0." arXiv v1, p. 4: the same
  statement as "Theorem 1". **Supported, number and parenthetical both right.** The theorem is
  stated for s-lecture hall *order* polytopes; the lecture hall simplices are the case P = the
  n-chain, as quoted above.

**Status: verified.**

### 7. Brion & Vergne (1997) — `BrionVergne1997`

**Citation:** M. Brion, M. Vergne, *Lattice points in simple polytopes*, J. Amer. Math. Soc. **10**(2)
(1997), 371–392, DOI `10.1090/S0894-0347-97-00229-4`. Crossref confirms every field. The held copy
(`literature/Brion-Vergne-1997-…pdf`, Jan's browser download) is the journal version; Unpaywall
lists it as free from the AMS (bronze), so it belongs in `literature/`, not `subscription/`.

**Claim supported:** `.org:3094–3096`, "the corresponding statement follows from the Euler–Maclaurin
formula of Brion and Vergne [Theorem 2.15]".

**Quotation**, pp. 376–377: "Theorem 2.15. Let V be a vector space with a lattice M. Let P be a
simple lattice polytope in V, and let Σ be its associated fan. Then, for small h, the volume
vol(P(h)) of the deformed polytope P(h) is a polynomial function of h, and we have |M ∩ P| =
Todd(Σ, ∂/∂h) vol(P(h))|_{h=0} … More generally, if φ is a polynomial function on V, then I(φ)(h) =
∫_{P(h)} φ(x)dx is a polynomial function of h for small h, and ∑_{m∈M∩P} φ(m) =
Todd(Σ, ∂/∂h)I(φ)(h)|_{h=0}".

**Verdict:** the formula for polynomial weights is there, **for simple lattice polytopes**. The
manuscript's "in general" outruns the hypothesis; its use for Koz(n), a simplex, does not
(finding 5). The step from Theorem 2.15 to the two-term expansion for dilates is an inference the
manuscript labels "follows from". The `.bib` note records that B–V extract the top two coefficients
only for weight 1. **Status: verified, with the hypothesis to add.**

### 8. Caicedo, Juhnke & Poullot (2025) — `CaicedoJuhnkePoullot2025`

**Citation:** J. B. Caicedo, M. Juhnke, G. Poullot, *Ehrhart non-positivity and unimodular
triangulations for classes of s-lecture hall simplices*, arXiv:2508.18890, 2025. The arXiv API
confirms title and authors; **the current version is v4, of 2026-10-27**, whereas the `.bib` note
says v3 was read.

**Copies checked:** v3 (held) and v4 (downloaded today). The numbered statements are the same in
both.

**Claim supported:** `.org:2001–2002`, "a second family, s = (a, …, a, a+1), by Caicedo, Juhnke and
Poullot [Theorem 3.5]".

**Quotation**, v4 p. 8: "Theorem 3.5. For any n ≥ 5, there exists α(n) such that for all a ≥ α(n)
and s = (a, …, a, a+1) of length n, the simplex Pₙˢ is not Ehrhart positive. More precisely, as
a → ∞, [tⁿ⁻⁴]L_{Pₙˢ}(t) ∼ −aⁿ⁻¹/(720(n−4)!)." v3, p. 8, is the same theorem with the same
number; it reads "as a → ∞, we have:" before the display.

**Verdict:** **supported**, with the source's qualifiers: length at least 5, a large enough.
**Status: verified (v3 and v4).**

### 9. Ceballos, Padrol & Sarmiento (2015) — `CeballosPadrolSarmiento2015`

**Citation:** C. Ceballos, A. Padrol, C. Sarmiento, *Dyck path triangulations and extendability*,
J. Combin. Theory Ser. A **131** (2015), 187–208, DOI `10.1016/j.jcta.2014.10.009`, arXiv:1402.5111.
Crossref confirms every field. The arXiv API has v1 only.

**Copy checked:** arXiv v1 only (`literature/ceballos-…_arXiv-1402.5111.pdf`, 15 pp.).

**Claims supported and verdicts:**

- `.org:1336–1339`, the monotone paths are "the maximal simplices of the staircase triangulation of
  Δʳ⁻¹ × Δⁿ⁻¹ [Example 2.2]". p. 4: "Example 2.2 (Staircase triangulation of Δᵐ⁻¹ × Δⁿ⁻¹). Consider
  all monotone paths in G_{m×n} from (1, 1) to (m, n). … Every such monotone path, or staircase,
  defines a (m + n − 2)-simplex of Δᵐ⁻¹ × Δⁿ⁻¹, whose points are labelled by the squares in the path.
  It is easy to see that this collection of simplices forms a triangulation of Δᵐ⁻¹ × Δⁿ⁻¹, which is
  called the staircase triangulation". **Supported.** (The grid is transposed: CPS put (eᵢ, e_j) in
  column i, row j, and Part III puts it in row i, column j. Harmless.)
- `.org:1340–1343`, the Cayley trick, "[…; Section 2]". p. 5 (§2, "Mixed subdivisions and tropical
  arrangements"): "To each simplex s ∈ T associate the simplex sᵢ = conv{e_j : (eᵢ, e_j) ∈ s} ⊂ Δⁿ⁻¹.
  The set of Minkowski sums {s₁ + ··· + s_m : s ∈ T} forms a mixed subdivision of mΔⁿ⁻¹. The Cayley
  trick states that this correspondence is a bijection between triangulations of Δᵐ⁻¹ × Δⁿ⁻¹ and
  fine mixed subdivisions of mΔⁿ⁻¹". **Supported**, nearly word for word.

**Status: verified in arXiv v1, and in the JCTA version** (added the same evening, from the copy Jan
saved from Elsevier's open archive, `literature/ceballos-padrol-sarmiento-2015-dyck-path-triangulations-extendability_JCTA.pdf`).
The numbering is unchanged. JCTA p. 192, §2.2 *Grid representation*: "Example 2.2 (Staircase
triangulation of Δᵐ⁻¹ × Δⁿ⁻¹). Consider all monotone paths in G_{m×n} from (1, 1) to (m, n). … Every
such monotone path, or staircase, defines an (m + n − 2)-simplex of Δᵐ⁻¹ × Δⁿ⁻¹, whose points are
labelled by the squares in the path. It is easy to see that this collection of simplices forms a
triangulation of Δᵐ⁻¹ × Δⁿ⁻¹, which is called the staircase triangulation". JCTA pp. 193–194, §2.4
*Mixed subdivisions and tropical arrangements*: "The Cayley trick states that this correspondence is a
bijection between triangulations of Δᵐ⁻¹ × Δⁿ⁻¹ and fine mixed subdivisions of mΔⁿ⁻¹". Both claims
are **supported** in the published version, with the same locators.

### 10. Chen, Li & Sam (2012) — `ChenLiSam2012`

**Citation:** S. Chen, N. Li, S. V. Sam, *Generalized Ehrhart polynomials*, Trans. Amer. Math. Soc.
**364**(1) (2012), 551–569, DOI `10.1090/S0002-9947-2011-05494-2`, arXiv:1002.3658. Crossref confirms
every field (online 2011-06-29). The arXiv journal reference agrees.

**Copy checked:** arXiv v2 (2010-10-30), held.

**Claim supported:** `.org:3780–3782`, "|𝓛ₙ⁽ᵖ⁾| is a quasi-polynomial in p for large p, because the
vertices of Koz⁽ᵖ⁾(n) are polynomials in p [Theorem 1.4]".

**Quotation**, p. 3: "Theorem 1.4. Given polynomials v_{ij}(x), w_{ij}(x) ∈ ℤ[x] for 0 ≤ i ≤ s and
1 ≤ j ≤ d, let n be a positive integer such that w_{ij}(n) ≠ 0 for all i, j. … we can define a
rational polytope P(n) = conv(p₀(n), p₁(n), …, p_s(n)) ∈ ℝᵈ, where pᵢ(n) = (v_{i1}(n)/w_{i1}(n), …,
v_{id}(n)/w_{id}(n)). Then #(P(n) ∩ ℤᵈ) ∈ QP_{≫0}."

**Verdict:** **supported.** C(p, k) = v(p)/k! with v ∈ ℤ[x], so the vertices are of the required
form. **The TAMS numbering is not checked**: the AMS returned its HTML landing page, whose PDF link
goes through a login page.

### 11. Haase, Juhnke-Kubitzke, Sanyal & Theobald (2017) — `HaaseJuhnkeSanyalTheobald2017`

**Citation:** C. Haase, M. Juhnke-Kubitzke, R. Sanyal, T. Theobald, *Mixed Ehrhart polynomials*,
Electron. J. Combin. **24**(1) (2017), P1.10, DOI `10.37236/5815`. Crossref confirms every field
(article number P1.10, issued 2017-01-20). The arXiv API gives arXiv:1509.02254v2, same title and
authors.

**Copy checked:** the EJC version (`literature/haase-…_EJC-24-P1.10.pdf`).

**Claim supported:** `.org:2229–2231` and the statement of `thm-mcmullen`, `.org:2239–2247`.

**Quotation**, p. 4: "For this we recall a result independently due to Bernstein and McMullen; see
[13, Theorem 19.4]. Theorem 2.3 (Bernstein-McMullen). For lattice polytopes P = (P₁, …, P_k) in ℝᵈ,
the function E_P(n₁, …, n_k) := |(n₁P₁ + ··· + n_kP_k) ∩ ℤᵈ| agrees with a multivariate polynomial
for all n₁, …, n_k ∈ ℤ_{⩾0}. The degree of E_P in nᵢ is dim Pᵢ." (The cardinality bars are lost in
the text extraction and are restored here.) [13] is "P. M. Gruber. Convex and Discrete Geometry.
Springer, Berlin, 2007."

**Verdict:** `thm-mcmullen` is a faithful restatement: any dimensions, nᵢ = 0 allowed, degree dim Pᵢ
in nᵢ. "found independently by Bernstein" matches. **Status: verified.** But this paper does not
cite McMullen 1977 (finding 8).

### 12. Hibi, Olsen & Tsuchiya (2018) — `HibiOlsenTsuchiya2018`

**Citation:** T. Hibi, M. Olsen, A. Tsuchiya, *Gorenstein properties and integer decomposition
properties of lecture hall polytopes*, Moscow Math. J. **18**(4) (2018), 667–679, DOI
`10.17323/1609-4514-2018-18-4-667-679`. Crossref confirms authors, title, journal, volume, issue and
year; it gives no pages. The arXiv journal reference reads "Mosc. Math. J. 18 (2018), no. 4,
667-679".

**Copy checked:** arXiv v2 (2016-09-08) only. Unpaywall lists no publisher copy.

**Claims supported and verdicts** (p. 2, read from the page image, unless stated):

- `.org:758–759`, the definition of the s-lecture hall simplex: "For a sequence of positive integers
  s = (s₁, s₂, …, s_d), the s-lecture hall polytope is P_d^{(s)} := {x ∈ ℝᵈ : 0 ≤ x₁/s₁ ≤ x₂/s₂ ≤ ···
  ≤ x_d/s_d ≤ 1}". **Matches eq:lhs.**
- `.org:793–794`, "the reversal equivalence of [HOT18]": "It should be noted that there is a easy
  unimodular equivalence P_d^{(s)} ≅ P_d^{(s_d,…,s₂,s₁)}." **Supported.**
- `.org:1128–1129`, IDP "proved for monotone s and conjectured in general". p. 9: "Theorem 3.1. Let
  s = (s₁, s₂, …, s_d) be a monotone sequence of positive integers. Then the polytope P_d^{(s)} is IDP."
  p. 13: "Conjecture 5.1. For any s = (s₁, ···, s_d), P_d^{(s)} is IDP." **Supported.**
- `.org:1872–1873`, the h*-formula "in the form in which it is quoted in" HOT: "Lemma 1.1 ([13,
  Theorem 5]). For any s, the δ-polynomial of P_d^{(s)} is given by δ(P_d^{(s)}, λ) = ∑_{e∈I_d^{(s)}}
  λ^{asc e}." [13] is Savage–Schuster, JCTA 119 (2012). **Supported.**
- `.org:1893–1897`, `rem-hstar-misprint`: "Given e ∈ I_d^{(s)}, we define the ascent set of e by
  Asc e := {i : 0 ≤ i < d and eᵢ/sᵢ < e_{i+1}/s_{i+1}} with the convention that e₀ = 1 and s₀ = 1."
  With e₀/s₀ = 1, i = 0 can never be an ascent, since e₁/s₁ < 1. **The misprint is present in arXiv
  v2**, and Savage–Visontai (entry 17) state e₀ = 0. See finding 6 for the published version and
  the orientation of the n = 4 figures.

**Status: verified in arXiv v2; the published version was not seen** (finding 6).

### 13. Kupreyeva (2019) — `Kupreyeva2019`

**Citation:** A. Kupreyeva, *Simplices of f-vectors*, Bachelor's thesis LiTH-MAT-EX--2019/05--SE,
Linköpings universitet, 2019. Title page of the held PDF: "LiTH-MAT-EX–2019/05—SE", supervisor Jan
Snellman, examiner Axel Hultman, June 2019. The DiVA URN in the `.bib` note was not re-checked; the
note field is not printed.

**Copy checked:** `literature/Kupreyeva - 2019 - Simplices of f-vectors (bachelor's thesis).pdf`.
Page numbers are the thesis's own. Article 2 relied only on the abstract; everything below was
checked afresh.

**Notation bridge:** the thesis indexes by dimension: "F_p = {f ∈ F | f₀ = p}", F_p^n = F_p ∩ Fⁿ,
with F_p^n in practice the f-vectors with faces of at most n elements (§4.1: the vertices of
conv(F_p^3) are (C(p,1), 0, 0), (C(p,1), C(p,2), 0), (C(p,1), C(p,2), C(p,3))). "T_p^n = the convex
hull of the elements in F_p^n projected to the last (n − 1)-coordinates" and "P_n(p) = the sum which
represents the number of lattice points in T_p^n" (p. 16). Part III's "f₁ = p", in cardinality
indexing, is her f₀ = p. The translation is right.

**Claims supported and verdicts:**

- `.org:1604–1613` ([Section 6.2]: the two counts, closed forms for 3 ≤ n ≤ 6, periods 3, 12, 60,
  60, same degree for n ≤ 30, the ratio q_n, an area argument at n = 3).
  - p. 16, n = 3: "we obtain the polynomials p₀, p₁, p₂ such that P₃(p) = pᵢ when p ≡ i mod 3".
  - p. 32, n = 4: "P₄(p) is a pseudo-polynomial in p. This time it depends on the value of p modulo
    12."
  - p. 50, n = 5: "The sum is a pseudo-polynomial in p and it depends on the value of p modulo 60";
    n = 6: "For n = 6 the number of lattice points in T₆ⁿ is again a pseudo-polynomial which depends
    on the value of p modulo 60."
  - p. 51: "Pₙ(p) is a pseudo-polynomial in p and #F_p^n is a polynomial in p".
  - p. 52: "So far we have observed that both Pₙ(p) and #F_p^n are polynomials of the same degree for
    n ≤ 6. Further computation … shows that it also holds n ≤ 30. Thus, in order to get the fraction
    … we can simply pick the coefficients of the highest terms".
  - Table 6.1, pp. 52–53: 4/5, 4/7, 8/21, 8/33 for n = 3, …, 6. These agree with Part III's
    qₙ = 2ⁿ⁻¹n!(n+1)!/(2n)!, evaluated here.

  **Supported.** "her T^n_p" (`.org:1607`) names the projected simplex, not the count, which she
  calls Pₙ(p); the line reads correctly as naming the hull.
- `.org:1708–1710`, the value 4/5 at n = 3, "an interpolation-and-area argument [Section 4.1]".
  p. 17: "The fraction between the f-vectors and all lattice points in T_p^3 for large p is:
  lim_{p→∞} #F_p^3/P₃(p) = 24/30 = 4/5". pp. 17–18: "let g(x) be the piecewise linear function which
  goes through the points (C(p,2), C(p,3)). Then g(x) = ð₂(x) in those points … lim ∫₀^{C(P,2)} g(x)dx
  / A(T_p^3) = 4/5." (ð is her pseudo-power.) **Supported.**
- `.org:1150–1152` (Euclidean volume, "the one in Kupreyeva's thesis") and `.org:1174–1175`
  ([Section 6.1]). pp. 48–49: "The next step is to find an ON-basis for this plane"; "Since the
  determinant in 6.4 is upper triangular, its value is the product of the diagonal entries, so
  Vol(conv(F_p)) = (1/(p−1)!) ∏_{k=2}^p C(p,k). … Vol(conv(F_p)) = (1/(p·(p−1)!)) ∏_{k=1}^p C(p,k)".
  That is Part III's vol(Koz(n)) = (1/n!)∏ₖ₌₁ⁿ C(n,k) with p = n. **Supported**; see finding 11 for
  "the same triangular determinant".
- `.org:2701–2703` ([Table 4.2], row p = 3; and Table 5.1, row p = 4). p. 26: "Table 4.2 … p = 3:
  (1.80, 0.20), (0.4000, 0.4000, 0.2000)". p. 43, Table 5.1: "p = 4: (4.25, 1.19, 0.06), (0.2917,
  0.4115, 0.2344, 0.0625)". (17/4, 19/16, 1/16) = (4.25, 1.1875, 0.0625), which agrees to the printed
  precision. **Both values are right, but the Table 4.2 sentence sits after the wrong centroid**
  (finding 4).
- `.org:829–831` (her Ehrhart computations for n = 3, 4): §4.3 "Ehrhart polynomial and series of
  T_p^3" and §5.2 "Ehrhart polynomial and series of T_p^4" (contents, p. xi). **Supported.**
- `.org:3930–3933` (acknowledgement: the fraction, the volume and the centroid "were first studied"
  there): abstract, p. iii, and Chapters 4–6 as above. **Supported** as a historical statement.

**Status: verified.**

### 14. Linusson (1999) — `Linusson1999`

**Citation:** S. Linusson, *The number of M-sequences and f-vectors*, Combinatorica **19**(2) (1999),
255–266, DOI `10.1007/s004930050055`. Crossref confirms every field.

**Copy checked:** the published version, `literature/subscription/Linusson_1999_…Combinatorica.pdf`,
which Jan supplied for article 2. pp. 262–263 were read from page images. Article 2's resolution
section established that this version's numbering differs from the preprint's; the passages below
were re-extracted.

**Claims supported and verdicts:**

- `.org:3745–3756` (the second proof): "In his notation |Sₙ⁽ᵖ⁾| = Fᵖ(n) − Fᵖ⁻¹(n) = ∑ₖ₌₁ⁿ Eᵖ(n,k)";
  "Eᵖ(n,k) is a polynomial in p of degree M − C(k+1,2)"; "γₙ = (1/(M−1)!) ∏ᵢ₌₁ⁿ⁻² C(M − C(i+1,2) − 1,
  i) [Theorem 3.3, and Proposition 2.8 with its proof]".
  - p. 262: "Fᵖ(n) := the number of f-vectors of simplicial complexes with f₁ ≤ p and f_j = 0 for all
    j > n." "Note that fᵢ's are indexed by cardinality and not by dimension."
  - p. 263: "Eᵖ(n,k) := the number of f-vectors for simplicial complexes with f₁ ≤ p and f_j = 0 for
    all j > n and with maximal value for f_j when j ≤ k but not for f_{k+1}".
  - p. 263: "Theorem 3.3. Eᵖ(n,k) is a polynomial in p of degree C(n+1,2) − C(k+1,2) and Fᵖ(n) is a
    polynomial in p of degree C(n+1,2), for each fixed n, k ≥ 0. Moreover, Eᵖ(n,k) and Fᵖ(n) has the
    same leading coefficients as Lᵖ(n,k) and Mᵖ(n), respectively."
  - p. 262: "Proposition 2.8. For n ≥ 1, the leading coefficient in Mᵖ(n) is ∏ᵢ₌₀ⁿ⁻² C(C(n+1,2) −
    C(i+1,2) − 1, i) / C(n+1,2)!. Proof. Let c(n,k) be the leading coefficient of Lᵖ(n,k). We will
    show that c(n,k) = ∏ᵢ₌ₖⁿ⁻² C(C(n+1,2) − C(i+1,2) − 1, i) / (C(n+1,2) − C(k+1,2))!".

  At k = 1 the last formula is γₙ, with M = C(n+1,2). **Supported, and the locator is exact**: the
  formula for c(n,k) is in the proof, not the statement, as the manuscript says. Both identities in
  the first quoted sentence are immediate from these definitions; f₁ = p means full at level 1.
  **Exception: "(Linusson's N)" at `.org:3749` is not Linusson's notation** (finding 3).
- `.org:3779–3780`, "|Sₙ⁽ᵖ⁾| is a polynomial in p [Linusson1999]": Theorem 3.3 for Fᵖ(n), and the
  difference of two polynomials. **Supported.**
- `.org:1711–1712`, "Linusson's enumeration of f-vectors": §3, as above. **Supported.**

**Status: verified against the published version**, with finding 3.

### 15. Liu & Solus (2019) — `LiuSolus2019`

**Citation:** F. Liu, L. Solus, *On the relationship between Ehrhart unimodality and Ehrhart
positivity*, Ann. Comb. **23**(2) (2019), 347–365, DOI `10.1007/s00026-019-00429-8`. Crossref
confirms every field.

**Copy checked:** arXiv:1804.08258v1, the only version, **downloaded today** (Unpaywall: green,
submitted version). The published version was not fetched (Springer).

**Claim supported:** `.org:2000–2001`, lecture hall simplices "that are not Ehrhart positive were first
exhibited by Liu and Solus [Theorem 4.3]".

**Quotation**, p. 9: "In fact, as we see with the following theorem, there exist infinitely many
s-lecture hall simplices, even in low dimensions, that are not Ehrhart positive. … Theorem 4.3. For
every d ≥ 3, there exist s-lecture hall simplices of the form P_d^{(1^{k₁}, a, 1^{k₂}, b, 1^{k₃})} that
are not Ehrhart positive."

**Verdict:** **supported** in arXiv v1. "First" is not stated in this paper or in Caicedo–Juhnke–
Poullot, who cite it as prior work ("Liu and Solus [LS19, Theorem 4.3] specified conditions …").
**Status: verified in arXiv v1; Annals numbering not checked.**

### 16. Santos (2005) — `Santos2005`

**Citation:** F. Santos, *The Cayley trick and triangulations of products of simplices*, in Integer
Points in Polyhedra, Contemp. Math. **374**, AMS, 2005, 151–177, DOI `10.1090/conm/374/06904`,
arXiv:math/0312069. Crossref confirms title, author, pages, series and year. The arXiv API gives v3,
whose comment reads "This version has been accepted in 'Proceedings of the Joint Summer Research
Conference on Integer Points in Polyhedra' …".

**Copy checked:** arXiv v3, held.

**Claim supported:** `.org:1340–1343`, the Cayley trick "is a bijection from triangulations to fine
mixed subdivisions [Theorem 1.4 and Section 1.4]".

**Quotations:**

- p. 6 (read from the page image): "Theorem 1.4 (Cayley Trick [10, Theorem 3.1]). (1) For any polyhedral subdivision of
  C(P₁, …, P_k), intersecting its cells with ℝᵈ × {∑(1/k)eᵢ} we get a mixed subdivision of
  (1/k)∑Pᵢ. (2) This correspondence is a poset isomorphism between polyhedral subdivisions of
  C(P₁, …, P_k) and mixed subdivisions of ∑Pᵢ, and bijects regular subdivisions of C(P₁, …, P_k) to
  coherent mixed subdivisions of ∑Pᵢ."
- p. 7, §1.4: "When all the polytopes Pᵢ are copies of a single polytope P ⊂ ℝᵈ, then C(P, …, P) =
  P × Δᵏ⁻¹. Hence, the Cayley Trick is a bijection between subdivisions of the product P × Δᵏ⁻¹ and
  mixed subdivisions of the dilation kP of P."
- p. 4: "The minimal elements in this poset … are the triangulations of P"; pp. 5–6: "The minimal
  elements are called fine mixed subdivisions."

**Verdict:** a poset isomorphism matches minimal elements to minimal elements, so triangulations
correspond to fine mixed subdivisions. **Supported.** **Status: verified in the accepted version;
Contemp. Math. pagination not checked.**

### 17. Savage & Visontai (2015) — `SavageVisontai2015`

**Citation:** C. D. Savage, M. Visontai, *The s-Eulerian polynomials have only real roots*, Trans.
Amer. Math. Soc. **367**(2) (2015), 1441–1466, DOI `10.1090/S0002-9947-2014-06256-9`. Crossref
confirms every field (online 2014-10-10). The arXiv journal reference agrees.

**Copy checked:** arXiv:1208.3831v3 (2013-07-19), held.

**Claims supported and verdicts:**

- `.org:1959`, "h*_{Koz(n)} is real-rooted, hence log-concave and unimodal [SV15]". p. 20: "Lemma
  4.1. For any sequence s of positive integers, ∑_{t≥0} i(Pₙ^{(s)}, t)xᵗ = Eₙ^{(s)}(x)/(1−x)^{n+1}."
  "Corollary 4.2. For any sequence s of positive integers, the h*-polynomial of the s-lecture hall
  polytope has all roots real." "Corollary 4.3. For any sequence s of positive integers, The
  h*-vector of the s-lecture hall polytope is unimodal and log-concave." **Supported.**
- `.org:1872–1873`, the formula "in the form in which it is quoted in" SV. p. 20: "The following is
  a special case of Theorem 5 in [30]", [30] being Savage–Schuster; p. 1: the ascent set is taken
  "with the convention that e₀ = 0 (and s₀ = 1)". **Supported**, and this is the reference point
  for finding 6.

**Status: verified in arXiv v3; TAMS numbering not checked** (no locator is used, so nothing
depends on it).

### 18. Ziegler (1995) — `Ziegler1995`

**Citation:** G. M. Ziegler, *Lectures on Polytopes*, GTM 152, Springer, New York, 1995, DOI
`10.1007/978-1-4613-8431-1`. Crossref confirms it, as "Updated Seventh Printing of the First
Edition", 1995.

**Copy checked:** `math-library/textbooks/combinatorics/ziegler-1995-lectures-polytopes.pdf`, the
corrected and updated printing of 2007, whose imprint page carries this DOI. Article 1 relied on
Proposition 7.12; Part III relies on something else, checked afresh.

**Claim supported:** `.org:2343–2347`, x ∈ relint C iff every linear functional maximised at x is
constant on C; a relative boundary point lies in a proper face [Chapter 2].

**Quotation**, p. 60: "Lemma 2.9. Let P be a polytope of dimension k := dim(P) in some ℝᵈ (k ≤ d).
Then the following conditions are equivalent for y ∈ P. (i) y is not contained in a proper face of
P, (ii) if ax ≤ a₀ is valid for P, with equality for y, then ax = a₀ holds for all x ∈ P, …" with
relint(P) defined just before it as "the interior of P with respect to the embedding of P into its
affine hull aff(P)".

**Verdict:** (i) ⇔ (ii) is exactly the characterisation used. **Supported; Lemma 2.9 is the exact
locator. Status: verified.**

### 19. Software papers — `BrunsIchim2010`, `Verdoolaege2007`, `Mathlib2020`, `deMouraUllrich2021`

All four are cited only as the reference for a program used (`.org:3363`, `3370`, `3418`,
`3939–3941`). The only claim is that the paper is the right reference for that program. Copies of
all four were **downloaded today** (none was held before).

- **Bruns & Ichim (2010)**, *Normaliz: algorithms for affine monoids and rational cones*, J. Algebra
  **324**(5), 1098–1113, DOI `10.1016/j.jalgebra.2010.01.031`. Crossref confirms every field. Copy:
  arXiv:0910.2845v2. Abstract: "Normaliz is a program for the computation of Hilbert bases of
  rational cones and the normalizations of affine monoids. … In this paper we present the algorithms
  implemented in the program." The version the `.bib` note names, 3.11.1, is the one installed on
  jts-pc (`normaliz --version`: "Normaliz 3.11.1"). **Verified.**
- **Verdoolaege, Seghir, Beyls, Loechner & Bruynooghe (2007)**, *Counting integer points in parametric
  polytopes using Barvinok's rational functions*, Algorithmica **48**(1), 37–66, DOI
  `10.1007/s00453-006-1231-0`. Crossref confirms every field. Copy: the authors' version from Lirias
  (KU Leuven). Its title page reads "Algorithmica (2007) DOI: 10.1007/s00453-006-1231-0", and p. 26
  "using version 0.13 of our own barvinok library". jts-pc has barvinok 0.41.9; the manuscript does
  not state a version. **Verified.**
- **The mathlib Community (2020)**, *The Lean mathematical library*, CPP 2020, 367–381, DOI
  `10.1145/3372885.3373824`. Crossref confirms every field. Copy: arXiv:1910.09336v2, whose arXiv
  record carries the same DOI. Abstract: "This paper describes mathlib, a community-driven effort to
  build a unified library of mathematics formalized in the Lean proof assistant." **Verified.** Its
  biblatex label prints as "[The20]", from the corporate author; that is cosmetic.
- **de Moura & Ullrich (2021)**, *The Lean 4 theorem prover and programming language*, CADE 28, LNCS
  12699, 625–635, DOI `10.1007/978-3-030-79876-5_37`. Crossref confirms every field. Copy: the CC-BY
  version in KIT's repository. Abstract: "Lean 4 is a reimplementation of the Lean interactive
  theorem prover (ITP) in Lean itself." **Verified.**

### 20. OEIS — `OEIS`

**Citation:** OEIS Foundation Inc., *The On-Line Encyclopedia of Integer Sequences*,
<https://oeis.org>, as article 2.

**Claim supported:** `.org:1915–1917`: "The sequence |𝓛ₙ| = 1, 2, 5, 20, 162, 1981, 60993, 3576524
(n = 1, …, 8) … was not in the OEIS [OEIS] when checked in October 2026."

**Check:** OEIS JSON search for that sequence, for 5, 20, 162, 1981, 60993, and for 20, 162, 1981:
no result, 2026-11-14 17:56. The same interface returned A000045 for 1, 1, 2, 3, 5, 8, 13, 21, 34,
so the empty answers are real. **Still absent; the dated claim stands.** Under the workspace's OEIS
convention this is a candidate for Jan to submit, never to be submitted on his behalf.

---

## B. No primary copy available — registry check instead

### 21. McMullen (1977) — `McMullen1977` — **verified the same evening** (was: not verified, source not available)

**Citation:** P. McMullen, *Valuations and Euler-type relations on certain classes of convex
polytopes*, Proc. London Math. Soc. (3) **35**(1) (1977), 113–135, DOI `10.1112/plms/s3-35.1.113`.
Crossref: same title, author "McMullen, P.", volume s3-35, issue 1, pp. 113–135, July 1977, Wiley.
Beck–Robins' bibliography lists the same paper with the same data (item 172, draft p. 274).

**Claim supported:** `.org:2229–2230`, `prop-linear-coeff` "also follows from a theorem of McMullen
[McMullen1977], found independently by Bernstein".

**Verification (first pass):** bibliographic only. Not in `literature/` or `math-library`;
Unpaywall says `is_oa: false`, closed. No held source connected the multivariate theorem to this
paper: Haase et al. point to Gruber's book, and Beck–Robins cite this paper for a different result.

**Verification (the same evening):** Jan supplied the Wiley PDF through the LiU subscription, now
`literature/subscription/mcmullen-1977-valuations-euler-type-relations-convex-polytopes_PLMS.pdf`.
The PDF is a scan with an OCR text layer; the passages below are transcribed from it with the
mathematical symbols restored.

- p. 117 (§2): "For the rest of this section, we restrict our attention to groups Λ which are
  d-dimensional vector spaces over some subfield of ℝ, or discrete lattices." So ℤᵈ is within the
  hypotheses of the results that §3 builds on.
- p. 121 (§3): "THEOREM 6. Let φ be a Λ-valuation, and let P₁, …, P_k ∈ 𝒫(Λ). Then for integers
  n₁, …, n_k ≥ 0, φ(n₁P₁ + … + n_kP_k) is a polynomial in n₁, …, n_k of total degree at most d.
  Moreover, the coefficient of n₁^r₁ … n_k^r_k is a homogeneous Λ-valuation of degree rᵢ in Pᵢ."
- p. 127 (§6, *Examples and applications*): "If G(P) is the number of lattice points in the lattice
  polytope P, then G is a ℤᵈ-valuation on 𝒫(ℤᵈ)."

Theorem 6 with Λ = ℤᵈ and φ = G gives the polynomiality of `thm-mcmullen` / HJST Theorem 2.3, for
any lattice polytopes and all nᵢ ≥ 0, with total degree at most d. HJST's finer statement, degree
dim Pᵢ in nᵢ, is not stated in this form in Theorem 6 and was not derived here; for that, the
quotation from HJST (entry 11) is the source. **Supported** for what `.org:2230` attributes to
McMullen, namely the theorem. The paper does not mention Bernstein; that half of `.org:2230` rests on
HJST, who credit both.

### 22. Savage & Schuster (2012) — `SavageSchuster2012` — **verified the same evening** (was: not verified against the text)

**Citation:** C. D. Savage, M. J. Schuster, *Ehrhart series of lecture hall polytopes and Eulerian
polynomials for inversion sequences*, J. Combin. Theory Ser. A **119**(4) (2012), 850–870, DOI
`10.1016/j.jcta.2011.12.005`. Crossref and OpenAlex confirm every field.

**Claims supported:** `.org:758–759`, the definition of the s-lecture hall simplex, cited jointly with
HOT; `.org:1871–1872`, "Savage and Schuster's formula for the h*-polynomial of a lecture hall
polytope as an s-Eulerian polynomial".

**Verification:** no copy. No arXiv version exists (arXiv search by authors and title: nothing).
Unpaywall and OpenAlex list only the publisher's open-archive copy (bronze), which ScienceDirect does
not serve to scripts. **Two independent held sources attribute the formula to this paper's Theorem
5:** HOT, Lemma 1.1, "([13, Theorem 5])", and SV, p. 20, "a special case of Theorem 5 in [30]". The
definition at `.org:758` is independently verified in HOT (entry 12). The attribution is therefore
corroborated, and no locator into this paper is used. Jan can open it free in a browser.

**Verification (the same evening):** Jan saved the JCTA PDF from Elsevier's open archive, now
`literature/savage-schuster-2012-ehrhart-series-lecture-hall-polytopes-eulerian-polynomials_JCTA.pdf`.

- The definition, p. 852, §2.2 *Lecture hall polytopes*: "For a sequence s = {sᵢ}ᵢ≥₁ of positive
  integers, define the lecture hall polytope Pₙ^(s) by Pₙ^(s) = {λ ∈ ℝⁿ | 0 ≤ λ₁/s₁ ≤ λ₂/s₂ ≤ ⋯ ≤
  λₙ/sₙ ≤ 1}." This is `eq:lhs` at `.org:762`, with D for n. **Supported.**
- The h*-formula. Abstract: "We show that for any sequence s of positive integers: (i) the
  h*-vector of the s-lecture hall polytope is the ascent polynomial for the associated s-inversion
  sequences". p. 857: "Theorem 5. Let s be any sequence of positive integers. For integer n ≥ 0,
  Σ_{t≥0} fₙ^(s)(t; u, q, z) xᵗ = Σ_{e∈Iₙ^(s)} x^{asc e} u^{amaj e} q^{lhp e} z^{|e|} /
  ∏ᵢ₌₀ⁿ (1 − x uⁿ⁻ⁱ q^{sᵢ₊₁+⋯+sₙ})", where (p. 856) fₙ^(s)(t; u, q, z) sums over the lattice
  points of tPₙ^(s). p. 861, Theorem 8, whose proof begins "The first identity is Theorem 5 with
  u = q = z = 1". At u = q = z = 1 the left side is the Ehrhart series and the numerator is the
  ascent polynomial. This is the formula `.org:1871–1872` specialises, and it is the theorem that
  HOT and Savage–Visontai cite as "Theorem 5". **Supported.**

### 23. Stanley (1996) — `Stanley1996` — **NOT VERIFIED — source not available**

**Citation:** R. P. Stanley, *Combinatorics and Commutative Algebra*, 2nd ed., Progress in
Mathematics 41, Birkhäuser Boston, 1996, DOI `10.1007/b139094` (corrected after article 2's finding
1). Crossref: title, Progress in Mathematics, Birkhäuser Boston, 1996, ISBNs 9780817643690 /
9780817644338. It lists no author. Unpaywall: closed.

**Claim supported:** `.org:1858–1859`, "by a theorem of Stanley this is equivalent to the Ehrhart ring
of P being a Gorenstein ring". This is a new use; article 2 cited the book for the Stanley–Reisner
construction.

**Verification:** none against the text. The book is still in neither `literature/` nor
`math-library`, as recorded for article 2 (the NAS library was enumerated then). The secondary
evidence points elsewhere (finding 9): HOT p. 2 attribute the Gorenstein ⇔ symmetric-h* equivalence
to Stanley's 1978 *Hilbert functions of graded algebras*. Beck–Robins (Ch. 4, Notes 7, p. 98) state
the equivalence for Gorenstein polytopes in their own definition, without naming Stanley.

*Added 2026-11-14, later the same day:* `math-library` holds Stanley's *Enumerative Combinatorics*,
volumes 1 and 2, and neither stands in for this book. In volume 1 (2nd ed., searchable text)
"Gorenstein" occurs only for Gorenstein* posets (index: pp. 312, 403). Volume 2 has no text layer;
its subjects (trees, algebraic and D-finite generating functions, symmetric functions) are not where
the theorem lives. Neither *Combinatorics and Commutative Algebra* nor the 1978 paper is in the
library.

### 24. Kruskal (1963), Katona (1968) — `Kruskal1963`, `Katona1968`

**Citations:** as in article 1's certificate, entries 12–13. The current `.bib` fields match,
including Katona's corrected pp. 187–207.

**Claim supported:** `.org:578`, "The set Sₙ is described by the Kruskal–Katona theorem
[Kruskal1963; Katona1968]". A historical attribution, the same use as in articles 1 and 2.

**Verification:** reused from article 1: MathSciNet MR0154827 and MR0290982, Jan's lookups of
2026-09-14. No copies. Corroborated by Kupreyeva p. 9: "The following result, found by Kruskal [9]
and Katona [7], gives a complete description of the f-vectors of simplicial complexes." **Status:
bibliographically verified; no passage relied on.**

### 25. Software without a paper — `Macaulay2`, `SageMath`

**Citations:** D. R. Grayson, M. E. Stillman, *Macaulay2, a software system for research in algebraic
geometry (Version 1.26.06)*, 2026, macaulay2.com; The Sage Developers, *SageMath, the Sage
Mathematics Software System (Version 10.9)*, 2026, sagemath.org.

**Claim supported:** `.org:3939–3940`, used for the computations.

**Verification:** the versions named exist: on jts-pc today, `M2 --version` prints 1.26.06 and
`sage --version` prints 10.9. Which machine ran which computation was not traced. **Status:
verified as far as a software citation can be.**

---

## Downloaded today (open access, now in `literature/`)

Each has a section in `literature/README.org`, "Copies fetched for Part III's reference certificate".

1. `liu-solus-2018-ehrhart-unimodality-vs-positivity_arXiv-1804.08258.pdf`. Liu–Solus, arXiv v1.
2. `caicedo-juhnke-poullot-2025-ehrhart-nonpositivity-s-lecture-hall_arXiv-2508.18890v4.pdf`.
   Caicedo–Juhnke–Poullot, arXiv v4, beside the held v3.
3. `bruns-ichim-2009-normaliz-algorithms-affine-monoids-rational-cones_arXiv-0910.2845.pdf`.
   Bruns–Ichim, arXiv v2.
4. `verdoolaege-seghir-beyls-loechner-bruynooghe-2007-counting-integer-points-parametric-polytopes_Lirias-preprint.pdf`.
   Verdoolaege et al., authors' version (Lirias).
5. `mathlib-community-2019-lean-mathematical-library_arXiv-1910.09336.pdf`. The mathlib Community,
   arXiv v2.
6. `demoura-ullrich-2021-lean4-theorem-prover-programming-language_CADE28-KIT.pdf`. de Moura–Ullrich,
   CC-BY (KIT).

## What could not be obtained, and what Jan would need

**Through a browser or the LiU subscription:**

1. ~~**McMullen 1977**, `10.1112/plms/s3-35.1.113` (Wiley, closed).~~ Supplied by Jan the same
   evening; verified (entry 21).
2. **Hibi–Olsen–Tsuchiya 2018, published**, `10.17323/1609-4514-2018-18-4-667-679` (Moscow Math. J.).
   It decides whether `rem-hstar-misprint`'s claim holds for the printed paper, and confirms the
   number of Lemma 1.1 (finding 6).
3. ~~**Ceballos–Padrol–Sarmiento 2015, JCTA**, `10.1016/j.jcta.2014.10.009`.~~ Supplied by Jan the
   same evening; numbering unchanged (entry 9).
4. ~~**Savage–Schuster 2012**, `10.1016/j.jcta.2011.12.005`.~~ Supplied by Jan the same evening;
   verified (entry 22).
5. Optional, numbering checks only: **Liu–Solus 2019, published**, `10.1007/s00026-019-00429-8`
   (Theorem 4.3); **Chen–Li–Sam 2012, TAMS**, `10.1090/S0002-9947-2011-05494-2` (Theorem 1.4); **Santos
   2005, Contemp. Math.**, `10.1090/conm/374/06904` (Theorem 1.4, §1.4; the arXiv v3 read is the
   accepted version); **Savage–Visontai 2015, TAMS**, `10.1090/S0002-9947-2014-06256-9` (no locator
   used). The AMS's two TAMS PDFs went to a login page for scripted requests.

**Books in neither `literature/` nor `math-library`:**

6. **Stanley, *Combinatorics and Commutative Algebra*, 2nd ed.**, `10.1007/b139094`, for the
   Gorenstein theorem's locator; or cite Stanley 1978 instead (finding 9).
7. **Beck–Robins, 2nd ed., the 2015 Springer printing.** Only the authors' 2020 draft of that edition
   is held, and all the Beck–Robins locators were checked there. Optional.
8. **Kruskal 1963 and Katona 1968** (proceedings volumes). As for articles 1 and 2: attribution only,
   bibliographic data from MathSciNet. No action needed.

## Which entries rest on a registry check rather than a quotation

Stanley1996 (Crossref only), Kruskal1963 and Katona1968 (MathSciNet, reused), Macaulay2 and
SageMath (installed versions), and OEIS (a database query, which is the claim itself). Every other
printed key is backed by a passage quoted above from a held copy. (McMullen1977 and
SavageSchuster2012 were on this list until the same evening.)

---

*Prepared 2026-11-14 by Claude (Claude Code, on jts-pc). Read-only with respect to the manuscript and
its `.bib`: nothing there has been changed, and the corrections suggested above are for Jan to apply.
Every quotation in section A was extracted from the named PDF during preparation of this document.
Nothing in it was supplied from memory of the cited works.*
