# Certificate of Existence — references cited in article 2

*(`ai-workspace/20-projects/exterior-convex/article/exterior-convex_article2_latest.org`, at
commit `98514c11` of 2026-10-08; written 2026-10-08 by Claude (Claude Code, on jts-office), at
Jan Snellman's request. **Extended 2026-10-09** (findings 5 and 6, once Jan supplied both books)
**and 2026-10-10** (the two new Horn–Johnson locators, the new `FlajoletSedgewick2009`, and one
correction to the manuscript) — both extensions are dated sections at the end, so the original
text above them stands as written. Line numbers refer to that `.org` source, which is the source
of truth.
The bibliography checked is `literature/exterior-convex-references.bib` in the same project.)*

## Purpose

Same purpose as article 1's certificate (`REFERENCE-CERTIFICATE.md` beside this file): arXiv's
2026 enforcement policy treats hallucinated or fabricated references as evidence of unchecked LLM
output, and this series was written with substantial AI assistance. For every key article 2 cites
this document records the bibliographic entry as checked; each place the article relies on a
specific statement, with its `.org` line; and *either* the passage relied on, quoted from a held
copy of the source with a page/number, plus a verdict, *or* an explicit statement that no primary
copy was available.

## Method, stated once

- **Quotations** were taken from `pdftotext` extractions (with `-layout`) of the PDFs in
  `20-projects/exterior-convex/literature/`, and where the extraction garbled the mathematics, from
  page renderings of the same PDFs read by eye (Linusson pp. 18–19; Amata–Crupi 2020KK pp. 43–44).
  Mathematics is transcribed into Unicode; the words are verbatim. Nothing was reconstructed from
  memory or from secondary descriptions.
- **Sources consulted, in order:** `literature/` (incl. `subscription/`), then
  `/home/jan/Repositories/math-library/` (searched by author, title and key in both the file tree
  and `math-library.bib`). Nothing paywalled was downloaded. The only network checks were metadata
  ones: Crossref (`api.crossref.org`) for each DOI, Unpaywall for Linusson's DOI, the arXiv API for
  the companion paper, and the OEIS through SageMath's client. All were made on 2026-10-08.
- **Entries reused from article 1's certificate** (Kozlov, Kruskal, Katona, Sköldberg, Kupreyeva,
  and the AHH quotation) were reused only where article 2 relies on the same statement. The
  passage was re-extracted in each case. Where article 2 relies on something different, it was
  checked afresh.

## Findings worth reading first

1. **Three DOIs in the `.bib` are wrong.** The DOIs are not printed in the PDF's reference list,
   but they are in the `.bbl`, which ships with an arXiv source.
   - `AmataCrupi2020`: `10.24330/ieja.663116` **does not resolve in Crossref**. The held PDF's
     own header and Crossref both give **`10.24330/ieja.663094`** (title, authors, IEJA 27,
     271–287, all match).
   - `AramovaHerzogHibi1997`: `10.1006/jabr.1996.6908` resolves to **a different paper**
     (U. Ray, *Some subalgebras of the Monster Lie algebra and the modular polynomial*, J. Algebra
     191, 109–126). The correct DOI is **`10.1006/jabr.1996.6903`**: Crossref gives the AHH title,
     authors and pp. 174–211, and the held PDF's header reads "ARTICLE NO. JA966903".
   - `Stanley1996`: `10.1007/978-1-4612-0759-7` resolves to **a different book** (P. Ribenboim,
     *The New Book of Prime Number Records*, Springer 1996). Crossref's record for *Combinatorics
     and Commutative Algebra*, Birkhäuser Boston 1996, Progress in Mathematics, is
     **`10.1007/b139094`**. The `url` field has the same error.
2. **"Amata and Crupi's Theorem 4.2" is in the *other* Amata–Crupi paper.** The theorem with
   conditions (a), (b), (c) that `.org:1513`, `1517` and `2930` rely on is Theorem 4.2 of
   **`AmataCrupi2020KK`** (An. Şt. Univ. Ovidius Constanţa 28(2), pp. 43–44). `AmataCrupi2020`
   (IEJA) has no Theorem 4.2: its §4 is "Examples", and its 4.2 is a *Remark*. The manuscript never
   attaches a citation key to "Theorem 4.2", and the nearest one (`.org:618`) cites both papers, so
   a reader cannot tell which paper is meant. Suggested fix: write `[cite:@AmataCrupi2020KK Theorem
   4.2]` at `.org:1513`.
3. **The "(a) ⇔ (c) half is sound" claim (`rem-explicit-inverse`, `.org:1688`) is not what that
   paper's proof provides.** In AmataCrupi2020KK the proof runs (a) ⇒ (b) ⇒ (c) ⇒ (a), so (a) ⇒ (c)
   is proved *through* (b). The existence and uniqueness of a lex representative is, however,
   stated and proved on its own as **Theorem 3.2 of `AmataCrupi2020` (IEJA, p. 278, "The
   Lex–Algorithm")**. Citing that theorem for this half would make the remark's claim checkable.
   See entry 4.
4. **The counterexample's "it satisfies (b)" depends on how (b) is read** (`.org:1689–1693`). As
   printed, the third clause of (b) asks that hᵢ = ∑_{j=N+1}^r C(n, i−f_j) + a, with "a a positive
   integer less than C(n, i−f_N)", for i = s+1, …, f_r+n. For n = 1, r = 2, d = (0,0), H = (1,2),
   that clause at i = 1 needs 2 = (2−N) + a with 0 < a < 1, which no integer satisfies. So
   **under the literal wording, (1,2) fails (b)**. But so does H = (2,2), the Hilbert sequence of F
   itself, so the literal wording is itself defective, and some reading with a looser bound on a is
   evidently intended. The remark should say which reading of (b) it uses. This is not a
   citation-existence problem, but the remark makes a claim about the source that a referee will
   check against the printed text.
5. **Linusson was checked against the author's preprint, not the published version.** The only
   copy anywhere in reach (`literature/`, and the same file in `math-library/preprints/`) is the
   25-page `preprint.dvi` rendering. The published Combinatorica version is 12 pages (255–266) and
   is not open access (Unpaywall: `is_oa: false`). In the preprint, every statement article 2
   attributes to Linusson is present, exactly as numbered: Theorem 5.2, Theorem 5.3, Proposition
   5.4, Tables 5 and 6, and the 100 + 99 printed table entries. **Whether the published version
   keeps the same theorem, proposition and table numbers, and still prints both appendix tables,
   has not been checked.** That needs one look at the published PDF through LiU.
6. **`HornJohnson2013` is not verified.** The book is not in `literature/` or `math-library`, and
   being commercial it was not fetched. The `.bib` note's "believed Theorem 8.4.5" therefore
   remains unconfirmed, as does the chapter-level "Ch. 8" locator at `.org:2494`. Crossref confirms
   the bibliographic data (2nd ed., CUP, DOI `10.1017/CBO9781139020411`, ISBN 978-0-521-83940-2
   among those listed). Crossref's issue date is **2012-10-22**. The `.bib` says 2013, the usual
   copyright year of the printing, which can only be settled from the copyright page.
7. **Minor imprecision.** `.org:667` says "The asymptotics in n, the analogue of Linusson's own
   §2.2". In the preprint, §2.2 ("Keeping p fixed") gives *exact* formulas for p = 1, 2, 3, not
   asymptotics. Asymptotics with p fixed is posed as an open question (§6, Problem 4). Suggested:
   "cf. Linusson's §2.2 and Problem 4".

---

## A. Primary source held — quoted

### 1. Linusson (1999) — `Linusson1999`

**Citation:** S. Linusson, *The number of M-sequences and f-vectors*, Combinatorica **19**(2)
(1999), 255–266, DOI `10.1007/s004930050055`. Crossref confirms every field.

**Copy checked:** the author's 25-page preprint (`literature/Linusson - 1999 - …pdf`, PDF title
`preprint.dvi`), *not* the published version. See finding 5. Page numbers below are the preprint's.

**Claims supported and verdicts:**

- `.org:460`, `.org:517–521` (abstract and introduction: a count by "a recursion on compressed
  complexes: peel off the last vertex, split … and record how far the first part is filled").
  Preprint p. 5, proof of Thm 2.1, which Thm 5.2's proof reuses via Thm 4.3: "Partition the
  multisets in M into two disjoint parts depending on whether the multiset contains x_p or not …
  Let i, i ≥ k, be the largest level in M₁ that is totally filled." **Says what is claimed.**
- `.org:908` — Definition `def-linusson`, cited "[Lin99, §5]". Preprint p. 17–18: "F^p(n) :=the
  number of f-vectors of simplicial complexes with f₁ ≤ p and f_j = 0 for all j > n"; "we include
  both (0, 0, …), the f-vector of the empty simplicial complex, and (1, 0, 0, …), the f-vector for
  the simplicial complex containing only the empty set"; "E^p(n, k) :=the number of f-vectors for
  simplicial complexes with f₁ ≤ p and f_j = 0 for all j > n and with maximal value for f_j when
  j ≤ k but not for f_{k+1}, i.e., fᵢ = C(p,i) for i ≤ k but f_{k+1} < C(p,k+1)." **Says what is
  claimed.**
- `.org:922` — Theorem `thm-linusson`, cited "[Lin99, Theorem 5.2]". Preprint p. 18 (read from the
  page image): "Theorem 5.2. For 0 ≤ k, 1 ≤ n ≤ p we have the recursions (11) F^p(n) = 1 +
  ∑_{i=0}^n E^{p−1}(n,i)F^{p−1}(i−1), if n < p; 1 + F^p(p−1), if n = p, and (12) E^p(n,k) =
  ∑_{i=k}^n E^{p−1}(n,i)E^{p−1}(i−1,k−1), if k ≤ n < p; E^p(p−1,k), if k < n = p; 1, if k = n = p,
  where the first recursion is implied by the second." **The transcription matches exactly.**
  *Note:* the theorem's closing boundary values and "Moreover F^p(n) = ∑_k E^p(n,k)" are not
  part of Theorem 5.2 itself. They come from the prose just before it, p. 18: "F^p(−1) = 1,
  F^p(0) = 2 for all p ≥ 0 and F⁰(n) = 2 for all n ≥ 0"; "for every pair p ≥ 0, n ≥ −1, that
  E^p(n,−1) = 1, E^p(n,n) = 1 and E^p(n,k) = 0 for k > n"; and (10), "F^p(n) = ∑_{k=−1}^n
  E^p(n,k), for all p ≥ n ≥ 0". All of these are correctly transcribed. Only the locator is
  slightly broader than "Theorem 5.2"; "§5, Theorem 5.2 and (10)" would be exact.
- `.org:946–952` — Remark `rem-transcription`: "all 100 printed entries of his Table 5 and all
  99 of his Table 6". Preprint pp. 24–25: Table 5 ("Table of F^p(n), the number of f-vectors for
  simplicial complexes of dimension at most n−1 and with at most p vertices") has rows p = 0…9 by
  columns n = −1…8, which is 100 entries. Table 6 ("Table of E^p(p,k), the refinement of F^p(p)")
  has rows p = 0…8 by columns k = −1…8 plus a column F^p(p), which is 99 entries. **Counts
  confirmed.** The "wrinkle": the definition's clause "f_{k+1} < C(p,k+1)" against the stated
  "E^p(n,n) = 1". Both are on p. 18 as quoted. **The remark's reading is accurate.**
- `.org:974` — "|S₉| = F⁹(7) = 3617645, a value printed in Linusson's Table 5". Table 5, row p = 9:
  "1 2 11 131 2189 35926 398663 2016372 3617645 3718353" for n = −1…8, so F⁹(7) = 3617645.
  **Confirmed.**
- `.org:1052–1053` — "Linusson's clause 'f_j = 0 for j > m'" and "'fᵢ = C(n,i) for i ≤ k but
  f_{k+1} < C(n,k+1)'". These are the definitions quoted above, at p = n. **Confirmed.**
- `.org:1064`, `.org:3036–3038`, `.org:3049`, `.org:3059` — "Table 6 gives E^p(p,k) … with F^p(p)
  recovered as a row sum in the last column". The Table 6 caption is as quoted, and its last column
  is headed F^p(p). **Confirmed.**
- `.org:3175`, `.org:3186` — Table 5 "indexed by his two parameters p and n"; "5, 10, 26, 96, 553
  is exactly the diagonal F^n(n) of Linusson's Table 5 (equivalently, the last column of his Table
  6)". Table 5 has F²(2) = 5, F³(3) = 10, F⁴(4) = 26, F⁵(5) = 96, F⁶(6) = 553, and Table 6's last
  column reads 2, 3, 5, 10, 26, 96, 553, 5461, 100709. **Confirmed.**
- `.org:2589`, `.org:2593`, `.org:2681`, `.org:2707`, `.org:2946` — Theorem 5.3. Preprint p. 19
  (page image): "Theorem 5.3. E^p(n,k) is a polynomial in p of degree C(n+1,2) − C(k+1,2) and
  F^p(n) is a polynomial in p of degree C(n+1,2), for each fixed n, k ≥ 0. Proof: Identical to
  the proof of Theorem 2.4." **Says what is claimed**, including the degree formula used at
  `.org:2707`. *Scope note:* the theorem is stated for n, k ≥ 0. Entries E^p(τ, ρ−1) with ρ = 0
  (k = −1) are the constant 1 by the boundary value E^p(n,−1) = 1, so `.org:2589`'s "polynomial in
  p … by Linusson's Theorem 5.3" covers them only trivially. That is harmless, but strictly the
  boundary value is what applies there.
- `.org:2681`, `.org:2711`, `.org:2811` — Proposition 5.4. Preprint p. 19 (page image):
  "Proposition 5.4. The coefficient for the term of highest degree in E^p(n,k) is (13)
  ∏_{i=k}^{n−2} C(C(n+1,2) − C(i+1,2) − 1, i) / (C(n+1,2) − C(k+1,2))! If k ≥ n−1, then the empty
  product in the numerator should be interpreted as 1. The coefficient for the term of highest
  degree in F^p(n) is the same as in E^p(n,0), so take k = 0 in (13). Proof: Identical to the
  proof of Proposition 2.5." The manuscript uses only that the leading coefficient exists and is
  positive, and applies it to E^p(n,1) and E^p(n,κ) with κ ≥ 0. **Consistent with the
  statement.**
- `.org:667` — "Linusson's own §2.2". **Imprecise**; see finding 7. Preprint p. 5: "2.2. Keeping
  p fixed." gives Corollary 2.2, the exact formulas for p = 1, 2, 3. p. 22: "Problem 4: … It still
  remains an interesting problem to give such results when keeping p fixed, p ≥ 4."

**Bib entry:** correct (Crossref). **Status: verified against the preprint; published-version
numbering not verified (finding 5).**

### 2. Amata & Crupi (2020), IEJA — `AmataCrupi2020`

**Citation:** L. Amata, M. Crupi, *Hilbert functions of graded modules over an exterior algebra:
an algorithmic approach*, Int. Electron. J. Algebra **27** (2020), 271–287. **DOI as in `.bib`,
`10.24330/ieja.663116`, is wrong; it should be `10.24330/ieja.663094`** (finding 1). Printed in
the PDF as [AC20b].

**Claims supported and verdicts:**

- `.org:775` — `[cite:@AmataCrupi2020 Definition 2.1]`. p. 273: "Definition 2.1. A graded
  submodule M of F is a monomial submodule if M is a submodule generated by monomials of F, i.e.,
  M = I₁g₁ ⊕ ··· ⊕ I_rg_r, with Iᵢ a monomial ideal of E, for each i." **Says what is claimed.**
- `.org:1492–1497`, `.org:1505–1506`, `.org:2929` — "Definition 2.6 ⇔ 2.7". p. 274: "Definition
  2.6. Let L be a monomial submodule of F. L is a lexicographic submodule (lex submodule, for
  short) if for all u, v ∈ Mon_d(F) with v ∈ L and u >lexF v, one has u ∈ L, for every d, i.e.,
  Mon_d(L) is a lexF segment of degree d, for each degree d. Definition 2.6 is equivalent to the
  following one [3, Proposition 3.12] (see also [7, Proposition 3.8]). Definition 2.7. Let L be a
  graded submodule of F. L is a lex submodule of F if L = ⊕_{i=1}^r Iᵢgᵢ, with Iᵢ lex ideals of E
  (i = 1, …, r), and (e₁, …, eₙ)^{ρᵢ+fᵢ−f_{i−1}} ⊆ I_{i−1}, for i = 2, …, r, with ρᵢ = indeg Iᵢ."
  **Says what is claimed:** the exponent ρᵢ + dᵢ − d_{i−1} and the inclusion into L_{i−1} match
  `.org:1494–1495`. The source does not prove the equivalence itself; it cites it from [3, Prop.
  3.12].
- `.org:1660` — "Amata and Crupi's module order makes g₁'s monomials the largest". p. 274:
  "ugᵢ >lexF vg_j if i < j or i = j and u >lex v." **Confirmed.**
- `.org:897` — negative generator degrees "as they are in Amata and Crupi". Example 2.8, p. 275:
  "deg g₁ = −2, deg g₂ = −1 and deg g₃ = 3". **Confirmed.**
- `.org:1513`, `.org:1688` — "Theorem 4.2". **Not in this paper.** See entry 3 and finding 2. The
  statement this paper *does* make that matches the half used is p. 278: "Theorem 3.2. (The
  Lex–Algorithm) Let (h_{f₁}, …, h_{f_r+n}) be the Hilbert sequence of a graded E-module F/M. Then,
  there exists a unique lex submodule L of F such that H_{F/L} = H_{F/M}."

**Status: Definitions verified; bib DOI wrong; Theorem 4.2 misattributable (finding 2).**

### 3. Amata & Crupi (2020), An. Şt. Univ. Ovidius Constanţa — `AmataCrupi2020KK`

**Citation:** L. Amata, M. Crupi, *A generalization of Kruskal–Katona's theorem*, An. Şt. Univ.
Ovidius Constanţa **28**(2) (2020), 35–51, DOI `10.2478/auom-2020-0018`. Crossref confirms every
field. Printed as [AC20a].

**Claims supported:** `.org:618` (cited jointly with entry 2 for the theory of lex submodules);
and, by content though not by key, "Theorem 4.2, implication (a) ⇔ (c)" at `.org:1513`,
`.org:1688–1691` and `.org:2930`.

**Quotation**, pp. 43–44 (page images): "Theorem 4.2. Let (f₁, f₂, …, f_r) ∈ ℤ^r be an r–tuple
such that f₁ ≤ f₂ ≤ ··· ≤ f_r and let (h_{f₁}, h_{f₁+1}, …, h_{f_r+n}) be a sequence of
nonnegative integers. Set s = min{k ∈ [f₁, f_r+n] : h_k ≠ 0}, and r̃_j = |{p ∈ [r] : f_p = s+j}|,
for j = 0, 1. Then the following conditions are equivalent: (a) ∑_{i=s}^{f_r+n} hᵢtⁱ is the
Hilbert series of a graded E-module F/M, with F = ⊕_{i=1}^r Egᵢ finitely generated graded free
E-module with the basis elements gᵢ of degrees fᵢ; (b) h_s ≤ r̃₀, h_{s+1} ≤ nr̃₀ + r̃₁, hᵢ =
∑_{j=N+1}^r C(n, i−f_j) + a, where a is a positive integer less than C(n, i−f_N), 0 < N ≤ r, and
h_{i+1} ≤ ∑_{j=N+1}^r C(n, i−f_j+1) + a^{(i−f_N)}, i = s+1, …, f_r+n; (c) there exists a unique
lexicographic submodule L of a finitely generated graded free E-module F = ⊕_{i=1}^r Egᵢ with the
basis elements gᵢ of degrees fᵢ and such that ∑_{i=s}^{f_r+n} hᵢtⁱ is the Hilbert series of F/L.
Proof. (a)⇒ (b). It follows from Proposition 4.1 and Discussion 3.2. … (b)⇒ (c). We construct
a lexicographic submodule L … (c)⇒ (a). It follows immediately."

The paper also has Definitions 2.1 (p. 37), 2.6 (p. 38) and 2.7 (p. 39), identical in wording to
entry 2's.

**Verdict:** the (a) ⇔ (c) equivalence is in the statement as claimed. But (a) ⇒ (c) is proved
here only through (b) (finding 3), and the remark's statement about (b) depends on how (b) is read
(finding 4). The manuscript never names this key alongside "Theorem 4.2" (finding 2). **Status:
statement verified; attribution needs a key; two remarks to tighten.**

### 4. Amata & Crupi (2021) — `AmataCrupi2021`

**Citation:** L. Amata, M. Crupi, *ExteriorModules: a package for computing monomial modules over
an exterior algebra*, J. Softw. Algebra Geom. **11** (2021), 71–81, DOI `10.2140/jsag.2021.11.71`.
Crossref confirms every field (issue 1, issued 2021-12-31). The year question was settled in
article 1's certificate, finding 5.

**Claims supported:** `.org:1693`, "the function `isHilbertSequence` of Amata and Crupi's Macaulay2
package … also rejects it"; `.org:2903–2906`, the package "enumerates lex submodules directly",
with counts 43, 69, 99, 236, 368.

**Quotation**, p. 80, function table: "isHilbertSequence(l,F) Check whether the Kruskal–Katona
theorem is satisfied for l"; "lexModule(hs,F) Give the lex module with the given Hilbert sequence
hs". p. 77, Example 3.3: "the lex submodule of F produced by both the functions lexModule(hs, F)
and lexModuleBySequences(hs, F) is the unique lex submodule L of F with H_{F/L} = hs."

**Verdict:** the function exists as named. **The counts and the rejection of (1,2) are the
project's own computations with the package. They are not printed in the paper and are not
citation claims.** The paper documents no function that enumerates lex submodules, so "enumerates
lex submodules directly" describes how the package was used, not a feature of it. That is fine,
but the wording could say "used to enumerate". **Status: verified.**

### 5. Aramova, Herzog & Hibi (1997) — `AramovaHerzogHibi1997`

**Citation:** A. Aramova, J. Herzog, T. Hibi, *Gotzmann theorems for exterior algebras and
combinatorics*, J. Algebra **191**(1) (1997), 174–211. **DOI as in `.bib`,
`10.1006/jabr.1996.6908`, is wrong; it should be `10.1006/jabr.1996.6903`** (finding 1).
`mrnumber` 1444495 was not re-checked.

**Claims supported:** `.org:1489`, `[cite/t:@AramovaHerzogHibi1997 Theorem 4.1]`: "surjective by
Kruskal–Katona in its exterior form …, every f-vector being attained by a compressed family, whose
complementary ideal is lex"; `.org:2931` (same, in the formalisation notes).

**Quotation** (re-extracted; same passage as article 1's entry 5), p. 195: "THEOREM 4.1. Let
(h₁, …, hₙ) be a sequence of integers. Then the following conditions are equivalent: (a) 1 +
∑_{i=1}^n hᵢtⁱ is the Hilbert series of a graded K-algebra E/I; (b) 0 ≤ h_{i+1} ≤ hᵢ^{(i)},
0 < i ≤ n−1." p. 196: "Proof of Theorem 4.1. (b) ⇒ (a). We construct a lexsegment ideal J such that
H_{E/J}(t) = 1 + ∑_{i=1}^n hᵢtⁱ."

**Verdict:** the theorem statement gives the characterisation. The part article 2 actually uses,
that every admissible sequence is attained by a *lex* ideal, is in the proof of (b) ⇒ (a) on
p. 196 rather than in the statement. Article 2's use is supported; "Theorem 4.1 and its proof"
would be exact. **Status: verified; bib DOI wrong.**

### 6. Kozlov (1997) — `Kozlov1997`

**Citation:** D. N. Kozlov, *Convex hulls of f- and β-vectors*, Discrete Comput. Geom. **18**(4)
(1997), 421–431, DOI `10.1007/PL00009326`. Crossref confirms every field.

**Claim supported:** `.org:516`, Kozlov "computes its convex hull".

**Quotation** (re-extracted; same as article 1's entry 1), p. 427: "Theorem 4.1. The convex hull of
the set of f-vectors of simplicial complexes on n vertices is given by conv{F̃₁, F̃₂, …, F̃ₙ}."
**Status: verified.**

### 7. Sköldberg (1999) — `Skoldberg1999`

**Citation:** E. Sköldberg, *Monomial Golod quotients of exterior algebras*, J. Algebra **218**(1)
(1999), 183–189, DOI `10.1006/jabr.1998.7826`. Crossref confirms every field.

**Claim supported:** `.org:508–509`, "(Ext)/I_Δ is the exterior face ring, also called Sköldberg's
indicator algebra". This differs from article 1, which relied on Proposition 1.

**Quotation**, p. 183: "If we denote the exterior algebra over k on the variables x₁, x₂, …, xₙ by
E, we may form the ideal J_Δ in E by letting it be generated by the set (1). The quotient E/J_Δ is
now denoted by k{Δ}, and is called the indicator algebra of Δ." **Says what is claimed. Status:
verified.**

### 8. Kupreyeva (2019) — `Kupreyeva2019`

**Citation:** A. Kupreyeva, *Simplices of f-vectors*, Bachelor's thesis LiTH-MAT-EX--2019/05--SE,
Linköpings universitet, 2019. The report number is confirmed on the title page of the held PDF.

**Claim supported:** `.org:3309–3311` (acknowledgements), the thesis "is where counting questions
about f-vectors entered this project". A historical claim. The thesis abstract supports its subject
matter: "We study the functions which count the number of lattice points in these convex hulls …
Chapter 6 is devoted to researching whether there is any relationship between the number of
f-vectors and the total number of lattice points". **Status: verified.**

### 9. Snellman (2026), article 1 — `SnellmanArticle1`

**Citation:** J. Snellman, *Hilbert functions over the exterior algebra and f-vectors in higher
rank, I: …*, LiTH-MAT-R 2026/04, Linköping University Electronic Press, 2026, DOI
`10.3384/LiTH-MAT-R-2026-04`, arXiv:2609.23605. Crossref confirms the DOI (report, issued
2026-09-18). The arXiv API returns the record, submitted 2026-09-20.

**Claims supported:** `.org:459`, `.org:542–543`, the companion paper "determines conv(FF(n; d))
… a Minkowski sum of r shifted copies" of the Kozlov simplex.

**Quotation** (arXiv abstract): "We determine the convex hull of the set of Hilbert functions of
the quotients F/M, where M runs over the monomial submodules of Amata and Crupi. The hull is the
Minkowski sum of r shifted copies of one and the same simplex: the Kozlov simplex". **Status:
verified.**

### 10. OEIS — `OEIS`, sequence A007695

**Citation:** OEIS Foundation Inc., *The On-Line Encyclopedia of Integer Sequences*,
<https://oeis.org>. The citation form follows OEIS's own request. Retrieved 2026-10-08 through
SageMath's `sage.databases.oeis` client.

**Claims supported:** `.org:968`, "The sequence F^p(p) is OEIS A007695"; `.org:3019–3023`, |Sₙ|
is "the first-difference sequence of A007695, which has no separate entry".

**Record as retrieved:** name "Cardinalities of Sperner families on 1,...,n."; comment "Also number
of f-vectors for simplicial complexes on at most n vertices."; offset 0; terms 2, 3, 5, 10, 26, 96,
553, 5461, 100709, 3718354, 289725509, 49513793526; references include "S. Linusson, The number of
M-sequences and f-vectors, Combinatorica, 19 (1999), 255-266."

**Verdict:** the terms match Linusson's F^p(p) for p = 0…8 (Table 6, last column). The next term,
3718354, equals 1 + F⁹(8) = 1 + 3718353 (Table 5 and recursion (11)). The manuscript's
|S₁₀| = 286007155 equals 289725509 − 3718354. An OEIS search for 1, 2, 5, 16, 70, 457, 4908,
95248 returned no match, which **confirms** "no separate entry" as of 2026-10-08. **Status:
verified.**

---

## B. No primary copy available

### 11. Horn & Johnson (2013) — `HornJohnson2013` — **NOT VERIFIED — source not available**

**Citation:** R. A. Horn, C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press.
Crossref: DOI `10.1017/CBO9781139020411`, edition 2, ISBNs 9780521839402 / 9780521548236 /
9781139020411, issued **2012-10-22** (`.bib` says 2013; see finding 6).

**Claim supported:** `.org:2491–2494`, the strict comparison theorem: "if 0 ≤ M ≤ M′ entrywise,
M ≠ M′ and M′ is irreducible, then the spectral radius of M is strictly smaller than that of M′
[HJ13, Ch. 8]".

**Verification:** none against the text. The book is in neither `literature/` nor `math-library`
(searched file names and `math-library.bib` for *Horn*, *Johnson*, *Matrix Analysis*, *Perron*);
being commercial, it was not fetched. **No theorem number was found.** The `.bib` note's "believed
Theorem 8.4.5" is recorded there as a belief and is not confirmed here. **Jan must supply the book,
or the theorem number from a copy**, before submission.

### 12. Stanley (1996) — `Stanley1996` — **NOT VERIFIED — source not available**

**Citation:** R. P. Stanley, *Combinatorics and Commutative Algebra*, 2nd ed., Progress in
Mathematics 41, Birkhäuser Boston, 1996. **DOI in `.bib` wrong; it should be `10.1007/b139094`**
(finding 1). Crossref's record for that DOI gives title, publisher, year and series; it lists no
author.

**Claim supported:** `.org:506`, "The construction is the one Stanley carries out in a polynomial
ring". This is a general attribution of the Stanley–Reisner construction, with no locator.

**Verification:** no copy in `literature/` or `math-library` (`math-library` has Stanley's
*Enumerative Combinatorics* and papers, not this book). The claim carries no locator and is the
standard attribution, so the risk is low. But no passage has been checked.

### 13–14. Kruskal (1963), Katona (1968) — `Kruskal1963`, `Katona1968`

**Citations:** as in article 1's certificate, entries 12–13. The fields match the current `.bib`,
including Katona's corrected pp. 187–207.

**Claim supported:** `.org:516`, "Kruskal–Katona … determines it exactly". A historical
attribution, the same use as in article 1.

**Verification:** reused from article 1's certificate: MathSciNet MR0154827 and MR0290982, Jan's
lookups of 2026-09-14. No copies held. **Status: bibliographically verified; no passage relied
on.**

---

## Works Jan must supply (in neither `literature/` nor `math-library`)

1. **Horn & Johnson, *Matrix Analysis*, 2nd ed.**: the theorem number for the strict comparison
   theorem (finding 6).
2. **Linusson 1999, the published Combinatorica version** (LiU subscription): to confirm that
   Theorem 5.2, Theorem 5.3, Proposition 5.4 and Tables 5–6 keep their preprint numbers, and that
   both tables are printed (finding 5).
3. **Stanley, *Combinatorics and Commutative Algebra*, 2nd ed.**: optional. Its claim has no
   locator.

---

*Prepared 2026-10-08 by Claude (Claude Code, on jts-office), read-only with respect to the
manuscript and its `.bib`: nothing there has been changed, and the corrections above are for Jan to
apply. Every quotation in section A was extracted from the named PDF during preparation of this
document. Nothing in this document was supplied from memory of the cited works.*

## Resolutions (2026-10-08, after this certificate was written)

- **Finding 1 (three wrong DOIs): fixed** in `literature/exterior-convex-references.bib`, each
  new DOI checked against Crossref: `10.24330/ieja.663094`, `10.1006/jabr.1996.6903`,
  `10.1007/b139094`. None of the three was printed in either article's PDF (DOIs are suppressed in
  the builds), so no published version is affected.
- **Finding 2 (Theorem 4.2 without a key): fixed**: `[cite:@AmataCrupi2020KK]` added at the
  proof of Theorem 23 and in §10.1.
- **Finding 6, "§2.2 asymptotics": fixed**: the sentence now says Linusson leaves the asymptotics
  in n as an open problem.
- **Findings 3 and 4**: proposed wording awaits Jan, in the working home's
  `20-projects/exterior-convex/working-notes/review-article2-step2-drafts-2026-10-08.org`.
- **Still to supply (Jan)**: Horn–Johnson 2nd ed. (theorem number), Linusson 1999 published
  version (numbering), and optionally Stanley 1996.

## Acquisition attempts (2026-10-09, Claude on jts-pc)

The three outstanding sources were chased from jts-pc, with the LiU VPN up (`ppp0`, peer
`130.236.0.1`). **None was obtained**, so entries 11 and 12 and finding 5 stand exactly as written
above. What follows records the routes tried, so they are not tried again blindly.

- **Linusson 1999, published Combinatorica version.** Unpaywall (`10.1007/s004930050055`) returns
  `oa_status: closed`, `has_repository_copy: false`, no OA locations at all — so the
  open-access-first rule is satisfied and the subscription route is the correct one. But
  `link.springer.com/content/pdf/10.1007/s004930050055.pdf` answers **HTTP 200 with a 3 KB
  "Client Challenge — JavaScript is disabled in your browser" page**, not the PDF. This is the
  bot-challenge-before-entitlement behaviour the workspace convention already records for
  ScienceDirect and SSRN; Springer now does it too, and the 200 status makes it easier to mistake
  for success. **A scripted fetch cannot get this paper. It needs a browser on the VPN**, and the
  file then belongs in `literature/subscription/` with its provenance stated.
- **Horn & Johnson, *Matrix Analysis*, 2nd ed.** Three routes, all closed:
  - *The NAS library* (`jts-nas.tailcc45b2.ts.net/library/textbooks/`): all **46** items were
    listed across the seven sections and searched for *horn*, *johnson*, *matrix*, *linear*,
    *perron* and *stanley*. The only hits are Schrijver's linear programming, Baccelli et al., and
    Stanley's *Enumerative Combinatorics* vols. 1–2. **Neither Horn–Johnson nor Stanley's
    *Combinatorics and Commutative Algebra* is in the library**, confirming section B's note by
    enumeration rather than by name search alone.
  - *Cambridge's own free front matter and index PDFs* for ISBN 978-0-521-83940-2 (which would at
    least give §8.4's exact title and page range): `assets.cambridge.org` **times out from this
    machine**, twice, at 90 s, and the same URL fetched through the agent's own web tool returned
    no content. Not retried further; note that even the index gives page numbers, not theorem
    numbers, so this route could never have settled 8.4.5 on its own.
  - *Secondary corroboration.* Several sources agree that chapter 8 of the 2nd edition is
    "Positive and Nonnegative Matrices" with a §8.4 "Irreducible nonnegative matrices", which is
    where a statement requiring `M′` irreducible would live. That is consistent with the `.bib`
    note's "believed Theorem 8.4.5" but **corroborates nothing**: no source consulted states what
    8.4.5 says. The citation therefore still reads "Ch. 8", and it was **not** tightened to "§8.4"
    on this evidence — the section title was not confirmed from Cambridge's own table of contents.
  - *The year, finding 6.* Left as `year = {2013}`, deliberately. Cambridge's own pages disagree
    with each other: the hardback with this ISBN is dated **22 October 2012** (Crossref and the
    Cambridge assets record) while the Higher Education listing gives **20 December 2012**, and
    2013 is the year the edition is normally cited by and is what the copyright page is understood
    to say. The copyright page is the only authority and it is inside the front matter PDF that
    could not be fetched. Changing a year on the strength of a bookseller date, against the
    edition's conventional year, is the failure mode this certificate exists to prevent, so
    nothing was changed; **this stays an open question for whoever opens the book.**

**Consequence for the responsibility paragraph.** "The reference list has been checked against
primary sources" is still not wholly true, for exactly the two reasons already stated — not for any
new one. Nothing in the manuscript's citations was altered on 2026-10-09 except `Stanley1996`'s
`edition` field, which is a rendering fix (`{2nd}` printed "2nd."; `{2}` prints "2nd ed.") and
touches no claim.

## Both sources supplied — findings 5 and 6 resolved (2026-10-09, later)

Jan obtained both from a browser on the LiU VPN and put them in
`20-projects/exterior-convex/literature/subscription/`. Both were read. **Both findings turned out
to be real defects, not formalities**, and the manuscript has been corrected.

### Finding 5 — resolved, and the answer was no

Finding 5 asked whether the published Combinatorica version keeps the preprint's numbering and
still prints both appendix tables. **It does neither.** The journal version is 13 pages against the
preprint's 26 and was substantially cut and reorganised. Every locator in article 2 was therefore
wrong for the version its `.bib` entry names. Verified against the PDF, statement by statement:

| article 2 cited | in the published version |
|---|---|
| §5 (`def-linusson`) | **§3**, "The number of f-vectors for simplicial complexes" |
| Theorem 5.2 (`thm-linusson`) | **Theorem 3.2**, equations (6) and (7) — transcription matches exactly |
| Theorem 5.3 (polynomiality in *p*) | **Theorem 3.3** |
| Proposition 5.4 (leading coefficient) | **Proposition 2.8**, carried to *E* and *F* by Theorem 3.3 |
| Tables 5 and 6 | **not present at all** |

The last row is the one that mattered. The published version **has no appendix** and prints exactly
one table, its own Table 1, of *M*ᵖ(*n*). The *f*-vector tables — Table 5 of *F*ᵖ(*n*) and Table 6 of
*E*ᵖ(*p*,*k*), the 100 + 99 entries article 2 checks itself against — exist only in the preprint.
Confirmed three ways: the string `3617645` (the value §4 says is "printed in Linusson's Table 5")
does not occur anywhere in the published text; §3 contains no numeric data at all; and the words
"appendix" and "Table" occur in the published version only in the caption of Table 1.

A verification claim is only as good as a reader's ability to repeat it, so §10.1's
"all 199 printed entries" would have sent a reader to a paper that does not contain them.
**Corrected:** every numbered result now cites the published version at its published number, and
the tables are cited to a separate `@unpublished` entry, `Linusson1999preprint`. The distinction is
stated once in `rem-transcription` and holds for the whole paper.

Also confirmed in §3's prose, so the manuscript's boundary values are sourced: *F*ᵖ(−1) = 1,
*F*ᵖ(0) = 2, *F*⁰(*n*) = 2, *E*ᵖ(*n*,−1) = 1, *E*ᵖ(*n*,*n*) = 1, *E*ᵖ(*n*,*k*) = 0 for *k* > *n*,
and *F*ᵖ(*n*) = ∑ₖ *E*ᵖ(*n*,*k*) as published equation (5). Bibliographic data all match: volume 19,
number 2, pages 255–266, 1999; received 28 February 1996, revised 26 February 1998.

### Finding 6 — resolved, and "believed Theorem 8.4.5" was right about the number and wrong about the theorem

**The year is settled and was nearly changed on worse evidence.** The copyright page reads
"First published 1985 / First paperback edition 1990 / **Second edition first published 2013**",
copyright "1985, 2013", with Library of Congress "QA188.H66 2012". Crossref's 2012-10-22 and
Cambridge's "20 December 2012" are release dates for the ISBN, not the edition's year.
`year = {2013}` stands, now on the primary source rather than on convention.

**The locator was wrong.** Theorem 8.4.5 exists, and it is *not* a strict-comparison theorem. It is
the equality case:

> **Theorem 8.4.5.** Let *A*, *B* ∈ *Mₙ*. Suppose that *A* is nonnegative and irreducible, and
> *A* ≥ |*B*|. Let λ = e^{iφ}ρ(*B*) be a given maximum-modulus eigenvalue of *B*. If
> ρ(*A*) = ρ(*B*), then there is a diagonal unitary matrix *D* ∈ *Mₙ* such that
> *B* = e^{iφ}*DAD*⁻¹.

Section 8.4, "Irreducible nonnegative matrices" (p. 533), contains **only** Lemmas 8.4.1–8.4.3,
Theorems 8.4.4–8.4.5 and Corollaries 8.4.6–8.4.7, and none of them is the strict comparison. In
this book the strict inequality appears **only as Problem 8.2.P15(b)**, and only for *B* positive.
So neither the old "Ch. 8" nor the believed "Theorem 8.4.5" would have supported the sentence as a
reader would check it.

**Corrected, and the statement is still true** — it just needs two results rather than one:

> **Corollary 8.1.19.** Let *A*, *B* ∈ *Mₙ* be nonnegative. If 0 ≤ *A* ≤ *B*, then
> ρ(*A*) ≤ ρ(*B*).

gives the weak inequality, and Theorem 8.4.5 excludes equality: for non-negative *M* and *M*′ it
forces each *M*[*i*][*j*] = |*M*′[*i*][*j*]|, hence *M* = *M*′. `prop-perron-threshold` now cites
both and says in one clause how the second delivers strictness, so a reader who looks up 8.4.5 is
not left wondering why an equality theorem was cited for a strict inequality.

**Status of entries 11 and 12.** Entry 11 (Horn & Johnson) is now **VERIFIED** against the book.
Entry 12 (Stanley, *Combinatorics and Commutative Algebra*) is **still not verified** — it was not
supplied, is not in the NAS library, and its claim carries no locator, so the risk stays low.

---

## Today's three new locators and one new reference (2026-10-10, Claude on jts-yoga)

The manuscript gained, on 2026-10-10, two Horn–Johnson locators in `prop-recurrence`'s proof and a
whole new reference carrying two locators in the new `lem-transfer-support` / `prop-growth-constant`
material. None of them was covered above, because all of them postdate the sections above. All four
are now verified **against the primary sources, read here, and quoted**.

### Entry 11 extended — `HornJohnson2013`, two further locators

Same copy as finding 6: `math-library/textbooks/linear-algebra/horn-johnson-2013-matrix-analysis-2ed.pdf`,
662 pdf pages. Printed page numbers below.

> **Theorem 5.7.10** (p. 372). "If *f* is a pre-norm on *Mₙ*, in particular, if it is a vector
> norm, then lim_{*k*→∞} [*f*(*Aᵏ*)]^{1/*k*} = ρ(*A*) for all *A* ∈ *Mₙ*."

Supports `prop-recurrence`'s step that ‖*Tₙ*(δ)^*k*‖^{1/*k*} → ρ(*Tₙ*(δ)) for ‖·‖ the entry sum.
**Exactly the right form**: the paper claims only that the entry sum is a norm, and 5.7.10 asks for
a *pre-norm*, so no submultiplicativity is needed. Gelfand's formula in this book (Corollary 5.6.14)
would have required a matrix norm; the manuscript's choice is the weaker hypothesis and is correct.

> **Theorem 8.3.1** (p. 529). "If *A* ∈ *Mₙ* is nonnegative, then ρ(*A*) is an eigenvalue of *A*
> and there is a nonnegative nonzero vector *x* such that *Ax* = ρ(*A*)*x*."

Supports the step that the spectral radius is itself an eigenvalue, the Perron root. The
manuscript quotes this one essentially verbatim and **needs no irreducibility**, which is the
point — `prop-recurrence` covers δ = 0, where *Tₙ*(0) is reducible. Verified that 8.3.1 as printed
carries no irreducibility hypothesis.

### Entry 15 — Flajolet & Sedgewick (2009) — `FlajoletSedgewick2009` — **VERIFIED**

**Citation:** P. Flajolet, R. Sedgewick, *Analytic Combinatorics*, Cambridge University Press,
2009, ISBN 978-0-521-89806-5, DOI `10.1017/CBO9780511801655`.

**Copy checked:** `math-library/textbooks/combinatorics/analyticcombinatoricsbook.pdf`, 822 pdf
pages. The book is **freely available from the authors**, so it is held legitimately and is not a
`subscription/` item.

**Claims supported and verdicts:**

- `prop-growth-constant`'s proof, `[cite:@FlajoletSedgewick2009 Theorem V.7]` — **verified**,
  printed p. 343, in §V.5 "Paths in graphs and automata", titled "Asymptotics of paths in graphs":

  > "Consider the matrix *F*(*z*) = (*I* − *zT*)⁻¹, where *T* is a scalar non-negative matrix, in
  > particular, the adjacency matrix of a graph equipped with positive weights. … If *T* is
  > irreducible and aperiodic, then ρ = λ₁⁻¹ is the unique dominant singularity of each
  > *F*^{*i*,*j*}(*z*), and \[*zⁿ*\]*F*^{*i*,*j*}(*z*) = ϕ_{*i*,*j*}λ₁ⁿ + *O*(ϱⁿ), 0 ≤ ϱ < λ₁, for
  > computable constants ϕ_{*i*,*j*} > 0."

  The manuscript's use is exactly this, with λ₁ identified as the Perron root and
  \[*zᵐ*\]*F*_{τ,τ′}(*z*) = (*Tₙ*(δ)^*m*)\[τ\]\[τ′\], which is immediate from the resolvent.
  Both hypotheses — irreducible **and** aperiodic — are the two the paper establishes from
  `lem-transfer-support`, and neither is dispensable in the source.
- The digraph paragraph after `lem-transfer-support`, `[cite:@FlajoletSedgewick2009 Note V.31]`,
  criterion (iii) — **verified**, printed p. 342, "Sufficient conditions for aperiodicity":

  > "(iii) *T* is irreducible and at least one diagonal element of *T* is non-zero."

  The paper's argument is a loop at *every* vertex, which is stronger, so the criterion applies.
  Criterion (i) ("*T* has strictly positive entries") would **not** serve: *Tₙ*(δ) has zero
  entries for δ ≤ *n*, by `lem-transfer-support` itself.
- Not relied on, but noted so a reader is not surprised: **Note V.34** (printed p. 345) is this
  book's statement of the named Perron–Frobenius theorem, derived there from Theorem V.7's proof.
  The manuscript does not cite it, and does not need to.

### One correction to the manuscript, found by this pass

`.org:774`, the §1.4 summary table, read "proved modulo Linusson's **Thm. 5.3**" — the *preprint's*
number, which finding 5 established is **Theorem 3.3** in the published version that `Linusson1999`
names. Every one of the other eight references to that result in the manuscript already said 3.3;
this single cell had been missed, and it sits in the paper's most-read table. **Corrected.**

### Status after this pass

Checked against the manuscript's actual citation list — seventeen keys, extracted from the `.org`
rather than recalled: `AmataCrupi2020`, `AmataCrupi2020KK`, `AmataCrupi2021`,
`AramovaHerzogHibi1997`, `FlajoletSedgewick2009`, `HornJohnson2013`, `Kozlov1997`, `Kruskal1963`,
`Kupreyeva2019`, `Linusson1999`, `Linusson1999preprint`, `Macaulay2`, `OEIS`, `SageMath`,
`Skoldberg1999`, `SnellmanArticle1`, `Stanley1996`.

Every one of them now has an entry, and every theorem-level locator in the manuscript has been
read in a primary source, with **one** exception: `Stanley1996` (entry 12), which was never
supplied and whose single claim carries no locator. `Kruskal1963` is bibliographically verified
with no passage relied on (entry 13–14); note that `Katona1968`, which entry 13–14 also covers, is
**no longer cited** by the manuscript — the entry is harmless but describes one key more than the
paper uses. The remaining decision is Jan's and is small.
