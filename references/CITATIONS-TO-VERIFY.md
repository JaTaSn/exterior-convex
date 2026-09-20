# Cited works with no local copy — to be checked against MathSciNet

> **Discharged 2026-09-20.** Jan's MathSciNet lookups (2026-09-14/16) and two registry checks
> (Crossref, 2026-09-20) settled every item below; the results — including the Katona pagination
> correction, the Schützenberger removal, the Meshalkin verification and the `AmataCrupi2021`
> dating — are recorded in **`REFERENCE-CERTIFICATE.md`** (the deliverable this file was the
> worklist for) and in the `.bib`'s per-entry annotations. Kept as the record of what needed
> checking and why; no longer a to-do list.

Generated 2026-09-14 from `articles/article-1/exterior-convex_article1_latest.org` and
`references/exterior-convex-references.bib`, by extracting every key inside a `[cite…:@…]` form and
matching it against the PDFs held in the working repository's `literature/` directory.

**Article 1 cites 20 keys. Eleven have a local copy; nine do not, and are listed below.** Those nine
are what the reference certificate cannot yet quote from a primary source, so they are the ones worth
confirming independently. Two of the nine are commercial textbooks that will never be held here, by
this project's own convention — they still want a MathSciNet check of the bibliographic data, but
their absence is deliberate rather than a gap.

Ordered with the ones that most need an outside eye first.

## 1. Katona (1968) — and a known page-range conflict

```bibtex
@article{Katona1968,
    author = {Katona, Gyula O. H.}, title = {A theorem of finite sets},
    journal = {Theory of Graphs}, pages = {209--214}, year = {1968},
    publisher = {Academic Press}}
```

**This is the one with a real discrepancy, already tracked in the project's `TODO.md`.** The `.bib`
says 209–214, Academic Press; the commonly quoted range is **187–207**, Akadémiai Kiadó. The Tihany
proceedings (*Theory of Graphs*, Proc. Colloq. Tihany 1966) were co-published by the two houses, which
is the likely source of the split. MathSciNet should settle which pagination goes with which imprint.
Cited in article 1 as one half of Kruskal–Katona (`thm-kk`).

## 2. Kruskal (1963) — the other half

```bibtex
@inproceedings{Kruskal1963,
    author = {Kruskal, Joseph B.}, title = {The number of simplices in a complex},
    booktitle = {Mathematical Optimization Techniques}, pages = {251--278},
    year = {1963}, publisher = {Univ. of California Press}}
```

Old conference-proceedings chapter; never attempted. No volume/editor recorded — the full citation is
usually given with editor R. Bellman and the series *Proc. Sympos. Math. Optimization Techniques,
Santa Monica 1960*, which is worth confirming, since the `booktitle` and year as recorded do not name
an editor at all.

## 3. Aramova & Herzog (2000) — the one ordinary journal article in the list

```bibtex
@article{AramovaHerzog2000,
    author = {Aramova, Annetta and Herzog, J{\"u}rgen},
    title = {Almost regular sequences and Betti numbers},
    journal = {American Journal of Mathematics}, volume = {122}, number = {4},
    pages = {689--719}, year = {2000}, publisher = {Johns Hopkins University Press},
    doi = {10.1353/ajm.2000.0025}}
```

`literature/README.org` records this as "not downloaded, not yet attempted (may be open via journal
access, not checked)". It is cited in `thm-invariance`, for invariance of Hilbert functions under
passing to an initial or generic-initial submodule. **This is the one of the nine most worth actually
obtaining**, rather than merely verifying, since it supports a theorem the paper uses rather than a
piece of historical attribution.

## 4–7. The four LYM papers

These four were added to the `.bib` when the local Lubell–Yamamoto–Meshalkin attribution was written,
and **none of them is catalogued in `literature/README.org` at all** — not even in its "Known but not
downloaded" section. That omission is itself worth fixing in the working repository.

```bibtex
@article{Yamamoto1954,
    author = {Yamamoto, K\^{o}ichi}, title = {Logarithmic order of free distributive lattice},
    journal = {Journal of the Mathematical Society of Japan}, volume = {6},
    pages = {343--353}, year = {1954}, doi = {10.2969/jmsj/00630343}}

@article{Meshalkin1963,
    author = {Meshalkin, L. D.},
    title = {Generalization of {S}perner's theorem on the number of subsets of a finite set},
    journal = {Theory of Probability and its Applications}, volume = {8},
    pages = {203--204}, year = {1963}}

@article{Lubell1966,
    author = {Lubell, David}, title = {A short proof of {S}perner's lemma},
    journal = {Journal of Combinatorial Theory}, volume = {1}, number = {2},
    pages = {299}, year = {1966}, doi = {10.1016/S0021-9800(66)80035-2}}

@techreport{Schutzenberger1959,
    author = {Sch\"{u}tzenberger, M. P.},
    title = {A characteristic property of certain polynomials of {E. F. M}oore and {C. E. S}hannon},
    institution = {Research Laboratory of Electronics, MIT},
    type = {RLE Quarterly Progress Report}, number = {55}, pages = {117--118}, year = {1959}}
```

Points to check, in decreasing order of doubt:

- **Meshalkin (1963)** has no DOI and a two-page range. The journal is the English translation of
  *Teor. Veroyatnost. i Primenen.*; volume and pagination of the translation and of the Russian
  original differ, and the `.bib` does not say which is meant.
- **Lubell (1966)** is recorded as a single page, 299, which is right for this famously one-page
  paper but worth confirming; also whether the journal name should be *Journal of Combinatorial
  Theory* (as recorded) or *J. Combin. Theory Ser. A*, which post-dates it.
- **Schützenberger (1959)** is an MIT RLE quarterly progress report, so MathSciNet may not index it
  at all. If it does not, that is worth knowing before the certificate claims it was checked there.
- **Yamamoto (1954)** appears sound; the DOI resolves in the recorded form.

The article attributes the *global* LYM inequality to these three independently, between 1954 and
1966, and Schützenberger separately — so the attribution claim, not just the pagination, is what the
certificate will need to support.

## 8–9. The two commercial textbooks — absent by policy, not by omission

```bibtex
@book{Eisenbud1995,
    author = {Eisenbud, David},
    title = {Commutative Algebra with a View Toward Algebraic Geometry},
    series = {Graduate Texts in Mathematics}, volume = {150}, year = {1995},
    publisher = {Springer-Verlag}, doi = {10.1007/978-1-4612-5350-1}, mrnumber = {1322960}}

@book{HerzogHibi2011,
    author = {Herzog, J{\"u}rgen and Hibi, Takayuki}, title = {Monomial Ideals},
    series = {Graduate Texts in Mathematics}, volume = {260}, year = {2011},
    publisher = {Springer}, doi = {10.1007/978-0-85729-106-6}}
```

Both are cited only in `thm-invariance`'s reference list, for standard background. Eisenbud already
carries an `mrnumber`; Herzog–Hibi does not, and could take one. Neither will be held locally.

# Two provenance issues found while compiling this list

Neither affects the list above, but both belong in the record.

1. **`AmataCrupi2021` is dated 2021 in the `.bib` and 2022 in the filename of the local PDF**
   (`Amata and Crupi - 2022 - ExteriorModules a package…`). The `ExteriorModules` package paper has
   appeared in more than one form; the `.bib` year should be checked against whichever version is
   actually cited.

2. **A copy of Ziegler, *Lectures on Polytopes* (Springer GTM 152) is present in the working
   repository's `literature/` directory.** That contradicts this project's stated convention —
   `literature/README.org` lists several commercial textbooks as "not downloaded (copyright)" — and
   it would be a copyright problem if `literature/` were ever included in a public repository. It is
   **not** copied into this repository, deliberately. Worth resolving at source: either remove it or
   record why it is an exception.
