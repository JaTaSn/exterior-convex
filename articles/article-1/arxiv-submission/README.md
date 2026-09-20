# arxiv-submission/ — the arXiv-ready package for article 1

**Regenerate with:** `python3 ../../../../ai-workspace/20-projects/exterior-convex/code/make_arxiv_submission.py`
(the generator lives in the working home; this whole directory is its output). It also writes
`../arxiv-submission.tar.gz`, which is what you upload.

## What is here, and why it is arXiv-safe

This is a **pdfLaTeX** submission with a **self-contained bibliography** — no XeLaTeX, no system
fonts, no biber. That is deliberate: the first submission attempt (2026-09-20) bounced because
arXiv read the document as XeLaTeX and could not find its fonts (FreeSerif and the Latin Modern
OpenType faces fontspec loads), and the biblatex/biber bibliography failed too. Both failure
modes are designed out here:

- **Fonts.** Compiled with pdfLaTeX + `lmodern` + `T1` fontenc. arXiv has these natively; nothing
  is uploaded. The `.tex`'s magic comment is `% Intended LaTeX compiler: pdflatex`, and there is
  no `fontspec`/`FreeSerif`/`FreeSans` anywhere in it. (Answer to "what did we use FreeSans for":
  nothing load-bearing — it was only ever the org template's default sans face under fontspec, and
  the body text is FreeSerif/Latin Modern serif. Dropping fontspec loses nothing visible.)
- **Bibliography.** Static `thebibliography`, generated once by classic BibTeX + `alpha.bst`
  (which reproduces the alphabetic `[Koz97]` labels) and inlined into the `.tex`. So the whole
  thing compiles with **`pdflatex` alone, three passes, no bibtex/biber run needed on arXiv**. The
  internal provenance `note` fields from the `.bib` are stripped before the bibliography is built,
  so they never appear in print. In-text citation order matches the original biblatex `sortcites`
  output.

Verified by the generator: **53 pages, 0 errors, 0 undefined citations/references**, compiled with
`pdflatex` only.

## Contents

| path | uploaded? | notes |
|---|---|---|
| `exterior-convex_article1_latest.tex` | yes | the article; pdflatex, inlined bibliography, image paths `img/…` |
| `img/` | yes | the nine figures the `.tex` includes |
| `anc/REFERENCE-CERTIFICATE.md` | yes (ancillary) | certificate of existence for every citation |
| `anc/lean/`, `anc/verification-code/` | yes (ancillary) | Lean formalization + verification code, junk-pruned |
| `make-tarball.sh` | no | builds the upload tarball (see below); excluded from it |
| `README.md` (this file) | no | repo documentation; excluded from the tarball |
| `exterior-convex_article1_latest.pdf` | **no** | local preview only; arXiv builds its own PDF |

`anc/` is arXiv's ancillary-files convention: attached to the submission and listed on the
abstract page, not compiled. The Lean and verification-code trees are included for reproducibility
(the Lean formalization is named in the abstract). To submit *without* them, delete those two
directories before running `make-tarball.sh` — the paper compiles identically without them, and
the full formalization is public at <https://gitlab.liu.se/jansn19/exterior-convex> either way.

## Making the upload

```sh
./make-tarball.sh      # writes ../arxiv-submission.tar.gz
```

Then upload `../arxiv-submission.tar.gz` to arXiv. `make-tarball.sh` needs only `tar` — it runs on
any machine with a clone (no LaTeX/emacs), and excludes this README, itself, and the local PDF.
arXiv auto-detects pdfLaTeX from the `.tex`'s magic comment and builds its own PDF.

## Git note

The whole folder is tracked except the built PDF and the tarball (both derived, both
`.gitignore`d). The `.tex`, `img/` and the `anc/` trees are committed, so a fresh clone on any
machine has a complete, ready-to-pack submission — which is the point of keeping it a folder rather
than a one-shot tarball. The generator (`code/make_arxiv_submission.py` in the working home)
regenerates the derived parts and preserves this README and `make-tarball.sh` across a rebuild; the
`anc/lean` + `anc/verification-code` trees are copies of the repo's own top-level `lean/` and
`verification-code/`, so re-run the generator after changing those.
