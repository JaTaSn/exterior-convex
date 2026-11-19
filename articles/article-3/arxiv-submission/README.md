# arxiv-submission/ — the arXiv package for Part III

**Regenerate with** `python3 20-projects/exterior-convex/code/make_arxiv_submission_article3.py`
in the working home (`ai-workspace`). This directory is its output, except this README,
`make-tarball.sh` and `ARXIV-METADATA.txt`, which it keeps across a rebuild. The form fields
(title, abstract, MSC, comments) are in `ARXIV-METADATA.txt`.

Same design as the packages of Parts I and II: **pdfLaTeX** with `lmodern`, and a **static
bibliography** made once by classic BibTeX with `alpha.bst` and inlined, so arXiv needs neither
XeLaTeX nor biber.

## What differs from `../exterior-convex_article3_latest.*`

`exterior-convex_article3_arxiv.org` is derived from the current source by the generator and is
never edited by hand. The differences:

1. The date is a literal date, not `\today` (arXiv recompiles the source).
2. One preamble line that only matters when the proof-reading labels are on is dropped.
3. In the `.tex`: the bibliography is inlined, `biblatex` and `fontspec` are gone, figure paths
   point at `img/`, and comment-only lines are removed, since arXiv publishes the source.

The text is the same. The Lean marks in the margin are part of the paper and are kept.

**There is no `anc/` directory**, unlike Parts I and II. The Lean files, the scripts, the run logs
and the reference certificate are in this repository and in its Zenodo archive
(DOI 10.5281/zenodo.24288404), and the paper cites both.

## Contents

| path | uploaded? | notes |
|---|---|---|
| `exterior-convex_article3_arxiv.tex` | yes | the article |
| `img/` | yes | ten figure PDFs; the lattice-path figure is TikZ |
| `exterior-convex_article3_arxiv.org` | no | derived source, for inspection |
| `exterior-convex_article3_arxiv.pdf` | no | local preview, not tracked; arXiv builds its own |
| `ARXIV-METADATA.txt` | no | the form fields |
| `README.md`, `make-tarball.sh` | no | this file and the packer |

## Making the upload

```sh
./make-tarball.sh      # writes ../arxiv-submission.tar.gz; needs only tar
```
