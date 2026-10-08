# arxiv-submission/ — the arXiv-ready package for article 2

**Regenerate with** `python3 20-projects/exterior-convex/code/make_arxiv_submission_article2.py`
in the working home (`ai-workspace`). This directory is its output, except this README and
`make-tarball.sh`, which it preserves across a rebuild. Form fields (title, abstract, MSC,
comments) are in `../ARXIV-SUBMISSION-METADATA.md`.

Same design as article 1's package (see `../../article-1/arxiv-submission/README.md` for why):
**pdfLaTeX** with `lmodern`, and a **static bibliography** generated once by classic BibTeX +
`alpha.bst` and inlined, so arXiv needs neither XeLaTeX, nor fonts, nor biber.

## What differs from the working draft

`exterior-convex_article2_arxiv.org` is derived from the current draft by the generator, never
edited by hand. Exactly two changes:

1. The `showkeys` setupfile line is dropped: no label names in the margin.
2. A subsection *Code, formalisation and tables* is inserted before *Open problems*, pointing
   the reader at `anc/`.

The `.org` is kept here for inspection and is excluded from the upload.

## Contents

| path | uploaded? | notes |
|---|---|---|
| `exterior-convex_article2_arxiv.tex` | yes | the article; pdfLaTeX, inlined bibliography |
| `img/` | yes | the one external figure (`perron-vs-delta-n5.pdf`); the digraph is TikZ |
| `anc/README.md` | yes (ancillary) | what the three trees below are and how to run them |
| `anc/lean/`, `anc/verification-code/` | yes (ancillary) | copies of the repository's own top-level trees, junk pruned |
| `anc/tables/` | yes (ancillary) | CSV tables of the counts, from `verification-code/oneoff/arxiv_anc_tables.py` |
| `exterior-convex_article2_arxiv.org` | no | derived source, for inspection |
| `exterior-convex_article2_arxiv.pdf` | no | local preview; arXiv builds its own |
| `README.md`, `make-tarball.sh` | no | repository documentation and the packer |

## Making the upload

```sh
./make-tarball.sh      # writes ../arxiv-submission.tar.gz; needs only tar
```
