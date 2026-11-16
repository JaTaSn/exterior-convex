# STRUCTURE — how this repository is laid out and kept up to date

[`README.md`](README.md) is the page for visitors: what the articles are, where to get them, and
how to check the Lean and the verification code. This file is for whoever maintains the
repository, meaning the author and the AI agents that do the copying. It describes where each
file comes from, what is deliberately left out, and how a release reaches this repository.

Split off from the README on 2026-11-14, at the author's request, so that the README can address
an outside reader.

## Where the material comes from

The working home of the series is the subtree `20-projects/exterior-convex/` of the author's
private workspace repository (`ai-workspace`). It holds everything this repository does not: the
logbook, working notes, review rounds, correspondence, the literature, and work on later parts.

**This repository is a copy, not a move.** Material flows into it from the working home, never
out of it. A file edited here is overwritten at the next copy, so make changes in the working
home and copy them over. There are two exceptions:

- **The reference certificates** (`references/REFERENCE-CERTIFICATE*.md`) are written here and
  exist only here. The arXiv generators in the working home read them from this repository.
- **The submitted versions** of Parts I and II (`articles/article-1/`, `articles/article-2/`) are
  frozen as they went to arXiv. Do not overwrite either from the working home without diffing
  first. Part II shows why: the two `.org` files agree, but the working home's `_latest.tex` is a
  stale export (2026-10-10 11:55), and the one here is the later export of the same `.org`
  (15:59).

## Layout

### `articles/`

- **`article-1/`**: Part I (LiTH-MAT-R 2026:04, arXiv 2609.23605).
  - `exterior-convex_article1_latest.{org,tex,bbl,pdf}`: the final version. The `.org` is the
    source; the `.tex` is generated from it.
  - `arxiv-submission/`: the package submitted to arXiv, the output of
    `code/make_arxiv_submission.py` in the working home. It is pdfLaTeX with the bibliography
    inlined, because the first attempt with XeLaTeX and Biber bounced. `anc/` holds the
    certificate (copied fresh at each build), the Lean development and the verification code.
    Only the `.tex`, `img/`, `anc/REFERENCE-CERTIFICATE.md` and the README are tracked; the
    built PDFs and the tarball are regenerated on demand (`.gitignore`). Exception: the two
    Amata–Crupi packages in its `anc/verification-code/` were removed on 2026-11-16 (see "What is
    held back").
  - `arxivcopy.pdf`: the PDF arXiv generated from that package.
  - `ARXIV-SUBMISSION-METADATA.md`: the arXiv form fields and the pre-submission checklist.
- **`article-2/`**: Part II (arXiv 2610.14985; **not** in the LiTH-MAT-R series, see below).
  - `exterior-convex_article2_latest.{org,tex,pdf}`: the version prepared for arXiv.
  - `arxiv-submission/`: the package, from `code/make_arxiv_submission_article2.py`. Its `anc/`
    also holds CSV tables of the counts.
  - `ARXIV-SUBMISSION-METADATA.md`: as for Part I.
  - `lith-report/`: the LiTH-MAT-R version (2026-11-16), from
    `code/make_lith_report_article2.py` in the working home. It is the arXiv paper built by the
    same pipeline, except that section 10.2 names this repository first and adds that Part I's
    scripts and Lean are here too, and the title page says "Also available as arXiv:2610.14985".
    The series adds its own cover with the report number. `abstract.txt` is the abstract in
    plain text, with no TeX, for the report form and the covering email. The `.org` is a record
    of the derived source and does **not** export here: its `#+SETUPFILE:` paths are relative to
    the working home's `article/`, where the generator exports it. The same holds for
    `arxiv-submission/*.org`.
- **`article-3/`**: Part III, pre-release.
  - `exterior-convex_article3_latest.{org,tex,pdf}`, copied from the working home's `article/`.
  - `img/`: the ten figure PDFs, copied from the working home's `artefacts/ff-pictures/`.
  - On copying, two paths in both the `.org` and the `.tex` are rewritten:
    `../artefacts/ff-pictures/` becomes `img/`, and the bibliography path becomes
    `../../references/exterior-convex-references.bib`.
  - The `.tex` builds in place: `xelatex`, `biber`, `xelatex`, `xelatex`. The `.org` does
    **not** export here, because its `#+SETUPFILE:` lines point at shared templates in the
    workspace (`50-writing/article-templates/`), which are not copied.
- **`img/`**: figures used by Part I, which refers to them as `../img/`.

### `lean/`

A mirror of the working home's `LEAN/`, without the build directory. `lean/README.md` is copied
too, with its working-home paths rewritten (listed in the recipe below).

### `verification-code/`

A mirror of the working home's `code/`, with `runs/` mirrored into `verification-code/runs/`.
Two consequences:

- The scripts and the READMEs inside call the directory `code/` and refer to the working home's
  LOGBOOK sessions, which are not public. `README.md` warns visitors about the first.
- A few workflow tools came along with the mirror, such as `make_review_copy.py` and
  `build_notebooklm_package.py`. They verify nothing.

Scripts must find their neighbours by relative path, not by an absolute path on the author's
machine. Three that did not were fixed on 2026-11-14. In a `.sage` script use `sys.argv[0]`, not
`__file__`, which under `sage x.sage` points inside Sage.

### `references/`

- `exterior-convex-references.bib`: copied from the working home's
  `literature/exterior-convex-references.bib`.
- `REFERENCE-CERTIFICATE.md` (Part I, 2026-09-20), `REFERENCE-CERTIFICATE-article2.md` (Part II,
  2026-10-08 to 10), `REFERENCE-CERTIFICATE-article3.md` (Part III, 2026-11-14). Written here; see
  above.
- `CITATIONS-TO-VERIFY.md`: the worklist that Part I's certificate grew from (the works cited
  with no local copy, and what needed checking about each). It is discharged, and kept as the
  record of that check.

## What is held back, and why

- **Literature PDFs**: copyright. The certificates quote from them; the files stay private.
- **Build and packaging scripts**: `build_article.sh`, `make_arxiv_submission*.py`,
  `leanmarks_article3.py` and `CODE.pm`. They depend on the workspace's templates and layout and
  would not run here.
- **The fibres of the sum map**: `code/fibres/`, `code/oneoff/small_n_fibre_counts.py`,
  `code/oneoff/koz3_fibre_pictures.py` and `runs/fibres/`. This is work towards a later part,
  not yet written up.
- **Amata and Crupi's Macaulay2 packages** (`code/amata-crupi_Exterior{Ideals,Modules}.m2` in the
  working home): theirs, not ours, and they ship with every Macaulay2, where the scripts load them
  with `needsPackage`. Removed from this repository on 2026-11-16 at the author's request, from
  `verification-code/` and from Part I's `arxiv-submission/anc/verification-code/`. The latter
  means that folder no longer matches the package exactly: arXiv's ancillary files for
  2609.23605v1 still include the two packages. Both remain in this repository's git history.
- **Everything else in the working home**: the logbook, the working notes, the review rounds and
  the correspondence.

## The copy recipe

As used on 2026-11-14. Run each `rsync` with `--dry-run --itemize-changes` first and read the
`deleting` lines before running it for real.

```sh
W=~/Repositories/ai-workspace/20-projects/exterior-convex
X=~/Repositories/exterior-convex

# Lean: build it in the working home first, and copy only a clean build.
#   (export PATH="$HOME/.elan/bin:$PATH"; cd $W/LEAN && lake build)
rsync -a --delete --exclude '.lake/' --exclude '*.olean' $W/LEAN/ $X/lean/

# Verification code. The '/runs/' exclusion stops --delete from removing the runs.
rsync -a --delete --exclude '__pycache__/' --exclude '/runs/' \
  --exclude '/build_article.sh' --exclude '/make_arxiv_submission*.py' \
  --exclude '/leanmarks_article3.py' --exclude '/CODE.pm' --exclude '/amata-crupi_*.m2' \
  --exclude '/fibres/' --exclude '/oneoff/small_n_fibre_counts.py' \
  --exclude '/oneoff/koz3_fibre_pictures.py' \
  $W/code/ $X/verification-code/
rsync -a --delete --exclude '/fibres/' $W/runs/ $X/verification-code/runs/

# Bibliography.
cp $W/literature/exterior-convex-references.bib $X/references/
```

Then, by hand:

1. **`lean/README.md`**: rewrite `20-projects/exterior-convex/LEAN/` and `LEAN/` to `lean/`;
   the heading to `# lean/ — …`; the build instructions to `cd lean && lake …`; paths into the
   working home's `article/` to `articles/article-N/…`; `runs/lean-anchors/` to
   `verification-code/runs/lean-anchors/`. Afterwards `grep -n -e 20-projects -e 'LEAN/'
   lean/README.md` should print nothing.
2. **The article being released**: copy its `_latest.{org,tex,pdf}` and its figures, and rewrite
   the two paths as described under `article-3/` above. Check that the `.tex` builds in place.
3. **`README.md`**: update the article list, the Lean figures (file count, line count, the date of
   the last clean build) and the list of certificates.

## Releasing an article

- **The proof-reading labels (showkeys) are switched off in the `.org`**, by deleting its
  `#+SETUPFILE: …latex-draft-showkeys.setup` line. Then build with
  `code/build_article.sh <article> --ship`, which refuses to run while that line is present. The
  labels must never be removed only by a build script stripping them from the generated `.tex`
  (the author's instruction of 2026-11-14). The Lean discs in Part III's margin are content, with
  a legend in §1, and stay.
- The arXiv package is made by the generator in the working home's `code/`. It copies the
  article's certificate from this repository into the package's `anc/`.
- Afterwards, copy the submitted package into `articles/article-N/arxiv-submission/`, and record
  the arXiv id and any report number in `README.md`.

**The report series.** Part I went to the LiTH-MAT-R series first and to arXiv two days later.
Part II went to arXiv only. The report was meant to follow, but as of 2026-11-14 Part II is
**not** in the series, and `README.md` must not say it is. If it is added later, the report
cites the arXiv id, and arXiv's Report-no field can be filled in on a replacement.

## Licences

Added 2026-11-14 at the author's choice ("MIT or some CC, same as we used with our Zenodo
packages"). They follow `lattice-line-covers`, the repository deposited on Zenodo: **MIT** for code
(`LICENSE`, the same text with the same copyright line) and **CC BY 4.0** for the text
(`LICENSE-CC-BY-4.0`, the full legal code, copied from `arithmetical-functions-truncations`). That
also matches Part II's arXiv licence, CC BY 4.0. `README.md`'s *Licence* section says which
directories fall under which. New code goes under MIT, and new prose under CC BY, without further
decision.

## Publishing

This repository is **public** (`gitlab.liu.se/jansn19/exterior-convex`). A commit stays local; a
push publishes. Push only on the author's go-ahead. The first push after the 2026-11-14 sync was
approved by the author that evening.
