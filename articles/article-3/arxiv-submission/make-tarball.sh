#!/usr/bin/env sh
# Produce the arXiv upload tarball from this folder. Needs only `tar`.
#
# Uploaded: the .tex (pdfLaTeX, bibliography inlined) and img/ (the ten figure PDFs).
# Not uploaded: this script, README.md, ARXIV-METADATA.txt, the derived .org, and the preview PDF
# at the root (arXiv builds its own). The exclude names the root PDF exactly; a `*.pdf` glob would
# also drop the figures.
set -eu
cd "$(dirname "$0")"
out=../arxiv-submission.tar.gz
tar czf "$out" \
    --exclude=./make-tarball.sh \
    --exclude=./README.md \
    --exclude=./ARXIV-METADATA.txt \
    --exclude=./exterior-convex_article3_arxiv.org \
    --exclude=./exterior-convex_article3_arxiv.pdf \
    .
echo "wrote $out"
echo "contents:"
tar tzf "$out" | sort
