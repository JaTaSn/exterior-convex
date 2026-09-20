#!/usr/bin/env bash
# make_arxiv_package.sh -- assemble the arXiv submission tarball for article 1.
#
# Changelog (newest first):
#
# 2026-09-20  Created (Jan: "ensure that REFERENCE-CERTIFICATE is in the anc package").
#             Produces arxiv-submission.tar.gz containing:
#               exterior-convex_article1_latest.tex   (image paths rewritten ../img/ -> img/)
#               exterior-convex_article1_latest.bbl   (arXiv has no biber; the .bbl IS the bibliography)
#               img/ (the nine figures the .tex includes)
#               anc/REFERENCE-CERTIFICATE.md          (copied FRESH from ../../references/ at
#                                                      pack time -- no stale duplicate is kept
#                                                      in this directory)
#             anc/ is arXiv's ancillary-files convention: everything under it is attached to
#             the submission and listed on the abstract page, but not compiled.
#             The tarball is assembled in a temp dir and left beside this script; it is NOT
#             committed (gitignored would be ideal; it is fully derived).
set -euo pipefail
cd "$(dirname "$0")"

F=exterior-convex_article1_latest
OUT=arxiv-submission.tar.gz
CERT=../../references/REFERENCE-CERTIFICATE.md

[ -f "$F.tex" ] || { echo "missing $F.tex" >&2; exit 1; }
[ -f "$F.bbl" ] || { echo "missing $F.bbl -- build the article first (biber pass)" >&2; exit 1; }
[ -f "$CERT" ]  || { echo "missing $CERT" >&2; exit 1; }

T=$(mktemp -d)
trap 'rm -rf "$T"' EXIT

sed 's|\.\./img/|img/|g' "$F.tex" > "$T/$F.tex"
cp "$F.bbl" "$T/"
mkdir -p "$T/img" "$T/anc"
# copy exactly the images the .tex references, so a figure added later cannot be silently missed
grep -o 'includegraphics\[[^]]*\]{[^}]*}' "$F.tex" | sed 's/.*{//;s/}//' | sort -u | while read -r p; do
  cp "../img/$(basename "$p")" "$T/img/"
done
cp "$CERT" "$T/anc/"

tar -C "$T" -czf "$OUT" .
echo "wrote $OUT:"
tar -tzf "$OUT" | sed 's/^/  /'
