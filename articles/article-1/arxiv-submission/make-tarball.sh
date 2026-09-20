#!/usr/bin/env sh
# Produce the arXiv upload tarball from this folder.
#
# Runnable ANYWHERE with just `tar` -- no LaTeX/emacs/bibtex needed. Use this on a machine that
# only has a clone of the repository (e.g. jts-yoga), where the full generator
# (code/make_arxiv_submission.py in the working home) cannot run.
#
# Excludes what must not go to arXiv: this script, the folder README (repo documentation), and the
# compiled article PDF at the root (arXiv builds its own from the .tex). Figure PDFs under img/ are
# KEPT -- the exclude names the root article PDF exactly rather than a `*.pdf` glob, which would
# also drop img/prop21-fibres-n4.pdf and make arXiv report it "missing from the source".
set -eu
cd "$(dirname "$0")"
out=../arxiv-submission.tar.gz
tar czf "$out" \
    --exclude=./make-tarball.sh \
    --exclude=./README.md \
    --exclude=./exterior-convex_article1_latest.pdf \
    .
echo "wrote $out"
echo "top of archive:"
tar tzf "$out" | grep -vE '^anc/(lean|verification-code)/' | sort
