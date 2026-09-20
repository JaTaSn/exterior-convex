#!/usr/bin/env sh
# Produce the arXiv upload tarball from this folder.
#
# Runnable ANYWHERE with just `tar` -- no LaTeX/emacs/bibtex needed. Use this on a machine that
# only has a clone of the repository (e.g. jts-yoga), where the full generator
# (code/make_arxiv_submission.py in the working home) cannot run.
#
# Excludes what must not go to arXiv: this script, the folder README (repo documentation), and any
# local PDF (arXiv builds its own from the .tex). Everything else -- the .tex, img/, and the whole
# anc/ tree -- is included.
set -eu
cd "$(dirname "$0")"
out=../arxiv-submission.tar.gz
tar czf "$out" \
    --exclude=make-tarball.sh \
    --exclude=README.md \
    --exclude='*.pdf' \
    .
echo "wrote $out"
echo "top of archive:"
tar tzf "$out" | grep -vE '^anc/(lean|verification-code)/' | sort
