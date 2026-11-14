# 2026-11-09 - Claude-Code (jts-mini), at Jan's request (round-2 report, item 14: "move this whole section
#   out of the article and to a new one ... article5 ... 'Module Kruskal-Katona'. In this new article,
#   delegate to an appendix ... thm-kk-rank1's discussion, lem-lex-rank1, prop-PQ (with its proof),
#   rem-blocks, prop-greedy, lem-monomial and lem-lexF-shadow").
# Copies sec-module-kk and Appendix sec-app-PQ of exterior-convex_article3_latest.org, verbatim, into a
# skeleton of article/exterior-convex_article5_draft_1.org. Article 3 itself is NOT edited here.
# Line ranges are those of article3_latest at commit fc2546a3; each range's first and last line is asserted.
# Run once: python3 code/oneoff/split_article5_from_article3.py
import os
SRC = 'article/exterior-convex_article3_latest.org'
DST = 'article/exterior-convex_article5_draft_1.org'
L = open(SRC).read().split('\n')

def take(a, b, first, last):
    """lines a..b (1-indexed, inclusive); assert the first and last start as given"""
    seg = L[a - 1:b]
    assert seg[0].startswith(first), (a, seg[0][:60])
    assert seg[-1].startswith(last), (b, seg[-1][:60])
    return '\n'.join(seg)

latex_header = take(209, 269, '#+LATEX_HEADER: \\usepackage{iftex}', '#+LATEX_HEADER: \\author{')
notation_T = take(448, 458, 'Throughout, \\(n\\) and the generator', 'Section [[#sec-module-kk]], where')
lex_and_B = take(871, 939, '** The lex order on', '\\(\\binom n0=1\\) each through')
sec_intro = take(863, 869, 'Corollary [[cor-membership]] decides', 'allowed, as Amata and Crupi allow')
omega_def = take(943, 945, 'For \\(k\\ge0\\) and \\(0\\le t', 'as defined above.')
kk_rank1 = take(947, 954, '#+NAME: thm-kk-rank1', '#+end_theorem')
kk_discussion = take(956, 959, 'The classical statement', 'colex-initial, so the two')
lex_rank1 = take(961, 989, '#+NAME: lem-lex-rank1', 'in the formal verification')
pq = take(991, 1003, '#+NAME: prop-PQ', 'recursion of Lemma [[lem-lex-rank1]](2), in fifteen')
blocks = take(1005, 1014, '#+NAME: rem-blocks', '#+end_remark')
greedy = take(1016, 1032, '#+NAME: prop-greedy', '#+end_proof')
monomial = take(1036, 1053, '#+NAME: lem-monomial', '#+end_proof')
lexF_shadow = take(1055, 1074, '#+NAME: lem-lexF-shadow', 'uses, without stating it')
module_thm = take(1076, 1200, '#+NAME: thm-module-kk', '#+end_mexample')
methods_kk = take(2872, 2878, '- *Module Kruskal--Katona.*', '  negatives. Scripts:')
lean_legend = take(2882, 2905, '** Formal verification', 'on a dilate).')
open_56 = take(2935, 2942, '5. *Beyond proper monomial', '   convex hull, a canonical section')
app_pq = take(3028, 3127, '* Proof of the two-component inequalities', 'formalised (Section [[#sec-methods]]).')
back = take(3389, 3487, '* Acknowledgements', '#+print_bibliography')

TODO = '# TODO(agent): '
out = f""":PROPERTIES:
:ID:       623b2b49-2edf-415a-ac89-2110d8a6d4bd
:CREATED:  [2026-11-09 Mon]
:END:

#+SETUPFILE: ../../../50-writing/article-templates/latex-common.setup
#+SETUPFILE: ../../../50-writing/article-templates/latex-variant-koma.setup
#+SETUPFILE: ../../../50-writing/article-templates/latex-draft-showkeys.setup
#+OPTIONS: toc:nil H:3 num:t tags:nil email:nil author:nil
# author:nil -- the author block (name, \\orcidlink, affiliation in \\thanks) is the \\author LATEX_HEADER
# below; org's own \\author would override it and cannot carry the affiliation.
#+STARTUP: showall inlineimages num hidedrawers

# ===================================================================================================
# PART V, DRAFT 1 -- 2026-11-09, jts-mini (Claude-Code), at Jan's request (round-2 report on Part III,
# article3-review-round2-report-2026-11-09.org, item 14).
#
# MADE BY code/oneoff/split_article5_from_article3.py, which copied, verbatim, Part III's section
# sec-module-kk and its Appendix sec-app-PQ (exterior-convex_article3_latest.org at commit fc2546a3).
# Jan's layout: thm-kk-rank1's discussion, lem-lex-rank1, prop-PQ (with its proof), rem-blocks,
# prop-greedy, lem-monomial and lem-lexF-shadow go to an appendix. The introduction must say plainly
# that Theorem thm-ac42 is Amata and Crupi's, and that this paper gives a new proof, along the same
# lines, part of which is formally verified.
# Part III no longer contains this material; it cites this paper as [cite:@SnellmanArticle5].
# NOTE FOR JAN: the series placement (Part V) and the subtitle are proposals.
# ===================================================================================================

{latex_header}

#+bibliography: ../literature/exterior-convex-references.bib
#+cite_export: biblatex alphabetic

#+title: Hilbert functions over the exterior algebra and \\(f\\)-vectors in higher rank
#+subtitle: V: Module Kruskal--Katona
#+author: Jan Snellman
#+date: \\today

#+begin_abstract
{TODO}abstract.
#+end_abstract

#+begin_export latex
\\medskip\\noindent\\textbf{{Keywords.}} exterior algebra; Hilbert function; Kruskal--Katona theorem;
lex submodule; Macaulay representation; formal verification.

\\smallskip\\noindent\\textbf{{2020 Mathematics Subject Classification.}} Primary 13D40, 05D05;
Secondary 13F55, 15A75.
\\medskip
#+end_export

#+TOC: headlines 2

* Introduction
:PROPERTIES:
:CUSTOM_ID: sec-intro
:END:

{TODO}the introduction. The section intro of Part III's sec-module-kk, verbatim, follows as material.

{sec_intro}

* Setup
:PROPERTIES:
:CUSTOM_ID: sec-setup
:END:

** Notation

{TODO}E, F, d_i (arbitrary integers here), k any field, Hilbert function H_{{F/M}}; a notation table.

{notation_T}

{lex_and_B}

* The module Kruskal--Katona theorem
:PROPERTIES:
:CUSTOM_ID: sec-module-kk
:END:

** Rank one

{omega_def}

{kk_rank1}

{TODO}pointer: the discussion of this statement, Lemma lem-lex-rank1, the two-component inequalities and
# the greedy step, and the two shadow lemmas are in Appendix sec-app-greedy.

** The module theorem

{module_thm}

* Methods and verification
:PROPERTIES:
:CUSTOM_ID: sec-methods
:END:

{TODO}opening paragraph (Part III's said: every theorem has a written proof, re-derived by an independent
# adversarial review, and checked by exact computation with code written for the review).

{methods_kk}

{lean_legend}

* Open problems
:PROPERTIES:
:CUSTOM_ID: sec-open
:END:

{TODO}these were open problems 5 and 6 of Part III; renumber and adapt.

{open_56}

#+begin_export latex
\\appendix
#+end_export

* The greedy step and the shadow lemmas
:PROPERTIES:
:CUSTOM_ID: sec-app-greedy
:END:

** Rank one

{kk_discussion}

{lex_rank1}

** The two-component inequalities and the greedy split

{pq}

{blocks}

{greedy}

** Reduction to monomials, and the shadow of a segment

{monomial}

{lexF_shadow}

{app_pq}

{back}
"""
assert not os.path.exists(DST), DST
open(DST, 'w').write(out)
print('wrote', DST, len(out.split('\n')), 'lines')
