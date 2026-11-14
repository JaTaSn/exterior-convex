# split_article3_draft4.py -- 2026-11-07, Claude-Code (jts-mini), at Jan's request.
# Made article/exterior-convex_article3_draft_5.org (the lattice side of Part III) and
# article/exterior-convex_article1_vertices-facets_draft_1.org (the vertices and facets, for Part I)
# from article/exterior-convex_article3_draft_4.org. Kept as the record of exactly what moved; it
# will not apply to any later draft. Run from article/:
#   python3 ../code/oneoff/split_article3_draft4.py exterior-convex_article3_draft_4.org \
#     exterior-convex_article3_draft_5.org exterior-convex_article1_vertices-facets_draft_1.org
# Analysis behind the cut: LOGBOOK/LOGBOOK-session-56-20261107-jts-mini.md.
# The same evening the block was renamed article/exterior-convex_article4_draft_1.org (Part IV, a
# separate paper, Jan's plan) and both outputs were edited, so neither is reproduced by this
# script any more: it records the split, not the current files.

"""Split article 3 draft 4 into draft 5 (lattice side) and a vertices/facets block for Part I.
Every replacement is asserted to match exactly once; every chunk is located by its heading."""
import sys, re
src, out5, outB = sys.argv[1:4]
L = open(src, encoding='utf-8').read().split('\n')

def idx(h):
    hits = [i for i, l in enumerate(L) if l == h]
    assert len(hits) == 1, (h, hits)
    return hits[0]
def chunk(a, b): return '\n'.join(L[idx(a):idx(b)]) + '\n'
def rep(s, old, new, label):
    assert s.count(old) == 1, (label, s.count(old))
    return s.replace(old, new)

H_INTRO = '* Introduction'
H_11 = '** Where Parts I and II leave things'
H_12 = '** What this paper does'
H_13 = '** What is proved, and what is only observed'
H_14 = '** What changes in Part I'
H_SETUP = '* Setup'
H_21 = '** Notation'
H_22 = '** Hilbert functions and ff-vectors'
H_23 = '** Right-angle simplices and the two coordinate systems'
H_24 = '** Log-concave leg vectors'
H_25 = '** The extremal tensor and the vertex criterion'
H_V = '* The vertices at every rank'
H_LAT = '* Lattice points: the canonical chained decomposition'
H_METH = '* Methods and verification'
H_LEAN = '** Formal verification'
H_OPEN = '* Open problems'
H_APPA = '* Proofs for the \\(\\Theta\\)-form'
H_APPB = '* Proof of the two-component inequalities'
H_ACK = '* Acknowledgements'
H_DISC = '* Disclosure of AI assistance'
H_FUND = '* Funding'

pre = '\n'.join(L[:idx(H_INTRO)]) + '\n'

# ---------------------------------------------------------------- shared pieces
STATUS_VF = [
 "Thm.~\\ref{thm-pairwise}, the consecutive pairwise reduction, weakly log-concave \\(\\vec a\\) & proved; verified\\\\\n",
 "Thm.~\\ref{thm-vdesc}, Cor.~\\ref{cor-kozlov-vertices}, explicit vertex description, every rank & proved; verified\\\\\n",
 "Cor.~\\ref{cor-rank2-lc}, the rank-two extremal matrix, weakly log-concave \\(\\vec a\\) & proved; verified \\(n\\le8\\)\\\\\n",
 "Thm.~\\ref{thm-hrep2}, Part I's Conjecture 55, and Cor.~\\ref{cor-ones-hrep}, its Conjecture 52 & proved; verified\\\\\n",
 "Thm.~\\ref{thm-theta}, the \\(\\Theta\\)-form at rank \\(r\\) & proved; verified\\\\\n",
 "Cor.~\\ref{cor-facets-every-d}, \\(ns\\) facets for every \\(\\vec d\\) & proved; verified\\\\\n",
]
intro = chunk(H_INTRO, H_14)
i12 = intro.index(H_12); i13 = intro.index(H_13)
bul_v = intro.index('- *Vertices at every rank*'); bul_f = intro.index('- *Facets at every rank*')
bul_l = intro.index('- *Lattice points* (Section')
VF_BULLETS = intro[bul_v:bul_l]

meth = chunk(H_METH, H_OPEN)
mv = meth.index('- *Vertices.*'); ml = meth.index('- *Lattice points, volume, Ehrhart.*')
METH_VF = meth[mv:ml]

opn = chunk(H_OPEN, H_APPA)
o1 = opn.index('1. *Log-convex leg vectors.*'); o4 = opn.index('4. *Ehrhart theory at rank')
OPEN_VF = opn[o1:o4]
OPEN_INTRO = ("The rank-two facet conjectures of Part I and the rank-\\(r\\) vertex description are settled above, and\n"
              "are removed from the list.\n\n")

disc = chunk(H_DISC, H_FUND)
dv = disc.index('- *Section [[#sec-vertices]].*'); dl = disc.index('- *Sections [[#sec-lattice]], [[#sec-volume]], [[#sec-ehrhart]].*')
DISC_VF = disc[dv:dl]

LEGEND_PARTIAL_OLD = ("- \\leanpartial{} part of the statement proved as for \\leanfull{}: for the \\(H\\)-descriptions, the\n"
                      "  equality of sets without the tightness, facet and irredundancy clauses; elsewhere a special case\n"
                      "  or the combinatorial core;\n")
STRONGER = ("Formalised statements are sometimes stronger than the printed ones: Corollary [[cor-rank2-lc]]\n"
            "needs neither \\(n\\ge2\\) nor \\(d\\le n-1\\), and the equality of sets in\n"
            "Corollary [[cor-facets-every-d]] holds for weakly log-concave \\(\\vec a\\), \\(n\\ge1\\) and unsorted\n"
            "shifts. ")

SENT_SECTIONS = ("Sections [[#sec-vertices]] and [[#sec-facets]] work\n"
                 "in \\(\\RA\\), Sections [[#sec-lattice]] onward in \\(\\Koz\\).")

# =============================================================== DRAFT 5
d5_head = """# ===================================================================================================
# DRAFT 5 OF PART III -- 2026-11-07, jts-mini (Claude-Code), at Jan's request: THE SPLIT.
#
# Made from draft 4 by a script (every replacement asserted unique); draft 4 is unchanged beside it.
# REMOVED, now in exterior-convex_article1_vertices-facets_draft_1.org (to be merged into Part I):
#   sec. 1.4 "What changes in Part I" (rem-partI-changes); sec. 2.4 (def-logconcave, lem-ratio);
#   sec. 2.5 (lem-criterion); sec. 3 "The vertices at every rank"; sec. 4 "The facets at every
#   rank"; Appendix A "Proofs for the Theta-form" (old Appendix B is now Appendix A); the vertex and
#   facet parts of the abstract, sec. 1.1-1.3, the notation table, sec. 11, 11.1, 12 and the AI
#   disclosure.  Subtitle was "III: Vertices, facets and lattice points of the Kozlov polytope".
# KEPT: all of sec. 2.3 except two sentences that pointed at secs. 3-4: prop-rank-one-H, the LYM
#   coordinates, fl/tp and ex-koz3-koz4 are used in secs. 5, 7 and 8 (dependency analysis:
#   ../LOGBOOK/LOGBOOK-session-56-20261107-jts-mini.md, entry 20:09).
# PLACEHOLDERS: \\PartIref{label} prints "[Part I: label]" where this paper now needs a result that
#   has moved to Part I and has no number yet.  grep for PartIref: four uses, of three labels.
# NOTE FOR JAN: the abstract and sec. 1.1 now say that Part I describes the vertices and facets,
#   which is true only once the block is merged into a revised Part I.  The subtitle is a proposal.
# The three header blocks below are draft 4's, kept verbatim.  Where they mention secs. 3-4,
# Appendix A or the vertex/facet labels, that material has moved as above.
# ===================================================================================================

"""
d5_pre = rep(pre, "#+STARTUP: showall inlineimages num hidedrawers\n",
             "#+STARTUP: showall inlineimages num hidedrawers\n\n" + d5_head, 'd5 head')
d5_pre = rep(d5_pre, "#+subtitle: III: Vertices, facets and lattice points of the Kozlov polytope",
             "#+subtitle: III: Lattice points of the Kozlov polytope", 'd5 subtitle')
d5_pre = rep(d5_pre,
 "#+LATEX_HEADER: \\newcommand{\\fl}{\\operatorname{fl}}\n",
 "#+LATEX_HEADER: \\newcommand{\\fl}{\\operatorname{fl}}\n"
 "# 2026-11-07 (split): a visible placeholder for a result that moved to Part I and has no number there yet.\n"
 "#+LATEX_HEADER: \\newcommand{\\PartIref}[1]{\\textsf{[Part~I:~#1]}}\n", 'd5 PartIref macro')
d5_pre = rep(d5_pre,
 "and described its vertices at\nrank two, conjecturing its facets there; Part II counted the Hilbert functions. Here we describe the polytope\n"
 "completely at every rank and study its lattice points.\n\n"
 "On the vertex side we prove that, for every weakly log-concave leg vector, the extremal tensor of\n"
 "the Minkowski sum is the conjunction of its consecutive rank-two restrictions, and we list the\n"
 "vertices of \\(\\Koz(n;\\vec d)\\) explicitly: the last non-zero coordinates of the summands' vertices climb weakly, and may\n"
 "climb by exactly one only across a window boundary. On the facet side we prove the rank-two \\(H\\)-description\n"
 "conjectured in Part I and a weighted generalisation at every rank; for \\(n\\ge2\\),\n"
 "\\(\\Koz(n;\\vec d)\\) has exactly \\(ns\\) facets, \\(s\\) the number of distinct generator degrees. On the lattice side we show that\n",
 "and described its vertices and\nfacets; Part II counted the Hilbert functions. Here we study its lattice points.\n\n"
 "We show that\n", 'd5 abstract')
d5_pre = rep(d5_pre, "polytope; Minkowski sum; vertex description; facet description; log-concavity; lecture hall\n",
             "polytope; Minkowski sum; log-concavity; lecture hall\n", 'd5 keywords')

d5_intro = intro
d5_intro = rep(d5_intro,
 "and determined its vertices and, conjecturally, its facets\nat rank two [cite:@SnellmanArticle1 Section 9].",
 "and determined its vertices and its facets at every rank\n(\\PartIref{thm-vdesc}, \\PartIref{thm-theta}).", 'd5 1.1 Part I')
q1 = d5_intro.index('Three questions were left open'); q3 = d5_intro.index('3. *The lattice points.*')
d5_intro = d5_intro[:q1] + ("The question left open, and the subject of this paper, is that of the lattice points.\n"
                            + d5_intro[q3 + len('3. *The lattice points.* '):])
d5_intro = rep(d5_intro, "A hull is coarse. Already for \\(n=4\\) the simplex \\(\\Koz(4)\\) contains\n"
               "   twenty lattice points of which only sixteen are \\(f\\)-vectors, and the proportion falls quickly\n"
               "   with \\(n\\). Which lattice points are Hilbert functions, and how are they distributed?",
               "A hull is coarse. Already for \\(n=4\\) the simplex \\(\\Koz(4)\\) contains twenty lattice points of\n"
               "which only sixteen are \\(f\\)-vectors, and the proportion falls quickly with \\(n\\). Which lattice\n"
               "points are Hilbert functions, and how are they distributed?", 'd5 q3 reflow')
d5_intro = rep(d5_intro, VF_BULLETS, '', 'd5 1.2 bullets')
for row in STATUS_VF:
    d5_intro = rep(d5_intro, row, '', 'd5 status ' + row[:30])

d5_setup = chunk(H_SETUP, H_24)
d5_setup = rep(d5_setup,
 "\\(\\vec a\\), \\(\\sigma_i\\) & leg vector; its slopes \\(a_{i+1}/a_i\\) & Def.~\\ref{def-logconcave}\\\\\n",
 "\\(\\vec a\\) & leg vector & Def.~\\ref{def-ra}\\\\\n", 'd5 nt a')
d5_setup = rep(d5_setup,
 "\\(W_p\\), \\(j_p\\), \\(m_p\\) & window, chosen vertex, chosen point \\(d_p+j_p\\) & \\S\\ref{sec-setup}\\\\\n"
 "\\(\\extten\\), \\(\\extten^{(p,q)}\\) & extremal tensor; rank-two restriction & \\S\\ref{sec-setup}\\\\\n",
 "\\(W_p\\) & window & Def.~\\ref{def-ra}\\\\\n", 'd5 nt W, M')
d5_setup = rep(d5_setup,
 "\\(\\Theta(p;c)\\), \\(M(p;c)\\) & reduced chain; roof after \\(p\\) & Thm.~\\ref{thm-theta}\\\\\n", '', 'd5 nt Theta')
d5_setup = rep(d5_setup,
 "(for instance \\(a\\), \\(b\\), \\(c\\) in\nAppendix [[#sec-app-PQ]], or \\(\\lambda\\) for weights in Section [[#sec-facets]] and for barycentric\n"
 "coordinates elsewhere)",
 "(for instance \\(a\\), \\(b\\), \\(c\\) in\nAppendix [[#sec-app-PQ]])", 'd5 letters')
d5_setup = rep(d5_setup, "with the leg vector allowed to be real, which costs\nnothing and is convenient for weights.",
               "with the leg vector allowed to be real, which costs\nnothing.", 'd5 weights')
d5_setup = rep(d5_setup, SENT_SECTIONS,
               "The vertex and facet descriptions of Part I are stated\nin \\(\\RA\\); from Section [[#sec-lattice]] on we work in \\(\\Koz\\).", 'd5 sections sentence')

d5_mid = chunk(H_LAT, H_METH)
d5_mid = rep(d5_mid, "the six facets of Example [[ex-hrep2-n4]], and", "six facets (\\PartIref{ex-hrep2-n4}), and", 'd5 ex1')
d5_mid = rep(d5_mid, "\\(8\\) facets (Example [[ex-hrep2-n4]])", "\\(8\\) facets (\\PartIref{ex-hrep2-n4})", 'd5 ex2')

d5_meth = meth
d5_meth = rep(d5_meth,
 "Each of the five groups of results (vertices, facets,\nlattice points and volume, centroids, module Kruskal--Katona) was in addition re-derived line by line\n"
 "by an independent adversarial review (Remark [[rem-permutohedron]] excepted: its source has not been reviewed, and only its agreement\n"
 "with the reviewed \\(\\Theta\\)-form at \\(\\vec a=\\onesvec(n)\\) was checked), and checked",
 "Each of the three groups of results (lattice points and\nvolume, centroids, module Kruskal--Katona) was in addition re-derived line by line\n"
 "by an independent adversarial review, and checked", 'd5 meth intro')
d5_meth = rep(d5_meth, METH_VF, '', 'd5 meth bullets')
d5_meth = rep(d5_meth, LEGEND_PARTIAL_OLD,
 "- \\leanpartial{} part of the statement proved as for \\leanfull{}: a special case or the\n  combinatorial core;\n", 'd5 legend')
d5_meth = rep(d5_meth, STRONGER, '', 'd5 stronger')

d5_open = opn
d5_open = rep(d5_open, OPEN_INTRO, '', 'd5 open intro')
d5_open = rep(d5_open, OPEN_VF, '', 'd5 open items')
for old, new in [('4. *Ehrhart', '1. *Ehrhart'), ('5. *Fill rates', '2. *Fill rates'), ('6. *A Kupreyeva', '3. *A Kupreyeva'),
                 ('7. *Centroids', '4. *Centroids'), ('8. *Beyond proper', '5. *Beyond proper'),
                 ('9. *The \\(\\mathbb Z^r\\)', '6. *The \\(\\mathbb Z^r\\)'), ('10. *Sköldberg', '7. *Sköldberg')]:
    d5_open = rep(d5_open, old, new, 'd5 renumber ' + old)
d5_open = d5_open.replace("\n    exterior face ring", "\n   exterior face ring").replace("\n    submodules of", "\n   submodules of").replace("\n    Snellman [cite", "\n   Snellman [cite")

d5_back = '\n'.join(L[idx(H_APPB):])
d5_back = rep(d5_back, DISC_VF, '', 'd5 disc bullets')

open(out5, 'w', encoding='utf-8').write(d5_pre + d5_intro + d5_setup + d5_mid + d5_meth + d5_open + d5_back)

# =============================================================== BLOCK
b_head = """# ===================================================================================================
# VERTICES AND FACETS AT EVERY RANK -- the block cut out of Part III, to be merged into Part I.
# 2026-11-07, jts-mini (Claude-Code), at Jan's request.  Made by a script from
# exterior-convex_article3_draft_4.org (unchanged beside it); the lattice side is draft 5.
#
# WHAT IS HERE, verbatim unless listed below: sec. 1.4 "What changes in Part I" (rem-partI-changes);
#   sec. 2.3 without fl/tp and without ex-koz3-koz4 and its figure (those stay in Part III);
#   secs. 2.4, 2.5, 3, 4; the vertex and facet parts of sec. 1.1-1.3, the notation table, sec. 11,
#   11.1 and 12; Appendix A; the two vertex/facet items of the AI disclosure.
# EDITED, not verbatim: the abstract (its vertex and facet sentences, with a new first paragraph);
#   sec. 1.1 (the newcomer's example dropped: its figure and lattice-point claims are Part III's);
#   the sentence in sec. 2.3 that pointed at Part III's sections; the methods intro ("two groups");
#   the Lean legend (no conditional mark occurs here); the acknowledgements.
# IT IS A STAGING FILE.  It builds on its own so that the cut can be checked (no undefined
#   reference means nothing here leans on Part III), but much of secs. 1-2 duplicates Part I
#   (Def. 36, Sec. 8, Lemma 13, Cor. 16), and "Part I" is cited from inside what will be Part I.
#   On merging: rem-partI-changes becomes edits to Part I itself (Conjectures 52 and 55 become
#   these theorems; the withdrawn paragraph of Part I's sec. 9.4 is deleted; Example 53's x_1 = 1).
# Status of every result, sources and reviews: see draft 4's header record.  Lean marks:
#   python3 ../code/leanmarks_article3.py <this file>.
# NOTE FOR JAN: the acknowledgements' list of software was copied from Part III and may name more
#   than the vertex and facet computations used.
# ===================================================================================================

"""
pre_lines = pre.split('\n')
# drop draft 4's own header blocks (lines from the first '# =====' after #+STARTUP to the last one)
st = pre_lines.index('#+STARTUP: showall inlineimages num hidedrawers')
seps = [i for i, l in enumerate(pre_lines) if l.startswith('# =====')]
a, b = seps[0], seps[-1]
assert a > st
b_pre = '\n'.join(pre_lines[:a]) + '\n' + b_head + '\n'.join(pre_lines[b + 1:]).lstrip('\n')
b_pre = rep(b_pre, "#+subtitle: III: Vertices, facets and lattice points of the Kozlov polytope",
            "#+subtitle: Vertices and facets of the Kozlov polytope at every rank (block for Part I)", 'b subtitle')
ab0 = b_pre.index('#+begin_abstract'); ab1 = b_pre.index('#+end_abstract')
abstract = b_pre[ab0:ab1]
v0 = abstract.index('On the vertex side'); v1 = abstract.index(' On the lattice side')
b_abs = ("#+begin_abstract\n"
 "Let \\(E\\) be the exterior algebra on \\(n\\) generators and \\(F=\\bigoplus_{i=1}^rEg_i\\) a graded free\n"
 "\\(E\\)-module with \\(\\deg g_i=d_i\\). The convex hull of the Hilbert functions of the quotients\n"
 "\\(F/M\\), \\(M\\) a proper monomial submodule, is the Kozlov polytope \\(\\Koz(n;\\vec d)\\), a Minkowski\n"
 "sum of shifted Kozlov simplices. We describe it completely at every rank.\n\n"
 + abstract[v0:v1] + "\n")
b_pre = b_pre[:ab0] + b_abs + b_pre[ab1:]
b_pre = rep(b_pre, "polytope; Minkowski sum; vertex description; facet description; log-concavity; lecture hall\n"
            "polytope; Ehrhart polynomial; Kruskal--Katona theorem; lex submodule.",
            "polytope; Minkowski sum; vertex description; facet description; log-concavity.", 'b keywords')

b_intro = chunk(H_INTRO, H_12)
e0 = b_intro.index('For example, for \\(n=3\\)'); e1 = b_intro.index('Three questions were left open')
b_intro = b_intro[:e0] + b_intro[e1:]
q3 = b_intro.index('3. *The lattice points.*')
b_intro = b_intro[:q3].rstrip('\n') + '\n\n'
b_intro = rep(b_intro, "Three questions were left open, and they are the subject of this paper.",
              "Two questions were left open, and they are the subject of this paper.", 'b two questions')
b_intro += intro[i12:bul_v] + VF_BULLETS.rstrip('\n') + '\n\n'
t13 = intro[i13:]
tab0 = t13.index('\\midrule\n') + len('\\midrule\n'); tab1 = t13.index('\\bottomrule')
b_intro += t13[:tab0] + ''.join(STATUS_VF) + t13[tab1:]
b_intro += chunk(H_14, H_SETUP)

b_setup = chunk(H_SETUP, H_23)
nt0 = b_setup.index('\\midrule\n') + len('\\midrule\n'); nt1 = b_setup.index('\\bottomrule')
rows = b_setup[nt0:nt1].split('\n')
keep = [r for r in rows if r and not any(k in r for k in
        ('\\(\\vec c\\)', '\\(\\fl\\)', '\\NV', 'fill', 'B(h,j)'))]
keep = [r.replace('\\(S_n\\), \\(\\mathcal L_n\\) & \\(f\\)-vectors of proper complexes on \\([n]\\); lattice points of \\(\\Koz(n)\\)',
                  '\\(S_n\\) & \\(f\\)-vectors of proper complexes on \\([n]\\)') for r in keep]
b_setup = b_setup[:nt0] + '\n'.join(keep) + '\n' + b_setup[nt1:]
b_setup = rep(b_setup,
 "(for instance \\(a\\), \\(b\\), \\(c\\) in\nAppendix [[#sec-app-PQ]], or \\(\\lambda\\) for weights in Section [[#sec-facets]] and for barycentric\n"
 "coordinates elsewhere)",
 "(for instance \\(\\lambda\\) for\nweights in Section [[#sec-facets]] and for barycentric coordinates elsewhere)", 'b letters')
tp0 = b_setup.index('Two statistics from Part II will be used')
b_setup = b_setup[:tp0].rstrip('\n') + '\n\n'
s23 = chunk(H_23, H_24)
s23 = rep(s23, SENT_SECTIONS, "Sections [[#sec-vertices]] and [[#sec-facets]] work\nin \\(\\RA\\).", 'b sections sentence')
f0 = s23.index('is an order simplex.') + len('is an order simplex.')
s23 = s23[:f0] + '\n\n'
b_setup += s23 + chunk(H_24, H_V)

b_vf = chunk(H_V, H_LAT)

b_meth = meth[:mv]
b_meth = rep(b_meth,
 "Each of the five groups of results (vertices, facets,\nlattice points and volume, centroids, module Kruskal--Katona) was in addition",
 "Each of the two groups of results (vertices, facets) was\nin addition", 'b meth intro')
lean0 = meth.index(H_LEAN)
b_meth += METH_VF + meth[meth.index('#+LATEX: \\endgroup'):]
b_meth = rep(b_meth,
 "- \\leancond{} proved in the same way, assuming the surjectivity half of Part II's chaining\n"
 "  reformulation [cite:@SnellmanArticle2 Theorems 23 and 41, with Lemma 40], which enters as an\n"
 "  explicit hypothesis of the formal statement, not as an axiom;\n", '', 'b legend cond')
b_meth = rep(b_meth, LEGEND_PARTIAL_OLD,
 "- \\leanpartial{} part of the statement proved as for \\leanfull{}: for the \\(H\\)-descriptions, the\n"
 "  equality of sets without the tightness, facet and irredundancy clauses;\n", 'b legend partial')
b_meth = rep(b_meth, "says what a partial mark covers, and records where a\nformal definition differs in form from the printed one (the normalised volume, the uniform measure\non a dilate).",
             "says what a partial mark covers.", 'b readme sentence')

b_open = opn[:o1]
b_open += OPEN_VF.rstrip('\n') + '\n\n'
b_open += opn[opn.index('#+begin_export latex\n\\appendix'):]

b_appA = chunk(H_APPA, H_APPB)

b_back = chunk(H_ACK, H_DISC)
k0 = b_back.index('This paper owes its lattice-point question'); k1 = b_back.index('Claude (Anthropic) assisted substantially')
b_back = b_back[:k0] + b_back[k1:]
b_disc = disc[:dv] + DISC_VF + disc[disc.index('- *Figures, code, formalisation.*'):]
b_disc = rep(b_disc, ", and the reference list has\nbeen checked against primary sources, except for the paper of Savage and Schuster, whose theorem is\ncited in the form quoted by two other sources.",
             ", and the reference list has\nbeen checked against primary sources.", 'b disc savage')
b_back += b_disc + '\n'.join(L[idx(H_FUND):])

open(outB, 'w', encoding='utf-8').write(b_pre + b_intro + b_setup + b_vf + b_meth + b_open + b_appA + b_back)
print('ok')
