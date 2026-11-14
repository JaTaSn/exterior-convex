# Changelog (reverse chronological):
# 2026-10-30 - Claude-Code-de276a21 (jts-pc): created and APPLIED ONCE to
#   article/exterior-convex_article3_draft_4.org, on Jan's answers to the notation audit
#   (working-notes/notation-audit-article3-2026-10-29.org: B1-B4, B7-B9, C). Kept as the record of
#   what was changed; running it again fails its first assertion.
import re, sys
p = sys.argv[1]
s = open(p).read()
def rep(a, b, count=1):
    global s
    n = s.count(a)
    assert n == count, (a[:80], n, count)
    s = s.replace(a, b)
def block(start, end):
    i = s.index(start); j = s.index(end, i)
    return i, j
def sub_in(start, end, pat, repl, expect=None):
    """regex substitution confined to s[start-anchor : end-anchor]"""
    global s
    i, j = block(start, end)
    new, n = re.subn(pat, repl, s[i:j])
    if expect is not None:
        assert n == expect, (pat, n, expect)
    s = s[:i] + new + s[j:]
    return n
# ---- B1: chosen-point count K in 3.2; define s_b
rep(r"Let \(\hat m_1<\dots<\hat m_s\) be the distinct chosen points and, for \(k<s\),",
    r"Let \(\hat m_1<\dots<\hat m_K\) be the distinct chosen points and, for \(k<K\),")
rep(r"\(G_1,\dots,G_{s-1}\), and the *tail* \(T=[\hat m_s+1,N]\).",
    r"\(G_1,\dots,G_{K-1}\), and the *tail* \(T=[\hat m_K+1,N]\).")
rep("so counts add; each run has \\(ns_b\\) facets by\nTheorem [[thm-theta]], and \\(\\sum_bns_b=ns\\).",
    "so counts add; the \\(b\\)-th run, with \\(s_b\\) distinct shifts, has \\(ns_b\\) facets by\nTheorem [[thm-theta]], and \\(\\sum_bns_b=ns\\).")
# ---- B2: e as an integer
sub_in("#+NAME: lem-value-table", "** Rank two", r"\\shift\^e", r"\\shift^d", 3)
sub_in("#+NAME: lem-value-table", "** Rank two", r"\\ell=c-e", r"\\ell=c-d", 1)
sub_in("#+NAME: lem-value-table", "** Rank two", r"c\+1=e\+1", r"c+1=d+1", 1)
rep(r"coordinate \(e=d_{p-1}+n+1\)", r"coordinate \(c^*=d_{p-1}+n+1\)")
rep(r"\(M(p-1;e)\)", r"\(M(p-1;c^*)\)")
rep("at \\(e=d_p+1\\). If \\(e>n\\), \\(w_e=x_e\\). If \\(e\\le n\\),\n  \\(w_e=\\min(x_e,M(1;e))\\)",
    "at \\(c^*=d_p+1\\). If \\(c^*>n\\), \\(w_{c^*}=x_{c^*}\\). If \\(c^*\\le n\\),\n  \\(w_{c^*}=\\min(x_{c^*},M(1;c^*))\\)")
rep(r"because \(M(1;e)\) contains", r"because \(M(1;c^*)\) contains")
i, j = block(r"/\((\mathrm D;p)\), \(u=e_{e_0}\)", "Only \\(e_{e_0}\\) is missing.")
j += len("Only \\(e_{e_0}\\) is missing.")
seg = s[i:j].replace("e_{e_0}", "e_{c^*}").replace("e_0", "c^*")
s = s[:i] + seg + s[j:]
# ---- B3: gadget labels (R^g), (L^g); the scalar Lambda keeps its name
n1 = sub_in("#+NAME: def-gadget", "** Consequences", r"\(\\mathrm E\)", r"(R^{\\mathrm g})")
n2 = sub_in("#+NAME: def-gadget", "** Consequences", r"\(\\Lambda\)", r"(L^{\\mathrm g})")
assert (n1, n2) == (8, 7), (n1, n2)
# ---- B4: offsets gamma_j; copies; C_{>=a}; Psi; the mass; c(.)
n = sub_in("#+NAME: thm-hrep2", "** Rank \\(r\\)", r"(?<![A-Za-z\\])c_j", r"\\gamma_j")
assert n == 7, n
sub_in("#+NAME: thm-hrep2", "** Rank \\(r\\)", r"(?<![A-Za-z\\])c_d=", r"\\gamma_d=", 1)
for a, b in [("c_1=4/6", "\\gamma_1=4/6"), ("c_2=6/4-4/6", "\\gamma_2=6/4-4/6"), ("c_3=4/1-6/4", "\\gamma_3=4/1-6/4")]:
    rep(a, b)
rep("Weights are what makes tied shifts manageable: \\(q\\) copies of a convex set sum to \\(q\\) times\nit.",
    "Weights are what makes tied shifts manageable: a sum of copies of a convex set is the\ncorresponding multiple of it.")
rep(r"Merging is exact, since a sum of \(q\) copies of a convex set is \(q\) times it.",
    r"Merging is exact, since a sum of copies of a convex set is the corresponding multiple of it.")
rep(r"\(W_a=\sum_{l\ge a}c_{k-d_l}\)", r"\(C_{\ge a}=\sum_{l\ge a}c_{k-d_l}\)")
rep(r"x_k-W_{a+1}", r"x_k-C_{\ge a+1}")
rep("  F=\\sum_{i=1}^r i\\,\\bigl\\lVert\\vec p_i\\bigr\\rVert_1,", "  \\Psi=\\sum_{i=1}^r i\\,\\bigl\\lVert\\vec p_i\\bigr\\rVert_1,")
rep("""The exchange moves the mass
\\(\\varepsilon M\\), \\(M=\\sum_{j=j_0}^{T}c_j>0\\), from summand \\(i\\) to summand \\(i+1\\):
\\(\\lVert\\vec p_i\\rVert_1\\) falls by \\(\\varepsilon M\\) and \\(\\lVert\\vec p_{i+1}\\rVert_1\\) rises by
\\(\\sum_m\\eta_mc_m=\\varepsilon M\\). So \\(F\\) rises by \\(\\varepsilon M\\), contradicting maximality.""",
"""The exchange moves the mass
\\(\\varepsilon\\sum_{j=j_0}^{T}c_j>0\\) from summand \\(i\\) to summand \\(i+1\\):
\\(\\lVert\\vec p_i\\rVert_1\\) falls by this amount and \\(\\lVert\\vec p_{i+1}\\rVert_1\\) rises by
\\(\\sum_m\\eta_mc_m\\), the same amount. So \\(\\Psi\\) rises by it, contradicting maximality.""")
rep(r"At rank \(r\) we use \(\nu_k=x_k/\dim F_k\), with \(\dim F_k=\sum_i\binom n{k-d_i}\).",
    "At rank \\(r\\) we use \\(\\nu_k=x_k/\\dim F_k\\), with \\(\\dim F_k=\\sum_i\\binom n{k-d_i}\\). We write \\(c(X)\\)\n"
    "for the centroid of the uniform measure on \\(X\\): the counting measure if \\(X\\) is finite,\n"
    "Lebesgue measure on its affine hull if \\(X\\) is a polytope.")
rep(r"centroid of \(S_n\) is \((1-\varepsilon_n)c^\circ+\varepsilon_nc^{\mathrm{top}}\).",
    r"centroid of \(S_n\) is \((1-\varepsilon_n)\,c(S_n^\circ)+\varepsilon_n\,c(S_n^{\mathrm{top}})\).")
rep(r"\(\operatorname{centroid}(S_5)=", r"\(c(S_5)=")
rep(r"\(t\,c(\Koz(n))+c_1+O(1/t)\)", r"\(t\,c(\Koz(n))+b+O(1/t)\)")
# ---- B7: lex segments Lex_n(k,t); the linear part of beta
n = sub_in("* Which lattice points are Hilbert functions", "* Discrete volume versus volume",
           r"(?<![A-Za-z\\])L_(n|\{n-1\})(\(|\\bigl\()", r"\\mathrm{Lex}_\1\2")
assert n == 9, n
rep(r"L\Sigma L^{\mathsf T}", r"\bar\beta\Sigma\bar\beta^{\mathsf T}", 3)
rep(r"\(L\) the matrix of the linear part of \(\beta\)", r"\(\bar\beta\) the matrix of the linear part of \(\beta\)")
# ---- B8: the difference map
n = sub_in("#+NAME: rem-permutohedron", "#+end_remark", r"\\partial(?![a-zA-Z])", r"\\operatorname{diff}")
assert n >= 2, n
# ---- B9: Part I's tilde F_j
rep("\\(\\tilde F_j=(c_0,\\dots,c_j,0,\\dots,0)\\), and",
    "\\(\\tilde F_j=(c_0,\\dots,c_j,0,\\dots,0)\\) (Part I's \\(\\tilde F_j\\) is its image under \\(\\pi\\)), and")
# ---- C
n = len(re.findall(r"\\phi\(", s)); assert n == 6, n
s = s.replace(r"\phi(", r"\operatorname{fill}(")
rep(r"\(\Phi=\lbrace\mu_{n-1}=0\rbrace=\conv(\tilde F_1,\dots,\tilde F_{n-2})\)",
    r"\(\Koz(n)^\circ=\Koz(n)\cap\lbrace\mu_{n-1}=0\rbrace=\conv(\tilde F_1,\dots,\tilde F_{n-2})\)")
rep(r"On the face \(\Phi\)", r"On the face \(\Koz(n)^\circ\)")
rep(r"in the codimension-two face \(\Phi\)", r"in the codimension-two face \(\Koz(n)^\circ\)")
i = s.index(r"\varepsilon_i=\tp(\vec p_i)+d_i"); j = s.index("and the barycentric", i)
seg = s[i-200:j+30]; assert seg.count(r"\varepsilon_i") == 6, seg.count(r"\varepsilon_i")
s = s[:i-200] + seg.replace(r"\varepsilon_i", r"\tau_i") + s[j+30:]
i = s.index(r"\(M(t)=\sum_{k=0}^{n-1}"); j = s.index(r"\vec u^{\mathcal L}M_0\vec1=", i) + 40
seg = s[i:j]; seg = re.sub(r"M\(t\)", "U(t)", seg); seg = re.sub(r"M_([01])", r"U_\1", seg)
s = s[:i] + seg + s[j:]
for a, b in [(r"B_l=\sum_{i\le l}z_i", r"Z_{\le l}=\sum_{i\le l}z_i"), (r"S_l=\sum_{i\ge l}z_i", r"Z_{\ge l}=\sum_{i\ge l}z_i"),
             (r"(1) With \(B_0=0\),", r"(1) With \(Z_{\le0}=0\),"), (r"\rho_i(B_i-B_{i-1})=\rho_lB_l+\sum_{i<l}(\rho_i-\rho_{i+1})B_i", r"\rho_i(Z_{\le i}-Z_{\le i-1})=\rho_lZ_{\le l}+\sum_{i<l}(\rho_i-\rho_{i+1})Z_{\le i}"),
             (r"(2) With \(S_{L+1}=0\),", r"(2) With \(Z_{\ge L+1}=0\),"), (r"\rho_i(S_i-S_{i+1})=\rho_lS_l+\sum_{i>l}(\rho_i-\rho_{i-1})S_i", r"\rho_i(Z_{\ge i}-Z_{\ge i+1})=\rho_lZ_{\ge l}+\sum_{i>l}(\rho_i-\rho_{i-1})Z_{\ge i}")]:
    rep(a, b)
rep(r"\lbrace1\ge y_2\ge\dots\ge y_n\ge0\rbrace", r"\lbrace1\ge\mu_2\ge\dots\ge\mu_n\ge0\rbrace")
rep(r"\(r=2\), \(d=(0,0)\), so", r"\(r=2\), \(\vec d=(0,0)\), so")
rep(r"At \(n=3\), \(c=(3,1)\):", r"At \(n=3\), \((c_2,c_3)=(3,1)\):")
rep(r"At \(n=4\), \(c=(6,4,1)\),", r"At \(n=4\), \((c_2,c_3,c_4)=(6,4,1)\),")
for t in ["(2,5,5)", "(2,3,6)", "(1,2,3)"]:
    rep(r"\(m=" + t + r"\)", r"\(\vec m=" + t + r"\)")
rep(r"R(\vec a;\vec d;\lambda)", r"R(\vec a;\vec d;\vec\lambda)")
rep(r"Q_\Theta(\vec a;\vec d;\lambda)", r"Q_\Theta(\vec a;\vec d;\vec\lambda)")
i = s.index("#+NAME: thm-hstar"); j = s.index("#+end_mexample", s.index("#+NAME: ex-hstar"))
seg = s[i:j]; c1 = seg.count(r"\vec r")
seg = seg.replace(r"\vec r", r"\vec z"); seg, c2 = re.subn(r"(?<![A-Za-z\\])r_(k|2|3|n)\b", r"z_\1", seg)
assert c1 == 7 and c2 >= 4, (c1, c2)
s = s[:i] + seg + s[j:]
i = s.index("* Ehrhart theory"); j = s.index("* The centroid of the Hilbert functions")
seg, c3 = re.subn(r"\\vec ?1(?![0-9])", r"\\mathds{1}", s[i:j]); assert c3 >= 15, c3
s = s[:i] + seg + s[j:]
rep(r"\(x_{d+1}\ge a_1\) and \(x_{n+1}\le a_{m+1}\), are new", r"\(x_2\ge3\) and \(x_4\le1\), are new")
n = len(re.findall(r"\\Delta\((\\ell|j)", s)); assert n == 6, n
s = re.sub(r"\\Delta\((\\ell|j)", r"V(\1", s)
open(p, 'w').write(s)
print("ok: K, s_b, c*, (R^g)/(L^g)", (n1, n2), "gamma, copies, C_>=a, Psi, c(.), Lex, beta-bar, diff, F~, fill, Koz°, tau_i, U(t), Z, mu, vectors, z, 1:", c3, "V")
