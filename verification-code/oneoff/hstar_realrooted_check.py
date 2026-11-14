# 2026-11-09 - Claude-Code (jts-mini): written by a subagent for working-notes/computational-data-inventory-2026-11-09.org
#   and moved here from the session scratchpad. Reads the stored h*-vectors (sections D of the 2026-10-20 volume/Ehrhart
#   log and the review log), checks conj-codegree, log-concavity, palindromy and real-rootedness (exact real-root
#   count by Sturm sequences, sympy count_roots; a count equal to the degree means all roots real). Needs sympy.
#   Usage, from the project directory: sage code/oneoff/hstar_realrooted_check.py (sympy comes with Sage)
import re, sys, ast
import sympy as sp
R = 'runs/2026-10-20_article3-overnight-push/'
txt = open(R + '2026-10-20_kozlov_volume_ehrhart.txt').read()
D = txt.split('D. Ehrhart polynomials')[1].split('E. Discrete volume')[0]
cases = {}
for m in re.finditer(r'n=(\d+) d=(\[[^\]]*\])\s+D=\s*(\d+) NV=(\d+)\s+h\*=(\[[^\]]*\])', D):
    n = int(m[1]); d = tuple(ast.literal_eval(m[2])); h = ast.literal_eval(m[5])
    cases[(n, d)] = dict(D=int(m[3]), h=h, src='D')
rev = open(R + '2026-10-20_review-volume-ehrhart.txt').read()
for m in re.finditer(r'n=(\d+) d=\(([^)]*)\) NV=(\d+) h\*=(\[[^\]]*\])', rev):
    n = int(m[1]); d = tuple(int(x) for x in m[2].split(',')); h = ast.literal_eval(m[4])
    if (n, d) in cases:
        assert cases[(n, d)]['h'] == h, (n, d)
    else:
        # dimension: |union of [d_i+2, d_i+n]|
        U = set()
        for di in d: U |= set(range(di + 2, di + n + 1))
        cases[(n, d)] = dict(D=len(U), h=h, src='review')
z = sp.symbols('z')
print('total cases', len(cases), 'from D:', sum(c['src']=='D' for c in cases.values()))
nontriv = 0; bad = []
for (n, d), c in sorted(cases.items(), key=lambda kv: (len(kv[0][1]), kv[0][0], kv[0][1])):
    h = c['h']; Dm = c['D']
    codeg = Dm + 1 - (len(h) - 1)
    eq = d[-2] == d[-1]
    conj_ok = (codeg == 1) == eq
    if n >= 3 and (eq or d[-1] == d[-2] + 1): nontriv += 1
    p = sp.Poly(list(reversed(h)), z)
    nreal = sp.Poly(p, z).count_roots() if p.degree() > 0 else 0
    rr = nreal == p.degree()
    lc = all(h[i]**2 >= h[i-1]*h[i+1] for i in range(1, len(h)-1))
    pal = h == h[::-1]
    if not (conj_ok and lc): bad.append((n, d))
    print(f"{n} {d} D={Dm} codeg={codeg} conj={'ok' if conj_ok else 'FAIL'} lc={lc} realrooted={rr} ({nreal}/{p.degree()}) pal={pal} src={c['src']}")
print('nontrivial conj cases (n>=3, d_r-d_{r-1} in {0,1}):', nontriv)
print('bad', bad)
