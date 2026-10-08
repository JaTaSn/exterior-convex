"""Emit the two appendix tables of article 2, the analogues of Linusson's Tables 5 and 6.

His Table 5 is a numeric grid of F^p(n) -- the counts themselves.  His Table 6 is E^p(p,k),
the refinement that drives his recursion, with F^p(p) recovered as the row sum in a last
column.  The analogues here keep that pairing:

  A.1  the joint distribution A[tau][rho] of (top, indeg) for n = 1..6, which is what drives
       OUR formula, with the row sums u[tau] and the grand total |F_n| in last column/row.
  A.2  |FF(n;d)| and |FF_pr(n;d)| for constant-gap d = (0, delta, ..., (r-1)delta).

Writes LaTeX to stdout.  Run from anywhere; paths are resolved against this file.
"""
import sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), os.pardir))
import linusson_ff_counting as L

NMAX_A = 6
out = []
w = out.append

# ---------------------------------------------------------------- A.1: the matrix A
w(r"\begingroup\small")
for n in range(1, NMAX_A + 1):
    A = L.A_from_linusson(n)                      # rows tau=-1..n, cols rho=0..n+1
    rows, cols = len(A), len(A[0])
    w(r"\begin{center}")
    w(r"\begin{tabular}{@{}r|" + "r" * cols + r"|r@{}}")
    w(r"\multicolumn{%d}{@{}l}{\(n=%d\)}\\[2pt]" % (cols + 2, n))
    w(r"\(\tau\backslash\rho\) & " + " & ".join(str(r) for r in range(cols))
      + r" & \(u[\tau]\)\\")
    w(r"\hline")
    for i, row in enumerate(A):
        tau = i - 1
        w(r"\(%d\) & " % tau + " & ".join(str(v) if v else r"\(\cdot\)" for v in row)
          + r" & \(%d\)\\" % sum(row))
    w(r"\hline")
    w(r"\(\Sigma\) & " + " & ".join(str(sum(A[i][j] for i in range(rows))) for j in range(cols))
      + r" & \(\mathbf{%d}\)\\" % sum(sum(r) for r in A))
    w(r"\end{tabular}")
    w(r"\end{center}")
    if n < NMAX_A:
        w(r"\addvspace{4pt}")
w(r"\endgroup")
w("%%SPLIT%%")

# ---------------------------------------------------------------- A.2/A.3: the counts
# Improper and proper go in SEPARATE tables: side by side is 10 numeric columns, and at n = 6
# the entries reach 11 digits, which ran 141 pt over the text block.
RS = [1, 2, 3, 4, 5]
for proper in (False, True):
    w(r"\begingroup\footnotesize")
    w(r"\begin{center}")
    w(r"\begin{tabular}{@{}cc" + "r" * len(RS) + r"@{}}")
    w(r"\toprule")
    w(r"\(n\) & \(\delta\) & " + " & ".join(r"\(r=%d\)" % r for r in RS) + r"\\")
    w(r"\midrule")
    for n in range(2, 7):
        for delta in range(0, n + 2):
            vals = [L.ff_count(n, [i * delta for i in range(r)], proper=proper) for r in RS]
            lead = r"\(%d\)" % n if delta == 0 else ""
            w("%s & \\(%d\\) & " % (lead, delta)
              + " & ".join(f"{v:,}".replace(",", r"\,") for v in vals) + r"\\")
        if n < 6:
            w(r"\addlinespace")
    w(r"\bottomrule")
    w(r"\end{tabular}")
    w(r"\end{center}")
    w(r"\endgroup")
    if not proper:
        w("%%SPLIT%%")
print("\n".join(out))
