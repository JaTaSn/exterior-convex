-- m2_oracle_ff_counts.m2 -- the Macaulay2 oracle of article 2's "How the results were checked".
--
-- Changelog (newest first):
--   2026-10-08  Claude (jts-office), at Jan's request.  The counts 43, 69, 99, 236 (n = 3) and 368
--               (n = 4) were first obtained 2026-09-05 with a throw-away script that was never
--               saved; their only record was working-notes/amata-crupi-monomial-modules.org.  The
--               2026-10-08 review of article 2 could not trace them to any script.  This is the
--               permanent version.
--
-- What it does, for each (n, d):  enumerate EVERY monomial submodule M = I_1 g_1 + ... + I_r g_r of
-- F = (wedge V) g_1 + ... + (wedge V) g_r, deg g_i = d_i (Amata and Crupi, Definition 2.1), with the
-- I_i ranging over all monomial ideals of the exterior algebra on n variables; compute the Hilbert
-- function of F/M with the ExteriorModules package's hilbertSequence; and report
--   (a) the number of distinct Hilbert functions, which is |FF(n; d)| by definition;
--   (b) the number of lex submodules (isLexModule), and
--   (c) the number of distinct Hilbert functions among the lex submodules.
-- Amata and Crupi's theory says (a) = (b) = (c): every achievable Hilbert function has exactly one lex
-- representative.  The expected value is the transfer-matrix count of the paper (Theorem thm-main),
-- computed independently by linusson_ff_counting.py; it is hard-coded below and compared.
--
-- Nothing here uses the paper's formula, Linusson's recursion, or Kruskal--Katona: only the module
-- theory as implemented in Macaulay2.
--
-- Run:  M2 --script m2_oracle_ff_counts.m2      (Macaulay2 1.26.06; about six minutes on jts-office, mostly n = 4)

needsPackage "ExteriorModules";

-- all up-closed families of subsets of {0..n-1}, i.e. all monomial ideals, as lists of subsets
upSets = n -> (
    subs := subsets toList(0..n-1);
    select(subsets subs, U -> all(U, S -> all(toList(0..n-1), i -> member(sort unique append(S, i), U))))
    );

monomialIdeal' = (E, U) -> (
    if #U == 0 then ideal(0_E)
    else ideal apply(U, S -> product(S, i -> E_i) * 1_E)
    );

countCheck = (n, d, expected) -> (
    E := QQ[e_1..e_n, SkewCommutative => true];
    F := E^(apply(d, x -> -x));
    ideals := apply(upSets n, U -> monomialIdeal' (E, U));
    L := n + max d - min d + 1;
    pad := hs -> join(hs, toList(max(0, L - #hs) : 0));
    allHF := new MutableHashTable; lexHF := new MutableHashTable; nlex := 0; nmods := 0;
    for t in toList((#d : 0) .. (#d : #ideals - 1)) do (
        M := createModule(apply(toList t, i -> ideals#i), F);
        hs := pad hilbertSequence M;
        allHF#hs = 1; nmods = nmods + 1;
        if isLexModule M then (nlex = nlex + 1; lexHF#hs = 1);
        );
    a := #keys allHF; c := #keys lexHF;
    ok := a == expected and nlex == expected and c == expected;
    print(concatenate("n=", toString n, " d=", toString d, ": ", toString nmods, " monomial submodules, ",
        toString a, " Hilbert functions, ", toString nlex, " lex submodules (", toString c,
        " distinct), expected ", toString expected, "  ", if ok then "PASS" else "FAIL"));
    ok
    );

results = {
    countCheck(3, {0, 0}, 43),
    countCheck(3, {0, 1}, 69),
    countCheck(3, {-1, 2}, 99),
    countCheck(3, {0, 0, 1}, 236),
    countCheck(4, {0, 1}, 368)
    };
print(if all(results, identity) then "ALL PASS" else "SOME FAILED");
