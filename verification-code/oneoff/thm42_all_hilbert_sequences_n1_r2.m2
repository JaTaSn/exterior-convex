-- thm42_all_hilbert_sequences_n1_r2.m2
--
-- Changelog (reverse chronological):
--   2026-10-18  Created.  Second, package-native verification for
--               working-notes/amata-crupi-thm42-b-worked-n1-r2.org that (1,2) is not
--               H(F/M) for n = 1, r = 2, f = (0,0).  ExteriorModules has no
--               "all Hilbert sequences" function (allHilbertSequences exists only in
--               ExteriorIdeals, for E/I), so the list is built from actual modules:
--               every monomial M = I_1 g_1 (+) I_2 g_2 via createModule, its quotient's
--               Hilbert sequence via hilbertSequence (which takes M, returns H(F/M)).
--               By the initial-module reduction (Amata-Crupi section 2) this is every
--               H(F/M) for graded M.  Also: isHilbertSequence over the whole box, and
--               lexModuleBySequences on (1,2).
--
-- Run:  M2 --script code/oneoff/thm42_all_hilbert_sequences_n1_r2.m2

needsPackage "ExteriorIdeals";
needsPackage "ExteriorModules";

E = QQ[e_1, SkewCommutative => true];
F = E^{0,0};   -- E^{d} puts the generator in degree -d; here both in degree 0

print "-- ExteriorIdeals: allHilbertSequences E  (Hilbert sequences of E/I, n = 1)";
print toString allHilbertSequences E;

ideals = {ideal(0_E), ideal(e_1), ideal(1_E)};
print "";
print "-- ExteriorModules: every monomial M = I1*g1 + I2*g2, and hilbertSequence M = H(F/M)";
seqs = {};
for I1 in ideals do for I2 in ideals do (
    M := createModule({I1, I2}, F);
    hs := hilbertSequence M;
    seqs = append(seqs, hs);
    print("I1 = " | toString I1 | ",  I2 = " | toString I2 | "   ->  H(F/M) = " | toString hs));
print "";
print("-- distinct H(F/M): " | toString sort unique seqs);
print("-- {1,2} among them? " | toString member({1,2}, seqs));

print "";
print "-- ExteriorModules: isHilbertSequence over the box [0,2] x [0,2]";
for a from 0 to 2 do for b from 0 to 2 do
    print(toString {a,b} | "  " | toString isHilbertSequence({a,b}, F));

print "";
print "-- ExteriorModules: lexModuleBySequences({1,2}, F)";
L = try lexModuleBySequences({1,2}, F) else "error";
print toString L;
if instance(L, Module) then (
    print("   hilbertSequence of it: " | toString hilbertSequence L);
    print("   isLexModule: " | toString isLexModule L));
print "-- control: lexModuleBySequences({1,1}, F)";
L2 = lexModuleBySequences({1,1}, F);
print(toString L2 | "   hilbertSequence: " | toString hilbertSequence L2);
