SetColumns(0);
SetLogFile("2dcharpolys_2ndcurve.log");
i := 2;
load "nonsurj7.txt";
load "allcharsoutput.txt";

AttachSpec("spec");
F<zeta3> := CyclotomicField(3);
OF := RingOfIntegers(F);
ell := 7;
K<zeta6> := CyclotomicField(ell-1);
P<x> := PolynomialRing(QQ);
f := P!curves[i];
cond := conds[i];

condgens := condgens_prunedchars;
vals := vals_prunedchars;
chars := [*HeckeCharacter((F!condgens[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals[i][j]*]) : j in [1..#vals[i]] *];
assert #chars eq 6;
ans := CompatibleSubsetsOfChars(P!curves[i],ell,chars,Galpairinds[i],pairinds[i]);
assert allpossiblesubsetsofchars[i] eq ans;
assert #ans eq 1;
ans := ans[1];
epsiloninds := &join[ {*x^^block[2] : x in block[1]*} : block in ans];
assert epsiloninds eq {* 1,2 *};
epsiloninds := Sort(Setseq(Set(epsiloninds)));
assert epsiloninds eq [1,2];
epsilons := [*chars[ii] : ii in epsiloninds*];
condgens[i][epsiloninds];

charpols := getcharpols(f); // precomputing the Frobenius characteristic polynomials

possibledets := find_determinant(f,ell,epsilons[1] : charpols := charpols);
assert #possibledets eq 1;
det := possibledets[1]`char;
chi_ell := AssociatedPrimitiveCharacter(epsilons[1]*epsilons[2]);
assert AssociatedPrimitiveCharacter(chi_ell^2) eq AssociatedPrimitiveCharacter(det^2);

primesdetstraces := find_trace(f,ell,epsilons[1],det : charpols := charpols);
#primesdetstraces;
primesdetstraces;

exacttraces := [x : x in primesdetstraces | #x[3] eq 1];
#exacttraces;
exacttraces;

{* #x[3] : x in primesdetstraces | #x[3] ne 1 *};                               
assert &and[x[3][1] eq -x[3][2] : x in primesdetstraces | #x[3] ne 1];

fil := "primesdetstraces_2ndcurve.txt";
PrintFile(fil, "primesdetstraces := ");
PrintFile(fil, primesdetstraces);
PrintFile(fil, ";");

////////////////////////////////////////////////////

assert det(-zeta3) eq 1;
detdiff := det*chi_ell^-1;
assert Conductor(detdiff) eq 4*OF;
assert Order(detdiff) eq 2;
L := NumberField(AbelianExtension(detdiff));
assert IsSquare(L!-1);
