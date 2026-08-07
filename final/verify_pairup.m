// SetLogFile("verify_pairup.log");
// load "nonsurj7.txt";
AttachSpec("spec");

load "allcharsoutput.txt";
assert #condgens eq 381 and #vals eq 381;

F<zeta3> := CyclotomicField(3);
OF := RingOfIntegers(F);
ell := 7;
ellaboveF := PrimeIdealsOverPrime(F,ell);
lam1 := ellaboveF[1]; lam2 := ellaboveF[2];
K<zeta6> := CyclotomicField(ell-1);
ellaboveK := PrimeIdealsOverPrime(K,ell)[1];
chi_ell := ModEllCyclotomicCharacter(F,ell : K := K, lambda := ellaboveK);

time allchars := [[*HeckeCharacter((F!condgens[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals[i][j]*]) : j in [1..#vals[i]] *] : i in [1..#vals]];
// takes a while (~1h) to rebuild all the characters from the stored values.

allpairinds := [];
for i := 1 to #allchars do
    pairedchars, inds := pairup(allchars[i],ell : chi_ell := chi_ell);
    Append(~allpairinds, inds);
end for;
allpairinds;

allconjdualinds := [];
for i := 1 to #allchars do
    conjdualinds := [j : j in [1..#allchars[i]] | isconjugatethedual(allchars[i][j],ell : chi_ell := chi_ell, lambda := ellaboveK)];
    Append(~allconjdualinds,conjdualinds);
end for;
{* #x : x in allconjdualinds *};
// {* 2^^380, 4 *}
allconjdualinds;

////////////////////////////////////////////////////////

/*
// pairing the characters with their duals is slightly tricky, as in the following example.

i := 4;
chars := allchars[i];
conds := [Conductor(x) : x in chars]; conds;
[<x subset lam1, x subset lam2> : x in conds];
// [ <true, true>, <false, true>, <true, false>, <false, true>, <true, true>, <true, false> ]
partially_ramified_chars := [*chars[i] : i in [1..#chars] | not (conds[i] subset ell*OF)*]; #partially_ramified_chars;
// 4
assert conds[2]*conds[3] eq 1008*OF;
assert conds[4]*conds[6] eq 63*OF;
assert Conductor(chars[4]*chars[6]) eq 7*OF;
assert Conductor(chars[2]*chars[3]) eq 7*OF;
assert Conductor(chars[1]*chars[5]) eq 7*OF;
chi1 := AssociatedPrimitiveCharacter(chars[4]*chars[6]);
chi2 := AssociatedPrimitiveCharacter(chars[2]*chars[3]);
chi3 := AssociatedPrimitiveCharacter(chars[1]*chars[5]);
chi1 eq chi2, chi2 eq chi3, chi3 eq chi1;
// false false false
chi1, chi2, chi3;
// $.1^5 $.1^3 $.1
Order(chi1), Order(chi2), Order(chi3);
// 6 2 6


chi1 := AssociatedPrimitiveCharacter(chars[4]*chars[6]);
chi2 := AssociatedPrimitiveCharacter(chars[1]*chars[2]);
chi3 := AssociatedPrimitiveCharacter(chars[3]*chars[5]);
assert chi1 eq chi2 and chi2 eq chi3 and chi3 eq chi1;

*/