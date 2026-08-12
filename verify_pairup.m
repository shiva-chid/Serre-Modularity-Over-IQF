// SetLogFile("verify_pairup.log");
// SetLogFile("CompatibleSubsetsOfChars.log");
// SetLogFile("CompatibleSubsetsOfChars1.log");

load "nonsurj7.txt";
load "allcharsoutput.txt";
assert #condgens eq 381 and #vals eq 381;

AttachSpec("spec");

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
{* #x : x in allpairinds *};   
// {* 2^^4, 3^^376, 4 *}

allconjdualinds := [];
for i := 1 to #allchars do
    conjdualinds := [j : j in [1..#allchars[i]] | isconjugatethedual(allchars[i][j],ell : chi_ell := chi_ell, ellaboveK := ellaboveK)];
    Append(~allconjdualinds,conjdualinds);
end for;
{* #x : x in allconjdualinds *};
// {* 2^^380, 4 *}
allconjdualinds;

// fil := "allcharsoutput.txt";
fil1 := "allcharsoutput1.txt";
PrintFile(fil1, "allpairinds := ");
PrintFile(fil1, allpairinds);
PrintFile(fil1, ";");
PrintFile(fil1, "allconjdualinds := ");
PrintFile(fil1, allconjdualinds);
PrintFile(fil1, ";");

allGalpairinds := [];
for i := 1 to #allchars do
    pairedchars, inds := pairupconjugate(allchars[i],ell);
    Append(~allGalpairinds, inds);
end for;
{* #x : x in allGalpairinds *};
// {* 3^^380, 4 *}

PrintFile(fil1, "allGalpairinds := ");
PrintFile(fil1, allGalpairinds);
PrintFile(fil1, ";");

SetLogFile("CompatibleSubsetsOfChars.log");
AttachSpec("spec");
P<x> := PolynomialRing(Rationals());

Allpossiblesubsetsofchars := [];
errorinds := [];
time for i := 1 to #curves do
    try
        chars := [*HeckeCharacter((F!condgens[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals[i][j]*]) : j in [1..#vals[i]] *];
        assert #chars in {4,6,8};
        ans := CompatibleSubsetsOfChars(P!curves[i],ell,chars,allGalpairinds[i],allpairinds[i]);
        printf "%o:%o\n", i, &cat[s : s in Split(Sprint(ans),"\n")];
        Append(~Allpossiblesubsetsofchars,ans);
    catch e;
        print i, e;
        Append(~errorinds,i);
    end try;
end for;
errorinds;
// L := [[[*<Set(z[1]),z[2]> : z in y*] : y in x] : x in Allpossiblesubsetsofchars];
L := Allpossiblesubsetsofchars;
{*#x : x in L*};
// old {* 1^^349, 2^^4, 3^^27, 5 *}
// {* 1^^352, 2, 3^^28 *}
PrintFile(fil1, "Allpossiblesubsetsofchars := ");
PrintFile(fil1, L);
PrintFile(fil1, ";");
{* {* {*<#z[1],z[2]> : z in y*} : y in x*} : x in L | #x eq 1 *};
/*
{*
{*
{* <2, 1>, <4, 0> *}
*}^^352
*}
*/
inds2 := [i : i in [1..#L] | #L[i] eq 2]; inds2;
// [ 207 ]
{* {* {*<#z[1],z[2]> : z in y*} : y in x*} : x in L | #x eq 2 *};
/*
{*
{*
{* <2, 0>, <2, 1>, <4, 0> *}^^2
*}
*}
*/
inds3 := [i : i in [1..#L] | #L[i] eq 3]; inds3;
// [ 25, 87, 104, 138, 169, 184, 194, 200, 209, 217, 238, 242, 248, 262, 273, 278, 279, 318, 329, 331, 333, 336, 349, 350, 351, 357, 360, 370 ]
{* {* {*<#z[1],z[2]> : z in y*} : y in x*} : x in L | #x eq 3 *};
/*
{*
{*
{* <2, 0>, <4, 1> *},
{* <2, 1>, <4, 0> *},
{* <2, 1>, <4, 1> *}
*}^^28
*}
*/
[i : i in [1..#L] | {* <2,1>, <4,1> *} in [{*<#z[1],z[2]> : z in y*} : y in L[i]]];
// old [ 25, 104, 138, 169, 184, 194, 200, 209, 217, 238, 242, 248, 262, 273, 278, 279, 318, 329, 331, 333, 336, 349, 350, 351, 357, 360, 370 ]
// [ 25, 87, 104, 138, 169, 184, 194, 200, 209, 217, 238, 242, 248, 262, 273, 278, 279, 318, 329, 331, 333, 336, 349, 350, 351, 357, 360, 370 ]
[i : i in [1..#L] | [* <2,2>, <2,1> *] in [[*<#z[1],z[2]> : z in y*] : y in L[i]]];
// old [ 87 ]
// []


P<x> := PolynomialRing(QQ);
L := [P!x : x in curves[inds3]];
AttachSpec("spec");
L1, L2 := UptoTwist(L);
assert #L1 eq 3;
L1, L2;
/*
[
2187*x^4 + 1586*x^3 + 420*x^2 + 48*x + 2,
1458*x^4 + 557*x^3 + 129*x^2 + 15*x + 1,
75*x^4 + 146*x^3 + 183*x^2 + 48*x + 1
]
[
x^4 - 98934*x^2 - 1139608*x + 2398493805,
x^4 + 1147818*x^2 + 70829416*x + 301621348077,
x^4 + 22926*x^2 - 2743264*x + 56437377
]
*/
////////////////////////////////////////////////////////

SetLogFile("verify_pairup.log");
primegens := [gen where _,gen is IsPrincipal(pp) : pp in PrimesUpTo(1000,F)];

// Raynaud says that for every character eps appearing in the semisimplification,
// one of eps or eps^-1*chi_ell must be unramified at lam1, and
// the same for lam2.
// Let's retain only those characters
// Note: Raynaud's theorem applies only to those Jacobians that have good/semistable reduction at 7.
prunedchars := [[*y : y in x | not &or[(Conductor(y) subset lami and Conductor(y^-1*chi_ell) subset lami) : lami in [lam1,lam2]] *] : x in allchars];
{* #x : x in prunedchars *};
// {* 0^^135, 2^^80, 4^^8, 6^^157, 8 *}

conds := [[* Conductor(x) : x in y *] : y in prunedchars];
condgens := [[Eltseq(gen) where _,gen is IsPrincipal(x) : x in y] : y in conds];
vals := [[[*<Eltseq(pp),Eltseq(K!(prunedchars[i][j](pp)))> : pp in primegens | not conds[i][j] subset pp*OF *] : j in [1..#prunedchars[i]]] : i in [1..#prunedchars]];
// {*{*{#val[2] : val in x} : x in y*} : y in vals*};
PrintFile(fil1, "condgens_prunedchars := ");
PrintFile(fil1, condgens);
PrintFile(fil1, ";");
PrintFile(fil1, "vals_prunedchars := ");
PrintFile(fil1, vals);
PrintFile(fil1, ";");

pairinds := [];
for i := 1 to #prunedchars do
    pairedchars, inds := pairup(prunedchars[i],ell : chi_ell := chi_ell);
    Append(~pairinds, inds);
end for;
pairinds;
{* #x : x in pairinds *};
// {* 0^^135, 1^^80, 2^^8, 3^^157, 4 *}

conjdualinds := [];
for i := 1 to #prunedchars do
    conjdual := [j : j in [1..#prunedchars[i]] | isconjugatethedual(prunedchars[i][j],ell : chi_ell := chi_ell, ellaboveK := ellaboveK)];
    Append(~conjdualinds,conjdual);
end for;
{* #x : x in conjdualinds *};
// {* 0^^141, 2^^239, 4 *}
conjdualinds;

PrintFile(fil1, "pairinds := ");
PrintFile(fil1, pairinds);
PrintFile(fil1, ";");
PrintFile(fil1, "conjdualinds := ");
PrintFile(fil1, conjdualinds);
PrintFile(fil1, ";");

Galpairinds := [];
for i := 1 to #prunedchars do
    pairedchars, inds := pairupconjugate(prunedchars[i],ell);
    Append(~Galpairinds, inds);
end for;
{* #x : x in Galpairinds *};
// {* 0^^135, 1^^79, 2^^6, 3^^160, 4 *}

PrintFile(fil1, "Galpairinds := ");
PrintFile(fil1, Galpairinds);
PrintFile(fil1, ";");

P<x> := PolynomialRing(Rationals());
time allpossiblesubsetsofchars := [CompatibleSubsetsOfChars(P!curves[i],ell,prunedchars[i],Galpairinds[i],pairinds[i]) : i in [1..#curves]];

////////////////////////////////////////////////////////
// calculations after loading in

P<x> := PolynomialRing(Rationals());

condgens := condgens_prunedchars;
vals := vals_prunedchars;
// time prunedchars := [[*HeckeCharacter((F!condgens[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals[i][j]*]) : j in [1..#vals[i]] *] : i in [1..#vals]];
// Time: 1284.250
// time prunedchars := [[*HeckeCharacter((F!condgens[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals[i][j]*]) : j in [1..#vals[i]] *] : i in [1..10]];
// time temp, pairinds := pairupconjugate(prunedchars[1],ell);
// time allpossiblesubsetsofchars := [CompatibleSubsetsOfChars(P!curves[i],ell,prunedchars[i],Galpairinds[i],pairinds[i]) : i in [1..#prunedchars]];
allpossiblesubsetsofchars := [];
errorinds := [];
for i := 1 to #curves do
    try
        chars := [*HeckeCharacter((F!condgens[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals[i][j]*]) : j in [1..#vals[i]] *];
        ans := CompatibleSubsetsOfChars(P!curves[i],ell,chars,Galpairinds[i],pairinds[i]);
        printf "%o:%o\n", i, &cat[s : s in Split(Sprint(ans),"\n")];
        Append(~allpossiblesubsetsofchars,ans);
    catch e;
        print e;
        Append(~errorinds,i);
    end try;
end for;
L := allpossiblesubsetsofchars;
{*#x : x in L*};
// {* 0^^135, 1^^241, 2^^5 *}
// {* 0^^135, 1^^245, 2 *}

PrintFile(fil1, "allpossiblesubsetsofchars := ");
PrintFile(fil1, L);
PrintFile(fil1, ";");

////////////////////////////////////////////////////////
load "allcharsoutput.txt";
#allpossiblesubsetsofchars;
L := allpossiblesubsetsofchars;
L[1];
{* {* <#y[1],y[2]> : y in x[1] *} : x in L | #x eq 1 *};
/*
{*
{* <2, 1> *}^^79,
{* <2, 1>, <4, 0> *}^^157,
{* <4, 1> *}^^5
*}
{*
{* <2, 0>, <2, 1> *}^^3,
{* <2, 1> *}^^80,
{* <2, 1>, <4, 0> *}^^157,
{* <4, 1> *}^^5
*}
{*
{* <2, 1> *}^^79,
{* <2, 1>, <4, 0> *}^^160,
{* <4, 1> *}^^6
*}
*/
inds := [ i : i in [1..#L] | #x eq 1 and {*<#y[1],y[2]> : y in x[1]*} eq {*<4,1>*} where x is L[i]]; inds;
// [ 194, 238, 279, 333, 349 ]
// [ 194, 238, 279, 333, 349 ]
// [ 87, 194, 238, 279, 333, 349 ]
[#x : x in vals_prunedchars[inds]];
// [ 2, 4, 4, 4, 4, 4 ]
Galpairinds[inds];
/*
[
[ <1, 1>, <2, 2> ],
[ <1, 4>, <2, 3> ],
[ <1, 4>, <2, 3> ],
[ <1, 4>, <2, 3> ],
[ <1, 4>, <2, 3> ],
[ <1, 4>, <2, 3> ]
]
*/
pairinds[inds];
/*
[
[ <1, 2> ],
[ <1, 3>, <2, 4> ],
[ <1, 3>, <2, 4> ],
[ <1, 3>, <2, 4> ],
[ <1, 2>, <3, 4> ],
[ <1, 3>, <2, 4> ]
]
*/



{* {* <#y[1],y[2]> : y in x[1] *} : x in L | #x eq 2 *};
/*
{*
{* <2, 0>, <2, 1> *}^^3,
{* <2, 0>, <2, 1>, <4, 0> *},
{* <2, 1> *}
*}
{*
{* <2, 0>, <2, 1>, <4, 0> *},
*}
*/
{* [{* <#z[1],z[2]> : z in y *} : y in x] : x in L | #x eq 2 *};
/*
{*
[
{* <2, 0>, <2, 1>, <4, 0> *},
{* <2, 0>, <2, 1>, <4, 0> *}
]
*}
*/
inds := [ i : i in [1..#L] | #L[i] eq 2]; inds;
// [ 6, 11, 87, 188, 207 ]
// [ 207 ]
// [ 207 ]
L[inds];
/*
[
[ [*
<{ 1, 3 }, 0>,
<{ 2, 4 }, 1>
*], [*
<{ 1, 3 }, 1>,
<{ 2, 4 }, 0>
*] ],
[ [*
<{ 1, 3 }, 0>,
<{ 2, 4 }, 1>
*], [*
<{ 1, 3 }, 1>,
<{ 2, 4 }, 0>
*] ],
[ [*
<{ 1, 2 }, 1>
*], [*
<{ 1, 2 }, 2>
*] ],
[ [*
<{ 1, 4 }, 0>,
<{ 2, 3 }, 1>
*], [*
<{ 1, 4 }, 1>,
<{ 2, 3 }, 0>
*] ],
[ [*
<{ 1, 5 }, 0>,
<{ 2, 6 }, 1>,
<{ 3, 4, 7, 8 }, 0>
*], [*
<{ 1, 5 }, 1>,
<{ 2, 6 }, 0>,
<{ 3, 4, 7, 8 }, 0>
*] ]
]

[
[ [*
<{* 1, 5 *}, 0>,
<{* 2, 6 *}, 1>,
<{* 3, 4, 7, 8 *}, 0>
*], [*
<{* 1, 5 *}, 1>,
<{* 2, 6 *}, 0>,
<{* 3, 4, 7, 8 *}, 0>
*] ]
]
*/
[#x : x in vals_prunedchars[inds]];
// [ 4, 4, 2, 4, 8 ]
// [ 8 ]
Galpairinds[inds];
/*
[
[ <1, 1>, <2, 4>, <3, 3> ],
[ <1, 1>, <2, 4>, <3, 3> ],
[ <1, 1>, <2, 2> ],
[ <1, 1>, <2, 3>, <4, 4> ],
[ <1, 5>, <2, 6>, <3, 7>, <4, 8> ]
]

[
[ <1, 5>, <2, 6>, <3, 7>, <4, 8> ]
]
*/
pairinds[inds];
/*
[
[ <1, 3>, <2, 4> ],
[ <1, 3>, <2, 4> ],
[ <1, 2> ],
[ <1, 4>, <2, 3> ],
[ <1, 5>, <2, 6>, <3, 4>, <7, 8> ]
]

[
[ <1, 5>, <2, 6>, <3, 4>, <7, 8> ]
]
*/
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