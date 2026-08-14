// initialize files. // overwrites. Use with caution.
/*
echo "allprimesdetstraces := AssociativeArray();" > allprimesdetstraces.txt
echo "numberofpossibledetchars := AssociativeArray();" > numberofpossibledetchars.txt
echo "orderofNebentypus := AssociativeArray();\nNebentypusField := AssociativeArray();" > Nebentypus.txt
*/

SetColumns(0);
i := StringToInteger(i);

load "nonsurj7.txt";
P<x> := PolynomialRing(QQ);
f := P!curves[i];
cond := conds[i];
ell := 7;
// if cond mod ell eq 0 then exit; end if;

load "allcharsoutput.txt";

AttachSpec("spec");
F<zeta3> := CyclotomicField(3);
OF := RingOfIntegers(F);
K<zeta6> := CyclotomicField(ell-1);
ellaboveK := PrimeIdealsOverPrime(K,ell)[1];
chi_ell := ModEllCyclotomicCharacter(F,ell : K := K, lambda := ellaboveK);


// fil1 := "allprimesdetstraces_goodat7.txt";
// fil2 := "numberofpossibledetchars_goodat7.txt";
// fil3 := "orderofNebentypus_goodat7.txt";
// fil_err := "error_detandtrace_goodat7.txt";
fil1 := "allprimesdetstraces.txt";
fil2 := "numberofpossibledetchars.txt";
fil3 := "Nebentypus.txt";
fil_err := "error_detandtrace.txt";

fil1 := "allprimesdetstraces_ns13.txt";
fil2 := "numberofpossibledetchars_ns13.txt";
fil3 := "Nebentypus_ns13.txt";
fil_err := "error_detandtrace_ns13.txt";


try
    // chars := [*HeckeCharacter((F!condgens_prunedchars[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals_prunedchars[i][j]*]) : j in [1..#vals_prunedchars[i]] *];
    // ans := CompatibleSubsetsOfChars(P!curves[i],ell,chars,Galpairinds[i],pairinds[i]);
    // assert allpossiblesubsetsofchars[i] eq ans;
    // assert #ans eq 1;
    // ans := ans[1];
    // epsiloninds := &join[ {*x^^block[2] : x in block[1]*} : block in ans];
    // epsiloninds := Sort(Setseq(Set(epsiloninds)));
    // epsilons := [*chars[ii] : ii in epsiloninds*];
    // condgens_prunedchars[i][epsiloninds];

    chars := [*HeckeCharacter((F!condgens[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals[i][j]*]) : j in [1..#vals[i]] *];
    ans := CompatibleSubsetsOfChars(P!curves[i],ell,chars,allGalpairinds[i],allpairinds[i]);
    assert Allpossiblesubsetsofchars[i] eq ans;
    assert #ans eq 1 or (i eq 207 and #ans eq 2) or #ans eq 3;
    if #ans gt 1 then ans := [x : x in ans | &+[#block[1]*block[2] : block in x] eq 2]; end if;
    if #ans gt 1 then
        out := Sprintf("%o:%o possibilities for the pair <epsilon,epsilon^c>", i, #ans);
        PrintFile(fil_err, out);
        exit;
    end if;
    assert #ans eq 1;
    ans := ans[1];
    epsiloninds := &join[ {*x^^block[2] : x in block[1]*} : block in ans];
    epsiloninds := Sort(Setseq(Set(epsiloninds)));
    epsilons := [*chars[ii] : ii in epsiloninds*];
    // condgens[i][epsiloninds];

    charpols := getcharpols(f); // precomputing the Frobenius characteristic polynomials

    possibledets := find_determinant(f,ell,epsilons[1] : charpols := charpols);
    dets := [*x`char : x in possibledets*];
    // print #dets;
    conjpairs, conjpairinds := pairupconjugate(dets,ell);
    goodpairs := [* x : x in conjpairs | AssociatedPrimitiveCharacter(x[1]*x[2]) eq chi_ell^2 *];
    assert #goodpairs eq 1;
    det := goodpairs[1][1];
    assert det(-zeta3) eq 1;
    Nebentypus := det*chi_ell^-1;
    ordNeben := Order(Nebentypus);
    // assert ordNeben le 2;
    Ldefpol := DefiningPolynomial(NumberField(AbelianExtension(Nebentypus)));


/*
    allprimesdetstraces := [find_trace(f,ell,epsilons[1],det : charpols := charpols) : det in dets];
    // #primesdetstraces;
    // primesdetstraces;

    allexacttraces := [[x : x in primesdetstraces | #x[3] eq 1] : primesdetstraces in allprimesdetstraces];
    // #exacttraces;
    // exacttraces;

    assert &and[#[x : x in primesdetstraces | #x[3] gt 2] eq 0 : primesdetstraces in allprimesdetstraces];
    // {* #x[3] : x in primesdetstraces | #x[3] ne 1 *};                               
    assert &and[&and[x[3][1] eq -x[3][2] : x in primesdetstraces | #x[3] ne 1] : primesdetstraces in allprimesdetstraces];
*/

    allprimesdetstraces := find_trace(f,ell,epsilons[1],det : charpols := charpols);
    // #primesdetstraces;
    // primesdetstraces;

    allexacttraces := [x : x in allprimesdetstraces | #x[3] eq 1];
    // #exacttraces;
    // exacttraces;

    assert #[x : x in allprimesdetstraces | #x[3] gt 2] eq 0;
    // {* #x[3] : x in primesdetstraces | #x[3] ne 1 *};
    assert &and[x[3][1] eq -x[3][2] : x in allprimesdetstraces | #x[3] ne 1];

    out := Sprintf("allprimesdetstraces[%o] := %m;", i, allprimesdetstraces);
    PrintFile(fil1, out);

    outextra := Sprintf("numberofpossibledetchars[%o] := %m;", i, #dets);
    PrintFile(fil2, outextra);

    outextra := Sprintf("orderofNebentypus[%o] := %m;\nNebentypusField[%o] := %m;", i, ordNeben, i, Ldefpol);
    PrintFile(fil3, outextra);
catch e;
    out := Sprintf("%o:%o:%o:%o:%o", i, #dets, goodpairs, e`Position, e`Object);
    PrintFile(fil_err, out);
end try;
exit;

////////////////////////////////////////////////////
/*
assert det(-zeta3) eq 1;
detdiff := det*chi_ell^-1;
assert Conductor(detdiff) eq 4*OF;
assert Order(detdiff) eq 2;
L := NumberField(AbelianExtension(detdiff));
assert IsSquare(L!-1);
*/

// seq 1 381 | parallel --eta -j 32 magma i:={} parallelrun_detandtrace.m

////////////////////////////////////////////////////////

load "allprimesdetstraces_goodat7.txt";
load "numberofpossibledetchars_goodat7.txt";
Ks := Keys(numberofpossibledetchars);
assert #Ks eq 109;
{* numberofpossibledetchars[i] : i in Ks *};
// {* 3^^4, 4^^105 *}

////////////////////////////////////////////////////////

load "allprimesdetstraces.txt";
load "numberofpossibledetchars.txt";
load "Nebentypus.txt";
Ks := Keys(numberofpossibledetchars);
assert #Ks eq 349;
assert Ks eq Keys(orderofNebentypus);
assert Ks eq Keys(NebentypusField);
assert Ks eq Keys(allprimesdetstraces);

badinds := Sort(Setseq({1..381} diff Ks)); badinds;
// [ 71, 89, 102, 129, 135, 154, 162, 175, 199, 204, 207, 234, 241, 260, 282, 288, 290, 293, 307, 310, 316, 321, 324, 330, 352, 353, 362, 363, 367, 371, 372, 380 ]

{* numberofpossibledetchars[i] : i in Ks *};
// {* 3^^11, 4^^338 *}
{* orderofNebentypus[i] : i in Ks *};
// {* 1^^4, 2^^7, 3^^104, 6^^234 *}

Ks := Sort(Setseq(Ks));
inds1 := [i : i in Ks | orderofNebentypus[i] eq 1]; inds1;
// [ 6, 11, 87, 188 ]
{* NebentypusField[i] : i in inds1 *};
/*
{*
(T^2 + T + 1)^^4
*}
*/
inds2 := [i : i in Ks | orderofNebentypus[i] eq 2]; inds2;
// [ 2, 30, 82, 86, 143, 370, 373 ]
{* NebentypusField[i] : i in inds2 *};
/*
{*
($.1^2 - 7)^^3,
($.1^2 + zeta_3)^^2,
($.1^2 + 7*zeta_3)^^2
*}
*/

for i in inds1 do
    fil := Sprintf("primesdetstraces_%othcurve.txt", i);
    PrintFile(fil, "primesdetstraces := ");
    PrintFile(fil, allprimesdetstraces[i]);
    PrintFile(fil, ";");
end for;

load "allcharsoutput.txt";
for i in inds1 do
    print i;
    print allGalpairinds[i], allpairinds[i], allconjdualinds[i];
    print Allpossiblesubsetsofchars[6];
end for;
/*
6
[ <1, 1>, <2, 4>, <3, 3> ]
[ <1, 3>, <2, 4> ]
[ 2, 4 ]
[ [*
<{* 1^^2, 3^^2 *}, 0>,
<{* 2, 4 *}, 1>
*] ]
11
[ <1, 1>, <2, 4>, <3, 3> ]
[ <1, 3>, <2, 4> ]
[ 2, 4 ]
[ [*
<{* 1^^2, 3^^2 *}, 0>,
<{* 2, 4 *}, 1>
*] ]
87
[ <1, 1>, <2, 2>, <3, 4> ]
[ <1, 2>, <3, 4> ]
[ 3, 4 ]
[ [*
<{* 1^^2, 3^^2 *}, 0>,
<{* 2, 4 *}, 1>
*] ]
188
[ <1, 1>, <2, 3>, <4, 4> ]
[ <1, 4>, <2, 3> ]
[ 2, 3 ]
[ [*
<{* 1^^2, 3^^2 *}, 0>,
<{* 2, 4 *}, 1>
*] ]
*/

possibly_fully_reducible_ss := [i : i in [1..#Allpossiblesubsetsofchars] | #Allpossiblesubsetsofchars[i] eq 3];
assert #possibly_fully_reducible_ss eq 28;
Set(possibly_fully_reducible_ss) meet Set(badinds);
// {}

