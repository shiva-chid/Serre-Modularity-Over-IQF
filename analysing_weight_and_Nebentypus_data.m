AttachSpec("spec");

////////////////////////////////////////////////////////

load "outputfiles/allprimesdetstraces_goodat7.txt";
load "outputfiles/numberofpossibledetchars_goodat7.txt";
Ks := Keys(numberofpossibledetchars);
assert #Ks eq 109;
{* numberofpossibledetchars[i] : i in Ks *};
// {* 3^^4, 4^^105 *}

////////////////////////////////////////////////////////

load "nonsurj7.txt";
load "outputfiles/allcharsoutput.txt";
// load "outputfiles/allprimesdetstraces.txt";
load "outputfiles/numberofpossibledetchars.txt";
load "outputfiles/Nebentypus.txt";

Ks := Keys(numberofpossibledetchars);
assert #Ks eq 349;
assert Ks eq Keys(wt);
assert Ks eq Keys(allprimesdetstraces);
Ks := Sort(Setseq(Ks));

{* numberofpossibledetchars[i] : i in Ks *};
// {* 3^^11, 4^^338 *}
{* wt[i] : i in Ks *};
/*
{*
{* 0, 4 *}^^93,
{* 1, 3 *}^^70,
{* 2^^2 *}^^119,
{* 5^^2 *}^^67
*}
*/

badinds := Sort(Setseq({1..381} diff Ks)); badinds;
// [ 71, 89, 102, 129, 135, 154, 162, 175, 199, 204, 207, 234, 241, 260, 282, 288, 290, 293, 307, 310, 316, 321, 324, 330, 352, 353, 362, 363, 367, 371, 372, 380 ]

goodat7inds := [i : i in [1..#conds] | conds[i] mod 7 ne 0];
assert #goodat7inds eq 109;
assert Set(goodat7inds) meet Set(badinds) eq {};
{* wt[i] : i in goodat7inds *};
/*
{*
{* 1, 3 *}^^18,
{* 2^^2 *}^^91
*}
*/

possibly_fully_reducible_ss := [i : i in [1..#Allpossiblesubsetsofchars] | #Allpossiblesubsetsofchars[i] eq 3];
assert #possibly_fully_reducible_ss eq 28;
assert Set(possibly_fully_reducible_ss) meet Set(badinds) eq {};
{* wt[i] : i in possibly_fully_reducible_ss *};
/*
{*
{* 0, 4 *}^^12,
{* 1, 3 *}^^8,
{* 2^^2 *}^^6,
{* 5^^2 *}^^2
*}
*/


Ks_pllwt := Keys(NebentypusField);
assert Ks_pllwt eq Keys(orderofNebentypus);
Ks_pllwt := Sort(Setseq(Ks_pllwt));
assert #Ks_pllwt eq 186;
Ks_pllwt;
// [ 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 17, 18, 19, 20, 21, 23, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 43, 45, 46, 47, 48, 50, 51, 53, 55, 56, 58, 59, 62, 63, 64, 65, 66, 68, 69, 70, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 84, 86, 87, 90, 91, 93, 94, 96, 97, 98, 100, 101, 106, 107, 108, 110, 113, 114, 116, 118, 121, 122, 123, 124, 126, 127, 130, 132, 133, 136, 137, 139, 140, 143, 145, 146, 147, 149, 150, 153, 156, 159, 161, 163, 165, 166, 170, 172, 173, 174, 177, 178, 181, 187, 188, 189, 190, 191, 192, 194, 195, 197, 198, 201, 202, 203, 205, 206, 211, 212, 214, 216, 222, 224, 225, 226, 229, 233, 235, 236, 237, 238, 239, 243, 245, 247, 249, 251, 254, 256, 268, 269, 279, 281, 286, 291, 295, 300, 302, 308, 314, 317, 322, 323, 333, 334, 336, 343, 346, 348, 349, 354, 355, 358, 365, 370, 373, 375, 376, 378 ]

////////////////////////////////////////////////////////

{* orderofNebentypus[i] : i in Ks_pllwt *};
// {* 1^^6, 2^^5, 3^^110, 6^^65 *}
inds1 := [i : i in Ks_pllwt | orderofNebentypus[i] eq 1]; inds1;
// [ 6, 11, 30, 87, 188, 373 ]
assert {* NebentypusField[i] : i in inds1 *} eq {*Polynomial([1,1,1])^^6*};
{* orderofNebentypus[i] : i in Ks_pllwt | wt[i] eq {*2^^2*} *};
// {* 1^^4, 2^^2, 3^^60, 6^^53 *}
[i : i in Ks_pllwt | orderofNebentypus[i] eq 1 and wt[i] eq {*2^^2*}];
// [ 6, 11, 87, 188 ]

inds2 := [i : i in Ks_pllwt | orderofNebentypus[i] eq 2]; inds2;
// [ 2, 82, 86, 143, 370 ]
{* NebentypusField[i] : i in inds2 *};
/*
{*
($.1^2 + zeta_3)^^5
*}
*/

for i in inds1 cat inds2 do
    fil := Sprintf("outputfiles/primesdetstraces_%othcurve.txt", i);
    out := Sprintf("primesdetstraces := %m;\n", allprimesdetstraces[i]);
    PrintFile(fil, out);
end for;

/////////////

for i in inds1 cat inds2 do
    printf "%o:%o:%o:%o\n%o\n\n", i, allGalpairinds[i], allpairinds[i], allconjdualinds[i], Allpossiblesubsetsofchars[i];
end for;
/*
6:[ <1, 1>, <2, 4>, <3, 3> ]:[ <1, 3>, <2, 4> ]:[ 2, 4 ]
[ [*
<{* 1^^2, 3^^2 *}, 0>,
<{* 2, 4 *}, 1>
*] ]

11:[ <1, 1>, <2, 4>, <3, 3> ]:[ <1, 3>, <2, 4> ]:[ 2, 4 ]
[ [*
<{* 1^^2, 3^^2 *}, 0>,
<{* 2, 4 *}, 1>
*] ]

30:[ <1, 4>, <2, 5>, <3, 6> ]:[ <1, 4>, <2, 6>, <3, 5> ]:[ 1, 4 ]
[ [*
<{* 1, 4 *}, 1>,
<{* 2, 3, 5, 6 *}, 0>
*] ]

87:[ <1, 1>, <2, 2>, <3, 4> ]:[ <1, 2>, <3, 4> ]:[ 3, 4 ]
[ [*
<{* 1^^2, 2^^2 *}, 0>,
<{* 3, 4 *}, 1>
*], [*
<{* 1^^2, 2^^2 *}, 1>,
<{* 3, 4 *}, 0>
*], [*
<{* 1^^2, 2^^2 *}, 1>,
<{* 3, 4 *}, 1>
*] ]

188:[ <1, 1>, <2, 3>, <4, 4> ]:[ <1, 4>, <2, 3> ]:[ 2, 3 ]
[ [*
<{* 1^^2, 4^^2 *}, 0>,
<{* 2, 3 *}, 1>
*] ]

373:[ <1, 4>, <2, 3>, <5, 6> ]:[ <1, 5>, <2, 3>, <4, 6> ]:[ 2, 3 ]
[ [*
<{* 2, 3 *}, 1>,
<{* 1, 4, 5, 6 *}, 0>
*] ]

2:[ <1, 2>, <3, 6>, <4, 5> ]:[ <1, 2>, <3, 5>, <4, 6> ]:[ 1, 2 ]
[ [*
<{* 1, 2 *}, 1>,
<{* 3, 4, 5, 6 *}, 0>
*] ]

82:[ <1, 4>, <2, 5>, <3, 6> ]:[ <1, 4>, <2, 6>, <3, 5> ]:[ 1, 4 ]
[ [*
<{* 1, 4 *}, 1>,
<{* 2, 3, 5, 6 *}, 0>
*] ]

86:[ <1, 5>, <2, 4>, <3, 6> ]:[ <1, 5>, <2, 6>, <3, 4> ]:[ 1, 5 ]
[ [*
<{* 1, 5 *}, 1>,
<{* 2, 3, 4, 6 *}, 0>
*] ]

143:[ <1, 6>, <2, 3>, <4, 5> ]:[ <1, 3>, <2, 6>, <4, 5> ]:[ 4, 5 ]
[ [*
<{* 4, 5 *}, 1>,
<{* 1, 2, 3, 6 *}, 0>
*] ]

370:[ <1, 5>, <2, 6>, <3, 4> ]:[ <1, 5>, <2, 3>, <4, 6> ]:[ 1, 5 ]
[ [*
<{* 1, 5 *}, 0>,
<{* 2, 3, 4, 6 *}, 1>
*], [*
<{* 1, 5 *}, 1>,
<{* 2, 3, 4, 6 *}, 0>
*], [*
<{* 1, 5 *}, 1>,
<{* 2, 3, 4, 6 *}, 1>
*] ]

*/

////////////////////////////////////////////////////////

i := 370;
P<x> := PolynomialRing(QQ);
f := P!curves[i]; f;
// 1701*x^4 + 1792*x^3 - 2142*x^2 - 1512*x + 945
ell := 7;
F<zeta3> := CyclotomicField(3);
OF := RingOfIntegers(F);
K<zeta6> := CyclotomicField(ell-1);
chars := [*HeckeCharacter((F!condgens[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals[i][j]*]) : j in [1..#vals[i]] *];
assert {Norm(Conductor(x)) mod 7 : x in chars} eq {0};
[Order(x) : x in chars];
// [ 6, 2, 6, 6, 6, 2 ]
Ls := [AbsoluteField(NumberField(AbelianExtension(x))) : x in chars | Order(x) eq 2]; Ls;
/*
[
Number Field with defining polynomial x^4 - 5*x^2 + 7 over the Rational Field,
Number Field with defining polynomial x^4 - 5*x^2 + 7 over the Rational Field
]
// They are the fields 4.0.1008.1
*/
