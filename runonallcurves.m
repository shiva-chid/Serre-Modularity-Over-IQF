load "nonsurj7.txt";
AttachSpec("spec");

ell := 7;
P<x> := PolynomialRing(Rationals());
NumberOfUnramifiedatellChars := [];
NumberOfPossiblyramifiedatellChars := [];
out1 := [];
out2 := [];
for coe in curves do
    f := P!coe;
    unramchars, rootsofLpols1 := find_onedimchar(f,ell);
    Append(~NumberOfUnramifiedatellChars, #unramchars);
    Append(~out1,unramchars);
    ramchars, rootsofLpols2 := find_onedimchar(f,ell : ramified := true);
    Append(~NumberOfPossiblyramifiedatellChars, #ramchars);
    Append(~out2,ramchars);
    assert rootsofLpols1 eq rootsofLpols2;
end for;
// sanity check: verifying that unramchars is a subset of ramchars
assert &and[NumberOfUnramifiedatellChars[i] le NumberOfPossiblyramifiedatellChars[i] : i in [1..#curves]];
for i in [1..#curves] do
    for x in out1[i] do
        assert exists(y){y : y in out2[i] | AssociatedPrimitiveCharacter(x`char) eq AssociatedPrimitiveCharacter(y`char)};
        // assert exists(y){y : y in out2[i] | &and[(x`values_modell)[k] eq (y`values_modell)[k] : k in Keys(x`values_modell)]};
    end for;
    printf "%o ", i;
end for;
// sanity check passed
// for more checks, see verify_pairup.m and verify_pairup.log

F<zeta3> := CyclotomicField(3);
OF := RingOfIntegers(F);
primegens := [gen where _,gen is IsPrincipal(pp) : pp in PrimesUpTo(1000,F)];
K := CyclotomicField(ell-1);

// printing the results to file
allchars := [[*AssociatedPrimitiveCharacter(x`char) : x in y*] : y in out2];
conds := [[* Conductor(x) : x in y *] : y in allchars];
condgens := [[Eltseq(gen) where _,gen is IsPrincipal(x) : x in y] : y in conds];
vals := [[[*<Eltseq(pp),Eltseq(K!(allchars[i][j](pp)))> : pp in primegens | not conds[i][j] subset pp*OF *] : j in [1..#allchars[i]]] : i in [1..#allchars]];
// {*{*{#val[2] : val in x} : x in y*} : y in vals*};
fil := "allcharsoutput.txt";
fil1 := "allcharsoutput1.txt";
PrintFile(fil, "condgens := ");
PrintFile(fil, condgens);
PrintFile(fil, ";");
PrintFile(fil, "vals := ");
PrintFile(fil, vals);
PrintFile(fil, ";");

/*
to recover the characters from file

load "allcharsoutput.txt";
F<zeta3> := CyclotomicField(3);
OF := RingOfIntegers(F);
K<zeta6> := CyclotomicField(6);

recoveredchars := [[*HeckeCharacter((F!condgens[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals[i][j]*]) : j in [1..#vals[i]] *] : i in [1..#vals]];
// takes a while (~1h) to rebuild all the characters from the stored values.

for i := 1 to #recoveredchars do
    for j := 1 to #recoveredchars[i] do
        assert recoveredchars[i][j] eq allchars[i][j];
    end for;
end for;
*/

////////////////////////////////

// Analysis of results

K<zeta3> := CyclotomicField(3);
AutKQ, auts, tau := AutomorphismGroup(K);
sigma := tau(AutKQ.1);
OK := RingOfIntegers(K);

#NumberOfUnramifiedatellChars;
// 381
NumberOfUnramifiedatellChars;
// [ 2, 2, 2, 0, 2, 1, 0, 2, 2, 0, 1, 2, 2, 2, 0, 0, 2, 2, 0, 2, 2, 0, 2, 2, 0, 0, 2, 2, 0, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 2, 0, 0, 2, 2, 0, 2, 0, 2, 2, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 0, 2, 0, 0, 0, 2, 2, 0, 0, 0, 2, 2, 2, 2, 2, 0, 0, 2, 0, 0, 1, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 1, 0, 2, 0, 2, 0, 2, 0, 0, 0, 2, 0, 0, 2, 2, 2, 0, 2, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 2, 0, 0, 0, 0, 0, 2, 0, 2, 2, 2, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 2, 0, 0, 0, 0, 2, 2, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 2, 0, 0, 0 ]
{*x : x in NumberOfUnramifiedatellChars*};
// {* 0^^265, 1^^4, 2^^112 *}

inds0 := [i : i in [1..#NumberOfUnramifiedatellChars] | NumberOfUnramifiedatellChars[i] eq 0]; inds0;
// [ 4, 7, 10, 15, 16, 19, 22, 25, 26, 29, 30, 31, 33, 35, 37, 38, 39, 41, 43, 44, 46, 48, 49, 52, 54, 57, 58, 59, 60, 61, 67, 69, 70, 71, 74, 75, 76, 82, 83, 85, 86, 88, 89, 90, 92, 94, 95, 97, 99, 101, 102, 103, 104, 105, 106, 107, 109, 111, 112, 113, 115, 116, 117, 119, 120, 121, 122, 123, 125, 127, 128, 129, 131, 132, 134, 135, 137, 138, 140, 141, 142, 144, 145, 147, 148, 151, 152, 153, 154, 155, 156, 157, 158, 160, 162, 163, 164, 165, 167, 168, 169, 171, 175, 176, 177, 179, 180, 182, 183, 184, 185, 186, 187, 189, 191, 193, 195, 196, 197, 199, 200, 204, 206, 207, 208, 209, 210, 213, 214, 215, 217, 218, 219, 220, 221, 222, 223, 225, 227, 228, 230, 231, 232, 233, 234, 236, 240, 241, 242, 243, 244, 245, 246, 248, 250, 251, 252, 253, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 270, 271, 272, 273, 274, 275, 276, 277, 278, 280, 281, 282, 283, 284, 285, 287, 288, 289, 290, 292, 293, 294, 295, 296, 297, 298, 299, 301, 303, 304, 305, 306, 307, 309, 310, 311, 312, 313, 314, 315, 316, 318, 319, 320, 321, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 335, 336, 337, 338, 339, 340, 341, 342, 344, 345, 346, 347, 350, 351, 352, 353, 356, 357, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 377, 379, 380, 381 ]
inds1 := [i : i in [1..#NumberOfUnramifiedatellChars] | NumberOfUnramifiedatellChars[i] eq 1]; inds1;
// [ 6, 11, 87, 188 ]
inds2 := [i : i in [1..#NumberOfUnramifiedatellChars] | NumberOfUnramifiedatellChars[i] eq 2]; inds2;
// [ 1, 2, 3, 5, 8, 9, 12, 13, 14, 17, 18, 20, 21, 23, 24, 27, 28, 32, 34, 36, 40, 42, 45, 47, 50, 51, 53, 55, 56, 62, 63, 64, 65, 66, 68, 72, 73, 77, 78, 79, 80, 81, 84, 91, 93, 96, 98, 100, 108, 110, 114, 118, 124, 126, 130, 133, 136, 139, 143, 146, 149, 150, 159, 161, 166, 170, 172, 173, 174, 178, 181, 190, 192, 194, 198, 201, 202, 203, 205, 211, 212, 216, 224, 226, 229, 235, 237, 238, 239, 247, 249, 254, 268, 269, 279, 286, 291, 300, 302, 308, 317, 322, 333, 334, 343, 348, 349, 354, 355, 358, 376, 378 ]

curves[inds1];
/*
[
[ 0, 2, 42, 289, 648 ],
[ -7, 36, -48, 8, 12 ],
[ 1, 15, 129, 557, 1458 ],
[ -4, -28, 126, 550, 625 ]
]
*/
NumberOfUnramifiedatellChars[inds1];
// [ 1, 1, 1, 1 ]
conds1 := [[Conductor(x`char) : x in out1[ii]] : ii in inds1];
assert {* #x : x in conds1 *} eq {* 1^^4 *};
conds1 := [x[1] : x in conds1];
[Norm(x) : x in conds1];
// [ 1, 1728, 1, 10800 ]
assert conds1[2] eq 24*(1-zeta3)*OK;
assert conds1[4] eq 60*(1-zeta3)*OK;


conds2 := [[Conductor(x`char) : x in out1[ii]] : ii in inds2];
assert {* #x : x in conds2 *} eq {* 2^^112 *};
assert &and[#Set(x) eq 1 : x in conds2];


// Verifying Galois conjugacy of the obtained characters
for ii := 1 to #curves do
    f := P!curves[ii];
    // n := NumberOfUnramifiedatellChars[ii];
    // chars, rootsofLpols1 := find_onedimchar(f,ell : primes_bound := 2000);
    n := NumberOfPossiblyramifiedatellChars[ii];
    chars, rootsofLpols1 := find_onedimchar(f,ell : ramified := true, primes_bound := 2000);
    assert #chars eq n;
    if n eq 0 then continue; end if;
    conds := [Conductor(x`char) : x in chars];
    sigmaconds := [sigma(x) : x in conds];
    assert Set(sigmaconds) eq Set(conds);
    // charvals := {{<k,(x`values_modell)[k]> : k in Keys(x`values_modell)} : x in chars};
    // sigmacharvals := {{<sigma(k),(sigma(x`values_modell))[k]> : k in Keys(x`values_modell)} : x in chars};
    // assert sigmacharvals eq charvals;
    charvals := [[<p, [(x`char)(pp) : pp in PrimeIdealsOverPrime(K,p)]> : p in PrimesInInterval(11,1000)] : x in chars];
    sigmacharvals := [[<x[1], Reverse(x[2])> : x in L] : L in charvals];
    assert Set(sigmacharvals) eq Set(charvals);
    printf "%o ", ii;
end for;


////////////////////////////////

NumberOfPossiblyramifiedatellChars;
// [ 6, 6, 6, 6, 6, 4, 6, 6, 6, 6, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 4, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 8, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6, 6 ]
{*x : x in NumberOfPossiblyramifiedatellChars*};
// {* 4^^4, 6^^376, 8 *}
[i : i in [1..#NumberOfPossiblyramifiedatellChars] | NumberOfPossiblyramifiedatellChars[i] eq 4];
// [ 6, 11, 87, 188 ]
$1 eq inds1;

[i : i in [1..#NumberOfPossiblyramifiedatellChars] | NumberOfPossiblyramifiedatellChars[i] eq 8];
// [ 207 ]
curves[$1];
// [ [ 588, 504, -396, 36, 27 ] ]
f := P!curves[207];
chars, rootsofLpols1 := find_onedimchar(f,ell : primes_bound := 5000);
ramchars, rootsofLpols2 := find_onedimchar(f,ell : ramified := true, primes_bound := 5000);
// still 8 possibilities
