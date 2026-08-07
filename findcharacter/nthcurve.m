load "nonsurj7.txt";

n := 1; condexpsC := [12,9,2];

primes := [2,3,5,7];
condC := &*[primes[i]^condexpsC[i] : i in [1..#condexpsC]];
sqfree, sqrtint := Squarefree(condC);

coe := curves[n];
P<x> := PolynomialRing(Rationals());
f := P!coe;
// f := x^4+160*x^2-512*x+3328
ChangeDirectory("final");
AttachSpec("spec");
ell := 7;
chars, rootsofLpols1 := find_onedimchar(f,ell);
ramchars, rootsofLpols2 := find_onedimchar(f,ell : ramified := true);
assert rootsofLpols1 eq rootsofLpols2;
assert #chars eq 2;
conds := [Conductor(x`char) : x in chars];
conds_fac := [Factorisation(x) : x in conds];

// verification
[[AssociatedPrimitiveCharacter(x`char) eq AssociatedPrimitiveCharacter(y`char) : y in ramchars] : x in chars];
// verification
[Norm(Conductor(y`char)) mod ell eq 0 : y in ramchars];
// verification
OF := Order(Modulus(Parent(ramchars[1]`char)));
K_targ := TargetRing(Parent(ramchars[1]`char));
OK_targ := RingOfIntegers(K_targ);
ellabove := PrimeIdealsOverPrime(K_targ,ell);
OK_targ_modell, resmodell := ResidueClassField(OK_targ,ellabove[1]);
{*{*resmodell((x`char)(pfrak)) : x in ramchars*} eq y[2] where pfrak is Factorisation(y[1]*OF)[1,1] : y in rootsofLpols2*};

/*
// verification // the two related and ramified at ell characters are Galois conjugate
beta := ramchars[4]`char;
betac := ramchars[6]`char;
AssociatedPrimitiveCharacter(beta*betac) eq AssociatedPrimitiveCharacter(ramchars[1]`char*ramchars[3]`char);
{*{*resmodell((beta)(q[1])) : q in pfac*} eq {*resmodell((betac)(q[1])) : q in pfac*} where pfac is Factorisation(p*OF) : p in PrimesUpTo(1000) | p mod 3 eq 1*};
*/

/*
cond_eps1_lowerbound := conds[1];
goodlevelbound := sqrtint/cond_eps1_lowerbound; Factorisation(goodlevelbound);
relaxedlevelbound := (sqfree*sqrtint)/cond_eps1_lowerbound; Factorisation(relaxedlevelbound);
*/

OK := Order(conds[1]);

/*
strictlevelnormbound := Norm(ideal<OK|sqrtint>/conds[1]);
strictSengunlevelnormbound := Norm(ideal<OK|ell>)*strictlevelnormbound;
strictSengunlevelnormbound, Factorisation(strictSengunlevelnormbound);
*/

condC_fac := Factorisation(ideal<OK|condC>);
levelnormbound := Norm(&*[x[1]^(x[2] div 2) : x in condC_fac]/conds[1]);
Sengunlevelnormbound := Norm(ideal<OK|ell>)*levelnormbound;
Sengunlevelnormbound, Factorisation(Sengunlevelnormbound);

