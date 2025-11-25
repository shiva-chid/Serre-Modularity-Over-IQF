coe := [ -7, 36, -48, 8, 12 ];
P<x> := PolynomialRing(Rationals());
f := P!coe;
ChangeDirectory("final");
GetCurrentDirectory();
AttachSpec("spec");
ell := 7;
chars, charvals := find_onedimchar(f,ell);
assert #chars eq 2;
conds := [Conductor(x`char) : x in chars];
conds_fac := [Factorisation(x) : x in conds];
conds_fac;
/*
[
[
<Prime Ideal
Two element generators:
[3, 0]
[2, 1], 3>,
<Principal Prime Ideal
Generator:
[2, 0], 3>
],
[
<Prime Ideal
Two element generators:
[3, 0]
[2, 1], 3>,
<Principal Prime Ideal
Generator:
[2, 0], 3>
]
]
*/

cond_eps1_lowerbound := 2^3*3;
condC := 2^14*3^13;
sqfree, sqrtint := Squarefree(condC);
goodlevelbound := sqrtint/cond_eps1_lowerbound; Factorisation(goodlevelbound);
relaxedlevelbound := (sqfree*sqrtint)/cond_eps1_lowerbound; Factorisation(relaxedlevelbound);

OK := Order(conds[1]);
relaxedlevelnormbound := Norm(ideal<OK|sqfree*sqrtint>/conds[1]); relaxedlevelnormbound;
goodlevelnormbound := Norm(ideal<OK|sqrtint>/conds[1]); goodlevelnormbound;

Sengunbound := ell*goodlevelbound; Sengunbound;
Sengunlevelnormbound := Norm(ideal<OK|ell>)*goodlevelnormbound; Sengunlevelnormbound;

