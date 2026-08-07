f := x^4+160*x^2-512*x+3328;
ChangeDirectory("final");
AttachSpec("spec");

ell := 7;
chars, rootsofLpols1 := find_onedimchar(f,ell);
ramchars, rootsofLpols2 := find_onedimchar(f,ell : ramified := true);
assert rootsofLpols1 eq rootsofLpols2;
assert #chars eq 2;

// verification
[[AssociatedPrimitiveCharacter(x`char) eq AssociatedPrimitiveCharacter(y`char) : y in ramchars] : x in chars];
// verification
[Norm(Conductor(y`char)) mod ell eq 0 : y in ramchars];
[Norm(Conductor(y`char)) mod ell^2 eq 0 : y in ramchars];
// verification
OF := Order(Modulus(Parent(ramchars[1]`char)));
K_targ := TargetRing(Parent(ramchars[1]`char));
OK_targ := RingOfIntegers(K_targ);
ellabove := PrimeIdealsOverPrime(K_targ,ell);
OK_targ_modell, resmodell := ResidueClassField(OK_targ,ellabove[1]);
{*{*resmodell((x`char)(pfrak)) : x in ramchars*} eq y[2] where pfrak is Factorisation(y[1]*OF)[1,1] : y in rootsofLpols2*};

