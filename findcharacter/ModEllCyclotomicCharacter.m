intrinsic ModEllCyclotomicCharacter(F :: Fld, ell :: RngIntElt : B := 10^Degree(F), K := Rationals(), lambda := 0) -> GrpHeckeElt, RngOrdIdl
{return a Hecke character over F valued in K=Q(zeta_(ell-1)), and a choice of a prime lambda in K above ell,
so that the mod-lambda reduction is the mod-ell cyclotomic character}
    OF := RingOfIntegers(F);
    firstnprimes := [pp : pp in PrimesUpTo(B,F) | Minimum(pp) ne ell];
    norms := [Norm(pp) : pp in firstnprimes];
    normsmodell := [x mod ell : x in norms];
    if lambda cmpeq 0 then
        K<zeta> := CyclotomicField(ell-1);
        lambda := PrimeIdealsOverPrime(K,ell)[1];
    end if;
    // OK := RingOfIntegers(K);
    Fell, OKtoFell := ResidueClassField(lambda);
    G := HeckeCharacterGroup(ell*OF : Target := K);
    A, AtoG := AbelianGroup(G);
    assert exists(chi_ell){AtoG(x) : x in A | [OKtoFell((AtoG(x))(pp)) : pp in firstnprimes] eq normsmodell};
    assert chi_ell eq AssociatedPrimitiveCharacter(chi_ell);
    return chi_ell, lambda;
end intrinsic;
