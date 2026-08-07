intrinsic pairup(L :: List, ell :: RngIntElt : chi_ell := 0) -> List
{Given a list containing an even number of Hecke characters valued in F_ell
pair them up so that the product of each pair is the mod-ell cyclotomic character,
and return the list of pairs, and their indices in the given list}
    require #L mod 2 eq 0 : "List must have even number of elements";
    if chi_ell cmpeq 0 then
        F<zeta3> := CyclotomicField(3);
        chi_ell, lambda := ModEllCyclotomicCharacter(F,ell);
    end if;

    pairs := [**];
    pairindices := [];
    doneindices := [];
    for i in [1..#L] do
        if i in doneindices then continue; end if;
        chi1 := L[i];
        for j in [i+1..#L] do
            if j in doneindices then continue; end if;
            chi2 := L[j];
            if AssociatedPrimitiveCharacter(chi1*chi2) eq chi_ell then
                Append(~pairs,<chi1,chi2>);
                Append(~pairindices,<i,j>);
                doneindices := doneindices cat [i,j];
                continue i;
            end if;
        end for;
        printf "Dual of %oth character in the list does not exist in the list.\n", i;
        return false;
    end for;
    assert Set(doneindices) eq {1..#L};
    return pairs, pairindices;
end intrinsic;


intrinsic isconjugatethedual(epsilon :: GrpHeckeElt, ell :: RngIntElt : chi_ell := 0, lambda := 0, n := 100) -> BoolElt
{for a Hecke character over a quadratic number field, returns whether its product with its Galois conjugate
is equal to the mod-ell cyclotomic character chi_ell}
    modulus := Modulus(epsilon);
    OF := Order(modulus);
    F := NumberField(OF);
    K := TargetRing(epsilon);
    if chi_ell cmpeq 0 then
        chi_ell, lambda := ModEllCyclotomicCharacter(F,ell);
    end if;
    Fell, OKtoFell := ResidueClassField(lambda);
    

    firstnprimes := [p : p in PrimesUpTo(n) | not p in {3,ell}];
    chi_ell_vals := AssociativeArray();
    for p in firstnprimes do
        chi_ell_vals[p] := (p mod 3 eq 1) select p mod ell else p^2 mod ell;
    end for;
    chi_ell_allvals := [[OKtoFell(chi_ell(pp)) : pp in PrimeIdealsOverPrime(F,p)] : p in firstnprimes];
    assert [chi_ell_vals[p] : p in firstnprimes] eq [x[1] : x in chi_ell_allvals];

    for p in firstnprimes do
        if GCD(Norm(modulus),p) ne 1 then continue; end if;
        paboveF := PrimeIdealsOverPrime(F,p);
        if #paboveF eq 1 then paboveF := paboveF cat paboveF; end if;
        prodval := &*[OKtoFell((epsilon)(pp)) : pp in paboveF];
        if prodval ne chi_ell_vals[p] then return false; end if;
    end for;
    return true;
end intrinsic;