// uselambdacharpols := false, noskip := true, Hecke_stricteval := true
intrinsic find_trace(f :: RngUPolElt, ell :: RngIntElt, epsillon1 :: GrpHeckeElt, det :: GrpHeckeElt : radical_cond := 1, charpols := [], primes_bound := 500, ramified := true, useinertFrobsq := true) -> SeqEnum
{returns list of traces and determinants of the two dimensional subrepresentation of the Galois group of K=Q(zeta_3) 
in the mod-ell Galois representation of the Jacobian of the curve y^3 = f(x) above various primes.}
    // From find_onedimchar
    SetColumns(0);
    Z := Integers();
    P_ell<T> := PolynomialRing(GF(ell));
    f := suppressed_integer_quartic(f);
    if radical_cond eq 1 then radical_cond := RadCond(f); end if;
    if ramified then
        radical_cond := (radical_cond mod ell eq 0) select radical_cond else ell*radical_cond;
    else
        radical_cond := radical_cond div ell^Valuation(radical_cond,ell);
    end if;
    cond := radical_cond^4;
    F<zeta3> := CyclotomicField(3);
    OF := RingOfIntegers(F);
    P_F<xF> := PolynomialRing(OF);
    ellaboveF := PrimeIdealsOverPrime(F,ell);
    OFmodell1, resF1 := ResidueClassField(OF,ellaboveF[1]);
    OFmodell2, resF2 := ResidueClassField(OF,ellaboveF[2]);
    G := HeckeCharacterGroup(cond*OF);
    K_targ := (ell mod 3 eq 1) select CyclotomicField(ell-1) else CyclotomicField(ell^2-1);
    G := TargetRestriction(G,K_targ);
    OK_targ := RingOfIntegers(K_targ);
    ellabove := PrimeIdealsOverPrime(K_targ,ell);
    OK_targ_modell, resmodell := ResidueClassField(OK_targ,ellabove[1]);

    if charpols eq [] then
        charpols := getcharpols(f : primesend := primes_bound);
    end if;
    // printf "Charpols found at primes:\n%o\n", [x[1] : x in charpols];
    if useinertFrobsq then
        // using Bracket-2 of charpols at inert primes.
        charpols := [(x[1] mod 3 eq 1) select x else <x[1],Bracket(2,x[2])> : x in charpols | x[1] ne 3 and x[1] ne ell];
    else
        charpols := [x : x in charpols | x[1] mod 3 eq 1 and x[1] ne ell];
        // printf "Throwing away ell and inert primes. Retained:\n%o\n", [x[1] : x in charpols];
    end if;
    charpolsmodell := [<x[1],P_ell ! x[2]> : x in charpols];

    primes := [x[1] : x in charpolsmodell];
    // printf "\nUsing L-polynomials at the (ordinary) primes\n%o\n\n", primes;
    // print charpolsmodell;

    gens_G := Setseq(Generators(G));
    n := #gens_G;
    exps_G := [Order(chi) : chi in gens_G];
    conds_G := [Conductor(chi) : chi in gens_G];
    // printf "Orders of the characters generating the Hecke character group:\n%o\n", exps_G;
    // printf "Orders and conductors of the characters generating the Hecke character group:\n%o\n%o\n", exps_G, conds_G;


/*
    // Method 1
    primes_dets_traces := [];
    for ind in [1..#charpolsmodell] do
        p := charpolsmodell[ind, 1];

        if cond mod p eq 0 then continue; end if;

        pabove := PrimeIdealsOverPrime(F, p);
        epsillon1_atpabove := resmodell(onedimchar(pabove[1]));
        det_atpabove := resmodell(det(pabove[1]));
        pp := P_ell!p;
        charpol := charpolsmodell[ind, 2];
        pabove := PrimeIdealsOverPrime(F, p);
        coeff := Coefficient(charpol, 5);
        denom := 1 + pp * det_atpabove^-1;
        if denom ne 0 then
            trace := -(coeff + epsillon1_atpabove + p * epsillon1_atpabove^-1)/denom;
            Append(~primes_dets_traces, <p, det_atpabove, trace>);
        else
            Append(~primes_dets_traces, <p, det_atpabove, "no trace">)
        end if;
    end for;

*/

    //Method 2
    primes_dets_traces := [];
    for ind in [1..#charpolsmodell] do
        p := charpolsmodell[ind, 1];

        if cond mod p eq 0 then continue; end if;
  
        pabove := PrimeIdealsOverPrime(F, p);
        epsillon1_atpabove := resmodell(epsillon1(pabove[1]));
        det_atpabove := resmodell(det(pabove[1]));
        pp := P_ell!Norm(pabove[1]);

        charpol := charpolsmodell[ind, 2];
        charpolfacs := Roots(charpol, GF(ell, 2));
        all_roots := [];
        for r in charpolfacs do
	        for i := 1 to r[2] do
 	            Append(~all_roots, r[1]);
            end for;
	    end for;
        assert #all_roots eq 6;

        // print p, all_roots, epsillon1_atpabove, pp/epsillon1_atpabove;
        index := Index(all_roots, epsillon1_atpabove);
        assert index ne 0;
        Remove(~all_roots, index);
        index := Index(all_roots, pp/epsillon1_atpabove);
        assert index ne 0;
        Remove(~all_roots, index);

        possible_traces_atp := {};
        for i in [1..(#all_roots-1)] do
            for j in [(i+1)..#all_roots] do
                if all_roots[i]*all_roots[j] eq det_atpabove then
                    Include(~possible_traces_atp, all_roots[i] + all_roots[j]);
                end if;
            end for;
        end for;

        Append(~primes_dets_traces, <p, det_atpabove, Setseq(possible_traces_atp)>);
    end for;

    return primes_dets_traces;

end intrinsic;

