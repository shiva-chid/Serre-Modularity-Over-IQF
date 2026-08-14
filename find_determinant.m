intrinsic find_determinant(f :: RngUPolElt, ell :: RngIntElt, epsilon :: GrpHeckeElt : radical_cond := 1, primes_bound := 500, charpols := [], ramified := true, useinertFrobsq := true, finddetpair := false) -> SeqEnum
{returns list of characters of the Galois group of K=Q(zeta_3) that can possibly occur as the 
determinant of a 2-dimensional subquotient representation in the mod-ell Galois representation 
of the Jacobian of the curve y^3 = f(x) over K.}
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

    if finddetpair then
        X := Set(CartesianProduct([[0..e-1] : e in exps_G] cat [[0..e-1] : e in exps_G]));
    else
        X := Set(CartesianProduct([[0..e-1] : e in exps_G]));
    end if;
    ind := 1;
    prime_ideals := [];
    number_linearfacs := 6;
    all_roots_charpolsmodell := [];



    while #X gt 0 do
        if ind gt #charpolsmodell then
            // printf "Checked %o primes, up to %o\n", #charpolsmodell, charpolsmodell[#charpolsmodell];
            break;
        end if;
        p := charpolsmodell[ind,1];
        charpol := charpolsmodell[ind,2];
        pabove := PrimeIdealsOverPrime(F,p);
        Append(~prime_ideals,pabove);
        pp := P_ell!Norm(pabove[1]);

        if cond mod p eq 0 then ind := ind+1; continue; end if;

        roots_charpol := Roots(charpol, GF(ell, 2));
        if #roots_charpol eq 0 then
            printf "Witness: p = %o, Frob_p charpol mod %o = %o has no roots\n", p, ell, charpol;
            return [], [];
        end if;
        eigvals_rhoell_frobp := {*r[1]^^r[2] : r in roots_charpol*};
        assert #eigvals_rhoell_frobp eq 6;
        Append(~all_roots_charpolsmodell, <p,eigvals_rhoell_frobp>);
        eigvals_rhoell_frobp := MultisetToSequence(eigvals_rhoell_frobp);
        assert #eigvals_rhoell_frobp eq 6;

        // printf "Charpol %o at p=%o has roots %o over F_%o\n",charpol, p, roots_charpol, ell;
        gens_evalsatpabove := [[resmodell((gens_G[i])(frakp)) : i in [1..n]] : frakp in pabove];

        epsilon_atpabove := resmodell(epsilon(pabove[1]));
        // printf "the value of epsilon at %o is %o\n", p, epsilon_atpabove[1];
        // printf "the prime %o is %o in F_%o\n", p, P_ell!p, ell;


        index := Index(eigvals_rhoell_frobp, epsilon_atpabove);
        assert index ne 0;
	    Remove(~eigvals_rhoell_frobp, index);
        index := Index(eigvals_rhoell_frobp, pp * epsilon_atpabove^-1);
        assert index ne 0;
	    Remove(~eigvals_rhoell_frobp, index);
        assert #eigvals_rhoell_frobp eq 4;

        if finddetpair then
            indices := {1..4};
            subs2 := Setseq(Subsets(indices,2));
            possible_detpairs := [<&*[eigvals_rhoell_frobp[i] : i in sub2], &*[eigvals_rhoell_frobp[i] : i in indices diff sub2]> : sub2 in subs2];

            index := Index(possible_detpairs, <pp,pp>);
            assert index ne 0;
            Remove(~possible_detpairs, index);
            index := Index(possible_detpairs, <pp,pp>);
            assert index ne 0;
            Remove(~possible_detpairs, index);

            // printf "possible determinants: %o\n", possible_detpairs;
            assert #possible_detpairs eq 4;

            X := [xx : xx in X | <&*[gens_evalsatpabove[1][i]^(xx[i]) : i in [1..n]], &*[gens_evalsatpabove[1][i]^(xx[n+i]) : i in [1..n]]> in possible_detpairs];
            print p, #X;
        else
            possible_dets := [eigvals_rhoell_frobp[i] * eigvals_rhoell_frobp[j] : i in [1..#eigvals_rhoell_frobp], j in [1..#eigvals_rhoell_frobp] | i lt j];

            index := Index(possible_dets, pp);
            assert index ne 0;
            Remove(~possible_dets, index);
            index := Index(possible_dets, pp);
            assert index ne 0;
            Remove(~possible_dets, index);

            // printf "possible determinants: %o\n", possible_dets;
            assert #possible_dets eq 4;

            X := [x : x in X | &*[gens_evalsatpabove[1][i]^(x[i]) : i in [1..n]] in possible_dets];
            print p, #X;
        end if;

        number_linearfacs := Minimum(number_linearfacs,&+([] cat [r[2] : r in roots_charpol | r[1] in GF(ell)]));
        ind := ind+1;
    end while;

    if finddetpair then
        X_chars := [* <&*[(gens_G[i])^xx[i] : i in [1..n]], &*[(gens_G[i])^xx[n+i] : i in [1..n]]> : xx in X *];
        RF := recformat<char1 : GrpHeckeElt, char2 : GrpHeckeElt, values1_modell : Assoc, values2_modell : Assoc>;
        X_chars_values := [];
        for chipair in X_chars do
            chi1 := chipair[1];
            chi2 := chipair[2];
            chi1_values_modell := AssociativeArray();
            chi2_values_modell := AssociativeArray();
            for i := 1 to #prime_ideals do
                p := Norm(prime_ideals[i][1] meet Z);
                chi1_values_modell[p] := <resmodell((chi1)(frakp)) : frakp in prime_ideals[i]>;
                chi2_values_modell[p] := <resmodell((chi2)(frakp)) : frakp in prime_ideals[i]>;
            end for;
            Append(~X_chars_values,rec<RF | char1 := chi1, char2 := chi2, values1_modell := chi1_values_modell, values2_modell := chi2_values_modell>);
        end for;
    else
        X_chars := <&*[(gens_G[i])^x[i] : i in [1..n]] : x in X>;
        RF := recformat<char : GrpHeckeElt, values_modell : Assoc>;
        X_chars_values := [];
        for chi in X_chars do
            chi_values_modell := AssociativeArray();
            for i := 1 to #prime_ideals do
                p := Norm(prime_ideals[i][1] meet Z);
                chi_values_modell[p] := <resmodell((chi)(frakp)) : frakp in prime_ideals[i]>;
            end for;
            Append(~X_chars_values,rec<RF | char := chi, values_modell := chi_values_modell>);
        end for;
    end if;
    return X_chars_values;
end intrinsic;
