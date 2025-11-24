intrinsic find_determinant(g :: RngUPolElt, ell :: RngIntElt, epsillon1 :: GrpHeckeElt : primes_bound := 400, charpols := [], unramified := false, useinertFrobsq := true) -> SeqEnum
{returns list of characters of the Galois group of K=Q(zeta_3) that can
possibly occur as the determinant of a 2-d subrepresentation in the mod-ell Galois representation of the Jacobian of the curve y^3 = f(x).}


    // From find_onedimchar
    SetColumns(0);
    Z := Integers();
    P_ell<T> := PolynomialRing(GF(ell));
    f := suppressed_integer_quartic(g);
    radical_cond := RadCond(f);
    if not unramified then
        radical_cond := (radical_cond mod ell eq 0) select radical_cond else ell*radical_cond;
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

    if #charpols eq 0 then
        charpols := getcharpols(f : primesend := primes_bound);
    end if;

    // printf "Charpols found at primes:\n%o\n", [x[1] : x in charpols];
    if useinertFrobsq then
        // using Bracket-2 of charpols at inert primes.
        charpols := [(x[1] mod 3 eq 1) select x else <x[1],Bracket(2,x[2])> : x in charpols | x[1] ne 3 and x[1] ne ell];
    else
        charpols := [x : x in charpols | x[1] mod 3 eq 1 and x[1] ne ell];
    end if;
    // printf "Throwing away ell, and possibly inert primes. Retained:\n%o\n", [x[1] : x in charpols];

    charpolsmodell := [<x[1],P_ell ! x[2]> : x in charpols];

    primes := [x[1] : x in charpolsmodell];
    // printf "\nUsing L-polynomials at the (ordinary) primes\n%o\n\n", primes;

    gens_G := Setseq(Generators(G));
    n := #gens_G;
    exps_G := [Order(chi) : chi in gens_G];
    conds_G := [Conductor(chi) : chi in gens_G];
    // printf "Orders of the characters generating the Hecke character group:\n%o\n", exps_G;

    X := Set(CartesianProduct([[0..e-1] : e in exps_G]));
    ind := 1;
    prime_ideals := [];
    number_linearfacs := 6;
    all_roots_charpolsmodell := [];



    // TODO: This reduces the possible characters down to 2 possibilities ab and pa/b, get it down to just ab.
    while #X gt 0 do
        if ind gt #charpolsmodell then
            // printf "Checked %o primes, up to %o\n", #charpolsmodell, charpolsmodell[#charpolsmodell];
            break;
        end if;
        p := charpolsmodell[ind,1];
        pp := P_ell!p;
        charpol := charpolsmodell[ind,2];
        pabove := PrimeIdealsOverPrime(F,p);
        Append(~prime_ideals,pabove);

        if cond mod p eq 0 then ind := ind+1; continue; end if;

        roots_charpol := Roots(charpol, GF(ell, 2));
        if #roots_charpol eq 0 then
            printf "Witness: p = %o, Frob_p charpol mod %o = %o has no roots\n", p, ell, charpol;
            return [], [];
        end if;
        Append(~all_roots_charpolsmodell, <p,&join[{*r[1] : i in [1..r[2]]*} : r in roots_charpol]>);
        eigvals_rhoell_frobp := [];
	for r in roots_charpol do
	    for i := 1 to r[2] do
 	        Append(~eigvals_rhoell_frobp, r[1]);
            end for;
	end for;

        // printf "Charpol %o at p=%o has roots %o over F_%o\n",charpol, p, roots_charpol, ell;
        gens_evalsatpabove := [[resmodell((gens_G[i])(frakp)) : i in [1..n]] : frakp in pabove];

        epsillon1_atpabove := resmodell(epsillon1(pabove[1]));
        // printf "the value of epsillon_1 at %o is %o\n", p, epsillon1_atpabove[1];
        // printf "the prime %o is %o in F_%o\n", p, P_ell!p, ell;


        index := Index(eigvals_rhoell_frobp, epsillon1_atpabove);
	if index ne 0 then
	    Remove(~eigvals_rhoell_frobp, index);
	end if;
        index := Index(eigvals_rhoell_frobp, pp * epsillon1_atpabove^-1);
	if index ne 0 then
	    Remove(~eigvals_rhoell_frobp, index);
    else
        pp := pp * pp;
        index := Index(eigvals_rhoell_frobp, pp * epsillon1_atpabove^-1);
        if index ne 0 then
            Remove(~eigvals_rhoell_frobp, index);
        else
            printf "could not find any factors %o or %o. Investigate further\n", P_ell!p/epsillon1_atpabove, pp/epsillon1_atpabove;
        end if;
	end if;

        possible_dets := [eigvals_rhoell_frobp[i] * eigvals_rhoell_frobp[j] : i in [1..#eigvals_rhoell_frobp], j in [1..#eigvals_rhoell_frobp] | i lt j];

        index := Index(possible_dets, pp);
	if index ne 0 then
	    Remove(~possible_dets, index);
        index := Index(possible_dets, pp);
	    if index ne 0 then
	        Remove(~possible_dets, index);
	    end if;
	end if;

    // printf "possible determinants: %o\n", possible_dets;

        X := [x : x in X | &*[gens_evalsatpabove[1][i]^(x[i]) : i in [1..n]] in possible_dets];
        number_linearfacs := Minimum(number_linearfacs,&+([] cat [r[2] : r in roots_charpol]));
        // print p, #X;
        ind := ind+1;
    end while;


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
        
    return X_chars_values;
end intrinsic;
