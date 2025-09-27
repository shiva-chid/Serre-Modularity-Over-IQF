intrinsic find_twodimchar(f :: RngUPolElt, ell :: RngIntElt, epsilon_1 : radical_cond := 1, primes_bound := 500, charpols := [], ramified := false, useinertFrobsq := false, noskip := true) -> SeqEnum, SeqEnum
{draft}
    SetColumns(0);
    Z := Integers();
    P_ell<T> := PolynomialRing(GF(ell));
    f := suppressed_integer_quartic(f);
    if radical_cond eq 1 then
        radical_cond := RadCond(f);
    end if;
    if ramified then
        radical_cond := (radical_cond mod ell eq 0) select radical_cond else ell*radical_cond;
    end if;
    cond := radical_cond^4;
    F<zeta3> := CyclotomicField(3);
    OF := RingOfIntegers(F);
    P_F<xF> := PolynomialRing(OF);
    ellaboveF := PrimeIdealsOverPrime(F,ell);
    OFmodell1, resF1 := ResidueClassField(OF,ellaboveF[1]);
    // If ell splits, second prime:
    OFmodell2, resF2 := ResidueClassField(OF,ellaboveF[2])
        where _ is (#ellaboveF eq 2) select ellaboveF[2] else ellaboveF[1];
    G := HeckeCharacterGroup(cond*OF);
    K_targ := (ell mod 3 eq 1) select CyclotomicField(ell-1) else CyclotomicField(ell^2-1);
    G := TargetRestriction(G,K_targ);
    OK_targ := RingOfIntegers(K_targ);
    ellabove := PrimeIdealsOverPrime(K_targ,ell);
    OK_targ_modell, resmodell := ResidueClassField(OK_targ,ellabove[1]);

    if charpols eq [] then
        charpols := getcharpols(f : primesend := primes_bound);
    end if;
    if useinertFrobsq then
        charpols := [(x[1] mod 3 eq 1) select x else <x[1],Bracket(2,x[2])>
                     : x in charpols | x[1] ne 3 and x[1] ne ell];
    else
        charpols := [x : x in charpols | x[1] mod 3 eq 1 and x[1] ne ell];
    end if;
    if not ramified then
        charpols := [x : x in charpols | x[1] mod ell eq 1];
    end if;

    charpolsmodell := [<x[1],P_ell ! x[2]> : x in charpols];
    primes := [x[1] : x in charpolsmodell];
    printf "\nUsing local L-polynomials at these primes (for determinant check):\n%o\n\n", primes;

    gens_G := SetToSequence(Generators(G));
    n := #gens_G;
    exps_G := [Order(chi) : chi in gens_G];
    conds_G := [Conductor(chi) : chi in gens_G];
    printf "Orders of the characters generating the Hecke character group:\n%o\n", exps_G;

    X := Set(CartesianProduct([[0..e-1] : e in exps_G]));

    ind := 1;
    prime_ideals := [];
    all_detvals := [];

    while #X gt 0 do
        if ind gt #charpolsmodell then
            printf "Checked %o primes, up to %o\n", #charpolsmodell, charpolsmodell[#charpolsmodell];
            break;
        end if;
        p := charpolsmodell[ind,1];
        charpol := charpolsmodell[ind,2];
        pabove := PrimeIdealsOverPrime(F,p);
        Append(~prime_ideals, pabove);

        if cond mod p eq 0 then
            ind := ind+1;
            continue;
        end if;

        // Factor => find deg2 factor => read off determinant
        facs := Factorisation(charpol);
        deg2facs := [ ff : ff in facs | Degree(ff[1]) eq 2 ];
        if #deg2facs eq 0 then
            printf "Witness: p = %o, no irreducible deg2 factor => no 2D det.\n", p;
            return [], [];
        end if;
        poly2 := deg2facs[1][1];
        // print poly2;
        b := Coefficient(poly2,0);
        Append(~all_detvals, <p,b>);

        // Evaluate epsilon_1(Frob_p) mod ell; pick the first prime ideal
        val_eps_p := resmodell(epsilon_1(pabove[1]));
        if val_eps_p eq 0 then
            printf "p = %o => epsilon_1(Frob_p) = 0 mod ell => conflict.\n", p;
            return [], [];
        end if;
        local_delta_val := b*(val_eps_p^-1);

        // Evaluate each generator at pabove[1], mod ell
        gens_evalsatp := [resmodell((gens_G[i])(pabove[1])) : i in [1..n]];

        // Prune
        Xnew := [ x : x in X |
            &*[ gens_evalsatp[i]^(x[i]) : i in [1..n] ] eq local_delta_val
        ];

        if #Xnew eq 0 then
            if noskip then
                printf "No exponent tuple survived at p = %o\n", p;
                return [], [];
            else
                ind := ind+1;
                continue;
            end if;
        end if;
        X := Set(Xnew);
        print p, #X;
        ind := ind+1;
    end while;

    // Build the final list of characters
    X_chars := < &*[(gens_G[i])^x[i] : i in [1..n]] : x in X >;
    RF := recformat<char : GrpHeckeElt, values_modell : Assoc>;
    X_chars_values := [];
    for chi in X_chars do
        chi_values_modell := AssociativeArray();
        for i := 1 to #prime_ideals do
            p := Norm(prime_ideals[i][1] meet Z);
            chi_values_modell[p] := <resmodell((chi)(frakp)) : frakp in prime_ideals[i]>;
        end for;
        Append(~X_chars_values, rec<RF | char := chi, values_modell := chi_values_modell>);
    end for;

    printf "Based on local determinant data up to prime index = %o:\n", ind-1;
    printf "Found %o possible 2D-determinant characters.\n", #X_chars;

    return X_chars_values, all_detvals;
end intrinsic;