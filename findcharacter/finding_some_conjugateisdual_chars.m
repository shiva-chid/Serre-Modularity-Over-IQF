AttachSpec("spec");

ell := 7;
F<zeta3> := CyclotomicField(3);
OF := RingOfIntegers(F);
ellaboveF := PrimeIdealsOverPrime(F,ell);
lam1 := ellaboveF[1]; lam2 := ellaboveF[2];

// constructing the mod-ell cyclotomic character
K<zeta6> := CyclotomicField(ell-1);
ellaboveK := PrimeIdealsOverPrime(K,ell)[1];
Fell, OKtoFell := ResidueClassField(ellaboveK);
chi_ell := ModEllCyclotomicCharacter(F,ell : K := K, lambda := ellaboveK);

// values of the mod-ell cyclotomic character
n := 1000;
firstnprimes := [p : p in PrimesUpTo(n) | not p in {3,ell}];
chi_ell_vals := AssociativeArray();
for p in firstnprimes do
    chi_ell_vals[p] := (p mod 3 eq 1) select p mod ell else p^2 mod ell;
end for;
chi_ell_allvals := [[OKtoFell(chi_ell(pp)) : pp in PrimeIdealsOverPrime(F,p)] : p in firstnprimes];
assert [chi_ell_vals[p] : p in firstnprimes] eq [x[1] : x in chi_ell_allvals];


dat := [**];
for m := 1 to 30 do
    modulus := ell*m;
    printf "Looking for special characters (whose product with Galois conjugate is the mod-ell cyclotomic character)\n of modulus %o valued in F_%o^*.\n", modulus, ell;
    G := HeckeCharacterGroup(modulus*OF : Target := K);
    A, AtoG := AbelianGroup(G); AbelianInvariants(A);
    // chi_ell := Extend(chi_ell,G);

    specialchars := [];
    for x in A do
        cand_epsilon := AtoG(x);
        for p in firstnprimes do
            if modulus mod p eq 0 then continue; end if;
            paboveF := PrimeIdealsOverPrime(F,p);
            if #paboveF eq 1 then paboveF := paboveF cat paboveF; end if;
            prodval := &*[OKtoFell((cand_epsilon)(pp)) : pp in paboveF];
            if prodval ne chi_ell_vals[p] then continue x; end if;
        end for;
        Append(~specialchars,cand_epsilon);
    end for;
    printf "%o specialcharacters found\n", #specialchars;
    if #specialchars eq 0 then continue; end if;
    Append(~dat,<m,specialchars>);
end for;
[x[1] : x in dat];
// [ 3, 6, 9, 12, 15, 18, 21, 24, 27, 30]
[#x[2] : x in dat];
// [ 6, 18, 18, 36, 36, 54, 6, 72, 18, 108]

epsilon := dat[1][2][1];
assert isconjugatethedual(epsilon,ell);
assert isconjugatethedual(epsilon,ell : chi_ell := chi_ell, lambda := ellaboveK);
