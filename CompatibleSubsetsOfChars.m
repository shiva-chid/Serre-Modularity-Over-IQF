intrinsic CompatibleSubsetsOfChars(f :: RngUPolElt, ell :: RngIntElt, chars :: List, Galpairs :: SeqEnum, Dualpairs :: SeqEnum : primesend := 1000, Lpols := []) -> SeqEnum
{given 
- a quartic polynomial defining a Picard curve
- a prime ell
- a list of F_ell-valued Hecke characters potentially appearing in the semisimplification
of the ell-torsion representation over F=Q(zeta_3)
- a sequence containing tuples of indices indicating Galois conjugate pairs
- a sequence containing tuples of indices indicating dual pairs
return all possible blocks of character indices, with multiplicities,
that can appear in the semisimplification of the ell-torsion representation.
Optional inputs: a bound for the number of primes to be used, or a precomputed list of Lpolynomials.
}
    if chars eq [**] then return []; end if;
    if Lpols eq [] then
        Lpols := getcharpols(f : primesend := primesend);
    end if;
    charpols := [(x[1] mod 3 eq 1) select x else <x[1],Bracket(2,x[2])> : x in Lpols | x[1] gt Maximum(7,ell)];
    chars_modulus := [Modulus(x) : x in chars];
    F := NumberField(Order(chars_modulus[1]));
    K := CyclotomicField(LCM([CyclotomicOrder(TargetRing(x)) : x in chars]));
    ellaboveK := PrimeIdealsOverPrime(K,ell)[1];
    Fell, OKtoFell := ResidueClassField(ellaboveK);
    toavoid := Norm(&meet(chars_modulus));
    primes := [x[1] : x in charpols | toavoid mod x[1] ne 0];
    primesF := [PrimeIdealsOverPrime(F,p) : p in primes];
    roots := [{*r[1]^^r[2] : r in Roots(x[2],GF(ell))*} : x in charpols | x[1] in primes];

    n := #chars;
    Sn := Sym(n);
    act1 := &*([Sn!1] cat [Sn!(x[1],x[2]) : x in Galpairs | x[1] ne x[2]]);
    act2 := &*([Sn!1] cat [Sn!(x[1],x[2]) : x in Dualpairs | x[1] ne x[2]]);
    G := sub<Sn|[act1,act2]>;
    assert GroupName(G) in {"C2^2","C2","C1"};
    irredblocks := Orbits(G);
    irredblocks := [{*y : y in x*} join {*y : y in x | y^act1 eq y*} : x in irredblocks];
    m := #irredblocks;
    X := CartesianProduct([{0..6 div #x} : x in irredblocks]);
    possibilities := [];
    for x in X do
        if x eq <0 : i in [1..m]> or &+[#irredblocks[i]*x[i] : i in [1..m]] gt 6 then continue; end if;
        for j := 1 to #primes do
            for pp in primesF[j] do
                try
                // xvalsinK := &join[{*chars[j](pp)^^x[i] : j in irredblocks[i]*} : i in [1..m]];
                // xvals := &join[{*OKtoFell(K!(chars[j](pp)))^^x[i] : j in irredblocks[i]*} : i in [1..m]];
                xvals := &join[{*OKtoFell(chars[j](pp))^^x[i] : j in irredblocks[i]*} : i in [1..m]];
                catch e;
                    print e;
                    // print xvalsinK;
                    // print {xval in K : xval in xvalsinK};
                    printf "Error for the prime pp=%o over p=%o, with irredblocks=\n%o,\nand multiplicity = %o\n", primesF[j], primes[j], irredblocks, x;
                    return [];
                end try;
                if not xvals subset roots[j] then continue x; end if;
            end for;
        end for;
        poss := [* <irredblocks[i],x[i]> : i in [1..m] *];
        Append(~possibilities,poss);
    end for;
    return possibilities;
end intrinsic;
