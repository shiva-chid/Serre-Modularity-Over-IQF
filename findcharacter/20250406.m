AttachSpec("spec");
AttachSpec("./CHIMP/CHIMP.spec");

P<x> := PolynomialRing(Integers());
f := x^4 + 2*x^3 + 4*x^2 + 2*x + 1;
chars, allroots := find_onedimchar(f, 7 : primes_bound := 1000, useinertFrobsq := true);
printf "Found %o characters:\n", #chars;
for i in [1..#chars] do
    chi := chars[i]`char;
    printf "\nCharacter %o:\n", i;
    printf "  - Conductor norm: %o\n", Norm(Conductor(chi));
    printf "  - Order: %o\n", Order(chi);
    printf "  - Values at primes:\n";
    for p in Keys(chars[i]`values_modell) do
        printf "    p = %o: %o\n", p, chars[i]`values_modell[p];
    end for;
end for;
printf "\nRoots of characteristic polynomials mod ell:\n";
for r in allroots do
    printf "  p = %o: roots = %o\n", r[1], r[2];
end for;
// G := Parent(chars[1]`char);
// gens := SetToSequence(Generators(G));
// gens;
// gens[1];
// Order(gens[1]);
// Conductor(gens[1]);
exit;