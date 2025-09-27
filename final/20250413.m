AttachSpec("spec");
AttachSpec("./CHIMP/CHIMP.spec");
P<x> := PolynomialRing(IntegerRing());
f := x^4 + 2*x^3 + 4*x^2 + 2*x + 1;
K<z3> := CyclotomicField(3);
OF := RingOfIntegers(K);
cond := 9*OF;
G := HeckeCharacterGroup(cond);
epsilon_1 := G!1;
twodimchars, local_data := find_twodimchar(
    f,                     
    7,                    
    epsilon_1 :           
      radical_cond  := 1, 
      primes_bound  := 200,
      charpols      := [],
      ramified      := false,
      useinertFrobsq:= false,
      noskip        := true
);

printf "Number of possible 2D-determinant characters found: %o\n", #twodimchars;
for rec in twodimchars do
    chi := rec`char;
    printf "Character = %o\n", chi;
end for;
