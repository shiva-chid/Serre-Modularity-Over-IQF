AttachSpec("spec");
AttachSpec("./CHIMP/CHIMP.spec");
P<x> := PolynomialRing(Integers());
f := x^4 + 2*x^3 + 4*x^2 + 2*x + 1;
chars, allroots := find_onedimchar(f,7 : primes_bound := 1000, useinertFrobsq := true);
chars;
allroots;
exit;