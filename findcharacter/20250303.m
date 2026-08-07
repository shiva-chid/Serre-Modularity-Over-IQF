AttachSpec("spec");
AttachSpec("./CHIMP/CHIMP.spec");
P<x> := PolynomialRing(Integers());
f := x^4 + 2*x^3 + 4*x^2 + 2*x + 1;
L := getcharpols(f);
L := getcharpols(f : primesend := 1000); // if you need more Euler factors

// This creates a list of tuples <p,the corresponding Euler factor L_p(T)>. For example, the first entry in L is <7, T^6 - T^5 - 3*T^4 + 34*T^3 - 21*T^2 - 49*T + 343>.

// Now, the following command checks that whenever p is a prime = 1 mod 3, the number of roots of L_p(T) in the finite field F_7 is always strictly greater than zero.
split_Eulerfacs := [x : x in L | x[1] mod 3 eq 1];
{#Roots(x[2],GF(7)) gt 0 : x in split_Eulerfacs};
L;
quit;