// Define the number field K = Q(√-3)
Q<x> := PolynomialRing(Rationals());
K<zeta3> := NumberField(x^2 + x + 1);
OK := RingOfIntegers(K);
// Compute the conductor N of a given genus 3 curve C
C := HyperellipticCurve(x^7 + 2*x^5 + 3*x^3 + 5*x + 7);
Genus(C);
N := Conductor(C);
print "Conductor of C:", N;
// Compute the ideal NOK in OK
NOK := ideal<OK | N>;
print "Conductor in OK:", NOK;

// Compute the Hecke Character Group
H := HeckeCharacterGroup(NOK);
print "Hecke Character Group:", H;

// Choose an unramified prime p (i.e., p ∤ N)
p := 5; // Example choice, ensure p ∤ N

// Compute the Euler factor Lp(C, t)
L_p<x> := EulerFactor(C, p);
print "Euler Factor at p:", L_p;


// Loop through all primes less than 1000.
for l in PrimesUpTo(1000) do
    // Create the finite field GF(l) and its polynomial ring.
    F := GF(l);
    PF<x> := PolynomialRing(F);
    
    // Reduce Lp modulo l.
    f := PF!L_p;
    
    // Check if f has any roots in GF(l).
    // Roots(f) returns a sequence of pairs [root, multiplicity].
    if #Roots(f) gt 0 then
         values := [Evaluate(f, F!i) : i in [1..l-1]];
         //print the result
         print l;
         print f;
         print values;
    end if;
end for;