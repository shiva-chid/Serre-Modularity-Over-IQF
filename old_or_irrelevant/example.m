// Write a function that a matrix group H as input, and returns the semisimplification of H
// i.e., a matrix group in block diagonal form, that is conjugate to the Levi subgroup of H.

// Example.

ell := 13;
G := GL(2,GF(ell));
MG := MaximalSubgroups(G);
[IsIrreducible(GModule(x`subgroup)) : x in MG];
// [ true, true, true, false, false, true, true ]
H := MG[4]`subgroup;
V := Radical(H);
U := sub<H|[x : x in V | {a[1] : a in Eigenvalues(x)} eq {1}]>; // U is the unipotent radical
n1 := Valuation(#V,ell);
assert #U eq ell^n1;
L1 := Complements(H,U); // possible Levi subgroups
assert #L1 eq 1;
G_ss := L1[1];
G_ss; // as you can see, G_ss is not in block diagonal form. // Conjugate it (i.e., change basis) to put it in block diagonal form

M := GModule(G_ss);
Decomp := DirectSumDecomposition(M);
if #Decomp eq 1 then
    P := IdentityMatrix(BaseRing(H), Degree(H));
    G_ss_diag := G_ss;
else
    NewBasis := [];
    for comp in Decomp do
        NewBasis cat:= Basis(comp);
    end for;
    n := #NewBasis;
    P := Matrix(BaseRing(H), n, n, &cat[ Eltseq(v) : v in NewBasis ]);
    G_ss_diag := sub< GL(n, BaseRing(H)) | [ P^-1 * g * P : g in Generators(G_ss) ] >;
end if;
G_ss_diag;
exit;

/*
MatrixGroup(3, GF(13)) of order 2^7 * 3^3 * 7 * 13
Generators:
[ 4  8  1]
[ 9  3  8]
[ 3  9  5]

[11 12  9]
[ 8  5 10]
[ 3  5  3]

[ 5 10  1]
[ 0  8  0]
[ 2  0  8]

[10 10 10]
[ 3  7  7]
[ 3  1  9]

[ 8  0  0]
[ 0  8  0]
[ 0  0  8]

[ 9  7  2]
[ 0  1  0]
[ 4 10  2]

[ 4  0  0]
[ 0  4  0]
[ 0  0  4]

[ 5  1  4]
[ 7  6 12]
[ 3  6  1]

[ 3  0  0]
[ 0  3  0]
[ 0  0  3]

[10  3 12]
[11  0  4]
[ 5  5  6]

[ 4  1  4]
[ 0  8  0]
[ 8  2  3]

[ 6  6 11]
[ 0 10  0]
[ 9  4  0]

[ 2  0  0]
[ 0  2  0]
[ 0  0  2]
*/
