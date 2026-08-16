// initialize files. // overwrites. Use with caution.
/*
echo "allprimesdetstraces := AssociativeArray();" > allprimesdetstraces.txt
echo "numberofpossibledetchars := AssociativeArray();" > numberofpossibledetchars.txt
echo "orderofNebentypus := AssociativeArray();\nNebentypusField := AssociativeArray();" > Nebentypus.txt
*/

SetColumns(0);
i := StringToInteger(i);

load "nonsurj7.txt";
P<x> := PolynomialRing(QQ);
f := P!curves[i];
cond := conds[i];
ell := 7;
// if cond mod ell eq 0 then exit; end if;

load "allcharsoutput.txt";

AttachSpec("spec");
F<zeta3> := CyclotomicField(3);
OF := RingOfIntegers(F);
ellaboveF := PrimeIdealsOverPrime(F,ell);
lam1 := ellaboveF[1]; lam2 := ellaboveF[2];
K<zeta6> := CyclotomicField(ell-1);
ellaboveK := PrimeIdealsOverPrime(K,ell)[1];
chi_ell := ModEllCyclotomicCharacter(F,ell : K := K, lambda := ellaboveK);
assert chi_ell(-zeta3) eq 1;

// fil1 := "outputfiles/allprimesdetstraces_goodat7.txt";
// fil2 := "outputfiles/numberofpossibledetchars_goodat7.txt";
// fil3 := "outputfiles/orderofNebentypus_goodat7.txt";
// fil_err := "outputfiles/error_detandtrace_goodat7.txt";
fil1 := "outputfiles/allprimesdetstraces.txt";
fil2 := "outputfiles/numberofpossibledetchars.txt";
fil3 := "outputfiles/Nebentypus.txt";
fil_err := "outputfiles/error_detandtrace.txt";

// fil1 := "outputfiles/allprimesdetstraces_ns13.txt";
// fil2 := "outputfiles/numberofpossibledetchars_ns13.txt";
// fil3 := "outputfiles/Nebentypus_ns13.txt";
// fil_err := "outputfiles/error_detandtrace_ns13.txt";


try
    // chars := [*HeckeCharacter((F!condgens_prunedchars[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals_prunedchars[i][j]*]) : j in [1..#vals_prunedchars[i]] *];
    // ans := CompatibleSubsetsOfChars(P!curves[i],ell,chars,Galpairinds[i],pairinds[i]);
    // assert allpossiblesubsetsofchars[i] eq ans;
    // assert #ans eq 1;
    // ans := ans[1];
    // epsiloninds := &join[ {*x^^block[2] : x in block[1]*} : block in ans];
    // epsiloninds := Sort(Setseq(Set(epsiloninds)));
    // epsilons := [*chars[ii] : ii in epsiloninds*];
    // condgens_prunedchars[i][epsiloninds];

    chars := [*HeckeCharacter((F!condgens[i][j])*OF,[*<F!x[1],K!x[2]> : x in vals[i][j]*]) : j in [1..#vals[i]] *];
    ans := CompatibleSubsetsOfChars(P!curves[i],ell,chars,allGalpairinds[i],allpairinds[i]);
    assert Allpossiblesubsetsofchars[i] eq ans;
    assert #ans eq 1 or (i eq 207 and #ans eq 2) or #ans eq 3;
    if #ans gt 1 then ans := [x : x in ans | &+[#block[1]*block[2] : block in x] eq 2]; end if;
    if #ans gt 1 then
        out := Sprintf("%o:%o possibilities for the pair <epsilon,epsilon^c>", i, #ans);
        PrintFile(fil_err, out);
        exit;
    end if;
    assert #ans eq 1;
    ans := ans[1];
    epsiloninds := &join[ {*x^^block[2] : x in block[1]*} : block in ans];
    epsiloninds := Sort(Setseq(Set(epsiloninds)));
    epsilons := [*chars[ii] : ii in epsiloninds*];
    // condgens[i][epsiloninds];

    charpols := getcharpols(f); // precomputing the Frobenius characteristic polynomials

    possibledets := find_determinant(f,ell,epsilons[1] : charpols := charpols);
    dets := [*x`char : x in possibledets*];
    // print #dets;
    conjpairs, conjpairinds := pairupconjugate(dets,ell);
    goodpairs := [* x : x in conjpairs | AssociatedPrimitiveCharacter(x[1]*x[2]) eq chi_ell^2 *];
    assert #goodpairs eq 1;
    det := goodpairs[1][1];
    assert det(-zeta3) eq 1;
    assert exists(wt1){k : k in [0..ell-2] | Conductor(det*chi_ell^-(k-1))+lam1 eq 1*OF};
    assert exists(wt2){k : k in [0..ell-2] | Conductor(det*chi_ell^-(k-1))+lam2 eq 1*OF};
    wt := {*wt1, wt2*};
    if #Set(wt) eq 1 then
        Nebentypus := det*chi_ell^-(Random(wt)-1);
        ordNeben := Order(Nebentypus);
        Ldefpol := DefiningPolynomial(NumberField(AbelianExtension(Nebentypus)));
        outextra := Sprintf("wt[%o] := %m;\norderofNebentypus[%o] := %m;\nNebentypusField[%o] := %m;\n", i, wt, i, ordNeben, i, Ldefpol);
    else
        outextra := Sprintf("wt[%o] := %m;\n", i, wt);
    end if;
    PrintFile(fil3, outextra);

/*
    allprimesdetstraces := [find_trace(f,ell,epsilons[1],det : charpols := charpols) : det in dets];
    // #primesdetstraces;
    // primesdetstraces;

    allexacttraces := [[x : x in primesdetstraces | #x[3] eq 1] : primesdetstraces in allprimesdetstraces];
    // #exacttraces;
    // exacttraces;

    assert &and[#[x : x in primesdetstraces | #x[3] gt 2] eq 0 : primesdetstraces in allprimesdetstraces];
    // {* #x[3] : x in primesdetstraces | #x[3] ne 1 *};                               
    assert &and[&and[x[3][1] eq -x[3][2] : x in primesdetstraces | #x[3] ne 1] : primesdetstraces in allprimesdetstraces];
*/

    allprimesdetstraces := find_trace(f,ell,epsilons[1],det : charpols := charpols);
    // #primesdetstraces;
    // primesdetstraces;

    allexacttraces := [x : x in allprimesdetstraces | #x[3] eq 1];
    // #exacttraces;
    // exacttraces;

    assert #[x : x in allprimesdetstraces | #x[3] gt 2] eq 0;
    // {* #x[3] : x in primesdetstraces | #x[3] ne 1 *};
    assert &and[x[3][1] eq -x[3][2] : x in allprimesdetstraces | #x[3] ne 1];

    out := Sprintf("allprimesdetstraces[%o] := %m;", i, allprimesdetstraces);
    PrintFile(fil1, out);

    outextra := Sprintf("numberofpossibledetchars[%o] := %m;", i, #dets);
    PrintFile(fil2, outextra);
catch e;
    out := Sprintf("%o:%o:%o:%o:%o", i, #dets, goodpairs, e`Position, e`Object);
    PrintFile(fil_err, out);
end try;
exit;

// seq 1 381 | parallel --eta -j 32 magma i:={} parallelrun_detandtrace.m

////////////////////////////////////////////////////////
