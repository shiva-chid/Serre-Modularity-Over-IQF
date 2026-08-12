SetLogFile("analysing_final_results_goodat7.log");

load "nonsurj7.txt";
load "allcharsoutput.txt";
assert {#curves,#conds,#condgens_prunedchars,#vals_prunedchars,#allpossiblesubsetsofchars} eq {381};
assert {#condgens,#vals,#Allpossiblesubsetsofchars} eq {381};

goodat7inds := [i : i in [1..#conds] | conds[i] mod 7 ne 0]; #goodat7inds;
goodat7inds;


AttachSpec("spec");
// L := allpossiblesubsetsofchars;
// Now with all characters, i.e., without the Raynaud condition
L := Allpossiblesubsetsofchars;

{* #L[i] : i in goodat7inds *};
{* {* <#y[1],y[2]> : y in L[i][1] *} : i in goodat7inds *};

// Output is the same without the Raynaud condition

ell := 7;
F<zeta3> := CyclotomicField(3);
OF := RingOfIntegers(F);
errorinds := [];
dat := [];
for i in goodat7inds do
    try
        charconds := condgens_prunedchars[i];
        goodcharpossibilities := [&join[ {*x^^block[2] : x in block[1]*} : block in option] : option in L[i]];
        goodcharcondpossibilities := [{* ((F!charconds[ii])*OF)^^Multiplicity(x,ii) : ii in Set(x) *} : x in goodcharpossibilities];
        Append(~dat,goodcharcondpossibilities);
        printf "%o:%o\n", i, &cat[s : s in Split(Sprint(goodcharcondpossibilities),"\n")];
    catch e;
        // print e;
        // break;
        // print i;
        Append(~errorinds,i);
    end try;
end for;
assert #errorinds eq 0;

{*{*#y : y in x*} : x in dat*};

AutF, auts, tau := AutomorphismGroup(F);
assert Order(AutF.1) eq 2; sigma := tau(AutF.1);
condpairs_decomp := [];
for i := 1 to #dat do
    condpair_decomp := [];
    for j := 1 to #dat[i] do
        condpair := Setseq(Set(dat[i][j]));
        assert #condpair eq 2;
        assert sigma(condpair[1]) eq condpair[2];
        g := &+(condpair);
        condpair_rempart := [x/g : x in condpair];
        assert &and[nxg eq ell^Valuation(nxg,ell) where nxg is Norm(xibyg) : xibyg in condpair_rempart]; // remaining part is ell part
        x1byg, x2byg := Explode(condpair_rempart);
        Append(~condpair_decomp,<g,x1byg,x2byg>);
    end for;
    Append(~condpairs_decomp,condpair_decomp);
end for;
#condpairs_decomp;

ZZ := Integers();
combinedcondofcharpairs := [[y[1]^2 : y in x] : x in condpairs_decomp]; // must remove the ell-part
assert &and[&and[y eq Minimum(y)*OF : y in x] : x in combinedcondofcharpairs];
combinedcondofcharpairs := [[ZZ!Minimum(y) : y in x] : x in combinedcondofcharpairs];
notreduciblecurves := [];
Sengunbound := [];
allextrafactors := [];
for i := 1 to #dat do
    ii := goodat7inds[i];
    temp1 := [];
    temp2 := [];
    for x in combinedcondofcharpairs[i] do
        if conds[ii] mod x ne 0 then continue x; end if;
        condquotient := ZZ!(conds[ii]/x);
        extrafac, sqfac := Squarefree(condquotient);
        assert extrafac*sqfac^2 eq condquotient;
        Append(~temp1,sqfac*ell);
        Append(~temp2,extrafac);
    end for;
    if #temp1 eq 0 then Append(~notreduciblecurves,i); continue; end if;
    Append(~Sengunbound,<ii,temp1,temp2>);
end for;
#notreduciblecurves;

smallestlevel := Minimum([Minimum(x[2]) : x in Sengunbound]);

Factorisation(smallestlevel);

Sengunbound := Sort(Sengunbound, func<x,y|x[2][1]-y[2][1]>);
Sengunbound;

[[Factorisation(y) : y in x[2]] : x in Sengunbound];
