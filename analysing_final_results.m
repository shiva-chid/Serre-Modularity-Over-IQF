SetLogFile("analysing_final_results.log");

load "nonsurj7.txt";
load "allcharsoutput.txt";
assert {#curves,#conds,#condgens_prunedchars,#vals_prunedchars,#allpossiblesubsetsofchars} eq {381};
assert {#condgens,#vals,#Allpossiblesubsetsofchars} eq {381};

AttachSpec("spec");
L := Allpossiblesubsetsofchars;
{* #L[i] : i in [1..#L] *};
{* {* {* <#z[1],z[2]> : z in y *} : y in L[i] *} : i in [1..#L] *};

ell := 7;
F<zeta3> := CyclotomicField(3);
OF := RingOfIntegers(F);
errorinds := [];
dat := [];
for i in [1..#L] do
    try
        charconds := condgens[i];
        goodcharpossibilities := [&join[ {*x^^block[2] : x in block[1]*} : block in option] : option in L[i]];
        goodcharpossibilities := [x : x in goodcharpossibilities | #x in {2,6}];
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
        if #dat[i][j] ne 2 then continue; end if;
        condpair := MultisetToSequence(dat[i][j]);
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
{* #x : x in condpairs_decomp *};

ZZ := Integers();
combinedcondofcharpairs := [[y[1]^2 : y in x] : x in condpairs_decomp]; // must remove the ell-part
assert &and[&and[y eq Minimum(y)*OF : y in x] : x in combinedcondofcharpairs];
combinedcondofcharpairs := [[ZZ!Minimum(y) : y in x] : x in combinedcondofcharpairs];
notreduciblecurves := [];
Sengunbound := [];
allextrafactors := [];
for i := 1 to #dat do
    if conds[i] eq 0 then continue; end if;
    temp1 := [];
    temp2 := [];
    for x in combinedcondofcharpairs[i] do
        if conds[i] mod x ne 0 then continue x; end if;
        condquotient := ZZ!(conds[i]/x);
        extrafac, sqfac := Squarefree(condquotient);
        assert extrafac*sqfac^2 eq condquotient;
        Append(~temp1,sqfac*ell);
        Append(~temp2,extrafac);
    end for;
    if #temp1 eq 0 then Append(~notreduciblecurves,i); continue; end if;
    Append(~Sengunbound,<i,temp1,temp2>);
end for;
#notreduciblecurves;

Sengunbound := Sort(Sengunbound, func<x,y|Minimum(x[2])-Minimum(y[2])>);
Sengunbound;

smallestlevel := Minimum(Sengunbound[1][2]);
index := Sengunbound[1][1];
smallestlevel, index;
Factorisation(smallestlevel);


[[Factorisation(y) : y in x[2]] : x in Sengunbound];
