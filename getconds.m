/*
P<x> := PolynomialRing(Integers());
load "PicardConductor.m";

fil := Open("nonsurj7.txt","r");
s := Gets(fil);
while not IsEof(s) do
    f := P ! [StringToInteger(x) : x in Split(s,"[, ]")];
    print f;
    cond := PicardConductor(f);
    print f, cond;
end while;
*/
//////////////////////////////////////////////////////////

// run in the folder: Serre-Modularity-Over-IQF/picard_curves/

AttachSpec("spec");
P<x> := PolynomialRing(Integers());
load "nonsurj7.txt";
assert #curves eq 381;

fil1 := "curve_conductors.txt";
fil2 := "error_curve_conductors.txt";


n := StringToInteger(n);
f := P!curves[n];
try
    cond := PicardConductor(f);
    faccond := Factorisation(cond);
    out := Sprintf("%o:%o:%o", n, curves[n], &cat[s : s in Split(Sprint(faccond),"\n")]);
    PrintFile(fil1,out);
catch e;
    try
        ff := suppressed_integer_quartic(f);
        cond := PicardConductor(ff);
        faccond := Factorisation(cond);
        out := Sprintf("%o:%o:%o", n, curves[n], &cat[s : s in Split(Sprint(faccond),"\n")]);
        PrintFile(fil1,out);
    catch e;
        out := Sprintf("%o:%o:%o:%o", n, curves[n], e`Position, e`Object);
        PrintFile(fil2,out);
    end try;
end try;
exit;

// seq 1 381 | parallel --eta -j 32 magma n:={} getconds.m
/*
ETA: 0s Left: 0 AVG: 42.45s  local:0/348/100%/42.5s
*/

/*
[ -1, 26, -222, 612, 108 ]
[ 9, 198, 1224, 1436, 4 ] -> [ -49201071843, 366634072, -768390, 0, 1 ]
*/