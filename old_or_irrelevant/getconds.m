P<x> := PolynomialRing(Integers());
load "../PicardConductor.m";
/*
fil := Open("final/nonsurj7.txt","r");
s := Gets(fil);
while not IsEof(s) do
    s1 := Split(s,"]")[1];
    f := P ! [StringToInteger(x) : x in Split(s1,"<[, ")];
    cond := PicardConductor(f);
    print f, cond;
end while;
*/
fil := Open("../nonsurj7.txt","r");
s := Gets(fil);
while not IsEof(s) do
    f := P ! [StringToInteger(x) : x in Split(s,"[, ]")];
    print f;
    cond := PicardConductor(f);
    print f, cond;
end while;

//////////////////////////////////////////////////////////
