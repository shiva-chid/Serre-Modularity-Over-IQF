intrinsic PicardConductor(f :: RngUPolElt) -> RngIntElt
{return the conductor of the Picard curve defined by y^3=f(x)
by appealing to a Sage implementation due to Sijsling et al}
    cmd := Sprintf("\"import sys; import os; sys.path.append(os.path.expanduser('~/mclf')); from mclf import *; from sage.all import QQ, PolynomialRing; from picard_curves import PicardCurve; R = PolynomialRing(QQ,'x'); C=PicardCurve(R(%o)); print(C.cond)\"", Coefficients(f));
    val := Pipe("cd ~/Serre-Modularity-Over-IQF/picard_curves\n sage -python -c " cat cmd, "");
    // print val;
    val := Split(val,"\n");
    val := val[#val];
    val := Split(val,"[(,)] \n");
    // print val;
    val := [StringToInteger(x) : x in val];
    assert #val mod 2 eq 0;
    return &*[val[2*i-1]^val[2*i] : i in [1..ExactQuotient(#val,2)]];
end intrinsic;
