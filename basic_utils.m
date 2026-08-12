intrinsic suppressed_quartic(f :: RngUPolElt) -> RngUPolElt
{Given a quartic polynomial f, returns an monic suppressed polynomial g of the form x^4+a*x^2+b*x+c,
such that the curve y^3=f is isomorphic to the curve y^3=g.}
    require Degree(f) eq 4 : "f must have degree 4";
    P<x> := Parent(f);
    a4 := Coefficient(f,4);
    if a4 ne 1 then
        f := a4^3*Evaluate(f,x/a4);
    end if;

    a3 := Coefficient(f,3);
    if a3 ne 0 then
        f := Evaluate(f,x-a3/4);
    end if;
    return f;
end intrinsic;


intrinsic suppressed_integer_quartic(f :: RngUPolElt : uptotwist := false) -> RngUPolElt
{Given a quartic polynomial f over the rationals, returns an integral polynomial g of the 
form x^4+a*x^2+b*x+c, such that the curve y^3=f is isomorphic to the curve y^3=g.}
    require Degree(f) eq 4 : "f must have degree 4";
    P<x> := PolynomialRing(Rationals());
    a4 := Coefficient(f,4);
    if a4 ne 1 then
        f := a4^3*Evaluate(f,x/a4);
    end if;

    a3 := Coefficient(f,3);
    if a3 ne 0 then
        f := Evaluate(f,x-a3/4);
    end if;

    coeffs := Coefficients(f)[1..3];
    coeffs_dens := [Denominator(x) : x in coeffs];
    pfacs_dens := &join[Set(PrimeFactors(x)) : x in coeffs_dens];
    P<x> := PolynomialRing(Integers());
    if uptotwist then
        m := (pfacs_dens eq {}) select 1 else &*[p^n where n is Maximum([Ceiling(Valuation(coeffs_dens[i],p)/(5-i)) : i in [1..3]]) : p in pfacs_dens];
        return P!([m^(5-i)*coeffs[i] : i in [1..3]] cat [0,1]);
    else
        m := (pfacs_dens eq {}) select 1 else &*[p^n where n is Maximum([Ceiling(Valuation(coeffs_dens[i],p)/(3*(5-i))) : i in [1..3]]) : p in pfacs_dens];
        return P!([m^(3*(5-i))*coeffs[i] : i in [1..3]] cat [0,1]);
    end if;
end intrinsic;


intrinsic RadCond(f :: RngUPolElt) -> RngIntElt
{Given a quartic polynomial f over the rationals, returns the product of the bad primes 
of the suppressed integral model of the curve y^3=f.}
    f := suppressed_integer_quartic(f);
    radical_disc := &*([1] cat [p : p in PrimeFactors(Discriminant(f))]);
    radical_leadcoeff := &*([1] cat [p : p in PrimeFactors(Coefficient(f,4))]);
    radical_cond := LCM(radical_leadcoeff,radical_disc);
    if radical_cond mod 3 ne 0 then
        radical_cond := 3*radical_cond;
    end if;
    return radical_cond;
end intrinsic;


intrinsic UptoTwist(L :: SeqEnum) -> SeqEnum, SeqEnum
{given a list L of
- quartic polynomials f, or
(this is not implemented yet) - pairs <f,h> consisting of a quartic polynomial f and a linear polynomial h,
describing Picard curves y^3 = f or h y^3 = f,
return a trimmed list containing the defining data for pairwise non-isomorphic curves
such that any curve in L is isomorphic to one in the trimmed list.}
    QQ := Rationals();
    Lnorm := [suppressed_integer_quartic(f : uptotwist := true) : f in L];

/*
    PPw2 := WeightedProjectiveSpace(QQ,[2,3,4]);
    abcsinPPw2 := [];
    Luptotwist := [];
    Lnormuptotwist := [];
    for i := 1 to #L do
        dat := Lnorm[i];
        abc := Reverse(Coefficients(dat)[1..3]);
        abcinPPw2 := PPw2!abc;
        if abcinPPw2 in abcsinPPw2 then continue i; end if; // equality of points in weighted projective space not implemented        
        Append(~abcsinPPw2,abcinPPw2);
        Append(~Luptotwist,L[i]);
        Append(~Lnormuptotwist,Lnorm[i]);
    end for;
    return Luptotwist, Lnormuptotwist;
*/
    abcsuptotwist := [];
    Luptotwist := [];
    Lnormuptotwist := [];
    for i := 1 to #Lnorm do
        abc := Reverse(Coefficients(Lnorm[i])[1..3]);
        a,b,c := Explode(abc);
        for seenabc in abcsuptotwist do
            a1,b1,c1 := Explode(seenabc);
            if a^2*c1 eq a1^2*c and a*c*b1^2 eq a1*c1*b^2 then continue i; end if;
        end for;
        Append(~abcsuptotwist,abc);
        Append(~Luptotwist,L[i]);
        Append(~Lnormuptotwist,Lnorm[i]);
    end for;
    return Luptotwist, Lnormuptotwist;
end intrinsic;

intrinsic UptoIsomorphism(L :: SeqEnum) -> SeqEnum, SeqEnum
{given a list L of
- quartic polynomials f, or
- pairs <f,h> consisting of a quartic polynomial f and a linear polynomial h,
describing Picard curves y^3 = f or h y^3 = f,
return a trimmed list containing the defining data for pairwise non-isomorphic curves
such that any curve in L is isomorphic to one in the trimmed list.}
    QQ := Rationals();
    PP2 := ProjectiveSpace(QQ,2);
    P3<x,y,z> := CoordinateRing(PP2);

    curvesuptoisom := [];
    Luptoisom := [];
    for dat in L do
        if Type(dat) cmpeq RngUPolElt then
            f := dat;
            C := Curve(PP2,P3!(Evaluate(f,x/z)*z^4)-y^3*z);
        else
            f,h := Explode(dat);
            C := Curve(PP2,P3!(Evaluate(f,x/z)*z^4)-y^3*P3!(Evaluate(h,x/z)*z));
        end if;
        
        for C1 in curvesuptoisom do
            if IsIsomorphic(C,C1) then continue dat; end if;
        end for;
        
        Append(~curvesuptoisom,C);
        Append(~Luptoisom,dat);
    end for;
    return Luptoisom, curvesuptoisom;
end intrinsic;
