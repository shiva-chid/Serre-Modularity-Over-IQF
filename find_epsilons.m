fname := "nonsurj7.txt";
outname := "chars_conds.txt";
P<x> := PolynomialRing(Integers());
goodlist := [];
badlist := [];

f := Open(fname, "r");


    line := Read(f);

    split_nums := Split(line, "[]\n");

    for coeffs in split_nums do
        strs := Split(coeffs, " ,");
        nums :=[];
        for str in strs do
            Append(~nums, StringToInteger(str));
        end for;
        f := elt<P | nums>;
        chars, allroots := find_onedimchar(f, 7);
        if #chars eq 0 then 
            chars, allroots := find_onedimchar(f,7: useinertFrobsq := false);
            if #chars eq 0 then 
                Append(~badlist, f);
                continue;
            end if;
        end if;
        for c in chars do
            Append(~goodlist, <f, Conductor(c`char), c`values_modell>);
        end for;
        print goodlist;
        print badlist;
    end for;


