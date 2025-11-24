fname := "nonsurj7.txt";
outfile := "./chars_conds/conds_charpolys";
suff := ".txt";
P<x> := PolynomialRing(Integers());


f := Open(fname, "r");

    line := Read(f);

delete f;


    split_nums := Split(line, "[]\n");

    for i in [1..10] do
        strs := Split(split_nums[i], " ,");
        nums :=[];
        of := outfile cat IntegerToString(i) cat suff;
        for str in strs do
            Append(~nums, StringToInteger(str));
        end for;
        f := elt<P | nums>;
        chars, allroots := find_onedimchar(f, 7);
        /*if #chars eq 0 then 
            chars, allroots := find_onedimchar(f,7: useinertFrobsq := false);
            if #chars eq 0 then 
                Append(~badlist, f);
                continue;
            end if;
        end if;
        */
        
        if #chars eq 2 then
        s := "f := " cat Sprint(f) cat ";\ne1cond := " cat Sprint(Conductor(chars[1]`char)) cat ";\n";
            for k in [1..2] do
                
                dets := find_determinant(f, 7, chars[k]`char);
                for j in [1..#dets] do
                    primes_dets_traces := find_trace(f, 7, chars[k]`char, dets[j]`char);
                    s := s cat "polys" cat IntegerToString(k) cat IntegerToString(j) cat " := " cat Sprint(primes_dets_traces) cat ";\n";
                end for;
        end for;

    end for;


