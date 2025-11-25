fname := "./nonsurj7.txt";
outfile := "./chars_conds.txt";
suff := ".txt";


P<x> := PolynomialRing(Integers());

f := Open(fname, "r");

line := Read(f);

delete f;


split_nums := Split(line, "[]\n");

    for i in [1..#split_nums] do // Range of polynomiLs to compute over
        str_i := IntegerToString(i);
        strs := Split(split_nums[i], " ,");
        nums :=[];
        for str in strs do
            Append(~nums, StringToInteger(str));
        end for;
        f := elt<P | nums>;
        frobcharpols := getcharpols(f : primesend := 100);
        chars, allroots := find_onedimchar(f, 7 : charpols := frobcharpols);

        if #chars gt 0 then
            s := "f" cat str_i cat " := " cat Sprint(f) cat ";\n\n";

            for j in [1..#chars] do
                str_j := IntegerToString(j);
                name1 := "e1" cat str_i cat strj cat ":= ";
                name2 := "e1" cat str_i cat strj "cond := ";
                s := s cat name1 cat Sprint(chars[i]`char) cat ";\n";
                s := s cat name2 cat Sprint(Conductor(chars[1]`char)) cat ";\n\n";
            end for;
            s := s cat "\n";

            if i eq 1 then
                Write(outfile, s : Overwrite := true);
            else
                Write(outfile, s);
            end if;

        end if;
            
    end for;
    


