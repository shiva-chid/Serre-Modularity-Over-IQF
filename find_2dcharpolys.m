fname := "nonsurj7.txt";
outfile := "./2dcharpolys/charpolys";
suff := ".txt";


P<x> := PolynomialRing(Integers());

f := Open(fname, "r");

line := Read(f);

delete f;


split_nums := Split(line, "[]\n");

for i in [1..4] do // can change the range of polynomials to compute over
    str_i := IntegerToString(i);
    of := outfile cat str_i cat suff; //2dcharpolys/charpolysi.txt

    strs := Split(split_nums[i], " ,");
    nums :=[];
    for str in strs do
        Append(~nums, StringToInteger(str));
    end for;
    f := elt<P | nums>;

    frobcharpols := getcharpols(f : primesend := 100); // precomputing the Frobenius polynomials for efficiency
    chars, allroots := find_onedimchar(f, 7 : charpols := frobcharpols);

    if #chars eq 2 then 
        s := "f" cat str_i " := " cat Sprint(f) cat ";\n"

        for j in [1..2] do
            str_j := IntegerToString(j);
            dets := find_determinant(f, 7, chars[j]`char: charpols := frobcharpols);
            for k in [1..#dets] do
                str_k := IntegerToString(k);
                primes_dets_traces := find_trace(f, 7, chars[j]`char, dets[k]`char : charpols := frobcharpols);
                seqname := "coeffs" cat str_j cat str_k; // coefficients of the resulting degree 2 charpoly indexed by epsilon1, determinant
                s := s cat seqname cat " := " cat Sprint(primes_dets_traces) cat ";\n";

            end for;
        end for;
        Write(of, s : Overwrite := true);

    end if;

end for;
    


