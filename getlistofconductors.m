fil := Open("curve_conductors_sorted.txt","r");
s := Gets(fil);
conductors := AssociativeArray();
while not IsEof(s) do
    s_split := Split(s,":");
    i := StringToInteger(s_split[1]);
    condfacs := [StringToInteger(x) : x in Split(s_split[3],"[<,> ]")];
    assert #condfacs mod 2 eq 0;
    cond := &*[condfacs[2*i-1]^condfacs[2*i] : i in [1..#condfacs/2]];
    conductors[i] := cond;
    s := Gets(fil);
end while;

N := #conds;
conductors := [(i in Keys(conductors)) select conductors[i] else 0 : i in [1..N]];
conductors eq conds;
