P<x> := PolynomialRing(Integers());
f := P![1458,557,129,15,1];
fstr := &cat(Split(Sprint(f)," *"));
fstr;
filename := Sprintf("temp_%o",Getpid());
System("./hwlpolys y^3=" cat fstr cat " " cat "9" cat " 1 0 -1 0 " cat filename);

cmd := "~/hwlpolys y^3=" cat fstr cat " " cat "9" cat " 1 0 -1 0 " cat filename; cmd;
System("~/hwlpolys y^3=" cat fstr cat " " cat "9" cat " 1 0 -1 0 " cat filename);
