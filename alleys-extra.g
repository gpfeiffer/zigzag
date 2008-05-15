#  Given W, d = w_L w_M and J such that |L - J| = 1
#  write d as a sequence of longest coset reps for J
helper:= function(W, J, d)
    local   seq,  des,  L,  a;
    seq:= [];
    while d <> () do
        des:= LeftDescentSet(W, d);
        if Size(des) <> 1 then Print("...ahemm...\n"); fi;
        Add(seq, des[1]);
        L:= Union(J, des);
        a:= LongestElement(W, J) * LongestElement(W, L);
        J:= OnSets(J, a);
        d:= a^-1 * d;
    od;
    return seq;
end;

