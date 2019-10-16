#############################################################################
##
#A  blocks.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
##
##  This file contains support for block vectors and block matrices/
##
##  <#GAPDoc Label="Intro:Blocks">
##    A <E>block vector</E> <Index>block vector</Index> is ...
##
##    A <E>block matrix</E> <Index>block matrix</Index> is ...
##
##    The functions described in this chapter are implemented in the file
##    <F>blocks.g</F>.
##  <#/GAPDoc>
##


## how to turn a block vector into a vector, relative to a composition com.
VecBlVec:= function(bv, com)
    local   n,  l,  v,  i,  u;

    n:= Sum(com);
    l:= Length(com);
    v:= [];
    for i in [1..l] do
        u:= bv[i];
        if IsList(u) then
            if Length(u) = com[i] then
                Append(v, u);
            else
                Error("lengths don't match");
            fi;
        else
            Append(v, 0*[1..com[i]] + u);
        fi;
    od;

    return v;
end;



##  given a composition com of n, turn a vector of length n into a block vector
BlVecVec:= function(v, com)
    local   set,  new,  s,  u;

    set:= SetComposition(com);
    new:= [];
    for s in set do
        u:= v{s};
        if Size(Set(u)) = 1 then
            Add(new, u[1]);
        else
            Add(new, u);
        fi;
    od;

    return new;
end;

## how to turn a block matrix into a matrix, relative to a composition com
MatBlMat:= function(bm, com)
    local   n,  l,  set,  mat,  i,  j;

    n:= Sum(com);
    l:= Length(com);
    set:= SetComposition(com);
    mat:= NullMat(n, n);
    for i in [1..l] do
        for j in [1..l] do
            if IsMat(bm[i][j]) then
                mat{set[i]}{set[j]}:= bm[i][j];
            else
                if bm[i][j] <> 0 then
                    # assert i = j
                    if i <> j then
                        Error("nonzero nondiagonal");
                    fi;
                    mat{set[i]}{set[i]}:= bm[i][i] * IdentityMat(com[i]);
                fi;
            fi;
        od;
    od;

    return mat;
end;

## umgekehrt
##
## FIXME: can we abbreviate an off diagonal multiple of an identity matrix???
##
BlMatMat:= function(m, com)
    local   new,  l,  set,  i,  j,  b;

    new:= [];
    l:= Length(com);
    set:= SetComposition(com);
    for i in [1..l] do
        new[i]:= [];
        for j in [1..l] do
            b:= m{set[i]}{set[j]};
            if b = 0*b then
                new[i][j]:= 0;
            elif i = j and b = b[1][1] * IdentityMat(com[i]) then
                new[i][i]:=  b[1][1];
            else
                new[i][j]:= b;
            fi;
        od;
    od;

    return new;
end;




#############################################################################
##
#E  Emacs  . . . . . . . . . . . . . . . . . . . . . . local emacs variables.
##
##  Local Variables:
##  mode:               gap
##  outline-regexp:     "#F\\|#V\\|#E\\|#A"
##  fill-column:        77
##  End:
##
