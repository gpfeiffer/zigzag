##  TODO:
##
##  * Avoid the expansion of RightRegularX into full matrices ...
##

#############################################################################
#
# Given a list of lists of rows of non-neg ints
# find the minimal possible value for every position in every row.
SlowFoundation:= function(lis)
    local   f, m, i, l;
    
    f:= [];
    for l in lis do
        m:= [];
        for i in [1..Length(l[1])] do
            m[i]:= Minimum(l{[1..Length(l)]}[i]);
            l{[1..Length(l)]}[i]:= l{[1..Length(l)]}[i] - m[i];
        od;
        Add(f, m);
    od;
    
    return f;
end;


# Given a list of lists of rows of non-neg ints and a sum
# select a row from each of the lists
# such that the sum of the rows equals the given sum.
# (There must be a standard way of doing this efficiently,
# but I don't find that now ... '
SlowI:= 0;  SlowLog:= [];
SlowCombine:= function(list, sum, index)
    local   l, i, sols,  r,  small, pos, min, found, d;
    
    # keep me informed.
#    SlowI:= SlowI+1;
#    if SlowI mod 100000 = 0 then
#        SlowI:= 0;
#        Print(list, "\n", sum, "\n");
#        Error("return; to return");
#    fi;
    
    # trivial case first ...
    if list = [] then
        if Sum(sum) = 0 then
#            Print("+\n");
            return [[]]; 
        else
            return [];
        fi;
    fi;
    
    list:= Copy(list);    
    
    # check that every given row fits into the sum ...
    for i in [1..Length(list)] do
        list[i]:= Filtered(list[i], x-> Minimum(sum - x) >= 0);
        
        # return if a list then is empty ...
        if list[i] = [] then 
            return []; 
        fi;
    od;
    
    # extract minimal values.
    found:= SlowFoundation(list);
    sum:= sum - Sum(found);
    if Minimum(sum) < 0 then
        return [];
    fi;
        
    # pick row from the shortest list ...
    min:= Length(list[1]);  pos:= 1;
    for i in [2..Length(list)] do
        if Length(list[i]) < min then
            min:= Length(list[i]);  pos:= i;
        fi;
    od;
#    if min = 1 then Print("!\c"); fi;
    
#    Print(SlowLog, "\r");
#    Print("+\c");
    d:= Length(SlowLog) + 1;
    SlowLog[d]:= min;
    
    sols:= [];  min:= Difference([1..Length(list)], [pos]);
    for r in list[pos] do
        
        # keep me informed.
        SlowLog[d]:= SlowLog[d] - 1;
        
        # and recurse with smaller problem ...
        small:= SlowCombine(list{min}, sum - r, index{min});
        
        # combine solutions
        for l in small do
            l[index[pos]]:= r;
            l{index}:= l{index} + found;
            Add(sols, l);
        od;
    od;
    
    Unbind(SlowLog[d]);
#    Print("-\c");
    
    # return list of all solutions.
    return sols;
end;

## for example:
#W:= CoxeterGroup("E", 6);
#cc:= ConjugacyClasses(W);
#List(cc, Size);
#cen:= List(cc, x-> x.centralizer);
#ctc:= List(cen, CharTable);
#ct:= CharTable(W);
#fus:= List(cen, x-> FusionConjugacyClasses(x, W));
#ind:= List([1..Length(cc)], i->
#  Set(Induced(ctc[i], ct, Filtered(ctc[i].irreducibles, x-> x[1] = 1), fus[i])));
#sum:= List(ct.irreducibles, x-> x[1]);
#lis:= List(ind, x-> MatScalarProducts(ct, ct.irreducibles, x));;
##sol:= SlowCombine(lis, sum, [1..Length(cc)]);;

# now: which characters of the centralizers are used?
# for each class, list: order of w, order of the character l, order of l(w)
# compare wrt to powermap.
WhatCharacters:= function(W, eta)
    local   cc,  ct,  ctc,  data,  i,  cen,  fus,  ind,  pos,  WJ,  
            cenJ,  fusJ;
    
    cc:= ConjugacyClasses(W);
    ct:= CharTable(W); 
    ctc:= [];
    data:= [];
    for i in [1..Length(cc)] do
        cen:= Centralizer(W, Representative(cc[i]));
        fus:= FusionConjugacyClasses(cen, W);
        if cen = W then
            ctc[i]:= ct;
        else
            ctc[i]:=  DixontinI(DixonInit(cen)).charTable;
        fi;
        ind:= Induced(ctc[i], ct, ctc[i].irreducibles, fus);
        pos:= Filtered([1..Length(ind)], x-> ind[x] = eta[i]);
        ctc[i].selected:= ctc[i].irreducibles{pos};
   #     kernel:= KernelChar(ctc[i].selected[1]);
        #     ns:= NormalSubgroups(cen);
        
        WJ:= ReflectionSubgroup(W, Set(CoxeterWord(W, Representative(cc[i]))));
        cenJ:= Intersection(cen, WJ);
        fusJ:= FusionConjugacyClasses(cenJ, cen);
        

        data[i]:= rec(index:= i,
                      w:= Representative(cc[i]),
                      order:= ct.orders[i],
                      centralizer:= cen,
                      table:= ctc[i],
                      fusion:= fus,
                      fusionJ:= fusJ,
                      chars:= pos
   #                   kernel:= ns[Position(List(ns, x-> Set(FusionConjugacyClasses(x, cen))), kernel)]
                      );
    od;
    
    return data;
end;


#############################################################################
##  
##  
RanMatDescent:= function(D)
    local   mat,  xxx,  shapes,  i,  row,  iii,  j,  jjj,  lis;
    
    mat:= [];
    xxx:= LeftRegularX(D);
    shapes:= Shapes(D.W);
    for i in [1..Length(shapes)] do
        row:= [];
        iii:= Sum(shapes{[1..i-1]}, Size) + [1..Size(shapes[i])];
        for j in [1..Length(shapes)] do
            jjj:= Sum(shapes{[1..j-1]}, Size) + [1..Size(shapes[j])];
            lis:= List(iii, i-> List(jjj, j-> List(xxx, x-> x[i][j])));
            Add(row, RankMat(Concatenation(lis)));
        od;
        Add(mat, row);
    od;
    return mat;
end;

SizMatDescent:= function(D)
    local   mat,  xxx,  shapes,  i,  row,  iii,  j,  jjj,  lis;
    
    mat:= [];
    xxx:= LeftRegularX(D);
    shapes:= Shapes(D.W);
    for i in [1..Length(shapes)] do
        row:= [];
        iii:= Sum(shapes{[1..i-1]}, Size) + [1..Size(shapes[i])];
        for j in [1..Length(shapes)] do
            jjj:= Sum(shapes{[1..j-1]}, Size) + [1..Size(shapes[j])];
            lis:= List(iii, i-> List(jjj, j-> List(xxx, x-> x[i][j])));
            Add(row, Size(Set(Filtered(Concatenation(lis), x-> x <> 0*x))));
        od;
        Add(mat, row);
    od;
    return mat;
end;


##  
##  for each mu >= lambda the set of nontrivial vectors aJKL, 
##  J <= S, K \in mu, L \in lambda.
##
LisMatDescent:= function(D)
    local   mat,  xxx,  shapes,  i,  row,  iii,  j,  jjj,  lis;
    
    mat:= [];
    xxx:= LeftRegularX(D);
    shapes:= Shapes(D.W);
    for i in [1..Length(shapes)] do
        row:= [];
        iii:= Sum(shapes{[1..i-1]}, Size) + [1..Size(shapes[i])];
        for j in [1..Length(shapes)] do
            jjj:= Sum(shapes{[1..j-1]}, Size) + [1..Size(shapes[j])];
            lis:= List(iii, i-> List(jjj, j-> List(xxx, x-> x[i][j])));
            Add(row, Set(Filtered(Concatenation(lis), x-> x <> 0*x)));
        od;
        Add(mat, row);
    od;
    return mat;
end;

##  
##  
ClosLis:= function(lis)
    local   l,  clo,  i,  j,  a,  b;
    ##  
    l:= Length(lis);
    clo:= [];
    for i in [1..l] do
        clo[i]:= [];
        for j in [1..l] do
            clo[i][j]:= Copy(lis[i][j]);
            for a in [j+1..i] do
                UniteSet(clo[i][j], lis[i][a]);
            od;
            for b in [j..i-1] do
                UniteSet(clo[i][j], lis[b][j]);
            od;
        od;
    od;
    return clo;
end;

OpenLis:= function(lis)
    local   l,  clo,  i,  j,  a,  b;
    ##  
    l:= Length(lis);
    clo:= [];
    for i in [1..l] do
        clo[i]:= [];
        for j in [1..l] do
            clo[i][j]:= [];
            for a in [j+1..i] do
                UniteSet(clo[i][j], lis[i][a]);
            od;
            for b in [j..i-1] do
                UniteSet(clo[i][j], lis[b][j]);
            od;
        od;
    od;
    return clo;
end;

##  
##  
ClosLisRank:= function(lis, rank)
    local   l,  clo,  i,  j,  a,  b;
    ##  
    l:= Length(lis);
    clo:= [];
    for i in [1..l] do
        clo[i]:= [];
        for j in [1..l] do
            clo[i][j]:= Copy(lis[i][j]);
            for a in [j+1..i] do
                if rank[j] = rank[a] - 1 then
                    UniteSet(clo[i][j], lis[i][a]);
                fi;
            od;
            for b in [j..i-1] do
                if rank[b] = rank[i] - 1 then
                    UniteSet(clo[i][j], lis[b][j]);
                fi;
            od;
        od;
    od;
    return clo;
end;

OpenLisRank:= function(lis, rank)
    local   l,  clo,  i,  j,  a,  b;
    ##  
    l:= Length(lis);
    clo:= [];
    for i in [1..l] do
        clo[i]:= [];
        for j in [1..l] do
            clo[i][j]:= [];
            for a in [j+1..i] do
                if rank[j] = rank[a] - 1 then
                    UniteSet(clo[i][j], lis[i][a]);
                fi;
            od;
            for b in [j..i-1] do
                if rank[b] = rank[i] - 1 then
                    UniteSet(clo[i][j], lis[b][j]);
                fi;
            od;
        od;
    od;
    return clo;
end;


#############################################################################
##  
##  
##  
QuiverB:= function(n)
    local   lab,  m,  edg,  p,  l,  i,  a,  j,  b,  k,  c,  e,  q;

    lab:= [];
    for m in [0..n] do 
        Append(lab, Partitions(m));
    od;
    
    edg:= [];

    # loop over the vertices.
    for p in lab do
        l:= Length(p);
        for i in [1..l] do
            a:= p[i];
            for j in [i+1..l] do
                b:= p[j];

                # drop two parts a, b.
                e:= Size(Set([a, b])) - 1;
                if e > 0 then
                    q:= p{Difference([1..l], [i,j])};
                    AddSet(edg, [q, p, e]);
                fi;
            
                # join three parts a, b, c.
                for k in [j+1..l] do
                    c:= p[k];
                    e:= Size(Set([a, b, c])) - 1;
                    if e > 0 then
                        q:= p{Difference([1..l], [i,j,k])};
                        Add(q, a+b+c);
                        Sort(q, function(a, b) return a > b; end);
                        AddSet(edg, [p, q, e]);
                    fi;
                od;
                
            od;
        od;
    od;
    
    return edg;    
end;


##  
##  FIXME.  The following is incorrect.
##  
##  in D4:   [ [  ], [ 3, 1 ], 1 ]  should be [ [  ], [ 3, 1 ], 2 ]
##  
##  
##  in D6:  [ [  ], [ 5, 1 ], 1 ]  should be [ [  ], [ 5, 1 ], 2 ]
##          [ [ 2 ], [ 3, 2, 1 ], 1 ]  should be [ [ 2 ], [ 3, 2, 1 ], 2 ]
##          [ [ 3 ], [ 3, 2, 1 ], 1 ]  should be [ [ 3 ], [ 3, 2, 1 ], 2 ]
##          missing:  [ [  ], [ 3, 3 ], 1 ]
##          missing:  [ [ 3, 3 ], [ 2, 2, 1, 1 ], 1 ]
##  
##  in D8: [ [  ], [ 5, 3 ], 1 ]  should be [ [  ], [ 5, 3 ], 3 ] !?!
##         [ [  ], [ 7, 1 ], 1 ]  should be [ [  ], [ 7, 1 ], 2 ]
##         [ [ 2 ], [ 5, 2, 1 ], 1 ]  should be [ [ 2 ], [ 5, 2, 1 ], 2 ]
##         [ [ 2, 2 ], [ 3, 2, 2, 1 ], 1 ]  should be [ [ 2, 2 ], [ 3, 2, 2, 1 ], 2 ]
##         [ [ 3, 2 ], [ 3, 2, 2, 1 ], 1 ]  should be [ [ 3, 2 ], [ 3, 2, 2, 1 ], 2 ]
##         [ [ 4 ], [ 4, 3, 1 ], 1 ]  should be [ [ 4 ], [ 4, 3, 1 ], 2 ]
##         [ [ 5, 3 ], [ 3, 2, 2, 1 ], 1 ]  should be [ [ 5, 3 ], [ 3, 2, 2, 1 ], 2 ]
##         missing: [ [  ], [ 3, 3, 1, 1 ], 1 ] !?!
##         missing: [ [ 2 ], [ 3, 3, 2 ], 1 ]
##         missing: [ [ 3 ], [ 5, 2, 1 ], 1 ] !?!
##         missing: [ [ 3, 3, 2 ], [ 2, 2, 2, 1, 1 ], 1 ]
##         missing: [ [ 5 ], [ 3, 3, 2 ], 1 ] !?!
##         missing: [ [ 5 ], [ 4, 3, 1 ], 1 ] !?!
##         missing: [ [ 5, 3 ], [ 4, 2, 1, 1 ], 1 ]
##  
##  in D5:   [ [  ], [ 3, 2 ], 1 ]  is not an edge
##           [ [  ], [ 4, 1 ], 1 ]  is not an edge
##           [ [ 2 ], [ 2, 2, 1 ], 1 ]  is not an edge
##           [ [ 5 ], [ 2, 2, 1 ], 1 ]  is not an edge
##           missing:  [ [ 3, 2 ], [ 2, 2, 1 ], 1 ]
##           missing:  [ [ 2 ], [ 3, 2 ], 1 ]
##           missing:  [ [ 5 ], [ 3, 2 ], 1 ]
##           missing:  [ [ 5 ], [ 4, 1 ], 1 ]
##           missing:  [ [  ], [ 5 ], 1 ]
##           but [ [ 5 ], [ 3, 1, 1 ], 1 ] is correct.


QuiverD:= function(n)
    local   edg,  m,  p,  l,  i,  a,  j,  b,  e,  q,  k,  c;

    # initialize results list.
    edg:= [];
    
    # deal with partitions of m < n-1 first.
    for m in [0..n-2] do 
        for p in Partitions(m) do
            l:= Length(p);
            for i in [1..l] do
                a:= p[i];
                for j in [i+1..l] do
                    b:= p[j];
                    
                    # drop two parts a, b.
                    e:= Size(Set([a, b])) - 1;
                    if e > 0 then
                        q:= p{Difference([1..l], [i,j])};
                        AddSet(edg, [q, p, e]);
                    fi;
                    
                    # join three parts a, b, c.
                    for k in [j+1..l] do
                        c:= p[k];
                        e:= Size(Set([a, b, c])) - 1;
                        if e > 0 then
                            q:= p{Difference([1..l], [i,j,k])};
                            Add(q, a+b+c);
                            Sort(q, function(a, b) return a > b; end);
                            AddSet(edg, [q, p, e]);     
                        fi;
                    od;
                    
                od;
            od;
        od;
    od;
    
    # partitions of n need some extra care.
    for p in Partitions(n) do
        l:= Length(p);
        if ForAll(p, x-> x mod 2 = 0) then
            for i in [1..l] do
                a:= p[i];
                for j in [i+1..l] do
                    b:= p[j];

                    # drop two parts a, b.
                    e:= Size(Set([a, b])) - 1;
                    if e > 0 then
                        q:= p{Difference([1..l], [i,j])};
                        AddSet(edg, [q, [p, '-'], e]);
                        AddSet(edg, [q, [p, '+'], e]);
                    fi;
            
                    # join three parts a, b, c.
                    for k in [j+1..l] do
                        c:= p[k];
                        e:= Size(Set([a, b, c])) - 1;
                        if e > 0 then
                            q:= p{Difference([1..l], [i,j,k])};
                            Add(q, a+b+c);
                            Sort(q, function(a, b) return a > b; end);
                            AddSet(edg, [[q, '-'], [p, '-'], e]);     
                            AddSet(edg, [[q, '+'], [p, '+'], e]);     
                        fi;
                    od;
                    
                od;
            od;
            
        elif n mod 2 = 0 then
            for i in [1..l] do
                a:= p[i];
                for j in [i+1..l] do
                    b:= p[j];
                    
                    # join two parts a, b and drop.
                    q:= p{Difference([1..l], [i,j])};
                    e:= Size(Set([a, b]));
                    if q <> [] then 
                        e:= e - 1; 
                    fi;
                    if e > 0 then
                        AddSet(edg, [q, p, e]);
                    fi;
                    
                    # join three parts a, b, c.
                    for k in [j+1..l] do
                        c:= p[k];
                        e:= Size(Set([a, b, c])) - 1;
                        if e > 0 then
                            q:= p{Difference([1..l], [i,j,k])};
                            Add(q, a+b+c);
                            Sort(q, function(a, b) return a > b; end);
                            if Sum(q) = n and ForAll(q, x-> x mod 2 = 0) then
                                AddSet(edg, [[q, '-'], p, e]);
                                AddSet(edg, [[q, '+'], p, e]);
                            else
                                AddSet(edg, [q, p, e]);     
                            fi;
                        fi;
                    od;
                    
                    # join a, b, drop c.
                    for k in Difference([1..l], [i,j]) do
                        c:= p[k];
                        e:= Size(Set([a, b, c])) - 2;
#                        if c > 1 and e > 0 then
                        if e > 0 then
                            q:= p{Difference([1..l], [i,j,k])};
                            Add(q, a+b);
                            Sort(q, function(a, b) return a > b; end);
                            AddSet(edg, [q, p, e]);     
                        fi;
                    od;
                    
                od;
            od;
            
        else
            for i in [1..l] do
                a:= p[i];
                
                # drop one part a
                q:= p{Difference([1..l], [i])};
                if a > 1 and ForAll(q, x-> x mod 2 = 0) then
                    AddSet(edg, [q, p, 1]);
                fi;
                
                for j in [i+1..l] do
                    b:= p[j];
                    
                    # join two parts a, b.
                    e:= Size(Set([a, b])) - 1;
                    q:= p{Difference([1..l], [i,j])};
#                    if e > 0 and not 1 in q and (a + b) mod 2 = 1 then
                    if e > 0 and ForAll(q, x-> x mod 2 = 0) and (a + b) mod 2 = 1 then
                        Add(q, a + b);
                        Sort(q, function(a, b) return a > b; end);
                        AddSet(edg, [q, p, e]);
                    fi;
                    
                    # drop two parts a, b.
                    e:= Size(Set([a, b])) - 1;
                    q:= p{Difference([1..l], [i,j])};
                    if e > 0 and not (Sum(p) = n and ForAll(q, x-> x mod 2 = 0)) then
                        AddSet(edg, [q, p, e]);
                    fi;
                    
                    for k in [j+1..l] do
                        c:= p[k];
                        e:= Size(Set([a, b, c])) - 1;
                        
#                        # drop three parts a, b, c.
#                        if e > 0 then
#                            q:= p{Difference([1..l], [i,j,k])};
#                            AddSet(edg, [q, p, e]);
#                        fi;

                        # join three parts a, b, c.
                        if e > 0 and Number(p, x-> x mod 2 = 1) > 1 then
                            q:= p{Difference([1..l], [i,j,k])};
                            Add(q, a+b+c);
                            Sort(q, function(a, b) return a > b; end);
                            AddSet(edg, [q, p, e]);     
                        fi;
                    od;
                    
                od;
            od;
        fi;
    od;

    return edg;    
end;


QuiverDod:= function(n)
    local   lab,  l,  mat,  i,  p,  abc,  e,  b,  a,  q,  j,  c;
    
    if n mod 2 = 0 then
        Error("<n> must be odd");
    fi;
    
    lab:= LabelsShapes(Shapes(CoxeterGroup("D", n)));
    l:= Length(lab);
    mat:= NullMat(l, l);
    
    # loop over the vertices.
    for i in [1..l] do
        p:= lab[i];
        
        if Sum(p) < n then
        
            # drop two parts a, b.
            for abc in Combinations(p, 2) do
                e:= Size(Set(abc)) - 1;
                if e > 0 then
                    b:= Position(p, abc[2]);
                    a:= Position(p, abc[1], b);
                    q:= p{Difference([1..Length(p)], [a,b])};
                    j:= Position(lab, q);
                    mat[j][i]:= mat[j][i] + e;
                fi;
            od;
            
            # join three parts a, b, c.
            for abc in Combinations(p, 3) do
                e:= Size(Set(abc)) - 1;
                if e > 0 then
                    c:= Position(p, abc[3]);
                    b:= Position(p, abc[2], c);
                    a:= Position(p, abc[1], b);
                    q:= p{Difference([1..Length(p)], [a,b,c])};
                    Add(q, Sum(abc));
                    Sort(q, function(a, b) return a > b; end);
                    j:= Position(lab, q);
                    mat[j][i]:= mat[j][i] + e;
                fi;
            od;
            
        else
            
            # drop an odd part a > 1.
            for abc in Combinations(p, 1) do
                if abc[1] > 1 then
                    a:= Position(p, abc[1]);
                    q:= p{Difference([1..Length(p)], [a])};
                    if ForAll(q, x-> x mod 2 = 0) then
                        j:= Position(lab, q);
                        mat[j][i]:= mat[j][i] + 1;
                    fi;
                fi;
            od;
            
            # join or drop two parts a, b.
            for abc in Combinations(p, 2) do
                e:= Size(Set(abc)) - 1;
                if e > 0 then
                    b:= Position(p, abc[2]);
                    a:= Position(p, abc[1], b);
                    q:= p{Difference([1..Length(p)], [a,b])};
                    if abc[1] > 1 or not 1 in q then
                        Add(q, Sum(abc));
                        Sort(q, function(a, b) return a > b; end);
                    fi;
                    j:= Position(lab, q);
                    mat[j][i]:= mat[j][i] + e;
                fi;
            od;
            
            # conditionally join three parts a, b, c.
            for abc in Combinations(p, 3) do
                e:= Size(Set(abc)) - 1;
                if e > 0 then
                    if Sum(abc) mod 2 = 0 or ForAll(abc, x-> x mod 2 = 1) then
                        c:= Position(p, abc[3]);
                        b:= Position(p, abc[2], c);
                        a:= Position(p, abc[1], b);
                        q:= p{Difference([1..Length(p)], [a,b,c])};
                        Add(q, Sum(abc));
                        Sort(q, function(a, b) return a > b; end);
                        j:= Position(lab, q);
                        mat[j][i]:= mat[j][i] + e;
                    fi;
                fi;
            od;
        fi;
    od;
    
    return mat;    
end;


# given two partitions, decide what joined or dropped.
CompareLabels:= function(sml, big)
    local   l,  i,  join,  drop,  list,  j;
    l:= 0*[1..Sum(sml)];
    for i in sml do
        l[i]:= l[i] + 1;
    od;
    for i in big do
        l[i]:= l[i] - 1;
    od;
    join:= [];  drop:= [];
    if Sum(sml) = Sum(big) then  
        list:= join;
    else 
        list:= drop;
    fi;
    
    for i in Reversed([1..Length(l)]) do
        for j in [1..l[i]] do
            Add(list, i);
        od;
    od;
        
    return rec(join:= join, drop:= drop);
end;

        


#############################################################################
MaximalAJKL1:= function(W, s)

   local S, M, pos, cosrep, aJML, inn, out, J, L, ddd, sub, j, l, x;

   ddd:= SubsetsShapes(Shapes(W));
   S:= W.rootInclusion{[1..W.semisimpleRank]};
   M:= Difference(S, [s]);
   pos:= Filtered([1..Length(ddd)], x-> IsSubset(M, ddd[x]));
   sub:= ddd{pos};

   cosrep:= Iterator(ParabolicTransversal(W, M));

   aJML:= List(ddd, x-> 0*pos);
   
   
#   for x in cosrep do
   while cosrep.hasNext() do
      x:= cosrep.next();
      inn:= Difference(S, RightDescentSet(W, x));
      if M = [] then 
          out:= inn;
      else
          L:= OnSets(M, x);
          out:= Filtered(inn, s-> OnSets(L, W.(W.rootRestriction[s]))[Length(L)] <= W.parentN);
      fi;
      InfoZigzag2(" i: ", inn, " o: ", out, "\n");
      for J in Combinations(inn) do
         L:= OnSets(Difference(J, out), x^-1);
         j:= Position(ddd, J);  l:= Position(sub, L);
         aJML[j][l]:= aJML[j][l] + 1;
      od;
   od;

   # compress into pos/val (where pos is relative to all of ddd!)
   out:= rec(pos:= [], val:= []);
   for j in [1..Length(aJML)] do
      out.pos[j]:= [];  out.val[j]:= [];
      for l in [1..Length(aJML[j])] do
         if aJML[j][l] > 0 then
            Add(out.pos[j], pos[l]);
            Add(out.val[j], aJML[j][l]);
         fi;
      od;
   od;
   out.ddd:= ddd; out.sub:= sub;
   return out;
end;
  
#############################################################################
##  
# this will find all possible combinations of characters that are
#
# 1. induced linear characters of the centralizer, one for each class C.
# 2. scalar product with YCharacters gives sizes of Y intersect C.
# 3. sums over Coxeter classes yield ECharacters.
# (not required) 4. summing over all elements of C results in a symmetric
# table.  This last test reduces the number of possibilites in the case
# of non-crystallographic Coxeter groups.   For the crystallographic
# case, there seems to be a unique solution after step 3, in many cases 
# after step 2 already.
CCharacters:= function(W)
    local   cc,  ct,  ind,  c,  cen,  fus,  ctc,  sec,  sect,  yct,  
            i,  scp,  fil,  ect,  ccc,  lis,  sum,  sol,  j;
    
    cc:= ConjugacyClasses(W);
    ct:= CharTable(W); 
    ind:= [];
    for c in cc do
        cen:= Centralizer(W, Representative(c));
        fus:= FusionConjugacyClasses(cen, W);
        if cen = W then
            ctc:= ct;
        else
            ctc:= DixontinI(DixonInit(cen)).charTable;
        fi;
        Add(ind, Set(Induced(ctc, ct, Filtered(ctc.irreducibles, x-> x[1] = 1), fus)));
    od;
    
    sec:= SizesDescentConjugacyClasses(W);
    sect:= TransposedMat(sec);
    yct:= YCharacters(W);
    
    for i in [1..Length(cc)] do
        scp:= MatScalarProducts(ct, yct, ind[i]);
        fil:= Filtered([1..Length(scp)], x-> scp[x] = sect[i]); 
        ind[i]:= ind[i]{fil}; 
    od;
    
    ect:= ECharacters(DescentAlgebra(W));
    ccc:= List(Shapes(W), ConjugacyClasses);
    
    for i in [1..Length(ect)] do
        lis:= List(ind{ccc[i]}, x-> MatScalarProducts(ct, ct.irreducibles, x));
        sum:= MatScalarProducts(ct, ct.irreducibles, ect{[i]})[1];
        sol:= SlowCombine(lis, sum, [1..Length(lis)]);
        for j in [1..Length(lis)] do
        fil:= Filtered([1..Length(lis[j])], x-> lis[j][x] in sol{[1..Length(sol)]}[j]);    
            ind[ccc[i][j]]:= ind[ccc[i][j]]{fil};
        od;
    od;
    
    return ind;
end;

#############################################################################
#
# Submodule structure, Loewy Series ...
#
# first: the Cartan Matrix.
# Could be more efficient if the matrices were not all fully blown up!
# Also could take into account its lower triangular shape!
#
PrimitiveIdempotents:= function(D)
    local   lll,  nu,  xxx,  EEE,  a,  l;
    
    if IsBound(D.primitiveIdempotents) then
        return D.primitiveIdempotents;
    fi;

    lll:= List(Shapes(D.W), Size);
    nu:= Call(D, "Mu")^-1;
    xxx:= LeftRegularX(D);
    
    EEE:= [];  a:= 0;
    for l in lll do
        Add(EEE, Sum(nu{a+[1..l]}) * xxx);
        a:= a + l;
    od;

    D.primitiveIdempotents:= EEE;
    return EEE;
end;


CartanMatDescent:= function(D)
    local   xxx,  EEE,  car,  l,  ll,  i,  j;
    
    xxx:= LeftRegularX(D);
    EEE:= PrimitiveIdempotents(D);
    car:= []; 
    l:= Length(EEE);  ll:= Length(EEE[1]);
    for i in [1..l] do
        car[i]:= [];
        for j in [1..l] do
            car[i][j]:= RankMat(List(xxx, x-> EEE[i][ll] * x) * EEE[j]);
#            Print(".\c");
        od; 
#        Print("!\n");
    od;  
    return car;
end;

# a gen set for the homs from Pi to Pj.
HomDescent:= function(D, i, j)
    local   xxx,  EEE,  ll,  hom;
    
    xxx:= LeftRegularX(D);
    EEE:= PrimitiveIdempotents(D);
    ll:= Length(EEE[1]);
    hom:=  Set(List(xxx, x-> EEE[i][ll] * x) * EEE[j]);
    TriangulizeMat(hom);
    return Filtered(hom, x-> x <> 0*x);
end;            
            

# second: the radical.
# Brute force again ...
#
RadicalDescent:= function(D)
    local   xxx,  rad,  a,  e,  i;
    
    xxx:= LeftRegularX(D);
    rad:= [];  a:= 0;
    for e in Shapes(D.W) do
        for i in a + [2..Size(e)] do
            Add(rad, xxx[i]-xxx[i-1]);
        od;
        a:= a + Size(e);
    od;
    return rad;
end;

RadicalSeriesDescent:= function(D)
    local   rad,  l,  r,  ser;
    
    rad:= RadicalDescent(D);
    if rad = [] then return []; fi;
    
    l:= Length(rad[1]);
    r:= List(rad, x-> x[l]);
    ser:= [r];
    
    while true do
        r:= Union(List(r, x-> List(rad, y-> x * y)));
        TriangulizeMat(r);
        r:= Difference(r, [0*r[1]]);
        if r = [] then 
            return ser; 
        fi;
        Add(ser, r);
    od;
    
end;

MatsRadsDescent:= function(D)
    local   rad,  hom,  l,  zero,  i,  j,  mat,  k;
    
    
    rad:= List(RadicalSeriesDescent(D), x-> VectorSpace(x, Rationals));
    hom:= [];
    l:= Length(Shapes(D.W));
    zero:= 0*[1..Dimension(D)];
    for i in [1..l] do
        hom[i]:= [];
        for j in [1..l] do
            hom[i][j]:= VectorSpace(HomDescent(D, i, j), Rationals, zero);
        od;
    od;
    mat:= [];
    for k in [1..Length(rad)] do
        mat[k]:= [];
        for i in [1..l] do
            mat[k][i]:= [];
            for j in [1..l] do
                mat[k][i][j]:= Dimension(Intersection(hom[i][j], rad[k]));
            od;
        od;
    od;
    
    for k in [2..Length(mat)] do
        mat[k-1]:= mat[k-1] - mat[k];
    od;
    
    return mat;
end;

#############################################################################
##  
##  deprecated, new version in streets.g
##  
ProjectiveModule1:= function(D, i)
    local   ser,  zero,  hom,  j,  lis,  s;

    ser:= List(RadicalSeriesDescent(D), x-> VectorSpace(x, Rationals));
    zero:= 0*[1..Dimension(D)];
    hom:= [];
    for j in [1..Length(Shapes(D.W))] do
        hom[j]:= VectorSpace(HomDescent(D, i, j), Rationals, zero);
    od;
    lis:= [List(hom, Dimension)];
    for s in ser do 
        Add(lis, List(hom, h-> Dimension(Intersection(s, h))));
    od;
    
    for j in [2..Length(lis)] do
        if lis[j] = 0*lis[j] then
            Unbind(lis[j]);
        else
            lis[j-1]:= lis[j-1] - lis[j];
        fi;
    od;
        
    return lis;
end;

LaTeXProjectiveModule1:= function(D, nam, i)
    local   lis,  text,  j,  comma,  k;
    lis:= ProjectiveModule1(D, i);
    text:= "$\\begin{array}[b]{|c|}\\hline\n";
    for j in [1..Length(lis)] do
        comma:= false;
        for k in [1..Length(nam)] do
            if lis[j][k] > 0 then
                if comma then
                    Append(text, "\\, \c");
                fi;
                if lis[j][k] = 1 then
                    Append(text, nam[k]);
                else 
                    Append(text, "(");
                    Append(text, nam[k]);
                    Append(text, ")^{");
                    Append(text, String(lis[j][k]));
                    Append(text, "}");
                fi;
                comma:= true;
            fi;
        od;
        Append(text, "\\\\\\hline\n");
    od;
    Append(text, "\\end{array}$");
    
    return text;
end;


#############################################################################
##
##  How to find Right multiplication by the primitive idempotents
##  in terms of the E Basis.
##
RightPIE:= function(D)
    local   EEE,  r,  mat;
    
    EEE:= List(PrimitiveIdempotents(D), x-> x[Dimension(D)]);
    r:= List(RightRegularX(D), MatCompressedAJKL);
    mat:= Call(D, "Mu")^-1;
    return List(EEE, e-> mat*Sum([1..Length(e)], i-> e[i]*r[i])/mat);
end;


#############################################################################
##
## ich glaub wir brauchen ne function die zu einem Vector die entsprechende
## Matrix macht.
##
MatDescentVec:= function(D, vec)
    local   xxx,  mat,  i;

    xxx:= LeftRegularX(D);
    
    mat:= NullMat(Dimension(D), Dimension(D));
    for i in [1..Length(xxx)] do
        mat:= mat + vec[i] * xxx[i];
    od;
    
    return mat;
end;


#############################################################################  
##  
##  given aaa \subset D, generate the space aaa.D
##
RightIdeal:= function(aaa, D)
    local   zero,  xxx,  base,  space,  a,  x,  y;

    zero:= 0*[1..Dimension(D)];
    xxx:= LeftRegularX(D);
    base:= [];  space:= RowSpace(Rationals, base, zero);
    for a in aaa do
        if not a in space then
            Add(base, a);
            space:= RowSpace(Rationals, base, zero);
        fi;
    od;
    for a in base do
        for x in xxx do
            y:= a * x;
            if not y in space then
                Add(base, y);
                space:= RowSpace(Rationals, base, zero);
            fi;
        od;
    od;
    return space;
end;

LeftIdeal:= function(aaa, D)
    local   zero,  xxx,  base,  space,  a,  x,  y;

    zero:= 0*[1..Dimension(D)];
    xxx:= IdentityMat(Dimension(D));
    base:= [];  space:= RowSpace(Rationals, base, zero);
    for a in aaa do
        if not a in space then
            Add(base, a);
            space:= RowSpace(Rationals, base, zero);
        fi;
    od;
    for a in base do
        for x in xxx do
            y:= x * MatDescentVec(D, a);
            if not y in space then
                Add(base, y);
                space:= RowSpace(Rationals, base, zero);
            fi;
        od;
    od;
    return space;
end;


##  
##  
##  
Lat:= function(D, i, j)
    local   r,  sss,  xxx,  ttt,  f,  c;
    r:= function(mat) if mat = [] then return 0; fi; return RankMat(mat); end;
    sss:= SubsetsShapes(Shapes(D.W));
    xxx:= List(RightRegularX(D), MatCompressedAJKL);
    ttt:= List(xxx, TransposedMat);
    f:= Filtered([j..i], k-> IsSubset(sss[i], sss[k]) and IsSubset(sss[k], sss[j]));
    c:= List(Filtered(Cartesian(f, f), x-> x[1] >= x[2]), x-> ttt[x[1]][x[2]]);
    return r(c) - r(Difference(c, [ttt[i][j]]));
end;

##  Helper.  Test for not 0.
IsNonZero:= m -> m <> 0*m;

#############################################################################
##
##  the cartan matrix of type D.
##  this is only an experiment:
##  
CartanMatrixD:=function(n)
    local   bigg,  typeComposition,  par,  p,  car,  i,  x,  j,  y;
    
    bigg:= 1000;  # a number bigger than all parts ever considered.

    #  the type of a composition is determined by the sums of the 
    #  factors of its Lyndon Factorization
    typeComposition:=function(com)
        local   fac,  sum;
        
        fac:= Filtered(LyndonFactorisation(com), x-> Length(x) mod 2 = 1);
#        fac:= LyndonFactorisation(com);
        sum:= List(fac, x-> Sum(x) mod bigg);
        Sort(sum);
        return Reversed(sum);
    end;

    par:= LabelsShapes(Shapes(CoxeterGroup("D", n)));
    p:= Length(par);
    car:= NullMat(p, p);
    for i in [1..p] do 
        for x in Arrangements(par[i], Length(par[i])) do
            j:= Position(par, typeComposition(x));
            car[j][i]:= car[j][i] + 1;
            
            # NEW: account for the other short leg.
            if Sum(x) = n and x[1] > 1 then
                y:= Reversed(x);  Add(y, bigg);
                j:= Position(par, typeComposition(y));
                car[j][i]:= car[j][i] + 1;
            fi;
        od;
    od;
    return car;
end;




