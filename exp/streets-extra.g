##  list all streets by hand.

Streets0:= function(W)
    local   list,  hhh,  sh,  new,  N;
    
    list:= [];
    
    hhh:= function(alley, N)
        local   L,  o,  s,  new,  Ns;
        
        L:= Difference(alley[1], alley[2]);
        for o in Orbits(N, L) do
            s:= o[1];
            new:= [alley[1], Concatenation(alley[2], [s])];
            Ns:= Stabilizer(N, s);
            Add(list, Street(W, new));
            hhh(new, Ns);
        od;
    end;
            
    for sh in Shapes(W) do
        new:= [Representative(sh), []];
        Add(list, Street(W, new));
        N:= Call(sh, "Complement");
        hhh(new, N);
    od;
    return list;
end;


##  what is an essential street?
EssentialStreets:= function(W)
    local   list,  hhh,  sh,  new,  N;
    
    list:= [];
    
    hhh:= function(alley, N)
        local   L,  o,  s,  new,  Ns,  m,  c;
        
        L:= Difference(alley[1], alley[2]);
        for o in Orbits(N, L) do
            s:= o[1];
            new:= [alley[1], Concatenation(alley[2], [s])];
            m:= DeltaAlley(W, new);
            if m <> 0*m then
                c:= Street(W, new);
                m:= Call(c, "Matrix").mat;
                if m <> 0*m then 
                    Add(list, c);
                    Print(".\c");
                fi;
            fi;
            Ns:= Stabilizer(N, s);
            hhh(new, Ns);
        od;
    end;
            
    for sh in Shapes(W) do
        new:= [Representative(sh), []];
        Add(list, Street(W, new));
        N:= Call(sh, "Complement");
        hhh(new, N);
    od;
    return list;
end;

##  old and alternative versions of QuiverRelations.
QuiverRelations1:= function(W)
    local   aaa,  bbb,  path,  path0,  more,  a,  relations,  sss,  l,  
            null,  all,  mat,  delta,  new,  kern,  adr,  delete,  
            line,  pos,  i,  b;
    
    # start with a reasonably small set of alley classes.
    bbb:= List(Shapes(W), x-> Call(x, "Street"));
    for a in bbb do 
        Append(bbb, Call(a, "Movers"));
    od;
    InfoZigzag1("Generated ", Length(bbb), " streets\n");

    aaa:= Filtered(bbb, x-> IsNonZero(Call(x, "Delta").mat));
    InfoZigzag1("Of which ", Length(aaa), " are nonzero streets\n");
    
    aaa:= Filtered(aaa, x-> x = Call(x, "LongestSuffix"));
    InfoZigzag1("Starting with ", Length(aaa), " irreducible streets\n");
    
    # split idempotents from nilpotents.
    path:= [];  path0:= [];  more:= [];
    for a in aaa do
        if a.alley[2] = [] then
            Add(path0, a);
        else
            Add(more, [a]);
        fi;
    od;
    InfoZigzag1("Of which ", Length(path0), " have length 0.\n");
    
    relations:= [];
    
    sss:= SubsetsShapes(Shapes(W));
    l:= SetComposition(List(Shapes(W), Size));
    null:= List(sss, x-> 0);
    
    while more <> [] do
        
        Add(path, more);
        InfoZigzag1("Added ", Length(more), " paths of length ", Length(path), ".\n");
        
        # consider all paths at once.
        all:= Concatenation(path);
        
        mat:= [];
        for a in all do
            delta:= DeltaPath(a);
            new:= Copy(null);
            new{l[delta.support]}:= delta.mat;
            Add(mat, new);
        od;
        
        kern:= NullspaceMat(mat);
        InfoZigzag1("Found ", Length(kern), " relations.\n");
        
        
        # FIXME:
        # suppose adr is a list of back references such that 
        #   all[i] = path[adr[i][1]][adr[i][2]] ...
        adr:= Concatenation(List([1..Length(path)], i-> TransposedMat([List(path[i], x-> i), [1..Length(path[i])]])));

        
        # find all relations.
        delete:= List(path, x-> []);
        for line in kern do
            pos:= Filtered([1..Length(line)], i-> line[i] <> 0);
            Add(relations, rec(paths:= all{pos}, coeffs:= line{pos}));
            Add(delete[adr[pos[1]][1]], adr[pos[1]][2]);
        od;
        
        # remove obsoletes.
        for i in [1..Length(path)] do
            path[i]:= path[i]{Difference([1..Length(path[i])], delete[i])};
        od;
        
        InfoZigzag1("Length: ", List(path, Length), ": ", Length(path0) + Sum(path, Length), ".\n");
        
        # extend paths.
        more:= [];
        for a in path[Length(path)] do
            for b in path[1] do
                if a[Length(a)] * b[1] <> [] then
                    Add(more, Concatenation(a, b));
                fi; 
            od;
        od;
        
    od;
    
    return rec(path0:= path0, path:= path, relations:= relations);
end;

QuiverRelations0:= function(W)
    local   aaa,  path,  path0,  more,  a,  relations,  sss,  l,  
            null,  all,  mat,  delta,  new,  kern,  adr,  delete,  
            line,  pos,  i,  b;
    
    # start with a reasonably small set of alley classes.
    aaa:= [];
    for a in Shapes(W) do
        Append(aaa, PreOrderProperty(Street(W, [a.J, []]), x-> IsNonZero(Call(x, "Delta").mat)));
        InfoZigzag1("\n");
    od;

#    aaa:= Filtered(Streets(W), x-> IsNonZero(Call(x, "Delta").mat));
    aaa:= Filtered(aaa, x-> x = Call(x, "LongestSuffix"));
    InfoZigzag1("Starting with ", Length(aaa), " alley classes.\n");
    
    # split idempotents from nilpotents.
    path:= [];  path0:= [];  more:= [];
    for a in aaa do
        if a.alley[2] = [] then
            Add(path0, a);
        else
            Add(more, [a]);
        fi;
    od;
    InfoZigzag1("Of which ", Length(path0), " have length 0.\n");
    
    relations:= [];
    
    sss:= SubsetsShapes(Shapes(W));
    l:= SetComposition(List(Shapes(W), Size));
    null:= List(sss, x-> 0);
    
    while more <> [] do
        
        Add(path, more);
        InfoZigzag1("Added ", Length(more), " paths of length ", Length(path), ".\n");
        
        # consider all paths at once.
        all:= Concatenation(path);
        
        mat:= [];
        for a in all do
            delta:= DeltaPath(a);
            new:= Copy(null);
            new{l[delta.support]}:= delta.mat;
            Add(mat, new);
        od;
        
        kern:= NullspaceMat(mat);
        InfoZigzag1("Found ", Length(kern), " relations.\n");
        
        
        # FIXME:
        # suppose adr is a list of back references such that 
        #   all[i] = path[adr[i][1]][adr[i][2]] ...
        adr:= Concatenation(List([1..Length(path)], i-> TransposedMat([List(path[i], x-> i), [1..Length(path[i])]])));

        
        # find all relations.
        delete:= List(path, x-> []);
        for line in kern do
            pos:= Filtered([1..Length(line)], i-> line[i] <> 0);
            Add(relations, rec(paths:= all{pos}, coeffs:= line{pos}));
            Add(delete[adr[pos[1]][1]], adr[pos[1]][2]);
        od;
        
        # remove obsoletes.
        for i in [1..Length(path)] do
            path[i]:= path[i]{Difference([1..Length(path[i])], delete[i])};
        od;
        
        InfoZigzag1("Length: ", List(path, Length), ": ", Length(path0) + Sum(path, Length), ".\n");
        
        # extend paths.
        more:= [];
        for a in path[Length(path)] do
            for b in path[1] do
                if a[Length(a)] * b[1] <> [] then
                    Add(more, Concatenation(a, b));
                fi; 
            od;
        od;
        
    od;
    
    return rec(path0:= path0, path:= path, relations:= relations);
end;

#############################################################################
VerifyQuiver:= function(qr)
    local   W,  D,  mu,  eee,  l,  a,  mat,  fa;
    
    # trivial case: nothing to verify.
    if qr.path = [] then
        return true;
    fi;
        
    W:= qr.path0[1].W;
    D:= DescentAlgebra(W);
    mu:= Call(D, "Mu");
    eee:= List(LeftRegularE(D), x-> x^mu);
    l:= SetComposition(List(Shapes(W), Size));
    
    # it suffices to check the paths of length 1.
    for a in qr.path[1] do
        Print("checking \c");
        mat:= Call(Product(a), "Matrix");
        Print(" ...\c");
        fa:= Sum(mat.mat) * eee{l[mat.target]};
        fa{l[mat.source]}{l[mat.target]}:= fa{l[mat.source]}{l[mat.target]} - mat.mat;
        if fa <> 0*fa then 
            return false;
        fi;
        Print (" OK.  ");
        fa:= mat.mat[1] * eee{l[mat.target]};
        if Length(l[mat.source]) * eee[l[mat.source][1]] * fa = fa then
            Print("Eigenvalue good also.\n");
        else
            Print("*** EIGENVALUE OUT OF LINE ***\n");
        fi;
        
    od;
    
    return true;
end;

#############################################################################
##
##  Movers as well
##
CartanMatMovers:= function(W)
    local   bbb,  a,  l,  mat,  b,  i,  j;
    
    bbb:= List(Shapes(W), x-> Call(x, "Street"));
    for a in bbb do 
        Append(bbb, Call(a, "Movers"));
    od;
    InfoZigzag1("Generated ", Length(bbb), " streets\n");
    
    l:= Length(Shapes(W));
    mat:= NullMat(l, l);
    for b in bbb do
        i:= Call(b, "Source");
        j:= Call(b, "Target");
        mat[i][j]:= mat[i][j] + 1;
    od;
    
    return mat;
end;

QuiverMatMovers:= function(W)
    local   c;
    c:= CartanMatMovers(W);
    return c^0 - c^-1; # c = d^0 + d^1 + d2 + ... => d = 1 - 1/c.
end;


#############################################################################
##
##  Movers Plus as well
##
CartanMatMoversPlus:= function(W)
    local   bbb,  a,  l,  mat,  b,  i,  j;
    
    bbb:= List(Shapes(W), x-> Call(x, "Street"));
    for a in bbb do 
        Append(bbb, Call(a, "MoversPlus"));
    od;
    InfoZigzag1("Generated ", Length(bbb), " streets\n");
    
    l:= Length(Shapes(W));
    mat:= NullMat(l, l);
    for b in bbb do
        i:= Call(b, "Source");
        j:= Call(b, "Target");
        mat[i][j]:= mat[i][j] + 1;
    od;
    
    return mat;
end;

QuiverMatMoversPlus:= function(W)
    local   c;
    c:= CartanMatMoversPlus(W);
    return c^0 - c^-1; # c = d^0 + d^1 + d2 + ... => d = 1 - 1/c.
end;


#############################################################################
##
##  Movers Plus NonZero is not!!!  At least not for type A_n, n > 4; E_6.
##
CartanMatMoversPlusNZ:= function(W)
    local   bbb,  a,  l,  mat,  b,  i,  j;
    
    bbb:= List(Shapes(W), x-> Call(x, "Street"));
    for a in bbb do 
        Append(bbb, Call(a, "MoversPlus"));
    od;
    InfoZigzag1("Generated ", Length(bbb), " streets\n");
    bbb:= Filtered(bbb, x-> IsNonZero(Call(x, "Delta").mat));
    InfoZigzag1("Of which ", Length(bbb), " are nonzero streets\n");
    
    l:= Length(Shapes(W));
    mat:= NullMat(l, l);
    for b in bbb do
        i:= Call(b, "Source");
        j:= Call(b, "Target");
        mat[i][j]:= mat[i][j] + 1;
    od;
    
    return mat;
end;

QuiverMatMoversPlusNZ:= function(W)
    local   c;
    c:= CartanMatMoversPlusNZ(W);
    return c^0 - c^-1; # c = d^0 + d^1 + d2 + ... => d = 1 - 1/c.
end;

SpelledOutQuiver:= function(W)
    local   edg,  m,  lab,  ran,  i,  j;
    
    edg:= [];
    m:= DimensionsMatrix(QuiverRelations(W))[1];
    lab:= List(Shapes(W), s-> Call(s, "Label"));
    ran:= [1..Length(lab)];
    for i in ran do
        for j in ran do
            if m[i][j] > 0 then
                Add(edg, [lab[i], lab[j], m[i][j]]);
            fi;
        od;
    od;
    
    return edg;
end;


Negative:= function(matrix)
    local   new;
    
    new:= ShallowCopy(matrix);
    new.mat:= -new.mat;
    return new;    
end;

#############################################################################
##
##  A procedure to represent an alley as a sum of (iterated delta images)
##  of streets.
##
StreetsAlley:= function(W, alley)
    
    # FIXME:
    return true;
end;


#############################################################################
##
##  a product for streets forming a path ...
##
StreetProduct:= function ( abc )
    local  pro, i;
    pro := abc[1];
    for i  in [ 2 .. Length( abc ) ]  do
        pro := pro * abc[i];
        if Length( pro ) = 1  then
            pro := pro[1];
        else
            Error( "not yet implemented ..." );
        fi;
    od;
    return pro;
end;


#############################################################################
##
##  given a square matrix 'mat', determine the blocks of the equivalence
##  relation '-' generated by i - j if mat[i][j] <> 0.
##
BlocksMat:= function(mat)
    local   l,  list,  i,  j,  new,  k;
    
    l:= Length(mat);
    list:= List([1..l], i-> [i]);
    for i in [1..l] do
        for j in [1..l] do
            if i <> j and mat[i][j] <> 0 and list[i] <> list[j] then
                # join the blocks of i and j:
                new:= Union(list[i], list[j]);
                for k in new do
                    list[k]:= new;
                od;
            fi;
        od;
    od;
    return list;
end;


#############################################################################
#
#  dim is the result of DimensionsMatrix
#
ProjectiveModule:= function(dim, i)
    local   lis,  j;
    
    lis:= [0 * dim[1][1]];
    lis[1][i]:= 1;
    
    for j in [1..Length(dim)] do
        if IsNonZero(dim[j][i]) then
            Add(lis, dim[j][i]);
        fi;
    od;
            
    return lis;
end;

LaTeXProjectiveModule:= function(dim, nam, i)
    local   lis,  text,  j,  comma,  k;
    
    lis:= ProjectiveModule(dim, i);
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


ProjectiveResolution:= function(dim, i)
    local   sum,  car,  lis,  l,  new,  j;
        
    sum:= Sum(dim);
    car:= sum + sum^0;
    lis:= [];
    
    l:= 0 * sum[i];
    l[i]:= 1;

    while l <> 0*l do
        new:= 0*l;
        for j in Reversed([1..i]) do
            if l[j] > 0 then
                new[j]:= l[j];
                l:= l - l[j] * car[j];
            fi;
        od;
        Add(lis, new);
        l:= -l;
    od;
    
    return Reversed(lis);
end;


LaTeXProjectiveResolution:= function(dim, nam, i)
    local   lis,  text,  l,  comma,  k;
    
    lis:= ProjectiveResolution(dim, i);
    text:= "0 \\to ";
    
    for l in lis do
        Append(text, "P(");
        comma:= false;
        for k in [1..Length(l)] do
            if l[k] > 0 then
                if comma then
                    Append(text, "\\, \c");
                fi;
                if l[k] = 1 then
                    Append(text, nam[k]);
                else 
                    Append(text, "(");
                    Append(text, nam[k]);
                    Append(text, ")^{");
                    Append(text, String(l[k]));
                    Append(text, "}");
                fi;
                comma:= true;
            fi;
        od;
        Append(text, ") \\to ");
    od;
    Append(text, nam[i]);
    Append(text, " \\to 0");
        
    return text;
end;

   
