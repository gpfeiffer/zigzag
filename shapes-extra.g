#############################################################################
##
##  CollapsedIncMatShapes( <shapes> )  . . . .  collapsed incidence matrix.
##
##  returns the Condensed Inc Mat under conjugation ... ???
##
CollapsedIncMatShapes:= function(shapes)
    local   mat,  a,  row,  b;

    mat:= [];
    for a in shapes do
        row:= [];
        for b in shapes do
            Add(row, Number(Elements(b), x-> IsSubset(a.J, x)));
        od;
        Add(mat, row);
    od;
    return mat;
end;


#############################################################################
##
##  IncMatShapes
##
##  returns the number of orbits of pairs J < K
##
IncMatShapes:= function(shapes)
    local   mat,  a,  row,  nor,  b;

    mat:= [];
    for a in shapes do
        row:= [];
        nor:= Call(a, "Complement");
        for b in shapes do
            Add(row, Length(Orbits(nor, Filtered(Elements(b), x-> IsSubset(a.J, x)), OnSets)));
        od;
        Add(mat, row);
    od;
    return mat;
end;


InxMatShapes:= function(shapes)
    local   mat,  a,  row,  b;

    mat:= [];
    for a in shapes do
        row:= [];
        for b in shapes do
            Add(row, Number(Elements(b), x-> IsSubset(a.J, x)));
        od;
        Add(mat, row);
    od;
    return mat;
end;


FusMatShapes1:= function(shapes)
    local   mat,  a,  row,  nor,  b;

    mat:= [];
    for a in shapes do
        row:= [];
        nor:= Closure(ReflectionSubgroup(a.W, a.J), Call(a, "Complement"));
        for b in shapes do
            Add(row, Length(Orbits(nor, Filtered(Elements(b), x-> IsSubset(a.J, x)), OnSets)));
        od;
        Add(mat, row);
    od;
    return mat;
end;

FusMatShapes:= function(shapes)
    local   mat,  a,  row,  nor,  sub,  aaa,  b,  orb,  n;

    mat:= [];
    for a in shapes do
        row:= [];
        nor:= Call(a, "Complement");
        sub:= ReflectionSubgroup(a.W, a.J);
        aaa:= Shapes(sub);
        for b in shapes do
            orb:= Orbits(nor, Filtered(Elements(b), x-> IsSubset(a.J, x)), OnSets);
            orb:= List(orb, x-> Filtered(x, y-> IsSubset([1..a.W.semisimpleRank], y)));
            if orb = [] then
                n:= 0;
            else
                n:= Size(Set(List(orb, x-> Set(List(x, y-> PositionProperty(aaa, z-> y in z))))));
            fi;

            Add(row, n);
        od;
        Add(mat, row);
    od;
    return mat;
end;


#############################################################################
##
##  CollapsedFusMatShapes( <shapes> )  . . . . . . collapsed fusion matrix.
##
##  returns the Condensed Fus Mat under conjugation ... ???
##
CollapsedFusMatShapes:= function(shapes)
    local   mat,  a,  fus,  row,  i;

    mat:= [];
    for a in shapes do
        fus:= List(Shapes(ReflectionSubgroup(a.W, a.J)),
                   x-> PositionProperty(shapes, y-> IsSubset(y, x)));
        row:= List(shapes, x-> 0);
        for i in fus do
            row[i]:= row[i] + 1;
        od;
        Add(mat, row);
    od;
    return mat;
end;


#############################################################################
PrimeShapes:= function(W)
    return 0; ##FIXME
end;

