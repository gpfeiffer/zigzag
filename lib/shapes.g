#############################################################################
##
#A  shapes.g                      Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2002, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: shapes.g,v 1.1 2002/05/07 17:10:40 goetz Exp $
##
##  This file contains the routines for shapes of Coxeter groups.
##
##  Let $(W, S)$ be a Coxeter system.  A *shape* of $W$ is an equivalence
##  class of
##  subsets of $S$ where the equivalence is defined via conjugation in
##  $W$.
##
RequirePackage("chevie");


#############################################################################
##  
#O  ShapesOps  
##  
ShapesOps:= OperationsRecord("ShapesOps", DomainOps);

#############################################################################
##  
#F  Shapes( <W> ) . . . . . . . . . . . . . . . . . . . . . . .  constructor.
##  
##  returns an object that represents the shapes of the Coxeter group <W>.
##  
##  contains: a list of subsets of [1..n], sorted by rank, index, conjugacy;
##            a list of Coxeter classes;
##      and the mapping of conjugacy classes of elements to Coxeter classes.
##  
Shapes:= function(W)
    local   this;
    
    this:= rec();
    this.isDomain:= true;
    this.W:= W;
    this.operations:= ShapesOps;    
    return this;
end;

#############################################################################  
##  
##  ShapesOps.Print( <shapes> )
##  
ShapesOps.Print:= function(shapes)
    Print("Shapes( ", shapes.W, " )");
end;

#############################################################################  
##  
#F  ShapesOps.Elements( <shapes> )  
##  
##  a list of coxeter classes; administrative information.
##  Algorithm: Lusztig-Spaltenstein.  Is much(!!) faster than
##  simple conjugacy tests!!
##
ShapesOps.Elements:= function(shapes)
    local   W,  onParabolics,  S,  elms,  l,  d,  orbit,  a,  i,  b,  
            pos;
    
    W:= shapes.W;
    
    # Given J subset S and i in S \ J, determine the image K of J
    # under the longest element of the parabolic to J add i.
    # the function assumes i notin J and will not test this.
    # Note how the action of W on the roots is used:
    # By theory J is mapped to a subset of S, represented by [1..n]
    # and their negatives [1..n]+N. 
    # Mod by N takes everything back into [0..n-1].
    onParabolics:= function(J, i)
        local w;
        w:= LongestCoxeterElement(ReflectionSubgroup(W, Union(J, [i])));
        return List(OnSets(J, w), x-> ((x-1) mod W.parentN)+1);
    end;

    S:= W.rootInclusion{[1..W.semisimpleRank]};

    # trivial case first.
    elms:= [[[]]];

    # loop over all possible ranks > 0.  
    for l in [1..Length(S)] do 
        d:= Combinations(S, l);

        # sort 'd' wrt size.
        Sort(d, function(a, b) return Size(ReflectionSubgroup(W, a)) < Size(ReflectionSubgroup(W, b)); end);

        # orbits algorithm.
        while d <> [] do
            orbit:= [d[1]]; 
            for a in orbit do
                for i in Difference(S, a) do 
                    b:= onParabolics(a, i);
                    if not b in orbit then
                        Add(orbit, b);
                    fi;
                od;
            od;
            pos:= List(orbit, x-> Position(d, x));
            d:= d{Difference([1..Length(d)], pos)};
            Sort(orbit);
            Add(elms, orbit);
        od;
    od;

    return elms;
end;

##  
##  braucht's das "uberhaupt???
##  
ShapesOps.Subsets:= function(shapes)
    return Concatenation(Elements(shapes));
end;

#############################################################################
##
#F  ConjugacyClasses( <shapes> )
##
##  returns a list of lists, one for every shape, of addresses of 
##  conjugacy classes of elements of $W$ of the corresponding shape.
##
ShapesOps.ConjugacyClasses:= function(shapes)
    local   W,  ccc,  cpos,  classes,  c,  J,  i;

    W:= shapes.W;

    ccc:= Elements(shapes);
    cpos:= []; classes:= List(ccc, x-> []);
    for c in ConjugacyClasses(W) do
        
        # this relies on the representative of c to be of minimal length!
        J:= Set(CoxeterWord(W, Representative(c)));
        i:= PositionProperty(ccc, x-> J in x);
        Add(cpos, i);  Add(classes[i], Length(cpos));
    od;

    return classes;
end;


##  base change x -> y;
ShapesOps.IncidenceMat:= function(shapes)
    local   subsets,  bbb,  a,  l,  b;

    subsets:= ShapesOps.Subsets(shapes);    
    bbb:= [];
    for a in subsets do 
        l:= [];
        for b in subsets do 
            if IsSubset(b, a) then Add(l, 1); else Add(l, 0); fi; 
        od;
        Add(bbb, l);
    od;

    return bbb;
end;



##  Condensed Inc Mat under conjugation ... ???
ShapesOps.CollapsedIncMat:= function(shapes)
    local   el,  mat,  a,  row,  b;
    
    el:= Elements(shapes);
    mat:= [];
    for a in el do
        row:= [];
        for b in el do
            Add(row, Number(b, x-> IsSubset(a[1], x)));
        od;
        Add(mat, row);
    od;
    return mat;
end;

ShapesOps.CollapsedFusMat:= function(shapes)
    local   el,  mat,  a,  el1,  fus,  row,  i;
    
    el:= Elements(shapes);
    mat:= [];
    for a in el do
        el1:= Elements(Shapes(ReflectionSubgroup(shapes.W, a[1])));        
        fus:= List(el1, x-> PositionProperty(el, y-> IsSubset(y, x)));
        row:= List(el, x-> 0);
        for i in fus do
            row[i]:= row[i] + 1;
        od;
        Add(mat, row);
    od;
    return mat;
end;


#############################################################################
##
#F  Display( <shapes> )
##
ShapesOps.Display:= function(shapes, options)
    local   e,  WJ;
    
    for e in Elements(shapes) do
        WJ:= ReflectionSubgroup(shapes.W, e[1]);
        Print(CartanName(WJ), ": ", Length(e), ";\n");
    od;
    
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
