#############################################################################
##
#A  shapes.g                      Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2002, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: shapes.g,v 1.6 2002/11/22 13:23:33 goetz Exp $
##
##  This file contains the routines for shapes of Coxeter groups.
##
##  Let $(W,  S)$ be a  Coxeter system.  A  *shape* of $W$ is  an equivalence
##  class of subsets of $S$  where the equivalence is defined via conjugation
##  in  $W$.  Shapes  thus parameterize  the conjugacy  classes  of parabolic
##  subgroups of $W$.
##
RequirePackage("chevie");
RequirePackage("monoid");

#############################################################################
##
#F  InfoZigzag? . . . . . . . . . . . . . . . . . . . . . . . info functions.
##
if not IsBound(InfoZigzag1) then InfoZigzag1:= Ignore; fi;
if not IsBound(InfoZigzag2) then InfoZigzag2:= Ignore; fi;

#############################################################################
##  
#O  ShapeOps . . . . . . . . . . . . . . . . . . . . . . . operations record.
##  
ShapeOps:= OperationsRecord("ShapeOps", DomainOps);

#############################################################################
##  
#C  Shape( <W>, <J> ) . . . . . . . . . . . . . . . . . . . . .  constructor.
#C  Shape( <W>, <WJ> )  . . . . . . . . . . . . . . . . . . . .  constructor.
#C  Shape( <W>, <w> ) . . . . . . . . . . . . . . . . . . . . .  constructor.
##  
##  returns an object that represents the shape of <J> in the Coxeter group 
##  <W>.
##
##  public fields:
##    W, the Coxeter group.
##    J, the parabolic subset of S.
##  
Shape:= function(W, J)
    local this;
    this:= rec(operations:= ShapeOps);
    this.isDomain:= true;  
    this.W:= W;  this.J:= J;
    return this;
end;


#############################################################################  
##  
#F  Print( <shape> ) . . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
ShapeOps.Print:= function(this)
    Print("Shape( ", this.W, ", ", this.J, " )");
end;


#############################################################################
##
#F  Representative( <shape> ) . . . . . . . . . . . . . . . . representative.
##
##  A shape, as a class of parabolic subsets, has a representative.
##
ShapeOps.Representative:= function(this)
    return this.J;
end;


#############################################################################  
##  
#F  Elements( <shape> ) . . . . . . . . . . . . . . . . . . . . . . elements.
##  
##  returns the set of members of a Coxeter class
##  in the form of subsets of S, sorted lexicographically. 
##
##  This function implements the Lusztig-Spaltenstein Theorem [GP 2.3.3].
##  That makes it much (!!) faster than simple conjugacy tests!!
##
ShapeOps.Elements:= function(this)
    local   W,  S,  onParabolics,  orbit,  transversal,  edges,  k,  
            l,  a,  i,  b,  pos,  perm, wM;
    
    # get the Coxeter System (W, S) to work in.
    W:= this.W;  S:= W.rootInclusion{[1..W.semisimpleRank]};
    
    # how to determine the image of $J \subseteq S$ under a generator.
    # Given $J \subseteq S$ and $i \in S \setminus J$, determine
    # the image $K$ of $J$
    # under the longest element of the parabolic to $J \cup \{i\}.
    # The function assumes $i \notin J$ and will not test this.
    # Note how the action of W on the roots is used:
    # By theory $J$ is mapped to a subset of $S$, represented by $[1..n]$
    # and their negatives $[1..n]+N$. 
    # Mod by $N$ takes everything back into $[0..n-1]$.
    onParabolics:= function(J, i)
        wM:= LongestCoxeterElement(ReflectionSubgroup(W, Union(J, [i])));
        return List(OnSets(J, wM), x-> (x-1) mod W.parentN + 1);
    end;
    
    # extended orbit algorithm.
    orbit:= [this.J];  transversal:= [()];  edges:= [];  k:= 0;  l:= 1;
    for a in orbit do
        k:= k+1;  edges[k]:= [];
        for i in Difference(S, a) do 
            b:= onParabolics(a, i);  pos:= Position(orbit, b);
            if pos = false then
                Add(orbit, b);
                Add(transversal, transversal[k] * wM);
                l:= l+1;  pos:= l;
            fi;
            edges[k][i]:= rec(v:= pos, w:= wM);
        od;
    od;
    
    # sort orbit lexicographically and keep transversal, edges in sync.
    perm:= Sortex(orbit);
    this.transversal:= Permuted(transversal, perm);
    edges:= Permuted(edges, perm);
    for a in edges do
        for i in [1..Length(a)] do
            if IsBound(a[i]) then a[i].v:= a[i].v^perm; fi;
        od;
    od;
    this.edges:= edges;
    this.root:= 1^perm;
    
    return orbit;
end;


#############################################################################
##
#F  ShapeOps.Transversal( <shape> )  . . . . . . . . . . . . . . transversal.
##
ShapeOps.Transversal:= function(this)
    this.operations.Elements(this);  # expand the shape.
    return this.transversal;
end;


#############################################################################
##
#F  ShapeOps.Edges( <shape> ) . . . . . . . . . . . . . . . . . . . .  edges.
##
ShapeOps.Edges:= function(this)
    this.operations.Elements(this);  # expand the shape.
    return this.edges;
end;


#############################################################################  
##  
#F  Display( <shape> ) . . . . . . . . . . . . . . . . . . . . . . . display.
##  
ShapeOps.Display:= function(this, options)
    
    # determine name, if necessary.
    if not IsBound(this.name) then
        this.name:= CartanName(ReflectionSubgroup(this.W, this.J));
        if this.name = "" then this.name:= "1"; fi;  # trivial subgroup.
    fi;
    
    Print(this.name, " [", Size(this), "]");
end;


#############################################################################
##
#F  NormalizerShape( <W>, <J> ) . . . . . . . . . . . . . . . . . normalizer.
##
##  returns $X_{JJJ}$ as a group generated by the eyes and ears of the shape.
##  The normalizer of $W_J$ in $W$ is the semidirect product of $W_J$ and
##  $X_{JJJ}$.  
##
##  The group returned has extra fields 'ears' and 'eyes' that contain these
##  lists of generators.  The 'ears' alone generate a Coxeter group (see
##  Howlett 1980, and Brink-Howlett 1999).  The latter describes the eyes and
##  ears as 'movers' and 'shakers'.
##
NormalizerShape:= function(W, J)
    local   shape,  edges,  t,  eyes,  ears,  i,  e,  j,  nor;
    
    shape:= Shape(W, J);
    edges:= shape.operations.Edges(shape);  
    t:= shape.operations.Transversal(shape);
    eyes:= [];  ears:= [];  i:= 0;
    for e in edges do
        i:= i+1;
        for j in [1..Length(e)] do
            if IsBound(e[j]) then
                if e[j].v = i then
                    AddSet(ears, t[i] * e[j].w / t[i]);
                else
                    AddSet(eyes, t[i] * e[j].w / t[e[j].v]);
                fi;
            fi;
        od;
    od;
    
    nor:= Subgroup(W, Union(ears, eyes));
    nor.ears:= ears;  nor.eyes:= eyes;
    return nor;
end;

#############################################################################
##
#F  RelationShape( <W>, <J> ) . . . . . . . . . . . . . . . . . . . relation.
##
##  returns the underlying directed graph of the shape as a binary relation.
##
RelationShape:= function(W, J)
    local   shape,  list;
    shape:= Shape(W, J);
    list:= List(shape.operations.Edges(shape), Set);
    return Relation(List(list, x-> List(x, y-> y[1])));
end;


#############################################################################
##
#F  ConjugacyClasses( <shape> )  . . . . . . . . . . . . . conjugacy classes.
##
##  returns the list of addresses of conjugacy
##  classes of elements of $W$ of the corresponding shape.
##
ShapeOps.ConjugacyClasses:= function(this)
    local   W,  cc;

    W:= this.W;  cc:= ConjugacyClasses(W);
    
    # this relies on the representative of c to be of minimal length!
    return Filtered([1..Length(cc)], 
                   i-> Set(CoxeterWord(W, Representative(cc[i]))) in this);
end;


##  TODO: Shapes(W) should return the list of shapes (as list) and store it
##  in W.

#############################################################################
##  
#O  ShapesOps . . . . . . . . . . . . . . . . . . . . . .  operations record.
##  
##  Warning: Shapes is not a domain/set.
##
ShapesOps:= OperationsRecord("ShapesOps");

#############################################################################
##  
#C  Shapes( <W> ) . . . . . . . . . . . . . . . . . . . . . . .  constructor.
##  
##  returns an object that represents the shapes of the Coxeter group <W>.
##  
##  contains: a list of subsets of [1..n], sorted by rank, index, conjugacy;
##            a list of Coxeter classes;
##      and the mapping of conjugacy classes of elements to Coxeter classes.
##
##  public fields:
##    W, the Coxeter group.
##  
Shapes:= function(W)
    local   this;
    this:= rec(operations:= ShapesOps);
    this.W:= W; 
    return this;
end;

#############################################################################  
##  
#F  Print( <shapes> ) . . . . . . . . . . . . . . . . . . . . . . . .  print.
##  
ShapesOps.Print:= function(this)
    Print("Shapes( ", this.W, " )");
end;

#############################################################################  
##  
#F  Constituents( <shapes> ) . . . . . . . . . . . . . . . . .  constituents.
##  
##  returns a list of Coxeter classes; each class consisting of its members
##  in the form of subsets of S, sorted lexicographically. The classes are
##  sorted by rank, and within each rank by the size of the parabolic
##  subgroup.
##
ShapesOps.Constituents:= function(this)
    local   W,  S,  shapes,  l,  d,  sh,  pos;
    
    # get the Coxeter System (W, S) to work in.
    W:= this.W;  S:= W.rootInclusion{[1..W.semisimpleRank]};
    
    # initialize.
    shapes:= [];

    # loop over all possible ranks l.  
    for l in [0..Length(S)] do 
        d:= Combinations(S, l);

        # sort 'd' wrt size.
        Sort(d, function(a, b) return 
          Size(ReflectionSubgroup(W, a)) < Size(ReflectionSubgroup(W, b)); 
        end);

        # orbits algorithm.
        while d <> [] do
            sh:= Shape(W, d[1]);
            pos:= List(Elements(sh), x-> Position(d, x));
            d:= d{Difference([1..Length(d)], pos)};
            Add(shapes, sh);
        od;
    od;

    return shapes;
end;


#############################################################################
##
#F  SubsetsShapes( <shapes> ) . . . . . . . . . . . . . . . . .  subsets.
##
##  returns a list of lists, one for every shape, of addresses of conjugacy
##  classes of elements of $W$ of the corresponding shape.
##
SubsetsShapes:= function(shapes)
    return Concatenation(List(Constituents(shapes), Elements));
end;


#############################################################################
##
#F  IncidenceMatShapes( <shapes> ) . . . . . . . . . . .  incidence matrix.
##
##  returns a $2^n \times 2^n$ matrix of $0$s and $1$s describing the
##  containment of subsets in each other wrt to the list returned by
##  'Subsets'.
##
##  This matrix serves as the base change matrix X -> Y.
##
IncidenceMatShapes:= function(shapes)
    local   subsets,  inc,  a,  l,  b;
    
    subsets:= SubsetsShapes(shapes);
    inc:= [];
    for a in subsets do 
        l:= [];
        for b in subsets do 
            if IsSubset(b, a) then Add(l, 1); else Add(l, 0); fi; 
        od;
        Add(inc, l);
    od;

    return inc;
end;


#############################################################################
##
##  CollapsedIncMatShapes( <shapes> )  . . . .  collapsed incidence matrix.
##
##  returns the Condensed Inc Mat under conjugation ... ???
##
CollapsedIncMatShapes:= function(shapes)
    local   mat,  a,  J,  row,  b;
    
    shapes:= Constituents(shapes);
    mat:= [];
    for a in shapes do
        J:= Representative(a);
        row:= [];
        for b in shapes do
            Add(row, Number(Elements(b), x-> IsSubset(J, x)));
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
    local   el,  mat,  a,  el1,  fus,  row,  i;
    
    el:= Constituents(shapes);
    mat:= [];
    for a in el do
        el1:= Constituents(Shapes(ReflectionSubgroup(a.W, a.J)));        
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
#F  Display( <shapes> ) . . . . . . . . . . . . . . . . . . . . . .  display.
##
##  display the Shapes object as a list of types with multiplicities.
##
ShapesOps.Display:= function(this, options)
    local   el,  i;
    
    el:= Constituents(this);
    Display(el[1]);
    for i in [2.. Length(el)] do
        Print(", ");
        Display(el[i]);
    od;
end;


#############################################################################
##
##  XCharacters( <W> ) . . . . . . . . . . . . . . . . . . . . .  characters.
##
##  returns the list of parabolic permutation characters of W.
##
XCharacters:= function(W)
    local   pch,  ct,  lambda,  sub,  cts,  fus;
    
    # initialize list of permchars.
    pch:= [];
    ct:= CharTable(W);
    
    # loop over classes of parabolics.
    for lambda in Constituents(Shapes(W)) do
        sub:= ReflectionSubgroup(W, Representative(lambda));
        InfoZigzag2("CharTable of ...");
        cts:= CharTable(sub);
        InfoZigzag2(cts.name, "\n");
        fus:= FusionConjugacyClasses(sub, W);
        Add(pch, Induced(cts, ct, [0*cts.classes+1], fus)[1]);
    od;
    
    return pch;
end;

#############################################################################
##
##  YCharacters( <W> ) . . . . . . . . . . . . . . . . . . . . .  characters.
##
##  returns the list of PIE stripped permutation characters of W, one
##  character for each subset $J \subseteq S$, sorted in the same order as the
##  'Subsets'.
##
YCharacters:= function(W)
    local   shapes,  lll,  iii,  i;

    shapes:= Shapes(W);
    
    # make an address book:
    lll:= List(Constituents(shapes), Size);
    iii:= [];
    for i in [1..Length(lll)] do
        Append(iii, 0 * [1..lll[i]] + i); 
    od;

    return IncidenceMatShapes(shapes)^-1 * XCharacters(W){iii};
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
