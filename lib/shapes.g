#############################################################################
##
#A  shapes.g                      Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2002, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: shapes.g,v 1.5 2002/11/19 20:50:15 goetz Exp $
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
#F  Elements( <shape> ) . . . . . . . . . . . . . . . . . . . . . . elements.
##  
##  returns the list of members of a Coxeter class
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
ShapeOps.Transversal:= function(this)
    this.operations.Elements(this);
    return this.transversal;
end;

#############################################################################
ShapeOps.Edges:= function(this)
    this.operations.Elements(this);
    return this.edges;
end;

#############################################################################
# TODO: Is this reflection subgroup safe?
NormalizerShape:= function(W, J)
    local   shape,  edges,  t,  movers,  shakers,  i,  e,  j,  nor;
    
    shape:= Shape(W, J);
    edges:= shape.operations.Edges(shape);  
    t:= shape.operations.Transversal(shape);
    movers:= [];  shakers:= [];  i:= 0;
    for e in edges do
        i:= i+1;
        for j in [1..Length(e)] do
            if IsBound(e[j]) then
                if e[j].v = i then
                    AddSet(shakers, t[i] * e[j].w / t[i]);
                else
                    AddSet(movers, t[i] * e[j].w / t[e[j].v]);
                fi;
            fi;
        od;
    od;
    
    nor:= Subgroup(W, Difference(Union(shakers, movers), [()]));
    nor.shakers:= shakers;
    nor.movers:= movers;
    return nor;
end;

#############################################################################
# TODO: Is this reflection subgroup safe?
RelationShape:= function(W, J)
    local   shape,  list;
    shape:= Shape(W, J);
    list:= List(shape.operations.Edges(shape), Set);
    return Relation(List(list, x-> List(x, y-> y[1])));
end;


#############################################################################
##  
#O  ShapesOps . . . . . . . . . . . . . . . . . . . . . .  operations record.
##  
ShapesOps:= OperationsRecord("ShapesOps", DomainOps);

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
##    isDomain, true, so all the set functions apply.
##  
Shapes:= function(W)
    local   this;
    this:= rec(operations:= ShapesOps);
    this.isDomain:= true;  
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
#F  Elements( <shapes> ) . . . . . . . . . . . . . . . . . . . . .  elements.
##  
##  returns a list of Coxeter classes; each class consisting of its members
##  in the form of subsets of S, sorted lexicographically. The classes are
##  sorted by rank, and within each rank by the size of the parabolic
##  subgroup.
##
ShapesOps.Elements:= function(this)
    local   W,  S,  elms,  l,  d,  orbit,  pos;
    
    # get the Coxeter System (W, S) to work in.
    W:= this.W;  S:= W.rootInclusion{[1..W.semisimpleRank]};

    # trivial case first: rank = 0.
    elms:= [[[]]];

    # loop over all possible ranks l > 0.  
    for l in [1..Length(S)] do 
        d:= Combinations(S, l);

        # sort 'd' wrt size.
        Sort(d, function(a, b) return 
          Size(ReflectionSubgroup(W, a)) < Size(ReflectionSubgroup(W, b)); 
        end);

        # orbits algorithm.
        while d <> [] do
            orbit:= Elements(Shape(W, d[1]));
            pos:= List(orbit, x-> Position(d, x));
            d:= d{Difference([1..Length(d)], pos)};
            Add(elms, orbit);
        od;
    od;

    return elms;
end;

#############################################################################
##
#F  Subsets( <shapes> ) . . . . . . . . . . . . . . . . . . . . . .  subsets.
##  
##  returns the complete list of subsets of S, in an order compatible with
##  the shapes.
##
##  braucht's das "uberhaupt???
##  
ShapesOps.Subsets:= function(this)
    return Concatenation(Elements(this));
end;

#############################################################################
##
#F  ConjugacyClasses( <shapes> ) . . . . . . . . . . . . . conjugacy classes.
##
##  returns a list of lists, one for every shape, of addresses of conjugacy
##  classes of elements of $W$ of the corresponding shape.
##
ShapesOps.ConjugacyClasses:= function(this)
    local   W,  ccc,  cpos,  classes,  c,  J,  i;

    W:= this.W;

    ccc:= Elements(this);
    cpos:= []; classes:= List(ccc, x-> []);
    for c in ConjugacyClasses(W) do
        
        # this relies on the representative of c to be of minimal length!
        J:= Set(CoxeterWord(W, Representative(c)));
        i:= PositionProperty(ccc, x-> J in x);
        Add(cpos, i);  Add(classes[i], Length(cpos));
    od;

    return classes;
end;

#############################################################################
##
#F  ShapesOps.IncidenceMat( <this> ) . . . . . . . . . . .  incidence matrix.
##
##  returns a $2^n \times 2^n$ matrix of $0$s and $1$s describing the
##  containment of subsets in each other wrt to the list returned by
##  'Subsets'.
##
##  This matrix serves as the base change matrix X -> Y.
##
ShapesOps.IncidenceMat:= function(this)
    local   subsets,  inc,  a,  l,  b;

    subsets:= this.operations.Subsets(this);    
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
##  ShapesOps.CollapsedIncMat( <this> )  . . . .  collapsed incidence matrix.
##
##  returns the Condensed Inc Mat under conjugation ... ???
##
ShapesOps.CollapsedIncMat:= function(this)
    local   el,  mat,  a,  row,  b;
    
    el:= Elements(this);
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



#############################################################################
##
##  ShapesOps.CollapsedFusMat( <this> )  . . . . . . collapsed fusion matrix.
##
##  returns the Condensed Fus Mat under conjugation ... ???
##
ShapesOps.CollapsedFusMat:= function(this)
    local   el,  mat,  a,  el1,  fus,  row,  i;
    
    el:= Elements(this);
    mat:= [];
    for a in el do
        el1:= Elements(Shapes(ReflectionSubgroup(this.W, a[1])));        
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
    local   e,  WJ,  el;
    
    # determine names, if necessary.
    if not IsBound(this.name) then
        this.name:= [];
        for e in Elements(this) do
            WJ:= ReflectionSubgroup(this.W, e[1]);
            Add(this.name, CartanName(WJ));
        od;
    fi;
    
    el:= Elements(this);
    
    for e in [1..Length(el)] do
        Print(this.name[e], " [", Length(el[e]), "], ");
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
    for lambda in Elements(Shapes(W)) do
        sub:= ReflectionSubgroup(W, lambda[1]); 
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
##  character for each subset $J \subseeq S$, sorted in the same order as the
##  'Subsets".
##
YCharacters:= function(W)
    local   shapes,  lll,  iii,  i;

    shapes:= Shapes(W);
    
    # make an address book:
    lll:= List(Elements(shapes), Length);
    iii:= [];
    for i in [1..Length(lll)] do
        Append(iii, 0 * [1..lll[i]] + i); 
    od;

    return ShapesOps.IncidenceMat(shapes)^-1 * XCharacters(W){iii};
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
