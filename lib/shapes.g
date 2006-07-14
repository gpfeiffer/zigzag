#############################################################################
##
#A  shapes.g                      Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2004, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: shapes.g,v 1.37 2006/07/14 15:23:24 goetz Exp $
##
##  This file contains the routines for shapes of Coxeter groups.
##
##  <#GAPDoc Label="Intro:Shapes">
##    Let </M>(W, S)</M> be a Coxeter system.  A <E>shape</E> of </M>W</M> is
##    an equivalence class of subsets of </M>S</M> where the equivalence is
##    defined via conjugation in </M>W</M>.  Shapes thus parameterize the
##    conjugacy classes of parabolic subgroups of </M>W</M>.
##  <#/GAPDoc>
##

#############################################################################
##  
#O  ShapeOps . . . . . . . . . . . . . . . . . . . . . . . operations record.
##  
ShapeOps:= OperationsRecord("ShapeOps", DomainOps);


#############################################################################
##  
#C  Shape( <W>, <J> ) . . . . . . . . . . . . . . . . . . . . .  constructor.
##  
##  <#GAPDoc Label="Shape">
##  <ManSection>
##  <Func Name="Shape" Arg="W, J"/>
##  <Returns>
##    a new shape, an object that represents the shape of <A>J</A> in 
##    <A>W</A>. 
##  </Returns>
##  <Description>
##  This is the simple constructor for the shape class.  It constructs and
##  returns the shape of <A>J</A> in <A>W</A>.  Here <A>W</A> is a finite
##  Coxeter group of rank <M>n</M> and <A>J</A> is a subset of
##  <M>[1..n]</M>.
##  <Example>
##  gap> W:= CoxeterGroup("E", 6);; 
##  gap> Shape(W, [1, 2, 3]);
##  Shape( CoxeterGroup("E", 6), [ 1, 2, 3 ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  public fields:
##    W, the Coxeter group.
##    J, the parabolic subset of S.
##  
Shape:= function(W, J)
    return 
      rec(
          isDomain:= true,
          isShape:= true,
          operations:= ShapeOps,
          W:= W,
          J:= J
          );
end;


#############################################################################
##
#F  IsShape( <obj> )  . . . . . . . . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsShape">
##  <ManSection>
##  <Func Name="IsShape" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a shape and <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsShape:= function(obj)
    return IsRec(obj) and IsBound(obj.isShape) and obj.isShape = true;
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
##  <#GAPDoc Label="Representative(shape)">
##  <ManSection>
##  <Meth Name="Representative" Arg="shape" Label="for shapes"/>
##  <Returns>a representative of the shape <A>shape</A>.</Returns>
##  <Description>The representative of a shape constructed 
##  as <C>Shape(W, J)</C> (see <Ref Label="Shape"/>) will be its
##  initial element <C>J</C>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> Representative(Shape(W, [2]));
##  [ 2 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
ShapeOps.Representative:= function(this)
    return this.J;
end;


#############################################################################
##
#F  Rank( <shape> ) . . . . . . . . . . . . . . . . . . . . . . . . . . rank.
##
##  The rank of a shape is the size of its elements.
##
##  <#GAPDoc Label="Rank(shape)">
##  <ManSection>
##  <Meth Name="Rank" Arg="shape" Label="for shapes"/>
##  <Returns>the rank  of the shape <A>shape</A>.</Returns>
##  <Description>
##    The rank of a shape is the common size of its elements.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> List(Shapes(W), Rank);
##  [ 0, 1, 2, 2, 3 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
ShapeOps.Rank:= function(this)
    return Size(this.J);
end;


#############################################################################  
##  
#F  Elements( <shape> ) . . . . . . . . . . . . . . . . . . . . . . elements.
##  
##  <#GAPDoc Label="Elements(shape)">
##  <ManSection>
##  <Meth Name="Elements" Arg="shape" Label="for shapes"/>
##  <Returns>
##    the set of elements of the shape <A>shape</A>.
##  </Returns>
##  <Description>
##  The shape of <M>J</M> in <M>W</M> consists of all subsets of <M>S</M>
##  which are conjugate to <M>J</M> under <M>W</M>.
##  The conjugates can be efficiently computed
##  using <Cite Key="GePf2000" Where="Theorem 2.3.3"/>.
##  This is much faster than simple conjugacy tests.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> Elements(Shape(W, [2]));
##  [ [ 1 ], [ 2 ], [ 3 ] ] 
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ShapeOps.Elements:= function(this)
    local   W,  S,  K,  L, onParabolics,  orbit,  transversal,  edges,  k,  
            l,  i,  pos,  perm, d, e;

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
        d:= LongestCoxeterElement(ReflectionSubgroup(W, J)) * 
            LongestCoxeterElement(ReflectionSubgroup(W, Union(J, [i])));
        return Set(List(OnSets(J, d), x-> (x-1) mod W.parentN + 1));
    end;

    # extended orbit algorithm.
    orbit:= [this.J];  transversal:= [()];  edges:= [];  k:= 0;  l:= 1;
    for K in orbit do
        k:= k+1;  edges[k]:= [];
        for i in Difference(S, K) do 
            L:= onParabolics(K, i);  pos:= Position(orbit, L);
            if pos = false then
                Add(orbit, L);
                Add(transversal, transversal[k] * d);
                l:= l+1;  pos:= l;
            fi;
            edges[k][i]:= rec(v:= pos, d:= d);
        od;
    od;

    # sort orbit lexicographically and keep transversal, edges in sync.
    perm:= Sortex(orbit);
    this.transversal:= Permuted(transversal, perm);
    edges:= Permuted(edges, perm);
    for e in edges do
        for i in [1..Length(e)] do
            if IsBound(e[i]) then e[i].v:= e[i].v^perm; fi;
        od;
    od;
    this.edges:= edges;
    this.root:= 1^perm;  ##  the position of J in the list.

    return orbit;
end;

#############################################################################
##
#F  <l> = <r>  . . . . . . . . . . . . . . . . . . . . . . . . equality test.
##
ShapeOps.\= := function(l, r)
    return l.W = r.W and l.J in r;
end;

#############################################################################
##
#F  <l> < <r>  . . . . . . . . . . . . . . . . . . . . . . . . .  comparison.
##
ShapeOps.\< := function(l, r)
    if not IsShape(l) then return false; fi;
    if not IsShape(r) then return false; fi;
    return l.W < r.W or l.W = r.W and Elements(l) < Elements(r);
end;


#############################################################################
##
#F  ShapeOps.Edges( <shape> ) . . . . . . . . . . . . . . . . . . . .  edges.
##
##  <#GAPDoc Label="Edges(shape)">
##  <ManSection>
##  <Meth Name="Edges" Arg="shape" Label="for shapes"/>
##  <Meth Name="ShapeOps.Edges" Arg="shape"/>
##  <Returns>
##    the list of edges of the graph formed by the elements of the shape 
##    <A>shape</A>.
##  </Returns>
##  <Description>
##    The elements of a shape form the vertices of a directed graph.  The
##    <E>edges</E> of a shape are the edges of this graph and they are
##    defined as follows.  Let <M>J</M> be an element of the shape and let
##    <M>s \in S \setminus J</M>.  Let <M>M = J \cup \{s\}</M> and let <M>w
##    \in W</M> be the longest element of the parabolic subgroup <M>W_M</M>.
##    Then <M>J^w</M> is a subset of <M>M</M> and thus an element of the
##    shape.  In the graph, this yields and edge from <M>J</M> to <M>J^w</M>
##    with labels <M>s</M> and <M>w</M>.<P/>
##
##    The function 'Edges' returns all these edges in the form of a list of
##    lists, with one list for every vertex (element <M>J</M> of the shape).
##    The entries in the list for <M>J</M> correspond to the generators <M>s
##    \in S</M> with unbound entries for <M>s \in J</M>.  In the other cases
##    the list element is a record with components |v| and |w|, where |v|
##    gives the address of <M>J^w</M> in the list of elements, and where |w|
##    gives the permutation <M>w</M>.<P/>
##  
##    <C>ShapeOps.Edges(shape)</C> returns a list of lists <C>l</C> with
##    <C>l[i][k]</C> bound to a record <C>r</C> if vertex <C>i</C> is the
##    initial vertex of a directed edge with label <C>k</C>.  In that case
##    the record <C>r</C> has two components, <C>v</C> for the (address of
##    the) terminal vertex of the edge and <C>d</C> for the conjugating
##    element $d_J^M = w_J w_M \in W$ that maps the intial vertex to the
##    terminal vertex.
##  <Example>
##  gap> W:= CoxeterGroup("A", 2);;
##  gap> sh:= Shape(W, [1]);;
##  gap> Call(sh, "Edges");
##  [ [ , rec(
##            v := 2,
##            d := (1,2,6)(3,4,5) ) ], [ rec(
##            v := 1,
##            d := (1,6,2)(3,5,4) ) ] ]
##  </Example>
##    The edges of a shape are constructed together with the list of elements
##    of <A>shape</A> (see <Ref Meth="Elements" Label="for shapes"/>).
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
ShapeOps.Edges:= function(this)
    # (delete) this.operations.Elements(this);  # expand the shape.
    Call(this, "Elements");  # expand the shape.
    return this.edges;
end;


#############################################################################
##
#F  ShapeOps.Transversal( <shape> )  . . . . . . . . . . . . . . transversal.
##
##  <#GAPDoc Label="Transversal(shape)">
##  <ManSection>
##  <Meth Name="Transversal" Arg="shape" Label="for shapes"/>
##  <Meth Name="ShapeOps.Transversal" Arg="shape"/>
##  <Returns>
##    a transversal of the graph formed by the elements of the shape 
##    <A>shape</A>.
##  </Returns>
##  <Description>
##    The <E>transversal</E> <Index>transversal</Index> of the shape of
##    <M>J</M> in <M>W</M> is a list of elements of <M>W</M>, with the
##    property that the <M>i</M>th element of the list maps <M>J</M> under
##    conjugation to the <M>i</M>th element of the shape.  Note that <M>J</M>
##    need not be the first element in the shape.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> sh:= Shape(W, [2]);
##  Shape( CoxeterGroup("A", 3), [ 2 ] )
##  gap> Elements(sh);
##  [ [ 1 ], [ 2 ], [ 3 ] ]
##  gap> Call(sh, "Transversal");
##  [ ( 1,10, 2)( 3, 5, 6)( 4, 8, 7)( 9,11,12), (),
##    ( 1, 4, 6)( 2, 3,11)( 5, 8, 9)( 7,10,12) ]
##  </Example>
##    The transversal of a shape is constructed together with the list of
##    elements of <A>shape</A> (see <Ref Meth="Elements" Label="for
##    shapes"/>).
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##    
ShapeOps.Transversal:= function(this)
    Call(this, "Elements");  # expand the shape.
    return this.transversal;
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
#F  ShapeOps.Complement( <shape> )  . . . . . . . . . . . . . . . complement.
##
##  <#GAPDoc Label="Complement(shape)">
##  <ManSection>
##  <Meth Name="Complement" Arg="shape" Label="for shapes"/>
##  <Meth Name="ShapeOps.Complement" Arg="shape"/>
##  <Returns>
##   $X_{JJJ}$ as a group generated by the eyes and ears of the shape.
##  </Returns>
##  <Description>
##    The <E>complement</E> of a shape is the group of all paths that start
##    and end at the representative <M>J</M>.  It is called complement, because
##    this group is the complement of <M>W_J</M> in its normalizer
##    <M>N(W_J)</M> in <M>W</M>.<P/>
##
##    The normalizer of $W_J$ in $W$ is the semidirect product of $W_J$ and
##    $X_{JJJ}$; see <Cite Key="Howlett80"/> and <Cite Key="BriHow99"/>. <P/>
##  
##    The group returned has extra fields <C>ears</C> and <C>eyes</C> that
##    contain these lists of generators.  The 'ears' alone generate a Coxeter
##    group.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;  W.name:= "W";;
##  gap> J:= [1];;  sh:= Shape(W, J);;  WJ:= ReflectionSubgroup(W, J);;
##  gap> co:= Call(sh, "Complement");
##  Subgroup( W, [ ( 2, 5)( 3, 9)( 4, 6)( 8,11)(10,12) ] )
##  gap> Intersection(co, WJ);
##  Subgroup( W, [  ] )
##  gap> NJ:= Normalizer(W, WJ);;
##  gap> IsSubgroup(NJ, co);
##  true
##  gap> Size(co) = Index(NJ, WJ);
##  true
##  gap> NJ = Subgroup(W, Union(List([WJ, co], Generators)));
##  true
##  gap> co.ears;
##  [ ( 2, 5)( 3, 9)( 4, 6)( 8,11)(10,12) ]
##  gap> co.eyes;
##  [ () ]
##  </Example>
##    Find an example (the smallest) with real eyes ...
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ShapeOps.Complement:= function(this)
    local   edges,  t,  eyes,  ears,  i,  e,  j,  nor;

    # (delete) edges:= this.operations.Edges(this);  
    edges:= Call(this, "Edges");  
    # (delete) t:= this.operations.Transversal(this);
    t:= Call(this, "Transversal");
    eyes:= [];  ears:= [];  i:= 0;
    for e in edges do
        i:= i+1;
        for j in [1..Length(e)] do
            if IsBound(e[j]) then
                if e[j].v = i then
                    AddSet(ears, t[i] * e[j].d / t[i]);
                else
                    AddSet(eyes, t[i] * e[j].d / t[e[j].v]);
                fi;
            fi;
        od;
    od;

    nor:= Subgroup(this.W, Union(ears, eyes));
    nor.ears:= ears;  nor.eyes:= eyes;
    return nor;
end;

NormalizerComplement:= function(W, J)
    local   shape,  j,  x,  com,  new;
    
    # if all shapes are known, work with them.
    if IsBound(W.shapes) then    
        shape:= W.shapes[PositionProperty(W.shapes, x-> J in x)];
    
    # otherwise construct a single shape.
    else
        shape:= Shape(W, J);        
    fi;
    
    j:= Position(Elements(shape), J);
    x:= shape.transversal[j];
    
    com:= Call(shape, "Complement");
    new:= com^x;
    new.ears:= OnTuples(com.ears, x);
    new.eyes:= OnTuples(com.eyes, x);
    
    return new;    
end;


#############################################################################
##
#F  ShapeOps.Relation( <shape> )  . . . . . . . . . . . . . . . . . relation.
##
##  <#GAPDoc Label="Relation(shape)">
##  <ManSection>
##  <Meth Name="Relation" Arg="shape" Label="for shapes"/>
##  <Meth Name="ShapeOps.Relation" Arg="shape"/>
##  <Returns>
##    the directed graph formed by the elements of the shape as a binary
##    relation in the sense of MONOiD <Cite Key="monoid"/>.
##  </Returns>
##  <Description>
##  ...
##  <Example>
##  gap> sh:= Shape(CoxeterGroup("A", 5), [1, 3]);;
##  gap> Elements(sh);
##  [ [ 1, 3 ], [ 1, 4 ], [ 1, 5 ], [ 2, 4 ], [ 2, 5 ], [ 3, 5 ] ]
##  gap> Call(sh, "Relation");
##  Relation( [ [ 1, 2 ], [ 1, 3, 4 ], [ 2, 3, 5 ], [ 2, 4, 5 ], [ 3, 4, 6 ],
##  [ 5, 6 ] ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ShapeOps.Relation:= function(this)
    local  list;
    list:= List(Call(this, "Edges"), Set);
    return Relation(List(list, x-> List(x, y-> y.v)));
end;


#############################################################################
##
#F  ConjugacyClasses( <shape> )  . . . . . . . . . . . . . conjugacy classes.
##
##  <#GAPDoc Label="ConjugacyClasses(shape)">
##  <ManSection>
##  <Meth Name="ConjugacyClasses" Arg="shape" Label="for shapes"/>
##  <Meth Name="ShapeOps.ConjugacyClasses" Arg="shape"/>
##  <Returns>
##    the list of addresses of conjugacy classes of elements of $W$ of shape
##    <A>shape</A>.
##  </Returns>
##  <Description>
##  ...
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> List(ConjugacyClasses(W), x-> CoxeterWord(W, Representative(x)));
##  [ [  ], [ 1 ], [ 1, 3 ], [ 1, 2 ], [ 1, 2, 3 ] ]
##  gap> ConjugacyClasses(Shape(W, [1,2]));
##  [ 4 ]
##  gap> W:= CoxeterGroup("B", 3);;
##  gap> List(ConjugacyClasses(W), x-> CoxeterWord(W, Representative(x)));
##  [ [  ], [ 1 ], [ 1, 2, 1, 2 ], [ 1, 2, 1, 2, 3, 2, 1, 2, 3 ], [ 2 ],
##    [ 1, 2 ], [ 1, 3 ], [ 1, 2, 1, 2, 3 ], [ 2, 3 ], [ 1, 2, 3 ] ]
##  gap> ConjugacyClasses(Shape(W, [1,2]));
##  [ 3, 6 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ShapeOps.ConjugacyClasses:= function(this)
    local   W,  cc;

    W:= this.W;  cc:= ConjugacyClasses(W);

    # this relies on the representative of c to be of minimal length!
    return Filtered([1..Length(cc)], 
                   i-> Set(CoxeterWord(W, Representative(cc[i]))) in this);
end;


#############################################################################
##  
#C  Shapes( <W> ) . . . . . . . . . . . . . . . . . . . . . . .  constructor.
##  
##  contains: a list of subsets of [1..n], sorted by rank, index, conjugacy;
##            a list of Coxeter classes;
##      and the mapping of conjugacy classes of elements to Coxeter classes.
##
##  <#GAPDoc Label="Shapes">
##  <ManSection>
##  <Func Name="Shapes" Arg="W"/>
##  <Returns>
##    the list of shapes of the Coxeter group <A>W</A>.
##  </Returns>
##  <Description>
##  The shapes are sorted by rank, and within each rank by the size of the
##  corresponding parabolic subgroup, and within the same parabolic size
##  by the size of the shape.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;  W.name:= "W";;
##  gap> Shapes(W);                                
##  [ Shape( W, [  ] ), Shape( W, [ 1 ] ), Shape( W, [ 1, 3 ] ), 
##    Shape( W, [ 1, 2 ] ), Shape( W, [ 1, 2, 3 ] ) ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
ShapesRank:= function(W, l)
    local   S,  shapes,  d,  sh,  pos;

    # get the Coxeter System (W, S) to work in.
    S:= W.rootInclusion{[1..W.semisimpleRank]};

    # initialize.
    shapes:= [];
    d:= Combinations(S, l);

    # sort 'd' wrt size.
    Sort(d, function(a, b) 
        return 
          Size(ReflectionSubgroup(W, a)) < Size(ReflectionSubgroup(W, b)); 
    end);

    # orbits algorithm.
    while d <> [] do
        sh:= Shape(W, d[1]);
        pos:= List(Elements(sh), x-> Position(d, x));
        d:= d{Difference([1..Length(d)], pos)};
        Add(shapes, sh);
    od;

    Sort(shapes, function(a, b)
        local l;
        l:= Size(ReflectionSubgroup(W, a.J)) - Size(ReflectionSubgroup(W, b.J));
        if l = 0 then
            return Size(a) < Size(b);
        else
            return l < 0;
        fi;
    end);


    return shapes;
end;

Shapes:= function(W)
    local   S,  shapes,  l,  d,  sh,  pos;

    # lets see, we might know them already.
    if IsBound(W.shapes) then  return W.shapes;  fi;

    # get the Coxeter System (W, S) to work in.
    S:= W.rootInclusion{[1..W.semisimpleRank]};

    # initialize.
    shapes:= [];

    # loop over all possible ranks l.  
    for l in [0..Length(S)] do 
        Append(shapes, ShapesRank(W, l));
    od;

    # remember the shapes before returning them.
    W.shapes:= shapes;
    return shapes;
end;


#############################################################################
##
#F  SubsetsShapes( <shapes> ) . . . . . . . . . . . . . . . . .  subsets.
##
##  <#GAPDoc Label="SubsetsShapes">
##  <ManSection>
##  <Func Name="SubsetsShapes" Arg="shapes"/>
##  <Returns>
##    the list of subsets of <M>S</M> in shape order.
##  </Returns>
##  <Description>
##  Shape order means ...
##  <Example>
##  gap> SubsetsShapes(Shapes(CoxeterGroup("A", 3)));
##  [ [  ], [ 1 ], [ 2 ], [ 3 ], [ 1, 3 ], [ 1, 2 ], [ 2, 3 ], [ 1, 2, 3 ] ]
##  gap> SubsetsShapes(Shapes(CoxeterGroup("B", 3)));
##  [ [  ], [ 1 ], [ 2 ], [ 3 ], [ 1, 3 ], [ 2, 3 ], [ 1, 2 ], [ 1, 2, 3 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
SubsetsShapes:= function(shapes)
    return Concatenation(List(shapes, Elements));
end;


#############################################################################
##
#F  ComplementsShapes( <shapes> ) . . . . . . . . . . . . . . .  complements.
##
##  <#GAPDoc Label="ComplementsShapes">
##  <ManSection>
##  <Func Name="ComplementsShapes" Arg="shapes"/>
##  <Returns>
##    the permutation induced by the complementation operation on the list of
##    subsets of <M>S</M> in shape order.
##  </Returns>
##  <Description>
##  <Example>
##  gap> ComplementsShapes(Shapes(CoxeterGroup("A", 3)));
##  (1,8)(2,7)(3,5)(4,6)
##  gap> ComplementsShapes(Shapes(CoxeterGroup("B", 3)));
##  (1,8)(2,6)(3,5)(4,7)
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ComplementsShapes:= function(shapes)
    local   subsets,  S;
    subsets:= SubsetsShapes(shapes);  S:= subsets[Length(subsets)];
    return PermList(List(subsets, a-> Position(subsets, Difference(S, a))));
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


IncMatShapes:= function(shapes)
    local   mat,  a,  row,  nor,  b;

    mat:= [];
    for a in shapes do
        row:= [];
        # (delete) nor:= a.operations.Complement(a);
        nor:= Call(a, "Complement");
        for b in shapes do
            Add(row, Length(Orbits(nor, Filtered(Elements(b), x-> IsSubset(a.J, x)), OnSets)));
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
        # (delete) nor:= Closure(ReflectionSubgroup(a.W, a.J), a.operations.Complement(a));
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
##
##  XCharacters( <W> ) . . . . . . . . . . . . . . . . . . . . .  characters.
##
##  <#GAPDoc Label="XCharacters">
##  <ManSection>
##  <Func Name="XCharacters" Arg="W"/>
##  <Returns>
##    the list of parabolic permutation characters of <A>W</A>.
##  </Returns>
##  <Description>
##  <Example>
##  gap> W:= CoxeterGroup("D", 4);;
##  gap> xch:= XCharacters(W);                     
##  [ [ 192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
##    [ 96, 0, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
##    [ 48, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], 
##    [ 48, 0, 0, 8, 0, 0, 8, 0, 0, 0, 0, 0, 0 ], 
##    [ 48, 0, 0, 8, 0, 0, 0, 8, 0, 0, 0, 0, 0 ], 
##    [ 32, 0, 0, 8, 0, 0, 0, 0, 0, 2, 0, 0, 0 ], 
##    [ 24, 4, 0, 6, 0, 2, 4, 4, 0, 0, 0, 0, 0 ], 
##    [ 8, 4, 0, 4, 2, 0, 0, 0, 0, 2, 0, 0, 0 ], 
##    [ 8, 0, 0, 4, 0, 0, 4, 0, 0, 2, 0, 2, 0 ], 
##    [ 8, 0, 0, 4, 0, 0, 0, 4, 0, 2, 0, 0, 2 ], 
##    [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ] ]
##  gap> ct:= CharTable(W);;  Unbind(ct.irredinfo);
##  gap> Display(ct, rec(chars:= xch, letter:= "X", powermap:= false,        
##  >                    centralizers:= false));
##  W( D4 )
##  
##          1111. 11.11 .1111 211. 1.21 2.11 22.+ 22.- .22 31. .31 4.+ 4.-
##  
##  X.1       192     .     .    .    .    .    .    .   .   .   .   .   .
##  X.2        96     .     .    8    .    .    .    .   .   .   .   .   .
##  X.3        48     8     .    8    .    .    .    .   .   .   .   .   .
##  X.4        48     .     .    8    .    .    8    .   .   .   .   .   .
##  X.5        48     .     .    8    .    .    .    8   .   .   .   .   .
##  X.6        32     .     .    8    .    .    .    .   .   2   .   .   .
##  X.7        24     4     .    6    .    2    4    4   .   .   .   .   .
##  X.8         8     4     .    4    2    .    .    .   .   2   .   .   .
##  X.9         8     .     .    4    .    .    4    .   .   2   .   2   .
##  X.10        8     .     .    4    .    .    .    4   .   2   .   .   2
##  X.11        1     1     1    1    1    1    1    1   1   1   1   1   1
##  
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
XCharacters:= function(W)
    local   pch,  ct,  lambda,  sub,  cts,  fus;

    # initialize list of permchars.
    pch:= [];
    ct:= CharTable(W);

    # loop over classes of parabolics.
    for lambda in Shapes(W) do
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
#F  ParabolicTom( <W> ) . . . . . . . . . . . . . . parabolic table of marks.
##
##  <#GAPDoc Label="ParabolicTom">
##  <ManSection>
##  <Func Name="ParabolicTom" Arg="W"/>
##  <Returns>
##    the list of parabolic table of marks of <A>W</A>.
##  </Returns>
##  <Description>
##  <Example>
##  gap> W:= CoxeterGroup("D", 4);;
##  gap> tom:= ParabolicTom(W);                
##  gap> tom:= ParabolicTom(W);
##  [ [ 192, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ], [ 96, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0 ],
##    [ 48, 8, 8, 0, 0, 0, 0, 0, 0, 0, 0 ], [ 48, 8, 0, 8, 0, 0, 0, 0, 0, 0, 0 ],
##    [ 48, 8, 0, 0, 8, 0, 0, 0, 0, 0, 0 ], [ 32, 8, 0, 0, 0, 2, 0, 0, 0, 0, 0 ],
##    [ 24, 6, 4, 4, 4, 0, 2, 0, 0, 0, 0 ], [ 8, 4, 4, 0, 0, 2, 0, 2, 0, 0, 0 ],
##    [ 8, 4, 0, 4, 0, 2, 0, 0, 2, 0, 0 ], [ 8, 4, 0, 0, 4, 2, 0, 0, 0, 2, 0 ],
##    [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ] ]
##  gap> PrintArray(tom);
##  [ [  192,    0,    0,    0,    0,    0,    0,    0,    0,    0,    0 ],
##    [   96,    8,    0,    0,    0,    0,    0,    0,    0,    0,    0 ],
##    [   48,    8,    8,    0,    0,    0,    0,    0,    0,    0,    0 ],
##    [   48,    8,    0,    8,    0,    0,    0,    0,    0,    0,    0 ],
##    [   48,    8,    0,    0,    8,    0,    0,    0,    0,    0,    0 ],
##    [   32,    8,    0,    0,    0,    2,    0,    0,    0,    0,    0 ],
##    [   24,    6,    4,    4,    4,    0,    2,    0,    0,    0,    0 ],
##    [    8,    4,    4,    0,    0,    2,    0,    2,    0,    0,    0 ],
##    [    8,    4,    0,    4,    0,    2,    0,    0,    2,    0,    0 ],
##    [    8,    4,    0,    0,    4,    2,    0,    0,    0,    2,    0 ],
##    [    1,    1,    1,    1,    1,    1,    1,    1,    1,    1,    1 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ParabolicTom:= function(W)
    local   c;
    c:= List(Shapes(W), x-> ConjugacyClasses(x)[1]);
    return List(XCharacters(W), x-> x{c});
end;

#############################################################################
##
##  YCharacters( <W> ) . . . . . . . . . . . . . . . . . . . . .  characters.
##
##  <#GAPDoc Label="YCharacters">
##  <ManSection>
##  <Func Name="YCharacters" Arg="W"/>
##  <Returns>
##    the list of PIE stripped parabolic permutation characters of <A>W</A>.
##  </Returns>
##  <Description>
##  There is  one
##  character for each subset <M>J \subseteq S</M>, sorted in shape order;
##  see <Ref Func="SubsetsShapes"/>.
##  <Example>
##  gap> W:= CoxeterGroup("D", 4);;
##  gap> ych:= YCharacters(W);
##  [ [ 1, 1, 1, -1, -1, -1, 1, 1, 1, 1, 1, -1, -1 ], 
##    [ 7, -1, -1, -3, 1, 1, -1, 3, -1, 1, -1, 1, -1 ], 
##    [ 7, -1, -1, -3, 1, 1, 3, -1, -1, 1, -1, -1, 1 ], 
##    [ 23, 3, -1, -5, 1, -1, 3, 3, -1, -1, -1, 1, 1 ], 
##    [ 7, 3, -1, -3, -1, 1, -1, -1, -1, 1, -1, 1, 1 ], 
##    [ 17, 1, 1, -1, -1, -1, -3, -3, 1, -1, 1, 1, 1 ], 
##    [ 17, -3, 1, -1, 1, -1, 1, -3, 1, -1, 1, -1, 1 ], 
##    [ 17, -3, 1, -1, 1, -1, -3, 1, 1, -1, 1, 1, -1 ], 
##    [ 17, -3, 1, 1, -1, 1, -3, 1, 1, -1, 1, -1, 1 ], 
##    [ 17, -3, 1, 1, -1, 1, 1, -3, 1, -1, 1, 1, -1 ], 
##    [ 17, 1, 1, 1, 1, 1, -3, -3, 1, -1, 1, -1, -1 ], 
##    [ 23, 3, -1, 5, -1, 1, 3, 3, -1, -1, -1, -1, -1 ], 
##    [ 7, 3, -1, 3, 1, -1, -1, -1, -1, 1, -1, -1, -1 ], 
##    [ 7, -1, -1, 3, -1, -1, 3, -1, -1, 1, -1, 1, -1 ], 
##    [ 7, -1, -1, 3, -1, -1, -1, 3, -1, 1, -1, -1, 1 ], 
##    [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ] ]
##  gap> ct:= CharTable(W);;  Unbind(ct.irredinfo);
##  gap> Display(ct, rec(chars:= ych, letter:= "Y", powermap:= false,
##  >                    centralizers:= false));
##  W( D4 )
##  
##          1111. 11.11 .1111 211. 1.21 2.11 22.+ 22.- .22 31. .31 4.+ 4.-
##  
##  Y.1         1     1     1   -1   -1   -1    1    1   1   1   1  -1  -1
##  Y.2         7    -1    -1   -3    1    1   -1    3  -1   1  -1   1  -1
##  Y.3         7    -1    -1   -3    1    1    3   -1  -1   1  -1  -1   1
##  Y.4        23     3    -1   -5    1   -1    3    3  -1  -1  -1   1   1
##  Y.5         7     3    -1   -3   -1    1   -1   -1  -1   1  -1   1   1
##  Y.6        17     1     1   -1   -1   -1   -3   -3   1  -1   1   1   1
##  Y.7        17    -3     1   -1    1   -1    1   -3   1  -1   1  -1   1
##  Y.8        17    -3     1   -1    1   -1   -3    1   1  -1   1   1  -1
##  Y.9        17    -3     1    1   -1    1   -3    1   1  -1   1  -1   1
##  Y.10       17    -3     1    1   -1    1    1   -3   1  -1   1   1  -1
##  Y.11       17     1     1    1    1    1   -3   -3   1  -1   1  -1  -1
##  Y.12       23     3    -1    5   -1    1    3    3  -1  -1  -1  -1  -1
##  Y.13        7     3    -1    3    1   -1   -1   -1  -1   1  -1  -1  -1
##  Y.14        7    -1    -1    3   -1   -1    3   -1  -1   1  -1   1  -1
##  Y.15        7    -1    -1    3   -1   -1   -1    3  -1   1  -1  -1   1
##  Y.16        1     1     1    1    1    1    1    1   1   1   1   1   1
##  
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
YCharacters:= function(W)
    local   shapes,  lll,  iii,  i;

    shapes:= Shapes(W);

    # make an address book:
    lll:= List(shapes, Size);
    iii:= [];
    for i in [1..Length(lll)] do
        Append(iii, 0 * [1..lll[i]] + i); 
    od;

    return IncidenceMatShapes(shapes)^-1 * XCharacters(W){iii};
end;

#############################################################################
##
##  ZCharacters
##
##  zeta_K = sgn * pi_{S-K}, or as suitable  combination of the theta_K:
##
ZCharacters:= function(W)
    return TransposedMat(IncidenceMatShapes(Shapes(W))) * YCharacters(W);
end;


#############################################################################
##
##  Find all ConjugacyClasses of involutions as shapes with a center.
##  Reference: Richardson.
##  must care for the case of W being a parabolic subgroup.
##  how about reflection subgroups?
##  FIXME: What is the most efficient way to do this?
##
InvolutionShapes:= function(W)
    local   inv,  s,  r,  g,  w;
    inv:= [];
    for s in Shapes(W) do
        r:= Representative(s);
        w:= LongestCoxeterElement(ReflectionSubgroup(W, r));
        if ForAll(r, x-> x^w = x+W.parentN) then
            Add(inv, s);
        fi;
    od;
    return inv;    
end;

Involutions:= function(W)
    local   inv,  s;
    inv:= [];
    for s in InvolutionShapes(W) do
        inv:= Union(inv, ConjugacyClass(W, LongestCoxeterElement(ReflectionSubgroup(W, Representative(s)))));
    od;
    return inv;
end;

SpecialInvolutions:= function(W)
    local   invo,  spec,  s,  J,  WJ,  NJ;

    invo:= InvolutionShapes(W);
    spec:= [];
    for s in invo do
        J:= s.J;
        WJ:= ReflectionSubgroup(W, J);
        # (delete) NJ:= ShapeOps.Complement(s);
        NJ:= Call(s, "Complement");
        if Size(CommutatorSubgroup(WJ, NJ)) = 1 then
            Add(spec, LongestCoxeterElement(ReflectionSubgroup(W, Representative(s))));
        fi;
    od;
    return spec;
end;

OrlikSolomonCharacter:= function(W)
    local   reg,  sum,  s;
    reg:= PermutationCharacter(W, TrivialSubgroup(W));
    sum:= 0*reg;
    for s in SpecialInvolutions(W) do
        sum:= sum + 2 * PermutationCharacter(W, Subgroup(W, [s])) - reg;
    od;
    return sum;
end;



#############################################################################
PrimeShapes:= function(W)
    return 0; ##FIXME
end;

#############################################################################
ShapeOps.CartanName:= function(sh)
    #FIXME: this naming scheme works only for small irreducibles ...
    #FIXME: and maybe we have to take care of types B and F ...
    #FIXME: the best solution probably leaves room for changes by hand ...
    local   typ,  t,  name;

    # get Cartan type.
    typ:= Copy(CartanType(ReflectionSubgroup(sh.W, sh.J)));

    # trivial case first.
    if typ = [] then return "\\emptyset"; fi;

    # switch to rank information.
    for t in typ do
        t[2]:= Length(t[2]);
    od;

    Sort(typ, function(a, b) return a > b; end);

    #FIXME: this naming scheme works only for small irreducibles ...
    for t in [2..Length(typ)] do
        if typ[t][1] <> "A" then
            Error("not yet implemented");
        fi;
    od;

    for t in [1..Length(typ)] do
        if typ[t][2] > 9 then
            Error("not yet implemented");
        fi;
    od;


    name:= typ[1][1];
    Append(name, "_{");
    for t in typ do
        Append(name, String(t[2]));
    od;
    Append(name, "}");
    IsString(name);

    return name;
end;


NamesShapes:= function(shapes)
    local   nam,  n,  pos,  i,  j;
    nam:= List(shapes, CartanName);
    for n in nam do
        pos:= Filtered([1..Length(nam)], i-> nam[i] = n);
        if Length(pos) > 1 then
            for i in [1..Length(pos)] do
                for j in [1..i] do
                    Add(nam[pos[i]], '\'');
                    IsString(nam[pos[i]]);
                od;
            od;
        fi;
    od;

    return nam;
end;



#############################################################################
ShapeOps.Points:= function(this)
    local   points,  o;
    
    points:= [];
# (delete) for o in Orbits(ShapeOps.Complement(this), this.J) do
    for o in Orbits(Call(this, "Complement"), this.J) do
        Add(points, o[1]);
    od;
    return points;
end;
      

#############################################################################
##
##  How to turn a shape into an arrow class.
##
ShapeOps.Bundle:= function(this)
    return Bundle(this.W, [this.J, []]);
end;


###
###  next:  the mu map.
###
ShapeOps.Matrix:= function(this)
    return rec(tail:= this, head:= this, mat:=IdentityMat(Size(this)));
end;

# (delete) MatrixPath:= p -> Product(Reversed(p), x-> PointedShapeOps.Matrix(x).mat);
MatrixPath:= p -> Product(Reversed(p), x-> Call(x, "Matrix").mat);


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
