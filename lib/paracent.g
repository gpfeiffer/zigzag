#############################################################################
##
#A  paracent.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010-2012  Götz Pfeiffer
##
##  This file contains the routines for centralizers of parabolic subgroups.
##
##  <#GAPDoc Label="Intro:ParaCent">
##
##    Ordered  shapes are  domains, so  every  set theoretic  function for  a
##    domain  can  be applied  to  an  ordered  shape (see  section&nbsp;<Ref
##    Label="Sect:OrderedShapesAsSets"/>).<P/>
##
##    The functions  described in  this chapter are  implemented in  the file
##    <F>paracent.g</F>.
##  <#/GAPDoc>
##

#############################################################################
##
#O  OrderedShapeOps  . . . . . . . . . . . . . . . . . . . operations record.
##
OrderedShapeOps:= Ops("OrderedShape", DomainOps);


#############################################################################
##
#C  OrderedShape( <W>, <J> ) . . . . . . . . . . . . . . . . . .  constructor.
##
##  <#GAPDoc Label="OrderedShape">
##  <ManSection>
##  <Func Name="OrderedShape" Arg="W, J"/>
##  <Returns>
##    a new  ordered shape,  an object that  represents the ordered  shape of
##    <A>J</A> in <A>W</A>.
##  </Returns>
##  <Description>
##    This  is  the simple  constructor  for  the  ordered shape  class.   It
##    constructs and returns the ordered shape of <A>J</A> in <A>W</A>.  Here
##    <A>W</A> is a  finite Coxeter group of rank <M>n</M>  and <A>J</A> is a
##    duplicate free list of elements of <M>\{1, \dots, n\}</M>.
##  <Example>
##  gap> W:= CoxeterGroup("E", 6);;
##  gap> OrderedShape(W, [1,3]);
##  OrderedShape( CoxeterGroup("E", 6), [ 1, 3 ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
OrderedShape:= function(W, J)
    local   obj;
    obj:= Object("OrderedShape");
    obj.isDomain:= true;
    obj.W:= W;
    obj.J:= J;
    return obj;
end;


#############################################################################
##
#F  IsOrderedShape( <obj> )  . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsOrderedShape">
##  <ManSection>
##  <Func Name="IsOrderedShape" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is an ordered shape and <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsOrderedShape:= TypeCheck("OrderedShape");


#############################################################################
##
#F  Print( <shape> ) . . . . . . . . . . . . . . . . . . . . . . . . . print.
##
OrderedShapeOps.Print:= function(self)
    Print("OrderedShape( ", self.W, ", ", self.J, " )");
end;


#############################################################################
##
#F  Representative( <shape> )  . . . . . . . . . . . . . . .  representative.
##
##  An ordered shape, as a class of ordered parabolic subsets, has a representative.
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
OrderedShapeOps.Representative:= function(self)
    return self.J;
end;


#############################################################################
##
#F  Rank( <shape> )  . . . . . . . . . . . . . . . . . . . . . . . . .  rank.
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
OrderedShapeOps.Rank:= function(self)
    return Length(self.J);
end;


#############################################################################
##
#F  Elements( <shape> )  . . . . . . . . . . . . . . . . . . . . .  elements.
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
OrderedShapeOps.Elements:= function(self)
    local   W,  S,  K,  L, onParabolics,  orbit,  transversal,  edges,  k,
            l,  i,  pos,  perm, d, e;

    # get the Coxeter System (W, S) to work in.
    W:= self.W;  S:= W.rootInclusion{[1..W.semisimpleRank]};

    # how to determine the image of $J$ under a generator.
    # Given $J$ and $i \in S \setminus J$, determine
    # the image $K$ of $J$
    # under the longest coset rep of J in  $J \cup \{i\}$.
    # This yields J in case i \in J.
    onParabolics:= function(J, i)
        d:= LongestElement(W, J) * LongestElement(W, Union(J, [i]));
        return OnTuples(J, d);
    end;

    # extended orbit algorithm.
    orbit:= [self.J];  transversal:= [()];  edges:= [];  k:= 0;  l:= 1;
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
    self.transversal:= Permuted(transversal, perm);
    edges:= Permuted(edges, perm);
    for e in edges do
        for i in [1..Length(e)] do
            if IsBound(e[i]) then e[i].v:= e[i].v^perm; fi;
        od;
    od;
    self.edges:= edges;
    self.root:= 1^perm;  ##  the position of J in the list.

    return orbit;
end;

#############################################################################
##
#F  <l> = <r>  . . . . . . . . . . . . . . . . . . . . . . . . equality test.
##
OrderedShapeOps.\= := function(l, r)
    return l.W = r.W and l.J in r;
end;

#############################################################################
##
#F  <l> < <r>  . . . . . . . . . . . . . . . . . . . . . . . . .  comparison.
##
OrderedShapeOps.\< := function(l, r)
    if not IsShape(l) then return false; fi;
    if not IsShape(r) then return false; fi;
    return l.W < r.W or l.W = r.W and Elements(l) < Elements(r);
end;


#############################################################################
##
#F  Edges( <shape> ) . . . . . . . . . . . . . . . . . . . . . . . . . edges.
##
##  <#GAPDoc Label="Edges(shape)">
##  <ManSection>
##  <Meth Name="Edges" Arg="shape" Label="for ordered shapes"/>
##  <Returns>
##    the list  of edges of the graph  formed by the elements  of the ordered
##    shape
##    <A>shape</A>.
##  </Returns>
##  <Description>
##    The elements of an ordered shape form the vertices of a directed graph.
##    The <E>edges</E>  of a shape are the  edges of this graph  and they are
##    defined as  follows.  Let <M>J</M> be  an element of the  shape and let
##    <M>s \in S  \setminus J</M>.  Let <M>M = J \cup  \{s\}</M> and let <M>w
##    \in W</M> be the longest  element of the parabolic subgroup <M>W_M</M>.
##    Then <M>J^w</M>  is a  subset of  <M>M</M> and thus  an element  of the
##    shape.  In the graph, this  yields and edge from <M>J</M> to <M>J^w</M>
##    with labels <M>s</M> and <M>w</M>.<P/>
##
##    The function <C>Edges</C> returns all these edges in the form of a list
##    of  lists, with  one list  for every  vertex (element  <M>J</M>  of the
##    shape).   The  entries in  the  list  for  <M>J</M> correspond  to  the
##    generators <M>s \in S</M> with  unbound entries for <M>s \in J</M>.  In
##    the other cases  the list element is a  record with components <C>v</C>
##    and <C>w</C>,  where <C>v</C>  gives the address  of <M>J^w</M>  in the
##    list   of  elements,   and   where  <C>w</C>   gives  the   permutation
##    <M>w</M>.<P/>
##
##    <C>ShapeOps.Edges(shape)</C> returns a list of lists <C>l</C> with
##    <C>l[i][k]</C> bound to a record <C>r</C> if vertex <C>i</C> is the
##    initial vertex of a directed edge with label <C>k</C>.  In that case
##    the record <C>r</C> has two components, <C>v</C> for the (address of
##    the) terminal vertex of the edge and <C>d</C> for the conjugating
##    element <M>d_J^M = w_J w_M \in W</M> that maps the intial vertex to the
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
OrderedShapeOps.Edges:= function(self)
    Call(self, "Elements");  # expand the shape.
    return self.edges;
end;


#############################################################################
##
#F  Transversal( <shape> ) . . . . . . . . . . . . . . . . . . . transversal.
##
##  <#GAPDoc Label="Transversal(shape)">
##  <ManSection>
##  <Meth Name="Transversal" Arg="shape" Label="for ordered shapes"/>
##  <Returns>
##    a transversal of the graph formed by the elements of the ordered shape
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
OrderedShapeOps.Transversal:= function(self)
    Call(self, "Elements");  # expand the shape.
    return self.transversal;
end;


#############################################################################
##
#F  Display( <shape> ) . . . . . . . . . . . . . . . . . . . . . . . display.
##
OrderedShapeOps.Display:= function(self, options)

    # determine name, if necessary.
    if not IsBound(self.name) then
        self.name:= CartanName(ReflectionSubgroup(self.W, self.J));
        if self.name = "" then self.name:= "1"; fi;  # trivial subgroup.
    fi;

    Print(self.name, " [", Size(self), "]");
end;


#############################################################################
##
#F  OrthogonalComplement( <W>, <J> ) . . . . . . . . . . . . . . centralizer.
##
##  <#GAPDoc Label="OrthogonalComplement">
##  <ManSection>
##  <Func Name="OrthogonalComplement" Arg="W, J"/>
##  <Returns>
##   <M>X_{JJJ}</M> as a group generated by the eyes and ears of the shape.
##  </Returns>
##  <Description>
##    The normalizer of <M>W_J</M> in <M>W</M> is the semidirect product of
##    <M>W_J</M> and <M>X_{JJJ}</M>; see <Cite Key="Howlett1980"/> and <Cite
##    Key="BrinkHowlett1999"/>.  The complement <M>X_{JJJ}</M> is the image
##    in <M>W</M> of the group of all paths in the shape of <M>J</M> starting
##    and ending at <M>J</M>. Each choice of a spanning tree for the shape of
##    <M>J</M> yields a set of Schreier generators for this subgroup of
##    <M>W</M>.  If such a generator involves a loop it is called an
##    <E>ear</E>, otherwise it is called an <E>eye</E>.<P/>
##
##    The group returned has extra fields <C>ears</C> and <C>eyes</C> that
##    contain these lists of generators.  The <C>ears</C> alone generate a
##    Coxeter group.
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
OrderedShapeOps.Complement:= function(self)
    local   edges,  t,  eyes,  ears,  i,  e,  j,  T,  com;

    edges:= Call(self, "Edges");
    t:= Call(self, "Transversal");
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

    T:= Reflections(W);
    com:= ReflectionSubgroup(W, Set(List(ears, x-> Position(T, x))));
    com.ears:= ears;

    if Difference(eyes, [()]) <> [] then
        Error("Complement: ordered shape should not have eyes");
    fi;

    return com;
end;

##  centralizing elements from components.
OrderedShapeOps.Centre:= function(self)
    local   W,  J,  gens,  list,  set,  K,  wK,  L,  centre,  l;

    W:= self.W;
    J:= self.J;

    # separate central w0 from non-central ones.
    gens:= []; list:= [];
    for set in CartanType(ReflectionSubgroup(W, J)) do
        K:= J{set[2]};
        wK:= LongestElement(W, K);
        L:= List(OnTuples(K, wK), x-> (x-1) mod W.parentN + 1);
        if L = K then
            Add(gens, wK);
        else
            Add(list, K);
        fi;
    od;
    centre:= Subgroup(W, gens);

    # find generators of the form wK * n
    gens:= [];
    for set in Combinations(list) do
        K:= Union(set);
        wK:= LongestElement(W, K);
        L:= List(OnTuples(J, wK), x-> (x-1) mod W.parentN + 1);
        l:= Position(Elements(self), L);
        if l <> false then
            Add(gens, wK * Call(self, "Transversal")[l]);
        fi;
    od;
    gens:= GeneratorsAbelianGroup(Subgroup(W, gens));

    return Closure(centre, Subgroup(W, gens));
end;


OrthogonalComplement:= function(W, J)
    local   shape,  j,  x,  com,  new;

    shape:= OrderedShape(W, J);

    j:= Position(Elements(shape), J);
    x:= shape.transversal[j];

    com:= Call(shape, "Complement");
    new:= OnTuples(com.rootInclusion{[1..com.semisimpleRank]}, x);

    return ReflectionSubgroup(W, Set(new));
end;



CentralizerParabolic:= function(W, J)
    local   shape,  com,  ears,  centre;

    shape:= OrderedShape(W, J);
    com:= Call(shape, "Complement");
    ears:= com.ears;
    centre:= Call(shape, "Centre");
    com:= Closure(com, centre);
    com.ears:= ears;
    com.legs:= Generators(centre);
    return com;

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
