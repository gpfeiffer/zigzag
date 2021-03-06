#############################################################################
##
#A  streets.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
##
##  This file contains support for streets.
##
##  <#GAPDoc Label="Intro:Streets">
##    A <E>street</E><Index>street</Index> is an orbit of alleys under the
##    action of the free monoid <M>S^*</M>.<P/>
##
##    The functions described in this chapter are implemented in the file
##    <F>streets.g</F>.
##  <#/GAPDoc>
##

#############################################################################
##
#O  StreetOps . . . . . . . . . . . . . . . . . . . . . .  operations record.
##
StreetOps:= OperationsRecord("StreetOps", DomainOps);

#############################################################################
##
#C  Street( <W>, <alley> ) . . . . . . . . . . . . . . . . . . . constructor.
##
##  <#GAPDoc Label="Street">
##  <ManSection>
##  <Func Name="Street" Arg="W, alley"/>
##  <Returns>
##    a new street, an object that represents the orbit of the alley
##    <A>alley</A> under <A>S^*</A>.
##  </Returns>
##  <Description>
##    This is the simple constructor for streets.  It constructs and returns
##    the street of <A>alley</A> in <A>W</A>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Street(W, [[1,2,3], [3]]);
##  Street( CoxeterGroup("A", 5), [ [ 1, 2, 3 ], [ 3 ] ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  public fields:
##    W, the Coxeter group.
##    alley, an alley for W.
##
Street:= function(W, alley)
    return
      rec(
          isDomain:= true,
          isStreet:= true,
          operations:= StreetOps,
          W:= W,
          alley:= alley
          );
end;


#############################################################################
##
#F  IsStreet( <obj> )  . . . . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsStreet">
##  <ManSection>
##  <Func Name="IsStreet" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a street and <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsStreet:= function(obj)
    return IsRec(obj) and IsBound(obj.isStreet)
           and obj.isStreet = true;
end;


#############################################################################
##
#M  Print( <street> )  . . . . . . . . . . . . . . . . . . . . . . . . print.
##
StreetOps.Print:= function(self)
    Print("Street( ", self.W, ", ", self.alley, " )");
end;


#############################################################################
##
#F  Representative( <street> ) . . . . . . . . . . . . . . .  representative.
##
##  A street, as a class of parabolic subsets, has a representative.
##
##  <#GAPDoc Label="Representative(street)">
##  <ManSection>
##  <Meth Name="Representative" Arg="street" Label="for streets"/>
##  <Returns>a representative of the street <A>street</A>.</Returns>
##  <Description>The representative of a street constructed
##  as <C>Street(W, J)</C> (see <Ref Label="Street"/>) will be its
##  initial element <C>J</C>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Representative(Street(W, [[1,2,3], [3]]));
##  [ [ 1, 2, 3 ], [ 3 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Representative:= function(self)
    return self.alley;
end;

#############################################################################
##
#M  Elements( <street> )  . . . . . . . . . . . . . . . . . . . . . elements.
##
##  <#GAPDoc Label="Elements(street)">
##  <ManSection>
##  <Meth Name="Elements" Arg="street" Label="for streets"/>
##  <Returns>
##    the set of elements of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The street of the alley <M>(L; s, t, \dots)</M> is its orbit under the
##    action of <M>S^*</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Elements(Street(W, [[1,2,3], [3]]));
##  [ [ [ 1, 2, 3 ], [ 3 ] ], [ [ 2, 3, 4 ], [ 4 ] ], [ [ 3, 4, 5 ], [ 5 ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Elements:= function(self)
    local   elm,  W,  sh,  i,  j,  L,  list,  o,  x,  J,  t;

    elm:= [];
    W:= self.W;

    sh:= Shapes(W);  # carefully bring in sync with shape internals ...
    i:= PositionProperty(sh, x-> self.alley[1] in x);
    j:= Position(Elements(sh[i]), self.alley[1]);
    L:= sh[i].J;
    list:= OnTuples(self.alley[2], sh[i].transversal[j]^-1);
    o:= Orbit(Call(sh[i], "Complement"), list, OnTuples);
    for x in sh[i].transversal do
        J:= OnSets(L, x);
        for t in o do
            Add(elm, [J, OnTuples(t, x)]);
        od;
    od;
    return Set(elm);
end;

#############################################################################
##
#M  Movers( <street> ) . . . . . . . . . . . . . . . . . . . . . . . movers.
##
##  The edges of the graph of a street are either movers or shakers.
##
##  <#GAPDoc Label="Movers(street)">
##  <ManSection>
##  <Meth Name="Movers" Arg="street" Label="for streets"/>
##  <Returns>
##    a list of streets comprising the movers in the action graph of the
##    street <A>street</A>
##  </Returns>
##  <Description>
##    The edges of the action graph are either movers or shakers, following
##    Brink and Howlett <Cite Key="BrinkHowlett1999"/>.  A mover is an edge
##    with two distinct vertices.  The movers of a street form a collection
##    of streets.  Given a street <A>street</A>, this method constructs and
##    returns the list of streets comprising the movers of <A>street</A>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Call(Street(W, [[1,2,3], [3]]), "Movers");
##  [ Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 4 ], [ 1, 4 ] ] ),
##    Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 4 ], [ 4, 3 ] ] ) ]
##  gap> Union(last);
##  [ [ [ 1, 2, 3, 4 ], [ 1, 4 ] ], [ [ 1, 2, 3, 4 ], [ 4, 3 ] ],
##    [ [ 2, 3, 4, 5 ], [ 2, 5 ] ], [ [ 2, 3, 4, 5 ], [ 5, 4 ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Movers:= function(self)
    local   n,  movers,  a,  i,  b,  K,  L,  d,  c,  new;

    n:= self.W.semisimpleRank;
    movers:= [];
    for a in Elements(self) do
        for i in [1..n] do
            if not i in a[1] then
                b:= [Union(a[1], [i]), Concatenation([i], a[2])];
                K:= a[1];  L:= b[1];
                d:= LongestElement(self.W, K) * LongestElement(self.W, L);
                c:= OnAlleys(a, d);

                if c <> a then
                    AddSet(movers, b);
                fi;
            fi;
        od;
    od;

    new:= [];
    while movers <> [] do
        a:= Street(self.W, movers[1]);
        Add(new, a);
        movers:= Difference(movers, Elements(a));
    od;

    return new;
end;

#############################################################################
##
##  Streets of movers come in pairs of opposites.  MoversPlus lists only one.
##
StreetOps.MoversPlus:= function(self)
    local   n,  movers,  a,  i,  b,  K,  L,  d,  c,  new;

    n:= self.W.semisimpleRank;
    movers:= [];
    for a in Elements(self) do
        for i in [1..n] do
            if not i in a[1] then
                b:= [Union(a[1], [i]), Concatenation([i], a[2])];
                K:= a[1];  L:= b[1];
                d:= LongestElement(self.W, K) * LongestElement(self.W, L);
                c:= OnAlleys(a, d);

                if c <> a then
                    AddSet(movers, b);
                fi;
            fi;
        od;
    od;

    new:= [];
    while movers <> [] do
        a:= Street(self.W, movers[1]);
        b:= Street(self.W, ReversedAlley(self.W, movers[1]));
        Add(new, a);
        movers:= Difference(movers, Elements(a));
        movers:= Difference(movers, Elements(b));
    od;

    return new;
end;


#############################################################################
##
#M  Shakers( <street> ) . . . . . . . . . . . . . . . . . . . . . . . shakers.
##
##  The edges of the graph of a street are either movers or shakers.
##
##  <#GAPDoc Label="Shakers(street)">
##  <ManSection>
##  <Meth Name="Shakers" Arg="street" Label="for streets"/>
##  <Returns>
##    a list of streets comprising the shakers in the action graph of the
##    street <A>street</A>.
##  </Returns>
##  <Description>
##    The edges of the action graph are either movers or shakers, following
##    Brink and Howlett <Cite Key="BrinkHowlett1999"/>.  A shaker is an edge
##    whose initial and terminal vertex coincide.  The shakers of a street
##    form a collection of streets.  Given a street <A>street</A>, this
##    method constructs and returns the list of streets comprising the
##    shakers of <A>street</A>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Call(Street(W, [[1,2,3], [3]]), "Shakers");
##  [ Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 5 ], [ 5, 3 ] ] ) ]
##  gap> Elements(last[1]);
##  [ [ [ 1, 2, 3, 5 ], [ 5, 3 ] ], [ [ 1, 3, 4, 5 ], [ 1, 5 ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Shakers:= function(self)
    local   n,  shakers,  a,  i,  b,  K,  L,  d,  c,  new;

    n:= self.W.semisimpleRank;
    shakers:= [];
    for a in Elements(self) do
        for i in [1..n] do
            if not i in a[1] then
                b:= [Union(a[1], [i]), Concatenation([i], a[2])];
                K:= a[1];  L:= b[1];
                d:= LongestElement(self.W, K) * LongestElement(self.W, L);
                c:= OnAlleys(a, d);

                if c = a then
                    AddSet(shakers, b);
                fi;
            fi;
        od;
    od;

    new:= [];
    while shakers <> [] do
        a:= Street(self.W, shakers[1]);
        Add(new, a);
        shakers:= Difference(shakers, Elements(a));
    od;

    return new;
end;


#############################################################################
##
#M  Suffix( <street> ) . . . . . . . . . . . . . . . . . . . . . . .  suffix.
##
##  <#GAPDoc Label="Suffix(street)">
##  <ManSection>
##  <Meth Name="Suffix" Arg="street" Label="for streets"/>
##  <Returns>
##    the suffix of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The <E>suffix</E><Index>suffix</Index> of a street <M>\alpha = [L; s_1,
##    \dots, s_l]</M> of length <M>\ell(\alpha) = l > 0</M> is the street
##    <M>\sigma(\alpha) = [L; s_2, \dots, s_l]</M> of length <M>l-1</M>.
##    This method signals an error if the length of <A>street</A> is
##    <M>0</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Call(Street(W, [[1,2,3,5], [5,2,3]]), "Suffix");
##  Street( CoxeterGroup("A", 5), [ [ 1, 2, 3 ], [ 2, 3 ] ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Suffix:= function(self)

    # an alley of length 0 has no suffix.
    if self.alley[2] = [] then
        Error("street must have length > 0");
    fi;

    # otherwise, return the suffix of the representative.
    return Street(self.W, SuffixAlley(self.alley));
end;


#############################################################################
##
#M  InverseSuffix( <street> ) . . . . . . . . . . . . . . . . . . . . suffix.
##
##  <#GAPDoc Label="InverseSuffix(street)">
##  <ManSection>
##  <Meth Name="InverseSuffix" Arg="street" Label="for streets"/>
##  <Returns>
##    the inverse suffix of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The <E>inverse suffix</E><Index>inverse suffix</Index> of a street
##    <M>\alpha</M> is the set of all streets <M>\alpha'</M> with
##    <M>\sigma(\alpha') = \alpha</M>.  The inverse suffix of a street
##    <M>\alpha</M> is the (disjoint) union of the movers of <M>\alpha</M>
##    (see <Ref Meth="Movers" Label="for streets"/>) and the shakers of
##    <M>\alpha</M> (see <Ref Meth="Shakers" Label="for streets"/>).
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Call(Street(W, [[1,2,3], [2,3]]), "InverseSuffix");
##  [ Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 4 ], [ 1, 3, 4 ] ] ),
##    Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 4 ], [ 4, 2, 3 ] ] ),
##    Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 5 ], [ 5, 2, 3 ] ] ) ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  TODO: find a more systematic way to list all inverse suffixes.
##
StreetOps.InverseSuffix:= function(self)
    return Concatenation(Call(self, "Movers"), Call(self, "Shakers"));
end;


#############################################################################
##
#M  Prefix( <street> ) . . . . . . . . . . . . . . . . . . . . . . .  prefix.
##
##  <#GAPDoc Label="Prefix(street)">
##  <ManSection>
##  <Meth Name="Prefix" Arg="street" Label="for streets"/>
##  <Returns>
##    the prefix of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The <E>prefix</E><Index>prefix</Index> of a street <M>\alpha = [L; s_1,
##    \dots, s_l]</M> of length <M>\ell(\alpha) = l > 0</M> is the street
##    <M>\pi(\alpha) = [L; s_1, \dots, s_{l-1}]</M> of length <M>l-1</M>.
##    This method signals an error if the length of <A>street</A> is
##    <M>0</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Call(Street(W, [[1,2,3,5], [5,2,3]]), "Prefix");
##  Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 5 ], [ 5, 2 ] ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Prefix:= function(self)

    # an alley of length 0 has no prefix.
    if self.alley[2] = [] then
        Error("street must have length > 0");
    fi;

    # otherwise, return the prefix of the representative.
    return Street(self.W, PrefixAlley(self.alley));
end;


#############################################################################
##
#M  InversePrefix( <street> ) . . . . . . . . . . . . . . . . . . . . prefix.
##
##  <#GAPDoc Label="InversePrefix(street)">
##  <ManSection>
##  <Meth Name="InversePrefix" Arg="street" Label="for streets"/>
##  <Returns>
##    the inverse prefix of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The <E>inverse prefix</E><Index>inverse prefix</Index> of a street
##    <M>\alpha</M> is the set of all streets <M>\alpha'</M> with
##    <M>\pi(\alpha') = \alpha</M>.  The inverse prefix of the street
##    <M>\alpha = [a]</M> of <M>a = (L; s_1, \dots, s_l)</M> consists of the
##    streets <M>[L; s_1, \dots, s_l, t]</M> where <M>t</M> ranges over a
##    transversal of the orbits of the stabilizer of <M>a</M> (see <Ref
##    Func="StabilizerAlley"/>) on the set <M>L \setminus \{s_1, \dots,
##    s_l\}</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Call(Street(W, [[1,2,3,5], [5,2]]), "InversePrefix");
##  [ Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 5 ], [ 5, 2, 1 ] ] ),
##    Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 5 ], [ 5, 2, 3 ] ] ) ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.InversePrefix:= function(self)
    local   stab,  children,  o,  new;

    if IsBound(self.stab) then
        stab:= self.stab;
    elif IsBound(self.parent) then
        stab:= self.parent.stab;
        stab:= Stabilizer(stab, self.alley[2][Length(self.alley[2])]);
    else
        stab:= StabilizerAlley(self.W, self.alley);
    fi;
    self.stab:= stab;

    children:= [];
    for o in Orbits(stab, ApplyFunc(Difference, self.alley)) do
        new:= [self.alley[1], Copy(self.alley[2])];
        Add(new[2], o[1]);
        Add(children, Street(self.W, new));
    od;

    for o in children do
        o.parent:= self;
    od;

    return children;
end;

#############################################################################
##
#M  Children( <street> ) . . . . . . . . . . . . . . . . . . . . .  children.
##
##  <#GAPDoc Label="Children(street)">
##  <ManSection>
##  <Meth Name="Children" Arg="street" Label="for streets"/>
##  <Returns>
##    the children of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The children of a street are its inverse prefixes (see <Ref
##    Meth="InversePrefix" Label="for streets"/>).  This defines a tree
##    structure in the sense of Chapter <Ref Chap="ch:walker"/> on the set
##    of all streets of <M>W</M> which can be used to list them (see <Ref
##    Func="Streets"/>) or to count them (see <Ref Func="NrStreets"/>).
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Children:= StreetOps.InversePrefix;

#############################################################################
##
#F  Streets( <W> ) . . . . . . . . . . . . . . . . . . . . . . . . . streets.
##
##  <#GAPDoc Label="Streets">
##  <ManSection>
##  <Func Name="Streets" Arg="W"/>
##  <Returns>
##    the list of all streets of <A>W</A>.
##  </Returns>
##  <Description>
##  <Example>
##  gap> W:= CoxeterGroup("A", 2);;  W.name:= "W";;
##  gap> Streets(W);
##  [ Street( W, [ [  ], [  ] ] ), Street( W, [ [ 1 ], [  ] ] ),
##    Street( W, [ [ 1 ], [ 1 ] ] ), Street( W, [ [ 1, 2 ], [  ] ] ),
##    Street( W, [ [ 1, 2 ], [ 1 ] ] ), Street( W, [ [ 1, 2 ], [ 2 ] ] ),
##    Street( W, [ [ 1, 2 ], [ 1, 2 ] ] ), Street( W, [ [ 1, 2 ], [ 2, 1 ] ] ) ]
##  gap> List(Streets(W), Size);
##  [ 1, 2, 2, 1, 1, 1, 1, 1 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
Streets:= function(W)
    return Concatenation(List(Shapes(W),
                   x-> BreadthFirst(Call(x, "Street"))));
end;

#############################################################################
##
#F  NrStreets( <W> ) . . . . . . . . . . . . . . . . . . . number of streets.
##
##  <#GAPDoc Label="NrStreets">
##  <ManSection>
##  <Func Name="NrStreets" Arg="W"/>
##  <Returns>
##    the number of streets of <A>W</A>.
##  </Returns>
##  <Description>
##  <Example>
##  gap> NrStreets(CoxeterGroup("A", 2));
##  8
##  gap> NrStreets(CoxeterGroup("E", 6));
##  3347
##  gap> NrStreets(CoxeterGroup("E", 8));
##  180570
##  gap> NrStreets(CoxeterGroup("A", 8));
##  176175
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
NrStreets:= function(W)
    return Sum(Shapes(W), x-> NrPreOrder(Call(x, "Street")));
end;


#############################################################################
##
#M  Source( <street> ) . . . . . . . . . . . . . . . . . . . . . . .  source.
##
##  <#GAPDoc Label="Source(street)">
##  <ManSection>
##  <Meth Name="Source" Arg="street" Label="for streets"/>
##  <Returns>
##    the source of the street <A>street</A> as an address in the list of
##    shapes.
##  </Returns>
##  <Description>
##    The <E>source</E><Index>source</Index> of a street <M>\alpha = [L; s_1,
##    \dots, s_l]</M> is the shape
##    <M>\tau(\alpha) = [L]</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Call(Street(W, [[1,2,3,5], [5,2]]), "Source");
##  9
##  gap> Shapes(W)[9];
##  Shape( CoxeterGroup("A", 5), [ 1, 2, 3, 5 ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Source:= function(self)
    local   source;

    # maybe we know it already.
    if IsBound(self.source) then
        return self.source;
    fi;

    # otherwise: compute source.
    source:= SourceAlley(self.alley);
    source:= PositionProperty(Shapes(self.W), x-> source in x);

    # remember for next visit.
    self.source:= source;
    return self.source;
end;


#############################################################################
##
#M  Target( <street> ) . . . . . . . . . . . . . . . . . . . . . . .  target.
##
##  <#GAPDoc Label="Target(street)">
##  <ManSection>
##  <Meth Name="Target" Arg="street" Label="for streets"/>
##  <Returns>
##    the target of the street <A>street</A> as an address in the list of
##    shapes.
##  </Returns>
##  <Description>
##    The <E>target</E><Index>target</Index> of a street <M>\alpha = [L; s_1,
##    \dots, s_l]</M> is the shape
##    <M>\tau(\alpha) = [L \setminus \{s_1, \dots, s_{l-1}\}]</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Call(Street(W, [[1,2,3,5], [5,2]]), "Target");
##  3
##  gap> Shapes(W)[3];
##  Shape( CoxeterGroup("A", 5), [ 1, 3 ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Target:= function(self)
    local   target;

    # maybe we know it already.
    if IsBound(self.target) then
        return self.target;
    fi;

    # otherwise: compute target.
    target:= TargetAlley(self.alley);
    target:= PositionProperty(Shapes(self.W), x-> target in x);

    # remember for next visit.
    self.target:= target;
    return self.target;
end;


#############################################################################
##
##  compute the list of shapes a street passes trough: the shape of the street
##
StreetOps.Shapes:= function(self)
    local   sh,  a,  lis,  i;

    sh:= Shapes(self.W);
    a:= self.alley;
    lis:= [PositionProperty(sh, x-> a[1] in x)];
    for i in [1..Length(a[2])] do
        Add(lis, PositionProperty(sh, x-> Difference(a[1], a[2]{[1..i]}) in x));
    od;
    return lis;
end;


#############################################################################
StreetOps.Transversal:= function(self)
    #  FIXME:
    return 0;
end;


#############################################################################
##
#F  Edges( <street> )  . . . . . . . . . . . . . . . . . . . . . . . . edges.
##
##  <#GAPDoc Label="Edges(street)">
##  <ManSection>
##  <Meth Name="Edges" Arg="street" Label="for streets"/>
##  <Returns>
##    the edges of the action graph on the elements of the street
##    <A>street</A>.
##  </Returns>
##  <Description>
##  ... more ...
##  <Example>
##  gap> b:= Street(CoxeterGroup("A", 5), [[1,3,5], [1,3]]);;
##  gap> Elements(b);
##  [ [ [ 1, 3, 5 ], [ 1, 3 ] ], [ [ 1, 3, 5 ], [ 1, 5 ] ],
##    [ [ 1, 3, 5 ], [ 3, 1 ] ], [ [ 1, 3, 5 ], [ 3, 5 ] ],
##    [ [ 1, 3, 5 ], [ 5, 1 ] ], [ [ 1, 3, 5 ], [ 5, 3 ] ] ]
##  gap> Call(b, "Edges");
##  [ [ , 3,, 2 ], [ , 4,, 1 ], [ , 1,, 5 ], [ , 2,, 6 ], [ , 6,, 3 ],
##    [ , 5,, 4 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Edges:= function(self)
    local   W,  S,  source,  hhh,  eee,  all,  edges,  a,  new,  l,  s;

    W:= self.W;
    S:= [1..W.semisimpleRank];
    source:= Shapes(W)[Call(self, "Source")];
    hhh:= Elements(source);
    eee:= Call(source, "Edges");
    all:= Elements(self);
    edges:= [];
    for a in all do
        new:= [];
        l:= Position(hhh, a[1]);
        for s in S do
            if not s in a[1] then
                new[s]:= Position(all, OnAlleys(a, eee[l][s].d));
            fi;
        od;
        Add(edges, new);
    od;
    return edges;
end;

#############################################################################
##
#F  Relation( <street> )  . . . . . . . . . . . . . . . . . . . . . relation.
##
##  <#GAPDoc Label="Relation(street)">
##  <ManSection>
##  <Meth Name="Relation" Arg="street" Label="for streets"/>
##  <Returns>
##    the action graph on the elements of the street as a binary relation in
##    the sense of MONOiD <Cite Key="monoid"/>.
##  </Returns>
##  <Description>
##  ... more ...
##  <Example>
##  gap> b:= Street(CoxeterGroup("A", 5), [[1,3,5], [1,3]]);;
##  gap> Elements(b);
##  [ [ [ 1, 3, 5 ], [ 1, 3 ] ], [ [ 1, 3, 5 ], [ 1, 5 ] ],
##    [ [ 1, 3, 5 ], [ 3, 1 ] ], [ [ 1, 3, 5 ], [ 3, 5 ] ],
##    [ [ 1, 3, 5 ], [ 5, 1 ] ], [ [ 1, 3, 5 ], [ 5, 3 ] ] ]
##  gap> Call(b, "Relation");
##  Relation( [ [ 2, 3 ], [ 1, 4 ], [ 1, 5 ], [ 2, 6 ], [ 3, 6 ], [ 4, 5 ] ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Relation:= function(self)
    return Relation(List(Call(self, "Edges"), Set));
end;

#############################################################################
StreetOps.SpanningTree:= function(self)
    #  FIXME:
    return 0;
end;


#############################################################################
##
#M  Length( <street> ) . . . . . . . . . . . . . . . . . . . . . . .  length.
##
##  <#GAPDoc Label="Length(street)">
##  <ManSection>
##  <Meth Name="Length" Arg="street" Label="for streets"/>
##  <Returns>
##    the length of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The <E>length</E><Index>length</Index> of a street <M>\alpha = [L; s_1,
##    \dots, s_l]</M> is the length <M>l</M> of a representative <M>(L; s_1,
##    \dots, s_l)</M>.
##  <Example>
##  gap> Call(Street(CoxeterGroup("A", 5), [[1,2,3,5], [5,2]]), "Length");
##  2
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Length:= function(self)
    return LengthAlley(self.alley);
end;


#############################################################################
##
#M  Depth( <street> ) . . . . . . . . . . . . . . . . . . . . . . . .  depth.
##
##  <#GAPDoc Label="Depth(street)">
##  <ManSection>
##  <Meth Name="Depth" Arg="street" Label="for streets"/>
##  <Returns>
##    the depth of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The <E>depth</E><Index>depth</Index> of a street <M>\alpha = [L; s_1,
##    \dots, s_l]</M> is the size of <M>L \circ \alpha</M>, the number of
##    alleys in the street with the same source <M>L</M>.  In most cases, the
##    depth is 1.  The size of a street is the product of its depth and its
##    width (see <Ref Meth="Width" Label="for streets"/>).
##  <Example>
##  gap> b:= Street(CoxeterGroup("A", 4), [[1, 3], [1]]);;
##  gap> Call(b, "Depth");
##  2
##  gap> Elements(b);
##  [ [ [ 1, 3 ], [ 1 ] ], [ [ 1, 3 ], [ 3 ] ], [ [ 1, 4 ], [ 1 ] ],
##    [ [ 1, 4 ], [ 4 ] ], [ [ 2, 4 ], [ 2 ] ], [ [ 2, 4 ], [ 4 ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  streets of larger depth tend to map to 0.
##
StreetOps.Depth:= function(self)
    return Index(StabilizerAlley(self.W, [self.alley[1], []]),
                 StabilizerAlley(self.W, self.alley));
end;

#############################################################################
##
#M  Width( <street> ) . . . . . . . . . . . . . . . . . . . . . . . .  width.
##
##  <#GAPDoc Label="Width(street)">
##  <ManSection>
##  <Meth Name="Width" Arg="street" Label="for streets"/>
##  <Returns>
##    the width of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The <E>width</E><Index>width</Index> of a street <M>\alpha = [L; s_1,
##    \dots, s_l]</M> is the size of the shape of its source.  The size of a
##    street is the product of its depth and its width (see <Ref Meth="Depth"
##    Label="for streets"/>).
##  <Example>
##  gap> b:= Street(CoxeterGroup("A", 4), [[1, 3], [1]]);;
##  gap> Call(b, "Width");
##  3
##  gap> Elements(b);
##  [ [ [ 1, 3 ], [ 1 ] ], [ [ 1, 3 ], [ 3 ] ], [ [ 1, 4 ], [ 1 ] ],
##    [ [ 1, 4 ], [ 4 ] ], [ [ 2, 4 ], [ 2 ] ], [ [ 2, 4 ], [ 4 ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Width:= function(self)
    return Size(Shapes(self.W)[Call(self, "Source")]);
end;


#############################################################################
##
#M  Reversed( <street> )  . . . . . . . . . . . . . . . . . . . . . reversed.
##
##  <#GAPDoc Label="Reversed(street)">
##  <ManSection>
##  <Meth Name="Reversed" Arg="street" Label="for streets"/>
##  <Returns>
##    the reverse of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The <E>reverse</E><Index>reverse</Index> of a street <M>\alpha =
##    [a]</M> is the street <M>\overline{\alpha} = [\overline{a}]</M>; see
##    <Ref Func="ReversedAlley"/>.
##  <Example>
##  gap> b:= Street(CoxeterGroup("A", 4), [[1, 2, 3], [1, 3]]);;
##  gap> Call(b, "Reversed");
##  Street( CoxeterGroup("A", 4), [ [ 1, 2, 3 ], [ 3, 2 ] ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Reversed:= function(self)
    return Street(self.W, ReversedAlley(self.W, self.alley));
end;


#############################################################################
##
#M  Matrix( <street> ) . . . . . . . . . . . . . . . . . . . . . . .  matrix.
##
##  <#GAPDoc Label="Matrix(street)">
##  <ManSection>
##  <Meth Name="Matrix" Arg="street" Label="for streets"/>
##  <Returns>
##    the matrix of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The <E>matrix</E><Index>matrix</Index> of a street <M>\alpha</M> of the
##    Coxeter group <M>W</M> is the matrix of the linear map
##    <M>\mu(\alpha)</M> defined by <M>L.\mu(\alpha) = \Delta(L \circ
##    \alpha)</M>.  It is represented by a record with components
##    <K>source</K>, <K>target</K> and <K>mat</K>, where <K>source</K> is the
##    position of the source of <M>\alpha</M> in the list of shapes of
##    <M>W</M>, <K>target</K> is the position of the target of <M>\alpha</M>
##    in the list of shapes of <M>W</M>, and <K>mat</K> is the portion of the
##    matrix corresponding to these two subsets of <M>S</M>.  All other
##    entries are 0 anyway.
##  <Example>
##  gap> W:= CoxeterGroup("A", 4);
##  gap> b:= Street(W, [[1,2,3], [3]]);;
##  gap> Call(b, "Matrix");
##  rec(
##    target := 4,
##    source := 6,
##    mat := [ [ 1, -1, 0 ], [ 0, 1, -1 ] ] )
##  gap> Elements(Shapes(W)[6]);
##  [ [ 1, 2, 3 ], [ 2, 3, 4 ] ]
##  gap> Elements(Shapes(W)[4]);
##  [ [ 1, 2 ], [ 2, 3 ], [ 3, 4 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Matrix:= function(self)
    local   sh,  L,  J,  subL,  mat,  e,  i;

    # maybe we know it already.
    if not IsBound(self.matrix) then
        sh:= Shapes(self.W);
        L:= Call(self, "Source");
        J:= Call(self, "Target");
        subL:= Elements(sh[L]);
        mat:= NullMat(Size(sh[L]), Size(sh[J]));
        for e in Elements(self) do
            i:= Position(subL, e[1]);
            mat[i]:= mat[i] + DeltaAlley(self.W, e);
        od;
        self.matrix:= mat;
    fi;

    return rec(target:= self.target, source:= self.source, mat:= self.matrix);
end;

## Deprecate:
StreetOps.BigMatrix:= function(self)
    local   sh,  m,  l,  mat;

    sh:= Shapes(self.W);
    m:= Sum(sh, Size);
    l:= SetComposition(List(sh, Size));
    mat:= NullMat(m, m);
    m:= Call(self, "Matrix");
    mat{l[m.source]}{l[m.target]}:= m.mat;
    return mat;
end;


#  how to multiply two such matrices.  checked!  Turn into proper objects?
ProductStreetMatrices:= function(a, b)
    if a.target = b.source then
        return rec(target:= b.target, source:= a.source, mat:= a.mat * b.mat);
    fi;
    return 0;
end;

##  the product of a list of streets.
ProductStreetMatrixList:= function(list)
    local   product,  i;

    # trivial case: the empty product.
    if list = [] then return 1; fi;  # ???

    product:= list[1];
    for i in [2..Length(list)] do
        product:= ProductStreetMatrices(product, list[i]);
    od;

    return product;
end;

##  the sum of two such matrices.
SumStreetMatrices:= function(a, b)
    if a.target = b.target and a.source = b.source then
        return rec(target:= b.target, source:= a.source, mat:= a.mat + b.mat);
    fi;
    Error("not yet implemented ...");
end;


#############################################################################
##
#M  Delta( <street> ) . . . . . . . . . . . . . . . . . . . . . . . .  delta.
##
##  <#GAPDoc Label="Delta(street)">
##  <ManSection>
##  <Meth Name="Delta" Arg="street" Label="for streets"/>
##  <Returns>
##    <M>\Delta(\alpha)</M> where <M>\alpha</M> is the street <A>street</A>.
##  </Returns>
##  <Description>
##    <M>\Delta(\alpha)</M> for a street <M>\alpha</M> is the sum of the
##    <M>\Delta(a)</M> of the elements <M>a \in \alpha</M>, as computed by
##    <Ref Func="DeltaAlley"/>.  It is represented as a record with
##    components <K>support</K> and <K>mat</K>, where <K>support</K> is the
##    position of the target of <M>\alpha</M> in the list of shapes of
##    <M>W</M> and <K>mat</K> is the list of coefficients of
##    <M>\Delta(\alpha)</M> on this two subset of <M>S</M>.  All other
##    entries are 0 anyway.
##  <Example>
##  gap> W:= CoxeterGroup("A", 4);
##  gap> b:= Street(W, [[1,2,3], [3]]);;
##  gap> Call(b, "Delta");
##  rec(
##    support := 4,
##    mat := [ 1, 0, -1 ] )
##  gap> Elements(Shapes(W)[4]);
##  [ [ 1, 2 ], [ 2, 3 ], [ 3, 4 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Delta:= function(self)
    local   mat;
    mat:= Call(self, "Matrix");
    return rec(support:= mat.target, mat:= Sum(mat.mat));
end;


#############################################################################
##
##  Streets can be multiplied.  With other streets or alleys.
##
##  FIXME:  use formula to do this more efficiently!!!
##
##  FIXME: result should be an element of the StreetAlgebra
##
StreetOps.\*:= function(l, r)
    local   W,  res,  all,  a,  b,  c;

    res:= [];

    #  alley * street.
    if not IsStreet(l) then
        for b in Elements(r) do
            c:= ProductAlleys(l, b);
            if c <> 0 then
                Add(res, c);
            fi;
        od;
        return res;
    fi;

    # street * alley
    if not IsStreet(r) then
        for a in Elements(l) do
            c:= ProductAlleys(a, r);
            if c <> 0 then
                Add(res, c);
            fi;
        od;
        return res;
    fi;

    # street * street.
    if l.W <> r.W then
        Error("factors must have same W component");
    fi;

    W:= l.W;

    # unless they fit together
    if Call(l, "Target") <> Call(r, "Source") then
        return res;
    fi;

    # form all products of all members.
    all:= [];
    for a in Elements(l) do
        for b in Elements(r) do
            c:= ProductAlleys(a, b);
            if c <> 0 then
                Add(all, c);
            fi;
        od;
    od;

    # Q: can the same nonzero c ever occur twice ?
    # no: because of unique factorization.

    a:= Length(all);
    all:= Set(all);
    if a <> Size(all) then
        Error("Panic: problem with unique factorization!");
    fi;


    # split into classes
    while all <> [] do
        c:= Street(W, all[1]);
        Add(res, c);
        a:= Length(all);
        all:= Difference(all, Elements(c));
        if a <> Size(all) + Size(c) then
            Error("Panic:  problem with alley class products!");
        fi;
    od;

    return res;
end;


##  FIXME: should be an element of a street algebra:
ProductStreets:= function(list)
    local   pro,  i,  new,  p;
    pro:= [list[1]];
    for i in [2..Length(list)] do
        new:= [];
        for p in pro do
            Append(new, p * list[i]);
        od;
        pro:= new;
    od;
    return pro;
end;


#############################################################################
##
##  Find the last irreducible factor (actually the first when you read
##  left to right ...)
##
StreetOps.LongestSuffix:= function(self)
    local   fff,  i,  lft,  rgt,  pro;

    # idempotent case first.
    if self.alley[2] = [] then
        return self;
    fi;

    # short case next.
    if Length(self.alley[2]) = 1 then
        return self;
    fi;

    fff:= FactorsAlley(self.alley);
    for i in [1..Length(fff)-1] do
        lft:= Street(self.W, ProductAlleyList(fff{[1..i]}));
        rgt:= Street(self.W, ProductAlleyList(fff{[i+1..Length(fff)]}));
        pro:= lft * rgt;
        if Length(pro) = 1 and pro[1] = self then
            return lft;
        fi;
    od;

    return self;

end;

##FIXME:  does a street have a unique factorization into irreducibles?
StreetOps.Factors:= function(self)
    local   fff,  fac,  o,  i,  lft,  rgt,  pro;

    # idempotent case first.
    if self.alley[2] = [] then
        return self;
    fi;


    fff:= FactorsAlley(self.alley);
    fac:= [];
    o:= 1;
    for i in [1..Length(fff)-1] do
        lft:= Street(self.W, ProductAlleyList(fff{[o..i]}));
        rgt:= Street(self.W, ProductAlleyList(fff{[i+1..Length(fff)]}));
        pro:= lft * rgt;
        if Length(pro) = 1 then
            Add(fac, lft);
            o:= i+1;
        fi;
    od;
    Add(fac, Street(self.W, ProductAlleyList(fff{[o..Length(fff)]})));
    return fac;
end;


#############################################################################
StreetOps.Monoid:= function(self)
    local   W,  S,  source,  hhh,  eee,  all,  edges,  a,  new,  l,  s, i;

    W:= self.W;
    S:= [1..W.semisimpleRank];
    source:= Shapes(W)[Call(self, "Source")];
    hhh:= Elements(source);
    eee:= Call(source, "Edges");
    all:= Elements(self);
    edges:= [];
    i:= 0;
    for a in all do
        i:= i+1;
        new:= [];
        l:= Position(hhh, a[1]);
        for s in S do
            if not s in a[1] then
                new[s]:= Position(all, OnAlleys(a, eee[l][s].d));
            else
                new[s]:= i;
            fi;
        od;
        Add(edges, new);
    od;
    return Monoid(List(Transposed(edges), Transformation));
end;


#############################################################################
## a subset of streets, big enough to generate the descent algebra.
BasicStreets:= function(W)
    local   isNonZero,  basic,  a;

    # how to test for zero matrix.
    isNonZero:= m -> m <> 0*m;

    # start with a reasonably small set of alley classes.
    basic:= Map(Shapes(W), "Street");
    for a in basic do
        Append(basic, Call(a, "MoversPlus"));
    od;
    InfoZigzag1("Generated ", Length(basic), " streets\n");

    # test for irreducibility.
    basic:= Filtered(basic, x-> x = Call(x, "LongestSuffix"));
    InfoZigzag1("of which ", Length(basic), " are irreducible\n");

    # test for Delta = 0.
    basic:= Filtered(basic, x-> isNonZero(Call(x, "Delta").mat));
    InfoZigzag1("Starting with ", Length(basic), " nonzero streets\n");

    # return survivors.
    return basic;
end;

#  leave out irrducibility test!
BasicStreetsNonZero:= function(W)
    local   isNonZero,  basic,  a;

    # how to test for zero matrix.
    isNonZero:= m -> m <> 0*m;

    # start with a reasonably small set of alley classes.
    basic:= Map(Shapes(W), "Street");
    for a in basic do
        Append(basic, Call(a, "MoversPlus"));
    od;
    InfoZigzag1("Generated ", Length(basic), " streets\n");

    # test for Delta = 0.
    basic:= Filtered(basic, x-> isNonZero(Call(x, "Delta").mat));
    InfoZigzag1("Starting with ", Length(basic), " nonzero streets\n");

    # return survivors.
    return basic;
end;



#############################################################################
# given a set of streets, compute all possible paths, ie, sequences of streets
# of length up to len.
##  why does this need to bound the length?  There are no loops, after all???
##  except for 0 length paths of course, but can we not simply ignore them???
##
PathsStreets:= function(streets, len)
    local   paths,  old,  i,  new,  a,  b;

    paths:= [];
    old:= List(streets, x-> [x]);
    #    while old <> [] do
    for i in [1..len] do
        Add(paths, old);
        new:= [];
        for a in old do
            for b in streets do
                if Call(a[Length(a)], "Target") = Call(b, "Source") then
                    Add(new, Concatenation(a, [b]));
                fi;
            od;
        od;
        old:= new;
    od;

    return paths;
end;

PathsStreets1:= function(streets)
    local   paths,  edges,  old,  new,  a,  b;

    paths:= [];

    # ignore streets of length 0.
    edges:= Filtered([1..Length(streets)], i-> Call(streets[i], "Length") > 0);

    old:= List(edges, x-> [x]);
    while old <> [] do
        Add(paths, old);
        new:= [];
        for a in old do
            for b in edges do
                if Call(streets[a[Length(a)]], "Target")
                   = Call(streets[b], "Source") then
                    Add(new, Concatenation(a, [b]));
                fi;
            od;
        od;
        old:= new;
    od;

    return paths;
end;



#############################################################################
##
##  Conjecture:  The streets form a path algebra.
##
CartanMatStreets:= function(W)
    local   l,  mat,  b,  i,  j;

    l:= Length(Shapes(W));
    mat:= NullMat(l, l);
    for b in Streets(W) do
        i:= Call(b, "Source");
        j:= Call(b, "Target");
        mat[i][j]:= mat[i][j] + 1;
    od;

    return mat;
end;

QuiverMatStreets:= function(W)
    local   c;
    c:= CartanMatStreets(W);
    return c^0 - c^-1; # c = d^0 + d^1 + d2 + ... => d = 1 - 1/c.
end;


#############################################################################
##
##  Conjecture 2:  The slanted streets form a path algebra.
##

# this only makes sense for W of type A
CartanMatSlantedStreets0:= function(W)
    local   l,  n,  mat,  b,  i,  j;

    l:= Length(Shapes(W));
    n:= W.semisimpleRank+1;
    mat:= NullMat(l, l);
    for b in Streets(W) do
        if IsSlanted(ForestAlley(n, b.alley)) then
            i:= Call(b, "Source");
            j:= Call(b, "Target");
            mat[i][j]:= mat[i][j] + 1;
        fi;
    od;

    return mat;
end;

# this is more generally applicable:
# a slanted street is one that occurs as part of a
# path of the quiver (this depends on th choice of
# the quiver, and prefersone of a pair of negatives)
SlantedStreets:= function(W)
    local   l,  sla,  q,  i,  j,  p;

    l:= Length(Shapes(W));
    sla:= [];
    q:= DescentQuiver(W);
    for i in [1..l] do
        for j in [1..l] do
            for p in q.pathmat[i][j].path do
                if p <> [] then
                    Append(sla, ProductStreets(q.path1{p}));
                fi;
            od;
        od;
    od;

    return Concatenation(q.path0, sla);
end;


CartanMatSlantedStreets:= function(W)
    local   l,  mat,  q,  i,  j,  p;

    l:= Length(Shapes(W));
    mat:= [];
    q:= DescentQuiver(W);
    for i in [1..l] do
        mat[i]:= [];
        for j in [1..l] do
            mat[i][j]:= 0;
            for p in q.pathmat[i][j].path do
                if p = [] then
                    mat[i][j]:= mat[i][j] + 1;
                else
                    mat[i][j]:= mat[i][j] + Length(ProductStreets(q.path1{p}));
                fi;
            od;
        od;
    od;

    return mat;
end;

QuiverMatSlantedStreets:= function(W)
    local   c;
    c:= CartanMatSlantedStreets(W);
    return c^0 - c^-1; # c = d^0 + d^1 + d2 + ... => d = 1 - 1/c.
end;


#  colours.
#
#  the colour of an alley (L; s) of length 1 is the pair of shapes
#  [K], [K_s], where K is the connected component of s in L.
#
#  the colour of a street is the multiset of colours of
#  a factorization of one of its alleys into length 1 alleys.
StreetOps.Colours:= function(self)
    return ColoursAlley(self.W, self.alley);
end;


#############################################################################
##
##  Street Algebra Elements.
##
##  A street algebra element is a linear combination of streets.
##

#############################################################################
##
#O  StreetAlgebraEltOps . . . . . . . . . . . . . . . . operations record.
##
StreetAlgebraEltOps:= OperationsRecord("StreetAlgebraEltOps");

#############################################################################
##
#C  StreetAlgebraElt( <coef>, <elts> ) . . . . . . . . . . .  constructor.
##
##  <#GAPDoc Label="StreetAlgebraElt">
##  <ManSection>
##  <Func Name="StreetAlgebraElt" Arg="coef, elts"/>
##  <Returns>
##    a new street algebra element with components ...
##  </Returns>
##  <Description>
##  This is the simple constructor for quiver elements ...
##  <Example>
##  gap> StreetAlgebraElt([1], [[3, 4]]);
##  StreetAlgebraElt([1], [[3, 4]])
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetAlgebraElt:= function(coef, elts)
    local self;
    self:= rec(coef:= coef, elts:= elts);
    self.isStreetAlgebraElt:= true;
    self.operations:= StreetAlgebraEltOps;
    return self;
end;


#############################################################################
##
#F  IsStreetAlgebraElt( <obj> )  . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsStreetAlgebraElt">
##  <ManSection>
##  <Func Name="IsStreetAlgebraElt" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a joinnt and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsStreetAlgebraElt:= function(obj)
    return IsRec(obj) and IsBound(obj.isStreetAlgebraElt) and obj.isStreetAlgebraElt = true;
end;

#############################################################################
StreetAlgebraEltOps.Print:= function(self)
    Print("StreetAlgebraElt( ", self.coef, ", ", self.elts, " )");
end;

# how to normalize a list e of elements with coefficients c
StreetAlgebraEltOps.Normalize:= function(self)
    local   e,  c,  eee,  ccc,  i,  elt,  coe;

    e:= self.elts;
    c:= self.coef;
    SortParallel(e, c);
    eee:= [];
    ccc:= [];
    i:= 1;
    while i <= Length(e) do
        elt:= e[i];
        coe:= c[i];
        i:= i+1;
        while i <= Length(e) and e[i] = elt do
            coe:= coe + c[i];
            i:= i+1;
        od;
        if coe <> 0*coe then
            Add(eee, elt);
            Add(ccc, coe);
        fi;
    od;

    # copy normalized lists back into originals.
    self.elts:= eee;
    self.coef:= ccc;
end;



#############################################################################
StreetAlgebraEltOps.\*:= function(l, r)
    local   c,  e,  i,  j,  a,  s,  pro;

    if IsStreetAlgebraElt(l) then
        if IsStreetAlgebraElt(r) then
            c:= [];
            e:= [];
            for i in [1..Length(l.elts)] do
                for j in [1..Length(r.elts)] do
                    a:=  l.coef[i] * r.coef[j];
                    for s in l.elts[i] * r.elts[j] do
                        Add(c, a);
                        Add(e, s);
                    od;
                od;
            od;
            pro:= StreetAlgebraElt(c, e);
        else
            pro:= StreetAlgebraElt(l.coef * r, l.elts);
        fi;
    else
        pro:= StreetAlgebraElt(l * r.coef, r.elts);
    fi;

    Call(pro, "Normalize");
    return pro;
end;

#############################################################################
StreetAlgebraEltOps.\+:= function(l, r)
    local   q,  sum;

    # check arguments.
    if not IsStreetAlgebraElt(r) then
        Error("<r> is not a StreetAlgebraElt");
    fi;
    if not IsStreetAlgebraElt(l) then
        Error("<l> is not a StreetAlgebraElt");
    fi;

    # from the sum and normalize.
    sum:= StreetAlgebraElt(Concatenation(l.coef, r.coef),
                          Concatenation(l.elts, r.elts));
    Call(sum, "Normalize");
    return sum;
end;


#############################################################################
StreetAlgebraEltOps.\-:= function(l, r)
    return l + (-1)*r;
end;





#############################################################################
##
#E  Emacs  . . . . . . . . . . . . . . . . . . . . . . local emacs variables.
##
##  Local Variables:
##  mode:               gap
##  outline-regexp:     "#F\\|#V\\|#E\\|#A\\|#O\\|#C"
##  fill-column:        77
##  End:
##
