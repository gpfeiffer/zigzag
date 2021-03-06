#############################################################################
##
#A  classes.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2011  Götz Pfeiffer
##
##  This file contains routines for conjugacy classes of Coxeter groups.
##
##  <#GAPDoc Label="Intro:Classes">
##    The conjugation action of a finite group on itself naturally
##    partitions the group into conjugacy classes.
##    The conjugacy classes of a finite Coxeter group <M>W</M> are
##    further partitioned into cyclic shift classes, see
##    <Ref Func="CyclicShifts"/> and <Ref Func="CyclicShiftClasses"/>.<P/>
##
##    The stabilizer in <M>W</M> of the fixed point space of an element
##    <M>w \in W</M> is a parabolic subgroup <M>P</M> of <M>W</M>.
##    According to Konvalinka,  Pfeiffer and Röver <Cite Key="KoPfRo2011"/>,
##    the centralizer of <M>w</M> in <M>P</M> usually has a complement
##    (isomorphic to the complement of <M>P</M> in its normalizer; see
##    <Ref Func="NormalizerComplement"/>) in the full centralizer of
##    <M>w</M> in <M>W</M>.  This complement, if it exists, is computed by
##    the function <Ref Func="CentralizerComplement"/>.<P/>
##
##    The functions described in this chapter are implemented in the file
##    <F>classes.g</F>.
##  <#/GAPDoc>
##


#############################################################################
##
#O  CyclicShiftsOps  . . . . . . . . . . . . . . . . . . . operations record.
##
CyclicShiftsOps:= OperationsRecord("CyclicShiftsOps", DomainOps);


#############################################################################
##
#C  CyclicShifts( <W>, <w> )  . . . . . . . . . . . . . . . . .  constructor.
##
##  <#GAPDoc Label="CyclicShifts">
##  <ManSection>
##  <Func Name="CyclicShifts" Arg="W, w"/>
##  <Returns>
##    a new cyclic shift class, an object that represents the set of cyclic
##    shifts of <A>w</A> in
##    <A>W</A>.
##  </Returns>
##  <Description>
##  This is the simple constructor for the cyclic shifts class.  It constructs and
##  returns the cyclic shift class of <A>w</A> in <A>W</A>.  Here <A>W</A> is a finite
##  Coxeter group and <A>w</A> is an element of
##  <M>W</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 4);
##  CoxeterGroup("A", 4)
##  gap> cyc:=  CyclicShifts(W, PermCoxeterWord(W, [1..4]));
##  CyclicShifts( CoxeterGroup("A", 4), ( 1,20, 4, 3, 2)( 5,19,18, 7, 6)
##  ( 8,17,16,15, 9)(10,14,13,12,11) )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  public fields:
##    W, the Coxeter group.
##    w, the element
##
##  actually, w doesn't need to be in W as long as both have a common parent ...
##
CyclicShifts:= function(W, w)
    return
      rec(
          isDomain:= true,
          isCyclicShifts:= true,
          operations:= CyclicShiftsOps,
          W:= W,
          w:= w
          );
end;


#############################################################################
##
#F  IsCyclicShifts( <obj> )  . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsCyclicShifts">
##  <ManSection>
##  <Func Name="IsCyclicShifts" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a cyclic shift class and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsCyclicShifts:= function(obj)
    return IsRec(obj) and IsBound(obj.isCyclicShifts)
           and obj.isCyclicShifts = true;
end;


#############################################################################
##
#F  Print( <shifts> )  . . . . . . . . . . . . . . . . . . . . . . . . print.
##
CyclicShiftsOps.Print:= function(self)
    Print("CyclicShifts( ", self.W, ", ", self.w, " )");
end;


#############################################################################
##
#F  Representative( <shifts> ) . . . . . . . . . . . . . . .  representative.
##
##  A cyclic shift class, as a class of elements, has a representative.
##
##  <#GAPDoc Label="Representative(shifts)">
##  <ManSection>
##  <Meth Name="Representative" Arg="shifts" Label="for cyclic shifts"/>
##  <Returns>a representative of the cyclic shift class <A>shifts</A>.</Returns>
##  <Description>
##  The representative of a cyclic shift class constructed
##  as <C>CyclicShifts(W, w)</C> (see <Ref Label="CyclicShifts"/>) will be its
##  initial element <C>w</C>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 4);
##  CoxeterGroup("A", 4)
##  gap> cyc:=  CyclicShifts(W, PermCoxeterWord(W, [1..4]));
##  CyclicShifts( CoxeterGroup("A", 4), ( 1,20, 4, 3, 2)( 5,19,18, 7, 6)
##  ( 8,17,16,15, 9)(10,14,13,12,11) )
##  gap> Representative(cyc);
##  ( 1,20, 4, 3, 2)( 5,19,18, 7, 6)( 8,17,16,15, 9)(10,14,13,12,11)
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
CyclicShiftsOps.Representative:= function(self)
    return self.w;
end;


#############################################################################
##
#F  Elements( <shifts> ) . . . . . . . . . . . . . . . . . . . . .  elements.
##
##  <#GAPDoc Label="Elements(shifts)">
##  <ManSection>
##  <Meth Name="Elements" Arg="shifts" Label="for cyclic shifts"/>
##  <Returns>
##    the set of elements of the cyclic shift class <A>shifts</A>.
##  </Returns>
##  <Description>
##  An element <M>w'</M> of <M>W</M> is a cyclic shift of <M>w</M>
##  if there are elements <M>v</M> and <M>v'</M> of<M>W</M> such that
##  <M>w = vv'</M> with <M>\ell(w) = \ell(v) + \ell(v')</M> and
##  <M>w' = v'v</M> with <M>\ell(w') = \ell(v') + \ell(v) = \ell(w)</M>.
##  The cyclic shift class of <M>w</M> in <M>W</M> consists of all cyclic
##  shifts of <M>w</M>.
##
##  As a side effect, <C>Elements</C> also computes lists of elements
##  immediately below or above this cyclic shift class, which can be used
##  to decide whether this is a class of elements of minimal or of maximal
##  length, or to find conjugate elements of minimal or maximal length,
##  see ... below.
##  <Example>
##  gap> W:= CoxeterGroup("A", 4);
##  CoxeterGroup("A", 4)
##  gap> cyc:=  CyclicShifts(W, PermCoxeterWord(W, [1..4]));
##  CyclicShifts( CoxeterGroup("A", 4), ( 1,20, 4, 3, 2)( 5,19,18, 7, 6)
##  ( 8,17,16,15, 9)(10,14,13,12,11) )
##  gap> List(Elements(cyc), x-> CoxeterWord(W, x));
##  [ [ 4, 3, 2, 1 ], [ 3, 2, 1, 4 ], [ 2, 1, 4, 3 ], [ 2, 1, 3, 4 ],
##    [ 1, 4, 3, 2 ], [ 1, 3, 2, 4 ], [ 1, 2, 4, 3 ], [ 1, 2, 3, 4 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  y = s_i x s_i is a cyclic shift of x if either
##  l(s_i x) > l(x) and l(s_i x s_i) < l(s_i x) or
##  l(s_i x) < l(x) and l(s_i x s_i) > l(s_i x)
##
##
CyclicShiftsOps.Elements:= function(self)
    local   W,  S,  orb,  transversal,  gens,  j,  edges,  x,  i,  s,
            y,  z,  k,  perm;

    W:= self.W;
    S:= W.rootInclusion{[1 .. W.semisimpleRank]};

    self.above:= [];
    self.below:= [];

    orb:= [self.w];  transversal:= [()];  gens:= [];  j:= 0;
    edges:= [];
    for x in orb do
        j:= j+1;  # x = orb[j];
        for i in S do
            s:= W.(W.rootRestriction[i]);
            y:= s * x;
            z:= y * s;
            #if i^x > N then
            if IsLeftDescent(W, x, i) then
                #if i/y > N then
                if IsRightDescent(W, y, i) then
                    AddSet(self.below, z);
                else
                    k:= Position(orb, z);
                    if k = false then
                        Add(orb, z);
                        Add(transversal, transversal[j] * s);
                        Add(edges, [j, Length(orb), i]);
                    else
                        Add(gens, transversal[j] * s * transversal[k]^-1);
                        Add(edges, [j, k, i]);
                    fi;
                fi;
            else
                # if i/y > N then
                if not IsRightDescent(W, y, i) then
                    AddSet(self.above, z);
                fi;
            fi;
        od;
    od;
    self.gens:= gens;

    # sort orbit lexicographically and keep transversal, edges in sync.
    perm:= Sortex(orb);
    self.transversal:= Permuted(transversal, perm);
    self.edges:= List(edges, e -> [e[1]^perm, e[2]^perm, e[3]]);
    self.root:= 1^perm;  ##  the position of w in the list.

    return orb;
end;


CyclicShiftsOps.Centralizer:= function(self)
    Elements(self);
    return Subgroup(self.W, self.gens);
end;


#############################################################################
##
#F  IsMinimal( <shifts> )
##
CyclicShiftsOps.IsMinimal:= function(self)
    Elements(self);
    return self.below = [];
end;

#############################################################################
##
#F  IsMaximal( <shifts> )
##
CyclicShiftsOps.IsMaximal:= function(self)
    Elements(self);
    return self.above = [];
end;

#############################################################################
##
#F  AllAbove( <shifts> )
##
##  compute a set of elements that contains representatives of *all* cyclic
##  shift classes immediately above this one.
##
CyclicShiftsOps.AllAbove:= function(self)
    Elements(self);
    return self.above;
end;


#############################################################################
##
#F  AllBelow( <shifts> )
##
##  compute a set of elements that contains representatives of *all* cyclic
##  shift classes immediately below this one.
##
CyclicShiftsOps.AllBelow:= function(self)
    Elements(self);
    return self.below;
end;


#############################################################################
##
#F  <l> = <r>  . . . . . . . . . . . . . . . . . . . . . . . . equality test.
##
CyclicShiftsOps.\= := function(l, r)
    return l.W = r.W and l.w in r;
end;

#############################################################################
##
#F  <l> < <r>  . . . . . . . . . . . . . . . . . . . . . . . . .  comparison.
##
CyclicShiftsOps.\< := function(l, r)
    if not IsCyclicShifts(l) then return false; fi;
    if not IsCyclicShifts(r) then return false; fi;
    return l.W < r.W or l.W = r.W and Elements(l) < Elements(r);
end;


#############################################################################
##
#F  Edges( <shifts> )  . . . . . . . . . . . . . . . . . . . . . . . . edges.
##
CyclicShiftsOps.Edges:= function(self)
    Elements(self);
    return self.edges;
end;


#############################################################################
##
#F  Transversal( <shifts> )  . . . . . . . . . . . . . . . . . . transversal.
##
CyclicShiftsOps.Transversal:= function(self)
    Elements(self);
    return self.transversal;
end;

#############################################################################
##
#F  Relation( <shifts> ) . . . . . . . . . . . . . . . . . . . . .  relation.
##


#############################################################################
##
#F  Iterator( <shifts> ) . . . . . . . . . . . . . . . . . . . . .  iterator.
##
##  the iterator version of a cyclic shift class:
##
##  <#GAPDoc Label="Iterator(shifts)">
##  <ManSection>
##  <Meth Name="Iterator" Arg="shifts" Label="for cyclic shifts"/>
##  <Returns>
##    an iterator for the elements of the prefix oject <A>prefixes</A>.
##  </Returns>
##  <Description>
##    The prefixes of <M>w</M> in <M>W</M> ...
##  <Example>
##  gap> w:= PermCoxeterWord(CoxeterGroup("A", 5), [ 1, 2, 3, 4, 5, 4 ]);;
##  gap> ...
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
CyclicShiftsOps.Iterator:= function(self)

    local   W,  S,  orb,  pos,  next,  itr;

    W:= self.W;
    S:= W.rootInclusion{[1 .. W.semisimpleRank]};

    orb:= [self.w];
    pos:= 1;
    next:= pos;

    itr:= rec();

##
##  hasNext() simply checks whether there is more left in the orbit.
##
    itr.hasNext:= function()
        return IsBound(orb[pos]);
    end;

##
##  next() simply returns the element 'focus' is looking at.  But before it
##  does that it needs to advance 'focus' to the next element in the queue,
##  and if the queue in front of 'focus' happens to be empty it needs to
##  fill it up with prefixes of elements between 'back and 'focus'.
##
    itr.next:= function()
        local   x,  i,  s,  y,  z;

        while pos = Length(orb) and next <= pos do # expand next in line
            x:= orb[next];
            for i in S do
                s:= W.(W.rootRestriction[i]);
                y:= s * x;
                z:= y * s;
                if IsLeftDescent(W, x, i) then
                    if not IsRightDescent(W, y, i) then
                        if not z in orb then
                            Add(orb, z);
                        fi;
                    fi;
                else
                    if IsRightDescent(W, y, i) then
                        if not z in orb then
                            Add(orb, z);
                        fi;
                    fi;
                fi;
            od;
            next:= next + 1;
        od;
        x:= orb[pos];
        pos:= pos + 1;
        return x;
    end;

    return itr;
end;

#############################################################################
##
#F  OneBelow( <shifts> )
##
##  find an element immediately below this cyclic shift class, or
##  return false if none exists.
##
##  FIXME: using the iterator presumably would be faster ...
##
CyclicShiftsOps.OneBelow:= function(self)
    Elements(self);
    if self.below = [] then
        return false;
    else
        return self.below[1];
    fi;
end;


#############################################################################
##
#F  OneAbove( <shifts> )
##
##  find an element immediately above this cyclic shift class, or
##  return false if none exists.
##
##  FIXME: using the iterator presumably would be faster ...
##
CyclicShiftsOps.OneAbove:= function(self)
    Elements(self);
    if self.above = [] then
        return false;
    else
        return self.above[1];
    fi;
end;


#############################################################################
##
#F  MinimalLengthConjugate:= function(W, w)
##
##  find a conjugate of w of minimal length.
##
MinimalLengthConjugate:= function(W, w)
    local   cyc;

    cyc:= CyclicShifts(W, w);
    while not Call(cyc, "IsMinimal") do
        cyc:= CyclicShifts(W, Call(cyc, "OneBelow"));
    od;
    return cyc.w;
end;


#############################################################################
##
#F  MaximalLengthConjugate:= function(W, w)
##
##  find a conjugate of w of maximal length.
##
MaximalLengthConjugate:= function(W, w)
    local   cyc;

    cyc:= CyclicShifts(W, w);
    while not Call(cyc, "IsMaximal") do
        cyc:= CyclicShifts(W, Call(cyc, "OneAbove"));
    od;
    return cyc.w;
end;


#############################################################################
##
#F  CentralizerComplement( <W>, <w> )  . . . . . . . . . . . . . centralizer.
##
##  <#GAPDoc Label="CentralizerComplement">
##  <ManSection>
##  <Func Name="CentralizerComplement" Arg="W, w"/>
##  <Func Name="CentralizerComplementMinimal" Arg="W, w"/>
##  <Returns>
##    a complement of the centralizer of <A>w</A> in the smallest parabolic
##    subgroup of <A>W</A> containing <A>w</A>, or <C>false</C> if none
##    exists.
##  </Returns>
##  <Description>
##    The centralizer of <M>w</M> in <M>W</M> is ...
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;  W.name:= "W";;
##  ...
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
CyclicShiftsOps.Complement0:= function(self)
    local   W,  w,  J,  WJ,  NJ,  CJ,  gen,  res,  x,  new,  K,  wK,
            car,  can;

    W:= self.W;
    w:= self.w;

    # assert that w has minimal length in its class.
    J:= Set(CoxeterWord(W, w));
    WJ:= ReflectionSubgroup(W, J);
    NJ:= NormalizerComplement(W, J);
    CJ:= Centralizer(WJ, NJ);
    gen:= Generators(NJ);

    res:= [];
    for x in gen do
        # don't fix what's not broken.
        if w^x = w then
            new:= [()];
        else
            new:= [];
            for K in SubsetsShapes(Shapes(WJ)) do
                wK:= LongestElement(W, K);
                if wK in CJ and w^x = w^wK then
                    Add(new, wK);
                fi;
            od;
            if new = [] then
                return false;
            fi;
        fi;
        Add(res, new);
    od;

    # try all combinations of possible generators.
    for car in Cartesian(res) do
        can:= List([1..Length(gen)], i-> gen[i] * car[i]);
        can:= Subgroup(W, can);
        can.gen:= gen;
        can.car:= car;
        if Size(Intersection(can, WJ)) = 1 and Size(can) = Size(NJ) then
            return can;
#        else
#            Print("-\c");
        fi;
    od;

    # if everything fails ...
    return false;
end;

CyclicShiftsOps.Complement1:= function(self)
    local   W,  w,  J,  WJ,  NJ,  gen,  res,  x,  new,  K,  wK,  car,
            can;

    W:= self.W;
    w:= self.w;

    # assert that w has minimal length in its class.
    J:= Set(CoxeterWord(W, w));
    WJ:= ReflectionSubgroup(W, J);
    NJ:= NormalizerComplement(W, J);
    gen:= Generators(NJ);

    res:= [];
    for x in gen do
        # don't fix what's not broken.
        if w^x = w then
            new:= [()];
        else
            new:= [];
            for K in SubsetsShapes(Shapes(WJ)) do
                wK:= LongestElement(W, K);
                if x^wK = x and w^x = w^wK then
                    Add(new, wK);
                fi;
            od;
            if new = [] then
                return false;
            fi;
        fi;
        Add(res, new);
    od;

    # try all combinations of possible generators.
    for car in Cartesian(res) do
        can:= List([1..Length(gen)], i-> gen[i] * car[i]);
        can:= Subgroup(W, can);
        can.gen:= gen;
        can.car:= car;
        if Size(Intersection(can, WJ)) = 1 and Size(can) = Size(NJ) then
            return can;
#        else
#            Print("+\c");
        fi;
    od;

    # if everything fails ...
    return false;
end;


# minimal length case.
CentralizerComplementMinimal:= function(W, w)
    local   v,  com,  u;

    # first round: try to find wK's that centralize all of NJ
    for v in Elements(CyclicShifts(W, w)) do
        com:= Call(CyclicShifts(W, v), "Complement0");
        if com <> false then
            u:= RepresentativeOperation(W, v, w);
            return com^u;
        fi;
    od;

    # second round: relax centralising condition
    for v in Elements(CyclicShifts(W, w)) do
        com:= Call(CyclicShifts(W, v), "Complement1");
        if com <> false then
            u:= RepresentativeOperation(W, v, w);
            return com^u;
        fi;
    od;

    return false;
end;


# general case ...
CentralizerComplement:= function(W, w)
    local   m,  com,  u;
    m:= MinimalLengthConjugate(W, w);
    com:= CentralizerComplementMinimal(W, m);
    if com = false then
        return false;
    fi;
    u:= RepresentativeOperation(W, m, w);
    return com^u;
end;


# lab is a pair of partitions
IsNonCompliant:= function(lab)
    return
      Length(lab[2]) > 0 and
      Length(lab[2]) mod 2 = 0 and
      ForAll(lab[2], x-> x mod 2 = 0) and
      ForAny(lab[1], x-> x mod 2 = 1);
end;


# cuspidal classes
CuspidalClasses:= function(W)
    local   cc,  n;

    cc:= ConjugacyClasses(W);
    n:= W.semisimpleRank;
    return Filtered([1..Length(cc)], i->
                   Size(Set(CoxeterWord(W, Representative(cc[i])))) = n);
end;



#############################################################################
##
##  <#GAPDoc Label="CyclicShiftClasses">
##  <ManSection>
##  <Func Name="CyclicShiftClasses" Arg="W, w"/>
##  <Returns>
##    the set of all cyclic shift classes in the conjugacy class of
##    the element <A>w</A> of the finite Coxeter group <A>W</A>.
##  </Returns>
##  <Description>
##  This function computes the partition of the conjugacy class of
##  the element <A>w</A> in the finite Coxeter group <A>W</A>
##  into cyclic shift classes;
##  see <Ref Func="CyclicShifts"/>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;  W.name:= "W";;
##  gap> cyc:= CyclicShiftClasses(W, PermCoxeterWord(W, [1..3]));
##  [ CyclicShifts( W, ( 1,12, 3, 2)( 4,11,10, 5)( 6, 9, 8, 7) ),
##    CyclicShifts( W, ( 1, 3, 7, 9)( 2,11, 6,10)( 4, 8, 5,12) ) ]
##  gap> List(cyc, Size);
##  [ 4, 2 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
CyclicShiftClasses:= function(W, w)
    local   classes,  a,  old,  new,  all,  cyc;

    # make sure w has minimal length in its class
    w:= MinimalLengthConjugate(W, w);

    # initialize list with minimal length cyclic shift classes.
    classes:= [];
    for a in Call(Shape(W, Set(CoxeterWord(W, w))), "Transversal") do
        Add(classes, CyclicShifts(W, w^a));
    od;

    # grow to completion.
    old:= classes;
    while old <> [] do
        new:= [];
        all:= Union(Map(old, "AllAbove"));
        while all <> [] do
            cyc:= CyclicShifts(W, all[1]);
            Add(new, cyc);
            all:= Difference(all, cyc);
        od;
        Append(classes, new);
        old:= new;
    od;

    # return result.
    return classes;
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
