#############################################################################
##
#A  $Id: subsets.g,v 1.24 2007/10/11 11:28:04 goetz Exp $
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2001-2007 Götz Pfeiffer
##
##  This file contains structures and functions for certain subsets of a 
##  finite Coxeter group.
##
##  <#GAPDoc Label="Intro:Subsets">
##    A finite Coxeter group <M>W</M> has various important subsets, which
##    are neither groups nor cosets.  In this chapter we collect some common
##    functionality for prefix sets of elements of <M>W</M>, minimal length
##    transversals of cosets and double cosets of parabolic subgroups, and
##    other sets related to these.<P/>
##
##    The functions described in this chapter are implemented in the file
##    <F>subsets.g</F>.  
##  <#/GAPDoc>
##  

#############################################################################
##
##  Prefixes.  
##
##  <#GAPDoc Label="Intro:Prefixes">
##    An element <M>v \in W</M> is called a
##    <E>prefix</E><Index>prefix</Index> of an element <M>w \in W</M> if
##    there exist an element <M>v' \in W</M> such that <M>w = vv'</M> and
##    <M>\ell(w) = \ell(v) + \ell(v')</M>.  In that case we write <M>v \leq
##    w</M>.  In other words, <M>v \leq w</M> if <M>\ell(w) - \ell(v) =
##    \ell(v^{-1} w)</M>.  The prefix set of <M>w \in W</M> is the set <M>\{v
##    \in W : v \leq w\}</M> of all prefixes <M>v</M> of <M>w</M>.  Many
##    types of subsets in this chapter are in some way described by sets of
##    prefixes of a given word.
##  <#/GAPDoc>
##
##  TODO: the prefixes form a lattice ...
##

#############################################################################
##
#O  PrefixesOps . . . . . . . . . . . . . . . . . . . . .  operations record.
##
##  A Prefixes is a Domain.
##
PrefixesOps:= OperationsRecord("PrefixesOps", DomainOps);

#############################################################################
##
#C  Prefixes( <W>, <w> ) . . . . . . . . . . . . . . . . . . . . constructor.
##
##  <#GAPDoc Label="Prefixes">
##  <ManSection>
##  <Func Name="Prefixes" Arg="W, w"/>
##  <Returns>
##    an object that represents the prefixes  of <A>w</A> in 
##    <A>W</A>. 
##  </Returns>
##  <Description>
##    This is the constructor for the prefixes class.  It constructs and
##    returns the prefixes of the element <A>w</A> in the finite Coxeter
##    group <A>W</A>.
##  <Example>
##  gap> w:= PermCoxeterWord(CoxeterGroup("A", 5), [ 1, 2, 3, 4, 5, 4 ]);;
##  gap> pre:= Prefixes(W, w);
##  Prefixes( CoxeterGroup("A", 5), ( 1,30, 9, 3, 2)( 4, 8,11,13,20)
##  ( 5,19,23,26,28)( 6,29,25,12, 7)(10,27,22,21,14)(15,24,18,17,16) )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
Prefixes:= function(W, w)
    return 
      rec(
          isDomain:= true,
          isPrefixes:= true,
          operations:= PrefixesOps,
          W:= W,
          w:= w
          );
end;


#############################################################################
##
#F  IsPrefixes( <obj> ) . . . . . . . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsPrefixes">
##  <ManSection>
##  <Func Name="IsPrefixes" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a prefixes object and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsPrefixes:= function(obj)
    return IsRec(obj) and IsBound(obj.isPrefixes) and obj.isPrefixes = true;
end;


#############################################################################
##
#F  Print( <prefixes> ) . . . . . . . . . . . . . . . . . . . . . . .  print.
##
PrefixesOps.Print:= function(self)
    Print("Prefixes( ", self.W, ", ", self.w, " )");
end;


#############################################################################
##
#F  <w> in <prefixes>  . . . . . . . . . . . . . . . . . . . . .  membership.
## 
##  <w> is in the prefix set  <prefixes> if and only if ...
##
PrefixesOps.\in:= function(w, self)
    return CoxeterLength(w^-1 * self.w) = 
           CoxeterLength(self.w) - CoxeterLength(w);
end;


#############################################################################
##
#F  Elements( <prefixes> ) . . . . . . . . . . . . . . . . . . . .  elements.
##
##  <#GAPDoc Label="Elements(prefixes)">
##  <ManSection>
##  <Meth Name="Elements" Arg="prefixes" Label="for prefixes"/>
##  <Returns>
##    the set of elements of the prefix oject <A>prefixes</A>.
##  </Returns>
##  <Description>
##    The prefixes of <M>w</M> in <M>W</M> ...
##  <Example>
##  gap> w:= PermCoxeterWord(CoxeterGroup("A", 5), [ 1, 2, 3, 4, 5, 4 ]);;
##  gap> pre:= Prefixes(W, w);;
##  gap> List(Elements(pre), x-> CoxeterWord(W, x));
##  [ [  ], [ 5 ], [ 1 ], [ 1, 5 ], [ 1, 2 ], [ 1, 2, 5 ], [ 1, 2, 3 ],
##    [ 1, 2, 3, 5 ], [ 1, 2, 3, 4 ], [ 1, 2, 3, 5, 4 ], [ 1, 2, 3, 4, 5 ],
##    [ 1, 2, 3, 4, 5, 4 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
PrefixesOps.Elements:= function(self)
    local W, X, Y, Z, S, i, x, y, k, edges, perm;

    W:= self.W;
    S:= W.rootInclusion{[1 .. W.semisimpleRank]};
    Y:= [self.w];  X:= [];  edges:= [];  k:= 0;
    while Y <> [] do
        Append(X, Y);
        Z:= [];
        for x in Y do
            k:= k + 1;  edges[k]:= [];
            for i in S do
                if i / x > W.parentN then
                    y:= x * W.(W.rootRestriction[i]);
                    AddSet(Z, y);
                    edges[k][i]:= y;
                fi;
            od;
        od;
        Y:= Z;
    od;

    perm:= Sortex(X);
    edges:= Permuted(edges, perm);
    for x in edges do
        for i in [1..Length(x)] do
            if IsBound(x[i]) then
                x[i]:= Position(X, x[i]);
            fi;
        od;
    od;
    self.edges:= edges;
    
    return X;
end;

#############################################################################
##
#F  Iterator( < prefixes> ) . . . . . . . . . . . . . . . . . . . . iterator.
##
##  the iterator version of a set of prefixes:
##  it consists of a queue (linked list) of elements to be processed,
##  pointers to the back (next element to be expanded),
##  the focus (next element to be returned) and the head
##  where the next prefix is to be put in the queue.
##
##  initially:
##
##    f
##    v
##    w -> .
##    ^    ^
##    b    h
##
##
##  <#GAPDoc Label="Iterator(prefixes)">
##  <ManSection>
##  <Meth Name="Iterator" Arg="prefixes" Label="for prefixes"/>
##  <Returns>
##    an iterator for the elements of the prefix oject <A>prefixes</A>.
##  </Returns>
##  <Description>
##    The prefixes of <M>w</M> in <M>W</M> ...
##  <Example>
##  gap> w:= PermCoxeterWord(CoxeterGroup("A", 5), [ 1, 2, 3, 4, 5, 4 ]);;
##  gap> itr:= Iterator(Prefixes(W, w));
##  rec(
##    hasNext := function (  ) ... end,
##    next := function (  ) ... end )
##  gap> while itr.hasNext() do Print(CoxeterWord(W, itr.next()), "\n"); od;
##  [ 1, 2, 3, 4, 5, 4 ]
##  [ 1, 2, 3, 4, 5 ]
##  [ 1, 2, 3, 5, 4 ]
##  [ 1, 2, 3, 4 ]
##  [ 1, 2, 3, 5 ]
##  [ 1, 2, 3 ]
##  [ 1, 2, 5 ]
##  [ 1, 2 ]
##  [ 1, 5 ]
##  [ 1 ]
##  [ 5 ]
##  [  ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
PrefixesOps.Iterator:= function(self)

    local   W,  S,  head,  focus,  back,  itr;

    W:= self.W;
    S:= W.rootInclusion{[1 .. W.semisimpleRank]};

    head:= rec();
    focus:= rec(w:= self.w, next:= head);
    back:= focus; 

    itr:= rec();
    
##    
##  hasNext() simply checks whether 'focus' is lookin' at an element.
##    
    itr.hasNext:= function()
        return IsBound(focus.w);
    end;
    
##
##  next() simply returns the element 'focus' is lookin at.  But before it
##  does that it needs to advance 'focus' to the next element in the queue,
##  and if the queue in front of 'focus' happens to be empty it needs to 
##  fill it up with prefixes of elements between 'back and 'focus'.
##
    itr.next:= function()
        local   w,  x,  i,  Z, y;
        w:=  focus.w;
        focus:= focus.next;   
        if not IsBound(focus.w) then

            # expand back.w to focus.w
            Z:= [];
            while not IsIdentical(back, focus) do
                x:= back.w;
                for i in S do
                    if i / x > W.parentN then
                        y:= x * W.(W.rootRestriction[i]);
                        if not y in Z then
                            AddSet(Z, y);
                            head.w:= y;
                            head.next:= rec();
                            head:= head.next;
                        fi;
                    fi;
                od;
                back:= back.next;
            od;
        fi;
        return w;
    end;

    return itr;
end;


#############################################################################
##
#F  PrefixesOps.Edges( <prefixes> ) . . . . . . . . . . . . . . . . .  edges.
##
##  <#GAPDoc Label="Edges(prefixes)">
##  <ManSection>
##  <Meth Name="Edges" Arg="prefixes" Label="for prefixes"/>
##  <Meth Name="PrefixesOps.Edges" Arg="prefixes"/>
##  <Returns>
##    the list of edges of the graph formed by the elements of the prefixes 
##    <A>prefixes</A>.
##  </Returns>
##  <Description>
##    <C>PrefixesOps.Edges(prefixes)</C> returns a list of lists <C>l</C>
##    with <C>l[i][k]</C> containing the address <C>a</C> if vertex <C>i</C> is
##    the initial vertex of a directed edge with label <C>k</C> to vertex
##    <C>a</C>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> w:= PermCoxeterWord(W, [1,2,3,2,1]);;
##  gap> pre:= Prefixes(W, w);
##  Prefixes( CoxeterGroup("A", 3), ( 1,11)( 3,10)( 4, 9)( 5, 7)( 6,12) )
##  gap> Call(pre, "Edges");
##  [ [  ], [ ,, 1 ], [ 4 ], [ , 2 ], [ 1 ], [ 2,, 5 ], [ 9, 3 ], [ , 5 ],
##    [ , 6 ], [ 12,, 7 ], [ ,, 8 ], [ , 11, 9 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
PrefixesOps.Edges:= function(self)
    Call(self, "Elements");  # expand the prefixes.
    return self.edges;
end;


#############################################################################
##
#F  PrefixesOps.Relation( <prefixes> ) . . . . . . . . . . . . . .  relation.
##
##  <#GAPDoc Label="Relation(prefixes)">
##  <ManSection>
##  <Meth Name="Relation" Arg="prefixes" Label="for prefixes"/>
##  <Meth Name="PrefixesOps.Relation" Arg="prefixes"/>
##  <Returns>
##    the graph formed by the elements of the prefixes <A>prefixes</A> as a
##    binary relation in the sense of MONOiD <Cite Key="monoid"/>.
##  </Returns>
##  <Description>
##    <C>PrefixesOps.Relation(prefixes)</C> returns a list of lists <C>l</C>
##    with <C>l[i][k]</C> containing the address <C>a</C> if vertex <C>i</C> is
##    the initial vertex of a directed edge with label <C>k</C> to vertex
##    <C>a</C>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> w:= PermCoxeterWord(W, [1,2,3,2,1]);;
##  gap> pre:= Prefixes(W, w);
##  Prefixes( CoxeterGroup("A", 3), ( 1,11)( 3,10)( 4, 9)( 5, 7)( 6,12) )
##  gap> Call(pre, "Relation");
##  Relation( [ [  ], [ 1 ], [ 4 ], [ 2 ], [ 1 ], [ 2, 5 ], [ 3, 9 ], [ 5 ],
##  [ 6 ], [ 7, 12 ], [ 8 ], [ 9, 11 ] ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
PrefixesOps.Relation:= function(self)
    return Relation(List(Call(self, "Edges"), Set));
end;


#############################################################################
##
##  Weak (Bruhat) Intervals.
##
##  More generally, every (weak) interval [w1, w2] can be described as a
##  "shifted" prefix set.
##


#############################################################################
##
#O  WeakIntervalOps . . . . . . . . . . . . . . . . . . .  operations record.
##
##  A WeakInterval is a Domain.
##
WeakIntervalOps:= OperationsRecord("WeakIntervalOps", DomainOps);


#############################################################################
##
#C  WeakInterval( <W>, <bot>, <top> ) . . . . . . . . . . . . .  constructor.
##
##  <#GAPDoc Label="WeakInterval">
##  <ManSection>
##  <Func Name="WeakInterval" Arg="W, bot, top"/>
##  <Returns>
##    an object that represents the weak interval from <A>bot</A> to
##    <A>top</A> in <A>W</A>.
##  </Returns>
##  <Description>
##  This is the constructor for weak intervals.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;                                     
##  gap> w:= PermCoxeterWord(W, [ 1, 2, 3, 4, 5, 4 ]);;                   
##  gap> v:= PermCoxeterWord(W, [ 3, 4, 5, 4 ]);;                   
##  gap> weak:= WeakInterval(W, v, w);
##  WeakInterval( CoxeterGroup("A", 5), ( 2,14, 7)( 3,27, 9)( 4, 8,20)( 5,19,23)
##  ( 6,15,10)(12,24,18)(17,29,22)(21,30,25), ( 1,30, 9, 3, 2)( 4, 8,11,13,20)
##  ( 5,19,23,26,28)( 6,29,25,12, 7)(10,27,22,21,14)(15,24,18,17,16) )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
WeakInterval:= function(W, bot, top)
    return 
      rec(
          isDomain:= true,
          isWeakInterval:= true,
          operations:= WeakIntervalOps,
          W:= W,
          bot:= bot,
          top:= top,
          pre:= Prefixes(W, bot^-1 * top)
          );
end;


#############################################################################
##
#F  IsWeakInterval( <obj> ) . . . . . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsWeakInterval">
##  <ManSection>
##  <Func Name="IsWeakInterval" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a weak interval object and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsWeakInterval:= function(obj)
    return IsRec(obj) and IsBound(obj.isWeakInterval) 
           and obj.isWeakInterval = true;
end;


#############################################################################
##
#F  Print( <interval> )  . . . . . . . . . . . . . . . . . . . . . . . print.
##
WeakIntervalOps.Print:= function(self)
    Print("WeakInterval( ", self.W, ", ", self.bot, ", ", self.top, " )");
end;


#############################################################################
##
#F  Elements( <interval> ) . . . . . . . . . . . . . . . . . . . .  elements.
##
##  the interval [bot, top] is isomorphic to the interval [1, bot^-1 * top].
##
##  <#GAPDoc Label="Elements(interval)">
##  <ManSection>
##  <Meth Name="Elements" Arg="interval" Label="for weak intervals"/>
##  <Returns>
##    the set of elements of the weak interval <A>interval</A>.
##  </Returns>
##  <Description>
##    The interval from <M>v</M> to <M>w</M> in <M>W</M> ...
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> w:= PermCoxeterWord(W, [ 1, 2, 3, 4, 5, 4 ]);;
##  gap> v:= PermCoxeterWord(W, [ 1, 2]);;       
##  gap> interval:= WeakInterval(W, v, w);;
##  gap> List(Elements(interval), x-> CoxeterWord(W, x));
##  [ [ 1, 2 ], [ 1, 2, 5 ], [ 1, 2, 3 ], [ 1, 2, 3, 5 ], [ 1, 2, 3, 4 ], 
##    [ 1, 2, 3, 5, 4 ], [ 1, 2, 3, 4, 5 ], [ 1, 2, 3, 4, 5, 4 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
WeakIntervalOps.Elements:= function(self)
    local   list;
    list:= self.bot * Elements(self.pre);
    self.perm:= Sortex(list);
    return list;
end;


#############################################################################
##
#F  Iterator( <interval> ) . . . . . . . . . . . . . . . . . . . .  iterator.
##
##  <#GAPDoc Label="Iterator(interval)">
##  <ManSection>
##  <Meth Name="Iterator" Arg="interval" Label="for weak intervals"/>
##  <Returns>
##    an iterator for the elements of the weak interval <A>interval</A>.
##  </Returns>
##  <Description>
##    The weak interval from <M>v</M> to <M>w</M> in <M>W</M> ...
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> w:= PermCoxeterWord(W, [ 1, 2, 3, 4, 5, 4 ]);;
##  gap> v:= PermCoxeterWord(W, [ 1, 2]);;
##  gap> itr:= Iterator(WeakInterval(W, v, w));;
##  gap> while itr.hasNext() do Print(CoxeterWord(W, itr.next()), "\n"); od;
##  [ 1, 2, 3, 4, 5, 4 ]
##  [ 1, 2, 3, 4, 5 ]
##  [ 1, 2, 3, 5, 4 ]
##  [ 1, 2, 3, 4 ]
##  [ 1, 2, 3, 5 ]
##  [ 1, 2, 3 ]
##  [ 1, 2, 5 ]
##  [ 1, 2 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
WeakIntervalOps.Iterator:= function(self)
    local   preitr,  itr;
    preitr:= Iterator(self.pre);
    itr:= rec(hasNext:= preitr.hasNext);
    itr.next:= function()
        return self.bot * preitr.next();
    end;
    return itr;
end;


#############################################################################
##
#F  Size( <interval> ) . . . . . . . . . . . . . . . . . . . . . . . .  size.
##
WeakIntervalOps.Size:= function(self)
    return Size(self.pre);
end;


#############################################################################
##
#F  WeakIntervalOps.Relation( <interval> ) . . . . . . . . . . . .  relation.
##
WeakIntervalOps.Relation:= function(self)
    return Call(self.pre, "Relation")^self.perm;
end;


#############################################################################
##
##  Parabolic Transversals.  
##
##  Aka Right Coset Representatives.  Aka $X_J$, the prefix set of $w_J w_0$.
##

#############################################################################
##
#O  ParabolicTransversalOps . . . . . . . . . . . . . . .  operations record.
##
##  A ParabolicTransversal is a Prefixes.
##
ParabolicTransversalOps:= 
  OperationsRecord("ParabolicTransversalOps", PrefixesOps);


#############################################################################
##
#C  ParabolicTransversal( <W>, <J> ) . . . . . . . . . . . . . . constructor.
##
##  <#GAPDoc Label="ParabolicTransversal">
##  <ManSection>
##  <Func Name="ParabolicTransversal" Arg="W, J"/>
##  <Returns>
##    an object that represents the parabolic transversal  of <A>J</A> in 
##    <A>W</A>. 
##  </Returns>
##  <Description>
##  This is the constructor for ...
##  <Example>
##  gap> ...
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ParabolicTransversal:= function(W, J)
    ##??? need to check the arguments?
    local self;
    self:= Prefixes(W, LongestCoxeterElement(ReflectionSubgroup(W, J))
                   * LongestCoxeterElement(W));
    self.isParabolicTransversal:= true;
    self.operations:= ParabolicTransversalOps;
    self.J:= J;
    return self;
end;


#############################################################################
##
#F  IsParabolicTransversal( <obj> ) . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsParabolicTransversal">
##  <ManSection>
##  <Func Name="IsParabolicTransversal" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a parabolic transversal and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsParabolicTransversal:= function(obj)
    return IsRec(obj) and IsBound(obj.isParabolicTransversal)
           and obj.isParabolicTransversal = true;
end;


#############################################################################
##
#F  Print( <transversal> )  . . . . . . . . . . . . . . . . . . . . .  print.
##
ParabolicTransversalOps.Print:= function(self)
    Print("ParabolicTransversal( ", self.W, ", ", self.J, " )");
end;


#############################################################################
##
#F  Size( <transversal> ) . . . . . . . . . . . . . . . . . . . . . . . size.
##
ParabolicTransversalOps.Size:= function(self)
    return Index(self.W, ReflectionSubgroup(self.W, self.J));
end;


#############################################################################
##
#F  <w> in <transversal> . . . . . . . . . . . . . . . . . . . .  membership.
## 
##  <w> is in the parabolic transversal <transversal> if and only if its 
##  LeftDescentSet  is disjoint from J.
##
ParabolicTransversalOps.\in:= function(w, self)
    local W, res, j;
    W:= self.W;  res:= [];
    for j in W.rootInclusion{[1 .. W.semisimpleRank]} do
        if j in self.J and j^w > W.parentN then
            return false;
        fi;
    od;
    return true;
end;


#############################################################################
##
##  Descent Classes. 
##
##  Aka $Y_K$.  They are not prefix sets, but shifted prefix sets.
##
##  (called classes because they partition $W$ into $2^n$ classes.)
##
# And how to make $Y_K$?  Here $K \subseteq \{1, \dots, n\}$.
# Use: $Y_K$ is the interval from $w_{\hat{K}}$ to $w_K w_0$.
# Which is isomorphic to the interval from $1$ to $w = w_{\hat{K}} w_K w_0$.
#
# Here Y_K = { w \in W : sw > w <==> s \in K }
#

#############################################################################
##
#O  DescentClassOps . . . . . . . . . . . . . . . . . . .  operations record.
##
##  A DescentClass is a WeakInterval.
##
DescentClassOps:= OperationsRecord("DescentClassOps", WeakIntervalOps);


#############################################################################
##
#C  DescentClass( <W>, <K> ) . . . . . . . . . . . . . . . . . . constructor.
##
##  <#GAPDoc Label="DescentClass">
##  <ManSection>
##  <Func Name="DescentClass" Arg="W, K"/>
##  <Returns>
##    an object that represents the descent class  of <A>K</A> in 
##    <A>W</A>. 
##  </Returns>
##  <Description>
##    This is the constructor for the descent class <M>Y_K</M> in <M>W</M>.
##    It is represented as the weak interval <M>[w_{\hat{K}}, w_K w_0]</M>.
##  <Example>
##  gap> ...
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##??? ReflectionSubgroup safe?
##
DescentClass:= function(W, K)
    local   n,  w1,  w2,  self;
    ##??? need to check the arguments?
    
    n:= W.semisimpleRank;   
    w1:= LongestCoxeterElement(ReflectionSubgroup(W, Difference([1..n], K)));
    w2:= LongestCoxeterElement(ReflectionSubgroup(W, K)) 
         * LongestCoxeterElement(W);
    self:= WeakInterval(W, w1, w2);   
    self.operations:= DescentClassOps;
    self.isDescentClass:= true;
    self.K:= K;
    return self;
end;


#############################################################################
##
#F  IsDescentClass( <obj> ) . . . . . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsDescentClass">
##  <ManSection>
##  <Func Name="IsDescentClass" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a descent class and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsDescentClass:= function(obj)
    return IsRec(obj) and IsBound(obj.isDescentClass)
           and obj.isDescentClass = true;
end;


#############################################################################
##
#F  Print( <class> )  . . . . . . . . . . . . . . . . . . . . . . . .  print.
##
DescentClassOps.Print:= function(self)
    Print("DescentClass( ", self.W, ", ", self.K, " )");
end;


#############################################################################
##
#F  <w> in <class> . . . . . . . . . . . . . . . . . . . . . . .  membership.
## 
##  <w> is in the descent class <class> if and only if its LeftDescentSet
##  is the complement of K in S.
##
DescentClassOps.\in:= function(w, self)
    local W, res, j;
    W:= self.W;  res:= [];
    for j in W.rootInclusion{[1 .. W.semisimpleRank]} do
        if j^w <= W.parentN then
            Add(res, j);
        fi;
    od;
    return res = self.K;
end;


#############################################################################
##
#F  Representative( <class> ) . . . . . . . . . . . . . . . . representative.
##
DescentClassOps.Representative:= function(self)
    return self.bot;  # which is $w_{\bar{K}}$.
end;


#############################################################################
##
#F  Size( <class> ) . . . . . . . . . . . . . . . . . . . . . . . . . . size.
##
##  Is there quick way to a way to find the size of a DescentClass
##  without listing all its elements?
##  Yes:
##  |Y_K| = \sum_{J contains K} (-1)^{|J - K|} |X_J|
##
DescentClassOps.Size:= function(self)
    local   sum,  L;

    sum:= 0;    # loop over all J above K.
    for L in Combinations(Difference([1..self.W.semisimpleRank], self.K)) do
        sum:= sum + (-1)^Size(L) 
              * Size(ParabolicTransversal(self.W, Union(self.K, L)));
    od;
    return sum;
end;

    
#############################################################################
##
#F  DescentClasses( <W> ) . . . . . . . . . . . . . . . . .  descent classes.
##
##  <#GAPDoc Label="DescentClasses">
##  <ManSection>
##  <Func Name="DescentClasses" Arg="W"/>
##  <Returns>
##    the list of descent classes of the Coxeter group <A>W</A> in shape
##    order (see <Ref Func="SubsetsShapes"/>).
##  </Returns>
##  <Description>
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;  W.name:= "W";;
##  gap> DescentClasses(W);
##  [ DescentClass( W, [  ] ), DescentClass( W, [ 1 ] ), DescentClass( W, [ 2 ] ),
##    DescentClass( W, [ 3 ] ), DescentClass( W, [ 1, 3 ] ),
##    DescentClass( W, [ 1, 2 ] ), DescentClass( W, [ 2, 3 ] ),
##    DescentClass( W, [ 1, 2, 3 ] ) ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
DescentClasses:= function(W)
    return List(SubsetsShapes(Shapes(W)), x-> DescentClass(W, x));
end;


#############################################################################
##
##  Left Coset Representatives.
##
##  A Left Parabolic Transversal is not a Prefixes set, so cannot
##  inherit. But composition works.
##


#############################################################################
##
#O  LeftParabolicTransversalOps . . . . . . . . . . . . .  operations record.
##
##  A LeftParabolicTransversal is a Domain.
##
LeftParabolicTransversalOps:= 
  OperationsRecord("LeftParabolicTransversalOps", DomainOps);


#############################################################################
##
#C  LeftParabolicTransversal( <W>, <J> ) . . . . . . . . . . . . constructor.
##
##  <#GAPDoc Label="LeftParabolicTransversal">
##  <ManSection>
##  <Func Name="LeftParabolicTransversal" Arg="W, J"/>
##  <Returns>
##    an object that represents the left parabolic transversal of <A>J</A> in 
##    <A>W</A>. 
##  </Returns>
##  <Description>
##  This is the constructor for ...
##  <Example>
##  gap> ...
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
LeftParabolicTransversal:= function(W, J)
    return 
      rec(
          isDomain:= true,
          isLeftParabolicTransversal:= true,
          operations:= LeftParabolicTransversalOps,
          W:= W,
          J:= J,
          right:= ParabolicTransversal(W, J)
          );
end;


#############################################################################
##
#F  Print( <transversal> )  . . . . . . . . . . . . . . . . . . . . .  print.
##
LeftParabolicTransversalOps.Print:= function(self)
    Print("LeftParabolicTransversal( ", self.W, ", ", self.J, " )");
end;


#############################################################################
##
#F  IsLeftParabolicTransversal( <obj> ) . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsLeftParabolicTransversal">
##  <ManSection>
##  <Func Name="IsLeftParabolicTransversal" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a left parabolic transversal and
##    <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsLeftParabolicTransversal:= function(obj)
    return IsRec(obj) and IsBound(obj.isLeftParabolicTransversal) and
           obj.isLeftParabolicTransversal = true;
end;


#############################################################################
##
#F  Size( <transversal> ) . . . . . . . . . . . . . . . . . . . . . . . size.
##
LeftParabolicTransversalOps.Size:= function(self)
    return Size(self.right);
end;


#############################################################################
##
#F  Elements( < transversal> )  . . . . . . . . . . . . . . . . . . elements.
##
LeftParabolicTransversalOps.Elements:= function(self)
    return Set(List(Elements(self.right), x-> x^-1));
end;


#############################################################################
##
#F  Iterator( < transversal> )  . . . . . . . . . . . . . . . . . . iterator.
##
LeftParabolicTransversalOps.Iterator:= function(self)
    local   right,  itr;
    right:= Iterator(self.right);
    itr:= rec(hasNext:= right.hasNext());
    itr.next:= function()
        return right.next()^-1;
    end;
    return itr;
end;


#############################################################################
##
#F  <w> in <transversal> . . . . . . . . . . . . . . . . . . . .  membership.
## 
LeftParabolicTransversalOps.\in:= function(w, self)
    return w^-1 in self.right;
end;


#############################################################################
##
##  Double Coset Reps.
##


#############################################################################
##
#O  DoubleParabolicTransversalOps . . . . . . . . . . . .  operations record.
##
##  A DoubleParabolicTransversal is a Domain.
##
DoubleParabolicTransversalOps:= 
  OperationsRecord("DoubleParabolicTransversalOps", DomainOps);


#############################################################################
##
#C  DoubleParabolicTransversal( <W>, <J>, <K> )  . . . . . . . . constructor.
##
##  <#GAPDoc Label="DoubleParabolicTransversal">
##  <ManSection>
##  <Func Name="DoubleParabolicTransversal" Arg="W, J, K"/>
##  <Returns>
##    an object that represents the double parabolic transversal of <A>J</A>
##    and <A>K</A> in <A>W</A>.
##  </Returns>
##  <Description>
##  This is the constructor for ...
##  <Example>
##  gap> ...
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
DoubleParabolicTransversal:= function(W, J, K)
    return 
      rec(
          isDomain:= true,
          isDoubleParabolicTransversal:= true,
          operations:= DoubleParabolicTransversalOps,
          W:= W,
          J:= J,
          K:= K
          );
end;


#############################################################################
##
#F  Print( <transversal> )  . . . . . . . . . . . . . . . . . . . . .  print.
##
DoubleParabolicTransversalOps.Print:= function(self)
    Print("DoubleParabolicTransversal( ", self.W, ", ", self.J, ", ", 
          self.K, " )");
end;


#############################################################################
##
#F  IsDoubleParabolicTransversal( <obj> ) . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsDoubleParabolicTransversal">
##  <ManSection>
##  <Func Name="IsDoubleParabolicTransversal" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a left parabolic transversal and
##    <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsDoubleParabolicTransversal:= function(obj)
    return IsRec(obj) and IsBound(obj.isDoubleParabolicTransversal) and
           obj.isDoubleParabolicTransversal = true;
end;


#############################################################################
##
#F  Elements( <transversal> ) . . . . . . . . . . . . . . . . . . . elements.
##
##  The algorithm used here is different from  Algorithm E (p.51), because
##  that one doesn't actually find all double cosets :-(
##
DoubleParabolicTransversalOps.Elements:= function(self)
    local   left,  itr,  list,  w;
    
    left:= LeftParabolicTransversal(self.W, self.K);
    itr:= Iterator(ParabolicTransversal(self.W, self.J));
    list:= [];
    while itr.hasNext() do
        w:= itr.next();
        if w in left then
            Add(list, w);
        fi;
    od;
    
    return Set(list);
        
#    return Filtered(Elements(ParabolicTransversal(self.W, self.J)),
#                   w-> w in LeftParabolicTransversal(self.W, self.K));
end;


#############################################################################
##
##  XJKLs.
##

#############################################################################
##
#O  XJKLOps . . . . . . . . . . . . . . . . . . . . . . .  operations record.
##
##  An XJKL is a Domain.
##
XJKLOps:= OperationsRecord("XJKLOps", DomainOps);


#############################################################################
##
#C  XJKL( <W>, <J>, <K>, <L> )  . . . . . . . . . . . . . . . .  constructor.
##
##  <#GAPDoc Label="XJKL">
##  <ManSection>
##  <Func Name="XJKL" Arg="W, J, K, L"/>
##  <Returns>
##    an object that represents the set <M>X_{JKL}</M> for the subsets
##    <A>J</A>, <A>K</A>, and <A>L</A> in <A>W</A>.
##  </Returns>
##  <Description>
##  This is the constructor for ...
##  <Example>
##  gap> ...
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
XJKL:= function(W, J, K, L)
    #??? take care of special cases
    # J or K or L = S or 0
    # J = K = L
    return 
      rec(
          isDomain:= true,
          isXJKL:= true,
          operations:= XJKLOps,
          W:= W,
          J:= J,
          K:= K,
          L:= L
          );
end;


#############################################################################
##
#F  Print( <xjkl> ) . . . . . . . . . . . . . . . . . . . . . . . . .  print.
##
XJKLOps.Print:= function(self)
    Print("XJKL( ", self.W, ", ", self.J, ", ", self.K, ", ", self.L, " )");
end;


#############################################################################
##
#F  IsXJKL( <obj> ) . . . . . . . . . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsXJKL">
##  <ManSection>
##  <Func Name="IsXJKL" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is an <M>X_{JKL}</M> object and
##    <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsXJKL:= function(obj)
    return IsRec(obj) and IsBound(obj.isXJKL) and obj.isXJKL = true;
end;


#############################################################################
##
#F  Elements( <xjkl> ) . . . . . . . . . . . . . . . . . . . . . .  elements.
##
XJKLOps.Elements:= function(self)
    return 
      Filtered(Elements(DoubleParabolicTransversal(self.W, self.J, self.K)),
              d -> Intersection(
                      List(OnSets(self.J, d), x-> (x-1) mod self.W.parentN + 1),
                      self.K) = self.L);
end;


#############################################################################
XJKLOps.\*:= function(l, r)
    if IsXJKL(r) then
        if l in r.W then
            return Set(List(Elements(r), x-> l * x));
        else
            Error("don't know how to multiply <l> and XJKL");
        fi;
    elif IsXJKL(l) then
        if r in l.W then
            return Set(List(Elements(l), x-> x * r));
        else
            Error("don't know how to multiply XJKL and <r>");
        fi;
    else
        Error("Panic: neither <l> nor <r> is XJKL!");
    fi;
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
