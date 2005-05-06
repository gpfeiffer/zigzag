#############################################################################
##
#A  subsets.g                    Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2004, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: subsets.g,v 1.9 2005/05/06 13:48:03 goetz Exp $
##
##  This file contains structures and functions for certain subsets of a 
##  finite Coxeter group.
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
##  Prefixes.  All types of subsets in this file are in some sense sets of
##  prefixes of a given word.  So we provide the general functions first.
##
##  TODO: the prefixes form a lattice ...
##

#############################################################################
##
#O  PrefixesOps . . . . . . . . . . . . . . . . . . . . .  operations record.
##
##  A Prefix is a Domain.
##
PrefixesOps:= OperationsRecord("PrefixesOps", DomainOps);

#############################################################################
##
#C  Prefixes( <W>, <w> ) . . . . . . . . . . . . . . . . . . . . constructor.
##
##  represents the prefixes of a given element w in W.
##  ??? find more descriptive names for w and W.  coxeterGroup and element?
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
IsPrefixes:= function(obj)
    return IsRec(obj) and IsBound(obj.isPrefixes) and obj.isPrefixes = true;
end;


#############################################################################
##
#F  Print( <prefixes> ) . . . . . . . . . . . . . . . . . . . . . . .  print.
##
PrefixesOps.Print:= function(this)
    Print("Prefixes( ", this.W, ", ", this.w, " )");
end;


#############################################################################
##
#F  Elements( <prefixes> ) . . . . . . . . . . . . . . . . . . . .  elements.
##
PrefixesOps.Elements:= function(this)
    local W, X, Y, Z, S, i, x, y, k, edges, perm;

    W:= this.W;
    S:= W.rootInclusion{[1 .. W.semisimpleRank]};
    Y:= [this.w];  X:= [];  edges:= [];  k:= 0;
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
    this.edges:= edges;
    
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
PrefixesOps.Iterator:= function(this)

    local   W,  S,  head,  focus,  back,  itr;

    W:= this.W;
    S:= W.rootInclusion{[1 .. W.semisimpleRank]};

    head:= rec();
    focus:= rec(w:= this.w, next:= head);
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
PrefixesOps.Edges:= function(this)
    this.operations.Elements(this);  # expand the prefixes.
    return this.edges;
end;


#############################################################################
##
#F  PrefixesOps.Relation( <prefixes> )
##
PrefixesOps.Relation:= function(this)
    return Relation(List(this.operations.Edges(this), Set));
end;


#############################################################################
##
##  Weak (Bruhat) Intervals.  More generally, every (weak) interval [w1, w2]
##  can be described as a "shifted" prefix set.
##


#############################################################################
##
#O  WeakIntervalOps . . . . . . . . . . . . . . . . . . .  operations record.
##
WeakIntervalOps:= OperationsRecord("WeakIntervalOps", DomainOps);


#############################################################################
##
#C  WeakInterval( <W>, <bot>, <top> ) . . . . . . . . . . . . .  constructor.
##
##  represents the interval from <bot> to <top> in <W>.
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
IsWeakInterval:= function(obj)
    return IsRec(obj) and IsBound(obj.isWeakInterval) 
           and obj.isWeakInterval = true;
end;


#############################################################################
##
#F  Print( <interval> )  . . . . . . . . . . . . . . . . . . . . . . . print.
##
WeakIntervalOps.Print:= function(this)
    Print("WeakInterval( ", this.W, ", ", this.bot, ", ", this.top, " )");
end;


#############################################################################
##
#F  Elements( <interval> ) . . . . . . . . . . . . . . . . . . . .  elements.
##
##  the interval [bot, top] is isomorphic to the interval [1, bot^-1 * top].
##
WeakIntervalOps.Elements:= function(this)
    local   list;
    list:= this.bot * Elements(this.pre);
    this.perm:= Sortex(list);
    return list;
end;


#############################################################################
##
#F  Iterator( <interval> ) . . . . . . . . . . . . . . . . . . . .  iterator.
##
WeakIntervalOps.Iterator:= function(this)
    local   preitr,  itr;
    preitr:= Iterator(this.pre);
    itr:= rec(hasNext:= preitr.hasNext);
    itr.next:= function()
        return this.bot * preitr.next();
    end;
    return itr;
end;


#############################################################################
##
#F  Size( <interval> ) . . . . . . . . . . . . . . . . . . . . . . . .  size.
##
WeakIntervalOps.Size:= function(this)
    return Size(this.pre);
end;


#############################################################################
##
#F  WeakIntervalOps.Relation( <interval> )
##
WeakIntervalOps.Relation:= function(this)
    return this.pre.operations.Relation(this.pre)^this.perm;
end;


#############################################################################
##
##  Coset Representatives.  Aka $X_J$.  Is the prefix set of $w_J w_0$.
##
ParabolicTransversalOps:= 
  OperationsRecord("ParabolicTransversalOps", PrefixesOps);


#############################################################################
ParabolicTransversal:= function(W, J)
    ##??? need to check the arguments?
    local this;
    this:= Prefixes(W, LongestCoxeterElement(ReflectionSubgroup(W, J))
                   * LongestCoxeterElement(W));
    this.isParabolicTransversal:= true;
    this.operations:= ParabolicTransversalOps;
    this.J:= J;
    return this;
end;


#############################################################################
IsParabolicTransversal:= function(obj)
    return IsRec(obj) and IsBound(obj.isParabolicTransversal)
           and obj.isParabolicTransversal = true;
end;


#############################################################################
ParabolicTransversalOps.Print:= function(this)
    Print("ParabolicTransversal( ", this.W, ", ", this.J, " )");
end;


#############################################################################
ParabolicTransversalOps.Size:= function(this)
    return Index(this.W, ReflectionSubgroup(this.W, this.J));
end;

#############################################################################
##
##  <w> in <transversal>
## 
##  <w> is in the parabolic transversal <transversal> if and only if its 
##  LeftDescentSet  is disjoint from J.
##
ParabolicTransversalOps.\in:= function(w, this)
    local W, res, j;
    W:= this.W;  res:= [];
    for j in W.rootInclusion{[1 .. W.semisimpleRank]} do
        if j in this.J and j^w > W.parentN then
            return false;
        fi;
    od;
    return true;
end;


#############################################################################
##
##  Descent Classes. Aka $Y_K$.  They are not prefix sets,  but shifted 
##  prefix sets.
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
DescentClassOps:= OperationsRecord("DescentClassOps", WeakIntervalOps);

#############################################################################
##
##??? ReflectionSubgroup safe?
##
DescentClass:= function(W, K)
    local   n,  w1,  w2,  this;
    ##??? need to check the arguments?
    
    n:= W.semisimpleRank;   
    w1:= LongestCoxeterElement(ReflectionSubgroup(W, Difference([1..n], K)));
    w2:= LongestCoxeterElement(ReflectionSubgroup(W, K)) 
         * LongestCoxeterElement(W);
    this:= WeakInterval(W, w1, w2);   
    this.operations:= DescentClassOps;
    this.isDescentClass:= true;
    this.K:= K;
    return this;
end;


#############################################################################
IsDescentClass:= function(obj)
    return IsRec(obj) and IsBound(obj.isDescentClass)
           and obj.isDescentClass = true;
end;


#############################################################################
DescentClassOps.Print:= function(this)
    Print("DescentClass( ", this.W, ", ", this.K, " )");
end;


#############################################################################
##
##  <w> in <class>
## 
##  <w> is in the descent class <class> if and only if its LeftDescentSet
##  is the complement of K in S.
##
DescentClassOps.\in:= function(w, this)
    local W, res, j;
    W:= this.W;  res:= [];
    for j in W.rootInclusion{[1 .. W.semisimpleRank]} do
        if j^w <= W.parentN then
            Add(res, j);
        fi;
    od;
    return res = this.K;
end;


#############################################################################
DescentClassOps.Representative:= function(this)
    return this.bot;  # which is $w_{\bar{K}}$.
end;

#############################################################################
##
##  Is there quick way to a way to find the size of a DescentClass
##  without listing all its elements?
##  Yes:
##  |Y_K| = \sum_{J contains K} (-1)^{|J - K|} |X_J|
##
DescentClassOps.Size:= function(this)
    local   sum,  L;

    sum:= 0;    # loop over all J above K.
    for L in Combinations(Difference([1..this.W.semisimpleRank], this.K)) do
        sum:= sum + (-1)^Size(L) 
              * Size(ParabolicTransversal(this.W, Union(this.K, L)));
    od;
    return sum;
end;

    
#############################################################################
##
##  list all of them in shapes order.
##
##??? remember them in W? No.
##
DescentClasses:= function(W)
    return List(SubsetsShapes(Shapes(W)), x-> DescentClass(W, x));
end;


#############################################################################
##
##  What about left coset reps?  I know they are just the inverses ... but
##  how do they fit into this scheme best?
##


#############################################################################
##
##  is not a Prefixes set, so can't inherit. But composition works.
##
LeftParabolicTransversalOps:= 
  OperationsRecord("LeftParabolicTransversalOps", DomainOps);


#############################################################################
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
LeftParabolicTransversalOps.Print:= function(this)
    Print("LeftParabolicTransversal( ", this.W, ", ", this.J, " )");
end;


#############################################################################
IsLeftParabolicTransversal:= function(obj)
    return IsRec(obj) and IsBound(obj.isLeftParabolicTransversal) and
           obj.isLeftParabolicTransversal = true;
end;


#############################################################################
LeftParabolicTransversalOps.Size:= function(this)
    return Size(this.right);
end;


#############################################################################
LeftParabolicTransversalOps.Elements:= function(this)
    return Set(List(Elements(this.right), x-> x^-1));
end;


#############################################################################
LeftParabolicTransversalOps.Iterator:= function(this)
    local   right,  itr;
    right:= Iterator(this.right);
    itr:= rec(hasNext:= right.hasNext());
    itr.next:= function()
        return right.next()^-1;
    end;
    return itr;
end;


#############################################################################
LeftParabolicTransversalOps.\in:= function(w, this)
    return w^-1 in this.right;
end;



#############################################################################
##
##  Double Coset Reps.
##
##  TODO ...
##

#############################################################################
DoubleParabolicTransversalOps:= 
  OperationsRecord("DoubleParabolicTransversalOps", DomainOps);


#############################################################################
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
DoubleParabolicTransversalOps.Print:= function(this)
    Print("DoubleParabolicTransversal( ", this.W, ", ", this.J, ", ", 
          this.K, " )");
end;


#############################################################################
##
##  see Algorithm E (p.51).
##
##  Scheisse: funktioniert nicht!
##
#DoubleParabolicTransversalOps.Elements:= function(this)
#    local   W,  J,  K,  WJ,  WK,  S,  X,  Z,  w,  x,  i;
#
#    W:= this.W;  J:= this.J;  K:= this.K;
#    WJ:= ReflectionSubgroup(W, J);
#    WK:= ReflectionSubgroup(W, K);
#    S:= W.rootInclusion{[1..W.semisimpleRank]};
#    X:= [];
#    Z:= [LongestCoxeterElement(WJ) * LongestCoxeterElement(W)];
#    for w in Z do
#        InfoZigzag1("lookin at ", CoxeterWord(W, w), ":\n");
#        x:= ReducedInCoxeterCoset(WK, w^-1)^-1;
#        InfoZigzag1("reduced to ", CoxeterWord(W, x), ".\n");
#        if not x in X then
#            InfoZigzag1("NEW!!!\n");
#            Add(X, x);
#            for i in LeftDescentSet(W, x^-1) do
#                InfoZigzag1("Adding ", CoxeterWord(W, x * W.(W.rootRestriction[i])), "...\n");
#                Add(Z, x * W.(W.rootRestriction[i]));
#            od;
#        fi;
#    od;
#    
#    return Set(X);
#end;

DoubleParabolicTransversalOps.Elements:= function(this)
    local   left,  itr,  list,  w;
    
    left:= LeftParabolicTransversal(this.W, this.K);
    itr:= Iterator(ParabolicTransversal(this.W, this.J));
    list:= [];
    while itr.hasNext() do
        w:= itr.next();
        if w in left then
            Add(list, w);
        fi;
    od;
    
    return Set(list);
        
#    return Filtered(Elements(ParabolicTransversal(this.W, this.J)),
#                   w-> w in LeftParabolicTransversal(this.W, this.K));
end;


#############################################################################
PDTransversalOps:= 
  OperationsRecord("PDTransversalOps", DomainOps);


#############################################################################
PDTransversal:= function(W, J, K)
    return 
      rec(
          isDomain:= true,
          isPDTransversal:= true,
          operations:= PDTransversalOps,
          W:= W,
          J:= J,
          K:= K
          );
end;


#############################################################################
PDTransversalOps.Print:= function(this)
    Print("PDTransversal( ", this.W, ", ", this.J, ", ", 
          this.K, " )");
end;


#############################################################################
##
##  see Algorithm E (p.51).
##
##  Scheisse: funktioniert nicht!
##
PDTransversalOps.Elements:= function(this)
    local   W,  J,  K,  WJ,  WK,  S,  X,  Z,  w,  x,  i;

    W:= this.W;  J:= this.J;  K:= this.K;
    WJ:= ReflectionSubgroup(W, J);
    WK:= ReflectionSubgroup(W, K);
    S:= W.rootInclusion{[1..W.semisimpleRank]};
    X:= [];
    Z:= [LongestCoxeterElement(WJ) * LongestCoxeterElement(W)];
    for w in Z do
        InfoZigzag1("lookin at ", CoxeterWord(W, w), ":\n");
        x:= ReducedInCoxeterCoset(WK, w^-1)^-1;
        InfoZigzag1("reduced to ", CoxeterWord(W, x), ".\n");
        if not x in X then
            InfoZigzag1("NEW!!!\n");
            Add(X, x);
            for i in Difference(LeftDescentSet(W, w^-1), K) do
                InfoZigzag1("Adding ", CoxeterWord(W, w * W.(W.rootRestriction[i])), "...\n");
                Add(Z, w * W.(W.rootRestriction[i]));
            od;
            for i in LeftDescentSet(W, x^-1) do
                InfoZigzag1("Adding ", CoxeterWord(W, x * W.(W.rootRestriction[i])), "...\n");
                Add(Z, x * W.(W.rootRestriction[i]));
            od;
        fi;
    od;
    
    return Set(X);
end;


#############################################################################
XJKLOps:= OperationsRecord("XJKLOps", DomainOps);

#############################################################################
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
XJKLOps.Print:= function(this)
    Print("XJKL( ", this.W, ", ", this.J, ", ", this.K, ", ", this.L, " )");
end;


#############################################################################
IsXJKL:= function(obj)
    return IsRec(obj) and IsBound(obj.isXJKL) and obj.XJKL = true;
end;


#############################################################################
XJKLOps.Elements:= function(this)
    return 
      Filtered(Elements(DoubleParabolicTransversal(this.W, this.J, this.K)),
              d -> Intersection(
                      List(OnSets(this.J, d), x-> (x-1) mod this.W.parentN + 1),
                      this.K) = this.L);
end;


#############################################################################
##
#E  Emacs  . . . . . . . . . . . . . . . . . . . . . . local emacs variables.
##
##  Local Variables:
##  mode:               gap
##  minor-mode:         outline
##  outline-regexp:     "#F\\|#V\\|#E\\|#A"
##  fill-column:        77
##  End:
##
