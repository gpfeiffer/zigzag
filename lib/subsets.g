#############################################################################
##
#A  subsets.g                    Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2002, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: subsets.g,v 1.3 2002/11/25 12:33:28 goetz Exp $
##
##  This file contains structures and functions for certain subsets of a 
##  finite Coxeter group.
##  
RequirePackage("chevie");

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
PrefixesOps:= OperationsRecord("PrefixesOps", DomainOps);

#############################################################################
##
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
IsPrefixes:= function(obj)
    return IsRec(obj) and IsBound(obj.isPrefixes) and obj.isPrefixes = true;
end;


#############################################################################
PrefixesOps.Print:= function(this)
    Print("Prefixes( ", this.W, ", ", this.w, " )");
end;


#############################################################################
##
## the prefixes of a given element w.
##
##  WARNING: Elements should return a set!
##
PrefixesOps.Elements:= function(this)
    local W, X, Y, Z, S, i, x;

    W:= this.W;
    S:= W.rootInclusion{[1..W.semisimpleRank]};
    Y:= [this.w];  X:= [];
    while Y <> [] do
        Append(X, Y);
        Z:= [];
        for x in Y do
            for i in S do
                if i / x > W.parentN then
                    AddSet(Z, x * W.(W.rootRestriction[i]));
                fi;
            od;
        od;
        Y:= Z;
    od;

    return Set(X);
end;

#############################################################################
##
# the iterator version of a set of prefixes:
# it consists of a linked list of elements to be processed,
# pointers to the back (next element to be expanded),
# the middle (where the next length starts)
# the focus (next element to be returned) and the front
# where the next prefix is to be put in the queue.
#
# initially:
#
#  foc
#   v
#   w -> .
#   ^    ^
#   b    f
##
PrefixesOps.Iterator:= function(this)

    local   W,  S,  head,  focus,  back,  itr;

    W:= this.W;
    S:= W.rootInclusion{[1..W.semisimpleRank]};

    head:= rec();
    focus:= rec(w:= this.w, next:= head);
    back:= focus; 

    itr:= rec();

    itr.hasNext:= function()
        return IsBound(focus.w);
    end;

    itr.next:= function()
        local   w,  x,  i,  Z, y;
        w:=  focus.w;
        focus:= focus.next;   
        if not IsBound(focus.w) then
            Z:= [];

            # expand back.w to focus.w
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
##  More generally, every (weak) interval [w1, w2] can be described as a 
##  "shifted"
##  prefix set.
##
##  TODO ...
##


#############################################################################
WeakIntervalOps:= OperationsRecord("WeakIntervalOps", DomainOps);


#############################################################################
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
IsWeakInterval:= function(obj)
    return IsRec(obj) and IsBound(obj.isWeakInterval) 
           and obj.isWeakInterval = true;
end;


#############################################################################
WeakIntervalOps.Print:= function(this)
    Print("WeakInterval( ", this.W, ", ", this.bot, ", ", this.top, " )");
end;


#############################################################################
##
##  the interval [bot, top] is isomorphic to the interval [1, bot^-1 * top].
##
WeakIntervalOps.Elements:= function(this)
    return Set(this.bot * Elements(this.pre));
end;


#############################################################################
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
WeakIntervalOps.Size:= function(this)
    return Size(this.pre);
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
    local this, w;
    w:= LongestCoxeterElement(ReflectionSubgroup(W, J))
        * LongestCoxeterElement(W);
    this:= Prefixes(W, w);
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
##???  Is there a more efficient method for the size of Y_K?  
##  something that uses the moebius inversion?
##

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
##  list all of them in shapes order.
##
##??? remember them in W?
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
##
##  Double Coset Reps.
##
##  TODO ...
##

#############################################################################
ParabolicDoubleTransversalOps:= 
  OperationsRecord("ParabolicDoubleTransversalOps", DomainOps);


#############################################################################
ParabolicDoubleTransversal:= function(W, J, K)
    return 
      rec(
          isDomain:= true,
          isParabolicDoubleTransversal:= true,
          operations:= ParabolicDoubleTransversalOps,
          W:= W,
          J:= J,
          K:= K
          );
end;


#############################################################################
ParabolicDoubleTransversalOps.Print:= function(this)
    Print("ParabolicDoubleTransversal( ", this.W, ", ", this.J, ", ", 
          this.K, " )");
end;


#############################################################################
##
##  see Algorithm E (p.51).
##
##  Scheisse: funktioniert nicht!
##
ParabolicDoubleTransversalOps.Elements:= function(this)
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
            for i in LeftDescentSet(W, x^-1) do
                InfoZigzag1("Adding ", CoxeterWord(W, x * W.(W.rootRestriction[i])), "...\n");
                Add(Z, x * W.(W.rootRestriction[i]));
            od;
        fi;
    od;
    
    return Set(X);
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
