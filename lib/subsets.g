#############################################################################
##
#A  subsets.g                    Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2002, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: subsets.g,v 1.2 2002/11/22 18:09:30 goetz Exp $
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
Prefixes:= function(W, w)
    return 
      rec(
          operations:= PrefixesOps,
          isDomain:= true,
          W:= W,
          w:= w
      );
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
                    AddSet(Z, x*W.(W.rootRestriction[i]));
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
                        y:= x*W.(W.rootRestriction[i]);
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
##  More generally, every interval [w1, w2] can be described as a "shifted"
##  prefix set.
##
##  TODO ...
##

#############################################################################
##
##  Coset Representatives.  Aka $X_J$.  Is the prefix set of $w_J w_0$.
##
##??? A ParabolicTransversal "is a" Prefixes set.  So inherit!
##
ParabolicTransversalOps:= 
  OperationsRecord("ParabolicTransversalOps", DomainOps);

#############################################################################
ParabolicTransversal:= function(W, J)
    ##??? need to check the arguments?
    local w;
    w:= LongestCoxeterElement(ReflectionSubgroup(W, J))
        * LongestCoxeterElement(W);
    return 
      rec( operations:= ParabolicTransversalOps,
           isDomain:= true,
           W:= W,
           w:= w,
           J:= J );
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
ParabolicTransversalOps.Elements:= function(this)
    return Elements(Prefixes(this.W, this.w));
end;

#############################################################################
ParabolicTransversalOps.Iterator:= function(this)
    return Iterator(Prefixes(this.W, this.w));
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
DescentClassOps:= OperationsRecord("DescentClassOps", DomainOps);

#############################################################################
DescentClass:= function(W, K)
    ##??? need to check the arguments?
    
    ##??? should store w_K and w_{\bar{K}}
    return 
      rec( operations:= DescentClassOps,
           isDomain:= true,
           W:= W,
           K:= K );
end;

#############################################################################
DescentClassOps.Print:= function(this)
    Print("DescentClass( ", this.W, ", ", this.K, " )");
end;

#############################################################################
DescentClassOps.Elements:= function(this)
   local   W, K, n,  w,  Y;
   
   W:= this.W;  K:= this.K;
   n:= W.semisimpleRank;   
   w:= LongestCoxeterElement(ReflectionSubgroup(W, Difference([1..n], K)));
   Y:= Prefixes(W, w * LongestCoxeterElement(ReflectionSubgroup(W, K)) 
                     * LongestCoxeterElement(W));
   return Set(w * Elements(Y));
end;

#############################################################################
# iterator version
DescentClassOps.Iterator:= function(this)
    local   W, K, n,  w,  itr, ditr;
    
    W:= this.W;  K:= this.K;
    n:= W.semisimpleRank;   
    w:= LongestCoxeterElement(ReflectionSubgroup(W, Difference([1..n], K)));
    itr:= Iterator(Prefixes(W, w*LongestCoxeterElement(ReflectionSubgroup(W, K))
                  * LongestCoxeterElement(W)));
    ditr:= rec();
    ditr.hasNext:= function() return itr.hasNext(); end;
    ditr.next:= function() return w * itr.next(); end;
    
    return ditr;
end;


#############################################################################
##
##  What about left coset reps?  I know they are just the inverses ... but
##  how do they fit into this scheme best?
##

#############################################################################
##
##  Double Coset Reps.
##
##  TODO ...
##


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
