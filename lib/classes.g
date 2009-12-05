#############################################################################
##
#A  $Id: classes.g,v 1.1 2009/12/05 17:18:20 goetz Exp $
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2009-2010 Götz Pfeiffer
##
##  This file contains routines for conjugacy classes of Coxeter groups.
##
##  <#GAPDoc Label="Intro:Classes">
##    The conjugacy classes of a finite Coxeter group <M>W</M> are naturally
##    partitioned into cyclic shift classes ...
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
##  gap> W:= CoxeterGroup("E", 6);; 
##  ...
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
#F  Print( <cycsc> ) . . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
CyclicShiftsOps.Print:= function(self)
    Print("CyclicShifts( ", self.W, ", ", self.w, " )");
end;


#############################################################################
##
#F  Representative( <cycsc> )  . . . . . . . . . . . . . . .  representative.
##
##  A cyclic shift class, as a class of elements, has a representative.
##
##  <#GAPDoc Label="Representative(cycsc)">
##  <ManSection>
##  <Meth Name="Representative" Arg="cycsc" Label="for cyclic shift classes"/>
##  <Returns>a representative of the cyclic shift class <A>cycsc</A>.</Returns>
##  <Description>The representative of a shape constructed 
##  as <C>Shape(W, J)</C> (see <Ref Label="Shape"/>) will be its
##  initial element <C>J</C>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> ...
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
#F  Elements( <cycsc> )  . . . . . . . . . . . . . . . . . . . . .  elements.
##  
##  <#GAPDoc Label="Elements(cycsc)">
##  <ManSection>
##  <Meth Name="Elements" Arg="shape" Label="for cyclic shift classes"/>
##  <Returns>
##    the set of elements of the cyclic shift class <A>cycsc</A>.
##  </Returns>
##  <Description>
##  The cyclic shift class of <M>w</M> in <M>W</M> consists of all ...
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> Elements(...);
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  TODO:  make parabolic-safe
##
##  y = s_i x s_i is a cyclic shift of x if either
##  l(s_i x) > l(x) and l(s_i x s_i) < l(s_i x) or
##  l(s_i x) < l(x) and l(s_i x s_i) > l(s_i x) 
##
##
CyclicShiftsOps.Elements:= function(self)
    local   W,  S,  orb,  x,  i,  s,  y,  z;
    
    W:= self.W;
    S:= W.rootInclusion{[1 .. W.semisimpleRank]};
    
    self.isMinimal:= true;
    self.isMaximal:= true;
    self.above:= false;
    self.below:= false;
    
    orb:= [self.w];
    for x in orb do
        for i in S do
            s:= W.(W.rootRestriction[i]);
            y:= s * x;
            z:= y * s;
            #if i^x > N then
            if IsLeftDescent(W, x, i) then
                #if i/y > N then
                if IsRightDescent(W, y, i) then
                    self.isMinimal:= false;
                    self.below:= z;
                else
                    if not z in orb then
                        Add(orb, z);
                    fi;
                fi;
            else
                # if i/y > N then
                if IsRightDescent(W, y, i) then
                    if not z in orb then
                        Add(orb, z);
                    fi;
                else
                    self.isMaximal:= false;
                    self.above:= z;
                fi;
            fi;
        od;
    od;
    return Set(orb);

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
#F  Edges( <shape> ) . . . . . . . . . . . . . . . . . . . . . . . . . edges.
##


#############################################################################
##
#F  Transversal( <shape> ) . . . . . . . . . . . . . . . . . . . transversal.
##


#############################################################################
##
#F  Relation( <shape> ) . . . . . . . . . . . . . . . . . . . . . . relation.
##


#############################################################################
##
#F  Iterator( < class > ) . . . . . . . . . . . . . . . . . . . . iterator.
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
##  <#GAPDoc Label="Iterator(class)">
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
CyclicShiftsOps.Iterator:= function(self)

    local   W,  S,  head,  focus,  back,  itr;

    W:= self.W;
    S:= W.rootInclusion{[1 .. W.semisimpleRank]};

    head:= rec();
    focus:= rec(w:= self.w, next:= head);
    back:= focus; 

    itr:= rec();
    
##    
##  hasNext() simply checks whether 'focus' is looking at an element.
##    
    itr.hasNext:= function()
        return IsBound(focus.w);
    end;
    
##
##  next() simply returns the element 'focus' is looking at.  But before it
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
                    #if i / x > W.parentN then
                    if IsRightDescent(W, x, i) then
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
#F  CentralizerComplement( <W>, <w> )  . . . . . . . . . . . . . centralizer.
##
##  <#GAPDoc Label="NormalizerComplement">
##  <ManSection>
##  <Func Name="NormalizerComplement" Arg="W, J"/>
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
CyclicShiftsOps.Complement:= function(W, w)
    local   J,  WJ,  NJ,  gen,  res,  x,  new,  K,  wK,  can,  car;
    
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
        if Size(Intersection(can, WJ)) = 1 and Size(can) = Size(NJ) then
            return can;
        fi;
    od;
    
    # if everything fails ...
    return false;
end;

CentralizerComplement:= function(W, w)
    local   v,  com,  u;
    
    for v in Elements(CyclicShifts(W, w)) do
        com:= CyclicShiftsOps.Complement(W, v);
        if com <> false then
            u:= RepresentativeOperation(W, v, w);
            return com^u;
        fi;
    od;
    
    return false;
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
