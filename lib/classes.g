#############################################################################
##
#A  $Id: classes.g,v 1.4 2009/12/10 09:53:24 goetz Exp $
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
#F  Elements( <shifts> ) . . . . . . . . . . . . . . . . . . . . .  elements.
##  
##  <#GAPDoc Label="Elements(shifts)">
##  <ManSection>
##  <Meth Name="Elements" Arg="shape" Label="for cyclic shifts"/>
##  <Returns>
##    the set of elements of the cyclic shift class <A>shifts</A>.
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
#F  Transversal( <shifts> )  . . . . . . . . . . . . . . . . . . transversal.
##


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
##  hasNext() simply checks whether 'focus' is looking at an element.
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
#F  CentralizerComplement( <W>, <w> )  . . . . . . . . . . . . . centralizer.
##
##  <#GAPDoc Label="CentralizerComplement">
##  <ManSection>
##  <Func Name="CentralizerComplement" Arg="W, J"/>
##  <Returns>
##   <M>X_{JJJ}</M> as a group generated by the eyes and ears of the shape.
##  </Returns>
##  <Description>
##    The centralizer of <M>w</M> in <M>W</M> is ...
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;  W.name:= "W";;
##  ...
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

# minimal length case.
CentralizerComplementMinimal:= function(W, w)
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

# general case ...
# FIXME: need an efficient way to conjugate w in W to an element of minimal length in its class ... based on an iterator?? ...


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
#E  Emacs  . . . . . . . . . . . . . . . . . . . . . . local emacs variables.
##
##  Local Variables:
##  mode:               gap
##  outline-regexp:     "#F\\|#V\\|#E\\|#A"
##  fill-column:        77
##  End:
##
