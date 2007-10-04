#############################################################################
##
#A  $Id: iterator.g,v 1.11 2007/10/04 15:31:04 goetz Exp $
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2001-2007, Götz Pfeiffer
##
##  This file contains a dispatcher for iterators on domains.
##  
##  <#GAPDoc Label="Intro:Iterators">
##  An <E>iterator</E> <Index>Iterator</Index>
##  is a record that provides two functions <C>hasNext()</C>
##  and <C>next()</C>  that can be used to loop over the elements of a
##  (finite) domain.
##  
##  <C>hasNext()</C> returns <K>true</K> if there are still elements to
##  be looped over.<Index Key="hasNext"><C>hasNext()</C></Index>
##  
##  <C>next()</C> returns the next element from the domain.
##  <Index Key="next"><C>next()</C></Index>
##
##  Typical usage:
##  <Example>
##  itr:= Iterator(domain);
##  while itr.hasNext() do
##      Print(itr.next(), "\n");
##  od;
##  </Example>
##
##  Iterators are disposable.
##  After the loop, the iterator object 
##  is exhausted and should be discarded.
##
##  <#/GAPDoc>
##

#############################################################################
##  
#F  IteratorSet( <set> ) . . . . . . . . . . . . . . . . . . . . .  iterator.
##
##  <#GAPDoc Label="IteratorSet">
##  <ManSection>
##  <Func Name="IteratorSet" Arg="set"/>
##  <Returns>
##    an iterator for the set <A>set</A>
##  </Returns>
##  <Description>
##  <Example>
##  gap> X:= [2, 3, 5, 7, 11];
##  [ 2, 3, 5, 7, 11 ]
##  gap> itr:= IteratorSet(X);
##  rec(
##    hasNext := function (  ) ... end,
##    next := function (  ) ... end )
##  gap> Print(itr.next());  while itr.hasNext() do Print(", ", itr.next()); od;
##  2, 3, 5, 7, 11gap> Print("\n");  Unbind(itr);
##  
##  </Example>
##    A special iterator for the empty set is provided by <Ref
##    Var="IteratorEmpty"/>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
IteratorSet:= function(set)
    local itr, i;
    
    # initialize.
    i:=0;  itr:= rec();
    
    # the hasNext() function.
    itr.hasNext:= function() 
        return i < Length(set);
    end;
    
    # the next() function.
    itr.next:= function() 
        i:= i + 1;
        return set[i]; 
    end;
    
    return itr;
end;

#############################################################################
##
#V  IteratorEmpty . . . . . . . . . . . . . . . . . . . . . . . . . iterator.
##
##  <#GAPDoc Label="IteratorEmpty">
##  <ManSection>
##  <Var Name="IteratorEmpty" Comm="an iterator for the empty set"/>
##  <Description>
##     The <C>hasNext</C> function of an iterator for the empty set will
##     always return <C>false</C>.  Therefore, this iterator does not even
##     have a <C>next</C> function, since it should never be called anyway.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
IteratorEmpty:= rec(hasNext:= function() return false; end);


#############################################################################
##
#F  Iterator( <domain> ) . . . . . . . . . . . . . . . . . . . . .  iterator. 
##
##  <#GAPDoc Label="Iterator">
##  <ManSection>
##  <Oper Name="Iterator" Arg="domain"/>
##  <Returns>
##    an iterator for the domain <A>domain</A>.
##  </Returns>
##  <Description>
##    An iterator is to be used only once and therefore it must not be
##    remembered.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
Iterator:= function(D)
    local  itr;
    if IsSet(D)  then
        itr:= IteratorSet(D);
    elif IsDomain(D)  then
        # (delete) itr:= D.operations.Iterator(D);
        itr:= Call(D, "Iterator");
    else
        Error( "<D> must be a domain or a set" );
    fi;
    return itr;
end;


#############################################################################
##
#F  DomainOps.Iterator( <domain> ) . . . . . . . . . . . . . . . .  iterator.
##
##  <#GAPDoc Label="Iterator(domain)">
##  <ManSection>
##  <Meth Name="Iterator" Label="for domains" Arg="domain"/>
##  <Returns>an iterator for the domain <A>domain</A>.</Returns>
##  <Description>
##  The default iterator for a domain is the iterator returned by 
##  <Ref Func="IteratorSet"/> for its set of elements.
##  Particular domains can implement their own more space efficient versions.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
DomainOps.Iterator:= function(D)
    return IteratorSet(Elements(D));
end;

#############################################################################
##
#F  IteratorRange( <range> ) . . . . . . . . . . . . . . . . . . .  iterator.
##
IteratorRange:= function(range)
    local   itr,  len,  more,  lo,  hi,  inc,  val;
    
    # check argument.
    if not IsRange(range) then Error("<range> must be a range"); fi;
    
    # initialize.
    itr:= rec();  len:= Length(range);  more:= len > 0;
    if more then
        lo:= range[1];  hi:= range[len]; 
        if len > 1 then inc:= range[2]-lo; else inc:= 0; fi;
    fi;
    
    # the hasNext() function.
    itr.hasNext:= function() return more; end;
    
    # the next() function.
    itr.next:= function() 
        local val;
        more:= lo <> hi;  val:= lo;  lo:= lo + inc;
        return val; 
    end;
    
    return itr;
end;
         

#############################################################################
##
##  An MPartition of n is a partition of n into m parts.
##
MPartitionsOps:= OperationsRecord("MPartitionsOps", DomainOps);

MPartitions:= function(n, m)
    return rec(n:= n, m:= m, isDomain:= true, operations:= MPartitionsOps);
end;

MPartitionsOps.Print:= function(self)
    Print("MPartitions( ", self.n, ", ", self.m, " )");
end;


NrMPartitions:= function(n, m)
    local   sz;
    if m = 0 and n = 0 then
        return 1;
    elif m = 0 or m > n then
        return 0;
    elif n < 2 * m then 
        return NrMPartitions(n - 1, m - 1);
    fi;
    return NrMPartitions(n - 1, m - 1) + NrMPartitions(n - m, m);
end;

MPartitionsOps.Size:= function(self)
    return NrMPartitions(self.n, self.m);
end;


MPartitionsOps.Iterator:= function(self)
    local   inner,  done,  iter;
    
    #  trivial cases m = 0 and m > n.
    if self.m = 0 and self.n = 0 then
        return IteratorSet([Partition([])]);
    elif self.m = 0 or self.m > self.n then
        return IteratorEmpty;
    fi;
    
    done:= false;            # install iterator for first summand.
    inner:= Iterator(MPartitions(self.n - 1, self.m - 1));
    iter:= rec();
    
    iter.hasNext:= function()
        if done then
            return inner.hasNext();
        elif inner.hasNext() then
            return true;
        elif self.n < 2 * self.m then
            return false;
        fi;
        
        done:= true;        # install iterator for second summand.
        inner:= Iterator(MPartitions(self.n - self.m, self.m));
        return inner.hasNext();
    end;
    
    iter.next:= function()
        local   new;
        new:= inner.next().parts;
        if done then
            new:= new + 1;
        else
            Add(new, 1);
        fi;
        return Partition(new);
    end;
    
    return iter;
end;


MPartitionsOps.Elements:= function(self)
    local   elts,  iter;
    
    elts:= [];
    iter:= Iterator(self);
    while iter.hasNext() do
        Add(elts, iter.next());
    od;
    return elts;
end;


#############################################################################
##
##  For example: a rudimentary PartitionsInt class.
##
PartitionsIntOps:= OperationsRecord("PartitionsIntOps", DomainOps);

PartitionsInt:= function(n)
    return rec(n:= n, isDomain:= true, operations:= PartitionsIntOps);
end;

PartitionsIntOps.Print:= function(self)
    Print("PartitionsInt( ", self.n, " )");
end;


PartitionsIntOps.Iterator:= function(self)
    local   m,  inner,  iter;
    
    m:= 0;
    inner:= Iterator(MPartitions(self.n, m));
    iter:= rec();
    
    iter.hasNext:= function()
        while m < self.n do
            if inner.hasNext() then
                return true;
            fi;
            m:= m + 1;
            inner:= Iterator(MPartitions(self.n, m));
        od;
        return inner.hasNext();
    end;
    
    iter.next:= function()
        return Transposed(inner.next());
    end;
    
    return iter;
end;


PartitionsIntOps.Elements:= function(self)
    local   elt,  itr;
    
    elt:= [];
    itr:= Iterator(self);
    while itr.hasNext() do
        Add(elt, itr.next());
    od;
    return elt;
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
