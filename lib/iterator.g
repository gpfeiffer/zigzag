#############################################################################
##
#A  iterator.g                    Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2002, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: iterator.g,v 1.3 2002/12/03 18:01:27 goetz Exp $
##
##  <#GAPDoc Label="Intro:Iterators">
##  This file contains a dispatcher for iterators on domains.
##  
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
##  that was used is garbage and should be discarded.
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
        itr:= D.operations.Iterator(D);
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
##  The default iterator for domain is the iterator over its set of elements.
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
#E  Emacs  . . . . . . . . . . . . . . . . . . . . . . local emacs variables.
##
##  Local Variables:
##  mode:               gap
##  minor-mode:         outline
##  outline-regexp:     "#F\\|#V\\|#E\\|#A"
##  fill-column:        77
##  End:
##
