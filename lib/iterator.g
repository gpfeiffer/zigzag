#############################################################################
##
#A  iterator.g                    Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2002, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: iterator.g,v 1.1 2002/11/22 13:29:12 goetz Exp $
##
##  This file contains a dispatcher for iterators on domains.
##  
##  An iterator is a record that provides two functions 'hasNext()'
##  and 'next()'  that can be used to loop over the elements of a
##  (finite) domain.
##  
##  'hasNext()' returns 'true' if there are still elements to be looped over.
##  
##  'next()' returns the next element from the domain.
##
##  After the loop, the iterator object is garbage and shoul be discarded.
##
##  Typical usage:
##  
##  itr:= Iterator(domain);
##  while itr.hasNext() do
##      Print(itr.next(), "\n");
##  od;
##
##

#############################################################################
##  
##  An iterator for sets:
##
IteratorSet:= function(set)
    local itr;
    itr:= rec(set:= set, i:= 0);
    itr.hasNext:= function() 
        return itr.i < Length(itr.set);
    end;
    itr.next:= function() 
        itr.i:= itr.i + 1;
        return itr.set[itr.i]; 
    end;
    return itr;
end;

#############################################################################
##
#F  Iterator( <domain> )
##
##  returns an iterator for the domain.  
##  
##  An iterator is to be used only once and therefore it must not be
##  remembered.
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
##  The default iterator for domain is the iterator over its set of elements.
##  Particular domains can implement their own more space efficient versions.
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
