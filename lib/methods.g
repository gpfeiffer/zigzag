#############################################################################
##
#A  methods.g                     Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2006, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: methods.g,v 1.7 2007/10/04 09:27:44 goetz Exp $
##
##  This file contains support for methods.
##  
##  <#GAPDoc Label="Intro:Methods">
##  A <E>method</E> <Index>method</Index> is a \GAP\ function that is
##  defined in the operations record of an object and is usually
##  applied to this object (and possibly further arguments).
##
##  The functions described here are in the file <F>methods.g</F>.
##  <#/GAPDoc>
##

#############################################################################
##
#F  Call( <object>, <method> ) . . . . . . . . . . . . . . . . . method call. 
##
##  <#GAPDoc Label="Call">
##  <ManSection>
##  <Func Name="Call" Arg="object, method"/>
##  <Returns>
##    the result of <A>object.operations.(method)(object)</A>.
##  </Returns>
##  <Description>
##    This function calls the method <A>method</A> on behalf of the
##    object <A>object</A>.  Only methods that return a value can be used.
##  <Example>
##  gap> Call(Partition([4, 3, 3, 1]), "Length");
##  4
##  </Example>
##    In other object oriented programming languages the construct
##    <C>Call(p, "Length")</C> might more succinctly be expressed as
##    <C>p.Length()</C>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
Call:= function(object, method)
    return object.operations.(method)(object);
end;

#############################################################################
##
#F  ApplyMethod( <object>, <method>, <arg1>, ... ) . . . . . . . method call. 
##
##  <#GAPDoc Label="ApplyMethod">
##  <ManSection>
##  <Func Name="ApplyMethod" Arg="object, method, arg1, arg2, ..."/>
##  <Returns>
##    the result of <A>object.operations.(method)(object, arg1,
##    arg2, ...)</A>.
##  </Returns>
##  <Description>
##    This function calls the method <A>method</A> on behalf of the
##    object <A>object</A> with further arguments <A>arg1, arg2, ...</A>.  Only
##    methods that return a value can be used.
##  <Example>
##  gap> ApplyMethod(Partition([4, 3, 3, 1]), "At", 2);
##  3
##  </Example>
##    In other object oriented programming languages the construct
##    <C>ApplyMethod(p, "At", 2)</C> might more succinctly be
##    expressed as <C>p.At(2)</C>, or even, if the square brackets can
##    be overloaded, as <C>p[2]</C>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ApplyMethod:= function(arg)
    local   object,  method,  list;
    
    object:= arg[1];
    method:= object.operations.(arg[2]);
    if Length(arg) = 2 then
        return method(object);
    fi;
    list:= [object];
    Append(list, arg{[3..Length(arg)]});
    return ApplyFunc(method, list);
end;


#############################################################################
##
##  For example: a rudimentary partitions class.
##
PartitionOps:= rec();

Partition:= function(parts)
    return rec(parts:= parts, operations:= PartitionOps);
end;

PartitionOps.Print:= function(self)
    Print("Partition( ", self.parts, " )");
end;

PartitionOps.Length:= function(self)
    return Length(self.parts);
end;

PartitionOps.At:= function(self, i)
    return self.parts[i];
end;

PartitionOps.Transposed:= function(self)
    local   tran,  p;
    
    if self.parts = [] then return Partition([]); fi;
    tran:= 0 * [1..self.parts[1]];
    for p in self.parts do
        tran{[1..p]}:= tran{[1..p]} + 1;
    od;
    return Partition(tran);
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
