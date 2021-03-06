#############################################################################
##
#A  methods.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
##
##  This file contains support for methods.
##
##  <#GAPDoc Label="Intro:Methods">
##    A <E>method</E> <Index>method</Index> is a &GAP; function that is
##    defined in the operations record of an object and is usually applied to
##    this object (and possibly further arguments).  &GAP; uses dispatchers
##    in the form of global functions to invoke methods.  This chapter
##    describes an alternative way to carry out method calls in &GAP;, with
##    or without further arguments.<P/>
##
##    The functions described in this chapter are implemented in the file
##    <F>methods.g</F>.
##  <#/GAPDoc>
##

#############################################################################
##
##  a global repository of operations records.
##
OPERATIONS:= rec();

Ops:= function(arg)
    local  ops;
    if Length(arg) = 1  then
        ops:= rec();
    else
        ops:= Copy(arg[2]);
    fi;
    ops.name := Concatenation(arg[1], "Ops");
    ops.operations := OpsOps;
    OPERATIONS.(ops.name):= ops;
    return ops;
end;

#############################################################################
##
#F  Object( <type> )
##
##  how to initialize an object of type <type>.
##
Object:= function(type)
    local   object;
    object:= rec();
    object.(Concatenation("is", type)):= true;
    object.operations:= OPERATIONS.(Concatenation(type, "Ops"));
    return object;
end;

#############################################################################
##
#F
##
TypeCheck:= function(type)
    local   comp;
    comp:= Concatenation("is", type);
    return obj-> IsRec(obj) and IsBound(obj.(comp)) and obj.(comp) = true;
end;

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
##  How to apply a method to a list of objects.
##
Map:= function(list, method)
    return List(list, x-> Call(x, method));
end;


#############################################################################
##
#F  Iverson
##
##  not really a method but a useful general concept: maps true/false to 1/0.
##
Iverson:= function(bool)
    if bool then
        return 1;
    else
        return 0;
    fi;
end;


#############################################################################
##
##  For example: a rudimentary Partition class.
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
