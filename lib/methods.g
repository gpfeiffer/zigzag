#############################################################################
##
#A  methods.g                     Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2006, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: methods.g,v 1.1 2006/05/29 11:52:04 goetz Exp $
##
##  <#GAPDoc Label="Intro:Methods">
##  This file contains support for methods.
##  
##  A <E>method</E> <Index>Method</Index> is a GAP function that is
##  defined in the operations record of an object and is usually
##  applied to this object (and possibly further arguments).
##
##  Typical usage:
##  <Example>
##  ShapeOps.Matrix:= function(this)
##  ...
##  end;
##  sh:= Shape(W, [1]);
##  m:= Dot(sh, Matrix);
##  </Example>
##
##  <#/GAPDoc>
##

#############################################################################
##  
#F  Call( ... )
##
##  method must return a value!
##
Call:= function(object, method)
    return object.operations.(method)(object);
end;

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
#E  Emacs  . . . . . . . . . . . . . . . . . . . . . . local emacs variables.
##
##  Local Variables:
##  mode:               gap
##  minor-mode:         outline
##  outline-regexp:     "#F\\|#V\\|#E\\|#A"
##  fill-column:        77
##  End:
##
