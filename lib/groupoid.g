#############################################################################
##
#A  groupoid.g                    Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2007, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: groupoid.g,v 1.1 2007/03/29 14:03:36 goetz Exp $
##
##  This file contains support for the groupoid of shapes and its elements.
##  
##  <#GAPDoc Label="Intro:Groupoid">
##    The pairs <M>(J, x)</M> form a groupoid with partial
##    multiplication ...
##  <#/GAPDoc>
##
##  ??? better name than Groupoid
##


#############################################################################
##  
#O  GroupoidOps  . . . . . . . . . . . . . . . . . . . . . operations record.
## 
GroupoidOps:= OperationsRecord("GroupoidOps", DomainOps);

#############################################################################
##  
#C  Groupoid( <W> ) . . . . . . . . . . . . . . . . . . . . . .  constructor.
##  
Groupoid:= function(W)
    return 
      rec(
          isDomain:= true,
          isGroupoid:= true,
          operations:= GroupoidOps,
          W:= W
          );
end;


#############################################################################
##
#F  IsGroupoid( <obj> ) . . . . . . . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsGroupoid">
##  <ManSection>
##  <Func Name="IsGroupoid" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a shape and <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsGroupoid:= function(obj)
    return IsRec(obj) and IsBound(obj.isGroupoid) and obj.isGroupoid = true;
end;


#############################################################################  
##  
#F  Print( <groupoid> )  . . . . . . . . . . . . . . . . . . . . . . . print.
##  
GroupoidOps.Print:= function(this)
    Print("Groupoid( ", this.W, " )");
end;


#############################################################################
##  
#O  GroupoidEltOps . . . . . . . . . . . . . . . . . . . . operations record.
## 
GroupoidEltOps:= OperationsRecord("GroupoidEltOps");


#############################################################################
##  
#C  GroupoidElt( <W>, <elt> ) . . . . . . . . . . . . . . . . .  constructor.
##  
GroupoidElt:= function(W, elt)
    return 
      rec(
          isDomain:= true,
          isGroupoidElt:= true,
          operations:= GroupoidEltOps,
          W:= W,
          elt:= elt
          );
end;


#############################################################################
##
#F  IsGroupoidElt( <obj> )  . . . . . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsGroupoidElt">
##  <ManSection>
##  <Func Name="IsGroupoidElt" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a groupoid element and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsGroupoidElt:= function(obj)
    return IsRec(obj) and IsBound(obj.isGroupoidElt) 
           and obj.isGroupoidElt = true;
end;


#############################################################################  
##  
#F  Print( <groupoidelt> ) . . . . . . . . . . . . . . . . . . . . . . print.
##  
GroupoidEltOps.Print:= function(this)
    Print("GroupoidElt( ", this.W, ", ", this.elt, " )");
end;

#############################################################################
GroupoidEltOps.Source:= function(this)
    return this.elt[1];
end;

#############################################################################
GroupoidEltOps.Target:= function(this)
    return ApplyFunc(OnSets, this.elt);
end;

#############################################################################
GroupoidEltOps.\*:= function(l, r)
    local   wl,  wr;
    #FIXME: check arguments
    
    wl:= l.elt[2];
    wr:= r.elt[2];
    if OnSets(l.elt[1], wl) = r.elt[1] then
        return GroupoidElt(l.W, [l.elt[1], wl * wr]);
    else
        return false;
    fi;
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
