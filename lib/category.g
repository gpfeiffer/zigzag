#############################################################################
##
#A  category.g                    Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2007, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: category.g,v 1.1 2007/03/29 14:03:46 goetz Exp $
##
##  This file contains support for the category of shapes and its elements.
##  
##  <#GAPDoc Label="Intro:Category">
##    The pairs <M>(J, x)</M> form a category with partial
##    multiplication ...
##  <#/GAPDoc>
##
##  ??? better name than Category
##


#############################################################################
##  
#O  CategoryOps  . . . . . . . . . . . . . . . . . . . . . operations record.
## 
CategoryOps:= OperationsRecord("CategoryOps", DomainOps);

#############################################################################
##  
#C  Category( <W> ) . . . . . . . . . . . . . . . . . . . . . .  constructor.
##  
Category:= function(W)
    return 
      rec(
          isDomain:= true,
          isCategory:= true,
          operations:= CategoryOps,
          W:= W
          );
end;


#############################################################################
##
#F  IsCategory( <obj> ) . . . . . . . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsCategory">
##  <ManSection>
##  <Func Name="IsCategory" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a shape and <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsCategory:= function(obj)
    return IsRec(obj) and IsBound(obj.isCategory) and obj.isCategory = true;
end;


#############################################################################  
##  
#F  Print( <category> )  . . . . . . . . . . . . . . . . . . . . . . . print.
##  
CategoryOps.Print:= function(this)
    Print("Category( ", this.W, " )");
end;


#############################################################################
##  
#O  CategoryEltOps . . . . . . . . . . . . . . . . . . . . operations record.
## 
CategoryEltOps:= OperationsRecord("CategoryEltOps");


#############################################################################
##  
#C  CategoryElt( <W>, <elt> ) . . . . . . . . . . . . . . . . .  constructor.
##  
CategoryElt:= function(W, elt)
    return 
      rec(
          isDomain:= true,
          isCategoryElt:= true,
          operations:= CategoryEltOps,
          W:= W,
          elt:= elt
          );
end;


#############################################################################
##
#F  IsCategoryElt( <obj> )  . . . . . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsCategoryElt">
##  <ManSection>
##  <Func Name="IsCategoryElt" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a category element and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsCategoryElt:= function(obj)
    return IsRec(obj) and IsBound(obj.isCategoryElt) 
           and obj.isCategoryElt = true;
end;


#############################################################################  
##  
#F  Print( <categoryelt> ) . . . . . . . . . . . . . . . . . . . . . . print.
##  
CategoryEltOps.Print:= function(this)
    Print("CategoryElt( ", this.W, ", ", this.elt, " )");
end;

#############################################################################
CategoryEltOps.Source:= function(this)
    return this.elt[1];
end;

#############################################################################
CategoryEltOps.Target:= function(this)
    return Call(Call(this, "GroupoidElt"), "Target");    
end;

#############################################################################
CategoryEltOps.GroupoidElt:= function(this)
    local   w,  d,  J,  s,  L,  a;
    
    w:= this.W.identity;
    d:= function(J, L)
        return LongestCoxeterElement(ReflectionSubgroup(this.W, J))
               * LongestCoxeterElement(ReflectionSubgroup(this.W, L));
    end;
    J:= this.elt[1];
    for s in this.elt[2] do
        L:= Union(J, [s]);
        a:= d(J, L);
        w:= w * a;
        J:= OnSets(J, a);
    od;
    
    return GroupoidElt(this.W, [this.elt[1], w]);
end;    
        

#############################################################################
CategoryEltOps.\*:= function(l, r)
    local   wl,  wr;
    #FIXME: check arguments
    
    wl:= l.elt[2];
    wr:= r.elt[2];
    if OnSets(l.elt[1], wl) = r.elt[1] then
        return CategoryElt(l.W, [l.elt[1], Concatenation(wl, wr)]);
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
