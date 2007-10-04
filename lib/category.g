#############################################################################
##
#A  $Id: category.g,v 1.5 2007/10/04 09:36:48 goetz Exp $
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2007, Götz Pfeiffer
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
CategoryOps.Print:= function(self)
    Print("Category( ", self.W, " )");
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
CategoryEltOps.Print:= function(self)
    Print("CategoryElt( ", self.W, ", ", self.elt, " )");
end;

#############################################################################
CategoryEltOps.Source:= function(self)
    return self.elt[1];
end;

#############################################################################
CategoryEltOps.Target:= function(self)
    return Call(Call(self, "GroupoidElt"), "Target");    
end;

#############################################################################
CategoryEltOps.GroupoidElt:= function(self)
    local   w,  d,  J,  s,  L,  a;
    
    w:= self.W.identity;
    d:= function(J, L)
        return LongestCoxeterElement(ReflectionSubgroup(self.W, J))
               * LongestCoxeterElement(ReflectionSubgroup(self.W, L));
    end;
    J:= self.elt[1];
    for s in self.elt[2] do
        L:= Union(J, [s]);
        a:= d(J, L);
        w:= w * a;
        J:= OnSets(J, a);
    od;
    
    return GroupoidElt(self.W, [self.elt[1], w]);
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
##  restrict (L; s, t, ...) to J \subset L
##
CategoryEltOps.Restricted:= function(self, J)
    local   L,  seq,  K,  s,  c,  d;
    L:= self.elt[1];
    if not IsSubset(L, J) then
        Error("<J> must be a subset");
    fi;
    
    seq:= [];  K:= J;
    for s in self.elt[2] do
        c:= CategoryElt(W, [L, [s]]);
        c:= Call(c, "GroupoidElt");
        d:= c.elt[2];
        c:= GroupoidElt(W, [K, d]);
        K:= OnSets(K, d);  L:= OnSets(L, d);
        c:= Call(c, "CategoryElt");
        Append(seq, c.elt[2]);
    od;
    
    return CategoryElt(W, [J, seq]);
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
