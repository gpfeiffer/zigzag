#############################################################################
##
#A  category.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
##
##  This file contains support for the category of shapes and its elements.
##
##  <#GAPDoc Label="Intro:Category">
##    The pairs <M>(J, x)</M> form a category with partial
##    multiplication ...
##  <#/GAPDoc>
##
##  FIXME??? better name than Category
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
##  <#GAPDoc Label="Category">
##  <ManSection>
##  <Func Name="Category" Arg="W"/>
##  <Returns>
##    a new category, an object that represents the category of <A>W</A>.
##  </Returns>
##  <Description>
##  This is the simple constructor for categories.  It constructs and
##  returns the category of <A>W</A>.  Here <A>W</A> is a finite
##  Coxeter group of rank.
##  <Example>
##  gap> W:= CoxeterGroup("E", 6);;
##  gap> Category(W);
##  Category( CoxeterGroup("E", 6) )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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
##  <#GAPDoc Label="CategoryElt">
##  <ManSection>
##  <Func Name="CategoryElt" Arg="W, elt"/>
##  <Returns>
##    a new category element.
##  </Returns>
##  <Description>
##  This is the simple constructor for category elements.  It constructs and
##  returns the category element <A>elt</A> of <A>W</A>.  Here <A>W</A> is
##  a finite Coxeter, and <A>elt</A> is the pair <M>(J, x)</M>, where
##  <M>J</M> is a subset of <M>S</M> and <M>x \in X_J</M> is such that
##  <M>J^x</M> is a subset of <M>S</M>, too.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> J:= [1, 2];;
##  gap> CategoryElt(W, [J, [1, 2, 3]]);
##  CategoryElt( CoxeterGroup("A", 3), [ [ 1, 2 ], [ 1, 2, 3 ] ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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
##
#F  GroupoidElt( <celt> )
##
##  find a reduced expression and turn into groupoid element.
##
##  <#GAPDoc Label="GroupoidElt(celt)">
##  <ManSection>
##  <Meth Name="GroupoidElt" Arg="celt" Label="for category elements"/>
##  <Returns>
##  a groupoid element corresponding to the category element <A>celt</A>.
##  </Returns>
##  <Description>
##  Each category element is a product of longest coset representatives.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> J:= [1, 2];;
##  gap> CategoryElt(W, [J, [3, 2, 1]]);
##  CategoryElt( CoxeterGroup("A", 3), [ [ 1, 2 ], [ 3, 2, 1 ] ] )
##  gap> Call(last, "GroupoidElt");
##  GroupoidElt( CoxeterGroup("A", 3), [ [ 1, 2 ], () ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
CategoryEltOps.GroupoidElt:= function(self)
    local   w,  d,  J,  s,  L,  a;

    w:= self.W.identity;
    d:= function(J, L)
        return LongestElement(self.W, J) * LongestElement(self.W, L);
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
