#############################################################################
##
#A  groupoid.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
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
##  <#GAPDoc Label="Groupoid">
##  <ManSection>
##  <Func Name="Groupoid" Arg="W"/>
##  <Returns>
##    a new groupoid, an object that represents the groupoid of <A>W</A>. 
##  </Returns>
##  <Description>
##  This is the simple constructor for groupoids.  It constructs and
##  returns the groupoid of <A>W</A>.  Here <A>W</A> is a finite
##  Coxeter group of rank.
##  <Example>
##  gap> W:= CoxeterGroup("E", 6);; 
##  gap> Groupoid(W);
##  Groupoid( CoxeterGroup("E", 6) )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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
##    <K>true</K> if <A>obj</A> is a groupoid and <K>false</K> otherwise.
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
GroupoidOps.Print:= function(self)
    Print("Groupoid( ", self.W, " )");
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
##  <#GAPDoc Label="GroupoidElt">
##  <ManSection>
##  <Func Name="GroupoidElt" Arg="W, elt"/>
##  <Returns>
##    a new groupoid element.
##  </Returns>
##  <Description>
##  This is the simple constructor for groupoid elements.  It constructs and
##  returns the groupoid element <A>elt</A> of <A>W</A>.  Here <A>W</A> is 
##  a finite Coxeter, and <A>elt</A> is the pair <M>(J, x)</M>, where 
##  <M>J</M> is a subset of <M>S</M> and <M>x \in X_J</M> is such that
##  <M>J^x</M> is a subset of <M>S</M>, too.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> J:= [1, 2];;
##  gap> GroupoidElt(W, [J, LongestElement(W, J) * LongestElement(W, [1..3])]);
##  GroupoidElt( CoxeterGroup("A", 3), 
##  [ [ 1, 2 ], ( 1, 2, 3,12)( 4, 5,10,11)( 6, 7, 8, 9) ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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
GroupoidEltOps.Print:= function(self)
    Print("GroupoidElt( ", self.W, ", ", self.elt, " )");
end;

#############################################################################
GroupoidEltOps.Source:= function(self)
    return self.elt[1];
end;

#############################################################################
GroupoidEltOps.Target:= function(self)
    return ApplyFunc(OnSets, self.elt);
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
#F  CategoryElt( <gelt> )
##
##  find a reduced expression and turn into category element.
##
##  <#GAPDoc Label="CategoryElt(gelt)">
##  <ManSection>
##  <Meth Name="CategoryElt" Arg="gelt" Label="for groupoid elements"/>
##  <Returns>
##  a category element corresponding to the groupoid element <A>gelt</A>.
##  </Returns>
##  <Description>
##  Each groupoid element is a product of longest coset representatives.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> J:= [1, 2];;
##  gap> GroupoidElt(W, [J, LongestElement(W, J) * LongestElement(W, [1..3])]);
##  GroupoidElt( CoxeterGroup("A", 3), 
##  [ [ 1, 2 ], ( 1, 2, 3,12)( 4, 5,10,11)( 6, 7, 8, 9) ] )
##  gap> Call(last, "CategoryElt");
##  CategoryElt( CoxeterGroup("A", 3), [ [ 1, 2 ], [ 3 ] ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
GroupoidEltOps.CategoryElt:= function(self)
    local   seq,  W,  J,  d,  des,  L,  a;
    
    seq:= [];
    W:= self.W;
    J:= self.elt[1];
    d:= self.elt[2];
    while d <> () do
        #FIXME: SmallestLeftDescent would suffice here.
        des:= LeftDescentSet(W, d);
        Add(seq, des[1]);
        L:= Union(J, des{[1]});
        a:= LongestElement(W, J) * LongestElement(W, L);
        J:= OnSets(J, a);
        d:= a^-1 * d;
    od;
    return CategoryElt(W, [self.elt[1], seq]);
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
