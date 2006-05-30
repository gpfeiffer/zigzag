#############################################################################
##
#A  arrows.g                     Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2006, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: alleys.g,v 1.3 2006/05/30 09:57:16 goetz Exp $
##
##  <#GAPDoc Label="Intro:Arrows">
##  This file contains support for arrows and arrow classes.
##  
##  An <E>arrow</E> <Index>arrow</Index> is a pair consisting of a subset L of S and a list (s_1, ..., s_l) of pairwise different elements of L.
##
##  <#/GAPDoc>
##

#############################################################################
HeadArrow:= function(W, arrow)
    local   sh;
    sh:= Shapes(W);
    return sh[PositionProperty(sh, x-> arrow[1] in x)];
end;

#############################################################################
TailArrow:= function(W, arrow)
    local   sh;
    sh:= Shapes(W);
    return sh[PositionProperty(sh, x-> Difference(arrow[1], arrow[2]) in x)];
end;

#############################################################################
OnArrows:= function(arrow, d)
    return [OnSets(arrow[1], d), OnTuples(arrow[2], d)];
end;
                   
#############################################################################
DeltaArrow:= function(W, arrow)
    local   L,  list,  head,  res,  K,  d,  lft,  rgt;
    
    L:= arrow[1];
    list:= arrow[2];
    if list = [] then
        head:= Elements(HeadArrow(W, arrow));
        res:= List(head, x-> 0);
        res[Position(head, L)]:= 1;
    else
        K:= Difference(L, list{[1]});
        d:= LongestCoxeterElement(ReflectionSubgroup(W, K))
            * LongestCoxeterElement(ReflectionSubgroup(W, L));
        lft:= [K, list{[2..Length(list)]}];
        rgt:= OnArrows(lft, d);
        if lft = rgt then # early 0 detection
            res:= List(Elements(TailArrow(W, arrow)), x-> 0);
        else
            res:= DeltaArrow(W, lft) - DeltaArrow(W, rgt);
        fi;
    fi;
    return res;
end;

    
#############################################################################
##
##  Arrow Classes.
##
##  An *arrow class* is an equivalence class of arrows
##  under the conjugation action of W.
##
##  Representatives can be obtained by choosing s as representatives
##  of the orbits of N_L on L, for every shape representative L, ...
##



#############################################################################
##  
#O  ArrowClassOps  . . . . . . . . . . . . . . . . . . . operations record.
##  
ArrowClassOps:= OperationsRecord("ArrowClassOps", DomainOps);

#############################################################################
##  
#C  Shape( <W>, <J> ) . . . . . . . . . . . . . . . . . . . . .  constructor.
#C  Shape( <W>, <WJ> )  . . . . . . . . . . . . . . . . . . . .  constructor.
#C  Shape( <W>, <w> ) . . . . . . . . . . . . . . . . . . . . .  constructor.
##  
##  <#GAPDoc Label="Shape">
##  <ManSection>
##  <Func Name="Shape" Arg="W, J"/>
##  <Returns>
##    a new shape, an object that represents the shape of <A>J</A> in 
##    <A>W</A>. 
##  </Returns>
##  <Description>
##  This is the simple constructor for the shape class.  It constructs and
##  returns the shape of <A>J</A> in <A>W</A>.  Here <A>W</A> is a finite
##  Coxeter group of rank <M>n</M> and <A>J</A> is a subset of
##  <M>[1..n]</M>.
##  <Example>
##  gap> W:= CoxeterGroup("E", 6);; 
##  gap> Shape(W, [1, 2, 3]);
##  Shape( CoxeterGroup("E", 6), [ 1, 2, 3 ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  public fields:
##    W, the Coxeter group.
##    J, the parabolic subset of S.
##  
ArrowClass:= function(W, arrow)
    return 
      rec(
          isDomain:= true,
          isArrowClass:= true,
          operations:= ArrowClassOps,
          W:= W,
          arrow:= arrow
          );
end;


#############################################################################
##
#F  IsShape( <obj> )  . . . . . . . . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsShape">
##  <ManSection>
##  <Func Name="IsShape" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a shape and <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsArrowClass:= function(obj)
    return IsRec(obj) and IsBound(obj.isArrowClass) 
           and obj.isArrowClass = true;
end;


#############################################################################  
##  
#F  Print( <shape> ) . . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
##  
##
ArrowClassOps.Print:= function(this)
    Print("ArrowClass( ", this.W, ", ", this.arrow, " )");
end;


#############################################################################
##
#F  Representative( <shape> ) . . . . . . . . . . . . . . . . representative.
##
##  A shape, as a class of parabolic subsets, has a representative.
##
##  <#GAPDoc Label="Representative(shape)">
##  <ManSection>
##  <Meth Name="Representative" Arg="shape" Label="for shapes"/>
##  <Returns>a representative of the shape <A>shape</A>.</Returns>
##  <Description>The representative of a shape constructed 
##  as <C>Shape(W, J)</C> (see <Ref Label="Shape"/>) will be its
##  initial element <C>J</C>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> Representative(Shape(W, [2]));
##  [ 2 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
ArrowClassOps.Representative:= function(this)
    return this.arrow;
end;

#############################################################################
##
#F  ArrowClasses
##
ArrowClasses:= function(W)
    local   list,  hhh,  sh,  new,  N;
    
    list:= [];
    
    hhh:= function(arrow, N)
        local   L,  o,  s,  new,  Ns;
        
        L:= Difference(arrow[1], arrow[2]);
        for o in Orbits(N, L) do
            s:= o[1];
            new:= [arrow[1], Concatenation(arrow[2], [s])];
            Ns:= Stabilizer(N, s);
            Add(list, ArrowClass(W, new));
            hhh(new, Ns);
        od;
    end;
            
    for sh in Shapes(W) do
        new:= [Representative(sh), []];
        Add(list, ArrowClass(W, new));
        N:= Call(sh, "Complement");
        hhh(new, N);
    od;
    return list;
end;

#############################################################################  
##  
#F  Elements( <shape> ) . . . . . . . . . . . . . . . . . . . . . . elements.
##  
##  <#GAPDoc Label="Elements(shape)">
##  <ManSection>
##  <Meth Name="Elements" Arg="shape" Label="for shapes"/>
##  <Returns>
##    the set of elements of the shape <A>shape</A>.
##  </Returns>
##  <Description>
##  The shape of <M>J</M> in <M>W</M> consists of all subsets of <M>S</M>
##  which are conjugate to <M>J</M> under <M>W</M>.
##  The conjugates can be efficiently computed
##  using <Cite Key="GePf2000" Where="Theorem 2.3.3"/>.
##  This is much faster than simple conjugacy tests.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> Elements(Shape(W, [2]));
##  [ [ 1 ], [ 2 ], [ 3 ] ] 
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ArrowClassOps.Elements:= function(this)
    local   elm,  W,  sh,  i,  j,  L,  list,  o,  x,  J,  t;
    
    elm:= [];
    W:= this.W;
    
    sh:= Shapes(W);  # carefully bring in sync with shape internals ...
    i:= Position(sh, Shape(W, this.arrow[1]));
    j:= Position(Elements(sh[i]), this.arrow[1]);
    L:= sh[i].J;
    list:= OnTuples(this.arrow[2], sh[i].transversal[j]^-1);
    o:= Orbit(Call(sh[i], "Complement"), list, OnTuples);
    for x in sh[i].transversal do
        J:= OnSets(L, x);
        for t in o do
            Add(elm, [J, OnTuples(t, x)]);
        od;
    od;
    return Set(elm);
end;

#############################################################################
ArrowClassOps.Tail:= function(this)
    return Position(Shapes(this.W), 
                   Shape(this.W, ApplyFunc(Difference, this.arrow)));
end;

#############################################################################
ArrowClassOps.Head:= function(this)
    return Position(Shapes(this.W), Shape(this.W, this.arrow[1]));
end;


###
###  next:  the mu map.
###
ArrowClassOps.Matrix:= function(this)
    local   sh,  L,  J,  subL,  mat,  e,  i;

    sh:= Shapes(this.W);
    L:= Call(this, "Head");
    J:= Call(this, "Tail");
    subL:= Elements(sh[L]);
    mat:= NullMat(Size(sh[L]), Size(sh[J]));
    for e in Elements(this) do
        i:= Position(subL, e[1]);
        mat[i]:= mat[i] + DeltaArrow(this.W, e);
    od;
    return rec(tail:= J, head:= L, mat:= mat);
end;

Negative:= function(matrix)
    local   new;
    
    new:= ShallowCopy(matrix);
    new.mat:= -new.mat;
    return new;    
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
