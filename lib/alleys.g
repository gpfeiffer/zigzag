#############################################################################
##
#A  arrows.g                     Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2006, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: alleys.g,v 1.9 2006/06/16 13:34:31 goetz Exp $
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
LittleDeltaArrow:= function(W, arrow)
    local   L,  list,  K,  d,  lft,  rgt;
    
    L:= arrow[1];
    list:= arrow[2];
    if list = [] then
        Error("arrow must have length > 0");
    else
        K:= Difference(L, list{[1]});
        d:= LongestCoxeterElement(ReflectionSubgroup(W, K))
            * LongestCoxeterElement(ReflectionSubgroup(W, L));
        lft:= [K, list{[2..Length(list)]}];
        rgt:= OnArrows(lft, d);
    fi;
    return [lft, rgt];
end;

#############################################################################
#
#  Deprecate:
#
BigMatrixArrow:= function(W, arrow)
    local   sub,  mat,  sh,  l,  i,  j;
    
    sub:= SubsetsShapes(Shapes(W));
    mat:= NullMat(Length(sub), Length(sub));
    sh:= Shapes(W);
    l:= SetComposition(List(sh, Size));
    i:= Position(sub, arrow[1]);
    j:= PositionProperty(sh, x-> Difference(arrow[1], arrow[2]) in x);
    mat[i]{l[j]}:= DeltaArrow(W, arrow);    
    return mat;
end;



#############################################################################
ProductArrows:= function(a, b)
    if Difference(a[1], a[2]) = b[1] then
        return [a[1], Concatenation(a[2], b[2])];
    fi;
    return 0;
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
StabilizerArrow:= function(W, arrow)
    return Stabilizer(NormalizerComplement(W, arrow[1]), arrow[2], OnTuples);
end;


#############################################################################
ArrowClassOps.Children:= function(this)
    local   stab,  children,  o,  new;
    
    if IsBound(this.stab) then
        stab:= this.stab;
    elif IsBound(this.parent) then
        stab:= this.parent.stab;
        stab:= Stabilizer(stab, this.arrow[2][Length(this.arrow[2])]);
    else
        stab:= StabilizerArrow(this.W, this.arrow);
    fi;
    this.stab:= stab;
    
    children:= [];
    for o in Orbits(stab, ApplyFunc(Difference, this.arrow)) do
        new:= [this.arrow[1], Copy(this.arrow[2])];
        Add(new[2], o[1]);
        Add(children, ArrowClass(W, new));
    od;
    
    for o in children do
        o.parent:= this;
    od;
    
    return children;
end;


BreadthFirst:= function(tree)
    local   list,  next;
    
    list:= [tree];
    for next in list do
        Append(list, Call(next, "Children"));
    od;
    return list;
end;

PreOrder:= function(tree)
   local   list,  c;
    
    list:= [tree];
    for c in Call(tree, "Children") do
        Append(list, PreOrder(c));
    od;
    return list;
end;

PreOrderProperty:= function(tree, property)
    local   list,  c;
    
    list:= [];
    if property(tree) then
        Add(list, tree);
    fi;
    
    for c in Call(tree, "Children") do
        Append(list, PreOrderProperty(c, property));
    od;
    return list;
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

ArrowClasses1:= function(W)
    local   list,  shape;
    list:= [];
    for shape in Shapes(W) do
        Append(list, BreadthFirst(ArrowClass(W, [shape.J, []])));
    od;
    return list;
end;

EssentialArrowClasses:= function(W)
    local   list,  hhh,  sh,  new,  N;
    
    list:= [];
    
    hhh:= function(arrow, N)
        local   L,  o,  s,  new,  Ns,  m,  c;
        
        L:= Difference(arrow[1], arrow[2]);
        for o in Orbits(N, L) do
            s:= o[1];
            new:= [arrow[1], Concatenation(arrow[2], [s])];
            m:= DeltaArrow(W, new);
            if m <> 0*m then
                c:= ArrowClass(W, new);
                m:= Call(c, "Matrix").mat;
                if m <> 0*m then 
                    Add(list, c);
                    Print(".\c");
                fi;
            fi;
            Ns:= Stabilizer(N, s);
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
    i:= PositionProperty(sh, x-> this.arrow[1] in x);
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
    return PositionProperty(Shapes(this.W), 
                   x-> ApplyFunc(Difference, this.arrow) in x);
end;

#############################################################################
ArrowClassOps.Head:= function(this)
    return PositionProperty(Shapes(this.W), x-> this.arrow[1] in x);
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

ArrowClassOps.BigMatrix:= function(this)
    local   sh,  m,  l,  mat;
    
    sh:= Shapes(this.W); 
    m:= Sum(sh, Size);
    l:= SetComposition(List(sh, Size));
    mat:= NullMat(m, m);
    m:= Call(this, "Matrix");
    mat{l[m.head]}{l[m.tail]}:= m.mat;
    return mat;
end;

    

Negative:= function(matrix)
    local   new;
    
    new:= ShallowCopy(matrix);
    new.mat:= -new.mat;
    return new;    
end;

##
##  Arrow classes can be multiplied. 
##
##  how to do this efficiently ?
##
ArrowClassOps.\*:= function(l, r)
    local   W,  res,  all,  a,  b,  c;
    
    res:= [];
    
    #  arrow * arrow class.
    if not IsArrowClass(l) then
        for b in Elements(r) do
            c:= ProductArrows(l, b);
            if c <> 0 then
                Add(res, c);
            fi;
        od;
        return res;
    fi;
    
    # arrow class * arrow
    if not IsArrowClass(r) then
        for a in Elements(l) do
            c:= ProductArrows(a, r);
            if c <> 0 then
                Add(res, c);
            fi;
        od;
        return res;
    fi;
    
    # arrow class * arrow class.
    if l.W <> r.W then
        Error("factors must have same W component");
    fi;
    
    W:= l.W;
    
    # unless they fit together
    if Call(l, "Tail") <> Call(r, "Head") then
        return res;
    fi;
    
    # form all products of all members.
    all:= [];
    for a in Elements(l) do
        for b in Elements(r) do
            c:= ProductArrows(a, b);
            if c <> 0 then
                Add(all, c);
            fi;
        od;
    od;
    
    # Q: can the same nonzero c ever occur twice ?
    # no: because of unique factorization.
    
    a:= Length(all);
    all:= Set(all);
    if a <> Size(all) then
        Error("Panic: problem with unique factorization!");
    fi;
    
    
    # split into classes
    while all <> [] do
        c:= ArrowClass(W, all[1]);
        Add(res, c);
        a:= Length(all);
        all:= Difference(all, Elements(c));
        if a <> Size(all) + Size(c) then
            Error("Panic:  problem with arrow class products!");
        fi;
    od;
    
    return res;
end;

#############################################################################
ArrowClassOps.Length:= function(this)
    return Length(this.arrow[2]);
end;

#############################################################################
##
##  the width of an arrow class alpha is the Size of alpha(L),
##  the number of arrows in the class with the same head L.
##  Thus the size of the class is the size of the shape of its head
##  times its width.  In most cases, the width is 1.
##
##
ArrowClassOps.Width:= function(this)
    return Index(StabilizerArrow(W, [this.arrow[1], []]),
                 StabilizerArrow(W, this.arrow));
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
