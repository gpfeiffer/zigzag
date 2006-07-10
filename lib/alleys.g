#############################################################################
##
#A  arrows.g                     Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2006, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: alleys.g,v 1.20 2006/07/10 12:09:11 goetz Exp $
##
##  This file contains support for arrows and arrow classes.
##  
##  <#GAPDoc Label="Intro:Arrows">
##    An <E>arrow</E> <Index>arrow</Index> is a pair consisting of a subset
##    <M>L</M> of <M>S</M> and a list <M>(s_1, ..., s_l)</M> of pairwise
##    different elements of <M>L</M>.
##  <#/GAPDoc>
##

#############################################################################
##
#F  HeadArrow( <W>, <arrow> )  . . . . . . . . . . . . . . . . . . . .  head.
##
##  <#GAPDoc Label="HeadArrow">
##  <ManSection>
##  <Func Name="HeadArrow" Arg="tree"/>
##  <Returns>
##    the shape of the head of the arrow <A>arrow</A>.
##  </Returns>
##  <Description>
##    The <E>head</E> of an arrow <M>a = (L; s, t, ...)</M> is the subset
##    <M>L</M> of <M>S</M>.
##  <Example>
##  gap> HeadArrow(W, [[1, 2, 3, 5], [5, 2]]);
##  Shape( CoxeterGroup("A", 5), [ 1, 2, 3, 5 ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
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

##
##  the product of a list of arrows.
ProductArrowList:= function(list)
    local   product,  i;
    
    # trivial case: the empty product.
    if list = [] then return [[], []]; fi;
    
    product:= list[1];
    for i in [2..Length(list)] do
        product:= ProductArrows(product, list[i]);
    od;
    
    return product;
end;


#############################################################################
##
##  Every arrow of length > 0 has a unique factorization into arrows of
##  length 1.
##
FactorsArrow:= function(a)
    local   factors,  b;
    
    # protect a against accidental corruption.
    a:= Copy(a);
    
    # trivial case first.
    if a[2] = [] then return [a];  fi;
    
    factors:= [];
    while Length(a[2]) > 0 do
        b:= a[2]{[1]};
        Add(factors, [a[1], b]);
        a:= [Difference(a[1], b), a[2]{[2..Length(a[2])]}];
    od;
    
    return factors;
end;

    
#############################################################################
StabilizerArrow:= function(W, arrow)
    return Stabilizer(NormalizerComplement(W, arrow[1]), arrow[2], OnTuples);
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
