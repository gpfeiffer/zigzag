#############################################################################
##
#A  arrows.g                     Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2006, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: alleys.g,v 1.29 2007/04/27 09:22:19 goetz Exp $
##
##  This file contains support for arrows and arrow classes.
##  
##  <#GAPDoc Label="Intro:Arrows">
##    An <E>arrow</E> <Index>arrow</Index> is a pair <M>(L; s_1, \dots,
##    s_l)</M> consisting of a subset <M>L</M> of <M>S</M> and a list
##    <M>(s_1, \dots, s_l)</M> of pairwise different elements of
##    <M>L</M>.
##  <#/GAPDoc>
##

#############################################################################
##
#F  ProductArrows( <a>, <b> )  . . . . . . . . . . . . . . . . . . . product.
##
##  <#GAPDoc Label="ProductArrows">
##  <ManSection>
##  <Func Name="ProductArrows" Arg="a, b"/>
##  <Returns>
##    the product of the arrows <A>a</A> and <A>b</A>, if the tail of
##    <A>a</A> is the head of <A>b</A>, and <M>0</M> otherwise.
##  </Returns>
##  <Description>
##    The product of arrow <M>a = (L; s, t, \dots)</M> and arrow <M>b = (L';
##    s', t', \dots)</M> is <M>a \circ b = (L; s, t, \dots, s', t', \dots)</M>
##    provided <M>L \setminus \{s, t, \dots\} = L'</M>.
##  <Example>
##  gap> ProductArrows([[1,3,4,5], [4]], [[1,3,5], [1]]);
##  [ [ 1, 3, 4, 5 ], [ 4, 1 ] ]
##  gap> ProductArrows([[1,3,4,5], [4]], [[1,3,4], [1]]);
##  0
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ProductArrows:= function(a, b)
    if Difference(a[1], a[2]) = b[1] then
        return [a[1], Concatenation(a[2], b[2])];
    fi;
    return 0;
end;


#############################################################################
##
#F  ProductArrowList( <list> ) . . . . . . . . . . . . . . . . . . . product.
##
##  <#GAPDoc Label="ProductArrowList">
##  <ManSection>
##  <Func Name="ProductArrowList" Arg="list"/>
##  <Returns>
##    the product of a list <A>list</A> of arrows.
##  </Returns>
##  <Description>
##  <Example>
##  gap> ProductArrowList([[[1, 2, 3, 5], [5]], [[1, 2, 3], [2]], [[1, 3], [3]]]);
##  [ [ 1, 2, 3, 5 ], [ 5, 2, 3 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ProductArrowList:= function(list)
    local   product,  i;
    
    # trivial case: the empty product.
    if list = [] then return [[], []]; fi;
    
    product:= list[1];
    for i in [2..Length(list)] do
        if product = 0 then
            return 0;
        fi;
        product:= ProductArrows(product, list[i]);
    od;
    
    return product;
end;


#############################################################################
##
#F  FactorsArrow( <arrow> ) . . . . . . . . . . . . . . . . . . . .  factors.
##
##  <#GAPDoc Label="FactorsArrow">
##  <ManSection>
##  <Func Name="FactorsArrow" Arg="arrow"/>
##  <Returns>
##    the list of factors of the arrow <A>arrow</A>.
##  </Returns>
##  <Description>
##    Every arrow <M>a</M> of length <M>l(a) > 0</M> has a unique
##    factorization into arrows of length 1.
##  <Example>
##  gap> FactorsArrow([[1, 2, 3, 5], [5, 2, 3]]);
##  [ [ [ 1, 2, 3, 5 ], [ 5 ] ], [ [ 1, 2, 3 ], [ 2 ] ], [ [ 1, 3 ], [ 3 ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
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
##
#F  HeadArrow( <W>, <arrow> )  . . . . . . . . . . . . . . . . . . . .  head.
##
##  returns a reference to the shape of the head of <arrow>.
##
HeadArrow:= function(W, arrow)
    local   sh, head;
    sh:= Shapes(W);
    head:= arrow[1];
    return sh[PositionProperty(sh, x-> head in x)];
end;

#############################################################################
##
#F  TailArrow( <W>, <arrow> )  . . . . . . . . . . . . . . . . . . . .  head.
##
##  returns a reference to the shape of the tail of <arrow>.
##
TailArrow:= function(W, arrow)
    local   sh, tail;
    sh:= Shapes(W);
    tail:= Difference(arrow[1], arrow[2]);
    return sh[PositionProperty(sh, x-> tail in x)];
end;

#############################################################################
##
#F  OnArrows( <arrow>, <d> )  . . . . . . . . . . . . . . . . . .  operation.
##
##  <#GAPDoc Label="OnArrows">
##  <ManSection>
##  <Func Name="OnArrows" Arg="arrow, d"/>
##  <Returns>
##    the image of the arrow <A>arrow</A> under the permutation <A>d</A>.
##  </Returns>
##  <Description>
##    The Coxeter group <M>W</M> acts on its arrows by conjugation.  However,
##    in order to map an arrow <M>(L; s, t, \dots)</M> to another arrow, the
##    element <M>d</M> must be such that it maps <M>L</M> to a subset of
##    <M>S</M>.  This is always the case if <M>d</M> is a longest coset
##    representative of the parabolic subgroup <M>W_L</M> in a parabolic
##    supergroup.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> L:= [1, 2, 3, 5];;
##  gap> d:= LongestCoxeterElement(ReflectionSubgroup(W, L)) *
##  > LongestCoxeterElement(W);
##  ( 1, 3, 5)( 2, 4,30)( 6, 8,28)( 7, 9,29)(10,12,26)(11,25,27)(13,21,23)
##  (14,22,24)(15,17,19)(16,18,20)
##  gap> OnArrows([L, [5, 2]], d);
##  [ [ 1, 3, 4, 5 ], [ 1, 4 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
OnArrows:= function(arrow, d)
    return [OnSets(arrow[1], d), OnTuples(arrow[2], d)];
end;
                   

#############################################################################
##
#F  StabilizerArrow( <W>, <arrow> ) . . . . . . . . . . . . . . . stabilizer.
##
##  <#GAPDoc Label="StabilizerArrow">
##  <ManSection>
##  <Func Name="StabilizerArrow" Arg="W, arrow"/>
##  <Returns>
##    the stabilizer in <A>W</A> of the arrow <A>arrow</A>.
##  </Returns>
##  <Description>
##    The stabilizer of the arrow <A>arrow</A> is a subgroup of the
##    stabilizer of its head.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> L:= [1, 3, 5];;
##  gap> st:= StabilizerArrow(W, [L, []]);;
##  gap> List(Generators(st), x-> RestrictedPerm(x, L));
##  [ (3,5), (1,3) ]
##  gap> st:= StabilizerArrow(W, [L, [3]]);;
##  gap> List(Generators(st), x-> RestrictedPerm(x, L));
##  [ (1,5) ]
##  gap> st:= StabilizerArrow(W, [L, [3,5]]);
##  Subgroup( CoxeterGroup("A", 5), [  ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StabilizerArrow:= function(W, arrow)
    return Stabilizer(NormalizerComplement(W, arrow[1]), arrow[2], OnTuples);
end;


#############################################################################
##
#F  LittleDeltaArrow( <W>, <arrow> ) . . . . . . . . . . . . . .  difference.
##
##  <#GAPDoc Label="LittleDeltaArrow">
##  <ManSection>
##  <Func Name="LittleDeltaArrow" Arg="W, arrow"/>
##  <Returns>
##    <M>\delta(a) = a - b</M> as the pair <M>(a, b)</M>, where <M>a</M> is
##    the arrow <A>arrow</A>.
##  </Returns>
##  <Description>
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> L:= [1, 2, 3, 5];;
##  gap> LittleDeltaArrow(W, [L, [3]]);
##  [ [ [ 1, 2, 5 ], [  ] ], [ [ 2, 3, 5 ], [  ] ] ]
##  gap> LittleDeltaArrow(W, [L, [3,1]]);
##  [ [ [ 1, 2, 5 ], [ 1 ] ], [ [ 2, 3, 5 ], [ 2 ] ] ]
##  gap> LittleDeltaArrow(W, [L, [5]]);
##  [ [ [ 1, 2, 3 ], [  ] ], [ [ 1, 2, 3 ], [  ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
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
##
#F  DeltaArrow( <W>, <arrow> ) . . . . . . . . . . . . . .  difference.
##
##  <#GAPDoc Label="DeltaArrow">
##  <ManSection>
##  <Func Name="DeltaArrow" Arg="W, arrow"/>
##  <Returns>
##    the coefficients of <M>\Delta(a)</M> in terms of the shape of its tail,
##    where <M>a</M> is the arrow <A>arrow</A>.
##  </Returns>
##  <Description>
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> L:= [1, 2, 3, 5];;
##  gap> DeltaArrow(W, [L, [3]]);
##  [ 0, 1, 0, 0, -1, 0 ]
##  gap> DeltaArrow(W, [L, [3,1]]);
##  [ 0, 0, -1, 0, 2, -1 ]
##  gap> DeltaArrow(W, [L, [5]]);
##  [ 0, 0, 0 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
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
##
##  ReversedArrow(W, arrow)
##
##  <#GAPDoc Label="ReversedArrow">
##  <ManSection>
##  <Func Name="ReversedArrow" Arg="W, arrow"/>
##  <Returns>
##    the reversed arrow of <A>arrow</A>.
##  </Returns>
##  <Description>
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> L:= [1, 2, 3, 5];;
##  gap> ReversedArrow(W, [L, [3]]);
##  [ [ 1, 2, 3, 5 ], [ 1 ] ]
##  gap> ReversedArrow(W, [L, [3,1]]);
##  [ [ 1, 2, 3, 5 ], [ 1, 2 ] ]
##  gap> ReversedArrow(W, [L, [5]]);
##  [ [ 1, 2, 3, 5 ], [ 5 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ReversedArrow:= function(W, arrow)

    local   L,  list,  s,  K,  wL,  d,  rev;
    
    L:= arrow[1];
    list:= arrow[2];
    if list = [] then
        Error("arrow must have length > 0");
    fi;
    
    s:= list[1];
    wL:= LongestCoxeterElement(ReflectionSubgroup(W, L));
    K:= Difference(L, [s]);
    d:= LongestCoxeterElement(ReflectionSubgroup(W, K)) * wL;
    rev:= [s^wL - W.N];
    Append(rev, OnTuples(list{[2..Length(list)]}, d));

    return [L, rev];
end;

LittleDeltaBarArrow:= function(W, arrow)
    local   delta;
    
    delta:= LittleDeltaArrow(W, arrow);
    delta[2]:= ReversedArrow(W, delta[2]);
    return delta;
end;

#############################################################################
PrefixArrow:= function(arrow)
    local   list;
    list:= arrow[2];
    if list = [] then
        Error("arrow must have length > 0");
    fi;
    return [arrow[1], list{[1..Length(list)-1]}];
end;


#############################################################################
SuffixArrow:= function(arrow)
    local   list,  s,  K;
    list:= arrow[2];
    if list = [] then
        Error("arrow must have length > 0");
    fi;
    s:= list[1];
    K:= Difference(arrow[1], [s]);
    return [K, list{[2..Length(list)]}];
end;


#############################################################################
##
##  Associate (a reduced expression for) w_{L'} w_L to an arrow (L; ...)
##
ReducedWordArrow:= function(W, arrow)
    local   z,  K,  Kz,  c;
    
    if arrow[2] = [] then
        return CategoryElt(W, arrow);
    fi;
    
    z:= arrow[2]{[Length(arrow[2])]};
    K:= Difference(arrow[1], arrow[2]);
    
    Kz:= Call(CategoryElt(W, [K, z]), "Target");
    c:= ApplyMethod(ReducedWordArrow(W, PrefixArrow(arrow)), "Restricted", Kz);
    Append(z, c.elt[2]);
    
    return CategoryElt(W, [K, z]);
end;


#  Given W, d = w_L w_M and J such that |L - J| = 1
#  write d as a sequence of longest coset reps for J
helper:= function(W, J, d)
    local   seq,  des,  L,  a;
    seq:= [];
    while d <> () do
        des:= LeftDescentSet(W, d);
        if Size(des) <> 1 then Print("...ahemm...\n"); fi;
        Add(seq, des[1]);
        L:= Union(J, des);
        a:= LongestCoxeterElement(ReflectionSubgroup(W, J)) *
            LongestCoxeterElement(ReflectionSubgroup(W, L));
        J:= OnSets(J, a);
        d:= a^-1 * d;
    od;
    return seq;
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
