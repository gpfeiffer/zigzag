#############################################################################
##
#A  $Id: alleys.g,v 1.42 2007/10/22 09:10:55 goetz Exp $
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2001-2007, Götz Pfeiffer
##
##  This file contains support for alleys.
##  
##  <#GAPDoc Label="Intro:Alleys">
##    An <E>alley</E> <Index>alley</Index> is a pair <M>(L; s_1, \dots,
##    s_l)</M> consisting of a subset <M>L</M> of <M>S</M> and a list
##    <M>(s_1, \dots, s_l)</M> of pairwise different elements of
##    <M>L</M>. <P/>
##    
##    Alleys are to be treated as immutable objects.<P/>
##
##    The functions described in this chapter are implemented in the file
##    <F>alleys.g</F>.  
##  <#/GAPDoc>
##

#############################################################################
##
#F  ProductAlleys( <a>, <b> )  . . . . . . . . . . . . . . . . . . . product.
##
##  <#GAPDoc Label="ProductAlleys">
##  <ManSection>
##  <Func Name="ProductAlleys" Arg="a, b"/>
##  <Returns>
##    the product of the alleys <A>a</A> and <A>b</A>, if the target of
##    <A>a</A> is the source of <A>b</A>, and <M>0</M> otherwise.
##  </Returns>
##  <Description>
##    The product of alley <M>a = (L; s, t, \dots)</M> and alley <M>b = (L';
##    s', t', \dots)</M> is <M>a \circ b = (L; s, t, \dots, s', t', \dots)</M>
##    provided <M>L \setminus \{s, t, \dots\} = L'</M>.
##  <Example>
##  gap> ProductAlleys([[1,3,4,5], [4]], [[1,3,5], [1]]);
##  [ [ 1, 3, 4, 5 ], [ 4, 1 ] ]
##  gap> ProductAlleys([[1,3,4,5], [4]], [[1,3,4], [1]]);
##  0
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ProductAlleys:= function(a, b)
    if Difference(a[1], a[2]) = b[1] then
        return [a[1], Concatenation(a[2], b[2])];
    fi;
    return 0;
end;


#############################################################################
##
#F  ProductAlleyList( <list> ) . . . . . . . . . . . . . . . . . . . product.
##
##  <#GAPDoc Label="ProductAlleyList">
##  <ManSection>
##  <Func Name="ProductAlleyList" Arg="list"/>
##  <Returns>
##    the product of a list <A>list</A> of alleys.
##  </Returns>
##  <Description>
##  <Example>
##  gap> ProductAlleyList([[[1, 2, 3, 5], [5]], [[1, 2, 3], [2]], [[1, 3], [3]]]);
##  [ [ 1, 2, 3, 5 ], [ 5, 2, 3 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ProductAlleyList:= function(list)
    local   product,  i;
    
    # trivial case: the empty product.
    if list = [] then return 1; fi;
    
    product:= list[1];
    for i in [2..Length(list)] do
        if product = 0 then
            return 0;
        fi;
        product:= ProductAlleys(product, list[i]);
    od;
    
    return product;
end;


#############################################################################
##
#F  FactorsAlley( <alley> ) . . . . . . . . . . . . . . . . . . . .  factors.
##
##  <#GAPDoc Label="FactorsAlley">
##  <ManSection>
##  <Func Name="FactorsAlley" Arg="alley"/>
##  <Returns>
##    the list of factors of the alley <A>alley</A>.
##  </Returns>
##  <Description>
##    Every alley <M>a</M> of length <M>l(a) > 0</M> has a unique
##    factorization into alleys of length 1.
##  <Example>
##  gap> FactorsAlley([[1, 2, 3, 5], [5, 2, 3]]);
##  [ [ [ 1, 2, 3, 5 ], [ 5 ] ], [ [ 1, 2, 3 ], [ 2 ] ], [ [ 1, 3 ], [ 3 ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
FactorsAlley:= function(a)
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
#F  OnAlleys( <alley>, <d> )  . . . . . . . . . . . . . . . . . .  operation.
##
##  <#GAPDoc Label="OnAlleys">
##  <ManSection>
##  <Func Name="OnAlleys" Arg="alley, d"/>
##  <Returns>
##    the image of the alley <A>alley</A> under the permutation <A>d</A>.
##  </Returns>
##  <Description>
##    The Coxeter group <M>W</M> acts on its alleys by conjugation.  However,
##    in order to map an alley <M>(L; s, t, \dots)</M> to another alley, the
##    element <M>d</M> must be such that it maps <M>L</M> to a subset of
##    <M>S</M>.  This is always the case if <M>d</M> is a longest coset
##    representative of the parabolic subgroup <M>W_L</M> in a parabolic
##    supergroup.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> L:= [1, 2, 3, 5];;
##  gap> d:= LongestElement(W, L) * LongestCoxeterElement(W);
##  ( 1, 3, 5)( 2, 4,30)( 6, 8,28)( 7, 9,29)(10,12,26)(11,25,27)(13,21,23)
##  (14,22,24)(15,17,19)(16,18,20)
##  gap> OnAlleys([L, [5, 2]], d);
##  [ [ 1, 3, 4, 5 ], [ 1, 4 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
OnAlleys:= function(alley, d)
    return [OnSets(alley[1], d), OnTuples(alley[2], d)];
end;
                   
#############################################################################
##
#F  StabilizerAlley( <W>, <alley> ) . . . . . . . . . . . . . . . stabilizer.
##
##  <#GAPDoc Label="StabilizerAlley">
##  <ManSection>
##  <Func Name="StabilizerAlley" Arg="W, alley"/>
##  <Returns>
##    the stabilizer in <A>W</A> of the alley <A>alley</A>.
##  </Returns>
##  <Description>
##    The stabilizer of the alley <A>alley</A> is a subgroup of the
##    stabilizer of its source.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> L:= [1, 3, 5];;
##  gap> st:= StabilizerAlley(W, [L, []]);;
##  gap> List(Generators(st), x-> RestrictedPerm(x, L));
##  [ (3,5), (1,3) ]
##  gap> st:= StabilizerAlley(W, [L, [3]]);;
##  gap> List(Generators(st), x-> RestrictedPerm(x, L));
##  [ (1,5) ]
##  gap> st:= StabilizerAlley(W, [L, [3,5]]);
##  Subgroup( CoxeterGroup("A", 5), [  ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StabilizerAlley:= function(W, alley)
    return Stabilizer(NormalizerComplement(W, alley[1]), alley[2], OnTuples);
end;


#############################################################################
##
#F  NrAlleys( <n> ) . . . . . . . . . . . . . . . . . . . . number of alleys.
##
##  <#GAPDoc Label="NrAlleys">
##  <ManSection>
##  <Func Name="NrAlleys" Arg="n"/>
##  <Returns>
##    the number of alleys on a set of size <A>n</A>.
##  </Returns>
##  <Description>
##    The number of alleys on a set of size <M>n</M> is <M>n! \sum_{l=0}^n
##    2^l/l!</M>.
##  <Example>
##  gap> List([0..9], NrAlleys);
##  [ 1, 3, 10, 38, 168, 872, 5296, 37200, 297856, 2681216 ]
##  gap> NrAlleys(55);          
##  93814436634832245005010260707043886255914618433202630120004150861368393728
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  n! \sum_{l=0}^n 2^l/l!
##
NrAlleys:= function(n)
    local   term,  sum,  l;
    term:= Factorial(n);
    sum:= term;
    for l in [1..n] do
        term:= term * 2 / l;
        sum:= sum + term;
    od;
    return sum;
end;


#############################################################################
##
#F  SourceAlley( <alley> )  . . . . . . . . . . . . . . . . . . . . . source.
##
##  <#GAPDoc Label="SourceAlley">
##  <ManSection>
##  <Func Name="SourceAlley" Arg="alley"/>
##  <Returns>
##    the source of the alley <A>alley</A>.
##  </Returns>
##  <Description>
##    The source of an alley <M>a = (L; s, t, \dots)</M> is the set
##    <M>\iota(a) = L \subseteq S</M>.
##  <Example>
##  gap> SourceAlley([[1, 2, 3, 5], [5, 2]]);
##  [ 1, 2, 3, 5 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
SourceAlley:= function(alley)
    return alley[1];
end;

#############################################################################
##
#F  TargetAlley( <alley> )  . . . . . . . . . . . . . . . . . . . . . target.
##
##  <#GAPDoc Label="TargetAlley">
##  <ManSection>
##  <Func Name="TargetAlley" Arg="alley"/>
##  <Returns>
##    the target of the alley <A>alley</A>.
##  </Returns>
##  <Description>
##    The target of an alley <M>a = (L; s, t, \dots)</M> is the set
##    <M>\tau(a) = L \setminus \{s, t, \dots\} \subseteq S</M>.
##  <Example>
##  gap> TargetAlley([[1, 2, 3, 5], [5, 2]]);
##  [ 1, 3 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
TargetAlley:= function(alley)
    return ApplyFunc(Difference, alley);
end;

#############################################################################
##
#F  PrefixAlley( <alley> )  . . . . . . . . . . . . . . . . . . . . . prefix.
##
##  <#GAPDoc Label="PrefixAlley">
##  <ManSection>
##  <Func Name="PrefixAlley" Arg="alley"/>
##  <Returns>
##    the prefix of the alley <A>alley</A>.
##  </Returns>
##  <Description>
##    The <E>prefix</E><Index>prefix</Index> of an alley <M>a = (L; s_1,
##    \dots, s_l)</M> of length <M>\ell(a) = l > 0</M> is the alley <M>\pi(a)
##    = (L; s_1, \dots, s_{l-1})</M> of length <M>l-1</M>.  This function
##    signals an error if the length of <A>alley</A> is <M>0</M>.
##  <Example>
##  gap> PrefixAlley([[1, 2, 3, 5], [5, 2, 3]]);
##  [ [ 1, 2, 3, 5 ], [ 5, 2 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
PrefixAlley:= function(alley)
    if alley[2] = [] then
        Error("alley must have length > 0");
    fi;
    return [alley[1], alley[2]{[1..Length(alley[2])-1]}];
end;

#############################################################################
##
#F  SuffixAlley( <alley> )  . . . . . . . . . . . . . . . . . . . . . suffix.
##
##  <#GAPDoc Label="SuffixAlley">
##  <ManSection>
##  <Func Name="SuffixAlley" Arg="alley"/>
##  <Returns>
##    the suffix of the alley <A>alley</A>.
##  </Returns>
##  <Description>
##    The <E>suffix</E><Index>suffix</Index> of an alley <M>a = (L; s_1,
##    \dots, s_l)</M> of length <M>\ell(a) = l > 0</M> is the alley
##    <M>\sigma(a) = (L; s_2, \dots, s_l)</M> of length <M>l-1</M>.  This
##    function signals an error if the length of <A>alley</A> is <M>0</M>.
##  <Example>
##  gap> SuffixAlley([[1, 2, 3, 5], [5, 2, 3]]);
##  [ [ 1, 2, 3 ], [ 2, 3 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
SuffixAlley:= function(alley)
    if alley[2] = [] then
        Error("alley must have length > 0");
    fi;
    return [Difference(alley[1], alley[2]{[1]}), 
            alley[2]{[2..Length(alley[2])]}];
end;

#############################################################################
##
#F  ActionAlley( <alley> )  . . . . . . . . . . . . . . . . . . . . . action.
##
##  <#GAPDoc Label="ActionAlley">
##  <ManSection>
##  <Func Name="ActionAlley" Arg="alley"/>
##  <Returns>
##    the edge of the action graph corresponding to  the alley <A>alley</A>.
##  </Returns>
##  <Description>
##    An alley <M>a = (L; s_1, \dots, s_l)</M> of length <M>\ell(a) = l >
##    0</M> corresponds to an edge from <M>\sigma(a)</M> to
##    <M>\sigma(a).s</M> labelled by <M>s</M>.  This function returns the
##    pair <M>(\sigma(a), \sigma(a).s</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> ActionAlley(W, [[1, 2, 3, 5], [2, 3]]);
##  [ [ [ 1, 3, 5 ], [ 3 ] ], [ [ 1, 3, 5 ], [ 1 ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ActionAlley:= function(W, alley)
    local   suf;
    suf:= SuffixAlley(alley);
    return [suf, 
     OnAlleys(suf, LongestElement(W, suf[1]) * LongestElement(W, alley[1]))];
end;


#############################################################################
##
#F  LittleDeltaAlley( <W>, <alley> ) . . . . . . . . . . . . . .  difference.
##
##  <#GAPDoc Label="LittleDeltaAlley">
##  <ManSection>
##  <Func Name="LittleDeltaAlley" Arg="W, alley"/>
##  <Returns>
##    <M>\delta(a) = a - b</M> as the pair <M>(a, b)</M>, where <M>a</M> is
##    the alley <A>alley</A>.
##  </Returns>
##  <Description>
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> L:= [1, 2, 3, 5];;
##  gap> LittleDeltaAlley(W, [L, [3]]);
##  [ [ [ 1, 2, 5 ], [  ] ], [ [ 2, 3, 5 ], [  ] ] ]
##  gap> LittleDeltaAlley(W, [L, [3,1]]);
##  [ [ [ 1, 2, 5 ], [ 1 ] ], [ [ 2, 3, 5 ], [ 2 ] ] ]
##  gap> LittleDeltaAlley(W, [L, [5]]);
##  [ [ [ 1, 2, 3 ], [  ] ], [ [ 1, 2, 3 ], [  ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  FIXME: result should be an element of the AlleyAlgebra.
##
LittleDeltaAlley:= function(W, alley)
    local   act;
    act:= ActionAlley(W, alley);
    return act;
end;

#############################################################################
##
#F  DeltaAlley( <W>, <alley> ) . . . . . . . . . . . . . .  difference.
##
##  <#GAPDoc Label="DeltaAlley">
##  <ManSection>
##  <Func Name="DeltaAlley" Arg="W, alley"/>
##  <Returns>
##    the coefficients of <M>\Delta(a)</M> in terms of the shape of its
##    target, where <M>a</M> is the alley <A>alley</A>
##  </Returns>
##  <Description>
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> DeltaAlley(W, [[1, 2, 3, 5], [3]]);
##  [ 0, 1, 0, 0, -1, 0 ]
##  gap> DeltaAlley(W, [[1, 2, 3, 5], [3, 1]]);
##  [ 0, 0, -1, 0, 2, -1 ]
##  gap> DeltaAlley(W, [[1, 2, 3, 5], [5]]);   
##  [ 0, 0, 0 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  FIXME:  result should be an element of the DescentAlgebra.
##  in any case it should have the same format as Delta(street).
##
DeltaAlley:= function(W, alley)
    local   L,  shape,  res,  act;
    
    L:= alley[1];
    if alley[2] = [] then
        shape:= Elements(Shape(W, L));
        res:= List(shape, x-> 0);
        res[Position(shape, L)]:= 1;
    else
        act:= ActionAlley(W, alley);
        if act[1] = act[2] then # early 0 detection
            res:= [1..Size(Shape(W, TargetAlley(alley)))] * 0;
        else
            res:= DeltaAlley(W, act[1]) - DeltaAlley(W, act[2]);
        fi;
    fi;
    return res;
end;


#############################################################################
#
#  Deprecate:
#
BigMatrixAlley:= function(W, alley)
    local   sub,  mat,  sh,  l,  i,  j;
    
    sub:= SubsetsShapes(Shapes(W));
    mat:= NullMat(Length(sub), Length(sub));
    sh:= Shapes(W);
    l:= SetComposition(List(sh, Size));
    i:= Position(sub, alley[1]);
    j:= PositionProperty(sh, x-> Difference(alley[1], alley[2]) in x);
    mat[i]{l[j]}:= DeltaAlley(W, alley);    
    return mat;
end;

#############################################################################
##
##  ReversedAlley(W, alley)
##
##  <#GAPDoc Label="ReversedAlley">
##  <ManSection>
##  <Func Name="ReversedAlley" Arg="W, alley"/>
##  <Returns>
##    the reversed alley of <A>alley</A>.
##  </Returns>
##  <Description>
##    An alley <M>a = (L; s, t, \dots)</M> of length <M>l(a) > 0</M>
##    has a reverse <M>\overline{a} = (L; s^{w_L}, t^d, \dots)</M>,
##    where <M>d = \omega(L_s, s)</M>.  When <M>a</M> is regarded as
##    an edge, then <M>\overline{a}</M> is the reversed edge going in
##    the opposite direction.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> L:= [1, 2, 3, 5];;
##  gap> ReversedAlley(W, [L, [3]]);
##  [ [ 1, 2, 3, 5 ], [ 1 ] ]
##  gap> ReversedAlley(W, [L, [3,1]]);
##  [ [ 1, 2, 3, 5 ], [ 1, 2 ] ]
##  gap> ReversedAlley(W, [L, [5]]);
##  [ [ 1, 2, 3, 5 ], [ 5 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ReversedAlley:= function(W, alley)

    local   L,  list,  s,  K,  wL,  d,  rev;
    
    L:= alley[1];
    list:= alley[2];
    if list = [] then
        Error("alley must have length > 0");
    fi;
    
    s:= list[1];
    wL:= LongestElement(W, L);
    K:= Difference(L, [s]);
    d:= LongestElement(W, K) * wL;
    rev:= [s^wL - W.N];
    Append(rev, OnTuples(list{[2..Length(list)]}, d));

    return [L, rev];
end;

#############################################################################
LittleDeltaBarAlley:= function(W, alley)
    local   delta;
    
    delta:= LittleDeltaAlley(W, alley);
    delta[2]:= ReversedAlley(W, delta[2]);
    return delta;
end;


#############################################################################
##
##  Associate (a reduced expression for) w_J w_L to an alley (L; ...)
##
ReducedWordAlley:= function(W, alley)
    local   z,  K,  Kz,  c;
    
    if alley[2] = [] then
        return CategoryElt(W, alley);
    fi;
    
    z:= alley[2]{[Length(alley[2])]};
    K:= Difference(alley[1], alley[2]);
    
    Kz:= Call(CategoryElt(W, [K, z]), "Target");
    c:= ApplyMethod(ReducedWordAlley(W, PrefixAlley(alley)), "Restricted", Kz);
    Append(z, c.elt[2]);
    
    return CategoryElt(W, [K, z]);
end;

#############################################################################
##
##  The alley algebra.
##


#############################################################################
AlleyAlgebraOps:= OperationsRecord("AlleyAlgebraOps", AlgebraOps);

#############################################################################
AlleyAlgebra:= function(W)
    local   self;
    
    self:= rec();
    self.isAlleyAlgebra:= true;
    self.W:= W;
    self.operations:= AlleyAlgebraOps;
    return self;
end;

#############################################################################
IsAlleyAlgebra:= function(obj)
    return IsRec(obj) and IsBound(obj.isAlleyAlgebra)
           and obj.isAlleyAlgebra = true;
end;

#############################################################################
##  
#F  Print( <aa> )  
##  
AlleyAlgebraOps.Print:= function(self)
    if IsBound(self.name) then
        Print(self.name);
    else
        Print("AlleyAlgebra( ", self.W, " )");
    fi;
end;


#############################################################################
##
##  n! \sum_{l=0}^n 2^l/l!
##
AlleyAlgebraOps.Dimension:= function(self)
    return NrAlleys(self.W.semisimpleRank);
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
