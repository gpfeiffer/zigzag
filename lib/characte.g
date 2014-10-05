#############################################################################
##
#A  characte.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2011-2013  Götz Pfeiffer
##
##  This file contains routines for characters of finite Coxeter groups.
##
##  <#GAPDoc Label="Intro:Characters">
##    Characters ...<P/>
##
##    This chapter describes functions which compute certain named
##    characters of a finite group <M>G</M> 
##    (see <Ref Func="TrivialCharacter"/> and <Ref Func="RegularCharacter"/>)
##    or, more specially of a finite Coxeter group <M>W</M> 
##    (see <Ref Func="SignCharacter"/> and <Ref Func="AlphaCharacter"/>).
##    Moreover, there is a function to compute all linear characters
##    of a finite group; see <Ref Func="LinearCharacters"/>.
##    And there are various lists of characters of some importance
##    for a finite Coxeter group; see <Ref Func="ECharacters"/>.
##
##    The functions described in this chapter are implemented in the file
##    <F>characte.g</F>.  
##  <#/GAPDoc>
##

#############################################################################
##
#F  RegularCharacter( <grp> ) . . . . . . . . . . . . . .  regular character.
##
##  the regular character (|G|, 0, ..., 0) of G
##
##  <#GAPDoc Label="RegularCharacter">
##  <ManSection>
##  <Func Name="RegularCharacter" Arg="grp"/>
##  <Returns>
##    the regular character of the group <A>grp</A>.
##  </Returns>
##  <Description>
##  The <E>regular character</E> is the character of the 
##  <E>regular representation</E><Index>regular representation</Index> of
##  a group acting on itself by right multiplication.
##  <Example>
##  gap> RegularCharacter(CoxeterGroup("A", 5));
##  Character( CoxeterGroup("A", 5), [ 720, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0 ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
RegularCharacter:= function(grp)
    local   val;
    val:= List(ConjugacyClasses(grp), c-> 0);
    val[1]:= Size(grp);
    return Character(grp, val);
end;


#############################################################################
##
#F  TrivialCharacter( <grp> ) . . . . . . . . . . . . . .  trivial character.
##  
##  the trivial character (1, 1, ..., 1) of G
##
##  <#GAPDoc Label="TrivialCharacter">
##  <ManSection>
##  <Func Name="TrivialCharacter" Arg="grp"/>
##  <Returns>
##    the trivial character of the group <A>grp</A>.
##  </Returns>
##  <Description>
##  The <E>trivial character</E> is the character of the 
##  <E>trivial representation</E><Index>trivial representation</Index> of
##  a group acting trivially on a single point.
##  <Example>
##  gap> RegularCharacter(CoxeterGroup("A", 5));
##  Character( CoxeterGroup("A", 5), [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
TrivialCharacter:= function(grp)
    return Character(grp, List(ConjugacyClasses(grp), c-> 1));
end;


#############################################################################
##
#F  SignCharacter( <W> )  . . . . . . . . . . . . . . . . . . sign character.
##
##  the sign character w \mapsto (-1)^{\ell(w)} of W
##
##  <#GAPDoc Label="SignCharacter">
##  <ManSection>
##  <Func Name="SignCharacter" Arg="W"/>
##  <Returns>
##    the sign character of the Coxeter group <A>W</A>.
##  </Returns>
##  <Description>
##  The <E>sign character</E> is the character of the 
##  <E>sign representation</E><Index>sign representation</Index> of
##  a Coxeter group given by <M>w \mapsto (-1)^{\ell(w)}</M> for
##  <M>w \in W</M>.
##  <Example>
##  gap> SignCharacter(CoxeterGroup("A", 5));
##  Character( CoxeterGroup("A", 5), [ 1, -1, 1, -1, 1, -1, 1, -1, 1, 1, -1 ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
SignCharacter:= function(W)
    return Character(W, List(ConjugacyClasses(W), 
                   c-> (-1)^CoxeterLength(W, Representative(c))));
end;


#############################################################################
##
##  MultiplicitiesCharacter
##
##  compute the multiplicities of each irreducible character in chi.
##
MultiplicitiesCharacter:= function(chi)
    return List(Irr(chi.source), x-> ScalarProduct(x, chi));
end;


##  Computing Linear Characters.

#############################################################################
##
#F  GeneratorsAbelianGroup( <grp> )  . . . . . . . . . . . . . .  generators.
##
##  how to find a set of independent generators of an abelian group
##
GeneratorsAbelianGroup:= function(grp)
    local   all,  gens,  sub,  i,  a;

    all:= Elements(grp);
    gens:= [];
    sub:= TrivialSubgroup(grp);
    for i in Reversed(AbelianInvariants(grp)) do
        a:= First(all, x-> Order(grp, x) = i  and
                  Size(Intersection(Subgroup(grp, [x]), sub)) = 1);
        Add(gens, a);
        sub:= Closure(sub, a);
        all:= Difference(all, sub);
    od;

    return gens;
end;


#############################################################################
##
#F  LinearCharactersAbelianGroup( <A> )  . . . . . . . . . linear characters. 
##
##  how to compute all linear characters of an abelian group.
##  This implementation uses Algorithm H to first list the elements
##  of the group, and later compute the values of a particular character on
##  each element, and it uses Algorithm M to generate all linear characters,
##  by prescribing images of the generators in all possible ways.
##
LinearCharactersAbelianGroup:= function(A)
    local   gens,  ords,  n,  elts,  fus,  lin,  fun;
    
    #  trivial case first.
    if Size(A) = 1 then
        return [Character(A, [1])];
    fi;

    # find a nice generating set for A
    gens:= GeneratorsAbelianGroup(A);
    ords:= List(gens, x-> Order(A, x));  # = abelian invariants.
    n:= Length(gens);
    
    # force elements to be listed in a particular way?
    elts:= ProductsMixedTuplesH(gens, ords);
    fus:= List(ConjugacyClasses(A), c-> Position(elts, Representative(c)));
    
    # generate linear characters
    lin:= [];
    fun:= function(l)
        Add(lin, ProductsMixedTuplesH(l, ords));
    end;
    VisitMixedTuplesM(List(ords, i-> List([0..i-1], j-> E(i)^j)), fun);
    
    return List(lin, x-> Character(A, x{fus}));
end;


#############################################################################
##
#F  LinearCharacters( <G> ) . . . . . . . . . . . . .  characters of degree 1
##
##  compute the linear characters of G as those of the abelian quotient
##  G/G' and then lift back to G.
##
##  <#GAPDoc Label="LinearCharacters">
##  <ManSection>
##  <Func Name="LinearCharacters" Arg="G"/>
##  <Returns>
##    the list of linear characters of the group <A>G</A>.
##  </Returns>
##  <Description>
##    A character of a finite group <M>G</M> is called <E>linear</E> 
##    if it has degree 1, that
##    is, if it is a representation of <M>G</M>.
##    The linear characters of <M>G</M> form a group 
##    under multiplication, which is isomorphic to the commutator
##    quotient, the largest abelian quotient of <M>G</M>.
##  <Example>
##  gap> g:= Group((1,5,2,6)(3,8,4,7), (1,3,2,4)(5,7,6,8));;
##  gap> g.name:= "Q8";;
##  gap> lin:= LinearCharacters(g);
##  [ Character( Q8, [ 1, 1, 1, 1, 1 ] ), Character( Q8, [ 1, 1, 1, -1, -1 ] ), 
##    Character( Q8, [ 1, 1, -1, 1, -1 ] ), Character( Q8, [ 1, 1, -1, -1, 1 ] ) ]
##  </Example>
##    These characters can be displayed as follows.
##  <Example>
##  gap> Display(CharTable(g), rec(chars:= List(lin, x-> x.values), 
##  >            letter:= "L", powermap:= false, centralizers:= false));
##  Q8
##  
##         1a 2a 4a 4b 4c
##  
##  L.1     1  1  1  1  1
##  L.2     1  1  1 -1 -1
##  L.3     1  1 -1  1 -1
##  L.4     1  1 -1 -1  1
##  
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
LinearCharacters:= function(G)
    
    # maybe we know them  already.
    if IsBound(G.charTable) then
        return Filtered(Irr(G), x-> Degree(x) = 1);
    fi;
        
    # compute them as characters of G/G' and inflate.
    return Inflated(LinearCharactersAbelianGroup(CommutatorFactorGroup(G)), G);
end;

##  Other special characters.


#############################################################################
##
#F  ECharacters( <W> )  . . . . . . . . . . . . . . . . . . . . . characters.
##
##  <#GAPDoc Label="ECharacters">
##  <ManSection>
##  <Func Name="ECharacters" Arg="W"/>
##  <Returns>
##    the list of characters corresponding to the primitive idempotents of
##    the descent algebra of <A>W</A>.
##  </Returns>
##  <Description>
##    Each idempotent <M>e</M> in the group algebra <M>KW</M> of a finite
##    Coxeter <M>W</M> generates a submodule <M>eKW</M> of the regular
##    module <M>KW</M>.  This function computes the characters of the
##    modules generated in this way by the primitive idempotents of the
##    descent algebra of <M>W</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> ech:= ECharacters(W);
##  [ [ 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1 ], 
##    [ 15, 5, -1, -3, 3, -1, 0, 1, -1, 0, 0 ], 
##    [ 45, -3, 1, 9, 0, 0, 0, -1, -1, 0, 0 ], 
##    [ 40, 8, 0, 0, 1, -1, -2, 0, 0, 0, 0 ], 
##    [ 15, -3, 3, -7, 0, 0, 3, -1, 1, 0, -1 ], 
##    [ 120, -8, 0, 0, -3, 1, 0, 0, 0, 0, 0 ], 
##    [ 90, 6, -2, -6, 0, 0, 0, 0, 0, 0, 0 ], 
##    [ 40, 0, 0, 8, -2, 0, 1, 0, 0, 0, -1 ], 
##    [ 90, -6, -2, 6, 0, 0, 0, 0, 0, 0, 0 ], 
##    [ 144, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0 ], 
##    [ 120, 0, 0, -8, 0, 0, -3, 0, 0, 0, 1 ] ]
##  </Example>
##    These characters can be displayed in the form of a character table
##    as follows.
##  <Example>
##  gap> ct:= CharTable(W);;  Unbind(ct.irredinfo);
##  gap> Display(ct, rec(chars:= ech, letter:= "E", powermap:= false,
##  >            centralizers:= false));
##  W( A5 )
##  
##          111111 21111 2211 222 3111 321 33 411 42 51  6
##  
##  E.1          1     1    1   1    1   1  1   1  1  1  1
##  E.2         15     5   -1  -3    3  -1  .   1 -1  .  .
##  E.3         45    -3    1   9    .   .  .  -1 -1  .  .
##  E.4         40     8    .   .    1  -1 -2   .  .  .  .
##  E.5         15    -3    3  -7    .   .  3  -1  1  . -1
##  E.6        120    -8    .   .   -3   1  .   .  .  .  .
##  E.7         90     6   -2  -6    .   .  .   .  .  .  .
##  E.8         40     .    .   8   -2   .  1   .  .  . -1
##  E.9         90    -6   -2   6    .   .  .   .  .  .  .
##  E.10       144     .    .   .    .   .  .   .  . -1  .
##  E.11       120     .    .  -8    .   . -3   .  .  .  1
##  
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
##  this table can be computed as product of the following matrices:
##    sha:= [Iverson(lambda contains J)]_{lambda in Lambda, J \subseteq S}
##    nu:= mu^-1
##    inc:= IncidenceMatShapes(Shapes(W))
##    sdc:= SizesDescentConjugacyClasses(W)
##    dia:= DiagonalMat(List(ConjugacyClasses(W), x-> Size(W)/Size(x)))
##
ECharacters:= function(W)
    local   mat,  dia;
    
    mat:= Call(DescentAlgebra(W), "Mu")^-1;
    mat:= List(SetComposition(List(Shapes(W), Size)), x-> Sum(mat{x}));
    mat:= mat * IncidenceMatShapes(Shapes(W)) * SizesDescentConjugacyClasses(W);
    dia:= List(ConjugacyClasses(W), x-> Size(W)/Size(x));
    return List(mat, x-> List([1..Length(x)], i-> x[i] * dia[i]));    
end;

#############################################################################
##
#F  AlphaCharacter( <W>, <J> )  . . . . . . . . . . . . . .  alpha character.
##
##  <#GAPDoc Label="AlphaCharacter">
##  <ManSection>
##  <Func Name="AlphaCharacter" Arg="W, J"/>
##  <Returns>
##    the character <M>\alpha_J</M> of the normalizer <M>N_W(W_J)</M>.
##  </Returns>
##  <Description>
##    The character <M>\alpha_J \colon N_W(W_J) \to \C</M> is defined 
##    (in <Cite Key="HowLeh1982"/>) as
##    the determinant on the orthogonal complement of the <M>V_J</M>
##    spanned by the simple roots corresponding to the reflections in
##    the subset <M>J</M> of <M>S</M>.  Obviously, this character has
##    the parabolic subgroup <M>W_J</M> in its kernel.  And
##    according to Lemma 2.1 in <Cite Key ="DoPfRo2012"/>,
##    it equals
##    sign times the determinant of the permutation induced on <M>J</M>
##    on the normalizer complement (see <Ref Func="NormalizerComplement"/>).
##  <Example>
##  gap> AlphaCharacter(CoxeterGroup("A", 3), [1]);
##  Character( Subgroup( CoxeterGroup("A", 3), 
##  [ ( 1, 7)( 2, 4)( 5, 6)( 8,10)(11,12), 
##    ( 2, 5)( 3, 9)( 4, 6)( 8,11)(10,12) ] ), [ 1, -1, 1, -1 ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
AlphaCharacter:= function(W, J)
    local   nor,  vals,  w;
    
    nor:= NormalizerParabolic(W, J);
    vals:= [];
    for w in List(ConjugacyClasses(nor), Representative) do
        w:= ParabolicCoordinates(W, J, w)[2];
        Add(vals, (-1)^CoxeterLength(W, w) * SignPerm(Sortex(OnTuples(J, w))));
    od;
        
    return Character(nor, vals);
end;

#############################################################################
##
#F  LambdaCharacter( <lambda>, <cval>, <xval> )
#F  ACharacter( <lambda> )
##
LambdaCharacter:= function(lambda, cval, xval)
    local   u,  n,  W,  ct,  t,  s,  i,  ttt,  sss,  o,  old,  w,  
            gens,  vals,  l,  cycle,  cen,  lin,  phi;
    
    n:= Sum(lambda);
    W:= CoxeterGroup("A", n-1);
    ct:= CharTable(W);
    
    # name the generators of W
    s:= [];
    for i in [1..n-1] do
        s[i]:= W.(i); 
    od;
    
    # the product s_a ... s_b
    sss:= function(a, b)
        if b < a then
            return ();
        fi;
        return Product(s{[a..b]});
    end;

    o:= 0;  # offset
    old:= 0;  # previous part considered
    
    w:= ();  # to make w_{lambda}
    gens:= [];  vals:= [];
     
    # loop over the parts
    for l in lambda do
        cycle:= sss(o+1, o+l-1);
        w:= w * cycle;
        if  l = old then   # add a swapper
            Add(gens, sss(o-l+1, o+l-1)^l);
            Add(vals, xval(l)); 
        else               # add the cycle and an r
            Add(gens, cycle);
            Add(vals, cval(l)); 
        fi;
        old:= l;  o:= o+l;  # update offset and old
    od;
    
    cen:= Subgroup(W, gens);
    lin:= LinearCharacters(cen);
    phi:= First(lin, chi-> OnTuples(gens, chi) = vals);
    phi.element:= w;
    
    return phi;
end;

ACharacter:= function(lambda)
    local   ell,  one;
    ell:= l-> E(l);
    one:= l-> 1;
    return LambdaCharacter(lambda, ell, one);
end;


#############################################################################
##
#F  Lambda2Character( <lambda>, <cval>, <dval>, <xval>, <yval>, <rval> )
##
##
##  the ?val arguments are 5 functions, to compute the character values
##  of a c, d, x, y, r element respectively, from the current part l.
##
Lambda2Character:= function(lambda, cval, dval, xval, yval, rval)
    local   u,  n,  W,  ct,  t,  s,  i,  ttt,  sss,  o,  old,  w,  
            gens,  vals,  l,  cycle,  cen,  lin,  phi;
    
    # rare case
    u:= 0;
    if not IsList(lambda[2]) then
        if lambda[2] = '-' then u:= 1; fi;
        lambda[2]:= [];
    fi;
    
    n:= Sum(lambda, Sum);
    W:= CoxeterGroup("B", n);
    ct:= CharTable(W);
    
    # name the generators of W(B_n)
    t:= W.1;
    s:= [];
    for i in [2..n] do
        s[i-1]:= W.(i); 
    od;
    
    # conjugating element
    u:= t^u;
    
    # the product t_a ... t_b
    ttt:= function(a, b)
        if b < a then
            return t^0;
        fi;
        return Product([a..b], i-> t^sss(1, i-1));
    end;
     
    # the product s_a ... s_b
    sss:= function(a, b)
        if b < a then
            return t^0;
        fi;
        return Product(s{[a..b]});
    end;

    o:= 0;  # offset
    old:= 0;  # previous part considered
    
    w:= ();  # to make w_{lambda}
    gens:= [];  vals:= [];
     
    # loop over the negative parts in reverse
    for l in Reversed(lambda[2]) do
        cycle:= t^sss(1, o) * sss(o+1, o+l-1);
        w:= w * cycle;
        if  l = old then   # add a swapper
            Add(gens, sss(o-l+1, o+l-1)^l);
            Add(vals, xval(l)); 
        else               # add the cycle
            Add(gens, cycle);
            Add(vals, cval(l)); 
        fi;
        old:= l;  o:= o+l;  # update offset and old
    od;
    
    old:= 0;
    
    # loop over the positive parts
    for l in lambda[1] do
        cycle:= sss(o+1, o+l-1);
        w:= w * cycle;
        if  l = old then   # add a swapper
            Add(gens, sss(o-l+1, o+l-1)^l);
            Add(vals, yval(l)); 
        else               # add the cycle and an r
            Add(gens, cycle);
            Add(vals, dval(l)); 
            Add(gens, ttt(o+1, o+l));
            Add(vals, rval(l));
        fi;
        old:= l;  o:= o+l;  # update offset and old
    od;
    
    # conjugate if necessary.
    gens:= OnTuples(gens, u);
    w:= w^u;
    
    cen:= Subgroup(W, gens);
    lin:= LinearCharacters(cen);
    phi:= First(lin, chi-> OnTuples(gens, chi) = vals);
    phi.element:= w;
    
    return phi;
end;

BCharacter:= function(lambda)
    local   tpp,  ell,  two,  one,  alt;
    tpp:= function(l)
        while l mod 2 = 0 do
            l:= l/2;
        od;
        return -E(l);  # = E(2*l) as l is odd here.
    end;
    ell:= l-> E(l);
    two:= l-> -1; 
    one:= l-> 1;
    alt:= l-> (-1)^(l-1);
    return Lambda2Character(lambda, tpp, ell, two, one, alt);
end;

DCharacter:= function(lambda)
    local   tel,  ell,  two,  one;
    tel:= l-> E(2*l);
    ell:= l-> E(l);
    two:= l-> -1;
    one:= l-> 1;
    return Lambda2Character(lambda, tel, ell, two, one, two);
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
