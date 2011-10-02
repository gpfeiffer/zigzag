#############################################################################
##
#A  characte.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2011  Götz Pfeiffer
##
##  This file contains routines for characters of finite Coxeter groups.
##
##  <#GAPDoc Label="Intro:Characters">
##    Characters ...<P/>
##
##    The functions described in this chapter are implemented in the file
##    <F>characte.g</F>.  
##  <#/GAPDoc>
##

#############################################################################
##
##  RegularCharacter
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
##  TrivialCharacter
##  
##  the trivial character (1, 1, .... 1) of G
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
##  SignCharacter
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


##  Computing Linear Characters.

#############################################################################
##
##  GeneratorsAbelianGroup
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
##  LinearCharactersAbelianGroup
##
##  how to compute all linear characters of an abelian group.
##  This implementation uses ProductsAlgorithmH to first list the elements
##  of the group, and later compute the values of a particular character on
##  each element, and it uses AlgorithmM to generate all linear characters,
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
    elts:= ProductsAlgorithmH(gens, ords);
    fus:= List(ConjugacyClasses(A), c-> Position(elts, Representative(c)));
    
    # generate linear characters
    lin:= [];
    fun:= function(l)
        Add(lin, ProductsAlgorithmH(l, ords));
    end;
    AlgorithmM(List(ords, i-> List([0..i-1], j-> E(i)^j)), fun);
    
    return List(lin, x-> Character(A, x{fus}));
end;


#############################################################################
##
#F  LinearCharacters( <G> ) . . . . . . . . . . . . .  characters of degree 1
##
##  compute the linear characters of G as those of the abelian quotient
##  G/G' and then lift back to G.
##
LinearCharacters:= function(G)
    
    # maybe we know them  already.
    if IsBound(G.charTable) then
        return Filtered(Irr(G), x-> Degree(x) = 1);
    fi;
        
    # compute them as characters of G/G' and inflate.
    return Inflated(LinearCharactersAbelianGroup(CommutatorFactorGroup(G)), G);
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
