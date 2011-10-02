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
