#############################################################################
##
#A  $Id: faces.g,v 1.1 2007/11/13 09:45:23 goetz Exp $
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2007 Götz Pfeiffer
##
##  This file contains the routines for faces of hyperplane
##  arrangements of finite Coxeter groups
##
##  <#GAPDoc Label="Intro:Faces">
##    Let <M>(W, S)</M> be a finite Coxeter system.  The <E>face</E>
##    <Index>face</Index> ... <P/>
##      
##    The functions described in this chapter are implemented in the file
##    <F>faces.g</F>.  
##  <#/GAPDoc>
##

#############################################################################
##  
#O  FaceOps . . . . . . . . . . . . . . . . . . . . . . . operations record.
##  
FaceOps:= OperationsRecord("FaceOps", DomainOps);


#############################################################################
##  
#C  Face( <W>, <J> ) . . . . . . . . . . . . . . . . . . . . .  constructor.
##  
##  <#GAPDoc Label="Face">
##  <ManSection>
##  <Func Name="Face" Arg="W, J"/>
##  <Returns>
##    a new face, an object that represents the face of <A>J</A> and
##    <A>x</A> in <A>W</A>.
##  </Returns>
##  <Description>
##    This is the simple constructor for the face class.  It
##    constructs and returns the face <M>W_J x</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);; 
##  gap> Face(W, [1, 2], PermCoxeterWord(W, [3, 2]));
##  Face( CoxeterGroup("A", 3), [ 1, 2 ], ( 1, 4, 6)( 2, 3,11)( 5, 8, 9)
##  ( 7,10,12) )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  public fields:
##    W, the Coxeter group.
##    J, the parabolic subset of S.
##    x, a coset rep of W_J
##  
Face:= function(W, J, x)
    return 
      rec(
          isDomain:= true,
          isFace:= true,
          operations:= FaceOps,
          W:= W,
          J:= J,
          x:= x
          );
end;


#############################################################################
##
#F  IsFace( <obj> ) . . . . . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsFace">
##  <ManSection>
##  <Func Name="IsFace" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a face and <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsFace:= function(obj)
    return IsRec(obj) and IsBound(obj.isFace) and obj.isFace = true;
end;


#############################################################################  
##  
#F  Print( <face> ) . . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
FaceOps.Print:= function(self)
    Print("Face( ", self.W, ", ", self.J, ", ", self.x, " )");
end;

#############################################################################
##
##  FIXME: use iterator, or avoid complete listing at all.
##
Faces:= function(W)
    local   faces,  J,  x;
    faces:= [];
    for J in SubsetsShapes(Shapes(W)) do
        for x in Elements(ParabolicTransversal(W, J)) do
            Add(faces, Face(W, J, x));
        od;
    od;
    return faces;
end;


#############################################################################
##
##  the sign of a face W_Jx is the sign sequence of x, with 0 on all
##  the reflections in W_J^x.
##
FaceOps.Sign:= function(self)
    local   sign,  i,  r;
    
    sign:= "";
    for i in [1..self.W.N] do
        if i/self.x > self.W.N then
            sign[i]:= '-';
        else
            sign[i]:= '+';
        fi;
    od;
    r:= ReflectionSubgroup(self.W, OnSets(self.J, self.x));
    for i in r.rootInclusion{[1..r.N]} do
        sign[i]:= '0';
    od;
    return String(sign);
end;

#############################################################################
ProductLSigns:= function(l, r)
    local   pro,  i;
    
    # check arguments
    if Length(l) <> Length(r) then
        Error("<l> and <r> must be string of the same length");
    fi;
    
    # calculate product gravitating towards l.
    pro:= "";
    for i in [1..Length(l)] do
        if l[i] = '0' then
            pro[i]:= r[i];
        else
            pro[i]:= l[i];
        fi;
    od;
    return String(pro);
end;

ProductRSigns:= function(l, r)
    local   pro,  i;
    
    # check arguments
    if Length(l) <> Length(r) then
        Error("<l> and <r> must be string of the same length");
    fi;
    
    # calculate product gravitating towards r.
    pro:= "";
    for i in [1..Length(l)] do
        if r[i] = '0' then
            pro[i]:= l[i];
        else
            pro[i]:= r[i];
        fi;
    od;
    return String(pro);
end;


#############################################################################
FaceOps.\*:= function(l, r)
    local   W,  J,  K,  x,  y,  dv,  d,  v;
    
    # check arguments
    if l.W < r.W then
        Error("<l> and <r> must be faces of the same Coxeter group");
    fi;
    W:= l.W;
    J:= l.J;  K:= r.J;
    x:= l.x;  y:= r.x;
    
    # write x/y as udv
    dv:= ReducedInCoxeterCoset(ReflectionSubgroup(W, J), x/y);
    d:= ReducedInCoxeterCoset(ReflectionSubgroup(W, K), dv^-1)^-1;
    v:= d^-1 * dv;
    return Face(W, Intersection(OnSets(J, d), K), v*y);
end;
