#############################################################################
##
#A  faces.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
##
##  This file contains the routines for faces of hyperplane
##  arrangements of finite Coxeter groups.
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
#O  FaceOps . . . . . . . . . . . . . . . . . . . . . . .  operations record.
##
FaceOps:= OperationsRecord("FaceOps", DomainOps);


#############################################################################
##
#C  Face( <W>, <J>, <x> ) . . . . . . . . . . . . . . . . . . .  constructor.
##
##  <#GAPDoc Label="Face">
##  <ManSection>
##  <Func Name="Face" Arg="W, J, x"/>
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

    # check arguments?
    if IsList(x) then
        x:= PermCoxeterWord(W, x);
    fi;

    return rec(
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
##
##
FaceOps.\=:= function(l, r)
    if not IsFace(l) or not IsFace(r) then
        return false;
    fi;

    return l.W = r.W and l.J = r.J and l.x = r.x;
end;


#############################################################################
##
#F  Print( <face> ) . . . . . . . . . . . . . . . . . . . . . . . . . print.
##
FaceOps.PrintFormat:= "perm";  # "perm" or "word"

FaceOps.Print:= function(self)
    if FaceOps.PrintFormat = "word" then
        Print("Face( ", self.W, ", ", self.J, ", ", CoxeterWord(self.W, self.x), " )");
    else
        Print("Face( ", self.W, ", ", self.J, ", ", self.x, " )");
    fi;
end;

#############################################################################
##
##  FIXME: use iterator, or avoid complete listing at all.
##
Faces:= function(W)
    local   faces,  J,  x;

    # lets see, we might know them already.
    if IsBound(W.faces) then  return W.faces;  fi;

    # initialize.
    faces:= [];

    # loop over all subsets
    for J in SubsetsShapes(Shapes(W)) do
        for x in Elements(ParabolicTransversal(W, J)) do
            Add(faces, Face(W, J, x));
        od;
    od;

    # remember the faces before returning them.
    W.faces:= faces;
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
    if l.W <> r.W then
        Error("<l> and <r> must be faces of the same Coxeter group");
    fi;
    W:= l.W;
    J:= l.J;  K:= r.J;
    x:= l.x;  y:= r.x;

    # write x/y as udv, u in W_J, d in X_{JK}, v in X_{J^d \cap K}^K.
    dv:= ReducedInCoxeterCoset(ReflectionSubgroup(W, J), x/y);
    d:= ReducedInCoxeterCoset(ReflectionSubgroup(W, K), dv^-1)^-1;
    v:= d^-1 * dv;
    return Face(W, Intersection(OnSets(J, d), K), v*y);
end;

#############################################################################
##
##  FIXME: avoid listing of elements.  implement IsSubset!!
##
FaceOps.Elements:= function(self)
    return Elements(ReflectionSubgroup(W, self.J) * self.x);
end;


#############################################################################
FaceOps.IsSubset:= function(l, r)
    if IsFace(l) and IsFace(r) and l.W = r.W then
        return IsSubset(l.J, r.J)
            and ReducedInCoxeterCoset(ReflectionSubgroup(W, l.J), r.x) = l.x;
    else
        return IsSubset(Elements(l), Elements(r));
    fi;
end;


#############################################################################
FaceOps.Closure:= function(self)
    local   S,  faces,  K,  L,  w;
    S:= [1..self.W.semisimpleRank];
    faces:= [];
    for K in Combinations(Difference(S, self.J)) do
        L:= Union(self.J, K);
        w:= ReducedInCoxeterCoset(ReflectionSubgroup(self.W, L), self.x);
        Print(L, ": ", CoxeterWord(self.W, w), "\n");
        Add(faces, Face(self.W, L, w));
    od;
    return faces;
end;

#############################################################################
Hyperplanes:= function(W)
    local   reflections,  planes,  face,  sign,  i;
    reflections:= [1..W.N];
    planes:= List(reflections, x-> []);
    for face in Faces(W) do
        sign:= Call(face, "Sign");
        for i in reflections do
            if sign[i] = '0' then
                Add(planes[i], face);
            fi;
        od;
    od;
    return planes;
end;

#############################################################################
OnFaces:= function(face, w)
    return Face(face.W, face.J,
      ReducedInCoxeterCoset(ReflectionSubgroup(face.W, face.J), face.x * w));
end;

#############################################################################
FaceOps.Support:= function(self)
    return ReflectionSubgroup(W, OnSets(self.J, self.x));
end;

#############################################################################
KernelSupportMap:= function(W)
    local   fff,  sup,  pos,  ker,  i,  s,  p;

    fff:= Faces(W);
    sup:= [];  pos:= [];  ker:= [];
    for i in [1..Length(fff)] do
        s:= Call(fff[i],"Support");
        p:= Position(sup, s);
        if p = false then
            Add(sup, s);  Add(pos, i);  Add(ker, [i]);
        else
            Add(ker, ker[pos[p]]);
            Add(ker[i], i);
        fi;
    od;
    return ker;
end;


#############################################################################
##
##  a facet is a subface of codimension 1 ???
##
##  FIXME: improve
##
FaceOps.CoFacets:= function(self)
    return Filtered(Faces(self.W), x-> Size(x.J) = Size(self.J) + 1 and IsSubset(x, self));
end;

FaceOps.Facets:= function(self)
    local   WJ,  list,  s,  K,  u;

    WJ:= ReflectionSubgroup(W, self.J);
    list:= [];
    for s in self.J do
        K:= Difference(self.J, [s]);
        for u in Elements(ParabolicTransversal(WJ, K)) do
            Add(list, Face(self.W, K, u*self.x));
        od;
    od;
    return list;
end;


#############################################################################
##
##  The Face Monoid Algebra and its elements
##

#############################################################################
##
#O  FaceEltOps . . . . . . . . . . . . . . . . . . . . . . operations record.
##
FaceEltOps:= OperationsRecord("FaceEltOps", AlgebraElementOps);


#############################################################################
##
#C  FaceElt( <W>, <coef> ) . . . . . . . . . . . . . . . . . . .  constructor.
##
##  <#GAPDoc Label="FaceElt">
##  <ManSection>
##  <Func Name="Face" Arg="W, coef"/>
##  <Returns>
##    a new face monoid algebra element ...
##  </Returns>
##  <Description>
##    ...
##  <Example>
##  ...
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
FaceElt:= function(W, coef)
    return rec(W:= W,
               coef:= coef,
               isFaceElt:= true,
               operations:= FaceEltOps);
end;


#############################################################################
##
#F  IsFaceElt( <obj> ) . . . . . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsFaceElt">
##  <ManSection>
##  <Func Name="IsFaceElt" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a face monoid algebra element and
##    <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##
IsFaceElt:= function(obj)
    return IsRec(obj) and IsBound(obj.isFaceElt) and obj.isFaceElt = true;
end;

#############################################################################
##
#F  Print( <faceelt> ) . . . . . . . . . . . . . . . . . . . . . . . . . print.
##
FaceEltOps.Print:= function(self)
    local   null,  fff,  i;

    null:= true;
    fff:= Faces(self.W);
    for i in [1..Length(fff)] do
        if self.coef[i] > 0 then
            if not null then Print(" + "); fi;
            Print(self.coef[i], "*", fff[i]);
            null:= false;
        elif self.coef[i] < 0 then
            Print(" - ", -self.coef[i], "*", fff[i]);
            null:= false;
        fi;
    od;

    if null then Print(0); fi;
end;

#############################################################################
FaceOps.FaceElt:= function(self)
    local   fff,  coef,  p;

    fff:= Faces(self.W);
    coef:= List(fff, x-> 0);
    p:= Position(fff, self);
    coef[p]:= 1;
    return FaceElt(self.W, coef);
end;


#############################################################################
##
##  =
##
FaceEltOps.\=:= function(l, r)
    if not IsFaceElt(l) or not IsFaceElt(r) then
        return false;
    fi;

    return l.W = r.W and l.coef = r.coef;
end;

#############################################################################
##
##  +
##
FaceEltOps.\+:= function(l, r)
    if IsFaceElt(l) then
        if IsFaceElt(r) then
            if l.W <> r.W then
                Error("<l> and <r> must lie in a common domain");
            fi;
            return FaceElt(l.W, l.coef + r.coef);
        elif r = 0 then
            return l;
        else
            Error("don't know how to <l> + <r>");
        fi;

    elif l = 0 then
        if IsFaceElt(r) then
            return r;
        else
            Error("don't know how to <l> + <r>");
        fi;

    else

        Error("don't know how to <l> + <r>");
    fi;

end;


#############################################################################
##
##  *
##
FaceEltOps.\*:= function(l, r)
    local   fff,  prod,  i,  j,  k;

    if IsFaceElt(l) then
        if IsFaceElt(r) then
            if l.W <> r.W then
                Error("<l> and <r> must lie in a common domain");
            fi;
            fff:= Faces(l.W);
            prod:= List(fff, x-> 0);
            for i in [1..Length(fff)] do
                if l.coef[i] <> 0 then
                    for j in [1..Length(fff)] do
                        if r.coef[j] <> 0 then
                            k:= Position(fff, fff[i] * fff[j]);
                            prod[k]:= prod[k] + l.coef[i] * r.coef[j];
                        fi;
                    od;
                fi;
            od;
            return FaceElt(l.W, prod);
        elif IsCyc(r) then
            return FaceElt(l.W, r * l.coef);
        else
            Error("don't know how to <l> * <r>");
        fi;
    elif IsCyc(l) then
        if IsFaceElt(r) then
            return FaceElt(r.W, l * r.coef);
        else
            Error("Panic: this should not happen!");
        fi;
    else
        Error("don't know how to <l> * <r>");
    fi;
end;

#############################################################################
##
##
##
FaceOps.Delta:= function(self)
    local   epsilon,  sum,  x;

    epsilon:= function(a, b) # suppose a covers b
        local   s;
        s:= Difference(a.J, b.J)[1];
        return (-1)^(Number(b.J, t -> t > s) + CoxeterLength(a.W, b.x/a.x));
    end;

    sum:= 0 * Call(self, "FaceElt");
    for x in Call(self, "Facets") do
        sum:= sum + epsilon(self, x) * Call(x, "FaceElt");
    od;
    return sum;
end;


FaceEltOps.Delta:= function(self)
    local   fff,  sum,  i;

    fff:= Faces(self.W);
    sum:= 0 * self;
    for i in [1..Length(fff)] do
        if self.coef[i] <> 0 then
            sum:= sum + self.coef[i] * Call(fff[i], "Delta");
        fi;
    od;
    return sum;
end;


#############################################################################
##
##  The Intersection Lattice.
##

#############################################################################
##
##  Its elements.  How does this relate to KernelSupportMap?
##  Call(fff[s], "Support") = ImageSupportMap(W)[i] for all s in
##  Set(KernelSupportMap(W))[i]
##
ImageSupportMap:= function(W)
    local   list,  face,  sup;

    list:= [];
    for face in Faces(W) do
        sup:= Call(face, "Support");
        if not sup in list then
            Add(list, sup);
        fi;
    od;
    return list;
end;

#############################################################################
##
##  can be fed into HasseDiagram.
##
IncidenceIntersectionLattice:= function(W)
    local   lll;
    lll:= ImageSupportMap(W);
    return Relation(List(lll, x-> List(lll, y-> IsSubset(x, y))));
end;


#############################################################################
onReflectionSubgroups:= function(x, a)
    return ReflectionSubgroup(x.parent, OnTuples(x.rootInclusion, a));
end;


#############################################################################
##
##  PrimitiveIdempotents
##
PrimitiveIdempotentsFaceElts:= function(W)
    local   fff,  ker,  lll,  ell,  id,  i,  new,  sum,  j;

    fff:= Faces(W);
    ker:= Set(KernelSupportMap(W));
    lll:= ImageSupportMap(W);

    ell:= function(class)
        return Call(fff[class[1]], "FaceElt");
    end;

    ell:= function(class)
        return 1/Length(class) * Sum(class, k-> Call(fff[k], "FaceElt"));
    end;

    id:= [];
    for i in [1..Length(ker)] do
        new:= ell(ker[i]);
        sum:= new;
        for j in [1..i-1] do
            if IsSubset(lll[i], lll[j]) then
                sum:= sum + (-1)*id[j] * new;
            fi;
        od;
        id[i]:= sum;
    od;
    return id;
end;


NilpotentFaceElts:= function(W)
    local   fff,  ker,  lll,  has,  id,  nil,  i,  del,  new,  j;

    fff:= Faces(W);
    ker:= Set(KernelSupportMap(W));
    lll:= ImageSupportMap(W);
    has:= HasseDiagram(IncidenceIntersectionLattice(W));
    Print(has, "\n");
    id:= PrimitiveIdempotentsFaceElts(W);
    Print("idempotents.\n");
    nil:= [];
    for i in [1..Length(id)] do
        del:= Call(fff[ker[i][1]], "Delta");
        new:= 0 * [1..Length(id)];
        for j in i^has do
            new[j]:=  id[j] * del * id[i];
            Print(". \c");
        od;
        Add(nil, new);
        Print("\n");
    od;
    return nil;
end;


# helper
ProdMat:= function(a, b)
    local   c,  i,  j,  k;

    if Length(a[1]) <> Length(b) then
        Error("product not defined");
    fi;

    c:= [];
    for i in [1..Length(a)] do
        c[i]:= [];
        for j in [1..Length(b[1])] do
            c[i][j]:= 0;
            for k in [1..Length(b)] do
                c[i][j]:= c[i][j] + a[i][k] * b[k][j];
            od;
        od;
    od;
    return c;
end;
