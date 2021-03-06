#############################################################################
##
#A  descent.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
##
##  This file contains the basic routines for descent algebras.
##
##  <#GAPDoc Label="Intro:Descent">
##    The descent algebra of a finite Coxeter group <M>W</M> ...
##
##    The functions described in this chapter are implemented in the file
##    <F>descent.g</F>.
##  <#/GAPDoc>
##
##  TODO:  clean up: need only one program for the quiver!!!
##  TODO:  elements, bases, ..., in blocks by shape, ...
##

RequirePackage("chevie");


#############################################################################
##
##  create descent algebras as a subclass of Algebra -- need to provide
##  special functions later ...
##
DescentAlgebraOps:= OperationsRecord("DescentAlgebraOps", AlgebraOps);

#############################################################################
##
#F  DescentAlgebra( <W> ) . . . . . . . . . . . . . . . . . . .  constructor.
##
##  <#GAPDoc Label="DescentAlgebra">
##  <ManSection>
##  <Func Name="DescentAlgebra" Arg="W"/>
##  <Returns>
##    an object that represents the descent algebra of the Coxeter group
##    <A>W</A>.
##  </Returns>
##  <Description>
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> D:= DescentAlgebra(W);
##  DescentAlgebra( CoxeterGroup("A", 5) )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
DescentAlgebra:= function(W)
    local   self,  i;

    self:= rec(W:= W, operations:= DescentAlgebraOps, isDescentAlgebra:= true);

    self.GetAJKL:= function(J, K, L)
        local   xxx,  l;
        if L > K then return 0; fi;
        xxx:= RightRegularX(self);
        l:= Position(xxx[K].pos[J], L);
        if l = false then return 0; fi;
        return xxx[K].val[J][l];
    end;

    self.basis:= "x";  # default basis

    # a standard labelling of basis elements ...
    self.sss:= SubsetsShapes(Shapes(W));

    # ... and how to locate a label in the list
    self.encodeSet:= set -> Sum(set, i-> 2^(i-1)) + 1;
    self.pos:= [];
    for i in [1..Length(self.sss)] do
        self.pos[self.encodeSet(self.sss[i])]:= i;
    od;

    return self;
end;

#############################################################################
##
##
##
IsDescentAlgebra:= function(obj)
    return IsRec(obj) and IsBound(obj.isDescentAlgebra)
           and obj.isDescentAlgebra = true;
end;

#############################################################################
##
#F  Print( <descalg> )
##
DescentAlgebraOps.Print:= function(self)
    if IsBound(self.name) then
        Print(self.name);
    else
        Print("DescentAlgebra( ", self.W, " )");
    fi;
end;


#############################################################################
##
##
##
DescentAlgebraOps.Dimension:= function(self)
    return 2^self.W.semisimpleRank;
end;


#############################################################################
##
#F  DescentAlgebraOps.Mu( <D> )
##
##  The idempotents from BBHT.
##  the rows of nu express the quasi-idempotents e_J in terms of the x_J.
##  <init> could be any list of 2^n entries > 0.
##
DescentAlgebraOps.Mu:= function(D)
    local   lll,  mu,  j0,  a,  j,  k0,  b,  k,  l;

    lll:= List(Shapes(D.W), Size);
    mu:= [];  j0:= 0;
    for a in lll do
        for j in j0 + [1..a] do
            mu[j]:= [];  k0:= 0;
            for b in lll do
                for k in k0 + [1..b] do
                    mu[j][k]:= 0;
                    for l in k0 + [1..b] do
                        mu[j][k]:= mu[j][k] + D.GetAJKL(l, j, k);
                    od;
                od;
                k0:= k0 + b;
            od;
        od;
        j0:= j0 + a;
    od;

    return mu;
end;



#############################################################################
##
##  A DescentElt is an element of a DescentAlgebra
##


#############################################################################
##
#O  DescentEltOps
##
DescentEltOps:= OperationsRecord("DescentEltOps", AlgebraElementOps);

#############################################################################
##
##  DescentElt
##
DescentElt:= function(D, basis, coeff)
    return rec(D:= D,
               basis:= basis,
               coeff:= coeff,
               isDescentElt:= true,
               operations:= DescentEltOps);
end;


DescentAlgebraOps.Basis:= function(arg)
    local   self,  basis,  d,  i,  new;

    self:= arg[1];
    if Length(arg) = 1 then
        basis:= [];
        d:= Dimension(self);
        for i in [1..d] do
            new:=  0 * [1..d];
            new[i]:= 1;
            Add(basis, DescentElt(self, self.basis, new));
        od;
        return basis;
    elif Length(arg) = 2 then
        if arg[2] in ["x", "y", "z", "e"] then
            d:= arg[2];
            return function(arg)
                new:= 0 * [1..Dimension(self)];
                new[self.pos[self.encodeSet(arg)]]:= 1;
                return DescentElt(self, d, new);
            end;
        else
            Error("not yet implemented");
        fi;
    else
        Error("not yet implemented");
    fi;
end;

##  base changes ...
DescentEltOps.x:= function(self)
    local   mat;

    if self.basis = "x" then
        return self;
    elif self.basis = "y" then
        mat:= IncidenceMatShapes(Shapes(self.D.W));
        return DescentElt(self.D, "x", self.coeff / mat);
    elif self.basis = "e" then
        mat:= Call(self.D, "Mu");
        return DescentElt(self.D, "x", self.coeff / mat);
    else
        Error("not yet implemented");
    fi;
end;

DescentEltOps.y:= function(self)
    local   mat;

    if self.basis = "y" then
        return self;
    elif self.basis = "x" then
        mat:= IncidenceMatShapes(Shapes(self.D.W));
        return DescentElt(self.D, "y", self.coeff * mat);
    elif self.basis = "e" then
        mat:= Call(self.D, "Mu")^-1 * IncidenceMatShapes(Shapes(self.D.W));
        return DescentElt(self.D, "y", self.coeff * mat);
    else
        Error("not yet implemented");
    fi;
end;

DescentEltOps.e:= function(self)
    local   mat;

    if self.basis = "e" then
        return self;
    elif self.basis = "x" then
        mat:= Call(self.D, "Mu");
        return DescentElt(self.D, "e", self.coeff * mat);
    elif self.basis = "y" then
        mat:= IncidenceMatShapes(Shapes(self.W))^-1 * Call(self.D, "Mu");
        return DescentElt(self.D, "e", self.coeff * mat);
    else
        Error("not yet implemented");
    fi;
end;


#############################################################################
##
##  IsDescentElt
##
IsDescentElt:= function(obj)
    return IsRec(obj) and IsBound(obj.isDescentElt)
           and obj.isDescentElt = true;
end;


#############################################################################
##
##
##
DescentEltOps.String:= function(self)
    local   bracketless,  sss,  more,  summand,  str,  i;

    # helper: how to print a list without brackets
    bracketless:= function(list)
        local   str,  i;
        if list = [] then return ""; fi;
        str:= String(list[1]);
        for i in [2..Length(list)] do
            Add(str, ',');
            Append(str, String(list[i]));
        od;
        return str;
    end;

    sss:= SubsetsShapes(Shapes(self.D.W));
    more:= false;

    summand:= function(i)
        local   str;
        if self.coeff[i] = 0 then return ""; fi;
        if self.coeff[i] > 0 then
            if more then
                str:= " + ";
            else
                str:= "";
            fi;
            if self.coeff[i] <> 1 then
                Append(str, String(self.coeff[i]));
                Append(str, "*");
            fi;
        else
            if more then
                str:= " - ";
            else
                str:= "-";
            fi;
            if self.coeff[i] <> -1 then
                Append(str, String(-self.coeff[i]));
                Append(str, "*");
            fi;
        fi;

        Append(str, self.basis);
        Add(str, '(');
        Append(str, bracketless(sss[i]));
        Add(str, ')');
        return str;
    end;

    str:= "";
    for i in [1..Length(sss)] do
        Append(str, summand(i));
        if str <> "" then
            more:= true;
        fi;
    od;

    if str = "" then
        return "0";
    else
        return str;
    fi;
end;

##
DescentEltOps.Print:= function(self)
    Print("DescentElt(", self.D, ", \"", self.basis, "\", ", self.coeff, ")");
end;


DescentEltOps.\+:= function(l, r)
    if not (IsDescentElt(l) and IsDescentElt(r)) then
        Error("don't know how to add <l> and <r>");
    fi;
    if not IsIdentical(l.D, r.D) then
        Error("summands must be elements of the same algebra");
    fi;
    if l.basis <> r.basis then
        Error("not yet implemented");
    fi;
    return DescentElt(l.D, l.basis, l.coeff + r.coeff);
end;


DescentEltOps.Matrix:= function(self)
    local   d,  mat,  xxx,  i;
    if self.basis = "x" then
        d:= Length(self.coeff);
        mat:= NullMat(d, d);
        xxx:= RightRegularX(self.D);
        for i in [1..d] do
            if self.coeff[i] <> 0 then
                mat:= mat + self.coeff[i] * MatCompressedAJKL(xxx[i]);
            fi;
        od;
        return mat;
    else
        Error("not yet implemented");
    fi;
end;


DescentEltOps.\*:= function(l, r)
    if IsDescentElt(l) then
        if IsDescentElt(r) then
            if not IsIdentical(l.D, r.D) then
                Error("summands must be elements of the same algebra");
            fi;
            if l.basis <> r.basis then
                Error("not yet implemented");
            fi;
            return DescentElt(l.D, l.basis, l.coeff * Call(r, "Matrix"));
        else
            return DescentElt(l.D, l.basis, l.coeff * r);
        fi;
    else
        if IsDescentElt(r) then
            return DescentElt(r.D, r.basis, l * r.coeff);
        else
            Error("Panic: neither <l> nor <r> is a DescentElt!");
        fi;
    fi;
end;

DescentEltOps.\-:= function(l, r)
    return l + -r;
end;



#############################################################################
#
#  turn $a \in \Sigma(W)$ into the character $\theta(a)$.
#
#  elt must be a matrix in the X basis.
##  FIXME: let elt be DescentElt.
#
CharacterDescentElt:= function(W, elt)

   local cc, ddd, chi, c, i;

   chi:= [];
   ddd:= SubsetsShapes(Shapes(W));
   cc:= ConjugacyClasses(W);
   for c in cc do
      i:= Position(ddd, Set(CoxeterWord(W, Representative(c))));
      Add(chi, elt[i][i]);
   od;

   return chi;
end;

#############################################################################
#
#  Given W and s in S. Let M = S - s.  Loop over X_M and determine a_{JML}.
#  Returns a rectangular matrix with rows J subseteq S and cols L subseteq M.
#
#  iterator version.
#
MaximalAJKL:= function(W, s)

   local S, M, pos, cosrep, aJML, inn, out, J, L, ddd, sub, j, l, x;

   ddd:= SubsetsShapes(Shapes(W));
   S:= W.rootInclusion{[1..W.semisimpleRank]};
   M:= Difference(S, [s]);
   pos:= Filtered([1..Length(ddd)], x-> IsSubset(M, ddd[x]));
   sub:= ddd{pos};

   cosrep:= Iterator(ParabolicTransversal(W, M));

   aJML:= List(ddd, x-> 0*pos);

#   for x in cosrep do
   while cosrep.hasNext() do
      x:= cosrep.next();
      inn:= Difference(S, RightDescentSet(W, x));
      InfoZigzag2(" i: ", inn, "\n");
      for J in Combinations(inn) do
         L:= Intersection(M, OnSets(J, x^-1));
         j:= Position(ddd, J);  l:= Position(sub, L);
         aJML[j][l]:= aJML[j][l] + 1;
      od;
   od;

   # compress into pos/val (where pos is relative to all of ddd!)
   out:= rec(pos:= [], val:= []);
   for j in [1..Length(aJML)] do
      out.pos[j]:= [];  out.val[j]:= [];
      for l in [1..Length(aJML[j])] do
         if aJML[j][l] > 0 then
            Add(out.pos[j], pos[l]);
            Add(out.val[j], aJML[j][l]);
         fi;
      od;
   od;
   out.ddd:= ddd; out.sub:= sub;
   return out;
end;


# a function to blow up an aJML.
MatCompressedAJKL:= function(aJKL)
    local   n,  mat,  i,  j;

    n:= Length(aJKL.pos);
    mat:= List([1..n], x-> 0*[1..n]);
    for i in [1..n] do
        for j in [1..Length(aJKL.pos[i])] do
            mat[i][aJKL.pos[i][j]]:= aJKL.val[i][j];
        od;
    od;
    return mat;
end;


# a function to multiply two aJMLs.
ProductCompressedAJKL:= function(A, B)
    local   fus,  C,  k,  i,  c,  j,  p, inv;

    # c_{ik} = \sum_j a_{ij} * b_{jk}
    fus:= List(B.ddd, x-> Position(A.ddd, x));
    inv:= [];
    for i in [1..Length(fus)] do inv[fus[i]]:= i; od;
    C:= rec(pos:= List(A.pos, x-> []), val:= List(A.pos, x-> []));
    for k in Union(B.pos) do
        for i in [1..Length(A.pos)] do
            c:= 0;
            for j in [1..Length(A.pos[i])] do
                p:= Position(B.pos[inv[A.pos[i][j]]], k);
                if p <> false then
                    c:= c + A.val[i][j] * B.val[inv[A.pos[i][j]]][p];
                fi;
            od;
            if c <> 0 then
                Add(C.pos[i], fus[k]);
                Add(C.val[i], c);
            fi;
        od;
    od;

    C.ddd:= A.ddd;
    C.sub:= C.ddd{fus{Union(B.pos)}};

    return C;
end;


#############################################################################
##
#F  RightRegularX( <D> )
##
RightRegularX:= function(D)
    local   W,  S,  subsets,  complmt,  xxx,  d,  m,  c,  e,  p,  WJ;

    if IsBound(D.rightRegularX) then
        return D.rightRegularX;
    fi;

    W:= D.W;
    S:= W.rootInclusion{[1..W.semisimpleRank]};
    subsets:= SubsetsShapes(Shapes(W));
    complmt:= List(subsets, x-> Position(subsets, Difference(S, x)));
    xxx:= [];
    for d in subsets do
        if d = [] then
            m:= MaximalAJKL(W, 0);
        else
            c:= Difference(S, d);
            e:= Union(c, [d[Length(d)]]);
            p:= Position(subsets, Difference(S, e));
            WJ:= ReflectionSubgroup(W, e);
            m:= MaximalAJKL(WJ, d[Length(d)]);
            m:= ProductCompressedAJKL(xxx[p], m);
        fi;
        Add(xxx, m);
    od;

    D.rightRegularX:= xxx{complmt};
    return D.rightRegularX;
end;


# deprecate:
LeftRegularX:= function(D)
    local   xxx,  x,  i,  j;

    if IsBound(D.leftRegularX) then
        return D.leftRegularX;
    fi;

    xxx:= List(RightRegularX(D), MatCompressedAJKL);
    x:= [];
    for i in [1..Length(xxx)] do
        x[i]:= [];
        for j in [1..Length(xxx)] do
            x[i][j]:= xxx[j][i];
        od;
    od;

    D.leftRegularX:= x;
    return x;
end;


#  deprecate:
LeftRegularY:= function(D)
    local   inc;
    inc:= IncidenceMatShapes(Shapes(D.W))^-1;
    return List(inc, l-> l * LeftRegularX(D));
end;


#  deprecate:
LeftRegularZ:= function(D)
    local   w0;
    w0:= LeftRegularY(D)[1];
    #  warning: hier muss man eigentlich noch die Reihenfolge umdrehn:
    # dies hier ergibt die Liste der z_{\hat{J}} !!!
    return List(LeftRegularX(D), x-> x * w0);
end;


#  deprecate:
LeftRegularE:= function(D)
    local   nu;
    nu:= Call(D, "Mu")^-1;
    return List(nu, l-> l * LeftRegularX(D));
end;


#############################################################################
##
#F  SymmetricMatrix( <D> )  . . . . . . . . . . . . . . . . symmetric matrix.
##
##  <#GAPDoc Label="SymmetricMatrix">
##  <ManSection>
##  <Func Name="SymmetricMatrix" Arg="D"/>
##  <Returns>the matrix of values <M>\theta(x_J)(x_K)</M>.</Returns>
##  <Description>
##    Let <M>\theta</M> be the homomorphism from the descent algebra of a
##    finite Coxeter group <M>W</M> into the character ring of <M>W</M>
##    which, for <M>J \subseteq S</M> assigns to an element <M>x_J</M>
##    the permutation character of the action of <M>W</M> on the cosets
##    of the parabolic subgroup <M>W_J</M>.  Then the matrix of values
##    <M>\theta(x_J)(x_K)</M> is symmetric (see <Cite
##    Key="JoellenbeckReutenauer2001"/> and <Cite Key="BHS2005"/>).
##  <Example>
##  gap> D:= DescentAlgebra(CoxeterGroup("A", 3));;
##  gap> SymmetricMatrix(D);
##  [ [ 24, 24, 24, 24, 24, 24, 24, 24 ], [ 24, 18, 18, 18, 14, 14, 14, 12 ],
##    [ 24, 18, 18, 18, 14, 14, 14, 12 ], [ 24, 18, 18, 18, 14, 14, 14, 12 ],
##    [ 24, 14, 14, 14, 10, 8, 8, 6 ], [ 24, 14, 14, 14, 8, 7, 7, 4 ],
##    [ 24, 14, 14, 14, 8, 7, 7, 4 ], [ 24, 12, 12, 12, 6, 4, 4, 1 ] ]
##  gap> PrintArray(last);
##  [ [  24,  24,  24,  24,  24,  24,  24,  24 ],
##    [  24,  18,  18,  18,  14,  14,  14,  12 ],
##    [  24,  18,  18,  18,  14,  14,  14,  12 ],
##    [  24,  18,  18,  18,  14,  14,  14,  12 ],
##    [  24,  14,  14,  14,  10,   8,   8,   6 ],
##    [  24,  14,  14,  14,   8,   7,   7,   4 ],
##    [  24,  14,  14,  14,   8,   7,   7,   4 ],
##    [  24,  12,  12,  12,   6,   4,   4,   1 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
SymmetricMatrix:= function(D)
    local  inc,  sz,  yct;

    inc:= IncidenceMatShapes(Shapes(D.W));
    sz:= SizesDescentConjugacyClasses(D.W);
    yct:= YCharacters(D.W);
    return inc * yct * TransposedMat(inc * sz);
end;


#############################################################################
##
##  For type A:  The partitions quiver.
##
##  ??? This should be a binary relation ...
##
##  FIXME: use standard ordering on partitions.
##
MatQuiverSym:= function(n)
    local   shrirev,  ppp,  l,  mat,  i,  pp,  p,  new,  j;

    shrirev:= function(list)  # return list reversed and w/o holes.
        local   res,  i;
        res:= [];
        for i in [1..Length(list)] do
            if IsBound(list[i]) then Add(res, list[i]); fi;
        od;
        Sort(res, function(a, b) return a > b; end);
        return res;
    end;

    ppp:= Partitions(n);
    Sort(ppp, function(a, b) return Length(a) > Length(b); end);
    l:= Length(ppp);
    mat:= [[0]];  mat:= mat{0*[1..l]+1}{0*[1..l]+1};
    for i in [1..l] do
        pp:= Filtered(Combinations(ppp[i], 2), x-> x[1] <> x[2]);
        for p in pp do
            new:= Reversed(ppp[i]);
            Unbind(new[Position(new, p[1])]);
            Unbind(new[Position(new, p[2])]);
            Add(new, p[1]+p[2]);
            j:= Position(ppp, shrirev(new));
            mat[j][i]:= 1;
        od;
    od;
    return mat;
end;

##
##  and the Cartan Matrix after [Garsia-Reutenauer]
##
LyndonFactorisation:= function(word)
    local   lastFactor,  factors,  f;

    # The last factor is the lexicographically smallest tail of list.
    lastFactor:= function(list)
        local l, tail;
        l:= Length(list);
        tail:= List([1..l], i-> list{[i..l]});
        Sort(tail);
        return tail[1];
    end;

    factors:= [];
    while Length(word) > 0 do
        f:= lastFactor(word);
        Add(factors, f);
        word:= word{[1..Length(word)-Length(f)]};
    od;
    return Reversed(factors);
end;


##  FIXME: find faster way to produce partitions in standard order
CartanMatrixA:=function(n)
    local   typeComposition,  par,  p,  car,  i,  x,  j;

    #  the type of a composition is determined by the sums of the
    #  factors of its Lyndon Factorization
    typeComposition:=function(com)
        local sum;

        sum:= List(LyndonFactorisation(com), Sum);
        Sort(sum);
        return Reversed(sum);
    end;

    par:= LabelsShapes(Shapes(CoxeterGroup("A", n)));
    p:= Length(par);
    car:= NullMat(p, p);
    for i in [1..p] do
        for x in Arrangements(par[i], Length(par[i])) do
            j:= Position(par, typeComposition(x));
            car[j][i]:= car[j][i] + 1;
        od;
    od;
    return car;
end;

QCartanMatrixA:=function(n, q)
    local   typeComposition,  par,  p,  car,  i,  x,  j;

    #  the type of a composition is determined by the sums of the
    #  factors of its Lyndon Factorization
    typeComposition:=function(com)
        local sum;

        sum:= List(LyndonFactorisation(com), Sum);
        Sort(sum);
        return Reversed(sum);
    end;

    par:= LabelsShapes(Shapes(CoxeterGroup("A", n)));
    p:= Length(par);
    car:= q * NullMat(p, p);
    for i in [1..p] do
        for x in Arrangements(par[i], Length(par[i])) do
            j:= Position(par, typeComposition(x));
            car[j][i]:= car[j][i] + q^(Length(par[i]) - Length(par[j]));
        od;
    od;
    return car;
end;

##  this is only conjecturally correct:
##
CartanMatrixB:=function(n)
    local   typeComposition,  par,  p,  car,  i,  x,  j;

    #  the type of a composition is determined by the sums of the
    #  factors of its Lyndon Factorization
    typeComposition:=function(com)
        local   fac,  sum;

        fac:= Filtered(LyndonFactorisation(com), x-> Length(x) mod 2 = 1);
        sum:= List(fac, Sum);
        Sort(sum);
        return Reversed(sum);
    end;

    par:= LabelsShapes(Shapes(CoxeterGroup("B", n)));
    p:= Length(par);
    car:= NullMat(p, p);
    for i in [1..p] do
        for x in Arrangements(par[i], Length(par[i])) do
            j:= Position(par, typeComposition(x));
            car[j][i]:= car[j][i] + 1;
        od;
    od;
    return car;
end;


#############################################################################
##
#F  QuiverRelations( <D> )  . . . . . . . . . . . . . . . . . . . . . quiver.
##
##  <#GAPDoc Label="QuiverRelations">
##  <ManSection>
##  <Func Name="QuiverRelations" Arg="D"/>
##  <Returns>
##    the quiver with relations of the descent algebra
##    <A>D</A>.
##  </Returns>
##  <Description>
##    The quiver with relations of the descent algebra of a finite Coxeter
##    group <M>W</M> is computed by the algorithm from <Cite
##    Key="Pfeiffer2009"/>.  The result is a directed graph which has the
##    shapes of <M>W</M> as its vertex set.  This graph is here
##    represented by a record with components <K>path0</K>, the list of
##    vertices as streets of length 0, <K>path</K>, a list of lists of
##    lists, where <K>path[i]</K> is a list of paths of length <K>i</K>,
##    and <K>relations</K>, a list of relations that have been discovered
##    between paths of the same length.
##  <Example>
##  gap> qr:= QuiverRelations(DescentAlgebra(CoxeterGroup("A", 2)));
##  rec(
##    path0 := [ Street( CoxeterGroup("A", 2), [ [  ], [  ] ] ),
##        Street( CoxeterGroup("A", 2), [ [ 1 ], [  ] ] ),
##        Street( CoxeterGroup("A", 2), [ [ 1, 2 ], [  ] ] ) ],
##    path := [ [ [ Street( CoxeterGroup("A", 2), [ [ 1, 2 ], [ 1 ] ] ) ] ] ],
##    relations := [  ] )
##  </Example>
##    A formatted version of the quiver can be produced with the function
##    <Ref Func="DisplayQuiver"/>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
QuiverRelations0:= function(D)
    local   deltaPath,  path,  path0,  more,  a,  relations,  sss,  l,
            null,  all,  mat,  delta,  new,  kern,  adr,  delete,
            line,  pos,  i,  b;

    # maybe we know it already.
    if IsBound(D.quiverRelations) then
        return D.quiverRelations;
    fi;


    # a path is a sequence of streets, with adjacent ones multiplyable.
    deltaPath:= function(path)
        local   p;
        p:= ProductStreetMatrixList(Map(path, "Matrix"));
        return rec(support:= p.target, mat:= Sum(p.mat));
    end;

    # split idempotent from nilpotent generators.
    path:= [];  path0:= [];  more:= [];
    for a in BasicStreets(D.W) do
        if a.alley[2] = [] then
            Add(path0, a);
        else
            Add(more, [a]);
        fi;
    od;
    InfoZigzag1("of which ", Length(path0), " have length 0.\n");

    relations:= [];

    sss:= SubsetsShapes(Shapes(D.W));
    l:= SetComposition(List(Shapes(D.W), Size));
    null:= List(sss, x-> 0);

    while more <> [] do

        Add(path, more);
        InfoZigzag1("Added ", Length(more), " paths of length ", Length(path), ".\n");

        # consider all paths at once.
        all:= Concatenation(path);

        mat:= [];
        for a in all do
            delta:= deltaPath(a);
            new:= Copy(null);
            new{l[delta.support]}:= delta.mat;
            Add(mat, new);
        od;

        kern:= NullspaceMat(mat);
        InfoZigzag1("Found ", Length(kern), " relations.\n");


        # FIXME:
        # suppose adr is a list of back references such that
        #   all[i] = path[adr[i][1]][adr[i][2]] ...
        adr:= Concatenation(List([1..Length(path)], i-> TransposedMat([List(path[i], x-> i), [1..Length(path[i])]])));


        # find all relations.
        delete:= List(path, x-> []);
        for line in kern do
            pos:= Filtered([1..Length(line)], i-> line[i] <> 0);
            Add(relations, rec(paths:= all{pos}, coeffs:= line{pos}));
            Add(delete[adr[pos[1]][1]], adr[pos[1]][2]);
        od;

        # remove obsoletes.
        for i in [1..Length(path)] do
            path[i]:= path[i]{Difference([1..Length(path[i])], delete[i])};
        od;

        InfoZigzag1("Deleted: ", List(delete, Length), "\n");
        InfoZigzag1("Length: ", List(path, Length), ": ", Length(path0) + Sum(path, Length), ".\n");

        # extend paths.
        more:= [];
        for a in path[Length(path)] do
            for b in path[1] do
                if a[Length(a)] * b[1] <> [] then
                    Add(more, Concatenation(a, b));
                fi;
            od;
        od;

    od;

    # remember for next visit.
    D.quiverRelations:= rec(path0:= path0, path:= path, relations:= relations);

    return D.quiverRelations;
end;



#  alternatively:
#  with a slightly different, more efficient data structure.
#
##  The resulting object qr has components:
##
##  path0
##  a list of streets of length 0, the vertices, or paths of length 0.
##
##  path
##  a list, with path[i] being the list of all? paths of length i,
##  where a path is a list of Streets of length > 0.
##  In particular path[1] is the list of streets chosen to represent
##  the edges
##
##  relations
##
##  pathmat
##  a matrix with one entry for each  homspace with components
##
##    path
##    the list of paths in this hom-space
##
##    adr
##    the list of addresses of the paths in the above lists path0, path.
##
##    mat
##    the list of delta-values, ie. images in the descent algebra
##
##    kern
##    the nullspacemat of mat, a basis of the kernel of delta
##
##    basis
##    a list of positions in path, selecting a preimage of a basis
##
##    map
##    how to express the image of a path in terms of the basis.
##
##    cons
##    consequences of relations in other hom spaces to this one
##
##    rela
##    essential relations on this hom-space
##

QuiverRelations1:= function(D)
    local   sourcePath,  targetPath,  deltaPath,  path1,  path0,  s,
            path,  sh,  pathmat,  j,  i,  t,  delete,  adr,  mat,  a,
            kern,  line,  pos,  e,  k,  map,  p,  new,  rel,  cons,
            space,  relations;

#    # maybe we know it already.
#    if IsBound(D.quiverRelations) then
#        return D.quiverRelations;
#    fi;
#
    # a path is a sequence of streets, with adjacent ones multiplyable:
    # it has a source ...
    sourcePath:= function(path)
        return Call(path[1], "Source");
    end;

    # ... it has a target ...
    targetPath:= function(path)
        return Call(path[Length(path)], "Target");
    end;

    # ... and an associated delta-value.
    deltaPath:= function(path)
        local   p;
        p:= ProductStreetMatrixList(Map(path, "Matrix"));
        return rec(support:= p.target, mat:= Sum(p.mat));
    end;

    # split idempotent from nilpotent generators.
    path1:= [];  path0:= [];
    for s in BasicStreets(D.W) do
        if s.alley[2] = [] then
            Add(path0, s);
        else
            Add(path1, s);
        fi;
    od;
    InfoZigzag1("Starting with ", Length(path0) + Length(path1), " paths,\n");
    InfoZigzag1("of which ", Length(path0), " have length 0.\n");

    repeat
        path:= PathsStreets(path1, D.W.semisimpleRank);
        sh:= Shapes(D.W);

        # distribute paths over hom-spaces
        pathmat:= List(sh, x-> List(sh, x-> rec(path:= [], adr:= [])));
        for j in [1..Length(path0)] do  # here actually s == j !!!
            s:= Call(path0[j], "Source");
            Add(pathmat[s][s].adr, [0,j]);
            Add(pathmat[s][s].path, []);
        od;
        for i in [1..Length(path)] do
            for j in [1..Length(path[i])] do
                s:= sourcePath(path[i][j]);
                t:= targetPath(path[i][j]);
                Add(pathmat[s][t].adr, [i,j]);
                Add(pathmat[s][t].path, path[i][j]);
            od;
        od;

        # calculate all relations
        delete:= List(path, x-> []);

        for i in [1..Length(sh)] do
            for j in [1..Length(sh)] do
                adr:= pathmat[i][j].adr;
                mat:= [];
                for a in adr do
                    if a[1] = 0 then
                        Add(mat, Call(path0[a[2]], "Delta").mat);
                    else
                        Add(mat, deltaPath(path[a[1]][a[2]]).mat);
                    fi;
                od;
                if mat = [] then
                    kern:= [];
                else
                    kern:= NullspaceMat(mat);
                fi;

                for line in kern do
                    pos:= Filtered([1..Length(line)], i-> line[i] <> 0);
                    Add(delete[adr[pos[1]][1]], adr[pos[1]][2]);
                od;


                pathmat[i][j].mat:= mat;
                pathmat[i][j].kern:= kern;
                pathmat[i][j].basis:= Difference([1..Length(mat)], List(kern, x-> Position(x, 1)));

                # express each path in terms of chosen basis.
                mat:= TransposedMat(Reversed(mat));
                TriangulizeMat(mat);
                mat:= Filtered(mat, x-> x <> 0*x);
                pathmat[i][j].map:= Reversed(TransposedMat(Reversed(mat)));
            od;
        od;

        InfoZigzag1(delete, " ", delete[1], "\n");

        path1:= path1{Difference([1..Length(path1)], delete[1])};
    until delete[1] =  [];

    # determine consequences of relations.
    for i in [1..Length(sh)] do
        for j in [1..Length(sh)] do
            pathmat[i][j].cons:= [];
        od;
    od;

    for e in path[1] do
        j:= sourcePath(e);  k:= targetPath(e);

        # postmultply edge and make map from (i, j) to (i, k).
        for i in [1..Length(sh)] do
            map:= [];
            for p in pathmat[i][j].path do
                Add(map, Position(pathmat[i][k].path, Concatenation(p, e)));
            od;
            new:= [];
            for rel in pathmat[i][j].kern do
                cons:= List(pathmat[i][k].path, x-> 0);
                cons{map}:= rel;
                Add(new, cons);
            od;
            if new <> [] then
                Add(pathmat[i][k].cons, new);
            fi;
        od;


        # premultiply edge and make map from (k, i) to (j, i).
        for i in [1..Length(sh)] do
            map:= [];
            for p in pathmat[k][i].path do
                Add(map, Position(pathmat[j][i].path, Concatenation(e, p)));
            od;
            new:= [];
            for rel in pathmat[k][i].kern do
                cons:= List(pathmat[j][i].path, x-> 0);
                cons{map}:= rel;
                Add(new, cons);
            od;
            if new <> [] then
                Add(pathmat[j][i].cons, new);
            fi;

        od;


    od;

    # find essential relations.
    for i in [1..Length(sh)] do
        for j in [1..Length(sh)] do
            if pathmat[i][j].cons = [] then
                pathmat[i][j].rela:= pathmat[i][j].kern;
            else
                space:= RowSpace(Rationals, pathmat[i][j].kern);
                space:= space/Subspace(space, Concatenation(pathmat[i][j].cons));
                pathmat[i][j].rela:= Basis(space).vectors;
            fi;
        od;
    od;

    # calculate all relations
    relations:= [];

    for i in [1..Length(sh)] do
        for j in [1..Length(sh)] do
            adr:= pathmat[i][j].adr;
            for line in pathmat[i][j].rela do
                pos:= Filtered([1..Length(line)], i-> line[i] <> 0);
                Add(relations, rec(paths:= adr{pos}, coeffs:= line{pos}));
            od;
        od;
    od;


    return rec(path0:= path0, path:= path, pathmat:= pathmat, relations:= relations);
end;

QuiverRelations:= QuiverRelations1;


SyzygiesQuiver:= function(qr)
    local   basisPim,  N,  prores,  matrixEdge;

    # how to find the basis of a pim.
    basisPim:= function(i)
        return Concatenation(List(qr.pathmat[i], x-> x.adr{x.basis}));
    end;

    N:= Length(qr.pathmat);

    # now for the projective resolutions.
    prores:= List([1..N],
                  x-> rec(mat:= [], src:= []));

    # how to turn an edge into a matrix (of the hom from one pim to another)
    matrixEdge:= function(e)
        local   j,  k,  pj,  pk,  dimj,  dimk,  comj,  comk,  matrix,
                i,  map,  p;

        j:= Call(e[1], "Source");
        k:= Call(e[1], "Target");

        pj:= qr.pathmat[j];
        pk:= qr.pathmat[k];

        dimj:= List(pj, x-> Length(x.basis));
        dimk:= List(pk, x-> Length(x.basis));

        comj:= SetComposition(dimj);
        comk:= SetComposition(dimk);

        matrix:= NullMat(Sum(dimk), Sum(dimj));

        # premultiply edge and make map from (k, i) to (j, i).
        for i in [1..N] do
            map:= [];
            for p in pk[i].path{pk[i].basis} do
                Add(map, pj[i].map[Position(pj[i].path, Concatenation(e, p))]);
            od;
            if map <> [] then
                matrix{comk[i]}{comj[i]}:= map;
            fi;
        od;

        Add(prores[j].src, k);
        Append(prores[j].mat, matrix);

        return matrix;
    end;

    return rec(edges:=  List(qr.path[1], matrixEdge), prores:= prores);

end;

##  Suppose a module M is given as a submodule of a direct sum of projectives, ie., as a list of indices and a basis, find a projective cover, ie. a direct sum P of pims and a linear map  P -> M.
##
ProjectiveCover:= function(qr, pims, basis)
    local   N,  iii,  lll,  dim,  o,  com,  d,  ind,  pim,  i,  space,
            radical,  eMat,  e,  j,  k,  new,  pi,  map,  p,  ss,
            simples,  matrix,  top,  line,  a;

    N:= Length(qr.pathmat);  # nr of shapes.
    iii:= [1..Length(pims)];
    lll:= [1..Length(basis)];

    # set up some addresses
    dim:= List(pims, j-> List(qr.pathmat[j], x-> Length(x.basis)));
    o:= 0; # offset;
    com:= [];
    for d in dim do
        Add(com, SetComposition(d) + o);
        o:= o + Sum(d);
    od;

    # assert that no basis elt mixes pims and attach pims to them
    ind:= List([1..N], i-> Concatenation(com{iii}[i]));
    pim:= List(basis, x-> Filtered([1..N], i-> x{ind[i]} <> 0 * ind[i]));
    for i in [1..Length(pim)] do
        if Length(pim[i]) <> 1 then
            Error("basis elt mixes");
        else
            pim[i]:= pim[i][1];
        fi;
    od;

    # compute radical of the module: postmultiply edges
    space:= RowSpace(Rationals, basis);
    radical:= Subspace(space, []);
    eMat:= [];
    for e in qr.path[1] do
        j:= Call(e[1], "Source");
        k:= Call(e[1], "Target");
        new:= 0*basis;
        for i in iii do
            pi:= qr.pathmat[pims[i]];
            map:= [];
            for p in pi[j].path{pi[j].basis} do
                Add(map, pi[k].map[Position(pi[k].path, Concatenation(p, e))]);
            od;
            if map <> [] then
                new{lll}{com[i][k]}:= basis{lll}{com[i][j]} * map;
            fi;
        od;

        for k in new do
            if not k in radical then
                radical:= radical + Subspace(space, [k]);
            fi;
        od;


        # express new in terms of basis
        new:= TransposedMat(Concatenation(basis, new));
        TriangulizeMat(new);
        k:= Length(basis);
        Add(eMat, TransposedMat(new{[1..k]}{k+[1..k]}));
    od;

    # form the quotient
    ss:= Basis(space/radical).vectors;
    j:= Length(ss);

    # assert that these are a subset of the original basis.
    ss:= List(ss, x-> Position(basis, x));
    if false in ss then
        Error("quotient basis is not a subset");
    fi;



    #    # express ss in terms of basis
    #    ss:= TransposedMat(Concatenation(basis, ss));
    #    TriangulizeMat(ss);
    #    k:= Length(basis);
    #    ss:= TransposedMat(ss{[1..k]}{k+[1..j]});

    # identify simples (as *the* vMat that doesnt act trivially)
    simples:= pim{ss};


    # compute new matrix
    matrix:= [];
    for k in ss do
        top:= List(basis, x-> 0);  top[k]:= 1;      # make k-th basis vector
        pi:= qr.pathmat[pim[k]];
        for j in [1..N] do
            for p in pi[j].path{pi[j].basis} do
                line:= Copy(top);
                for a in p do
                    line:= line * eMat[Position(qr.path[1], [a])];
                od;
                Add(matrix, line);
            od;
        od;
    od;


    return rec(pim:= pim, com:= com, radical:= radical, eMat:= eMat, simples:= simples, matrix:= matrix);
end;

ProjectiveResolutions:= function(qr)
    local   pr,  sz,  N,  new,  sim,  null,  p;

    pr:= [];
    sz:= SyzygiesQuiver(qr);
    for N in [1..Length(sz.prores)] do
        new:= [[N]];
        sim:= sz.prores[N].src;
        if sim <> [] then
            Add(new, sim);
            null:= NullspaceMat(sz.prores[N].mat);
            while null <> [] do
                p:= ProjectiveCover(qr, sim, null);
                sim:=  p.simples;
                Add(new, sim);
                null:= NullspaceMat(p.matrix);
            od;
        fi;
        Add(pr, new);
    od;

    return pr;
end;


#  even better:
#  with a much slimmer, even more efficient data structure.
#
##  The resulting object quiver has components:
##
##  path0
##  a list of streets of length 0, the vertices, or paths of length 0.
##
##  path1
##  a list of streets chosen to represent the edges.
##
##  pathmat
##  a matrix with one entry for each  homspace with components
##
##    path
##    the list of paths in this hom-space
##
##    mat
##    the list of delta-values, ie. images in the descent algebra
##
##    basis
##    a list of positions in path, selecting a preimage of a basis
##
##    map
##    how to express the image of a path in terms of the basis.
##
##
##  FIXME:  move this into streets.g???
##
DescentQuiver:= function(W)
    local   sourcePath,  targetPath,  deltaPath,  positionsProperty,
            pathsStreets,  line,  cleanUp,  path1,  path0,  s,  path,
            sh,  pathmat,  i,  where,  j,  t,  delete,  ij,  ppp,
            mat,  p,  kern,  pos;

#    # maybe we know it already.
#    if IsBound(W.quiver) then
#        return W.quiver;
#    fi;
#
    # a path is a sequence of streets, with adjacent ones multiplyable:
    # it has a source ...
    sourcePath:= function(path)
        return Call(path[1], "Source");
    end;

    # ... it has a target ...
    targetPath:= function(path)
        return Call(path[Length(path)], "Target");
    end;

    # ... and an associated delta-value.
    deltaPath:= function(path)
        local   p;
        p:= ProductStreetMatrixList(Map(path, "Matrix"));
        return rec(support:= p.target, mat:= Sum(p.mat));
    end;

    # how to find the positions of the elements with a given property.
    positionsProperty:= function(list, func)
        return Filtered([1..Length(list)], i-> func(list[i]));
    end;

    # how to generate all paths from a given set of streets.
    pathsStreets:= function(streets)
        local   edges,  paths,  old,  new,  a,  b;

        # ignore streets of length 0.
        edges:= positionsProperty(streets, x-> Call(x, "Length") > 0);

        paths:= [];
        old:= List(edges, x-> [x]);
        while old <> [] do
            Add(paths, old);
            new:= [];
            for a in old do
                for b in edges do
                    if targetPath(streets{a}) = sourcePath([streets[b]]) then
                        Add(new, Concatenation(a, [b]));
                    fi;
                od;
            od;
            old:= new;
        od;

        return paths;
    end;


    # how to find a std gen of a line
    line:= v-> v/v[PositionProperty(v, x-> x<>0)];


    # how to remove those streets which are in line with a product.
    cleanUp:= function(bbb)
        local   lin,  cls,  a,  delta,  l,  pos,  poss,  b,  p,  hom,
                grp,  i,  all,  aaa,  mat,  sha,  len,  sol,  wgt,  r,
                sub;

        # sort streets into classes.
        lin:= [];  cls:= [];
        for a in bbb do
            delta:= Call(a, "Delta");
            l:= [delta.support, line(delta.mat)];
            pos:= Position(lin, l);
            if pos = false then
                Add(lin, l);  Add(cls, [a]);
            else
                Add(cls[pos], a);
            fi;
        od;

        # use a transversal, form all products, find their positions.
        poss:= [];
        for a in cls do
            a:= Call(a[1], "Matrix");
            for b in cls do
                b:= Call(b[1], "Matrix");

                p:= ProductStreetMatrices(a, b);
                if p <> 0 then
                    delta:= rec(support:= p.target, mat:= Sum(p.mat));
                    if delta.mat <> 0 * delta.mat then
                        l:= [delta.support, line(delta.mat)];
                        AddSet(poss, Position(lin, l));
                    fi;
                fi;
            od;
        od;

        # now group into hom spaces.
        hom:= [];
        grp:= [];
        for i in Difference([1..Length(cls)], poss) do
            l:= [cls[i][1].source, cls[i][1].target];
            pos:= Position(hom, l);
            if pos = false then
                Add(hom, l);
                Add(grp, cls[i]);
            else
                Append(grp[pos], cls[i]);
            fi;
        od;

        # for each hom space, find a lightweight basis.
        all:= [];
        for aaa in grp do
            mat:= List(aaa, x-> Call(x, "Delta").mat);
            sha:= Map(aaa, "Shapes");
            len:= List(mat, x-> x*x);
            sol:= [];  wgt:= [];
            r:= RankMat(mat);
            for sub in Combinations([1..Length(mat)], r) do
                if RankMat(mat{sub}) = r and Size(Set(sha{sub})) = r then
                    Add(sol, sub);
                    Add(wgt, Sum(len{sub}));
                fi;
            od;
            pos:= Position(wgt, Minimum(wgt));

#            Append(all, aaa{sol[pos]});
            Append(all, aaa{Random(sol)});
        od;

        # return survivors
        return all;
    end;

    # split idempotent from nilpotent generators.
    path1:= [];  path0:= [];
    for s in BasicStreets(W) do
        if s.alley[2] = [] then
            Add(path0, s);
        else
            Add(path1, s);
        fi;
    od;
    InfoZigzag1("Starting with ", Length(path0) + Length(path1), " paths,\n");
    InfoZigzag1("of which ", Length(path0), " have length 0.\n");

    path1:= cleanUp(path1);
    InfoZigzag1("remaining edges: ", Length(path1), "\n");

    path:= pathsStreets(path1);

    # distribute paths over hom-spaces
    sh:= Shapes(W);
    pathmat:= List(sh, x-> List(sh, x-> rec(path:= [])));
    for i in [1..Length(pathmat)] do
        Add(pathmat[i][i].path, []);   # path0[i] is the idempotent in pathmat[i][i]
    od;
    where:= List(path, x-> []);
    for i in [1..Length(path)] do
        for j in [1..Length(path[i])] do
            s:= sourcePath(path1{path[i][j]});
            t:= targetPath(path1{path[i][j]});
            Add(pathmat[s][t].path, path[i][j]);
            AddSet(where[i], [s,t]);
        od;
    od;

    # calculate all relations
    delete:= [];
    for ij in where[1] do
        i:= ij[1];  j:=  ij[2];

        ppp:= pathmat[i][j].path;
        mat:= [];
        for p in ppp do
            if p = [] then
                Add(mat, Call(path0[j], "Delta").mat);
            else
                Add(mat, deltaPath(path1{p}).mat);
            fi;
        od;
        if mat = [] then
            kern:= [];
        else
            kern:= NullspaceMat(mat);
        fi;

        for line in kern do
            pos:= PositionProperty(line, x-> x <> 0);
            if Length(ppp[pos]) = 1 then
                Add(delete, ppp[pos][1]);
            fi;
        od;
    od;

    # trim edge set for ker delta to be admissible.
    if delete <> [] then

        InfoZigzag1("delete ", delete, "\n");
        path1:= path1{Difference([1..Length(path1)], delete)};
        path:= pathsStreets(path1);

        # redistribute paths over hom-spaces
        pathmat:= List(sh, x-> List(sh, x-> rec(path:= [])));
        for i in [1..Length(pathmat)] do
            Add(pathmat[i][i].path, []);   # path0[i] is the idempotent in pathmat[i][i]
        od;
        for i in [1..Length(path)] do
            for j in [1..Length(path[i])] do
                p:= path[i][j];
                Add(pathmat[sourcePath(path1{p})][targetPath(path1{p})].path, p);
            od;
        od;
    fi;


    # calculate all relations
    delete:= [];

    for i in [1..Length(sh)] do
        for j in [1..Length(sh)] do
            ppp:= pathmat[i][j].path;
            mat:= [];
            for p in ppp do
                if p = [] then
                    Add(mat, Call(path0[j], "Delta").mat);
                else
                    Add(mat, deltaPath(path1{p}).mat);
                fi;
            od;
            if mat = [] then
                kern:= [];
            else
                kern:= NullspaceMat(mat);
            fi;

            for line in kern do
                pos:= PositionProperty(line, x-> x <> 0);
                if Length(ppp[pos]) = 1 then
                    Add(delete, ppp[pos][1]);
                fi;
            od;


            pathmat[i][j].mat:= mat;
            pathmat[i][j].basis:= Difference([1..Length(mat)], List(kern, x-> Position(x, 1)));

            # express each path in terms of chosen basis.
            mat:= TransposedMat(Reversed(mat));
            TriangulizeMat(mat);
            mat:= Filtered(mat, x-> x <> 0*x);
            pathmat[i][j].map:= Reversed(TransposedMat(Reversed(mat)));
        od;
    od;

    if delete <> [] then
        Error("delete <> [] ", delete);
    fi;

    return Quiver(rec(name:= "DescentQuiver(W)",
               path0:= path0,
               path1:= path1,
               pathmat:= pathmat));
end;


#  how to find a basis of the i-th projective
BasisProjectiveQuiver:= function(q, i)
    return Concatenation(List(q.pathmat[i], x-> x.path{x.basis}));
end;


# given a list pims of indices, describing a projective module Q as
# a direct sum of pims, and a matrix map, describing a surjective linear map pi from Q
# onto some module M, find a new list pims and a new matrix, describing a minimal projective cover of the kernel of pi
NextProjectiveCover:= function(qr, pims, map)
    local   pathsUnderPath,  vectorUnderPath,  basis,  N,  iii,  lll,
            o,  com,  j,  d,  ind,  pim,  x,  fil,  space,  radical,
            e,  k,  new,  i,  mat,  ss,  matrix,  pi,  p;

    # compute a basis of the kernel
    basis:= NullspaceMat(map);
    if basis = [] then
        return 0;
    fi;

    N:= Length(qr.pathmat);  # nr of shapes.
    iii:= [1..Length(pims)];
    lll:= [1..Length(basis)];

    # set up some addresses
    # com[k][i] contains the indices of all paths from i to pims[k].
    o:= 0; # offset;
    com:= [];
    for j in pims do
        d:= List(qr.pathmat[j], x-> Length(x.basis));
        Add(com, o + SetComposition(d));
        o:= o + Sum(d);
    od;

    # ind[i] contains the indices of all paths coming from i.
    ind:= List([1..N], i-> Concatenation(com{iii}[i]));

    # assert that each basis elt lies in a homogeneous component.
    pim:= [];
    for x in basis do
        fil:= Filtered([1..N], i-> x{ind[i]} <> 0 * ind[i]);
        if Length(fil) <> 1 then
            Error("basis elt does not lie in a homogeneous component");
        else
            Add(pim, fil[1]);
        fi;
    od;

    # how to compute the effect of a path a (from j to k) on pim i
    # as a matrix ....
    pathsUnderPath:= function(i, a)
        local   pi,  j,  k,  mat,  p;

        pi:= qr.pathmat[i];

        j:= Call(qr.path1[a[1]], "Source");
        k:= Call(qr.path1[a[Length(a)]], "Target");

        mat:= [];  # the matrix of e on a small space
        for p in pi[j].path{pi[j].basis} do
            Add(mat, pi[k].map[Position(pi[k].path, Concatenation(p, a))]);
        od;

        return mat;
    end;

    vectorUnderPath:= function(b, a)
        local   j,  k,  new,  i,  mat;

        if a = [] then
            return b;
        fi;

        j:= Call(qr.path1[a[1]], "Source");
        k:= Call(qr.path1[a[Length(a)]], "Target");

        new:= 0 * b;
        for i in iii do
            mat:= pathsUnderPath(pims[i], a);
            if mat <> [] then
                new{com[i][k]}:= b{com[i][j]} * mat;
            fi;
        od;

        return new;
    end;


    # compute radical of the module: postmultiply edges
    space:= RowSpace(Rationals, basis);

    radical:= [];
    for e in [1..Length(qr.path1)] do
        j:= Call(qr.path1[e], "Source");
        k:= Call(qr.path1[e], "Target");
        new:= 0*basis;
        for i in iii do
            mat:= pathsUnderPath(pims[i], [e]);
            if mat <> [] then
                new{lll}{com[i][k]}:= basis{lll}{com[i][j]} * mat;
            fi;
        od;
        UniteSet(radical, new);

    od;

    # assert that a subset of the original basis is a basis of the quotient.
    ss:= List(Basis(space/radical).vectors, x-> Position(basis, x));

    # compute new matrix
    matrix:= [];
    for i in ss do
        pi:= qr.pathmat[pim[i]];
        for j in [1..N] do
            for p in pi[j].path{pi[j].basis} do
                Add(matrix, vectorUnderPath(basis[i], p));
            od;
        od;
    od;

    return rec(pims:= pim{ss}, map:= matrix);
end;



# compute a minimal projective resolution of the i-th simple module.
ProjectiveResolution:= function(qr, i)
    local   pi,  n,  a,  p,  res,  pims,  map;

    pi:= qr.pathmat[i];
    n:= Sum(pi, x-> Length(x.basis));
    a:= 0*[1..n];  a[n]:= 1;
    p:= rec(pims:= [i], map:= TransposedMat([a]));

    res:= [];

    repeat
        pims:= p.pims;  map:= p.map;
        Add(res, p);
        p:= NextProjectiveCover(qr, pims, map);
    until p = 0;

    return res;
end;


#############################################################################
##
##  RelationsDescentQuiver
##
##
##
RelationsDescentQuiver:= function(q)
    local   N,  i,  j,  rels,  pr,  basi,  pos,  path,  r,  basr,
            edge,  rel,  p;

    N:= Length(q.pathmat);

    # do we really want to store them?
    for i in [1..N] do
        for j in [1..N] do
            q.pathmat[i][j].relation:= [];
        od;
    od;
    rels:= [];

    for i in [1..N] do
        pr:= ProjectiveResolution(q, i);
        if Length(pr) > 2 then

            basi:= Concatenation(List(q.pathmat[i], x-> x.path{x.basis}));

            # identify paths.
            pos:= 0;
            path:= [];
            for r in pr[2].pims do
                basr:= Concatenation(List(q.pathmat[r], x-> x.path{x.basis}));
                pos:= pos + Length(basr);
                edge:= basi[Position(pr[2].map[pos], 1)];
                Append(path, List(basr, x-> Concatenation(edge, x)));
            od;

            # find relations.
            pos:= 0;
            for r in pr[3].pims do
                pos:= pos + Sum(q.pathmat[r], x-> Length(x.basis));
                # now: pr[3].map[pos]  is the coeff vec of the relation, need to recover basis.
                rel:= [];
                for p in q.pathmat[i][r].path do
                    j:= Position(path, p);
                    if j = false then
                        Add(rel, 0);
                    else
                        Add(rel, pr[3].map[pos][j]);
                    fi;
                od;
                Add(q.pathmat[i][r].relation, rel);
                Add(rels, [i, r, rel]);
            od;
        fi;
    od;

    return rels;
end;

#############################################################################
##
#F  DisplayQuiver( <quiver> ) . . . . . . . . . . . . . . . . . . . . .  print.
##
##  <#GAPDoc Label="DisplayQuiver">
##  <ManSection>
##  <Func Name="DisplayQuiver" Arg="quiver"/>
##  <Returns>
##    nothing.
##  </Returns>
##  <Description>
##    This function produces a formatted description of a quiver as returned
##    by the function <Ref Func="QuiverRelations"/>.
##  <Example>
##  gap> quiver:= QuiverRelations(DescentAlgebra(CoxeterGroup("A", 5)));;
##  gap> DisplayQuiver(quiver);
##  A5    1 - 2 - 3 - 4 - 5
##
##  Vertices:
##  1. \emptyset []
##  2. A_{1} [1]
##  3. A_{11} [13]
##  4. A_{2} [12]
##  5. A_{111} [135]
##  6. A_{21} [124]
##  7. A_{3} [123]
##  8. A_{22} [1245]
##  9. A_{31} [1235]
##  10. A_{4} [1234]
##  11. A_{5} [12345]
##
##  Edges:
##  2 --> 4. [12;1]
##  3 --> 6. [124;1]
##  4 --> 7. [123;1]
##  6 --> 10. [1234;2]
##  6 --> 9. [1235;1]
##  6 --> 8. [1245;1]
##  7 --> 10. [1234;1]
##  9 --> 11. [12345;2]
##  10 --> 11. [12345;1]
##
##  Relations:
##  +1(11---9---6---3) +-1(11---10---6---3) [12345;2][1235;1][124;1], [12345;1][1234;2][124;1],
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
DisplayQuiver0:= function(qr)
    local   short,  shortalley,  name,  vertex,  i,  gens,  e,  mat,
            r,  p;

    short:= function(set)
        local   text,  s;

        text:= "";
        for s in set do
            Append(text, String(s));
        od;
        IsString(text);
        return text;
    end;

    shortalley:= function(a)
        local   text;
        text:= "[";
        Append(text, short(a[1]));
        Append(text, ";");
        Append(text, short(a[2]));
        Append(text, "]");
        return text;
    end;

    vertex:= qr.path0;
    name:= NamesShapes(Shapes(vertex[1].W));
    PrintDiagram(vertex[1].W);

    Print("\nVertices:\n");
    for i in [1..Length(vertex)] do
        Print(i, ". ", name[i], " [", short(vertex[i].alley[1]), "]\n");
    od;

    if qr.path = [] then return; fi;

    gens:= List(qr.path[1], x-> x[1]);
    Print("\nEdges:\n");
    for e in gens do
        mat:= Call(e, "Matrix");
        Print(mat.target, " --> ", mat.source, ". ",
              shortalley(e.alley), "\n");
    od;

    Print("\nRelations:\n");
    for r in qr.relations do
        if Difference(Union(r.paths), gens) = [] then
            i:= 0;
            for p in r.paths do
                i:= i + 1;
                Print("+", r.coeffs[i], "(");
                for e in p do
                    mat:= Call(e, "Matrix");
                    Print(mat.source, "---");
                od;
                Print(mat.target, ") \c");
            od;
            for p in r.paths do
                for e in p do
                    Print(shortalley(e.alley), "\c");
                od;
                Print(", ");
            od;
            Print("\n");
        fi;
    od;

end;

DisplayQuiver1:= function(qr)
    local   short,  shortalley,  name,  vertex,  i,  gens,  e,  mat,
            r,  p;

    short:= function(set)
        local   text,  s;

        text:= "";
        for s in set do
            Append(text, String(s));
        od;
        IsString(text);
        return text;
    end;

    shortalley:= function(a)
        local   text;
        text:= "[";
        Append(text, short(a[1]));
        Append(text, ";");
        Append(text, short(a[2]));
        Append(text, "]");
        return text;
    end;

    vertex:= qr.path0;
    name:= NamesShapes(Shapes(vertex[1].W));
    PrintDiagram(vertex[1].W);

    Print("\nVertices:\n");
    for i in [1..Length(vertex)] do
        Print(i, ". ", name[i], " [", short(vertex[i].alley[1]), "]\n");
    od;

    if qr.path = [] then return; fi;

    gens:= List(qr.path[1], x-> x[1]);
    Print("\nEdges:\n");
    for e in gens do
        mat:= Call(e, "Matrix");
        Print(mat.target, " --> ", mat.source, ". ",
              shortalley(e.alley), "\n");
    od;

    Print("\nRelations:\n");
    for r in qr.relations do
        i:= 0;
        for p in r.paths do
            i:= i + 1;
            Print("+", r.coeffs[i], "(");
            for e in qr.path[p[1]][p[2]] do
                mat:= Call(e, "Matrix");
                Print(mat.source, "---");
            od;
            Print(mat.target, ") \c");
        od;
        for p in r.paths do
            for e in qr.path[p[1]][p[2]] do
                Print(shortalley(e.alley), "\c");
            od;
            Print(", ");
        od;
        Print("\n");
    od;

end;

DisplayQuiver:= DisplayQuiver1;

#############################################################################
##
##  The Cartan Mat, decomposed along the radical series.
##
DimensionsMatrix0:= function(qr)
    local   W,  l,  dim,  k,  mat,  p,  i,  j;

    W:= qr.path0[1].W;
    l:= Length(Shapes(W));
    dim:= [];
    for k in [1..Length(qr.path)] do
        mat:= NullMat(l, l);
        for p in qr.path[k] do
            i:= Call(p[1], "Matrix").source;
            j:= Call(p[Length(p)], "Matrix").target;
            mat[i][j]:= mat[i][j] + 1;
        od;
        dim[k]:= mat;
    od;

    return dim;
end;

DimensionsMatrix1:= function(qr)
    local   l,  dim,  i,  j,  m,  k,  a;

    l:= Length(qr.pathmat);
    dim:= List([1..Length(qr.path)], k-> NullMat(l, l));

    for i in [1..l] do
        for j in [1..l] do
            m:= qr.pathmat[i][j];
            for k in m.basis do
                a:= m.adr[k];
                if a[1] > 0 then
                    dim[a[1]][i][j]:= dim[a[1]][i][j] + 1;
                fi;
            od;
        od;
    od;

    return dim;
end;

DimensionsMatrix:= DimensionsMatrix1;


#############################################################################
CartanMatQuiver0:= function(qr)
    local   car;

    car:= Sum(DimensionsMatrix0(qr));
    return car + car^0;
end;

CartanMatQuiver1:= function(qr)
    return List(qr.pathmat, x-> List(x, y-> Length(y.basis)));
end;

CartanMatQuiver:= CartanMatQuiver1;


QCartanMatQuiver0:= function(qr, q)
    local   dim,  car;

    dim:= DimensionsMatrix0(qr);
    car:= Sum([1..Length(dim)], i-> q^i * dim[i]);
    return car + car^0;
end;

QCartanMatQuiver1:= function(qr, q)
    return q^0 *
           List(qr.pathmat, x-> List(x, y-> Sum(y.adr{y.basis}, x-> q^x[1])));
end;

QCartanMatQuiver:= QCartanMatQuiver1;


##
##  how to typeset a square matrix with named rows and cols.
LaTeXMatNames:= function(mat, names, blocks, list)
    local   bb,  l,  i,  j;

    blocks:= Filtered(List(blocks, x-> Intersection(x, list)), y-> y <> []);
    bb:= List(blocks, x-> x[1]); # the block beginners.
    l:= Length(mat);  # the common length of *all* arguments

    # print preamble
    Print("\\begin{array}{r|\c");
    for i in list do
        if i in bb then
            Print("|");
        fi;
        Print("c");
    od;
    Print("|}\n");

    # print rows
    for i in list do
        if i in bb then
            Print("\\hline\n");
        fi;

        Print(names[i]);
        for j in list do
            Print("&\c");
            if mat[i][j] = 0*mat[i][j] then
                Print(".");
            else
                Print(String(mat[i][j]));
            fi;
        od;
        Print("\\\\\n");
    od;

    # print closing
    Print("\\hline\n\\end{array}\n");
end;

# the kernel of a list is the equvalence relation 'have the same value'
#FIXME: move into more appropriate file ...
KernelList:= function(list)
    local   vals,  i,  v;
    vals:= rec();
    for i in [1..Length(list)] do
        v:= list[i];
        if IsBound(vals.(v)) then
            Add(vals.(v), i);
        else
            vals.(v):= [i];
        fi;
    od;
    return Set(List(RecFields(vals), v-> vals.(v)));
end;


LaTeXQCartan:= function(W, file)
    local   D,  qr,  car,  q,  qar,  sh,  nam,  list,  blocks;

    D:= DescentAlgebra(W);
    qr:= QuiverRelations(D);
    car:= CartanMatQuiver(qr);
    q:= X(Rationals); q.name:= "q";
    qar:= QCartanMatQuiver(qr, q);
    sh:= Shapes(W);
    nam:= NamesShapes(sh);
    list:= [1..Length(sh)];
    blocks:= KernelList(List(sh, Rank));

    PrintTo(file, LaTeXMatNames(qar, nam, blocks, list));
    AppendTo(file, LaTeXMatNames(qar^-1, nam, blocks, list));
end;


##  given a Cartan matrix, determine the blocks (as an equivalence on the
##  row and column indices
BlocksCartan:= function(car)
    local   n,  equ,  i,  j,  new,  k;

    n:= Length(car);
    equ:= List([1..n], i-> [i]);
    for i in [1..n] do
        for j in [1..n] do
            if car[i][j] <> 0*car[i][j] and not i in equ[j] then
                new:= Union(equ[i], equ[j]);
                for k in new do
                    equ[k]:= new;
                od;
            fi;
        od;
    od;
    return Set(equ);
end;


#############################################################################
##
##   Conjecture.  A path in the quiver is a union of streets.  If two paths
##   intersect they are the same.  The quiver algebra is a subalgebra of
##   the streets algebra.
##
##   This function answers the question:
##   How many streets does a hom space in the quiver algebra consist of?
##
##   Input: a DescentQuiver(W)
##
MatNrStreetsQuiver:= function(quiver)
    local   l,  mat,  i,  j,  streets,  p,  m;

    l:= Length(quiver.pathmat);

    mat:= IdentityMat(l);
    for i in [1..l] do
        for j in [1..i-1] do
            streets:= [];
            for p in quiver.pathmat[i][j].path do
                Append(streets, ProductStreets(quiver.path1{p}));
            od;
            m:= Length(streets);
            if Size(Set(streets)) = m then
                mat[i][j]:= m;
            else
                Error("this conjecture is false: path do overlap!");
            fi;
        od;
    od;

    return mat;
end;

#  q-version, sort by path length
QMatNrStreetsQuiver:= function(quiver, q)
    local   l,  mat,  i,  j,  streets,  p,  m;

    l:= Length(quiver.pathmat);

    mat:= q^0 * IdentityMat(l);
    for i in [1..l] do
        for j in [1..i-1] do
            streets:= [];
            for p in quiver.pathmat[i][j].path do
                Append(streets, ProductStreets(quiver.path1{p}));
            od;
            m:= Length(streets);
            if m > 0 then
                mat[i][j]:= q^Length(p) * m;
            fi;
        od;
    od;

    return mat;
end;


MatNrPathsQuiver:= function(quiver)
    local   l,  mat,  i,  j;

    l:= Length(quiver.pathmat);

    mat:= IdentityMat(l);
    for i in [1..l] do
        for j in [1..i-1] do
            mat[i][j]:= Length(quiver.pathmat[i][j].path);
        od;
    od;

    return mat;
end;

#  q-version, sort by path length
QMatNrPathsQuiver:= function(quiver, q)
    local   l,  mat,  i,  j,  m;

    l:= Length(quiver.pathmat);

    mat:= q^0 * IdentityMat(l);
    for i in [1..l] do
        for j in [1..i-1] do
            m:= Length(quiver.pathmat[i][j].path);
            if m > 0 then
                mat[i][j]:= q^Length(quiver.pathmat[i][j].path[1]) * m;
            fi;
        od;
    od;

    return mat;
end;

#############################################################################
##
##  report on all redundant relations.
##
##  a redundant relation between s and t is an essential relation
##  between i and j, extended by a path a from s to i on the left,
##  and a path b from j to t on the right, in all possible ways.
##
RedundantRelations:= function(quiver, s, t)
    local   rel,  inf,  i,  a,  j,  b,  poss,  r,  new;

    rel:= [];
    inf:= [];

    for i in [s..t] do
        for a in quiver.pathmat[i][s].path do
            for j in [i..t]  do
                for b in quiver.pathmat[t][j].path do
                    poss:= List(quiver.pathmat[j][i].path,
                                x-> Position(quiver.pathmat[t][s].path, Concatenation(b, x, a)));
                    for r in quiver.pathmat[j][i].relation do
                        new:= List(quiver.pathmat[t][s].path, x-> 0);
                        new{poss}:= r;
                        Add(rel, new);
                        Add(inf, [i, j, a, b]);
                        Print(".\c");
                    od;
                    Print(poss, "\n");
                od;
            od;
        od;
    od;

    return rec(rel:= rel, inf:= inf);
end;




#############################################################################
##
#E  Emacs  . . . . . . . . . . . . . . . . . . . . . . local emacs variables.
##
##  Local Variables:
##  mode:               gap
##  outline-regexp:     "#F\\|#V\\|#E\\|#A"
##  fill-column:        77
##  fill-prefix:        "##  "
##  End:
##
