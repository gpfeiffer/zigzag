#############################################################################
##
#A  $Id: descent.g,v 1.67 2009/06/15 17:44:32 goetz Exp $
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2001-2007, Götz Pfeiffer
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
        if arg[2] = "x" then 
            return function(arg)
                new:= 0 * [1..Dimension(self)];
                new[self.pos[self.encodeSet(arg)]]:= 1;
                return DescentElt(self, "x", new);
            end;
        else
            Error("not yet implemented");
        fi;
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
    local   W,  n,  subsets,  complmt,  xxx,  d,  m,  c,  e,  p,  WJ;
    
    if IsBound(D.rightRegularX) then
        return D.rightRegularX;
    fi;
    
    W:= D.W;
    n:= W.semisimpleRank;
    subsets:= SubsetsShapes(Shapes(W));
    complmt:= List(subsets, x-> Position(subsets, Difference([1..n], x)));
    xxx:= [];
    for d in subsets do
        if d = [] then
            m:= MaximalAJKL(W, 0);
        else
            c:= Difference([1..n], d);
            e:= Union(c, [d[Length(d)]]);
            p:= Position(subsets, Difference([1..n], e));
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
#F  ECharacters( <D> )  . . . . . . . . . . . . . . . . . . . . . characters.
##
##  <#GAPDoc Label="ECharacters">
##  <ManSection>
##  <Func Name="ECharacters" Arg="D"/>
##  <Returns>
##    the list of characters corresponding to the primitive idempotents of
##    <A>D</A>.
##  </Returns>
##  <Description>
##    Each idempotent <M>e</M> in the group algebra <M>KW</M> of a finite
##    Coxeter <M>W</M> generates a submodule <M>eKW</M> of the regular
##    module <M>KW</M>.  This function computes the characters of the
##    modules generated in this way by the primitive idempotents of the
##    descent algebra of <M>W</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;                                                
##  gap> ech:= ECharacters(DescentAlgebra(W));
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
##  >            centralizer:= false));
##  W( A5 )
##  
##        2      4     4    4   4    1   1  1   3  3  .  1
##        3      2     1    .   1    2   1  2   .  .  .  1
##        5      1     .    .   .    .   .  .   .  .  1  .
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
ECharacters:= function(D)
    local   diagonalMat,  sec,  nu,  ee,  a,  lll,  l,  dia;
    
    # how to make a diagonal matrix.
    diagonalMat:= function(diag)
        local mat, i, n;
        n:= Length(diag);
        mat:= IdentityMat(n);
        for i in [1..n] do
            mat[i][i]:= diag[i];
        od;
        return mat;
    end;

    sec:= SizesDescentConjugacyClasses(D.W);
    nu:= Call(D, "Mu")^-1;
    ee:= [];  a:= 0;  lll:= List(Shapes(D.W), Size);
    for l in lll do
        Add(ee, Sum(nu{a+[1..l]}));
        a:= a + l;
    od;

    dia:= diagonalMat(List(ConjugacyClasses(D.W), x-> Size(D.W)/Size(x)));
    return ee * IncidenceMatShapes(Shapes(D.W)) * sec * dia;
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
##    Key="pfeiffer-quiver"/>.  The result is a directed graph which has the
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
        p:= ProductStreetMatrixList(List(path, x-> Call(x, "Matrix")));
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



# alternatively:

QuiverRelations1:= function(D)
    local   sourcePath,  targetPath,  deltaPath,  eee,  path1,  path0,  
            a,  path,  sh,  pathmat,  i,  j,  delete,  relations,  
            adr,  mat,  kern,  line,  pos,  e,  k,  map,  p,  rel,  
            cons,  space;
    
#    # maybe we know it already.
#    if IsBound(D.quiverRelations) then
#        return D.quiverRelations;
#    fi;
#        
    # a path is a sequence of streets, with adjacent ones multiplyable.
    sourcePath:= function(path)
        return Call(path[1], "Source");
    end;
    
    targetPath:= function(path)
        return Call(path[Length(path)], "Target");
    end;
    
    deltaPath:= function(path)
        local   p;
        p:= ProductStreetMatrixList(List(path, x-> Call(x, "Matrix")));
        return rec(support:= p.target, mat:= Sum(p.mat));
    end;
    
    eee:= BasicStreets(D.W);
    
    # split idempotent from nilpotent generators.
    path1:= [];  path0:= []; 
    for a in eee do
        if a.alley[2] = [] then
            Add(path0, a);
        else
            Add(path1, a);
        fi;
    od;
    InfoZigzag1("of which ", Length(path0), " have length 0.\n");
        
    repeat 
        path:= PathsStreets(path1, W.semisimpleRank);
        sh:= Shapes(W);
        
        # distribute paths over hom-spaces
        pathmat:= List(sh, x-> List(sh, x-> rec(path:= [], adr:= [])));
        for i in [1..Length(path)] do
            for j in [1..Length(path[i])] do
                Add(pathmat[sourcePath(path[i][j])][targetPath(path[i][j])].adr, [i,j]
                    );
                Add(pathmat[sourcePath(path[i][j])][targetPath(path[i][j])].path, path[i][j]
                    );
            od;
        od;
        
        # calculate all relations
        delete:= List(path, x-> []);
        relations:= [];
        
        for i in [1..Length(sh)] do
            for j in [1..Length(sh)] do
                adr:= pathmat[i][j].adr;
                mat:= [];
                for a in adr do
                    Add(mat, deltaPath(path[a[1]][a[2]]).mat);
                od;
                if mat = [] then
                    kern:= [];
                else
                    kern:= NullspaceMat(mat);
                fi;
                
                for line in kern do
                    pos:= Filtered([1..Length(line)], i-> line[i] <> 0);
                    Add(relations, rec(paths:= adr{pos}, coeffs:= line{pos}));
                    Add(delete[adr[pos[1]][1]], adr[pos[1]][2]);
                od;
                
                
                pathmat[i][j].mat:= mat;
                pathmat[i][j].kern:= kern;
            od;
        od;
        
#        InfoZigzag1(delete, "\n");
        
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
            for rel in pathmat[i][j].kern do
                cons:= List(pathmat[i][k].path, x-> 0);
                cons{map}:= rel;
                Add(pathmat[i][k].cons, cons);
            od;
        od;
        
        
        # premultiply edge and make map from (k, i) to (j, i).
        for i in [1..Length(sh)] do
            map:= [];
            for p in pathmat[k][i].path do
                Add(map, Position(pathmat[j][i].path, Concatenation(e, p)));
            od;
            for rel in pathmat[k][i].kern do
                cons:= List(pathmat[j][i].path, x-> 0);
                cons{map}:= rel;
                Add(pathmat[j][i].cons, cons);
            od;
        od;
        
        
    od;
    
    # find essential relations.
    for i in [1..Length(sh)] do
        for j in [1..Length(sh)] do
            if pathmat[i][j].cons = [] then
                pathmat[i][j].rela:= pathmat[i][j].kern;
            else
                space:= RowSpace(Rationals, pathmat[i][j].kern);
                space:= space/Subspace(space, pathmat[i][j].cons);
                pathmat[i][j].rela:= Basis(space).vectors;
            fi;
        od;
    od;
        
    # calculate all relations
    delete:= List(path, x-> []);
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
        
        
    return rec(path0:= path0, path:= path, pathmat:= pathmat, delete:= delete, relations:= relations);
end;

QuiverRelations:= QuiverRelations0;


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
DisplayQuiver:= function(qr)
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
    PrintDynkinDiagram(vertex[1].W);
    
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
    PrintDynkinDiagram(vertex[1].W);
    
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

#############################################################################
##
##  The Cartan Mat, decomposed along the radical series.
##
DimensionsMatrix:= function(qr)
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

#############################################################################
CartanMatQuiver:= function(qr)
    local   car;
    
    car:= Sum(DimensionsMatrix(qr));
    return car + car^0;
end;
  
  
QCartanMatQuiver:= function(qr, q)
    local   dim,  car;
    
    dim:= DimensionsMatrix(qr);
    car:= Sum([1..Length(dim)], i-> q^i * dim[i]);
    return car + car^0;
end;


#############################################################################
RelationsMatrix:= function(qr)
    local   capp,  dim,  inc,  pth,  car,  sum,  mat,  rel,  cap;

    # return a matrix cap of the same dimension as mat, such that cap + mat >=0.
    capp:= function(mat)
        local   cap,  row,  new,  a;
        cap:= [];
        for row in mat do
            new:= [];
            for a in row do
                if a < 0 then
                    Add(new, -a);
                else
                    Add(new, 0);
                fi;
            od;
            Add(cap, new);
        od;
        return cap;
    end;



# output:
#    a list mat such that
#
#      car = \sum_i inc^i - rel[i]
#
#    where 
#
#      rel[0] = 0 (and rel[1] = 0)
#
#    and
#
#      rel[i] = inc * rel[i-1] + rel[i-1] * inc + mat[i]
#
    dim:= DimensionsMatrix(qr);
    inc:= dim[1];
    pth:= inc^0;
    car:= Sum(dim) + pth;
    sum:= pth;
    mat:= [];
    rel:= 0 * pth;
    while pth <> 0 * pth do
        pth:= pth * inc;
        sum:= sum + pth;
        rel:= inc * rel + rel + rel * inc;
        cap:= capp(car - sum + rel);
        Add(mat, cap);
        rel:= rel + cap;
    od;
    return mat;
end;


#############################################################################
RelationsMatrix2:= function(qr)
    local   capp,  dim,  inc,  mat,  rel,  i,  cap;

    # return a matrix cap of the same dimension as mat, such that cap + mat >=0.
    capp:= function(mat)
        local   cap,  row,  new,  a;
        cap:= [];
        for row in mat do
            new:= [];
            for a in row do
                if a < 0 then
                    Add(new, -a);
                else
                    Add(new, 0);
                fi;
            od;
            Add(cap, new);
        od;
        return cap;
    end;



# output:
#    a list mat such that
#
#      car = \sum_i inc^i - rel[i]
#
#    where 
#
#      rel[0] = 0 (and rel[1] = 0)
#
#    and
#
#      rel[i] = inc * rel[i-1] + rel[i-1] * inc + mat[i]
#
    dim:= DimensionsMatrix(qr);
    inc:= dim[1];
    mat:= [];
    rel:= 0 * inc;
    for i in [1..Length(dim)] do
        rel:= inc * rel + rel * inc;
        cap:= capp(dim[i] - inc^i + rel);
        Add(mat, cap);
        rel:= rel + cap;
    od;
    return mat;
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

##  given a q-Cartan matrix, determine the minimal projective resolutions
ProjectiveResolutions:= function(D)
    local   q,  qr,  car;

    q:= X(Rationals);
    qr:= QuiverRelations(D);
    car:= QCartanMatQuiver(qr, q);
    return List(car^-1, x-> List(x, y-> Value(y, -q)));
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
