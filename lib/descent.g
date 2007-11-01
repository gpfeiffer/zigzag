#############################################################################
##
#A  $Id: descent.g,v 1.41 2007/11/01 12:00:10 goetz Exp $
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
#
# A helper function
#
DiagonalMat:= function(diag)
    local mat, i, n;
    n:= Length(diag);
    mat:= IdentityMat(n);
    for i in [1..n] do
        mat[i][i]:= diag[i];
    od;
    return mat;
end;


#############################################################################
#
#  intersections of Descent and Conjugacy classes.
#  there is probably a more efficient way to do this ...
##  
##  Application:  to calculate the symmetric matrix  \theta(x_J)(x_K)
##  
##  inc:= IncidenceMatShapes(Shapes(W));
##  zs:= SizesDescentConjugacyClasses(W);
##  yct:= YCharacters(W);
##  mat:= inc * yct * TransposedMat(inc * sz);
##  
#
SizesDescentConjugacyClasses:= function(W)
    local   subsets,  cc,  sec,  csp,  per,  J,  row,  des,  w,  p,  
            class;
    
    if IsBound(W.sizesDescentConjugacyClasses) then
        return W.sizesDescentConjugacyClasses;
    fi;
    
    subsets:= SubsetsShapes(Shapes(W));
    cc:= ConjugacyClasses(W);
    sec:= [];
    
    csp:= List(cc, x-> CycleStructurePerm(Representative(x)));
    per:= Sortex(csp);
    
    if IsSet(csp) then  # classes are distinguished by cycle structure!
        # now can identify class of w by
        #   PositionSorted(csp, CycleStructurePerm(w))/per
        
       for J in subsets do
           row:= List(cc, x-> 0);
           des:= Iterator(DescentClass(W, J));
           while des.hasNext() do
               w:= des.next();
               p:= PositionSorted(csp, CycleStructurePerm(w))/per;
               row[p]:= row[p] + 1;
           od;
           Add(sec, row);
           Print(".\c");
       od;
       Print("\n");
   else
       for J in subsets do
           row:= List(cc, x-> 0);
           des:= Iterator(DescentClass(W, J));
           while des.hasNext() do
               w:= des.next();
               p:= PositionProperty(cc, x-> w in x);
               row[p]:= row[p] + 1;
           od;
           Add(sec, row);
           Print(",\c");
       od;
       Print("\n");
   fi;
   
   W.sizesDescentConjugacyClasses:= sec;
   return sec;
end;
    
#############################################################################
##
# here is the procedure to calculate the Lie characters.
##
##  
ECharacters:= function(W)
    local   sec,  nu,  ee,  a,  lll,  l,  dia;
    
    sec:= SizesDescentConjugacyClasses(W);
    nu:= Call(DescentAlgebra(W), "Mu")^-1;
    ee:= [];  a:= 0;  lll:= List(Shapes(W), Size);
    for l in lll do
        Add(ee, Sum(nu{a+[1..l]}));
        a:= a + l;
    od;

    dia:= DiagonalMat(List(ConjugacyClasses(W), x-> Size(W)/Size(x)));
    return ee * IncidenceMatShapes(Shapes(W)) * sec * dia;
end;

##??? This should be a binary relation ...
#############################################################################
##
##  For type A:  The partitions quiver.
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


##  the major index of a permutation:
##
MajorIndex:= function(perm)
    local   maj,  i;
    
    # trivial case first.
    if perm = () then return 0; fi;
    
    maj:= 0;
    for i in [1..LargestMovedPointPerm(perm)] do
        if i^perm > (i+1)^perm then
            maj:= maj + i;
        fi;
    od;
    
    return maj;
end;


##  Helper.  How to turn a  composition of n into a set composition of [1..n]
SetComposition:= function(l)
    return List([1..Length(l)], i-> Sum(l{[1..i-1]}) + [1..l[i]]);
end;


##  Helper.  Test for not 0.
IsNonZero:= m -> m <> 0*m;


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
