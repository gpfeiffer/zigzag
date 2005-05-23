#############################################################################
##
#A  zigzag.g                      Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2004, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: descent.g,v 1.19 2005/05/23 17:00:51 goetz Exp $
##
##  This file contains the basic routines for descent algebras.
##
RequirePackage("chevie");


#############################################################################
##  
##  TODO:
##
##  * Avoid the expansion of RightRegularX into full matrices ...
##

#############################################################################
##
#F  InfoZigzag? . . . . . . . . . . . . . . . . . . . . . . . info functions.
##
if not IsBound(InfoZigzag1) then InfoZigzag1:= Ignore; fi;
if not IsBound(InfoZigzag2) then InfoZigzag2:= Ignore; fi;

##  create descent algebras as a subclass of Algebra -- need to provide
##  special functions later ...
##  
DescentAlgebraOps:= OperationsRecord("DescentAlgebraOps", AlgebraOps);

#############################################################################
##
#F  DescentAlgebra( <W> ) . . . . . . . . . . . . . . . . . . .  constructor.
##  
##  returns an object that represents the descent algebra of the Coxeter group
##  <W>.
##  
DescentAlgebra:= function(W)
    local   this;
    this:= rec(W:= W, operations:= DescentAlgebraOps);
    
    this.GetAJKL:= function(J, K, L)
        local   xxx,  l;
        if L > K then return 0; fi;
        xxx:= RightRegularX(this);
        l:= Position(xxx[K].pos[J], L);
        if l = false then return 0; fi;
        return xxx[K].val[J][l];
    end;

    return this;
end;

#############################################################################
##  
#F  Print( <descalg> )  
##  
DescentAlgebraOps.Print:= function(this)
    Print("DescentAlgebra( ", this.W, " )");
end;

#############################################################################
##  
##  
##  
DescentAlgebraOps.Dimension:= function(this)
    return 2^this.W.semisimpleRank;
end;


#############################################################################
##  
#F  DescentAlgebraOps.MuNu( <D> )
##  
##  The idempotents from BBHT.  
##  the rows of nu express the quasi-idempotents e_J in terms of the x_J.
##  <init> could be any list of 2^n entries > 0.
##    
DescentAlgebraOps.MuNu:= function(D)
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

    return rec(mu:= mu, nu:= mu^-1);
end;
    
#############################################################################
#
#  turn $a \in \Sigma(W)$ into the character $\theta(a)$.
#
#  elt must be a matrix in the X basis.
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
# Given a list of lists of rows of non-neg ints
# find the minimal possible value for every position in every row.
SlowFoundation:= function(lis)
    local   f, m, i, l;
    
    f:= [];
    for l in lis do
        m:= [];
        for i in [1..Length(l[1])] do
            m[i]:= Minimum(l{[1..Length(l)]}[i]);
            l{[1..Length(l)]}[i]:= l{[1..Length(l)]}[i] - m[i];
        od;
        Add(f, m);
    od;
    
    return f;
end;


# Given a list of lists of rows of non-neg ints and a sum
# select a row from each of the lists
# such that the sum of the rows equals the given sum.
# (There must be a standard way of doing this efficiently,
# but I don't find that now ... '
SlowI:= 0;  SlowLog:= [];
SlowCombine:= function(list, sum, index)
    local   l, i, sols,  r,  small, pos, min, found, d;
    
    # keep me informed.
#    SlowI:= SlowI+1;
#    if SlowI mod 100000 = 0 then
#        SlowI:= 0;
#        Print(list, "\n", sum, "\n");
#        Error("return; to return");
#    fi;
    
    # trivial case first ...
    if list = [] then
        if Sum(sum) = 0 then
            Print("+\n");
            return [[]]; 
        else
            return [];
        fi;
    fi;
    
    list:= Copy(list);    
    
    # check that every given row fits into the sum ...
    for i in [1..Length(list)] do
        list[i]:= Filtered(list[i], x-> Minimum(sum - x) >= 0);
        
        # return if a list then is empty ...
        if list[i] = [] then 
            return []; 
        fi;
    od;
    
    # extract minimal values.
    found:= SlowFoundation(list);
    sum:= sum - Sum(found);
    if Minimum(sum) < 0 then
        return [];
    fi;
        
    # pick row from the shortest list ...
    min:= Length(list[1]);  pos:= 1;
    for i in [2..Length(list)] do
        if Length(list[i]) < min then
            min:= Length(list[i]);  pos:= i;
        fi;
    od;
#    if min = 1 then Print("!\c"); fi;
    
    Print(SlowLog, "\r");
#    Print("+\c");
    d:= Length(SlowLog) + 1;
    SlowLog[d]:= min;
    
    sols:= [];  min:= Difference([1..Length(list)], [pos]);
    for r in list[pos] do
        
        # keep me informed.
        SlowLog[d]:= SlowLog[d] - 1;
        
        # and recurse with smaller problem ...
        small:= SlowCombine(list{min}, sum - r, index{min});
        
        # combine solutions
        for l in small do
            l[index[pos]]:= r;
            l{index}:= l{index} + found;
            Add(sols, l);
        od;
    od;
    
    Unbind(SlowLog[d]);
#    Print("-\c");
    
    # return list of all solutions.
    return sols;
end;

## for example:
#W:= CoxeterGroup("E", 6);
#cc:= ConjugacyClasses(W);
#List(cc, Size);
#cen:= List(cc, x-> x.centralizer);
#ctc:= List(cen, CharTable);
#ct:= CharTable(W);
#fus:= List(cen, x-> FusionConjugacyClasses(x, W));
#ind:= List([1..Length(cc)], i->
#  Set(Induced(ctc[i], ct, Filtered(ctc[i].irreducibles, x-> x[1] = 1), fus[i])));
#sum:= List(ct.irreducibles, x-> x[1]);
#lis:= List(ind, x-> MatScalarProducts(ct, ct.irreducibles, x));;
##sol:= SlowCombine(lis, sum, [1..Length(cc)]);;

#############################################################################
#
#  Given W and s in S. Let M = S - s.  Loop over X_M and determine a_{JML}.
#  Returns a rectangular matrix with rows J subseteq S and cols L subseteq M.
#
#  iterator version.
#
MaximalAJKL1:= function(W, s)

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
      if M = [] then 
          out:= inn;
      else
          L:= OnSets(M, x);
          out:= Filtered(inn, s-> OnSets(L, W.(W.rootRestriction[s]))[Length(L)] <= W.parentN);
      fi;
      InfoZigzag2(" i: ", inn, " o: ", out, "\n");
      for J in Combinations(inn) do
         L:= OnSets(Difference(J, out), x^-1);
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
  
MaximalAJKL2:= function(W, s)

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

MaximalAJKL:= MaximalAJKL2;

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
LeftRegularE:= function(D)
    local   nu;
    nu:= DescentAlgebraOps.MuNu(D).nu;    
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
    nu:= DescentAlgebraOps.MuNu(DescentAlgebra(W)).nu;
    ee:= [];  a:= 0;  lll:= List(Shapes(W), Size);
    for l in lll do
        Add(ee, Sum(nu{a+[1..l]}));
        a:= a + l;
    od;

    dia:= DiagonalMat(List(ConjugacyClasses(W), x-> Size(W)/Size(x)));
#    Error();
    return ee * IncidenceMatShapes(Shapes(W)) * sec * dia;
end;

#############################################################################
##  
# this will find all possible combinations of characters that are
#
# 1. induced linear characters of the centralizer, one for each class C.
# 2. scalar product with YCharacters gives sizes of Y intersect C.
# 3. sums over Coxeter classes yield ECharacters.
# (not required) 4. summing over all elements of C results in a symmetric
# table.  This last test reduces the number of possibilites in the case
# of non-crystallographic Coxeter groups.   For the crystallographic
# case, there seems to be a unique solution after step 3, in many cases 
# after step 2 already.
CCharacters:= function(W)
    local   cc,  ct,  ind,  c,  cen,  fus,  ctc,  sec,  sect,  yct,  
            i,  scp,  fil,  ect,  ccc,  lis,  sum,  sol,  j;
    
    cc:= ConjugacyClasses(W);
    ct:= CharTable(W); 
    ind:= [];
    for c in cc do
        cen:= Centralizer(W, Representative(c));
        fus:= FusionConjugacyClasses(cen, W);
        if cen = W then
            ctc:= ct;
        else
            ctc:= DixontinI(DixonInit(cen)).charTable;
        fi;
        Add(ind, Set(Induced(ctc, ct, Filtered(ctc.irreducibles, x-> x[1] = 1), fus)));
    od;
    
    sec:= SizesDescentConjugacyClasses(W);
    sect:= TransposedMat(sec);
    yct:= YCharacters(W);
    
    for i in [1..Length(cc)] do
        scp:= MatScalarProducts(ct, yct, ind[i]);
        fil:= Filtered([1..Length(scp)], x-> scp[x] = sect[i]); 
        ind[i]:= ind[i]{fil}; 
    od;
    
    ect:= ECharacters(W);
    ccc:= List(Shapes(W), ConjugacyClasses);
    
    for i in [1..Length(ect)] do
        lis:= List(ind{ccc[i]}, x-> MatScalarProducts(ct, ct.irreducibles, x));
        sum:= MatScalarProducts(ct, ct.irreducibles, ect{[i]})[1];
        sol:= SlowCombine(lis, sum, [1..Length(lis)]);
        for j in [1..Length(lis)] do
        fil:= Filtered([1..Length(lis[j])], x-> lis[j][x] in sol{[1..Length(sol)]}[j]);    
            ind[ccc[i][j]]:= ind[ccc[i][j]]{fil};
        od;
    od;
    
    return ind;
end;

# now: which characters of the centralizers are used?
# for each class, list: order of w, order of the character l, order of l(w)
# compare wrt to powermap.
WhatCharacters:= function(W, eta)
    local   cc,  ct,  ctc,  data,  i,  cen,  fus,  ind,  pos,  kernel,  
            ns;
    
    cc:= ConjugacyClasses(W);
    ct:= CharTable(W); 
    ctc:= [];
    data:= [];
    for i in [1..Length(cc)] do
        cen:= Centralizer(W, Representative(cc[i]));
        fus:= FusionConjugacyClasses(cen, W);
        if cen = W then
            ctc[i]:= ct;
        else
            ctc[i]:=  DixontinI(DixonInit(cen)).charTable;
        fi;
        ind:= Induced(ctc[i], ct, ctc[i].irreducibles, fus);
        pos:= Filtered([1..Length(ind)], x-> ind[x] = eta[i]);
        ctc[i].selected:= ctc[i].irreducibles{pos};
   #     kernel:= KernelChar(ctc[i].selected[1]);
   #     ns:= NormalSubgroups(cen);

        data[i]:= rec(index:= i,
                      w:= Representative(cc[i]),
                      order:= ct.orders[i],
                      centralizer:= cen,
                      table:= ctc[i],
                      fusion:= fus,
                      chars:= pos
   #                   kernel:= ns[Position(List(ns, x-> Set(FusionConjugacyClasses(x, cen))), kernel)]
                      );
    od;
    
    return data;
end;


#############################################################################
#
# Submodule structure, Loewy Series ...
#
# first: the Cartan Matrix.
# Could be more efficient if the matrices were not all fully blown up!
# Also could take into account its lower triangular shape!
#
ProjectiveIdempotents:= function(D)
    local   lll,  nu,  xxx,  EEE,  a,  l;
    
    if IsBound(D.projectiveIdempotents) then
        return D.projectiveIdempotents;
    fi;

    lll:= List(Shapes(D.W), Size);
    nu:= DescentAlgebraOps.MuNu(D).nu;
    xxx:= LeftRegularX(D);
    
    EEE:= [];  a:= 0;
    for l in lll do
        Add(EEE, Sum(nu{a+[1..l]}) * xxx);
        a:= a + l;
    od;

    D.projectiveIdempotents:= EEE;
    return EEE;
end;


CartanMatDescent:= function(D)
    local   xxx,  EEE,  car,  l,  ll,  i,  j;
    
    xxx:= LeftRegularX(D);
    EEE:= ProjectiveIdempotents(D);
    car:= []; 
    l:= Length(EEE);  ll:= Length(EEE[1]);
    for i in [1..l] do
        car[i]:= [];
        for j in [1..l] do
            car[i][j]:= RankMat(List(xxx, x-> EEE[i][ll] * x) * EEE[j]);
            Print(".\c");
        od; 
        Print("!\n");
    od;  
    return car;
end;

# a gen set for the homs from Pi to Pj.
HomDescent:= function(D, i, j)
    local   xxx,  EEE,  ll,  hom;
    
    xxx:= LeftRegularX(D);
    EEE:= ProjectiveIdempotents(D);
    ll:= Length(EEE[1]);
    hom:=  Set(List(xxx, x-> EEE[i][ll] * x) * EEE[j]);
    TriangulizeMat(hom);
    return Filtered(hom, x-> x <> 0*x);
end;            
            

# second: the radical.
# Brute force again ...
#
RadicalDescent:= function(D)
    local   xxx,  rad,  a,  e,  i;
    
    xxx:= LeftRegularX(D);
    rad:= [];  a:= 0;
    for e in Shapes(D.W) do
        for i in a + [2..Size(e)] do
            Add(rad, xxx[i]-xxx[i-1]);
        od;
        a:= a + Size(e);
    od;
    return rad;
end;

RadicalSeriesDescent:= function(D)
    local   rad,  l,  r,  ser;
    
    rad:= RadicalDescent(D);
    if rad = [] then return []; fi;
    
    l:= Length(rad[1]);
    r:= List(rad, x-> x[l]);
    ser:= [r];
    
    while true do
        r:= Union(List(r, x-> List(rad, y-> x * y)));
        TriangulizeMat(r);
        r:= Difference(r, [0*r[1]]);
        if r = [] then 
            return ser; 
        fi;
        Add(ser, r);
    od;
    
end;

MatsRadsDescent:= function(D)
    local   rad,  hom,  l,  zero,  i,  j,  mat,  k;
    
    
    rad:= List(RadicalSeriesDescent(D), x-> VectorSpace(x, Rationals));
    hom:= [];
    l:= Length(Shapes(D.W));
    zero:= 0*[1..Dimension(D)];
    for i in [1..l] do
        hom[i]:= [];
        for j in [1..l] do
            hom[i][j]:= VectorSpace(HomDescent(D, i, j), Rationals, zero);
        od;
    od;
    mat:= [];
    for k in [1..Length(rad)] do
        mat[k]:= [];
        for i in [1..l] do
            mat[k][i]:= [];
            for j in [1..l] do
                mat[k][i][j]:= Dimension(Intersection(hom[i][j], rad[k]));
            od;
        od;
    od;
    
    for k in [2..Length(mat)] do
        mat[k-1]:= mat[k-1] - mat[k];
    od;
    
    return mat;
end;

#############################################################################
##  
##  
##  
ProjectiveModule:= function(D, i)
    local   ser,  zero,  hom,  j,  lis,  s;

    ser:= List(RadicalSeriesDescent(D), x-> VectorSpace(x, Rationals));
    zero:= 0*[1..Dimension(D)];
    hom:= [];
    for j in [1..Length(Shapes(D.W))] do
        hom[j]:= VectorSpace(HomDescent(D, i, j), Rationals, zero);
    od;
    lis:= [List(hom, Dimension)];
    for s in ser do 
        Add(lis, List(hom, h-> Dimension(Intersection(s, h))));
    od;
    
    for j in [2..Length(lis)] do
        if lis[j] = 0*lis[j] then
            Unbind(lis[j]);
        else
            lis[j-1]:= lis[j-1] - lis[j];
        fi;
    od;
        
    return lis;
end;

LaTeXProjectiveModule:= function(D, nam, i)
    local   lis,  text,  j,  comma,  k;
    lis:= ProjectiveModule(D, i);
    text:= "$\\begin{array}[b]{|c|}\\hline\n";
    for j in [1..Length(lis)] do
        comma:= false;
        for k in [1..Length(nam)] do
            if lis[j][k] > 0 then
                if comma then
                    Append(text, "\\, \c");
                fi;
                if lis[j][k] = 1 then
                    Append(text, nam[k]);
                else 
                    Append(text, "(");
                    Append(text, nam[k]);
                    Append(text, ")^{");
                    Append(text, String(lis[j][k]));
                    Append(text, "}");
                fi;
                comma:= true;
            fi;
        od;
        Append(text, "\\\\\\hline\n");
    od;
    Append(text, "\\end{array}$");
    
    return text;
end;

#############################################################################
##
## ich glaub wir brauchen ne function die zu einem Vector die entsprechende
## Matrix macht.
##
MatDescentVec:= function(D, vec)
    local   xxx,  mat,  i;

    xxx:= LeftRegularX(D);
    
    mat:= NullMat(Dimension(D), Dimension(D));
    for i in [1..Length(xxx)] do
        mat:= mat + vec[i] * xxx[i];
    od;
    
    return mat;
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

#############################################################################
##  
##  
RanMatDescent:= function(D)
    local   mat,  xxx,  shapes,  i,  row,  iii,  j,  jjj,  lis;
    
    mat:= [];
    xxx:= LeftRegularX(D);
    shapes:= Shapes(D.W);
    for i in [1..Length(shapes)] do
        row:= [];
        iii:= Sum(shapes{[1..i-1]}, Size) + [1..Size(shapes[i])];
        for j in [1..Length(shapes)] do
            jjj:= Sum(shapes{[1..j-1]}, Size) + [1..Size(shapes[j])];
            lis:= List(iii, i-> List(jjj, j-> List(xxx, x-> x[i][j])));
            Add(row, RankMat(Concatenation(lis)));
        od;
        Add(mat, row);
    od;
    return mat;
end;

SizMatDescent:= function(D)
    local   mat,  xxx,  shapes,  i,  row,  iii,  j,  jjj,  lis;
    
    mat:= [];
    xxx:= LeftRegularX(D);
    shapes:= Shapes(D.W);
    for i in [1..Length(shapes)] do
        row:= [];
        iii:= Sum(shapes{[1..i-1]}, Size) + [1..Size(shapes[i])];
        for j in [1..Length(shapes)] do
            jjj:= Sum(shapes{[1..j-1]}, Size) + [1..Size(shapes[j])];
            lis:= List(iii, i-> List(jjj, j-> List(xxx, x-> x[i][j])));
            Add(row, Size(Set(Filtered(Concatenation(lis), x-> x <> 0*x))));
        od;
        Add(mat, row);
    od;
    return mat;
end;


##  
##  for each mu >= lambda the set of nontrivial vectors aJKL, 
##  J <= S, K \in mu, L \in lambda.
##
LisMatDescent:= function(D)
    local   mat,  xxx,  shapes,  i,  row,  iii,  j,  jjj,  lis;
    
    mat:= [];
    xxx:= LeftRegularX(D);
    shapes:= Shapes(D.W);
    for i in [1..Length(shapes)] do
        row:= [];
        iii:= Sum(shapes{[1..i-1]}, Size) + [1..Size(shapes[i])];
        for j in [1..Length(shapes)] do
            jjj:= Sum(shapes{[1..j-1]}, Size) + [1..Size(shapes[j])];
            lis:= List(iii, i-> List(jjj, j-> List(xxx, x-> x[i][j])));
            Add(row, Set(Filtered(Concatenation(lis), x-> x <> 0*x)));
        od;
        Add(mat, row);
    od;
    return mat;
end;

##  
##  
ClosLis:= function(lis)
    local   l,  clo,  i,  j,  a,  b;
    ##  
    l:= Length(lis);
    clo:= [];
    for i in [1..l] do
        clo[i]:= [];
        for j in [1..l] do
            clo[i][j]:= Copy(lis[i][j]);
            for a in [j+1..i] do
                UniteSet(clo[i][j], lis[i][a]);
            od;
            for b in [j..i-1] do
                UniteSet(clo[i][j], lis[b][j]);
            od;
        od;
    od;
    return clo;
end;

OpenLis:= function(lis)
    local   l,  clo,  i,  j,  a,  b;
    ##  
    l:= Length(lis);
    clo:= [];
    for i in [1..l] do
        clo[i]:= [];
        for j in [1..l] do
            clo[i][j]:= [];
            for a in [j+1..i] do
                UniteSet(clo[i][j], lis[i][a]);
            od;
            for b in [j..i-1] do
                UniteSet(clo[i][j], lis[b][j]);
            od;
        od;
    od;
    return clo;
end;

##  
##  
ClosLisRank:= function(lis, rank)
    local   l,  clo,  i,  j,  a,  b;
    ##  
    l:= Length(lis);
    clo:= [];
    for i in [1..l] do
        clo[i]:= [];
        for j in [1..l] do
            clo[i][j]:= Copy(lis[i][j]);
            for a in [j+1..i] do
                if rank[j] = rank[a] - 1 then
                    UniteSet(clo[i][j], lis[i][a]);
                fi;
            od;
            for b in [j..i-1] do
                if rank[b] = rank[i] - 1 then
                    UniteSet(clo[i][j], lis[b][j]);
                fi;
            od;
        od;
    od;
    return clo;
end;

OpenLisRank:= function(lis, rank)
    local   l,  clo,  i,  j,  a,  b;
    ##  
    l:= Length(lis);
    clo:= [];
    for i in [1..l] do
        clo[i]:= [];
        for j in [1..l] do
            clo[i][j]:= [];
            for a in [j+1..i] do
                if rank[j] = rank[a] - 1 then
                    UniteSet(clo[i][j], lis[i][a]);
                fi;
            od;
            for b in [j..i-1] do
                if rank[b] = rank[i] - 1 then
                    UniteSet(clo[i][j], lis[b][j]);
                fi;
            od;
        od;
    od;
    return clo;
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
##  fill-prefix:        "##  "
##  End:
##
