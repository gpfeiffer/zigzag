#############################################################################
##
#A  skyline.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
##
##  This file contains routines for classical Coxeter groups as permutations.
##
##  <#GAPDoc Label="Intro:Skyline">
##    A finite Coxeter group <M>W</M> of classical type ...
##      
##    The functions described in this chapter are implemented in the file
##    <F>skyline.g</F>.  
##  <#/GAPDoc>
##

# how to translate between permutations (as elements of the symmetric group) 
# and elements of the Coxeter group of type A.


# from i, length k.
FallingSequence:= function(i, k)
    local   lis;
    
    lis:= [1..i+1];
    lis{[i+1-k..i]}:= [i+2-k..i+1];
    lis[i+1]:= i+1-k;
    return PermList(lis);
end;


#############################################################################
#############################################################################
##
##  new data structure: SkylineA
##
##  represent an element of W(A_n) as a tower, ie, a sequence of
##  n integers tower[1] ... tower[n], with 0 <= tower[i] <= i.
##  Here a value tower[i] = k stands for a coset rep of length k,
##  ie., s_i s_{i-1} \dotsm s_{i-k+1}, or, in terms of permutations
##  of n + 1 points, the cycle (i-k+1, i-k+2, ... i+1).
##

#############################################################################
##  
#O  SkylineAOps . . . . . . . . . . . . . . . . . . . . . .  operations record.
##  
SkylineAOps:= OperationsRecord("SkylineAOps", GroupElementOps);


#############################################################################
##  
#C  SkylineA( <list> )  . . . . . . . . . . . . . . . . . . . . . constructor.
##  
SkylineA:= function(list)
    local   n;
    
    # expect a list of numbers.
    n:= Length(list);
    
    # delete trailing zeroes.
    while n > 0 and list[n] = 0 do 
        Unbind(list[n]);
        n:= n - 1;
    od;
    
    # construct object.
    return rec(
             isGroupElt:= true,
             isSkylineA:= true,
             tower:= list,
             operations:= SkylineAOps);
end;


#############################################################################
##
#F  IsSkylineA( <obj> )  . . . . . . . . . . . . . . . . . . . . .  type check.
##
IsSkylineA:= function(obj)
    return IsRec(obj) and IsBound(obj.isSkylineA) 
           and obj.isSkylineA = true;
end;


#############################################################################  
##  
#M  Print( <skyline> )  . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
SkylineAOps.Print:= function(self)
    Print("SkylineA( ", self.tower, " )");
end;


#############################################################################
SkylineAOps.\=:= function(l, r)
    if not IsSkylineA(r) or not IsSkylineA(l) then return false; fi;
    return l.tower = r.tower;
end;

#############################################################################
SkylineAOps.CoxeterLength:= function(self)
    return Sum(self.tower);
end;

#############################################################################
SkylineAOps.Permutation:= function(self)
    local   perm,  i;
    
    perm:= ();
    for i in [1..Length(self.tower)] do
        perm:= perm * FallingSequence(i, self.tower[i]);
    od;
    return perm;
end;

#############################################################################
SkylineAPerm:= function(pi)
    local   n,  set,  k;
    
    # trivial case first.
    if pi = () then return SkylineA([]); fi;
    
    n:= LargestMovedPointPerm(pi);
    
    set:= [];
    
    while n > 1 do
        k:= n^pi;
        set[n-1]:= n-k;
        pi:= pi / FallingSequence(n-1, n-k);
        n:= n - 1;
    od;
    return SkylineA(set);
end;

#############################################################################
SkylineAOps.Word:= function(self)
    local   word,  i;
    
    word:= [];
    for i in [1..Length(self.tower)] do
        Append(word, [i, i-1 .. i - self.tower[i] + 1]);
    od;
    return word;
end;

#############################################################################
SkylineAOps.Descents:= function(self)
    local   old,  des,  i,  new;
    
    old:= 0;
    des:= [];
    for i in [1..Length(self.tower)] do
        new:= self.tower[i];
        if new > old then
            Add(des, i);
        fi;
        old:= new;
    od;
    return des;
end;


#############################################################################
SkylineAOps.SmallestDescent:= function(self)
    return PositionProperty(self.tower, x-> x > 0);
end;

#############################################################################
SkylineAOps.\*:= function(lft, rgt)
    local   product,  j,  l,  m,  k;
    
    # check arguments.
    if not IsSkylineA(rgt) or not IsSkylineA(lft) then
        Error("don't know how to compute the product of <lft> and <rgt>");
    fi;
    
    # trivial case.
    if rgt.tower = [] then  return lft;  fi;
    
    # make a fresh copy of lft tower, extend if necessary.
    product:= Copy(lft.tower);
    Append(product, 0*[Length(lft.tower) + 1 .. Length(rgt.tower)]);
    
    # loop over factors of rgt
    for j in [1..Length(rgt.tower)] do
        
        # multiply product with factor rgt.tower[j] = l
        l:= rgt.tower[j];
        m:= Length(product);
        
        while l > 0 do
            k:= product[m];
            
            # multiply product.tower[m] = k by tower[j] = l
            if j > m - k + l then  # shift
                j:= j - 1;
            elif j > m - k then    # cancel
                j:= j - 1;
                k:= k - 1;
                l:= l - 1;
            elif j = m - k then    # join
                k:= k + l;
                l:= 0;
            fi;                    #  pass: do nothing.
            
            product[m]:= k;
            m:= m - 1;
        od;
    
    od;
    
    return SkylineA(product);
end;

    
#############################################################################
SkylineAOps.Inverse:= function(self)
    local   inverse,  l,  n,  i,  j;
    
    inverse:= Copy(self.tower);
    l:= Length(inverse);
    
    for n in [l, l-1 .. 1] do
        
        # locate rightmost zero.
        i:= 0;
        for j in [1..n] do
            if inverse[j] = 0 then
                i:= j;
            fi;
        od;
        
        # shift remainder of word.
        if i > 0 then
            inverse{[i..n-1]}:= inverse{[i+1..n]} - 1;
        else
            inverse{[i+1..n-1]}:= inverse{[i+2..n]} - 1;
        fi;

        # record inverse entry.
        inverse[n]:= n - i;
        
    od;
    
    return SkylineA(inverse);
end;

#############################################################################
SkylineAWord:= function(word)
    local   prod,  a,  l;
    
    prod:= SkylineA([]);
    for a in word do
        l:= 0*[1..a];
        l[a]:= 1;
        prod:= prod * SkylineA(l);
    od;
    return prod;
end;

    
#############################################################################
SkylineAOps.IsDescent:= function(self, i)
    if i = 1 then
        return self.tower[1] > 0;
    else
        return self.tower[i] > self.tower[i-1];
    fi;
end;


    
#############################################################################
#############################################################################
##
##  new data structure: SkylineB
##
##  represent an element of W(B_n) as a tower, ie, a sequence of
##  n integers tower[1], ..., tower[n], with -i <= tower[i] < i.
##  Here a value tower[i] = k >=0  stands for a coset rep of length k,
##  ie., s_{i-1} ... s_{i-k}, or, in terms of permutations
##  of 2n points, the double cycle (i-k, i-k+1, ..., i) and its
##  negative copy.
##  And a value tower[i] = -(k+1) < 0 stands for a coset rep of length 2i-k,
##  ie., s_{i-1} ... s_{i-k} s_{i-k-1} ... s_1 t s_1 ... s_{i-k-1},
##  or in terms of permutations of 2n points, the long cycle
##  (i-k, i-k+1, ..., i, followed by the negatives in the same order)
##


#############################################################################
##  
#O  SkylineBOps . . . . . . . . . . . . . . . . . . . . . .  operations record.
##  
SkylineBOps:= OperationsRecord("SkylineBOps", GroupElementOps);


#############################################################################
##  
#C  SkylineB( <list> )  . . . . . . . . . . . . . . . . . . . . . constructor.
##  
SkylineB:= function(list)
    local   n;
    
    # expect a list of numbers.
    n:= Length(list);
    
    # delete trailing zeroes.
    while n > 0 and list[n] = 0 do 
        Unbind(list[n]);
        n:= n - 1;
    od;
    
    # construct object.
    return rec(
             isGroupElt:= true,
             isSkylineB:= true,
             tower:= list,
             operations:= SkylineBOps);
end;


#############################################################################
##
#F  IsSkylineB( <obj> )  . . . . . . . . . . . . . . . . . . . . .  type check.
##
IsSkylineB:= function(obj)
    return IsRec(obj) and IsBound(obj.isSkylineB) 
           and obj.isSkylineB = true;
end;


#############################################################################  
##  
#M  Print( <skyline> )  . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
SkylineBOps.Print:= function(self)
    Print("SkylineB( ", self.tower, " )");
end;


#############################################################################
SkylineBOps.\=:= function(l, r)
    if not IsSkylineB(r) or not IsSkylineB(l) then return false; fi;
    return l.tower = r.tower;
end;

#############################################################################
SkylineBOps.CoxeterLength:= function(self)
    return Sum([1..Length(self.tower)], i-> self.tower[i] mod (2*i));
end;

#############################################################################
##
##  as words in [0, 1, .., n-1]!  CHEVIE uses [1..n]!
##
SkylineBOps.Word:= function(self)
    local   word,  i,  k;
    
    word:= [];
    for i in [1..Length(self.tower)] do
        k:= self.tower[i];
        if k < 0 then
            Append(word, [i-1, i-2 .. 0]);
            Append(word, [1..i+k]);
        else
            Append(word, [i-1, i-2 .. i-k]);
        fi;                 
    od;
    return word;
end;

#############################################################################
##
##  utility functions.
##

# how to turn tower[i] = -(k+1) < 0 into a permutation:
# the long cycle (i-k, i-k+1, ..., i, followed by the negatives in the same order)
SkylineBOps.permN:= function(i, k)
    local   lis;
    
    lis:= [1..2*i];
    lis{2*[i-k .. i-1]}:= 2*[i-k+1..i];
    lis[2*i]:= 2*(i-k)-1;
    lis{2*[i-k .. i-1]-1}:= 2*[i-k+1..i]-1;
    lis[2*i-1]:= 2*(i-k);
    return PermList(lis);
end;
    
# how to turn tower[i] = k >= 0 into a permutation:
# the double cycle (i-k, i-k+1, ..., i) and its negative copy
SkylineBOps.permP:= function(i, k)
    local   lis;
    
    lis:= [1..2*i];
    lis{2*[i-k .. i-1]}:= 2*[i-k+1..i];
    lis[2*i]:= 2*(i-k);
    lis{2*[i-k .. i-1]-1}:= 2*[i-k+1..i]-1;
    lis[2*i-1]:= 2*(i-k)-1;
    return PermList(lis);
end;


#############################################################################
##
##  t -> (1, 2); s_i -> (2i-1, 2i+1)(2i, 2i+2),
##  ie.,  i -> 2i;  -i -> 2i-1  for i > 0,
##  hence:   -: n -> n + 2(n mod 2) - 1.
##
SkylineBOps.Permutation:= function(self)
    local   perm,  i,  k;
    
    perm:= ();
    for i in [1..Length(self.tower)] do
        k:= self.tower[i];
        if k < 0 then
            perm:= perm * SkylineBOps.permN(i, -k-1);
        else
            perm:= perm * SkylineBOps.permP(i, k);
        fi;
    od;
    return perm;
end;

#############################################################################
SkylineBPerm:= function(pi)
    local   n,  set,  k;
    
    # trivial case first.
    if pi = () then return SkylineB([]); fi;
    
    n:= LargestMovedPointPerm(pi)/2;  # is always even!
    
    set:= [];
    
    while n > 0 do
        k:= (2*n)^pi;
        if k mod 2 = 0 then
            set[n]:= n-k/2;
            pi:= pi / SkylineBOps.permP(n, n-k/2);
        else
            set[n]:= (k-1)/2-n;
            pi:= pi / SkylineBOps.permN(n, n-(k+1)/2);
        fi;
        n:= n - 1;
    od;
    return SkylineB(set);
end;

#############################################################################
SkylineBOps.\*:= function(lft, rgt)
    local   product,  j,  l,  m,  k,  del,  eps;
    
    # check arguments.
    if not IsSkylineB(rgt) or not IsSkylineB(lft) then
        Error("don't know how to compute the product of <lft> and <rgt>");
    fi;
    
    # trivial case.
    if rgt.tower = [] then  return lft;  fi;
    
    # make a fresh copy of lft tower, extend if necessary.
    product:= Copy(lft.tower);
    Append(product, 0*[Length(lft.tower) + 1 .. Length(rgt.tower)]);
    
    # loop over factors of rgt
    for j in [1..Length(rgt.tower)] do
        
        # multiply product with factor rgt.tower[j] = l
        l:= rgt.tower[j];
        
        # adjust possible sign
        if l < 0 then
            del:= -1;
            l:= -l-1;
        else
            del:= 1;
        fi;
        
        # loop over the factors of product
        m:= Length(product);
        while l > 0 or del = -1 do
            
            # multiply product.tower[m] = k by tower[j] = l
            k:= product[m];
            
            # adjust possible sign
            if k < 0 then
                eps:= -1;
                k:= -k-1;
            else
                eps:= 1;
            fi;
            
            # distinguish four cases
            if j > m - k + l then  # shift
                j:= j - 1;
            elif j > m - k then    # cancel
                j:= j - 1;
                k:= k - 1;
                l:= l - 1;
            elif j = m - k then    # join
                k:= k + l;
                l:= 0;
                eps:= eps * del;
                del:= 1;
            fi;                    #  pass: do nothing.
            
            # adjust possible sign
            if eps = -1 then
                k:= -k-1;
            fi;
            
            product[m]:= k;
            m:= m - 1;
        od;
    
    od;
    
    return SkylineB(product);
end;

#############################################################################
SkylineBWord:= function(word)
    local   prod,  a,  l;
    
    prod:= SkylineB([]);
    for a in word do
        l:= 0*[1..a];
        if a = 0 then
            l[1]:= -1;
        else
            l[a+1]:= 1;
        fi;
        prod:= prod * SkylineB(l);
    od;
    return prod;
end;

#############################################################################
SkylineBOps.Inverse:= function(self)
    local   inverse,  l,  n,  i,  j,  new;
    
    inverse:= Copy(self.tower);
    l:= Length(inverse);
    
    for n in [l, l-1 .. 1] do
        
        # locate rightmost 0 or -1.
        i:= 0;
        for j in [1..n] do
            if inverse[j] in [-1, 0] then
                i:= j;
            fi;
        od;
        
        # compute inverse entry
        new:= n - i;
        if inverse[i] = -1 then
            new:= -new-1;
        fi;
                
        # shift remainder of word (assert i > 0).
        for j in [i..n-1] do
            inverse[j]:= inverse[j+1] - SignInt(inverse[j+1]);
        od;
        
        # record inverse entry.
        inverse[n]:= new;
        
    od;
    
    return SkylineB(inverse);
end;

    
#############################################################################
SkylineBOps.Descents:= function(self)
    local   old,  des,  n,  i,  new;
    
    old:= 0;
    des:= [];
    n:= Length(self.tower);
    for i in [1..n] do
        new:= self.tower[i];
        if new < 0 then
            if old >= 0 then
                Add(des, i-1);
            else
                if new - old >= 0 then
                    Add(des, i-1);
                fi;
            fi;
        else
            if old >= 0 then
                if new - old > 0 then
                    Add(des, i-1);
                fi;
            fi;
        fi;
        old:= new;
    od;
    return des;
end;


#############################################################################
SkylineBOps.SmallestDescent:= function(self)
    return PositionProperty(self.tower, x-> x <> 0) - 1;
end;

    
#############################################################################
SkylineBOps.IsDescent:= function(self, i)
    if i = 0 then
        return self.tower[1] <> 0;
    else
        if self.tower[i+1] < 0 then
            return self.tower[i] >= 0 or self.tower[i+1] >= self.tower[i];
        else
            return self.tower[i] >= 0 and self.tower[i+1] > self.tower[i];
        fi;
    fi;
end;

#############################################################################
#############################################################################
##
##  new data structure: SkylineD
##
##  represent an element of W(D_n) as a tower, ie, a sequence of
##  n integers tower[1], ..., tower[n-1], with -i-1 <= tower[i] <= i.
##  Here a value tower[i] = k >=0  stands for a coset rep of length k,
##  ie., s_{i} ... s_{i-k+1}, or, in terms of permutations
##  of 2n points, the double cycle (i-k, i-k+1, ..., i) and its
##  negative copy.
##  And a value tower[i] = -(k+1) < 0 stands for a coset rep of length 2i-k,
##  ie., s_{i} ... s_{i-k} s_{i-k-1} ... s_2 u s_1 ... s_{i-k-1},
##  or in terms of permutations of 2n points, the long cycle
##  (i-k, i-k+1, ..., i, followed by the negatives in the same order)
##


#############################################################################
##  
#O  SkylineDOps . . . . . . . . . . . . . . . . . . . . . .  operations record.
##  
SkylineDOps:= OperationsRecord("SkylineDOps", GroupElementOps);


#############################################################################
##  
#C  SkylineD( <list> )  . . . . . . . . . . . . . . . . . . . . . constructor.
##  
SkylineD:= function(list)
    local   n;
    
    # expect a list of numbers.
    n:= Length(list);
    
    # delete trailing zeroes.
    while n > 0 and list[n] = 0 do 
        Unbind(list[n]);
        n:= n - 1;
    od;
    
    # construct object.
    return rec(
             isGroupElt:= true,
             isSkylineD:= true,
             tower:= list,
             operations:= SkylineDOps);
end;


#############################################################################
##
#F  IsSkylineD( <obj> )  . . . . . . . . . . . . . . . . . . . . .  type check.
##
IsSkylineD:= function(obj)
    return IsRec(obj) and IsBound(obj.isSkylineD) 
           and obj.isSkylineD = true;
end;


#############################################################################  
##  
#M  Print( <skyline> )  . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
SkylineDOps.Print:= function(self)
    Print("SkylineD( ", self.tower, " )");
end;


#############################################################################
SkylineDOps.\=:= function(l, r)
    if not IsSkylineD(r) or not IsSkylineD(l) then return false; fi;
    return l.tower = r.tower;
end;

#############################################################################
SkylineDOps.CoxeterLength:= function(self)
    return Sum([1..Length(self.tower)], i-> self.tower[i] mod (2*i+1));
end;

#############################################################################
##
##  as words in [0, 1, .., n-1]!  CHEVIE uses [1..n]!
##
SkylineDOps.Word:= function(self)
    local   word,  i,  k;
    
    word:= [];
    for i in [1..Length(self.tower)] do
        k:= self.tower[i];
        if k < 0 then
            Append(word, [i, i-1 .. 2]);
            Append(word, [0 .. i+k+1]);
        else
            Append(word, [i, i-1 .. i-k+1]);
        fi;                 
    od;
    return word;
end;

#############################################################################
##
##  utility functions.
##

# how to turn tower[i] = -(k+1) < 0 into a permutation:
# the long cycle (1,-1)(i-k+1, i-k+2, ..., i+1, followed by the negatives in the same order)
SkylineDOps.permN:= function(i, k)
    local   lis;
    
    lis:= [1..2*i+2];
    lis{2*[i-k+1 .. i]}:= 2*[i-k+2..i+1];
    lis[2*i+2]:= 2*(i-k)+1;
    lis{2*[i-k .. i-1]+1}:= 2*[i-k+1..i]+1;
    lis[2*i+1]:= 2*(i-k+1);
    return (1,2)*PermList(lis);
end;
    
# how to turn tower[i] = k >= 0 into a permutation:
# the double cycle (i-k+1, i-k+2, ..., i+1) and its negative copy
SkylineDOps.permP:= function(i, k)
    local   lis;
    
    lis:= [1..2*i+2];
    lis{2*[i-k+1 .. i]}:= 2*[i-k+2..i+1];
    lis[2*i+2]:= 2*(i-k+1);
    lis{2*[i-k .. i-1]+1}:= 2*[i-k+1..i]+1;
    lis[2*i+1]:= 2*(i-k)+1;
    return PermList(lis);
end;


#############################################################################
##
##  u -> (1, 4)(2, 3); s_i -> (2i-1, 2i+1)(2i, 2i+2),
##  ie.,  i -> 2i;  -i -> 2i-1  for i > 0,
##  hence:   -: n -> n + 2(n mod 2) - 1.
##
SkylineDOps.Permutation:= function(self)
    local   perm,  i,  k;
    
    perm:= ();
    for i in [1..Length(self.tower)] do
        k:= self.tower[i];
        if k < 0 then
            perm:= perm * SkylineDOps.permN(i, -k-1);
        else
            perm:= perm * SkylineDOps.permP(i, k);
        fi;
    od;
    return perm;
end;

#############################################################################
SkylineDPerm:= function(pi)
    local   n,  set,  k;
    
    # trivial case first.
    if pi = () then return SkylineD([]); fi;
    
    n:= LargestMovedPointPerm(pi)/2;  # is always even!
    
    set:= [];
    
    while n > 1 do
        k:= (2*n)^pi;
        if k mod 2 = 0 then
            set[n-1]:= n-k/2;
            pi:= pi / SkylineDOps.permP(n-1, n-k/2);
        else
            set[n-1]:= (k-1)/2-n;
            pi:= pi / SkylineDOps.permN(n-1, n-(k+1)/2);
        fi;
        n:= n - 1;
    od;
    return SkylineD(set);
end;

#############################################################################
SkylineDOps.\*:= function(lft, rgt)
    local   product,  j,  l,  n,  k;
    
    # check arguments.
    if not IsSkylineD(rgt) or not IsSkylineD(lft) then
        Error("don't know how to compute the product of <lft> and <rgt>");
    fi;
    
    # trivial case.
    if rgt.tower = [] then  return lft;  fi;
    
    # make a fresh copy of lft tower, extend if necessary.
    product:= Copy(lft.tower);
    Append(product, 0*[Length(lft.tower) + 1 .. Length(rgt.tower)]);
    
    # loop over factors of rgt
    for j in [1..Length(rgt.tower)] do
        
        # multiply product with factor rgt.tower[j] = l
        l:= rgt.tower[j];
        n:= Length(product);
        
        while l <> 0 do
            k:= product[n];
            
            # multiply product.tower[n] = k by tower[j] = l
            if l < 0 then
                l:= -l-1;
                if k < 0 then
                    k:= -k-1;
                    if j = n - k then           # join
                        k:= -(k + l) - 1;       # !!! :) force k to come out positive
                        l:= -1;                 # !!! :) force l to come out positive
                    elif j > n - k then  
                        if j - l <= n - k then  # cancel
                            l:= l - 1;
                            k:= k - 1;
                        fi;                     # shift
                        j:= j - 1;
                    fi;                         # pass: do nothing.
                    k:= -k-1;    
                else
                    if j = n - k then           # join
                        k:= -(k + l) - 1;       # !!! :) make k come out negative
                        l:= -1;                 # !!! :) force l to come out positive
                    elif j > n - k then  
                        if j - l <= n - k then  # cancel
                            l:= l - 1;
                            k:= k - 1;
                        fi;                     # shift
                        j:= j - 1;
                    fi;                         # pass: do nothing.
                fi;
                l:= -l-1;
            else
                if k < 0 then
                    k:= -k-1;
                    if j = n - k then           # join
                        k:= k + l;
                        l:= 0;
                    elif j > n - k then  
                        if j - l <= n - k then  # cancel
                            l:= l - 1;
                            k:= k - 1;
                        fi;                     # shift
                        j:= j - 1;
                    fi;                         # pass: do nothing.
                    k:= -k-1;
                else
                    if j = n - k then           # join
                        k:= k + l;
                        l:= 0;
                    elif j > n - k then  
                        if j - l <= n - k then  # cancel
                            l:= l - 1;
                            k:= k - 1;
                        fi;                     # shift
                        j:= j - 1;
                    fi;                         # pass: do nothing.
                fi;
            fi;
            product[n]:= k;
            n:= n-1;
        od;
    
    od;
    
    return SkylineD(product);
end;

SkylineDOps.\*:= function(lft, rgt)
    local   product,  j,  l,  m,  k,  del,  eps;
    
    # check arguments.
    if not IsSkylineD(rgt) or not IsSkylineD(lft) then
        Error("don't know how to compute the product of <lft> and <rgt>");
    fi;
    
    # trivial case.
    if rgt.tower = [] then  return lft;  fi;
    
    # make a fresh copy of lft tower, extend if necessary.
    product:= Copy(lft.tower);
    Append(product, 0*[Length(lft.tower) + 1 .. Length(rgt.tower)]);
    
    # loop over factors of rgt
    for j in [1..Length(rgt.tower)] do
        
        # multiply product with factor rgt.tower[j] = l
        l:= rgt.tower[j];
        
        m:= Length(product);
        
#        while l <> 0 and m > 0 do
        while l <> 0 and m > 0 do
            k:= product[m];
            
            # multiply product.tower[m] = k by tower[j] = l
            if l < 0 then
                del:= -1;
                l:= -l-1;
            else
                del:= 1;
            fi;
            
            if k < 0 then
                eps:= -1;
                k:= -k-1;
            else
                eps:= 1;
            fi;
            
            if j > m - k + l then  # shift
                j:= j - 1;
                if eps = -1 then
                    if del = 1 then
                        if j = l then
                            del:= -1;
                        fi;
                    else
                        if m = k then
                            eps:= 1;
                        else
                            if j = l then
                                del:= 1;
                            fi;
                        fi;
                    fi;
                else
                    if del = -1 then
                        if m = k then
                            eps:= -1;
                            if j = l then
                                del:= 1;
                            fi;
                        fi;
                    fi;
                fi;
            elif j > m - k then    # cancel
                if eps = -1 then
                    if del = 1 then
                        if j = l then
                            del:= -1;
                        fi;
                    else
                        if m = k then
                            eps:= 1;
                        else
                            if j = l then
                                del:= 1;
                            fi;
                        fi;
                           
                    fi;
                else
                    if del = -1 then
                        if m = k then 
                            eps:= -1;
                            if j = l then
                                del:= 1;
                            fi;
                        fi;
                    fi;
                fi;
                j:= j - 1;
                k:= k - 1;
                l:= l - 1;
            elif j = m - k then    # join
                k:= k + l;
                l:= 0;
                eps:= eps * del;
                del:= 1;
            else                   # pass
                if eps = -1 then
                    if j = l then
                        del:= -del;
                    fi;
                fi;
            fi; 
            
            if del = -1 and j > 0 then
                l:= -l-1;
            fi;
            
            if eps = -1 then
                k:= -k-1;
            fi;
            
            product[m]:= k;
            m:= m - 1;
        od;
    
    od;
    
    return SkylineD(product);
end;
    
SkylineDOps.\*:= function(lft, rgt)
    local   product,  j,  l,  m,  k,  del,  eps;
    
    # check arguments.
    if not IsSkylineD(rgt) or not IsSkylineD(lft) then
        Error("don't know how to compute the product of <lft> and <rgt>");
    fi;
    
    # trivial case.
    if rgt.tower = [] then  return lft;  fi;
    
    # make a fresh copy of lft tower, extend if necessary.
    product:= Copy(lft.tower);
    Append(product, 0*[Length(lft.tower) + 1 .. Length(rgt.tower)]);
    
    # loop over factors of rgt
    for j in [1..Length(rgt.tower)] do
        
        # multiply product with factor rgt.tower[j] = l
        l:= rgt.tower[j];
        if l < 0 then
            del:= -1;
            l:= -l-1;
        else
            del:= 1;
        fi;
        m:= Length(product);
        
        while (l > 0 or del = -1) and m > 0 do
            k:= product[m];
            
            if k < 0 then
                eps:= -1;
                k:= -k-1;
            else
                eps:= 1;
            fi;
            
            # conjugate d_eps(m,k) by t(del)
            if m = k and del = -1 then
                eps:= -eps;
            fi;
                        
            # multiply product.tower[m] = k by tower[j] = l
            if j > m - k + l then  # shift
                j:= j - 1;
            elif j > m - k then    # cancel
                j:= j - 1;
                k:= k - 1;
                l:= l - 1;
            elif j = m - k then    # join
                k:= k + l;
                l:= 0;
                eps:= eps * del;
                del:= 1;
            fi;                    #  pass: do nothing.
            
            # conjugate d_del(j,l) by t(eps)
            if j = l and eps = -1 then
                del:= -del;
            fi;
                        
            if eps = -1 then
                k:= -k-1;
            fi;
            
            product[m]:= k;
            m:= m - 1;
        od;
    
    od;
    
    return SkylineD(product);
end;

#############################################################################
SkylineDWord:= function(word)
    local   prod,  a,  l;
    
    prod:= SkylineD([]);
    for a in word do
        l:= 0*[1..a];
        if a = 0 then
            l[1]:= -2;
        else
            l[a]:= 1;
        fi;
        prod:= prod * SkylineD(l);
    od;
    return prod;
end;


#############################################################################
SkylineDOps.Inverse:= function(self)
    local   inverse,  l,  n,  k,  j,  new;
    
    inverse:= Copy(self.tower);
    l:= Length(inverse);
    
    for n in [l, l-1 .. 1] do
        
        # locate rightmost 0 or -1.
        k:= 0;
        for j in [1..n] do
            if inverse[j] = 0 or inverse[j] = -1 then
                k:= j;
            fi;
        od;
        
        # compute inverse entry
        new:= n - k;
        if k = 0 then
            if inverse[1] < 0 then
                new:= -new-1;
            fi;
        elif k > 0 then
            if inverse[k] < 0 then
                new:= -new-1;
            fi;
        fi;
        
        # shift or adjust remainder of word
        if k > 0 and inverse[k] < 0 then
            for j in [1..k-1] do
                if inverse[j] = j or inverse[j] = -j-1 then
                    inverse[j]:= -inverse[j]-1;
                fi;
            od;
        fi;
                
        for j in [Maximum(k, 1)..n-1] do
            inverse[j]:= inverse[j+1] - SignInt(inverse[j+1]);
        od;
        
        # record inverse entry.
        inverse[n]:= new;
        
    od;
    
    return SkylineD(inverse);
end;

#### HOPEFULLY CORRECT UP TO HERE #####


    
#############################################################################
SkylineDOps.Descents:= function(self)
    local   old,  des,  n,  i,  new;
    
    old:= 0;
    des:= [];
    n:= Length(self.tower);
    for i in [1..n] do
        new:= self.tower[i];
        if new < 0 then
            if old >= 0 then
                Add(des, i-1);
            else
                if new - old >= 0 then
                    Add(des, i-1);
                fi;
            fi;
        else
            if old >= 0 then
                if new - old > 0 then
                    Add(des, i-1);
                fi;
            fi;
        fi;
        old:= new;
    od;
    return des;
end;


#############################################################################
SkylineDOps.SmallestDescent:= function(self)
    return PositionProperty(self.tower, x-> x <> 0) - 1;
end;

    
#############################################################################
SkylineDOps.IsDescent:= function(self, i)
    if i = 0 then
        return self.tower[1] <> 0;
    else
        if self.tower[i+1] < 0 then
            return self.tower[i] >= 0 or self.tower[i+1] >= self.tower[i];
        else
            return self.tower[i] >= 0 and self.tower[i+1] > self.tower[i];
        fi;
    fi;
end;


#############################################################################
##
##  other utiltiy functions for permutations.
##

#############################################################################
##
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
##  FOR EXAMPLE
##
#gen:= [];
#for i in [1..9] do l:= 0*[1..i]; l[i]:= 1; Add(gen, SkylineA(l)); od;
#A:= Group(List(gen, x-> Call(x, "Permutation")), ());
#
#gen:= [SkylineB([-1])];
#for i in [1..9] do l:= 0*[1..i]; l[i+1]:= 1; Add(gen, SkylineB(l)); od;
#B:= Group(List(gen, x-> Call(x, "Permutation")), ());
#
#gen:= [SkylineD([-2])];
#for i in [1..9] do l:= 0*[1..i]; l[i]:= 1; Add(gen, SkylineD(l)); od;
#D:= Group(List(gen, x-> Call(x, "Permutation")), ());
#
#a:= function(m, k)
#    local   lis;
#    lis:= 0*[1..m];
#    lis[m]:= k;
#    return SkylineD(lis);
#end;
#
#b:= function(m, k)
#    local   lis;
#    lis:= 0*[1..m];
#    lis[m]:= -k-1;
#    return SkylineB(lis);
#end;
#
#d:= function(m, k)
#    local   lis;
#    lis:= 0*[1..m];
#    lis[m]:= -k-1;
#    return SkylineD(lis);
#end;
#
#
#m:= function(x, y)
#    return SkylineDPerm(Call(x, "Permutation") * Call(y, "Permutation"));
#end;
#