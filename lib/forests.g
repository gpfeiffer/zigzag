#############################################################################
##
#A  $Id: forests.g,v 1.2 2009/12/16 20:12:27 goetz Exp $
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2009-2010 Götz Pfeiffer
##
##  This file contains routines for trees and forests.
##
##  <#GAPDoc Label="Intro:Forests">
##    Binary trees and forests are convenient data structures to represent alleys and streets in classical types...
##      
##    The functions described in this chapter are implemented in the file
##    <F>forests.g</F>.  
##  <#/GAPDoc>
##

#############################################################################
##  
#O  TreeOps  . . . . . . . . . . . . . . . . . . . operations record.
##  

##  trees first.
TreeOps:= OperationsRecord("TreeOps");

#############################################################################
##  
#C  Tree( <n> )  . . . . . . . . . . . . . . . . .  constructor.
#C  Tree( <i>, <l>, <r> )  . . . . . . . . . . . . . . . . .  constructor.
##  
##  <#GAPDoc Label="Tree">
##  <ManSection>
##  <Func Name="Tree" Arg="n"/>
##  <Func Name="Tree" Arg="i, l, r"/>
##  <Returns>
##    a new tree with components ...
##  </Returns>
##  <Description>
##  This is the simple constructor for  trees ...
##  <Example>
##  gap> Tree(1, Tree(2), Tree(3));
##  [2&lt;1&gt;3]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  A tree is a quadruple with components
##    l, r:  its left and right children
##    i: its *index* (which is 0 if the tree is a leaf)
##    n: its *value* (which is the sum of the values of the children)
##
Tree:= function(arg)
    local self, usage;
    usage:= "Usage: Tree( <n> ) or Tree( <i>, <l>, <r> )";
    if Length(arg) = 1 then
        self:= rec(i:= 0, l:= 0, r:= 0, n:= arg[1]);
    elif Length(arg) = 3 then
        self:= rec(i:= arg[1], l:= arg[2], r:= arg[3]);
        self.n:= self.l.n + self.r.n;
    else
        Error(usage);
    fi;
    self.isTree:= true;
    self.operations:= TreeOps;
    return self;
end;


#############################################################################
##
#F  IsTree( <obj> )  . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsTree">
##  <ManSection>
##  <Func Name="IsTree" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a tree and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsTree:= function(obj)
    return IsRec(obj) and IsBound(obj.isTree) and obj.isTree = true;
end;

#############################################################################
TreeOps.Print:= function(self)
    if self.i = 0 then
        Print(self.n);
    else
        Print("[", self.l, "<", self.i, ">", self.r, "]");
    fi;
end;

# the value of a tree is the sum of the values of its leaves
TreeOps.Value:= self-> self.n;

# the values of a tree is the list of values of its leaves
TreeOps.Values:= function(self)
    if self.i = 0 then
        return [self.n];
    else
        return Concatenation(Call(self.l, "Values"), Call(self.r, "Values"));
    fi;
end;

# returns the list of leaves (as trees)
TreeOps.Leaves:= function(self)
    if self.i = 0 then
        return [self];
    else
        return Concatenation(Call(self.l, "Leaves"), Call(self.r, "Leaves"));
    fi;
end;

# the list of indices on the inner nodes.
TreeOps.Indices:= function(self)
    if self.i = 0 then 
        return [];
    else
        return Concatenation(Call(self.l, "Indices"), [self.i], Call(self.r, "Indices"));
    fi;
end;


# the size of a tree is the number of inner nodes (= number of leaves - 1)
TreeOps.Size:= function(self)
    if self.i = 0 then 
        return 0;
    else
        return Call(self.l, "Size") + 1 + Call(self.r, "Size");
    fi;
end;    

# return a new tree with indices shifted by r.
TreeOps.\^:= function(l, r)
    local   usage;
    
    usage:= "usage: <tree> ^ <int>";
    if not IsTree(l) or not IsInt(r) then
        Error(usage);
    fi;
    
    if l.i = 0 then
        return Tree(l.n);
    else
        return Tree(l.i + r, l.l^r, l.r^r);
    fi;
end;    



##  how to turn a subset of [1..n-1] into a composition of n
##  * find the complement cmp of L in [0..n]
##  * set com[i]:= cmp[i+1] - cmp[i] for i in [1..Length(cmp)-1]  
##  e.g. n = 9, L = 45 7 \subseteq [1..8], 
##        cmp = 0123  6 89, 
##        com =  111  3 21)
##
CompositionSubset:= function(n, set)
    local   cmp;
    cmp:= Difference([0..n], set);
    return List([2..Length(cmp)], i-> cmp[i]-cmp[i-1]);
end;


##  how to turn a composition of n into a subset of [1..n-1]
SubsetComposition:= function(com)
    local   sum,  set,  s;
    sum:= 0;
    set:= [];
    for s in com do
        sum:= sum + s;
        Add(set, sum);
    od;
    return Difference([1..sum], set);
end;


#############################################################################

##  forests next.
ForestOps:= OperationsRecord("ForestOps");


##  a forest is a sequence of trees.
Forest:= function(list)
    local   self;
    
    self:= rec();
    self.list:= list;
    self.isForest:= true;
    self.operations:= ForestOps;
    return self;
end;


IsForest:= function(obj)
    return IsRec(obj) and IsBound(obj.isForest) and obj.isForest = true;
end;

#############################################################################
ForestOps.Print:= function(self)
    Print("Forest( ", self.list, " )");
end;





##  here is how to turn an alley into a forest.
ForestAlley1:= function(n, a)
    local   old,  t,  l,  i,  new,  p;
    
    # start at the bottom, 
    old:= CompositionSubset(n, Difference(a[1], a[2]));
    t:= List(old, Tree);
    
    # loop over the sets above
    l:= Length(a[2]);
    for i in [1..l] do
        new:= CompositionSubset(n, Difference(a[1], a[2]{[1..l-i]}));
        # there is probably a more efficient way to find p.
        p:= First([1..n], k-> new[k] <> old[k]);
        # so new is obtained from old by merging the parts at p and p+1
        t:= Concatenation(
                    t{[1..p-1]},
                    [Tree(i, t[p], t[p+1])],
                    t{[p+2..Length(t)]}
                    );
        old:= new;
    od;
    
    return Forest(t);
end;



# the value of a forest is the list of values of its trees.
# this produces the composition corresponding to the source of the forest.
ForestOps.Value:= function(self)
    return List(self.list, t-> Call(t, "Value"));
end;

#  the values of a forest are the values lists of its trees. 
# this produces the composition corresponding to the target of the forest.
ForestOps.Values:= function(self)
    return Concatenation(List(self.list, t-> Call(t, "Values")));
end;

ForestOps.Leaves:= function(self)
    return Concatenation(List(self.list, t-> Call(t, "Leaves")));
end;

ForestOps.Index:= function(self)
    return Concatenation(List(self.list, t-> Call(t, "Indices")));
end;


ForestOps.Indices:= function(self)
    local   ind,  l;
    
    ind:= [];
    for l in List(self.list, t-> Call(t, "Indices")) do
        Append(ind, l);
        Add(ind, 0);
    od;
    return ind;
end;


ForestOps.Size:= function(self)
    return Sum(self.list, x-> Call(x, "Size"));
end;

ForestOps.Length:= function(self)
    return Length(self.list);
end;


ForestOps.\^:= function(l, r)
    local   usage;
    
    usage:= "usage: <forest> ^ <int>";
    if not IsForest(l) or not IsInt(r) then
        Error(usage);
    fi;
    
    return Forest(List(l.list, t-> t^r));
end;    


ForestOps.\*:= function(l, r)
    local   prod,  leaf,  list,  i,  a;
    
    if not IsForest(l) or not IsForest(r) then
        Error("don't know how to multiply <l> and <r>");
    fi;
    
    # shift indices in l.
    prod:= l^Call(r, "Size");
    
    # replace leaves of l by trees of r if possible.
    leaf:= Call(prod, "Leaves");
    list:= r.list;
    if Length(leaf) <> Length(list) then
        return 0;
    fi;
    
    # loop over the leaf nodes.
    for i in [1..Length(leaf)] do
        if leaf[i].n <> list[i].n then
            return 0;
        fi;
        
        # attach tree to leaf node with same n-value.
        for a in "irl" do
            leaf[i].([a]):= list[i].([a]);      #;-)
        od;
    od;
    
    # return result.
    return prod;
    
end;


#############################################################################
##  how to turn [L; s] into a forest:
##  * find complement cmp of L in [0..n]
##  * set com[i]:= cmp[i+1] - cmp[i] 
##  * let k be the number of t in cmp which are strictly smaller than s
##  * replace com[k] by a tree with leaves s-cmp[k] and cmp[k+1]-s.
##  this works since the complement of L-s in [0..n] differs from 
##  the complemnt of L by an extra entry s, between cmp[k] and cmp[k+1].
##
ForestLs:= function(n, L, s)
    local   cmp,  com,  k;
    
    cmp:= Difference([0..n], L);
    com:= List([2..Length(cmp)], i-> Tree(cmp[i]-cmp[i-1]));
    k:= Number(cmp, t-> t < s);
    com[k]:= Tree(1, Tree(s - cmp[k]), Tree(cmp[k+1] - s));
    return Forest(com);
end;

ForestAlley:= function(n, a)
    local   f,  b;
    
    f:= Forest(List(CompositionSubset(n, a[1]), Tree));
    if a[2] = [] then 
        return f; 
    fi;
    
    for b in FactorsAlley(a) do
        f:= f * ForestLs(n, b[1], b[2][1]);
    od;
    
    return f;
end;


##  how to turn a forest into an alley.
ForestOps.Alley:= function(self)
    local   l,  m,  i,  v,  n,  set,  bar,  new;
    l:= Call(self, "Indices");
    m:= [];
    for i in [1..Length(l)] do
        if l[i] > 0 then 
            m[l[i]]:= i; 
        fi; 
    od;
    v:= Call(self, "Values");
    n:= Sum(v);
    set:= SubsetComposition(v);
    bar:= Difference([1..n-1], set);
    new:= bar{m};
    return [Union(set, new), Reversed(new)];
end;

ForestOps.Factors:= function(self)
    local   n;
    n:= Sum(Call(self, "Value"));
    return List(FactorsAlley(Call(self, "Alley")), x-> ForestAlley(n, x));
end;


#    each Lyndon word w of length > 1 has a standard factorization
#    w = l m into nonempty Lyndon words l and m such that m has maximal length
StandardFactorizationLyndon:= function(word)
    local   lastFactor,  n,  m,  l;

    # The last factor is the lexicographically smallest tail of list.
    lastFactor:= function(list)
        local l, tail;
        l:= Length(list);
        tail:= List([1..l], i-> list{[i..l]});
        Sort(tail);
        return tail[1];
    end;
    
    n:= Length(word);
    if n < 2 then  return word;  fi;
    m:= Length(lastFactor(word{[2..n]}));
    l:= n-m;
    return [word{[1..l]}, word{[l+1..n]}];
end;
    
StandardBracketingLyndon1:= function(word)
    local   lastFactor,  n,  m,  l;

    # The last factor is the lexicographically smallest tail of list.
    lastFactor:= function(list)
        local l, tail;
        l:= Length(list);
        tail:= List([1..l], i-> list{[i..l]});
        Sort(tail);
        return tail[1];
    end;
    
    n:= Length(word);
    if n = 0 then  return word;  fi;
    if n = 1 then  return word[1];  fi;
    m:= Length(lastFactor(word{[2..n]}));
    l:= n-m;
    return List([word{[1..l]}, word{[l+1..n]}], StandardBracketingLyndon);
end;


# index is the last label used. so the next one is at least one more.
StandardBracketingLyndon:= function(word, index)
    local   lastFactor,  n,  m,  l,  r;

    # The last factor is the lexicographically smallest tail of list.
    lastFactor:= function(list)
        local l, tail;
        l:= Length(list);
        tail:= List([1..l], i-> list{[i..l]});
        Sort(tail);
        return tail[1];
    end;
    
    n:= Length(word);
    if n = 1 then  return Tree(word[1]);  fi;
    m:= n - Length(lastFactor(word{[2..n]}));
    
    l:= StandardBracketingLyndon(word{[1..m]}, index);
    if l.i > 0 then  index:= l.i;  fi;
    r:= StandardBracketingLyndon(word{[m+1..n]}, index);
    if r.i > 0 then  index:= r.i;  fi;
    
    return Tree(index+1, l, r);
end;

StandardBracketing:= function(word)
    local   index,  lyndon,  list,  factor,  tree;
    
    index:= 0;
    lyndon:= LyndonFactorisation(word);
    list:= [];
    for factor in lyndon do
        tree:= StandardBracketingLyndon(factor, index);
        Add(list, tree);
        if tree.i > 0 then 
            index:= tree.i;
        fi;
    od;
    return Forest(list);
end;


# a basis for the descent algebra of S_n (type A_{n-1}).
LyndonBasis:= function(n)
    local   basis,  W,  p,  q;
    
    basis:= [];
    W:= CoxeterGroup("A", n-1);
    for p in Partitions(n) do
        for q in Arrangements(p, Length(p)) do
            Add(basis, Street(W, Call(StandardBracketing(q), "Alley")));
        od;
    od;
    return basis;
end;


IsCompletelyReducibleStreet:= function(alpha)
    local   a,  W,  f,  s,  i;
    a:= Representative(alpha);
    W:= alpha.W;
    f:= FactorsAlley(a);
    s:= Street(W, f[1]);
    for i in [2..Length(f)] do
        s:= s * Street(W, f[i]);
        if Length(s) > 1 then
            return false;
        fi;
        s:= s[1];
    od;
    return s = alpha;
end;



a:= [[2,3,4,5,8,9,11], [4, 5, 8, 3, 11]];
f:= ForestAlley(12, a);

