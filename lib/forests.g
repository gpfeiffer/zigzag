#############################################################################
##
#A  forests.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
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
##  TODO: rename Tree to BTree, BinTree, BinaryTree?
##


#############################################################################
##  
#O  LeanTreeOps  . . . . . . . . . . . . . . . . . . . operations record.
##  
##  A lean tree is a tree w/o inner node labels.
##
LeanTreeOps:= OperationsRecord("LeanTreeOps");

#############################################################################
##  
#C  LeanTree( <n> )  . . . . . . . . . . . . . . . . .  constructor.
#C  LeanTree( <l>, <r> )  . . . . . . . . . . . . . . . . .  constructor.
##  
##  <#GAPDoc Label="LeanTree">
##  <ManSection>
##  <Func Name="LeanTree" Arg="n"/>
##  <Func Name="LeanTree" Arg="l, r"/>
##  <Returns>
##    a new lean tree with components ...
##  </Returns>
##  <Description>
##  This is the simple constructor for lean trees ...
##  <Example>
##  gap> LeanTree(LeanTree(2), LeanTree(3));
##  [2^3]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  A lean tree is a triple with components
##    l, r:  its left and right children (or 0 if its a leaf)
##    n: its *value* (or top) (which is the sum of the values of the children, ie., its bottom)
##
LeanTree:= function(arg)
    local self, usage;
    usage:= "Usage: LeanTree( <n> ) or LeanTree( <l>, <r> )";
    if Length(arg) = 1 then
        self:= rec(l:= 0, r:= 0, n:= arg[1]);
    elif Length(arg) = 2 then
        self:= rec(l:= arg[1], r:= arg[2]);
        self.n:= self.l.n + self.r.n;
    else
        Error(usage);
    fi;
    self.isLeanTree:= true;
    self.operations:= LeanTreeOps;
    return self;
end;


#############################################################################
##
#F  IsLeanTree( <obj> )  . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsLeanTree">
##  <ManSection>
##  <Func Name="IsLeanTree" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a lean tree and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsLeanTree:= function(obj)
    return IsRec(obj) and IsBound(obj.isLeanTree) and obj.isLeanTree = true;
end;

#############################################################################
LeanTreeOps.Print:= function(self)
    if self.l = 0 then
        Print(self.n);
    else
        Print("[", self.l, "^", self.r, "]");
    fi;
end;

#############################################################################
#  how to sort lean trees.
LeanTreeOps.\<:= function(l, r)
    if not IsLeanTree(l) then return true; fi;
    if not IsLeanTree(r) then return false; fi;
    if l.n = r.n then 
        if Call(l, "Size") = Call(r, "Size") then
            return l.l < r.l or (l.l = r.l and l.r < r.r);
        else
            return Call(l, "Size") > Call(r, "Size");
        fi;
    else
        return l.n < r.n;
    fi;
end;


#############################################################################

# the value of a tree is the sum of its bottom
LeanTreeOps.Top:= self-> self.n;

# the bottom of a tree is the list of its leaves (as integers).
LeanTreeOps.Bot:= function(self)
    if self.l = 0 then
        return [self.n];
    else
        return Concatenation(Call(self.l, "Bot"), Call(self.r, "Bot"));
    fi;
end;

# returns the list of leaves (as lean trees)
LeanTreeOps.Leaves:= function(self)
    if self.l = 0 then
        return [self];
    else
        return Concatenation(Call(self.l, "Leaves"), Call(self.r, "Leaves"));
    fi;
end;

# returns the (sorted) list of all subtrees (as lean trees)
LeanTreeOps.SubTrees:= function(self)
    local list;
    list:= [self];
    if self.l <> 0 then
        Append(list, Call(self.l, "SubTrees"));
        Append(list, Call(self.r, "SubTrees"));
    fi;
    Sort(list);
    return list;
end;

# the profile of a tree is the partition obtained as values of all subtree.
# (this is a partition of what number?)
# (note that paths in the partition quiver have profiles, too)
LeanTreeOps.Profile:= function(self)
    return List(Call(self, "SubTrees"), x-> Call(x, "Top"));
end;


# the size of a lean tree is the number of inner nodes (= number of leaves - 1)
LeanTreeOps.Size:= function(self)
    if self.l = 0 then 
        return 0;
    else
        return Call(self.l, "Size") + 1 + Call(self.r, "Size");
    fi;
end;    


#############################################################################
##
##  swap l and r.
##
LeanTreeOps.Flipped:= function(self)
    local   new,  m;
    new:= Copy(self);
    m:= new.l;
    new.l:= new.r;
    new.r:= m;
    return new;
end;

#############################################################################
##
##  reverse order of leaves ...
##
LeanTreeOps.CoTree:= function(self)
    local   new,  m;
    new:= Copy(self);
    if new.l <> 0 then
        m:= Call(new.l, "CoTree");
        new.l:= Call(new.r, "CoTree");
        new.r:= m;
    fi;
    return new;
end;


#############################################################################
IsSlanted:= function(obj)
    return obj.operations.IsSlanted(obj);
end;


#############################################################################
##
##  a tree is slanted if it is either a leaf or it has slanted children of
##  increasing values.
##
LeanTreeOps.IsSlanted:= function(self)
    # leaves are slanted; otherwise left child weighs less than right. 
    if self.l = 0 then
        return true;
    elif self.l.n < self.r.n then
        return IsSlanted(self.l) and IsSlanted(self.r);
    else
        return false;
    fi;
end;    

##  make all lean trees of value n
LeanTrees:= function(n)
    local   all,  i,  a,  b;
    
    all:= [LeanTree(n)];
    for i in [1..n-1] do
        for a in LeanTrees(i) do
            for b in LeanTrees(n-i) do
                Add(all, LeanTree(a, b));
            od;
        od;
    od;
    Sort(all);
    return all;
end;


##  number of lean trees.  This is A007317 in the OEIS.
NrLeanTrees:= function(n)
    return Sum([1..n-1], i->  NrLeanTrees(i) * NrLeanTrees(n-i)) + 1;
end;


##  make all slanted lean trees of value n
SlantedLeanTrees:= function(n)
    local   all,  i,  a,  b;
    
    all:= [LeanTree(n)];
    for i in [1..Int((n-1)/2)] do
        for a in SlantedLeanTrees(i) do
            for b in SlantedLeanTrees(n-i) do
                Add(all, LeanTree(a, b));
            od;
        od;
    od;
    Sort(all);
    return all;
end;


##  number of slanted lean trees.  this sequence is not in the OEIS!!
NrSlantedLeanTrees:= function(n)
    return Sum([1..Int((n-1)/2)], i-> NrSlantedLeanTrees(i) * NrSlantedLeanTrees(n-i)) + 1;
end;


#############################################################################
##
##  children.  for walker.g
##
LeanTreeOps.Children:= function(self)
    if self.l = 0 then
        return [];
    else
        return [self.l, self.r];
    fi;
end;

            

#############################################################################

## lean forests next.
LeanForestOps:= OperationsRecord("LeanForestOps");


##  a lean forest is a sequence of lean trees.
LeanForest:= function(list)
    local   self;
    
    self:= rec();
    self.list:= list;
    self.isLeanForest:= true;
    self.operations:= LeanForestOps;
    return self;
end;


IsLeanForest:= function(obj)
    return IsRec(obj) and IsBound(obj.isLeanForest) and obj.isLeanForest = true;
end;

#############################################################################
LeanForestOps.Print:= function(self)
    Print("LeanForest( ", self.list, " )");
end;

#############################################################################
##
##  the top of a forest is the list of tops of its trees.
##  this produces the composition corresponding to the source of the forest.
##
LeanForestOps.Top:= function(self)
    return List(self.list, t-> Call(t, "Top"));
end;

#  the bottom of a forest is the joined bottoms of its trees. 
# this produces the composition corresponding to the target of the forest.
LeanForestOps.Bot:= function(self)
    return Concatenation(List(self.list, t-> Call(t, "Bot")));
end;

LeanForestOps.Leaves:= function(self)
    return Concatenation(List(self.list, t-> Call(t, "Leaves")));
end;

LeanForestOps.SubTrees:= function(self)
    local list;
    list:= Concatenation(List(self.list, x-> Call(x, "SubTrees")));
    Sort(list);
    return list;
end;

LeanForestOps.Profile:= function(self)
    return List(Call(self, "SubTrees"), x-> Call(x, "Top"));
end;


LeanForestOps.Size:= function(self)
    return Sum(self.list, x-> Call(x, "Size"));
end;

LeanForestOps.Length:= function(self)
    return Length(self.list);
end;


#############################################################################
##
##  Products of lean forests.
##
LeanForestOps.\*:= function(l, r)
    local   prod,  leaf,  list,  i,  a;
    
    if not IsLeanForest(l) or not IsLeanForest(r) then
        Error("don't know how to multiply <l> and <r>");
    fi;
    
    prod:= Copy(l);
    
    # replace leaves of l by trees of r if possible.
    leaf:= Call(prod, "Leaves");
    list:= r.list;
    if Length(leaf) <> Length(list) then
        return false;
    fi;
    
    # loop over the leaf nodes.
    for i in [1..Length(leaf)] do
        if leaf[i].n <> list[i].n then
            return false;
        fi;
        
        # attach tree to leaf node with same n-value.
        for a in "rl" do
            leaf[i].([a]):= list[i].([a]);      #;-)
        od;
    od;
    
    # return result.
    return prod;
end;


#############################################################################
LeanForestOps.IsSlanted:= function(self)
    return ForAll(self.list, x-> Call(x, "IsSlanted"));
end;

# make all lean forests of total value n
LeanForests:= function(n)
    local   all,  p,  q;
    
    all:= [];
    for p in Partitions(n) do
        for q in Arrangements(p, Length(p)) do
            Append(all, List(Cartesian(List(q, LeanTrees)), LeanForest));
        od;
    od;
    Sort(all);
    return all;
end;


# make all slanted lean forests of total value n
SlantedLeanForests:= function(n)
    local   all,  p,  q;
    
    all:= [];
    for p in Partitions(n) do
        for q in Arrangements(p, Length(p)) do
            Append(all, List(Cartesian(List(q, SlantedLeanTrees)), LeanForest));
        od;
    od;
    Sort(all);
    return all;
end;

# make all sorted slanted lean forests of total value n
SortedSlantedLeanForests:= function(n)
    local   all,  p,  new,  q;
    
    all:= [];
    for p in Partitions(n) do
        new:= Cartesian(List(p, SlantedLeanTrees));
        for q in new do
            Sort(q);
        od;
        Append(all, List(Set(new), LeanForest));
    od;
    return all;
end;

#############################################################################
CartanMatSortedSlantedLeanForests:= function(n)
    local   W,  lab,  mat,  a,  i,  j;
    
    W:= CoxeterGroup("A", n-1);
    lab:= LabelsShapes(Shapes(W));
    mat:= 0*IdentityMat(Length(lab));
    for a in SortedSlantedLeanForests(n) do
        i:= Call(a, "Top");
        Sort(i);
        i:= Position(lab, Reversed(i));
        j:= Call(a, "Bot");
        Sort(j);
        j:= Position(lab, Reversed(j));
        mat[i][j]:= mat[i][j] + 1;
    od;
    return mat;
end;


##  Suffixes
##  in contrast to a forest, a lean forest can have several suffixes.
LeanForestOps.Suffixes:= function(self)
    local   lis,  t,  i,  suf;
    
    lis:= [];
    t:= self.list;
    
    for i in [1..Length(t)] do
        if t[i].l <> 0 then
            suf:= Concatenation(t{[1..i]}, [0], t{[i+1..Length(t)]});
            suf{[i, i+1]}:= [t[i].l, t[i].r];
            Add(lis, LeanForest(suf));
        fi;
    od;
    
    return lis;
end;


#############################################################################
##
##  an orphan is a subtree that has neither children nor parents ...
##
LeanForestOps.Orphans:= function(self)
    local   orp;
    orp:= Filtered(self.list, t-> t.l = 0);
    return List(orp, t-> t.n);
end;

        
#############################################################################
##
##  how to insert labels into a lean forest
##
LeanForestOps.InverseLean:= function(self)
    local   lis,  t,  val,  flat,  i,  e,  suf;
    
    lis:= [];
    t:= self.list;
    val:= List(Call(self, "Top"), Tree);
    
    flat:= true;
    for i in [1..Length(t)] do
        if t[i].l <> 0 then
            flat:= false;
            e:= Copy(val);
            e[i]:= Tree(1, Tree(Call(t[i].l, "Top")), 
                        Tree(Call(t[i].r, "Top")));
            e:= Forest(e);
            suf:= Concatenation(t{[1..i]}, [0], t{[i+1..Length(t)]});
            suf{[i, i+1]}:= [t[i].l, t[i].r];
            Append(lis, List(Call(LeanForest(suf), "InverseLean"), 
                    x-> e * x));
        fi;
    od;
    
    if flat then
        Add(lis, Forest(val));
    fi;        

    return lis;
end;

# canonically labelled tree -- postfix order.
LeanForestOps.CanonicalLabels:= function(self)
    local   lab,  treeLabels;
    
    lab:= 0;
    
    treeLabels:= function(t)
        local   l,  r;
        if t.l = 0 then
            return Tree(t.n);
        else
            l:= treeLabels(t.l);
            r:= treeLabels(t.r);
            lab:= lab + 1;
            return Tree(lab, l, r);
        fi;
    end;
    
    return Forest(List(self.list, treeLabels));
end;
 
# favorably labelled tree -- prefix order.
LeanForestOps.FavoriteLabels:= function(self)
    local   lab,  treeLabels;
    
    lab:= 0;
    
    treeLabels:= function(t)
        local   l,  r;
        if t.l = 0 then
            return Tree(t.n);
        else
            r:= treeLabels(t.r);
            l:= treeLabels(t.l);
            lab:= lab + 1;
            return Tree(lab, l, r);
        fi;
    end;
    
    return Forest(Reversed(List(Reversed(self.list), treeLabels)));
end;
 


#############################################################################
##  the multiplier of f is m = #[InverseLean(f)] / #[f]
LeanForestOps.Multiplier:= function(self)
    local   szStab;
    
    # how to find the size of the arrangement stabilizer
    szStab:= function(obj)
        return Product(Collected(obj.list), x-> Factorial(x[2]));
    end;
    
    return szStab(self) / szStab(Call(self, "CanonicalLabels"));
end;

##
##   suppose that QuiverElt(q, c, e)
##   represents an element of the path algebra of the quiver q
##   with coefficients c applied to the paths e 
##   and that we can add and multiply them ...
##

# find a linear combination of paths in the quiver q that maps to the class of this lean forest.
# this is Marcus's factorize-adjust.
# returns: an element of the path algebra in the form of a list of paths (as indices in q.path1) in parallel to a list of coeffs
LeanForestOps.Path:= function(self, q)
    local   edge,  positionMin,  l,  top,  poss,  pos,  t,  x,  z,  w,  
            xtop,  ztop,  wtop,  xbot,  zbot,  p1,  p2,  p,  xztop,  
            posx,  xpol,  posz,  zpol,  v,  vtop;
    
    # given a forest of size 1, find the corresponding edge in the quiver
    edge:= function(f)
        local   a,  pos;
        a:= Call(Call(f, "CanonicalLabels"), "Alley");
        pos:= PositionProperty(q.path1, e-> a in e);
        if pos <> false then
            return QuiverElt(q, [1], [[pos]]);
        fi;
        
        a:= Call(Call(f, "Reversed"), "Alley");
        pos:= PositionProperty(q.path1, e-> a in e);
        if pos <> false then
            return QuiverElt(q, [-1], [[pos]]);
        fi;
        
        Error("Edge  not found");
    end;
    
    # how to find the position of a minimal tree
    positionMin:= function(list)
        local   pos,  i;
        if Length(list) = 0 then
            Error( "<list> must contain at least one element" );
        fi;
        pos:= 1;
        for i in [2..Length(list)] do
            if list[i] < list[pos] then
                pos:= i;
            fi;
        od;
        return pos;
    end;
    
    l:= Call(self, "Size");
    if l = 0 then
        return rec(path:= [], coef:= []); # FIXME: should this not be an idempotent?  maybe not, for paths of length 0 this question might never arise ...
    elif l = 1 then 
        return edge(self); # FIXME: the corresponding edge in q (or its reverse)
    else      # l > 1
        
        # find minimal tree x^z and write self as x^z w
        top:= Call(self, "Top");
        poss:= Filtered([1..Length(self.list)], i-> self.list[i].l > 0);
        pos:= positionMin(top{poss});
        pos:= poss[pos];
        
        t:= self.list[pos];
        x:= t.l;
        z:= t.r;
        
        w:= self.list{Difference([1..Length(self.list)], [pos])};
        
        xtop:= LeanTree(Call(x, "Top"));
        ztop:= LeanTree(Call(z, "Top"));
        wtop:= List(w, t-> LeanTree(Call(t, "Top")));
        
        xbot:= List(Call(x, "Bot"), LeanTree);
        zbot:= List(Call(z, "Bot"), LeanTree);
        
        
        # make p
        p1:= LeanForest(Concatenation([LeanTree(xtop, ztop)], wtop));
        p2:= LeanForest(Concatenation([x, z], w));
        p:= ApplyMethod(p1, "Path", q) * ApplyMethod(p2, "Path", q);
        
        xztop:= LeanTree(Call(x, "Top") + Call(z, "Top"));
        
        # check pollination status
        posx:= Position(w, xtop);
        xpol:=  x.l > 0  and  posx <> false;
        
        posz:= Position(w, ztop);
        zpol:=  z.l > 0  and  posz <> false;
        
        # make px
        if xpol then
            v:= w{Difference([1..Length(w)], [posx])};
            vtop:= List(v, t-> LeanTree(Call(t, "Top")));
            
            p1:= LeanForest(Concatenation([xztop, x], vtop));
            p2:= LeanForest(Concatenation([LeanTree(xtop, z)], xbot, v));
            p:= p - ApplyMethod(p1, "Path", q) * ApplyMethod(p2, "Path", q);
        fi;
        
        # make pz
        if zpol then
            v:= w{Difference([1..Length(w)], [posz])};
            vtop:= List(v, t-> LeanTree(Call(t, "Top")));
            
            p1:= LeanForest(Concatenation([xztop, z], vtop));
            p2:= LeanForest(Concatenation([LeanTree(x, ztop)], zbot, v));
            p:= p - ApplyMethod(p1, "Path", q) * ApplyMethod(p2, "Path", q);
        fi;
        
        # make pxz
        if xpol and zpol then
            v:= w{Difference([1..Length(w)], [posx, posz])};
            vtop:= List(v, t-> LeanTree(Call(t, "Top")));
            
            p1:= LeanForest(Concatenation([xztop, x, z], vtop));
            p2:= LeanForest(Concatenation([LeanTree(xtop, ztop)], xbot, zbot, v));
            p:= p - ApplyMethod(p1, "Path", q) * ApplyMethod(p2, "Path", q);
        fi;            
        
        return p;
    fi;
end;


#############################################################################
##  
#O  TreeOps  . . . . . . . . . . . . . . . . . . . operations record.
##
##  inherits from LeanTree
##
TreeOps:= OperationsRecord("TreeOps", LeanTreeOps);

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
##    n: its *value* (top) (which is the sum of the values of the children)
##
##  A tree is *not* a lean tree! (So we don't use a LeanTree
##  constructor, don't set isLeanTree property.)
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
##
##  Print( <tree> ) . . . . . . . . . . . . . . . . . . . . . . . . . print.
##
TreeOps.Print:= function(self)
    if self.i = 0 then
        Print(self.n);
    else
        Print("[", self.l, "<", self.i, ">", self.r, "]");
    fi;
end;



#############################################################################
TreeOps.\=:= function(l, r)
    if not (IsTree(l) and IsTree(r)) then return false; fi;
    return l.n = r.n and l.i = r.i and l.l = r.l and l.r = r.r;
end;


#############################################################################
#  how to sort trees.
TreeOps.\<:= function(l, r)
    if not IsTree(l) then return true; fi;
    if not IsTree(r) then return false; fi;
    if l.n = r.n then 
        if Call(l, "Size") = Call(r, "Size") then
            if l.i = r.i then
                return l.l < r.l or (l.l = r.l and l.r < r.r);
            else
                return l.i < r.i;
            fi;
        else
            return Call(l, "Size") > Call(r, "Size");
        fi;
    else
        return l.n < r.n;
    fi;
end;


#############################################################################
##
##  Draw( <tree> ) . . . . . . . . . . . . . . . . . . . . . . . . . print.
##
##  produce input for tikz.
##
TreeOps.Draw:= function(self, of, ht)
    local   leaf,  inner,  x,  res,  xl,  xr;
    
    leaf:= function(x, y, label)
        Print("\\draw (", x, ",", y, ") node (", x, ") {$_{", label, "}$};\n");
    end;
    
    inner:= function(x, y, l, r, label)
        Print("\\draw (", x, ",", y, ") node[p] (", x, ") {$_{_{", label, "}}$} edge (", l, ") edge (", r, ");\n");
    end;
    
    if self.i = 0 then  # leaf case
#        Print("% draw leaf ", self.n, " at (", of, ", ", ht, ").\n");
        leaf(of, ht, self.n);
        x:= of;
        of:= of + 1;
    else
        res:= ApplyMethod(self.l, "Draw", of, ht-1);
        of:= res[2];
        xl:= res[1];
        x:= of;
        res:= ApplyMethod(self.r, "Draw", of+1, ht-1);
        xr:=res[1];
        of:= res[2];
#        Print("% draw inner ", self.i, " at (", x, ", ", ht, ").\n");
#        Print("% and join to ", xl, " and ", xr, ".\n");
        inner(x, ht, xl, xr, self.i);
    fi;
    return [x, of];
end;


#############################################################################
##
##  Trees also have indices ...
##
# the list of indices on the inner nodes.
TreeOps.IndicesPostfix:= function(self)
    if self.i = 0 then 
        return [];
    else
        # postfix order!
        return Concatenation(Call(self.l, "IndicesPostfix"), 
                       Call(self.r, "IndicesPostfix"),
                       [self.i]);
    fi;
end;

TreeOps.Indices:= function(self)
    if self.i = 0 then 
        return [];
    else
        # prefix order!
        return Concatenation(
                       [self.i],
                       Call(self.l, "Indices"), 
                       Call(self.r, "Indices")
                       );
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


#############################################################################
##
##  how to forget the labels.
##
TreeOps.Lean:= function(self)
    if self.l = 0 then 
        return LeanTree(self.n);
    else
        return LeanTree(Call(self.l, "Lean"), Call(self.r, "Lean"));
    fi;
end;

##  FIXME:  conversely:  how to put the labels in a lean tree?
##  default way;  all possible ways ....




#############################################################################
##
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
##
##  inherit from LeanForest
##
ForestOps:= OperationsRecord("ForestOps", LeanForestOps);


##  a forest is a sequence of trees.
##  a Forest is *not* a LeanForest
##
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


#############################################################################
##
##  Forest also have indices.
##
ForestOps.Index:= function(self)
    return Concatenation(List(self.list, t-> Call(t, "Indices")));
end;


ForestOps.IndicesPostfix:= function(self)
    local   ind,  l;
    
    ind:= [];
    for l in List(self.list, t-> Call(t, "IndicesPostfix")) do
        Append(ind, l);
        Add(ind, 0);
    od;
    return ind;
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


ForestOps.\^:= function(l, r)
    local   usage;
    
    usage:= "usage: <forest> ^ <int>";
    if not IsForest(l) or not IsInt(r) then
        Error(usage);
    fi;
    
    return Forest(List(l.list, t-> t^r));
end;    

#############################################################################
##
##  Reverse as Street/Alley
##
ForestOps.Reversed:= function(self)
    local   pos,  max,  k,  new,  t;
    
    # locate highest tree.
    pos:= 0;
    max:= 0;
    for k in [1..Length(self.list)] do
        if self.list[k].i > max then
            pos:= k;
            max:= self.list[k].i;
        fi;
    od;
    
    if pos = 0 then
        Error("Cannot reverse forest of size 0");
    fi;
    
    new:= Copy(self.list);
    new[pos]:= Call(new[pos], "Flipped");
    
    return Forest(new);
end;

    
    
#############################################################################
##
##  x.Split(i) replaces x_i = u^v by  u, v
##
ForestOps.Split:= function(self, i)
    local   new;
    
    new:= self.list{[1..i-1]};
    Add(new, self.list[i].l);
    Add(new, self.list[i].r);
    Append(new, self.list{[i+1..Length(self.list)]});
    return Forest(new);
end;

# a labelled forest has a unique suffix.
# (note this depends on ordering of labels.)
ForestOps.Suffix:= function(self)
    local   i;
    i:= Call(self, "Size");
    i:= PositionProperty(self.list, t-> t.i = i);
    return ApplyMethod(self, "Split", i);
end;

##  Suffixes
##  replaces method inherited from LeanForestOps
ForestOps.Suffixes:= function(self)
    return [Call(self, "Suffix")];
end;

#############################################################################
##
##  x.Join(i, l) replaces x_i, x_{i+1} by x_i /l\ x_{i+1}
##
ForestOps.Join:= function(self, i, l)
    local   new;
    
    new:= self.list{[1..i-1]};
    Add(new, Tree(l, self.list[i], self.list[i+1]));
    Append(new, self.list{[i+2..Length(self.list)]});
    return Forest(new);
end;

    
#############################################################################
##
##  Products of forests.
##
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
        return false;
    fi;
    
    # loop over the leaf nodes.
    for i in [1..Length(leaf)] do
        if leaf[i].n <> list[i].n then
            return false;
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
##
##  how to turn an alley into a forest.
##
ForestAlley:= function(n, a)
    local   s,  k;
    
    # trivial case first
    if a[2] = []  then  
        return Forest(List(CompositionSubset(n, a[1]), Tree)); 
    fi;
    
    # otherwise recurse,
    s:= a[2][1];
    k:= s + 1 - Position(a[1], s); # = position of s in the complement of L_s
    return ApplyMethod(ForestAlley(n, SuffixAlley(a)), "Join", k, Length(a[2]));

end;


#############################################################################
##  the list of compositions travelled trough by a forest.
ForestOps.Compositions:= function(self)
    local   list;
    list:= [Call(self, "Top")];
    if Call(self, "Size") = 0 then
        return list;
    fi;
    Append(list, Call(Call(self, "Suffix"), "Compositions"));
    return list;
end;

#############################################################################
##  how to turn a forest into an alley.
ForestOps.Alley:= function(self)
    return AlleySubsets(List(Call(self, "Compositions"), SubsetComposition));
end;

#############################################################################
ForestOps.Factors:= function(self)
    local   n;
    n:= Sum(Call(self, "Top"));
    return List(FactorsAlley(Call(self, "Alley")), x-> ForestAlley(n, x));
end;

ForestOps.Factors:= function(self)
    local   pos,  max,  i,  new,  one;
    
    # short forests only have one factor.
    if Call(self, "Size") < 2 then
        return [self];
    fi;
    
    # otherwise, locate maximum and split.
    pos:= 1;
    max:= self.list[pos].i;
    for i in [2..Length(self.list)] do
        if self.list[i].i > max then
            pos:= i;
            max:= self.list[pos].i;
        fi;
    od;
    
    new:= Forest(Concatenation(self.list{[1..pos-1]},
            [self.list[pos].l, self.list[pos].r],
                  self.list{[pos+1..Length(self.list)]}));
    
    one:= Forest(List(self.list, x-> Tree(x.n)));
    one.list[pos]:= Tree(1, Tree(self.list[pos].l.n), Tree(self.list[pos].r.n));
    
    return Concatenation([one], Call(new, "Factors"));            
end;



#############################################################################
ForestOps.IsSlanted:= function(self)
    return ForAll(self.list, x-> Call(x, "IsSlanted"));
end;

#############################################################################
##
##  how to forget all the indices.
##
ForestOps.Lean:= function(self)
    return LeanForest(List(self.list, x-> Call(x, "Lean")));
end;


#############################################################################
ForestOps.Draw:= function(self)
    local   mittendrin,  t;
    
    mittendrin:= false;
    for t in self.list do
        if mittendrin then
            Print("\\,\n");
        fi;
        Print("\\begin{tikzpicture}\n");
        ApplyMethod(t, "Draw", 0, 1);
        Print("\\end{tikzpicture}");
        mittendrin:= true;
    od;
    Print("\n");
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

# a basis of paths for the descent algebra of S_n (type A_{n-1}).
LyndonPaths:= function(n)
    local   basis,  W,  p,  q,  a;
    
    basis:= [];
    W:= CoxeterGroup("A", n-1);
    for p in Partitions(n) do
        for q in Arrangements(p, Length(p)) do
            a:=  Call(StandardBracketing(q), "Alley");
            Add(basis, List(FactorsAlley(a), x-> Street(W, x)));
        od;
    od;
    return basis;
end;


#
# prefers:          over:
#
# 6                 6                   6                    6
#                                      / \                  / \
# 51                42                2   4                1   5
#                                        / \                  / \
# 321               321                 1   3                3   2
#                                          / \              / \
# 2211              2211                  1   2            1   2
#           



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


#### for example:
#
# a:= [[2,3,4,5,8,9,11], [4, 5, 8, 3, 11]];
# f:= ForestAlley(12, a);

#############################################################################
##
##  express relations in the type A_{n-1} quiver
##
NiceRelationsSym:= function(n)
    local   W,  lab,  q,  r,  rel,  a,  p,  pos;
    
    W:= CoxeterGroup("A", n-1);
    lab:= LabelsShapes(Shapes(W));
    q:= DescentQuiver(W);
    r:= RelationsDescentQuiver(q);
    
    rel:= [];
    for a in r do
        p:= q.pathmat[a[1]][a[2]].path;
        p:= List(p, x-> q.path1{x});
        pos:= Filtered([1..Length(a[3])], i-> a[3][i] <> 0);
        p:= List(p{pos}, ProductStreets);
        p:= List(p, x-> List(x, y-> ForestAlley(n, y.alley)));
        Add(rel, rec(
                from:= lab[a[2]], to:= lab[a[1]],
                path:= p, coef:= a[3]{pos}));
    od;
    
    return rel;
end;

DrawNiceRelation:= function(r)
    local   i,  p,  c,  o,  j;
    
    for i in [1..Length(r.path)] do
        p:= r.path[i];
        c:= r.coef[i];
        o:= "+";
        
        # print coeff, omit 1s.
        if c < 0 then
            o:= "-";
            c:= -c;
        fi;

        if c = 1 then
            c:= "";
        fi;
        
        Print(o, " ", c, "\n");
        Print("(");
        Call(p[1], "Draw");
        for j in [2..Length(p)] do
            Print("+\n");
            Call(p[j], "Draw");
        od;
        Print(")\n");
    od;    
    Print("& = 0.\n");
end;

##  a nice relation is core if it is not obtained from a smaller n
##  by adding parts.
IsCoreNiceRelation:= function(r)
    local   l;
    
    l:= List(r.path, p-> List(p, x-> Call(x, "Orphans")));
    l:= List(l, Intersection);
    return Intersection(l) = [];
end;


#############################################################################
##
##  LeanForest Classes.
##
##  the class of a lean forest consists of all of its rearrangements.
##

###############################################################################
##  
#O  LeanForestClassOps  . . . . . . . . . . . . . . . . . . . operations record.
##  
##  inherit from Domain so that set operations apply ...
##
LeanForestClassOps:= OperationsRecord("LeanForestClassOps", DomainOps);

#############################################################################
##
#C  LeanForestClass( <forest> ) . . . . . . . . . . . . . . . .  constructor.
##
##  stores the sorted list of trees!
##  FIXME: check arguments?
##
LeanForestClass:= function(forest)
    local   self,  list;

    if IsLeanForest(forest) then
        list:= Copy(forest.list);
    else
        list:= Copy(forest);
    fi;
    Sort(list);
    self:= rec(list:= list);
    self.isDomain:= true;
    self.isLeanForestClass:= true;
    self.operations:= LeanForestClassOps;
    
    return self;
end;


#############################################################################
##
#F  IsLeanForestClass( <obj> ) . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsLeanForestClass">
##  <ManSection>
##  <Func Name="IsLeanForestClass" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a lean forest class and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsLeanForestClass:= function(obj)
    return IsRec(obj) and IsBound(obj.isLeanForestClass) 
           and obj.isLeanForestClass = true;
end;


#############################################################################  
##  
#M  Print( <lfcl> )  . . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
LeanForestClassOps.Print:= function(self)
    Print("LeanForestClass( ", self.list, " )");
end;


#############################################################################
##
#F  Representative( <lfcl> ) . . . . . . . . . . . . . . . .  representative.
##
##  <#GAPDoc Label="Representative(lean forest class)">
##  <ManSection>
##  <Meth Name="Representative" Arg="lfcl" Label="for lean forest classes"/>
##  <Returns>a representative of the leanForest class <A>fcl</A>.</Returns>
##  <Description>The representative of a lean forest class constructed as
##  <C>LeanForestClass(forest)</C> (see <Ref Label="LeanForestClass"/>) will be one
##  of its elements, that is a rearrangement of <C>forest</C>.
##  <Example>
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
LeanForestClassOps.Representative:= function(self)
    return LeanForest(self.list);
end;

#############################################################################  
##  
#M  Elements( <fcl> ) . . . . . . . . . . . . . . . . . . . . . . . elements.
##  
##  <#GAPDoc Label="Elements(leanForest class)">
##  <ManSection>
##  <Meth Name="Elements" Arg="fcl" Label="for leanForest classes"/>
##  <Returns>
##    the set of elements of the leanForest class <A>fcl</A>.
##  </Returns>
##  <Description>
##    The class of the leanForest <M>(t_1, \dots, t_l)</M> is its orbit under the
##    action of <M>S_l</M>.
##  <Example>
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
LeanForestClassOps.Elements:= function(self)
    local   list;
    list:= self.list;
    list:= List(Arrangements(list, Length(list)), LeanForest);
    Sort(list);
    return list;
end;

#############################################################################
##  FIXME: use formula for efficiency
LeanForestClassOps.\*:= function(l, r)
    local   pro,  cnt,  forestL,  forestR,  new,  pos,  result,  i;
    
    if not IsLeanForestClass(l) or not IsLeanForestClass(r) then
        Error("don't know how to multiply <l> and <r>");
    fi;
    
    # compute all products
    pro:= [];
    cnt:= [];
    for forestL in Elements(l) do
        for forestR in Elements(r) do
            new:= forestL * forestR;
            if new <> false then
                pos:= Position(pro, new);
                if pos = false then
                    Add(pro, new);
                    Add(cnt, 1);
                else
                    cnt[pos]:= cnt[pos] + 1;
                fi;
            fi;
        od;
    od;
    
    SortParallel(pro, cnt);
    
    # split into classes.
    result:= [];
    while pro <> [] do
        new:= LeanForestClass(pro[1]);
        for i in [1..cnt[1]] do
            Add(result, new);
        od;
        pos:= List(Elements(new), x-> Position(pro, x));
        pos:= Difference([1..Length(pro)], pos);
        pro:= pro{pos};
        cnt:= cnt{pos};
    od;
        
    return result;    
end;



#############################################################################
##
##  Forest Classes.
##
##  the class of a forest consists of all of its rearrangements.
##

#############################################################################
##  
#O  ForestClassOps . . . . . . . . . . . . . . . . . . . . operations record.
##  
##  inherit from Domain so that set operations apply ...
##
ForestClassOps:= OperationsRecord("ForestClassOps", DomainOps);

#############################################################################
##
#C  ForestClass( <forest> ) . . . . . . . . . . . . . . . . . .  constructor.
##
##  stores the sorted list of trees!
##  FIXME: check arguments?
##
ForestClass:= function(forest)
    local   self,  list;

    if IsForest(forest) then
        list:= Copy(forest.list);
    else
        list:= Copy(forest);
    fi;
    Sort(list);
    self:= rec(list:= list);
    self.isDomain:= true;
    self.isForestClass:= true;
    self.operations:= ForestClassOps;
    
    return self;
end;


#############################################################################
##
#F  IsForestClass( <obj> ) . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsForestClass">
##  <ManSection>
##  <Func Name="IsForestClass" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a  forest class and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsForestClass:= function(obj)
    return IsRec(obj) and IsBound(obj.isForestClass) 
           and obj.isForestClass = true;
end;


#############################################################################  
##  
#M  Print( <fcl> ) . . . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
ForestClassOps.Print:= function(self)
    Print("ForestClass( ", self.list, " )");
end;


#############################################################################
##
#F  Representative( <fcl> )  . . . . . . . . . . . . . . . .  representative.
##
##  <#GAPDoc Label="Representative(forest class)">
##  <ManSection>
##  <Meth Name="Representative" Arg="fcl" Label="for forest classes"/>
##  <Returns>a representative of the Forest class <A>fcl</A>.</Returns>
##  <Description>The representative of a forest class constructed as
##  <C>ForestClass(forest)</C> (see <Ref Label="ForestClass"/>) will be one
##  of its elements, that is a rearrangement of <C>forest</C>.
##  <Example>
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
ForestClassOps.Representative:= function(self)
    return Forest(self.list);
end;

#############################################################################  
##  
#M  Elements( <fcl> ) . . . . . . . . . . . . . . . . . . . . . . . elements.
##  
##  <#GAPDoc Label="Elements(Forest class)">
##  <ManSection>
##  <Meth Name="Elements" Arg="fcl" Label="for Forest classes"/>
##  <Returns>
##    the set of elements of the Forest class <A>fcl</A>.
##  </Returns>
##  <Description>
##    The class of the Forest <M>(t_1, \dots, t_l)</M> is its orbit under the
##    action of <M>S_l</M>.
##  <Example>
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ForestClassOps.Elements:= function(self)
    local   list;
    list:= self.list;
    list:= List(Arrangements(list, Length(list)), Forest);
    Sort(list);
    return list;
end;

#############################################################################
ForestClassOps.\= := function(l, r)
    if IsForestClass(l) then
        if IsForestClass(r) then
            return l.list = r.list;
        else
            return false;
        fi;
    else
        return false;
    fi;
end;

#############################################################################
ForestClassOps.\< := function(l, r)
    if not IsForestClass(l) then  return false; fi;
    if not IsForestClass(r) then  return true; fi;
    return l.list < r.list;
end;



#############################################################################
##  FIXME: use double coset formula for efficient computation.
ForestClassOps.\*:= function(l,  r)
    local   pro,  forestL,  forestR,  new,  result;
    
    if not IsForestClass(l) or not IsForestClass(r) then
        Error("don't know how to multiply <l> and <r>");
    fi;
    
    # compute all products
    pro:= [];
    for forestL in Elements(l) do
        for forestR in Elements(r) do
            new:= forestL * forestR;
            if new <> false then
                AddSet(pro, new);
            fi;
        od;
    od;
    
    # split into classes.
    result:= [];
    while pro <> [] do
        new:= ForestClass(pro[1]);
        Add(result, new);
        pro:= Difference(pro, new);
    od;
        
    return result;    
end;


#############################################################################
##
##  Lean Forest Algebra Elements.
##
##  A lean forest algebra element is a linear combination of forest classes.
##

#############################################################################
##  
#O  LeanForestAlgebraEltOps  . . . . . . . . . . . . . . . operations record.
##  
LeanForestAlgebraEltOps:= OperationsRecord("LeanForestAlgebraEltOps");

#############################################################################
##  
#C  LeanForestAlgebraElt( <coef>, <elts> )  . . . . . . . . . .  constructor.
##  
##  <#GAPDoc Label="LeanForestAlgebraElt">
##  <ManSection>
##  <Func Name="LeanForestAlgebraElt" Arg="coef, elts"/>
##  <Returns>
##    a new quiver element with components ...
##  </Returns>
##  <Description>
##  This is the simple constructor for quiver elements ...
##  <Example>
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
LeanForestAlgebraElt:= function(coef, elts)
    local   self;
    self:= rec();
    self.coef:= coef;
    self.elts:= elts;
    self.isLeanForestAlgebraElt:= true;
    self.operations:= LeanForestAlgebraEltOps;
    return self;
end;


#############################################################################
##
#F  IsLeanForestAlgebraElt( <obj> )  . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsLeanForestAlgebraElt">
##  <ManSection>
##  <Func Name="IsLeanForestAlgebraElt" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a quiver element and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsLeanForestAlgebraElt:= function(obj)
    return IsRec(obj) and IsBound(obj.isLeanForestAlgebraElt) 
           and obj.isLeanForestAlgebraElt = true;
end;

#############################################################################
LeanForestAlgebraEltOps.\=:= function(l, r)
    
    if IsLeanForestAlgebraElt(l) then
        if IsLeanForestAlgebraElt(r) then
            return l.coef = r.coef and l.elts = r.elts;
        else
            return false;
        fi;
    else
        return false;
    fi;
end;    


#############################################################################
LeanForestAlgebraEltOps.Print:= function(self)
    Print("LeanForestAlgebraElt( ", self.coef, ", ", self.elts, " )");
end;

# how to normalize a list e of elements with coefficients c
LeanForestAlgebraEltOps.Normalize:= function(self)
    local   e,  c,  eee,  ccc,  i,  elt,  coe;

    e:= self.elts;
    c:= self.coef;
    SortParallel(e, c);
    eee:= [];
    ccc:= [];
    i:= 1;
    while i <= Length(e) do
        elt:= e[i];
        coe:= c[i];
        i:= i+1;
        while i <= Length(e) and e[i] = elt do
            coe:= coe + c[i];
            i:= i+1;
        od;
        if coe <> 0*coe then
            Add(eee, elt);
            Add(ccc, coe);
        fi;
    od;
    
    # copy normalized lists back into originals.
    self.elts:= eee;
    self.coef:= ccc;
end;
    


#############################################################################
LeanForestAlgebraEltOps.\*:= function(l, r)
    local   c,  e,  i,  j,  class,  pro;
 
    if IsLeanForestAlgebraElt(l) then
        if IsLeanForestAlgebraElt(r) then
            c:= [];
            e:= [];
            for i in [1..Length(l.elts)] do
                for j in [1..Length(r.elts)] do
                    for class in l.elts[i] * r.elts[j] do
                        Add(c, l.coef[i] * r.coef[j]);
                        Add(e, class);
                    od;
                od;
            od;
            pro:= LeanForestAlgebraElt(c, e);
        else
            pro:= LeanForestAlgebraElt(l.coef * r, l.elts);
        fi;
    else
        pro:= LeanForestAlgebraElt(l * r.coef, r.elts);
    fi;
    
    Call(pro, "Normalize");
    return pro;
end;    

#############################################################################
LeanForestAlgebraEltOps.\+:= function(l, r)
    local   sum;
    
    # check arguments.
    if not IsLeanForestAlgebraElt(r) then
        Error("<r> is not a LeanForestAlgebraElt");
    fi;
    if not IsLeanForestAlgebraElt(l) then
        Error("<l> is not a LeanForestAlgebraElt");
    fi;
    
    # form the sum.
    sum:= LeanForestAlgebraElt(Concatenation(l.coef, r.coef), 
                  Concatenation(l.elts, r.elts));
    Call(sum, "Normalize");
    return sum;
end;    


#############################################################################
LeanForestAlgebraEltOps.\-:= function(l, r)
    return l + (-1)*r;
end;


#############################################################################
##
##  Forest Algebra Elements.
##
##  A forest algebra element is a linear combination of forest classes.
##

#############################################################################
##  
#O  ForestAlgebraEltOps  . . . . . . . . . . . . . . . . . operations record.
##  
ForestAlgebraEltOps:= OperationsRecord("ForestAlgebraEltOps", LeanForestAlgebraEltOps);

#############################################################################
##  
#C  ForestAlgebraElt( <coef>, <elts> ) . . . . . . . . . . .  constructor.
##  
##  <#GAPDoc Label="ForestAlgebraElt">
##  <ManSection>
##  <Func Name="ForestAlgebraElt" Arg="coef, elts"/>
##  <Returns>
##    a new quiver element with components ...
##  </Returns>
##  <Description>
##  This is the simple constructor for quiver elements ...
##  <Example>
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
ForestAlgebraElt:= function(coef, elts)
    local   self;
    self:= rec();
    self.coef:= coef;
    self.elts:= elts;
    self.isForestAlgebraElt:= true;
    self.operations:= ForestAlgebraEltOps;
    return self;
end;


#############################################################################
##
#F  IsForestAlgebraElt( <obj> )  . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsForestAlgebraElt">
##  <ManSection>
##  <Func Name="IsForestAlgebraElt" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a quiver element and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsForestAlgebraElt:= function(obj)
    return IsRec(obj) and IsBound(obj.isForestAlgebraElt) and obj.isForestAlgebraElt = true;
end;

#############################################################################
ForestAlgebraEltOps.\=:= function(l, r)
    
    if IsForestAlgebraElt(l) then
        if IsForestAlgebraElt(r) then
            return l.coef = r.coef and l.elts = r.elts;
        else
            return false;
        fi;
    else
        return false;
    fi;
end;    


#############################################################################
ForestAlgebraEltOps.Print:= function(self)
    Print("ForestAlgebraElt( ", self.coef, ", ", self.elts, " )");
end;


#############################################################################
ForestAlgebraEltOps.\*:= function(l, r)
    local   c,  e,  i,  j,  class,  pro;
 
    if IsForestAlgebraElt(l) then
        if IsForestAlgebraElt(r) then
            c:= [];
            e:= [];
            for i in [1..Length(l.elts)] do
                for j in [1..Length(r.elts)] do
                    for class in l.elts[i] * r.elts[j] do
                        Add(c, l.coef[i] * r.coef[j]);
                        Add(e, class);
                    od;
                od;
            od;
            pro:= ForestAlgebraElt(c, e);
        else
            pro:= ForestAlgebraElt(l.coef * r, l.elts);
        fi;
    else
        pro:= ForestAlgebraElt(l * r.coef, r.elts);
    fi;
    
    Call(pro, "Normalize");
    return pro;
end;    

#############################################################################
ForestAlgebraEltOps.\+:= function(l, r)
    local   sum;
    
    # check arguments.
    if not IsForestAlgebraElt(r) then
        Error("<r> is not a ForestAlgebraElt");
    fi;
    if not IsForestAlgebraElt(l) then
        Error("<l> is not a ForestAlgebraElt");
    fi;
    
    # form the sum.
    sum:= ForestAlgebraElt(Concatenation(l.coef, r.coef), 
                  Concatenation(l.elts, r.elts));
    Call(sum, "Normalize");
    return sum;
end;    


