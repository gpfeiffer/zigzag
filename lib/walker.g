#############################################################################
##
#A  walker.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
##
##  This file contains some tree walking and counting functions.
##  
##  <#GAPDoc Label="Intro:Walker">
##    An <E>tree</E><Index>tree</Index>, or more precisely an ordered
##    rooted tree, is a collection of nodes, each of which has a list
##    of nodes as children.  Here, a tree is an object that implements
##    the <K>Children()</K> method in such a way that it returns a
##    (possibly empty) list of trees.  Several strategies for walking
##    over the nodes of a tree for processing or just counting them
##    are provided.<P/>
##
##    Frequently, the search tree is given implicitly, rather than
##    through an explicit notion of child nodes.  Examples of this include
##    the task of visiting all the elements of the Cartesian product
##    <M>X_1 \times X_2 \times X_r</M> of <M>r</M> finite sets
##    <M>X_1, X_2,\dots, X_r</M>.  Here the children of the root node
##    are the elements of <M>X_1</>, each such node has children
##    corresponding to the elements of <M>X_2</M>, etc.  This chapter
##    contains two efficient algorithms for the traveral of such a tree;
##    see <Ref Func="VisitMixedTuplesM"/> and <Ref Func="VisitMixedTuplesH"/>.
##    As an application, we get two efficient function for the 
##    enumeration of the elements of a finite abelian group,
##    regarded as a direct product of cyclic groups; see
##    <Ref Func="ProductsMixedTuplesM"/> and <Ref Func="ProductsMixedTuplesH"/>.
##
##    The functions described in this chapter are implemented in the file
##    <F>walker.g</F>.  
##  <#/GAPDoc>
##

#############################################################################
##
#F  BreadthFirst( <tree> ) . . . . . . . . . . . . . .  breadth first search.
##
##  <#GAPDoc Label="BreadthFirst">
##  <ManSection>
##  <Func Name="BreadthFirst" Arg="tree[, children]"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> in breadth first order.
##  </Returns>
##  <Description>
##    The breadth first order of the vertices of a tree starts with
##    the root, followed by the vertices at depth 1, followed by the
##    vertices at depth 2, etc.
##    The usual orbit algorithm is an example of a breadth first search.
##  <Example>
##  gap> BreadthFirst(BinomialTree(4));
##  [ 4, 0, 1, 2, 3, 0, 0, 1, 0, 1, 2, 0, 0, 0, 1, 0 ]
##  gap> Display(BinomialTree(4));
##  -4-0
##    -1-0
##    -2-0
##      -1-0
##    -3-0
##      -1-0
##      -2-0
##        -1-0
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BreadthFirst:= function(arg)
    local   usage,  children,  list,  next;
    
    # check arguments.
    usage:= "usage: BreadthFirst( tree [, children] )";
    if Length(arg) < 1 or Length(arg) > 2 then
        Error(usage);
    elif Length(arg) = 2 then
        children:= arg[2];
    else
        children:= "Children";         
    fi;
    
    # recurse.
    list:= [arg[1]];
    for next in list do
        Append(list, Call(next, children));
    od;
    return list;
end;


#############################################################################
##
#F  IteratorBreadthFirst( <tree> ) . . . . . . . . . .  breadth first search.
##
##  <#GAPDoc Label="IteratorBreadthFirst">
##  <ManSection>
##  <Func Name="IteratorBreadthFirst" Arg="tree[, children]"/>
##  <Returns>
##    an iterator for the vertices of the tree <A>tree</A>.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded breadth first, and vertices are
##    listed when they are encountered for the first time.
##  <Example>
##  gap> itr:= IteratorBreadthFirst(BinomialTree(4));;
##  gap> itr.hasNext();
##  true
##  gap> a:= itr.next();
##  4
##  gap> Print(a);  while itr.hasNext() do Print(", ", itr.next()); od;  Print("\n");
##  4, 0, 1, 2, 3, 0, 0, 1, 0, 1, 2, 0, 0, 0, 1, 0
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##

##
##  A breadth first iterator for trees.
##  it consists of a queue (linked list) of elements to be processed,
##  pointers to the back (next element to be expanded),
##  the focus (next element to be returned) and the head
##  where the next prefix is to be put in the queue.
##
##  initially:
##
##    f
##    v
##    w -> .
##    ^    ^
##    b    h
##
IteratorBreadthFirst:= function(arg)
    local   usage,  children,  head,  focus,  back,  itr,  w,  x,  c;
    
    # check arguments.
    usage:= "usage: IteratorBreadthFirst( tree [, children] )";
    if Length(arg) < 1 or Length(arg) > 2 then
        Error(usage);
    elif Length(arg) = 2 then
        children:= arg[2];
    else
        children:= "Children";         
    fi;
    
    # initialize.
    head:= rec();
    focus:= rec(w:= arg[1], next:= head);
    back:= focus; 

    itr:= rec();

##  hasNext() simply checks whether 'focus' is lookin' at an element.
    itr.hasNext:= function()
        return IsBound(focus.w);
    end;
    
##  next() simply returns the element 'focus' is lookin at.  But before it
##  does that it needs to advance 'focus' to the next element in the queue,
##  and to fill the queue up with the children of the elements between 'back
##  and 'focus'.
    itr.next:= function()
        local   w,  x,  c;
        w:=  focus.w;
        focus:= focus.next;   
        
        # expand back.w to focus.w
        while not IsIdentical(back, focus) do
            x:= back.w;
            for c in Call(x, children) do
                head.w:= c;
                head.next:= rec();
                head:= head.next;
            od;
            back:= back.next;
        od;
        return w;
    end;

    return itr;
end;


#############################################################################
##
#F  PreOrder( <tree> ) . . . . . . . . . . . . . . . . .  depth first search.
##
##  <#GAPDoc Label="PreOrder">
##  <ManSection>
##  <Func Name="PreOrder" Arg="tree[, children]"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> in pre-order.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and vertices are
##    listed when they are encountered for the first time.
##  <Example>
##  gap> PreOrder(BinomialTree(4));
##  [ 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0 ]
##  gap> Display(BinomialTree(4));
##  -4-0
##    -1-0
##    -2-0
##      -1-0
##    -3-0
##      -1-0
##      -2-0
##        -1-0
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
PreOrderNC:= function(tree, children)
    local   usage,  children,  list,  c;
    
    list:= [tree];
    for c in Call(list[1], children) do
        Append(list, PreOrderNC(c, children));
    od;
    return list;
end;

PreOrder:= function(arg)
    local   usage,  children;
    
    # check arguments.
    usage:= "usage: PreOrder( tree [, children] )";
    if Length(arg) < 1 or Length(arg) > 2 then
        Error(usage);
    elif Length(arg) = 2 then
        children:= arg[2];
    else
        children:= "Children";         
    fi;
    
    # recurse.
    return PreOrderNC(arg[1], children);
end;


#############################################################################
##
#F  NrPreOrder( <tree> ) . . . . . . . . . . . . . . . .  depth first search.
##
##  <#GAPDoc Label="NrPreOrder">
##  <ManSection>
##  <Func Name="NrPreOrder" Arg="tree[, children]"/>
##  <Returns>
##    the number of vertices of the tree <A>tree</A>.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and vertices are
##    counted when they are encountered for the first time.
##  <Example>
##  gap> NrPreOrder(BinomialTree(4));
##  16
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
NrPreOrderNC:= function(tree, children)
    return 1 + Sum(Call(tree, children), x-> NrPreOrderNC(x, children));
end;

NrPreOrder:= function(arg)
    local   usage,  children;
    
    # check arguments.
    usage:= "usage: NrPreOrder( tree [, children] )";
    if Length(arg) < 1 or Length(arg) > 2 then
        Error(usage);
    elif Length(arg) = 2 then
        children:= arg[2];
    else
        children:= "Children";         
    fi;
    
    # recurse.
    return NrPreOrderNC(arg[1], children);
end;


#############################################################################
##
#F  IteratorPreOrder( <tree> ) . . . . . . . . . . . . .  depth first search.
##
##  <#GAPDoc Label="IteratorPreOrder">
##  <ManSection>
##  <Func Name="IteratorPreOrder" Arg="tree[, children]"/>
##  <Returns>
##    an iterator for the vertices of the tree <A>tree</A>.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and vertices are
##    counted when they are encountered for the first time.
##  <Example>
##  gap> itr:= IteratorPreOrder(BinomialTree(4));;
##  gap> itr.hasNext();
##  true
##  gap> a:= itr.next();
##  4
##  gap> Print(a);  while itr.hasNext() do Print(", ", itr.next()); od;  Print("\n");
##  4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
IteratorPreOrder:= function(arg)
    local   usage,  children,  stack,  len,  push,  pop,  itr;
    
    # check arguments.
    usage:= "usage: IteratorPreOrder( tree [, children] )";
    if Length(arg) < 1 or Length(arg) > 2 then
        Error(usage);
    elif Length(arg) = 2 then
        children:= arg[2];
    else
        children:= "Children";         
    fi;
    
    # initialize stack.
    stack:= [];  len:= 0;
    
    # how to push an item.
    push:= function(obj)
        len:= len + 1;
        stack[len]:= obj;
    end;
    
    # how to pop.
    pop:= function()
        len:= len - 1;
        return stack[len+1];
    end;
    
    # push the tree.
    push(arg[1]);
    
    itr:= rec();
    
    itr.next:= function()
        local   a,  c;
        
        a:= pop();
        for c in Reversed(Call(a, "Children")) do
            push(c);
        od;
        return a;
    end;
    
    itr.hasNext:= function()
        return len > 0;
    end;
    
    return itr;
end;


#############################################################################
##
#F  PreOrderProperty( <tree>, <property> ) . . . . . . .  depth first search.
##
##  <#GAPDoc Label="PreOrderProperty">
##  <ManSection>
##  <Func Name="PreOrderProperty" Arg="tree, property[, children]"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> having the given
##    property <A>property</A> in pre-order.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and a vertex is
##    listed when it is encountered for the first time, provided it
##    satisfies the given property <A>property</A>.
##  <Example>
##  gap> PreOrderProperty(BinomialTree(4), x-> x.n > 0);
##  [ 4, 1, 2, 1, 3, 1, 2, 1 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
PreOrderPropertyNC:= function(tree, property, children)
    local   list,  c;
    
    list:= [];
    if property(tree) then
        Add(list, tree);
    fi;
    
    for c in Call(tree, children) do
        Append(list, PreOrderPropertyNC(c, property, children));
    od;
    return list;
end;

PreOrderProperty:= function(arg)
    local   usage,  children;
    
    # check arguments.
    usage:= "usage: PreOrderProperty( tree, property [, children] )";
    if Length(arg) < 2 or Length(arg) > 3 then
        Error(usage);
    elif Length(arg) = 3 then
        children:= arg[3];
    else
        children:= "Children";         
    fi;
    
    return PreOrderPropertyNC(arg[1], arg[2], children);
end;


#############################################################################
##
#F  NrPreOrderProperty( <tree>, <property> ) . . . . . .  depth first search.
##
##  <#GAPDoc Label="NrPreOrderProperty">
##  <ManSection>
##  <Func Name="NrPreOrderProperty" Arg="tree, property[, children]"/>
##  <Returns>
##    the number of vertices of the tree <A>tree</A> having the given
##    property <A>property</A>.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and a vertex is
##    counted when it is encountered for the first time, provided it
##    satisfies the given property <A>property</A>.
##  <Example>
##  gap> NrPreOrderProperty(BinomialTree(4), x-> x.n > 0);
##  8
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
NrPreOrderPropertyNC:= function(tree, property, children)
    local a;
    
    a:= 0;  if property(tree)  then a:= 1;  fi;
    return a + Sum(Call(tree, children), 
                   c-> NrPreOrderPropertyNC(c, property, children));
end;

NrPreOrderProperty:= function(arg)
    local   usage,  children;
    
    # check arguments.
    usage:= "usage: NrPreOrderProperty( tree, property [, children] )";
    if Length(arg) < 2 or Length(arg) > 3 then
        Error(usage);
    elif Length(arg) = 3 then
        children:= arg[3];
    else
        children:= "Children";         
    fi;
    
    return NrPreOrderPropertyNC(arg[1], arg[2], children);
end;


#############################################################################
##
#F  PostOrder( <tree> ) . . . . . . . . . . . . . . . . . depth first search.
##
##  <#GAPDoc Label="PostOrder">
##  <ManSection>
##  <Func Name="PostOrder" Arg="tree[, children]"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> in post-order.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and vertices are
##    listed when they are encountered for the last time.
##  <Example>
##  gap> PostOrder(BinomialTree(4));
##  [ 0, 0, 1, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1, 2, 3, 4 ]
##  gap> Display(BinomialTree(4));
##  -4-0
##    -1-0
##    -2-0
##      -1-0
##    -3-0
##      -1-0
##      -2-0
##        -1-0
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
PostOrderNC:= function(tree, children)
    local   list,  c;
    
    list:= [];
    for c in Call(tree, children) do
        Append(list, PostOrderNC(c, children));
    od;
    Add(list, tree);
    return list;
end;

PostOrder:= function(arg)
    local   usage,  children;
    
    # check arguments.
    usage:= "usage: PostOrder( tree [, children] )";
    if Length(arg) < 1 or Length(arg) > 2 then
        Error(usage);
    elif Length(arg) = 2 then
        children:= arg[2];
    else
        children:= "Children";         
    fi;
    
    return PostOrderNC(arg[1], children);
end;


#############################################################################
##
#F  PostOrderProperty( <tree>, <property> ) . . . . . . . depth first search.
##
##  <#GAPDoc Label="PostOrderProperty">
##  <ManSection>
##  <Func Name="PostOrderProperty" Arg="tree, property[, children]"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> having descendants
##    with the given property <A>property</A> in post-order.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and a vertex is
##    listed when it is encountered for the last time, provided it
##    <E>or one of its descendants</E> satisfies the given property
##    <A>property</A>.  In post-order, all descendants of a vertex
##    have been visited when it has to be decided whether to list the
##    vertex or not.
##  <Example>
##  gap> PostOrderProperty(BinomialTree(4), x-> x.n = 1);
##  [ 1, 1, 2, 1, 1, 2, 3, 4 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
PostOrderPropertyNC:= function(tree, property, children)
    local   list,  c;
    
    list:= [];
    for c in Call(tree, children) do
        Append(list, PostOrderPropertyNC(c, property, children));
    od;
    if list <> [] or property(tree) then
        Add(list, tree);
    fi;
    
    return list;
end;

PostOrderProperty:= function(arg)
    local   usage,  children;
    
    # check arguments.
    usage:= "usage: PostOrderProperty( tree, property [, children] )";
    if Length(arg) < 2 or Length(arg) > 3 then
        Error(usage);
    elif Length(arg) = 3 then
        children:= arg[3];
    else
        children:= "Children";         
    fi;
    
    return PostOrderPropertyNC(arg[1], arg[2], children);
end;
    

#############################################################################
##
#F  NrPostOrderProperty( <tree>, <property> ) . . . . . . depth first search.
##
##  <#GAPDoc Label="NrPostOrderProperty">
##  <ManSection>
##  <Func Name="NrPostOrderProperty" Arg="tree, property[, children]"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> having descendants
##    with the given property <A>property</A> in post-order.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and a vertex is
##    counted when it is encountered for the last time, provided it
##    <E>or one of its descendants</E> satisfies the given property
##    <A>property</A>.  In post-order, all descendants of a vertex
##    have been visited when it has to be decided whether to count the
##    vertex or not.
##  <Example>
##  gap> NrPostOrderProperty(BinomialTree(4), x-> x.n = 1);
##  8
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
NrPostOrderPropertyNC:= function(tree, property, children)
    local   sum;
    
    sum:= Sum(Call(tree, children), 
              x-> NrPostOrderPropertyNC(x, property, children));
    if sum > 0 or property(tree) then
        sum:= sum + 1;
    fi;
    
    return sum;
end;

NrPostOrderProperty:= function(arg)
    local   usage,  children;
    
    # check arguments.
    usage:= "usage: NrPostOrderProperty( tree, property [, children] )";
    if Length(arg) < 2 or Length(arg) > 3 then
        Error(usage);
    elif Length(arg) = 3 then
        children:= arg[3];
    else
        children:= "Children";         
    fi;
    
    return NrPostOrderPropertyNC(arg[1], arg[2], children);
end;
    

#############################################################################
##
##  Examples of trees.
##
BinomialTreeOps:= rec();

BinomialTree:= n -> rec(n:= n, operations:= BinomialTreeOps);

BinomialTreeOps.Children:= function(self)
    return List([0..self.n-1], BinomialTree);
end;

BinomialTreeOps.Print:= function(self)
    Print(self.n);
end;

BinomialTreeOps.indent:= 0;

BinomialTreeOps.Display:= function(self, dummy)   
    local  c;
    
    if self.n > 0 then
        for c in [1..BinomialTreeOps.indent] do
            Print(" ");
        od;
    fi;
    Print("-", self.n);
    if self.n = 0 then
        Print("\n");
    fi;
    
    BinomialTreeOps.indent:= BinomialTreeOps.indent + 2;
    for c in Call(self, "Children") do
        Display(c);
    od;
    BinomialTreeOps.indent:= BinomialTreeOps.indent - 2;
end;

##  General combinatorial tools.

#############################################################################
##
##  Generating all tuples, mixed radix
##
#############################################################################

#############################################################################
##
#F  VisitMixedTuplesM( <list>, <visit> )
##
##  (mixed-radix generation)  [Knuth, TAOCP 7.2.1.1, Algorithm M]
##
##  given a list of Lists, form (and visit) all possible combinations
##  of one from each list.
##
VisitMixedTuplesM:= function(list, visit)
    local   n,  m,  a,  c,  j;
    
    n:= Length(list);
    m:= List(list, Length);
    a:= List(list, x-> 1);
    c:= list{[1..n]}[1];
    
    while true do
        visit(c);
        j:= n;
        
        while a[j] = m[j] do
            if  j = 1  then  return;  fi;
            a[j]:= 1;
            c[j]:= list[j][1];
            j:= j - 1;
        od;
        
        a[j]:= a[j] + 1;
        c[j]:= list[j][a[j]];
    od;
end;


#############################################################################
##
##  Application: generate all elements of a finite abelian group.
##
##  given list gens of (images of) independent generators of an abelian group
##  and their orders m, generate all elements
##
ProductsMixedTuplesM:= function(gens, m)
    local   n,  a,  c,  all,  j;
    
    n:= Length(gens);
    a:= List(gens, x-> 1);
    c:= Product(gens, x-> x^0);  # or c:= gens[1]^0;
    
    all:= [];
    while true do
        Add(all, c);
        j:= n;
        
        while a[j] = m[j] do
            if j = 1 then
                return all;
            fi;
            a[j]:= 1;
            c:= c * gens[j];
            j:= j - 1;
        od;
        
        a[j]:= a[j] + 1;
        c:= c * gens[j];
    od;
end;


#############################################################################
##
##  Algorithm H (Loopless reflected mixed-radix Gray generation)
##  [Knuth, TAOCP, 7.2.1.1]
##
##  given a list of Lists, form (and visit) all possible combinations
##  of one from each list, changing only one component at each step.
##
VisitMixedTuplesH:= function(list, visit)
    local   n,  m,  a,  c,  f,  o,  j;

    n:= Length(list);
    m:= List(list, Length);
    a:= List(list, x-> 1);
    c:= list{[1..n]}[1];
    
    f:= [0..n];
    o:= List(list, x-> 1);
    
    while true do
        visit(c);
        
        if f[1] = n then 
            return;
        fi;
        
        j:= f[1]+1;
        f[1]:= 0;
        
        a[j]:= a[j] + o[j];
        c[j]:= list[j][a[j]];
        
        if a[j] = 1 or a[j] = m[j] then
            o[j]:= -o[j];
            f[j]:= f[j+1];
            f[j+1]:= j;
        fi;
    od;
end;

#############################################################################
##
##  Application: generate all elements of a finite abelian group.
##
##  given list gens of (images of) independent generators of an abelian group
##  and their orders m, generate all elements; this time by multiplying with 
##  a single generator only (or its inverse) in each step.
##
ProductsMixedTuplesH:= function(gens, m)
    local   n,  a,  c,  f,  o,  all,  j;
    
    n:= Length(gens);
    a:= List(gens, x-> 1);
    c:= Product(gens, x-> x^0);  # or c:= gens[1]^0;
    
    f:= [0..n];
    o:= List(gens, x-> 1);
    
    all:= [];
    
    while true do
        Add(all, c);
        
        if f[1] = n then 
            return all;
        fi;
        
        j:= f[1]+1;
        f[1]:= 0;
        
        a[j]:= a[j] + o[j];
        c:= c * gens[j]^o[j];
        
        if a[j] = 1 or a[j] = m[j] then
            o[j]:= -o[j];
            f[j]:= f[j+1];
            f[j+1]:= j;
        fi;
    od;
end;

#############################################################################
##
##  Packings
##
#############################################################################

#############################################################################
##
##  ExactPackings
##
##  given a list 'sum' of integers >= 0, and a list 'con'
##  of lists of constituents, find one/all ways to pick
##  one of each so that the picks add up to the given sum.
##
##  Example:
##
##  gap> sum:= [ 1, 2, 1 ];;
##  gap> con:= [
##  > [ [ 1, 0, 0 ], [ 0, 0, 1 ] ], 
##  > [ [ 1, 1, 0 ], [ 0, 1, 1 ] ], 
##  > [ [ 0, 1, 0 ], [ 1, 0, 1 ] ]  
##  > ];;
##  gap> ExactPackings(sum, con);
##  [ [ 2, 1, 1 ], [ 1, 2, 1 ] ]
##
##
##  recursive solution:
##
##  if Length(con) = 1:
##     locate sum in con[1]
##  else:
##     return fail
##
##  l = Length(con);
##  for each i in [1..Length(con[l])]:
##     if con[l][i] < sum:
##        for each sol in A(sum - con[l][i], con{[1..l-1]}):
##            append i to sol
##
##
##  FIXME: add parameter for single solution find.
##
ExactPackings:= function(sum, con) 
    local   isPositive,  log,  idx,  cmp,  cur,  all,  zero,  search;
    
    # how to test if a list has no negative entries.
    isPositive:= a-> ForAll(a, x-> x >= 0);
    
    # keep track of where we are.
    log:= [];
    idx:= [];  
    cmp:= [1..Length(con)];   # idx \disjoint cmp = [1..Length(con)]
    cur:= 0 * cmp; # current solution
    all:= []; # all solutions found
    
    zero:= 0*sum;
    
    # how to recurse
    search:= function(sum, pos)
        local   l,  qos,  k,  wgt,  sub,  j,  i;
        
        if cmp = [] then
            if sum = zero then
                Add(all, Copy(cur));  # one solution found.
            fi;
            return;
        fi;
        
        #  compute positions of subtractable constituents.
        l:= Length(pos);
        pos:= List([1..l], i-> Filtered(pos[i], j-> isPositive(sum - con[cmp[i]][j])));
        
        # stop if dead end.
        if [] in pos then  return;  fi;
        
        # sort out uniq choices.
        k:= PositionProperty(pos, x-> Length(x) = 1);
        
        # otherwise go for largest contribution
        if k = false then
            wgt:= List([1..l], i-> Sum(con[cmp[i]][pos[i][1]]));
            k:= Position(wgt, Maximum(wgt));
        fi;
        
        sub:= Difference([1..l], [k]);
        
        Add(log, Length(pos[k]));
        j:= cmp[k];
        Add(idx, j); 
        RemoveSet(cmp, j);
        for i in pos[k] do
            log[Length(log)]:= log[Length(log)] - 1;
            cur[j]:= i;
            Print(log, "\r");
            search(sum - con[j][i], pos{sub});
        od;
        Unbind(log[Length(log)]);
        AddSet(cmp, idx[Length(idx)]);
        Unbind(idx[Length(idx)]);
        cur[j]:= 0;
    end;
    
    # recurse and return all solutions found.
    search(sum, List(con, x-> [1..Length(x)])); 
    return all;
end;
    

#############################################################################
FunCon:= function(con, fun)
    return List([1..Length(con[1])], i-> fun(con{[1..Length(con)]}[i]));
end;

#############################################################################
##
##  RestrictCon1
##
##  given a list sum of rationals and a list con of lists of constituents
##  filter out from con those who potentially participate in a transversal
##  adding up to sum, using attainable maxima and minima.
RestrictCon1:= function(sum, con)
    local   N,  new,  old,  i,  lis,  min,  max;

    N:= Length(sum);

    # restrict choices.
    new:= Sum(con, Length);  old:= new + 1;
    while new < old do
        for i in Reversed([1..N]) do

            # pick values in i-th position.
            lis:= List(con, x-> List(x, y-> y[i]));  

            # do we have to take minimal values throughout?
            min:= List(lis, Minimum);
            if Sum(min) = sum[i] then
                con:= List(con, x-> Filtered(x, 
                              z-> z[i] = Minimum(List(x, y-> y[i]))));
            fi;

            # do we have to take maximal values throughout?
            max:= List(lis, Maximum);
            if Sum(max) = sum[i] then
                con:= List(con, x-> Filtered(x, 
                              z-> z[i] = Maximum(List(x, y-> y[i]))));
            fi;
        od;
        old:= new;
        new:= Sum(con, Length);
        Print(".\n");
    od;

    return con;
end;

#############################################################################
RestrictCon2:= function(sum, con)
    local   N,  i,  lis,  new,  j;

    N:= Length(con);

    # another way to restrict choices.
    for i in Reversed([1..N]) do
        lis:= List(con, x-> Set(List(x, y-> y[i]))); 
        new:= Filtered(Cartesian(lis), x-> Sum(x) = sum[i]);
        new:= List(TransposedMat(new), Set);
        if new <> lis then
            for j in [1..N] do
                con[j]:= Filtered(con[j], z-> z[i] in new[j]);
            od;
            Print("+\n");
        fi;
    od;

    return con;
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
