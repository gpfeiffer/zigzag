#############################################################################
##
#A  walker.g                     Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2006, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: walker.g,v 1.1 2006/07/05 18:45:41 goetz Exp $
##
##  <#GAPDoc Label="Intro:Walker">
##  This file contains some tree walking and counting functions.
##  
##  An <E>tree</E> <Index>tree</Index>, or more precisely an ordered
##  rooted tree, is an object that implements the 'Children' method,
##  such that it returns a (possibly empty) list of trees.
##
##  Introduce a suitable small example ...
##
##  <#/GAPDoc>
##

#############################################################################
##
#F  BreadthFirst( <tree> ) . . . . . . . . . . . . . .  breadth first search.
##
##  <#GAPDoc Label="BreadthFirst">
##  <ManSection>
##  <Func Name="BreadthFirst" Arg="tree"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> in breadth first order.
##  </Returns>
##  <Description>
##    The breadth first order of the vertices of a tree starts with
##    the root, followed by the vertices at depth 1, followed by the
##    vertices at depth 2, \ldots\
##    The usual orbit algorithm is an example of a breadth first search.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BreadthFirst:= function(tree)
    local   list,  next;
    
    list:= [tree];
    for next in list do
        Append(list, Call(next, "Children"));
    od;
    return list;
end;

#############################################################################
##
#F  PreOrder( <tree> ) . . . . . . . . . . . . . . . . .  depth first search.
##
##  <#GAPDoc Label="PreOrder">
##  <ManSection>
##  <Func Name="PreOrder" Arg="tree"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> in pre-order.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and vertices are
##    listed when they are encountered for the first time.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
PreOrder:= function(tree)
    local   list,  c;
    
    list:= [tree];
    for c in Call(tree, "Children") do
        Append(list, PreOrder(c));
    od;
    return list;
end;

#############################################################################
##
#F  NrPreOrder( <tree> ) . . . . . . . . . . . . . . . .  depth first search.
##
##  <#GAPDoc Label="NrPreOrder">
##  <ManSection>
##  <Func Name="NrPreOrder" Arg="tree"/>
##  <Returns>
##    the number of vertices of the tree <A>tree</A>.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and vertices are
##    counted when they are encountered for the first time.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
NrPreOrder:= function(tree)
    return 1 + Sum(Call(tree, "Children"), NrPreOrder);
end;

#############################################################################
##
#F  PreOrderProperty( <tree>, <property> ) . . . . . . .  depth first search.
##
##  <#GAPDoc Label="PreOrderProperty">
##  <ManSection>
##  <Func Name="PreOrderProperty" Arg="tree, property"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> having the given
##    property <A>property</A> in pre-order.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and a vertex is
##    listed when it is encountered for the first time, provided it
##    satisfies the given property <A>property</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
PreOrderProperty:= function(tree, property)
    local   list,  c;
    
    list:= [];
    if property(tree) then
        Add(list, tree);
        InfoZigzag1(".\c");
    fi;
    
    for c in Call(tree, "Children") do
        Append(list, PreOrderProperty(c, property));
    od;
    return list;
end;

#############################################################################
##
#F  NrPreOrderProperty( <tree>, <property> ) . . . . . .  depth first search.
##
##  <#GAPDoc Label="NrPreOrderProperty">
##  <ManSection>
##  <Func Name="NrPreOrderProperty" Arg="tree, property"/>
##  <Returns>
##    the number of vertices of the tree <A>tree</A> having the given
##    property <A>property</A>.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and a vertex is
##    counted when it is encountered for the first time, provided it
##    satisfies the given property <A>property</A>.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
NrPreOrderProperty:= function(tree, p)
    local a;
    a:= 0;  if p(tree) then a:= 1; fi;
    return a + Sum(Call(tree, "Children"), c-> NrPreOrderProperty(c, p));
end;

#############################################################################
##
#F  PostOrder( <tree> ) . . . . . . . . . . . . . . . . . depth first search.
##
##  <#GAPDoc Label="PostOrder">
##  <ManSection>
##  <Func Name="PostOrder" Arg="tree"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> in post-order.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and vertices are
##    listed when they are encountered for the last time.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
PostOrder:= function(tree)
    local   list,  c;
    
    list:= [];
    for c in Call(tree, "Children") do
        Append(list, PostOrder(c));
    od;
    Add(list, tree);
    return list;
end;

#############################################################################
##
#F  PostOrderProperty( <tree>, <property> ) . . . . . . . depth first search.
##
##  <#GAPDoc Label="PostOrderProperty">
##  <ManSection>
##  <Func Name="PostOrderProperty" Arg="tree, property"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> having descendants
##    with the given property <A>property</A> in post-order.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and a vertex is
##    listed when it is encountered for the last time, provided it or
##    one of its descendants satisfies the given property
##    <A>property</A>.  In post-order, all descendants of a vertex
##    have been visited when it has to be decided whether to list the
##    vertex or not.
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
PostOrderProperty:= function(tree, property)
    local   list,  c;
    
    list:= [];
    for c in Call(tree, "Children") do
        Append(list, PostOrderProperty(c, property));
    od;
    if property(tree) then
        Add(list, tree);
        InfoZigzag1(".\c");
    elif list <> [] then
        Add(list, tree);
        InfoZigzag1("+\c");
    fi;
    
    return list;
end;



#############################################################################
##
##  Examples of trees.
##
BinomialTreeOps:= rec();

BinomialTree:= n -> rec(n:= n, operations:= BinomialTreeOps);

BinomialTreeOps.Children:= function(this)
    return List([0..this.n-1], BinomialTree);
end;

BinomialTreeOps.Print:= function(this)
    Print(this.n);
end;

     
   
