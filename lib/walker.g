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
##    An <E>tree</E> <Index>tree</Index>, or more precisely an ordered
##    rooted tree, is a collection of nodes, each of which has a list
##    of nodes as children.  Here, a tree is an object that implements
##    the <K>Children()</K> method in such a way that it returns a
##    (possibly empty) list of trees.  Several strategies for walking
##    over the nodes of a tree for processing or just counting them
##    are provided.<P/>
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
##  <Func Name="BreadthFirst" Arg="tree"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> in breadth first order.
##  </Returns>
##  <Description>
##    The breadth first order of the vertices of a tree starts with
##    the root, followed by the vertices at depth 1, followed by the
##    vertices at depth 2, \ldots\
##    The usual orbit algorithm is an example of a breadth first search.
##  <Example>
##  gap> BreadthFirst(BinomialTree(4));
##  [ 4, 0, 1, 2, 3, 0, 0, 1, 0, 1, 2, 0, 0, 0, 1, 0 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BreadthFirst:= function(arg)
    local   usage,  children,  list,  next;
    
    usage:= "usage: BreadthFirst( tree [, children] )";
    if Length(arg) < 1 or Length(arg) > 2 then
        Error(usage);
    fi;
    
    if Length(arg) = 2 then
        children:= arg[2];
    else
        children:= "Children";         
    fi;
        
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
##  <Func Name="IteratorBreadthFirst" Arg="tree"/>
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
IteratorBreadthFirst:= function(tree)
    local   head,  focus,  back,  itr;
    
    head:= rec();
    focus:= rec(w:= tree, next:= head);
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
            for c in Call(x, "Children") do
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
##  <Func Name="PreOrder" Arg="tree"/>
##  <Returns>
##    the list of vertices of the tree <A>tree</A> in pre-order.
##  </Returns>
##  <Description>
##    The tree <A>tree</A> is expanded depth first, and vertices are
##    listed when they are encountered for the first time.
##  <Example>
##  gap> PreOrder(BinomialTree(4));
##  [ 4, 0, 1, 0, 2, 0, 1, 0, 3, 0, 1, 0, 2, 0, 1, 0 ]
##  </Example>
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
##  <Example>
##  gap> NrPreOrder(BinomialTree(4));
##  16
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
NrPreOrder:= function(tree)
    return 1 + Sum(Call(tree, "Children"), NrPreOrder);
end;


#############################################################################
##
#F  IteratorPreOrder( <tree> ) . . . . . . . . . . . . .  depth first search.
##
##  <#GAPDoc Label="IteratorPreOrder">
##  <ManSection>
##  <Func Name="IteratorPreOrder" Arg="tree"/>
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
IteratorPreOrder:= function(tree)
    local   stack,  len,  push,  pop,  itr;
    
    stack:= [];  len:= 0;
    push:= function(obj)
        len:= len + 1;
        stack[len]:= obj;
    end;
    
    pop:= function()
        len:= len - 1;
        return stack[len+1];
    end;
    
    push(tree);
    
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
##  <Func Name="PreOrderProperty" Arg="tree, property"/>
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
##  <Example>
##  gap> NrPreOrderProperty(BinomialTree(4), x-> x.n > 0);
##  8
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
NrPreOrderProperty:= function(tree, pro)
    local a;
    a:= 0;  if pro(tree) then a:= 1; fi;
    return a + Sum(Call(tree, "Children"), c-> NrPreOrderProperty(c, pro));
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
##  <Example>
##  gap> PostOrder(BinomialTree(4));
##  [ 0, 0, 1, 0, 0, 1, 2, 0, 0, 1, 0, 0, 1, 2, 3, 4 ]
##  </Example>
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
PostOrderProperty:= function(tree, property)
    local   list,  c;
    
    list:= [];
    for c in Call(tree, "Children") do
        Append(list, PostOrderProperty(c, property));
    od;
    if list <> [] or property(tree) then
        Add(list, tree);
    fi;
    
    return list;
end;


#############################################################################
##
#F  NrPostOrderProperty( <tree>, <property> ) . . . . . . depth first search.
##
##  <#GAPDoc Label="NrPostOrderProperty">
##  <ManSection>
##  <Func Name="NrPostOrderProperty" Arg="tree, property"/>
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
NrPostOrderProperty:= function(tree, pro)
    local   sum;
    
    sum:= Sum(Call(tree, "Children"), x-> NrPostOrderProperty(x, pro));
    if sum > 0 or pro(tree) then
        sum:= sum + 1;
    fi;
    
    return sum;
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
