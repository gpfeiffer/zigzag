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
