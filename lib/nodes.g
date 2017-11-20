#############################################################################
##
##  Nodes.
##
##  A node is a pair of an *index* and a list *children* of
##  nodes. The root node has index 0.
##

#############################################################################
##
##  Operations Record.
##
NodeOps:= OperationsRecord("NodeOps");

#############################################################################
##
##  Constructor.
##
Node:= function(index)
    return rec(index:= index, children:= [], operations:= NodeOps);
end;

#############################################################################
##
##  Equality.  Two nodes are equal if they have the same index and,
##  recursively, equal children.
##
NodeOps.\=:= function(l, r)
    return l.index = r.index and l.children = r.children;
end;

#############################################################################
##
##  Children.  This makes nodes usable by the walkers in walker.g
##
NodeOps.Children:= function(self)
    return self.children;
end;


#############################################################################
##
##  Print.
##
NodeOps.Print:= function(self)
    Print(self.index);
end;

#############################################################################
##
##  Display a node's tree structure.
##
NodeOps.indent:= 0;

NodeOps.Display:= function(self, dummy)
    local   isLeaf,  c;

    isLeaf:= self.children = [];

    for c in [1..NodeOps.indent] do
        Print(" ");
    od;
    Print(",[", self.index);
    if not isLeaf then
        Print("\n");
    fi;

    NodeOps.indent:= NodeOps.indent + 2;
    for c in self.children do
        Display(c);
    od;
    NodeOps.indent:= NodeOps.indent - 2;
    if not isLeaf then
        for c in [0..NodeOps.indent] do
            Print(" ");
        od;
    fi;
    Print("]");
    Print("\n");
end;


#############################################################################
##
##  Size.  A node's size  is the number of paths through its children.  DFS.
##
NodeOps.Size:= function(self)
    local   size,  child;
    size:= 1;
    for child in self.children do
        size:= size + Call(child, "Size");
    od;
    return size;
end;

#############################################################################
##
##  Nodes.  The set of all nodes in the tree.
##
NodeOps.Nodes:= function(self)
    local   nodes,  child;
    nodes:= [];
    for child in self.children do
        UniteSet(nodes, Call(child, "Nodes"));
    od;
    AddSet(nodes, self);
    return nodes;
end;

#############################################################################
##
##  Sets.  The set of all paths in the tree.
##
NodeOps.Sets:= function(self)
    local   ancestors,  sets,  walker;

    ancestors:= [];
    sets:= [];
    walker:= function(node, depth)
        local   set,  child;

        # determine this node's set and add
        set:= ancestors{[1..depth]};
        Add(sets, set);

        # recurse
        for child in node.children do
            ancestors[depth+1]:= child.index;
            walker(child, depth+1);
        od;
    end;
    walker(self, 0);
    return sets;
end;


CompressTree:= function(tree)
    local   ttt,  v;
    ttt:= [];
    v:= function ( t )
        local   i,  c,  pos;
        for i in [1..Length(t.children)] do
            c:= t.children[i];
            v( c );
            pos:= Position(ttt, c);
            if pos <> false then
                t.children[i]:= ttt[pos];
            else
                Add(ttt, c);
            fi;
        od;
    end;
    v(tree);
end;

ShowGraph:= function(g)
    local   orbit,  n,  c;
    orbit:= [g];
    for n in orbit do
        Print(n, ": \c");
        for c in n.children do
            Print(c, ", \c");
            if not c in orbit then
                Add(orbit, c);
            fi;
        od;
        Print("\n");
    od;
end;

JsonGraph:= function(g)
    local   orbit,  n,  c,  text,  i,  j;
    orbit:= [g];
    for n in orbit do
        Print(n, ": \c");
        for c in n.children do
            Print(c, ", \c");
            if not c in orbit then
                Add(orbit, c);
            fi;
        od;
        Print("\n");
    od;
    text:= List(orbit, x-> Concatenation("{\"name\":\"", String(x.index), "\",\"group\":1},\n"));
    text:= Concatenation(text);
    Unbind(text[Length(text)]);
    Unbind(text[Length(text)]);
    text:= Concatenation("\"nodes\":[\n", text, "\n],\n");
    Append(text, "\"links\":[\n");
    for  i in [1..Length(orbit)] do
        for c in orbit[i].children do
            j:= Position(orbit, c);
            Append(text, "{\"source\":");
            Append(text, String(i-1));
            Append(text, ",\"target\":");
            Append(text, String(j-1));
            Append(text, ",\"value\":1},\n");
        od;
    od;
    Unbind(text[Length(text)]);
    Unbind(text[Length(text)]);
    text:= Concatenation("{\n", text, "\n]\n}\n");
    return text;
end;


#############################################################################
##
##  How to save a node (and the entire graph it is part of) to a text file
##
NodeOps.Save:= function(self, filename)
    local   nodes,  iii,  i;

    nodes:= Call(self, "Nodes");
    iii:= List(nodes, x-> x.index);
    PrintTo(filename, "nodes:= List(\n");
    AppendTo(filename, BlanklessPrint(iii));
    AppendTo(filename, ", i-> Node(i));\n");
    for i in [1..Length(nodes)] do nodes[i].pos:= i; od;
    for i in [1..Length(nodes)] do
        AppendTo(filename, "nodes[");
        AppendTo(filename, i);
        AppendTo(filename, "].children:= nodes{");
        AppendTo(filename, BlanklessPrint(List(nodes[i].children, x-> x.pos)));
        AppendTo(filename, "};\n");
    od;
end;
