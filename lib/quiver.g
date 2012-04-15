#############################################################################
##
#A  quiver.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2010  Götz Pfeiffer
##
##  This file contains routines for path algebras and their elements.
##
##  <#GAPDoc Label="Intro:Quivers">
##    Quivers are directed graphs ...
##      
##    The functions described in this chapter are implemented in the file
##    <F>quiver.g</F>.  
##  <#/GAPDoc>
##
##  TODO: make them a proper GAP algebra !?!
##

#############################################################################
##
##  Quivers.  (As path algebras)
##
    
    
#############################################################################
##  
#O  QuiverOps  . . . . . . . . . . . . . . . . . . . operations record.
##  
##  A quiver is a ...
##
QuiverOps:= OperationsRecord("QuiverOps", AlgebraOps);

#############################################################################
##  FIXME
Quiver:= function(q)
    q:= Copy(q);
    q.isQuiver:= true;
    q.operations:= QuiverOps;
    return q;
end;
    

#############################################################################
##
#F  IsQuiver( <obj> )  . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsQuiver">
##  <ManSection>
##  <Func Name="IsQuiver" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a quiver  and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsQuiver:= function(obj)
    return IsRec(obj) and IsBound(obj.isQuiver) and obj.isQuiver = true;
end;

#############################################################################
QuiverOps.\=:= function(l, r)
    if IsQuiver(l) and IsQuiver(r) then
        return l.path0 = r.path0 and l.path1 = r.path1 and l.pathmat = r.pathmat;
    else
        return false;
    fi;
end;
    

#############################################################################
QuiverOps.Edges:= function(self)
    return List([1..Length(self.path1)], i-> QuiverElt(self, [1], [[i]]));
end;


#############################################################################
##
##  Edges.  (of quivers)
##
    
    
#############################################################################
##  
#O  EdgeOps  . . . . . . . . . . . . . . . . . . . operations record.
##  
##  An edge is an operator, capable of turning one vertex into the next
##  through the function stored in its 'nextVertex' component.
##
EdgeOps:= OperationsRecord("EdgeOps");

#############################################################################
##
##  constructor
##
Edge:= function(data, nextVertex)
    local   self;
    self:= rec();
    self.data:= data;
    self.nextVertex:= nextVertex;
    self.isEdge:= true;
    self.operations:= EdgeOps;
    return self;
end;
    

#############################################################################
##
#F  IsEdge( <obj> )  . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsEdge">
##  <ManSection>
##  <Func Name="IsEdge" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a edge  and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsEdge:= function(obj)
    return IsRec(obj) and IsBound(obj.isEdge) and obj.isEdge = true;
end;


EdgeOps.Print:= function(self)
    Print(self.data);
end;


#############################################################################
##
#F  <l> = <r>  . . . . . . . . . . . . . . . . . . . . . . . . equality test.
##
EdgeOps.\= := function(l, r)
    if not IsEdge(l) then return false; fi;
    if not IsEdge(r) then return false; fi;
    return l.data = r.data;
end;

#############################################################################
##
#F  <l> < <r>  . . . . . . . . . . . . . . . . . . . . . . . . .  comparison.
##
EdgeOps.\< := function(l, r)
    if not IsEdge(l) then return false; fi;
    if not IsEdge(r) then return true; fi;
    return l.data < r.data;
end;

EdgeOps.\^:= function(vertex, self)
    return self.nextVertex(vertex, self);
end;


#############################################################################
NextPartition:= function(vertex, edge)
    local   a,  b,  i,  new;
    a:= edge.data[1];
    b:= edge.data[2];
    i:= Position(vertex, a+b);
    if i = false then return false; fi;
    new:= Copy(vertex);
    new[i]:= a;
    Add(new, b);
    Sort(new);
    return new;
end;
    
PartitionEdge:= function(a, b)
    return Edge([a,b], NextPartition);
end;


#############################################################################
NextSubset:= function(vertex, edge)
    local   a,  set;
    a:= edge.data;
    set:= Copy(vertex);
    if not a in set then
        return false;
    fi;
    RemoveSet(set, a);
    return set;
end;

TakeAwayEdge:= function(a)
    return Edge(a, NextSubset);
end;


#############################################################################
##
##  Paths.  (of quivers)
##

#############################################################################
##  
#O  PathOps  . . . . . . . . . . . . . . . . . . . operations record.
##  
##  A path is a pair, consisting of a vertex 'source' and a (possibly empty)
##  list of edges.
##
PathOps:= OperationsRecord("PathOps");

#############################################################################
##
##  constructor
##
Path:= function(source, edges)
    local   target,  edge,  self;
    
    # compute target.
    target:= source;
    for edge in edges do
        target:= target^edge;
        if target = false then
            return false;
        fi;
    od;
    
    # construct new object.
    self:= rec();
    self.source:= source;
    self.edges:= edges;
    self.target:= target;
    self.isPath:= true;
    self.operations:= PathOps;
    return self;
end;
    

#############################################################################
##
#F  IsPath( <obj> )  . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsPath">
##  <ManSection>
##  <Func Name="IsPath" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a path  and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsPath:= function(obj)
    return IsRec(obj) and IsBound(obj.isPath) and obj.isPath = true;
end;


PathOps.Print:= function(self)
    Print("Path( ", self.source, ", ", self.edges, " )");
end;

PathOps.Source:= function(self)
    return self.source;
end;

PathOps.Target:= function(self)
    return self.target;
end;


PathOps.\*:= function(l, r)
    # path * edge
    if IsEdge(r) then
        return Path(l.source, Concatenation(l.edges, [r]));
    fi;
    
    # path * path
    if l.target <> r.source then
        return false;
    fi;
    return Path(l.source, Concatenation(l.edges, r.edges));
end;


#############################################################################
AddPartPartitionPath:= function(path, part)
    local   source;
    source:= Copy(path.source);
    Add(source, part);
    Sort(source);
    return Path(source, path.edges);
end;
    

#############################################################################
##  
#O  QuiverEltOps  . . . . . . . . . . . . . . . . . . . operations record.
##  
##  A quiver element is a linear combination of paths
##
QuiverEltOps:= OperationsRecord("QuiverEltOps");

#############################################################################
##  
#C  QuiverElt( <coef>, <elts> ) . . . . . . . . . . .  constructor.
##  
##  <#GAPDoc Label="QuiverElt">
##  <ManSection>
##  <Func Name="QuiverElt" Arg="coef, elts"/>
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
QuiverElt:= function(coef, elts)
    local   self;
    self:= rec();
    self.coef:= coef;
    self.elts:= elts;
    self.isQuiverElt:= true;
    self.operations:= QuiverEltOps;
    return self;
end;


#############################################################################
##
#F  IsQuiverElt( <obj> )  . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsQuiverElt">
##  <ManSection>
##  <Func Name="IsQuiverElt" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a quiver element and <K>false</K>
##    otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsQuiverElt:= function(obj)
    return IsRec(obj) and IsBound(obj.isQuiverElt) and obj.isQuiverElt = true;
end;

#############################################################################
QuiverEltOps.\=:= function(l, r)
    
    if IsQuiverElt(l) then
        if IsQuiverElt(r) then
            return l.coef = r.coef and l.elts = r.elts;
        else
            return false;
        fi;
    else
        return false;
    fi;
end;    


#############################################################################
QuiverEltOps.Print:= function(self)
    Print("QuiverElt( ", self.coef, ", ", self.elts, " )");
end;

# how to normalize a list e of elements with coefficients c
QuiverEltOps.Normalize:= function(self)
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
QuiverEltOps.\*:= function(l, r)
    local   c,  e,  i,  j,  path,  pro;
 
    if IsQuiverElt(l) then
        if IsQuiverElt(r) then
            c:= [];
            e:= [];
            for i in [1..Length(l.elts)] do
                for j in [1..Length(r.elts)] do
                    path:= l.elts[i] * r.elts[j];
                    if path <> false then
                        Add(c, l.coef[i] * r.coef[j]);
                        Add(e, path);
                    fi;
                od;
            od;
            pro:= QuiverElt(c, e);
        elif IsEdge(r) then
            pro:= QuiverElt(l.coef, List(l.elts, x-> x * r));
        else
            pro:= QuiverElt(l.coef * r, l.elts);
        fi;
    else
        pro:= QuiverElt(l * r.coef, r.elts);
    fi;
    
    Call(pro, "Normalize");
    return pro;
end;    

#############################################################################
QuiverEltOps.\+:= function(l, r)
    local   sum;
    
    # check arguments.
    if not IsQuiverElt(r) then
        Error("<r> is not a QuiverElt");
    fi;
    if not IsQuiverElt(l) then
        Error("<l> is not a QuiverElt");
    fi;
    
    # form the sum.
    sum:= QuiverElt(Concatenation(l.coef, r.coef), 
                  Concatenation(l.elts, r.elts));
    Call(sum, "Normalize");
    return sum;
end;    


#############################################################################
QuiverEltOps.\-:= function(l, r)
    return l + (-1)*r;
end;


#############################################################################
AddPartPartitionQuiverElt:= function(qe, part)
    return QuiverElt(qe.coef, List(qe.elts, x-> AddPartPartitionPath(x, part)));
end;
    
#############################################################################
PathsPartitionQuiver:= function(n)
    local   vertices,  edges,  j,  i,  paths,  v,  p,  e;
    
    vertices:= List(Partitions(n), Reversed);
    edges:= [];
    for j in [2..n-1] do
        for i in [1..Minimum(j-1, n-j)] do 
            Add(edges, PartitionEdge(i, j));
        od;
    od;
    
    paths:= [];
    
    for v in vertices do
        p:= Path(v, []);
        if p <> false then
            Add(paths, p);
        fi;
    od;
    
    # orbit algorithm.
    for p in paths do
        for e in edges do
            v:= p * e;
            if v <> false then
                Add(paths, v);
            fi;
        od;
    od;
    
    return paths;
    
end;
