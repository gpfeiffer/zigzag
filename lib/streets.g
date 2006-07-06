#############################################################################
##
#A  arrows.g                     Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2006, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: streets.g,v 1.2 2006/07/06 19:27:54 goetz Exp $
##
##  This file contains support for bundles aka arrow classes.
##  
##  <#GAPDoc Label="Intro:Bundles">
##    An <E>bundle</E> <Index>bundle</Index> is a class of arrows.
##  <#/GAPDoc>
##

#############################################################################
##
##  Bundles aka Arrow Classes.
##
##  An *arrow class* is an equivalence class of arrows
##  under the conjugation action of W.
##
##  Representatives can be obtained by choosing s as representatives
##  of the orbits of N_L on L, for every shape representative L, ...
##



#############################################################################
##  
#O  BundleOps  . . . . . . . . . . . . . . . . . . . operations record.
##  
BundleOps:= OperationsRecord("BundleOps", DomainOps);

#############################################################################
##  
#C  Bundle( <W>, <arrow> )  . . . . . . . . . . . . . . . .  constructor.
##  
##  <#GAPDoc Label="Bundle">
##  <ManSection>
##  <Func Name="Bundle" Arg="W, J"/>
##  <Returns>
##    a new arrow class, an object that represents the class of <A>arrow</A>
##    under <A>W</A>.
##  </Returns>
##  <Description>
##  This is the simple constructor for an arrow class.  It constructs and
##  returns the class  of <A>arrow</A> in <A>W</A>.  Here <A>W</A> is a finite
##  Coxeter group of rank <M>n</M> and <A>J</A> is a subset of
##  <M>[1..n]</M>.
##  <Example>
##  gap> W:= CoxeterGroup("E", 6);; 
##  gap> Shape(W, [1, 2, 3]);
##  Shape( CoxeterGroup("E", 6), [ 1, 2, 3 ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  public fields:
##    W, the Coxeter group.
##    arrow, an arrow for W.
##  
Bundle:= function(W, arrow)
    return 
      rec(
          isDomain:= true,
          isBundle:= true,
          operations:= BundleOps,
          W:= W,
          arrow:= arrow
          );
end;

#############################################################################
##
#F  IsBundle( <obj> ) . . . . . . . . . . . . . . . . . . . . type check.
##
##  <#GAPDoc Label="IsBundle">
##  <ManSection>
##  <Func Name="IsBundle" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is an arrow class and <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsBundle:= function(obj)
    return IsRec(obj) and IsBound(obj.isBundle) 
           and obj.isBundle = true;
end;


#############################################################################  
##  
#F  Print( <shape> ) . . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
BundleOps.Print:= function(this)
    Print("Bundle( ", this.W, ", ", this.arrow, " )");
end;


#############################################################################
##
#F  Representative( <bundle> ) . . . . . . . . . . . . . . . . representative.
##
##  A shape, as a class of parabolic subsets, has a representative.
##
##  <#GAPDoc Label="Representative(shape)">
##  <ManSection>
##  <Meth Name="Representative" Arg="shape" Label="for shapes"/>
##  <Returns>a representative of the shape <A>shape</A>.</Returns>
##  <Description>The representative of a shape constructed 
##  as <C>Shape(W, J)</C> (see <Ref Label="Shape"/>) will be its
##  initial element <C>J</C>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> Representative(Shape(W, [2]));
##  [ 2 ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
BundleOps.Representative:= function(this)
    return this.arrow;
end;

#############################################################################
BundleOps.Children:= function(this)
    local   stab,  children,  o,  new;
    
    if IsBound(this.stab) then
        stab:= this.stab;
    elif IsBound(this.parent) then
        stab:= this.parent.stab;
        stab:= Stabilizer(stab, this.arrow[2][Length(this.arrow[2])]);
    else
        stab:= StabilizerArrow(this.W, this.arrow);
    fi;
    this.stab:= stab;
    
    children:= [];
    for o in Orbits(stab, ApplyFunc(Difference, this.arrow)) do
        new:= [this.arrow[1], Copy(this.arrow[2])];
        Add(new[2], o[1]);
        Add(children, Bundle(this.W, new));
    od;
    
    for o in children do
        o.parent:= this;
    od;
    
    return children;
end;

#############################################################################
##
#F  Bundles
##
Bundles0:= function(W)
    local   list,  hhh,  sh,  new,  N;
    
    list:= [];
    
    hhh:= function(arrow, N)
        local   L,  o,  s,  new,  Ns;
        
        L:= Difference(arrow[1], arrow[2]);
        for o in Orbits(N, L) do
            s:= o[1];
            new:= [arrow[1], Concatenation(arrow[2], [s])];
            Ns:= Stabilizer(N, s);
            Add(list, Bundle(W, new));
            hhh(new, Ns);
        od;
    end;
            
    for sh in Shapes(W) do
        new:= [Representative(sh), []];
        Add(list, Bundle(W, new));
        N:= Call(sh, "Complement");
        hhh(new, N);
    od;
    return list;
end;

Bundles:= function(W)
    local   list,  shape;
    list:= [];
    for shape in Shapes(W) do
        Append(list, BreadthFirst(Bundle(W, [shape.J, []])));
    od;
    return list;
end;

NrBundles:= function(W)
    return Sum(Shapes(W), x-> NrPreOrder(Bundle(W, [x.J, []])));
end;
    

EssentialBundles:= function(W)
    local   list,  hhh,  sh,  new,  N;
    
    list:= [];
    
    hhh:= function(arrow, N)
        local   L,  o,  s,  new,  Ns,  m,  c;
        
        L:= Difference(arrow[1], arrow[2]);
        for o in Orbits(N, L) do
            s:= o[1];
            new:= [arrow[1], Concatenation(arrow[2], [s])];
            m:= DeltaArrow(W, new);
            if m <> 0*m then
                c:= Bundle(W, new);
                m:= Call(c, "Matrix").mat;
                if m <> 0*m then 
                    Add(list, c);
                    Print(".\c");
                fi;
            fi;
            Ns:= Stabilizer(N, s);
            hhh(new, Ns);
        od;
    end;
            
    for sh in Shapes(W) do
        new:= [Representative(sh), []];
        Add(list, Bundle(W, new));
        N:= Call(sh, "Complement");
        hhh(new, N);
    od;
    return list;
end;

#############################################################################  
##  
#F  Elements( <shape> ) . . . . . . . . . . . . . . . . . . . . . . elements.
##  
##  <#GAPDoc Label="Elements(shape)">
##  <ManSection>
##  <Meth Name="Elements" Arg="shape" Label="for shapes"/>
##  <Returns>
##    the set of elements of the shape <A>shape</A>.
##  </Returns>
##  <Description>
##  The shape of <M>J</M> in <M>W</M> consists of all subsets of <M>S</M>
##  which are conjugate to <M>J</M> under <M>W</M>.
##  The conjugates can be efficiently computed
##  using <Cite Key="GePf2000" Where="Theorem 2.3.3"/>.
##  This is much faster than simple conjugacy tests.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> Elements(Shape(W, [2]));
##  [ [ 1 ], [ 2 ], [ 3 ] ] 
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
BundleOps.Elements:= function(this)
    local   elm,  W,  sh,  i,  j,  L,  list,  o,  x,  J,  t;
    
    elm:= [];
    W:= this.W;
    
    sh:= Shapes(W);  # carefully bring in sync with shape internals ...
    i:= PositionProperty(sh, x-> this.arrow[1] in x);
    j:= Position(Elements(sh[i]), this.arrow[1]);
    L:= sh[i].J;
    list:= OnTuples(this.arrow[2], sh[i].transversal[j]^-1);
    o:= Orbit(Call(sh[i], "Complement"), list, OnTuples);
    for x in sh[i].transversal do
        J:= OnSets(L, x);
        for t in o do
            Add(elm, [J, OnTuples(t, x)]);
        od;
    od;
    return Set(elm);
end;

#############################################################################
BundleOps.Tail:= function(this)
    return PositionProperty(Shapes(this.W), 
                   x-> ApplyFunc(Difference, this.arrow) in x);
end;

#############################################################################
BundleOps.Head:= function(this)
    return PositionProperty(Shapes(this.W), x-> this.arrow[1] in x);
end;


###
###  next:  the mu map.
###
BundleOps.Matrix:= function(this)
    local   sh,  L,  J,  subL,  mat,  e,  i;

    sh:= Shapes(this.W);
    L:= Call(this, "Head");
    J:= Call(this, "Tail");
    subL:= Elements(sh[L]);
    mat:= NullMat(Size(sh[L]), Size(sh[J]));
    for e in Elements(this) do
        i:= Position(subL, e[1]);
        mat[i]:= mat[i] + DeltaArrow(this.W, e);
    od;
    return rec(tail:= J, head:= L, mat:= mat);
end;

#  how to multiply two such matrices.  checked!  Turn into proper objects?
ProductArrowMatrices:= function(a, b)
    if a.tail = b.head then
        return rec(tail:= b.tail, head:= a.head, mat:= a.mat * b.mat);
    fi;
    return 0;
end;

##  the product of a list of arrows.
ProductArrowMatrixList:= function(list)
    local   product,  i;
    
    # trivial case: the empty product.
    if list = [] then return 1; fi;  # ???
    
    product:= list[1];
    for i in [2..Length(list)] do
        product:= ProductArrowMatrices(product, list[i]);
    od;
    
    return product;
end;



SumArrowMatrices:= function(a, b)
    if a.tail = b.tail and a.head = b.head then
        return rec(tail:= b.tail, head:= a.head, mat:= a.mat + b.mat);
    fi;
    Error("think ...");
end;


BundleOps.Delta:= function(this)
    local   sh,  J,  mat,  e;

    sh:= Shapes(this.W);
    J:= Call(this, "Tail");
    mat:= List(Elements(sh[J]), x-> 0);
    for e in Elements(this) do
        mat:= mat + DeltaArrow(this.W, e);
    od;
    return rec(support:= J, mat:= mat);
end;

# a path is a sequence of arrows, with adjacent ones multiplyable.
DeltaPath:= function(path)
    local   p;
    
    p:= ProductArrowMatrixList(List(path, x-> Call(x, "Matrix")));
    return rec(support:= p.tail, mat:= Sum(p.mat));
end;

BundleOps.BigMatrix:= function(this)
    local   sh,  m,  l,  mat;
    
    sh:= Shapes(this.W); 
    m:= Sum(sh, Size);
    l:= SetComposition(List(sh, Size));
    mat:= NullMat(m, m);
    m:= Call(this, "Matrix");
    mat{l[m.head]}{l[m.tail]}:= m.mat;
    return mat;
end;

    

Negative:= function(matrix)
    local   new;
    
    new:= ShallowCopy(matrix);
    new.mat:= -new.mat;
    return new;    
end;

##
##  Arrow classes can be multiplied. 
##
##  how to do this efficiently ?
##
BundleOps.\*:= function(l, r)
    local   W,  res,  all,  a,  b,  c;
    
    res:= [];
    
    #  arrow * arrow class.
    if not IsBundle(l) then
        for b in Elements(r) do
            c:= ProductArrows(l, b);
            if c <> 0 then
                Add(res, c);
            fi;
        od;
        return res;
    fi;
    
    # arrow class * arrow
    if not IsBundle(r) then
        for a in Elements(l) do
            c:= ProductArrows(a, r);
            if c <> 0 then
                Add(res, c);
            fi;
        od;
        return res;
    fi;
    
    # arrow class * arrow class.
    if l.W <> r.W then
        Error("factors must have same W component");
    fi;
    
    W:= l.W;
    
    # unless they fit together
    if Call(l, "Tail") <> Call(r, "Head") then
        return res;
    fi;
    
    # form all products of all members.
    all:= [];
    for a in Elements(l) do
        for b in Elements(r) do
            c:= ProductArrows(a, b);
            if c <> 0 then
                Add(all, c);
            fi;
        od;
    od;
    
    # Q: can the same nonzero c ever occur twice ?
    # no: because of unique factorization.
    
    a:= Length(all);
    all:= Set(all);
    if a <> Size(all) then
        Error("Panic: problem with unique factorization!");
    fi;
    
    
    # split into classes
    while all <> [] do
        c:= Bundle(W, all[1]);
        Add(res, c);
        a:= Length(all);
        all:= Difference(all, Elements(c));
        if a <> Size(all) + Size(c) then
            Error("Panic:  problem with arrow class products!");
        fi;
    od;
    
    return res;
end;

#############################################################################
BundleOps.Length:= function(this)
    return Length(this.arrow[2]);
end;

#############################################################################
##
##  the *depth* of an arrow class alpha is the Size of alpha(L),
##  the number of arrows in the class with the same head L.
##  the *width of an arrow class is the size of the shape of its head.
##  Thus the size of the class is its width
##  times its depth.  In most cases, the depth is 1.  Also,
##  arrow classes of larger depth tend to map to 0.
##
##
BundleOps.Depth:= function(this)
    return Index(StabilizerArrow(this.W, [this.arrow[1], []]),
                 StabilizerArrow(this.W, this.arrow));
end;

BundleOps.Width:= function(this)
    return Size(Shapes(this.W)[Call(this, "Head")]);
end;

#############################################################################
##  
##  Find the last irreducible factor (actually the first when you read
##  left to right ...)
##
BundleOps.Suffix:= function(this)
    local   fff,  i,  lft,  rgt,  pro;
    
    # idempotent case first.
    if this.arrow[2] = [] then
        return this;
    fi;
    
    # short case next.
    if Length(this.arrow[2]) = 1 then
        return this;
    fi;
    
    fff:= FactorsArrow(this.arrow);
    for i in [1..Length(fff)-1] do
        lft:= Bundle(this.W, ProductArrowList(fff{[1..i]}));
        rgt:= Bundle(this.W, ProductArrowList(fff{[i+1..Length(fff)]}));
        pro:= lft * rgt;
        if Length(pro) = 1 and pro[1] = this then
            return lft;
        fi;
    od;
    
    return this;
          
end;

# a path is a sequence of arrows, with adjacent ones multiplyable.
DeltaPath:= function(path)
    local   p;
    
    p:= ProductArrowMatrixList(List(path, x-> Call(x, "Matrix")));
    return rec(support:= p.tail, mat:= Sum(p.mat));
end;


QuiverRelations:= function(W)
    local   aaa,  path,  path0,  more,  a,  relations,  sss,  l,  
            null,  all,  mat,  delta,  new,  kern,  adr,  delete,  
            line,  pos,  i,  b;
    
    # start with a reasonably small set of arrow classes.
    aaa:= Filtered(Bundles(W), x-> IsNonZero(Call(x, "Delta").mat));
    aaa:= Filtered(aaa, x-> x = Call(x, "Suffix"));
    InfoZigzag1("Starting with ", Length(aaa), " arrow classes.\n");
    
    # split idempotents from nilpotents.
    path:= [];  path0:= [];  more:= [];
    for a in aaa do
        if a.arrow[2] = [] then
            Add(path0, a);
        else
            Add(more, [a]);
        fi;
    od;
    InfoZigzag1("Of which ", Length(path0), " have length 0.\n");
    
    relations:= [];
    
    sss:= SubsetsShapes(Shapes(W));
    l:= SetComposition(List(Shapes(W), Size));
    null:= List(sss, x-> 0);
    
    while more <> [] do
        
        Add(path, more);
        InfoZigzag1("Added ", Length(more), " paths of length ", Length(path), ".\n");
        
        # consider all paths at once.
        all:= Concatenation(path);
        
        mat:= [];
        for a in all do
            delta:= DeltaPath(a);
            new:= Copy(null);
            new{l[delta.support]}:= delta.mat;
            Add(mat, new);
        od;
        
        kern:= NullspaceMat(mat);
        InfoZigzag1("Found ", Length(kern), " relations.\n");
        
        
        # FIXME:
        # suppose adr is a list of back references such that 
        #   all[i] = path[adr[i][1]][adr[i][2]] ...
        adr:= Concatenation(List([1..Length(path)], i-> TransposedMat([List(path[i], x-> i), [1..Length(path[i])]])));

        
        # find all relations.
        delete:= List(path, x-> []);
        for line in kern do
            pos:= Filtered([1..Length(line)], i-> line[i] <> 0);
            Add(relations, rec(paths:= all{pos}, coeffs:= line{pos}));
            Add(delete[adr[pos[1]][1]], adr[pos[1]][2]);
        od;
        
        # remove obsoletes.
        for i in [1..Length(path)] do
            path[i]:= path[i]{Difference([1..Length(path[i])], delete[i])};
        od;
        
        InfoZigzag1("Length: ", List(path, Length), ": ", Length(path0) + Sum(path, Length), ".\n");
        
        # extend paths.
        more:= [];
        for a in path[Length(path)] do
            for b in path[1] do
                if a[Length(a)] * b[1] <> [] then
                    Add(more, Concatenation(a, b));
                fi; 
            od;
        od;
        
    od;
    
    return rec(path0:= path0, path:= path, relations:= relations);
end;

QuiverRelations0:= function(W)
    local   aaa,  path,  path0,  more,  a,  relations,  sss,  l,  
            null,  all,  mat,  delta,  new,  kern,  adr,  delete,  
            line,  pos,  i,  b;
    
    # start with a reasonably small set of arrow classes.
    aaa:= [];
    for a in Shapes(W) do
        Append(aaa, PreOrderProperty(Bundle(W, [a.J, []]), x-> IsNonZero(Call(x, "Delta").mat)));
        InfoZigzag1("\n");
    od;

#    aaa:= Filtered(Bundles(W), x-> IsNonZero(Call(x, "Delta").mat));
    aaa:= Filtered(aaa, x-> x = Call(x, "Suffix"));
    InfoZigzag1("Starting with ", Length(aaa), " arrow classes.\n");
    
    # split idempotents from nilpotents.
    path:= [];  path0:= [];  more:= [];
    for a in aaa do
        if a.arrow[2] = [] then
            Add(path0, a);
        else
            Add(more, [a]);
        fi;
    od;
    InfoZigzag1("Of which ", Length(path0), " have length 0.\n");
    
    relations:= [];
    
    sss:= SubsetsShapes(Shapes(W));
    l:= SetComposition(List(Shapes(W), Size));
    null:= List(sss, x-> 0);
    
    while more <> [] do
        
        Add(path, more);
        InfoZigzag1("Added ", Length(more), " paths of length ", Length(path), ".\n");
        
        # consider all paths at once.
        all:= Concatenation(path);
        
        mat:= [];
        for a in all do
            delta:= DeltaPath(a);
            new:= Copy(null);
            new{l[delta.support]}:= delta.mat;
            Add(mat, new);
        od;
        
        kern:= NullspaceMat(mat);
        InfoZigzag1("Found ", Length(kern), " relations.\n");
        
        
        # FIXME:
        # suppose adr is a list of back references such that 
        #   all[i] = path[adr[i][1]][adr[i][2]] ...
        adr:= Concatenation(List([1..Length(path)], i-> TransposedMat([List(path[i], x-> i), [1..Length(path[i])]])));

        
        # find all relations.
        delete:= List(path, x-> []);
        for line in kern do
            pos:= Filtered([1..Length(line)], i-> line[i] <> 0);
            Add(relations, rec(paths:= all{pos}, coeffs:= line{pos}));
            Add(delete[adr[pos[1]][1]], adr[pos[1]][2]);
        od;
        
        # remove obsoletes.
        for i in [1..Length(path)] do
            path[i]:= path[i]{Difference([1..Length(path[i])], delete[i])};
        od;
        
        InfoZigzag1("Length: ", List(path, Length), ": ", Length(path0) + Sum(path, Length), ".\n");
        
        # extend paths.
        more:= [];
        for a in path[Length(path)] do
            for b in path[1] do
                if a[Length(a)] * b[1] <> [] then
                    Add(more, Concatenation(a, b));
                fi; 
            od;
        od;
        
    od;
    
    return rec(path0:= path0, path:= path, relations:= relations);
end;

#############################################################################
##
##  a product for arrow classes forming a path ...
##
BundleProduct:= function ( abc )
    local  pro, i;
    pro := abc[1];
    for i  in [ 2 .. Length( abc ) ]  do
        pro := pro * abc[i];
        if Length( pro ) = 1  then
            pro := pro[1];
        else
            Error( "think!" );
        fi;
    od;
    return pro;
end;


#############################################################################
PrintQuiver:= function(qr)
    local   short,  shortarrow,  name,  vertex,  i,  gens,  e,  mat,  
            r,  p;
    
    short:= function(set)
        local   text,  s;
        
        text:= "";
        for s in set do
            Append(text, String(s));
        od;
        IsString(text);
        return text;
    end;
    
    shortarrow:= function(a)
        local   text;
        text:= "[";
        Append(text, short(a[1]));
        Append(text, ";");
        Append(text, short(a[2]));
        Append(text, "]");
        return text;
    end;
    
    vertex:= qr.path0;
    name:= NamesShapes(Shapes(vertex[1].W));
    PrintDynkinDiagram(vertex[1].W);
    
    Print("\nVertices:\n");
    for i in [1..Length(vertex)] do
        Print(i, ". ", name[i], " [", short(vertex[i].arrow[1]), "]\n");
    od;
    
    if qr.path = [] then return; fi;
    
    gens:= List(qr.path[1], x-> x[1]);
    Print("\nEdges:\n");
    for e in gens do
        mat:= Call(e, "Matrix");
        Print(mat.tail, " --> ", mat.head, ". ", 
              shortarrow(e.arrow), "\n");
    od;
    
    Print("\nRelations:\n");
    for r in qr.relations do
        if Difference(Union(r.paths), gens) = [] then
            i:= 0;
            for p in r.paths do
                i:= i + 1;
                Print("+", r.coeffs[i], "(");
                for e in p do
                    mat:= Call(e, "Matrix");
                    Print(mat.head, "---");
                od;
                Print(mat.tail, ") \c");
            od;
            for p in r.paths do
                for e in p do
                    Print(shortarrow(e.arrow), "\c");
                od;
                Print(", ");
            od;
            Print("\n");
        fi;
    od;
        
end;

#############################################################################
##
##  The Cartan Mat, decomposed along the radical series.
##
DimensionsMatrix:= function(qr)
    local   W,  l,  dim,  k,  mat,  p,  i,  j;
    
    W:= qr.path0[1].W;
    l:= Length(Shapes(W));
    dim:= [];
    for k in [1..Length(qr.path)] do
        mat:= NullMat(l, l);
        for p in qr.path[k] do
            i:= Call(p[1], "Matrix").head;
            j:= Call(p[Length(p)], "Matrix").tail;
            mat[i][j]:= mat[i][j] + 1;
        od;
        dim[k]:= mat;
    od;
    
    return dim;
end;



#############################################################################
VerifyQuiver:= function(qr)
    local   W,  D,  mu,  eee,  l,  a,  mat,  fa;
    
    # trivial case: nothing to verify.
    if qr.path = [] then
        return true;
    fi;
        
    W:= qr.path0[1].W;
    D:= DescentAlgebra(W);
    mu:= Call(D, "MuNu").mu;
    eee:= List(LeftRegularE(D), x-> x^mu);
    l:= SetComposition(List(Shapes(W), Size));
    
    # it suffices to check the paths of length 1.
    for a in qr.path[1] do
        Print("checking \c");
        mat:= Call(Product(a), "Matrix");
        Print(" ...\c");
        fa:= Sum(mat.mat) * eee{l[mat.tail]};
        fa{l[mat.head]}{l[mat.tail]}:= fa{l[mat.head]}{l[mat.tail]} - mat.mat;
        if fa <> 0*fa then 
            return false;
        fi;
        Print (" OK.  ");
        fa:= mat.mat[1] * eee{l[mat.tail]};
        if Length(l[mat.head]) * eee[l[mat.head][1]] * fa = fa then
            Print("Eigenvalue good also.\n");
        else
            Print("*** EIGENVALUE OUT OF LINE ***\n");
        fi;
        
    od;
    
    return true;
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
##  End:
##
