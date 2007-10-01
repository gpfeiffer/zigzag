#############################################################################
##
#A  streets.g                     Götz Pfeiffer <goetz.pfeiffer@nuigalway.ie>
##
##  This file  is part of ZigZag  <http://schmidt.nuigalway.ie/zigzag>, a GAP
##  package for descent algebras of finite Coxeter groups.
##
#Y  Copyright (C) 2001-2007, Department of Mathematics, NUI, Galway, Ireland.
##
#A  $Id: streets.g,v 1.22 2007/10/01 08:43:26 goetz Exp $
##
##  This file contains support for streets aka alley classes.
##  
##  <#GAPDoc Label="Intro:Streets">
##    An <E>street</E> <Index>street</Index> is an orbit of alleys under the
##    conjugation action of W.
##  <#/GAPDoc>
##

#############################################################################
##  
#O  StreetOps  . . . . . . . . . . . . . . . . . . . operations record.
##  
StreetOps:= OperationsRecord("StreetOps", DomainOps);

#############################################################################
##  
#C  Street( <W>, <alley> )  . . . . . . . . . . . . . . . .  constructor.
##  
##  <#GAPDoc Label="Street">
##  <ManSection>
##  <Func Name="Street" Arg="W, J"/>
##  <Returns>
##    a new alley class, an object that represents the class of the alley
##    <A>alley</A> under <A>W</A>.
##  </Returns>
##  <Description>
##    This is the simple constructor for an alley class.  It constructs and
##  returns the class  of <A>alley</A> in <A>W</A>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);; 
##  gap> Street(W, [[1,2,3], [3]]);
##  Street( CoxeterGroup("A", 5), [ [ 1, 2, 3 ], [ 3 ] ] )
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
##  public fields:
##    W, the Coxeter group.
##    alley, an alley for W.
##  
Street:= function(W, alley)
    return 
      rec(
          isDomain:= true,
          isStreet:= true,
          operations:= StreetOps,
          W:= W,
          alley:= alley
          );
end;

#############################################################################
##
#F  IsStreet( <obj> )  . . . . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsStreet">
##  <ManSection>
##  <Func Name="IsStreet" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is an alley class and <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsStreet:= function(obj)
    return IsRec(obj) and IsBound(obj.isStreet) 
           and obj.isStreet = true;
end;


#############################################################################  
##  
#F  Print( <street> )  . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
StreetOps.Print:= function(self)
    Print("Street( ", self.W, ", ", self.alley, " )");
end;


#############################################################################
##
#F  Representative( <street> ) . . . . . . . . . . . . . . .  representative.
##
##  A street, as a class of parabolic subsets, has a representative.
##
##  <#GAPDoc Label="Representative(street)">
##  <ManSection>
##  <Meth Name="Representative" Arg="street" Label="for streets"/>
##  <Returns>a representative of the street <A>street</A>.</Returns>
##  <Description>The representative of a street constructed 
##  as <C>Street(W, J)</C> (see <Ref Label="Street"/>) will be its
##  initial element <C>J</C>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 3);;
##  gap> Representative(Street(W, [[1,2,3], [3]]));
##  [ [ 1, 2, 3 ], [ 3 ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##  
StreetOps.Representative:= function(self)
    return self.alley;
end;

#############################################################################  
##  
#F  Elements( <street> )  . . . . . . . . . . . . . . . . . . . . . elements.
##  
##  <#GAPDoc Label="Elements(street)">
##  <ManSection>
##  <Meth Name="Elements" Arg="street" Label="for streets"/>
##  <Returns>
##    the set of elements of the street <A>street</A>.
##  </Returns>
##  <Description>
##    The street of the alley <M>(L; s, t, \dots)</M> is its orbit under the
##    action of <M>A^*</M>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;                
##  gap> Elements(Street(W, [[1,2,3], [3]]));      
##  [ [ [ 1, 2, 3 ], [ 3 ] ], [ [ 2, 3, 4 ], [ 4 ] ], [ [ 3, 4, 5 ], [ 5 ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Elements:= function(self)
    local   elm,  W,  sh,  i,  j,  L,  list,  o,  x,  J,  t;
    
    elm:= [];
    W:= self.W;
    
    sh:= Shapes(W);  # carefully bring in sync with shape internals ...
    i:= PositionProperty(sh, x-> self.alley[1] in x);
    j:= Position(Elements(sh[i]), self.alley[1]);
    L:= sh[i].J;
    list:= OnTuples(self.alley[2], sh[i].transversal[j]^-1);
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
##
#F  Movers( <street> ) . . . . . . . . . . . . . . . . . . . . . . . movers.
##
##  The edges of the graph of a street are either movers or shakers.
##  
##  <#GAPDoc Label="Movers(street)">
##  <ManSection>
##  <Meth Name="Movers" Arg="street" Label="for streets"/>
##  <Returns>
##    a list of streets comprising the movers in the action graph of the
##    street <A>street</A>
##  </Returns>
##  <Description>
##    The edges of the action graph are either movers or shakers, following
##    Brink and Howlett~\cite{BriHow99}.  A mover is an edge with two
##    distinct vertices.  The movers of a street form a collection of
##    streets.  Given a street <A>street</A>, this method constructs and
##    returns the list of streets comprising the movers of <A>street</A>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Call(Street(W, [[1,2,3], [3]]), "Movers"); 
##  [ Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 4 ], [ 1, 4 ] ] ), 
##    Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 4 ], [ 4, 3 ] ] ) ]
##  gap> Union(last);
##  [ [ [ 1, 2, 3, 4 ], [ 1, 4 ] ], [ [ 1, 2, 3, 4 ], [ 4, 3 ] ], 
##    [ [ 2, 3, 4, 5 ], [ 2, 5 ] ], [ [ 2, 3, 4, 5 ], [ 5, 4 ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Movers:= function(self)
    local   n,  movers,  a,  i,  b,  K,  L,  d,  c,  new;
    
    n:= self.W.semisimpleRank;
    movers:= [];
    for a in Elements(self) do
        for i in [1..n] do
            if not i in a[1] then
                b:= [Union(a[1], [i]), Concatenation([i], a[2])];
                K:= a[1];  L:= b[1];
                d:= LongestCoxeterElement(ReflectionSubgroup(self.W, K))
                    * LongestCoxeterElement(ReflectionSubgroup(self.W, L));
                c:= OnAlleys(a, d);
                
                if c <> a then
                    AddSet(movers, b);
                fi;
            fi;
        od;
    od;
    
    new:= [];
    while movers <> [] do
        a:= Street(self.W, movers[1]);
        Add(new, a);
        movers:= Difference(movers, Elements(a));
    od;
    
    return new;
end;


StreetOps.MoversPlus:= function(self)
    local   n,  movers,  a,  i,  b,  K,  L,  d,  c,  new;
    
    n:= self.W.semisimpleRank;
    movers:= [];
    for a in Elements(self) do
        for i in [1..n] do
            if not i in a[1] then
                b:= [Union(a[1], [i]), Concatenation([i], a[2])];
                K:= a[1];  L:= b[1];
                d:= LongestCoxeterElement(ReflectionSubgroup(self.W, K))
                    * LongestCoxeterElement(ReflectionSubgroup(self.W, L));
                c:= OnAlleys(a, d);
                
                if c <> a then
                    AddSet(movers, b);
                fi;
            fi;
        od;
    od;
    
    new:= [];
    while movers <> [] do
        a:= Street(self.W, movers[1]);
        b:= Street(self.W, ReversedAlley(self.W, movers[1]));
        Add(new, a);
        movers:= Difference(movers, Elements(a));
        movers:= Difference(movers, Elements(b));
    od;
    
    return new;
end;


#############################################################################
##
#F  Shakers( <street> ) . . . . . . . . . . . . . . . . . . . . . . . shakers.
##
##  The edges of the graph of a street are either movers or shakers.
##  
##  <#GAPDoc Label="Shakers(street)">
##  <ManSection>
##  <Meth Name="Shakers" Arg="street" Label="for streets"/>
##  <Returns>
##    a list of streets comprising the shakers in the action graph of the
##    street <A>street</A>.
##  </Returns>
##  <Description>
##    The edges of the action graph are either movers or shakers, following
##    Brink and Howlett~\cite{BriHow99}.  A shaker is an edge whose initial
##    and terminal vertex coincide.  The shakers of a street form a
##    collection of streets.  Given a street <A>street</A>, this method
##    constructs and returns the list of streets comprising the shakers of
##    <A>street</A>.
##  <Example>
##  gap> W:= CoxeterGroup("A", 5);;
##  gap> Call(Street(W, [[1,2,3], [3]]), "Shakers"); 
##  [ Street( CoxeterGroup("A", 5), [ [ 1, 2, 3, 5 ], [ 5, 3 ] ] ) ]
##  gap> Elements(last[1]);
##  [ [ [ 1, 2, 3, 5 ], [ 5, 3 ] ], [ [ 1, 3, 4, 5 ], [ 1, 5 ] ] ]
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
StreetOps.Shakers:= function(self)
    local   n,  shakers,  a,  i,  b,  K,  L,  d,  c,  new;
    
    n:= self.W.semisimpleRank;
    shakers:= [];
    for a in Elements(self) do
        for i in [1..n] do
            if not i in a[1] then
                b:= [Union(a[1], [i]), Concatenation([i], a[2])];
                K:= a[1];  L:= b[1];
                d:= LongestCoxeterElement(ReflectionSubgroup(self.W, K))
                    * LongestCoxeterElement(ReflectionSubgroup(self.W, L));
                c:= OnAlleys(a, d);
                
                if c = a then
                    AddSet(shakers, b);
                fi;
            fi;
        od;
    od;
    
    new:= [];
    while shakers <> [] do
        a:= Street(self.W, shakers[1]);
        Add(new, a);
        shakers:= Difference(shakers, Elements(a));
    od;
    
    return new;
end;

#############################################################################
StreetOps.Suffix:= function(self)
    
    # an alley of length 0 has no suffix.
    if self.alley[2] = [] then return false; fi;
    
    # otherwise, form the longest nontrivial suffix.
    return Street(self.W, [Difference(self.alley[1], self.alley[2]{[1]}),
                   self.alley[2]{[2..Length(self.alley[2])]}]);
end;

##  TODO: find a more systematic way to list all inverse suffixes.
StreetOps.InverseSuffix:= function(self)
    return Concatenation(Call(self, "Movers"), Call(self, "Shakers"));
end;


StreetOps.Prefix:= function(self)
    
    # an alley of length 0 has no prefix.
    if self.alley[2] = [] then return false; fi;
    
    # otherwise, form the longest nontrivial prefix.
    return Street(self.W, [self.alley[1], 
                   self.alley[2]{[1..Length(self.alley[2])-1]}]);
end;

StreetOps.InversePrefix:= function(self)
    local   stab,  children,  o,  new;
    
    if IsBound(self.stab) then
        stab:= self.stab;
    elif IsBound(self.parent) then
        stab:= self.parent.stab;
        stab:= Stabilizer(stab, self.alley[2][Length(self.alley[2])]);
    else
        stab:= StabilizerAlley(self.W, self.alley);
    fi;
    self.stab:= stab;
    
    children:= [];
    for o in Orbits(stab, ApplyFunc(Difference, self.alley)) do
        new:= [self.alley[1], Copy(self.alley[2])];
        Add(new[2], o[1]);
        Add(children, Street(self.W, new));
    od;
    
    for o in children do
        o.parent:= self;
    od;
    
    return children;
end;

StreetOps.Children:= StreetOps.InversePrefix;

#############################################################################
##
#F  Streets( <W> )
##
Streets0:= function(W)
    local   list,  hhh,  sh,  new,  N;
    
    list:= [];
    
    hhh:= function(alley, N)
        local   L,  o,  s,  new,  Ns;
        
        L:= Difference(alley[1], alley[2]);
        for o in Orbits(N, L) do
            s:= o[1];
            new:= [alley[1], Concatenation(alley[2], [s])];
            Ns:= Stabilizer(N, s);
            Add(list, Street(W, new));
            hhh(new, Ns);
        od;
    end;
            
    for sh in Shapes(W) do
        new:= [Representative(sh), []];
        Add(list, Street(W, new));
        N:= Call(sh, "Complement");
        hhh(new, N);
    od;
    return list;
end;

Streets:= function(W)
    local   list,  shape;
    list:= [];
    for shape in Shapes(W) do
        Append(list, BreadthFirst(Call(shape, "Street")));
    od;
    return list;
end;

NrStreets:= function(W)
    return Sum(Shapes(W), x-> NrPreOrder(Call(x, "Street")));
end;
    

EssentialStreets:= function(W)
    local   list,  hhh,  sh,  new,  N;
    
    list:= [];
    
    hhh:= function(alley, N)
        local   L,  o,  s,  new,  Ns,  m,  c;
        
        L:= Difference(alley[1], alley[2]);
        for o in Orbits(N, L) do
            s:= o[1];
            new:= [alley[1], Concatenation(alley[2], [s])];
            m:= DeltaAlley(W, new);
            if m <> 0*m then
                c:= Street(W, new);
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
        Add(list, Street(W, new));
        N:= Call(sh, "Complement");
        hhh(new, N);
    od;
    return list;
end;

#############################################################################
StreetOps.Transversal:= function(self)
    #  FIXME:
    return 0;
end;

#############################################################################
StreetOps.Edges:= function(self)
    local   W,  S,  head,  hhh,  eee,  all,  edges,  a,  new,  l,  s;
    
    W:= self.W;
    S:= [1..W.semisimpleRank];
    head:= Shapes(W)[Call(self, "Head")];
    hhh:= Elements(head);
    eee:= Call(head, "Edges");
    all:= Elements(self);
    edges:= [];
    for a in all do
        new:= [];
        l:= Position(hhh, a[1]);
        for s in S do
            if not s in a[1] then
                new[s]:= Position(all, OnAlleys(a, eee[l][s].d));
            fi;
        od;
        Add(edges, new);
    od;
    return edges;
end;

#############################################################################
StreetOps.Relation:= function(self)
    return Relation(List(Call(self, "Edges"), Set));
end;


#############################################################################
StreetOps.SpanningTree:= function(self)
    #  FIXME:
    return 0;
end;


#############################################################################
StreetOps.Tail:= function(self)
    return PositionProperty(Shapes(self.W), 
                   x-> ApplyFunc(Difference, self.alley) in x);
end;

#############################################################################
StreetOps.Head:= function(self)
    return PositionProperty(Shapes(self.W), x-> self.alley[1] in x);
end;


###
###  next:  the mu map.
###
StreetOps.Matrix:= function(self)
    local   sh,  L,  J,  subL,  mat,  e,  i;

    sh:= Shapes(self.W);
    L:= Call(self, "Head");
    J:= Call(self, "Tail");
    subL:= Elements(sh[L]);
    mat:= NullMat(Size(sh[L]), Size(sh[J]));
    for e in Elements(self) do
        i:= Position(subL, e[1]);
        mat[i]:= mat[i] + DeltaAlley(self.W, e);
    od;
    return rec(tail:= J, head:= L, mat:= mat);
end;

#  how to multiply two such matrices.  checked!  Turn into proper objects?
ProductAlleyMatrices:= function(a, b)
    if a.tail = b.head then
        return rec(tail:= b.tail, head:= a.head, mat:= a.mat * b.mat);
    fi;
    return 0;
end;

##  the product of a list of alleys.
ProductAlleyMatrixList:= function(list)
    local   product,  i;
    
    # trivial case: the empty product.
    if list = [] then return 1; fi;  # ???
    
    product:= list[1];
    for i in [2..Length(list)] do
        product:= ProductAlleyMatrices(product, list[i]);
    od;
    
    return product;
end;



SumAlleyMatrices:= function(a, b)
    if a.tail = b.tail and a.head = b.head then
        return rec(tail:= b.tail, head:= a.head, mat:= a.mat + b.mat);
    fi;
    Error("think ...");
end;


StreetOps.Delta:= function(self)
    local   sh,  J,  mat,  e;

    sh:= Shapes(self.W);
    J:= Call(self, "Tail");
    mat:= List(Elements(sh[J]), x-> 0);
    for e in Elements(self) do
        mat:= mat + DeltaAlley(self.W, e);
    od;
    return rec(support:= J, mat:= mat);
end;

# a path is a sequence of alleys, with adjacent ones multiplyable.
DeltaPath:= function(path)
    local   p;
    
    p:= ProductAlleyMatrixList(List(path, x-> Call(x, "Matrix")));
    return rec(support:= p.tail, mat:= Sum(p.mat));
end;

StreetOps.BigMatrix:= function(self)
    local   sh,  m,  l,  mat;
    
    sh:= Shapes(self.W); 
    m:= Sum(sh, Size);
    l:= SetComposition(List(sh, Size));
    mat:= NullMat(m, m);
    m:= Call(self, "Matrix");
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
##  Alley classes can be multiplied. 
##
##  how to do this efficiently ?
##
StreetOps.\*:= function(l, r)
    local   W,  res,  all,  a,  b,  c;
    
    res:= [];
    
    #  alley * alley class.
    if not IsStreet(l) then
        for b in Elements(r) do
            c:= ProductAlleys(l, b);
            if c <> 0 then
                Add(res, c);
            fi;
        od;
        return res;
    fi;
    
    # alley class * alley
    if not IsStreet(r) then
        for a in Elements(l) do
            c:= ProductAlleys(a, r);
            if c <> 0 then
                Add(res, c);
            fi;
        od;
        return res;
    fi;
    
    # alley class * alley class.
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
            c:= ProductAlleys(a, b);
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
        c:= Street(W, all[1]);
        Add(res, c);
        a:= Length(all);
        all:= Difference(all, Elements(c));
        if a <> Size(all) + Size(c) then
            Error("Panic:  problem with alley class products!");
        fi;
    od;
    
    return res;
end;

#############################################################################
StreetOps.Length:= function(self)
    return Length(self.alley[2]);
end;

#############################################################################
##
##  the *depth* of an alley class alpha is the Size of alpha(L),
##  the number of alleys in the class with the same head L.
##  the *width of an alley class is the size of the shape of its head.
##  Thus the size of the class is its width
##  times its depth.  In most cases, the depth is 1.  Also,
##  alley classes of larger depth tend to map to 0.
##
##
StreetOps.Depth:= function(self)
    return Index(StabilizerAlley(self.W, [self.alley[1], []]),
                 StabilizerAlley(self.W, self.alley));
end;

StreetOps.Width:= function(self)
    return Size(Shapes(self.W)[Call(self, "Head")]);
end;

#############################################################################
##  
##  Find the last irreducible factor (actually the first when you read
##  left to right ...)
##
StreetOps.LongestSuffix:= function(self)
    local   fff,  i,  lft,  rgt,  pro;
    
    # idempotent case first.
    if self.alley[2] = [] then
        return self;
    fi;
    
    # short case next.
    if Length(self.alley[2]) = 1 then
        return self;
    fi;
    
    fff:= FactorsAlley(self.alley);
    for i in [1..Length(fff)-1] do
        lft:= Street(self.W, ProductAlleyList(fff{[1..i]}));
        rgt:= Street(self.W, ProductAlleyList(fff{[i+1..Length(fff)]}));
        pro:= lft * rgt;
        if Length(pro) = 1 and pro[1] = self then
            return lft;
        fi;
    od;
    
    return self;
          
end;

# a path is a sequence of alleys, with adjacent ones multiplyable.
DeltaPath:= function(path)
    local   p;
    
    p:= ProductAlleyMatrixList(List(path, x-> Call(x, "Matrix")));
    return rec(support:= p.tail, mat:= Sum(p.mat));
end;


#############################################################################
##
##  A procedure to represent an alley as a sum of (iterated delta images)
##  of streets.
##
StreetsAlley:= function(W, alley)
    
    # FIXME:
    return true;
end;


#############################################################################
QuiverRelations:= function(W)
    local   aaa,  bbb,  path,  path0,  more,  a,  relations,  sss,  l,  
            null,  all,  mat,  delta,  new,  kern,  adr,  delete,  
            line,  pos,  i,  b;
    
    # start with a reasonably small set of alley classes.
    bbb:= List(Shapes(W), x-> Call(x, "Street"));
    for a in bbb do 
        Append(bbb, Call(a, "MoversPlus"));
    od;
    InfoZigzag1("Generated ", Length(bbb), " streets\n");

    aaa:= Filtered(bbb, x-> IsNonZero(Call(x, "Delta").mat));
    InfoZigzag1("Of which ", Length(aaa), " are nonzero streets\n");
    
    aaa:= Filtered(aaa, x-> x = Call(x, "LongestSuffix"));
    InfoZigzag1("Starting with ", Length(aaa), " irreducible streets\n");
    
    # split idempotents from nilpotents.
    path:= [];  path0:= [];  more:= [];
    for a in aaa do
        if a.alley[2] = [] then
            Add(path0, a);
        else
            Add(more, [a]);
        fi;
    od;
    InfoZigzag1("of which ", Length(path0), " have length 0.\n");
    
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
        
        InfoZigzag1("Deleted: ", List(delete, Length), "\n");
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


QuiverRelations5:= function(W)
    local   aaa,  bbb,  path,  path0,  more,  a,  relations,  sss,  l,  
            null,  all,  mat,  delta,  new,  kern,  adr,  delete,  
            line,  pos,  i,  b;
    
    # start with a reasonably small set of alley classes.
    bbb:= List(Shapes(W), x-> Call(x, "Street"));
    for a in bbb do 
        aaa:= Call(a, "MoversPlus");
        aaa:= Filtered(aaa, x-> x = Call(x, "LongestSuffix"));
        Append(bbb, aaa);
    od;
    InfoZigzag1("Generated ", Length(bbb), " streets\n");

    aaa:= Filtered(bbb, x-> IsNonZero(Call(x, "Delta").mat));
    InfoZigzag1("Of which ", Length(aaa), " are nonzero streets\n");
    
    aaa:= Filtered(aaa, x-> x = Call(x, "LongestSuffix"));
    InfoZigzag1("Starting with ", Length(aaa), " irreducible streets\n");
    
    # split idempotents from nilpotents.
    path:= [];  path0:= [];  more:= [];
    for a in aaa do
        if a.alley[2] = [] then
            Add(path0, a);
        else
            Add(more, [a]);
        fi;
    od;
    InfoZigzag1("of which ", Length(path0), " have length 0.\n");
    
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
        
        InfoZigzag1("Deleted: ", List(delete, Length), "\n");
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

QuiverRelations1:= function(W)
    local   aaa,  bbb,  path,  path0,  more,  a,  relations,  sss,  l,  
            null,  all,  mat,  delta,  new,  kern,  adr,  delete,  
            line,  pos,  i,  b;
    
    # start with a reasonably small set of alley classes.
    bbb:= List(Shapes(W), x-> Call(x, "Street"));
    for a in bbb do 
        Append(bbb, Call(a, "Movers"));
    od;
    InfoZigzag1("Generated ", Length(bbb), " streets\n");

    aaa:= Filtered(bbb, x-> IsNonZero(Call(x, "Delta").mat));
    InfoZigzag1("Of which ", Length(aaa), " are nonzero streets\n");
    
    aaa:= Filtered(aaa, x-> x = Call(x, "LongestSuffix"));
    InfoZigzag1("Starting with ", Length(aaa), " irreducible streets\n");
    
    # split idempotents from nilpotents.
    path:= [];  path0:= [];  more:= [];
    for a in aaa do
        if a.alley[2] = [] then
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
    
    # start with a reasonably small set of alley classes.
    aaa:= [];
    for a in Shapes(W) do
        Append(aaa, PreOrderProperty(Street(W, [a.J, []]), x-> IsNonZero(Call(x, "Delta").mat)));
        InfoZigzag1("\n");
    od;

#    aaa:= Filtered(Streets(W), x-> IsNonZero(Call(x, "Delta").mat));
    aaa:= Filtered(aaa, x-> x = Call(x, "LongestSuffix"));
    InfoZigzag1("Starting with ", Length(aaa), " alley classes.\n");
    
    # split idempotents from nilpotents.
    path:= [];  path0:= [];  more:= [];
    for a in aaa do
        if a.alley[2] = [] then
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
##  a product for alley classes forming a path ...
##
StreetProduct:= function ( abc )
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
    local   short,  shortalley,  name,  vertex,  i,  gens,  e,  mat,  
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
    
    shortalley:= function(a)
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
        Print(i, ". ", name[i], " [", short(vertex[i].alley[1]), "]\n");
    od;
    
    if qr.path = [] then return; fi;
    
    gens:= List(qr.path[1], x-> x[1]);
    Print("\nEdges:\n");
    for e in gens do
        mat:= Call(e, "Matrix");
        Print(mat.tail, " --> ", mat.head, ". ", 
              shortalley(e.alley), "\n");
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
                    Print(shortalley(e.alley), "\c");
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

CartanMatQuiver:= function(qr)
    local car;
    
    car:= Sum(DimensionsMatrix(qr));
    return car + car^0;
end;

SpelledOutQuiver:= function(W)
    local   edg,  m,  lab,  ran,  i,  j;
    
    edg:= [];
    m:= DimensionsMatrix(QuiverRelations(W))[1];
    lab:= List(Shapes(W), s-> Call(s, "Label"));
    ran:= [1..Length(lab)];
    for i in ran do
        for j in ran do
            if m[i][j] > 0 then
                Add(edg, [lab[i], lab[j], m[i][j]]);
            fi;
        od;
    od;
    
    return edg;
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
    mu:= Call(D, "Mu");
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
#
#  dim is the result of DimensionsMatrix
#
ProjectiveModule:= function(dim, i)
    local   lis,  j;
    
    lis:= [0 * dim[1][1]];
    lis[1][i]:= 1;
    
    for j in [1..Length(dim)] do
        if IsNonZero(dim[j][i]) then
            Add(lis, dim[j][i]);
        fi;
    od;
            
    return lis;
end;

LaTeXProjectiveModule:= function(dim, nam, i)
    local   lis,  text,  j,  comma,  k;
    
    lis:= ProjectiveModule(dim, i);
    text:= "$\\begin{array}[b]{|c|}\\hline\n";
    for j in [1..Length(lis)] do
        comma:= false;
        for k in [1..Length(nam)] do
            if lis[j][k] > 0 then
                if comma then
                    Append(text, "\\, \c");
                fi;
                if lis[j][k] = 1 then
                    Append(text, nam[k]);
                else 
                    Append(text, "(");
                    Append(text, nam[k]);
                    Append(text, ")^{");
                    Append(text, String(lis[j][k]));
                    Append(text, "}");
                fi;
                comma:= true;
            fi;
        od;
        Append(text, "\\\\\\hline\n");
    od;
    Append(text, "\\end{array}$");
    
    return text;
end;


#############################################################################
##
##  The streets form a path algebra.
##
CartanMatStreets:= function(W)
    local   l,  mat,  b,  i,  j;
    
    l:= Length(Shapes(W));
    mat:= NullMat(l, l);
    for b in Streets(W) do
        i:= Call(b, "Head");
        j:= Call(b, "Tail");
        mat[i][j]:= mat[i][j] + 1;
    od;
    
    return mat;
end;

QuiverMatStreets:= function(W)
    local   c;
    c:= CartanMatStreets(W);
    return c^0 - c^-1; # c = d^0 + d^1 + d2 + ... => d = 1 - 1/c.
end;


#############################################################################
##
##  Movers as well
##
CartanMatMovers:= function(W)
    local   bbb,  a,  l,  mat,  b,  i,  j;
    
    bbb:= List(Shapes(W), x-> Call(x, "Street"));
    for a in bbb do 
        Append(bbb, Call(a, "Movers"));
    od;
    InfoZigzag1("Generated ", Length(bbb), " streets\n");
    
    l:= Length(Shapes(W));
    mat:= NullMat(l, l);
    for b in bbb do
        i:= Call(b, "Head");
        j:= Call(b, "Tail");
        mat[i][j]:= mat[i][j] + 1;
    od;
    
    return mat;
end;

QuiverMatMovers:= function(W)
    local   c;
    c:= CartanMatMovers(W);
    return c^0 - c^-1; # c = d^0 + d^1 + d2 + ... => d = 1 - 1/c.
end;


#############################################################################
##
##  Movers Plus as well
##
CartanMatMoversPlus:= function(W)
    local   bbb,  a,  l,  mat,  b,  i,  j;
    
    bbb:= List(Shapes(W), x-> Call(x, "Street"));
    for a in bbb do 
        Append(bbb, Call(a, "MoversPlus"));
    od;
    InfoZigzag1("Generated ", Length(bbb), " streets\n");
    
    l:= Length(Shapes(W));
    mat:= NullMat(l, l);
    for b in bbb do
        i:= Call(b, "Head");
        j:= Call(b, "Tail");
        mat[i][j]:= mat[i][j] + 1;
    od;
    
    return mat;
end;

QuiverMatMoversPlus:= function(W)
    local   c;
    c:= CartanMatMoversPlus(W);
    return c^0 - c^-1; # c = d^0 + d^1 + d2 + ... => d = 1 - 1/c.
end;


#############################################################################
##
##  Movers Plus NonZero is not!!!  At least not for type A_n, n > 4; E_6.
##
CartanMatMoversPlusNZ:= function(W)
    local   bbb,  a,  l,  mat,  b,  i,  j;
    
    bbb:= List(Shapes(W), x-> Call(x, "Street"));
    for a in bbb do 
        Append(bbb, Call(a, "MoversPlus"));
    od;
    InfoZigzag1("Generated ", Length(bbb), " streets\n");
    bbb:= Filtered(bbb, x-> IsNonZero(Call(x, "Delta").mat));
    InfoZigzag1("Of which ", Length(bbb), " are nonzero streets\n");
    
    l:= Length(Shapes(W));
    mat:= NullMat(l, l);
    for b in bbb do
        i:= Call(b, "Head");
        j:= Call(b, "Tail");
        mat[i][j]:= mat[i][j] + 1;
    od;
    
    return mat;
end;

QuiverMatMoversPlusNZ:= function(W)
    local   c;
    c:= CartanMatMoversPlusNZ(W);
    return c^0 - c^-1; # c = d^0 + d^1 + d2 + ... => d = 1 - 1/c.
end;

#############################################################################
##
##  given a square matrix 'mat', determine the blocks of the equivalence
##  relation '-' generated by i - j if mat[i][j] <> 0.
##
BlocksMat:= function(mat)
    local   l,  list,  i,  j,  new,  k;
    
    l:= Length(mat);
    list:= List([1..l], i-> [i]);
    for i in [1..l] do
        for j in [1..l] do
            if i <> j and mat[i][j] <> 0 and list[i] <> list[j] then
                # join the blocks of i and j:
                new:= Union(list[i], list[j]);
                for k in new do
                    list[k]:= new;
                od;
            fi;
        od;
    od;
    return list;
end;


#############################################################################
##
#E  Emacs  . . . . . . . . . . . . . . . . . . . . . . local emacs variables.
##
##  Local Variables:
##  mode:               gap
##  outline-regexp:     "#F\\|#V\\|#E\\|#A\\|#O\\|#C"
##  fill-column:        77
##  End:
##
