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
#O  QuiverEltOps  . . . . . . . . . . . . . . . . . . . operations record.
##  
##  A quiver element is a linear combination of paths in a quiver.
##
QuiverEltOps:= OperationsRecord("QuiverEltOps");

#############################################################################
##  
#C  QuiverElt( <quiver>, <coef>, <elts> ) . . . . . . . . . . .  constructor.
##  
##  <#GAPDoc Label="QuiverElt">
##  <ManSection>
##  <Func Name="QuiverElt" Arg="n"/>
##  <Func Name="QuiverElt" Arg="l, r"/>
##  <Returns>
##    a new lean tree with components ...
##  </Returns>
##  <Description>
##  This is the simple constructor for lean trees ...
##  <Example>
##  gap> QuiverElt(q, [1], [[3, 4]]);
##  QuiverElt(q, [1], [[3. 4]])
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
QuiverElt:= function(quiver, coef, elts)
    local   self;
    self:= rec(quiver:= quiver, coef:= coef, elts:= elts);
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
QuiverEltOps.Print:= function(self)
    Print("QuiverElt( ", self.quiver, ", ", self.coef, ", ", self.elts, " )");
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
    local   q,  c,  e,  i,  pathL,  t,  j,  pathR,  s,  pro;
 
    if IsQuiverElt(l) then
        if IsQuiverElt(r) then
            if l.quiver <> r.quiver then
                Error("factors must belong to the same quiver");
            fi;
            
            q:= l.quiver;
            c:= [];
            e:= [];
            
            for i in [1..Length(l.elts)] do
                pathL:= l.elts[i];
                t:= Call(q.path1[pathL[Length(pathL)]], "Target");
                for j in [1..Length(r.elts)] do
                    pathR:= r.elts[j];
                    s:= Call(q.path1[pathR[1]], "Source");
                    
                    if s = t then
                        Add(c, l.coef[i] * r.coef[j]);
                        Add(e, Concatenation(pathL, pathR));
                    fi;
                od;
            od;
            
            pro:= QuiverElt(q, c, e);
        else
            pro:= QuiverElt(l.quiver, l.coef * r, l.elts);
        fi;
    else
        pro:= QuiverElt(r.quiver, l * r.coef, r.elts);
    fi;
    
    Normalize(pro);
    return pro;
end;    

#############################################################################
QuiverEltOps.\+:= function(l, r)
    local   q,  sum;
    
    if IsQuiverElt(l) then
        if IsQuiverElt(r) then
            if l.quiver <> r.quiver then
                Error("factors must belong to the same quiver");
            fi;
            
            q:= l.quiver;
            
            sum:= QuiverElt(q, Concatenation(l.coef, r.coef), 
                          Concatenation(l.elts, r.elts));
            Normalize(sum);
            return sum;
        else
            Error("<r> is not a QuiverElt");
        fi;
    else
        Error("<l> is not a QuiverElt");
    fi;
end;    


#############################################################################
QuiverEltOps.\-:= function(l, r)
    return l + (-1)*r;
end;

    
    
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
QuiverOps.Edges:= function(self)
    return List([1..Length(self.path1)], i-> QuiverElt(self, [1], [[i]]));
end;
