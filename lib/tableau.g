#############################################################################
##
#A  tableau.g
##
#A  This file is part of ZigZag <http://schmidt.nuigalway.ie/zigzag>.
##
#Y  Copyright (C) 2012  Götz Pfeiffer
##
##  This file contains support for Young tableaus.
##  
##  <#GAPDoc Label="Intro:Tableau">
##    A <E>tableau</E><Index>tableau</Index> is ...
##    <P/>
##
##    The functions described in this chapter are implemented in the file
##    <F>tableau.g</F>.  
##  <#/GAPDoc>
##

#############################################################################
##  
#O  TableauOps . . . . . . . . . . . . . . . . . . . . . .  operations record.
##  
TableauOps:= OperationsRecord("TableauOps");

#############################################################################
##  
#C  Tableau( <W>, <alley> ) . . . . . . . . . . . . . . . . . . . constructor.
##  
##  <#GAPDoc Label="Tableau">
##  <ManSection>
##  <Func Name="Tableau" Arg="rows"/>
##  <Returns>
##    a new tableau
##  </Returns>
##  <Description>
##    This is the simple constructor for tableaus.  It constructs and returns
##    the tableau consisting of  <A>rows</A>.
##  <Example>
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
Tableau:= function(rows)
    return 
      rec(
          isTableau:= true,
          operations:= TableauOps,
          rows:= rows
          );
end;


#############################################################################
##
#F  IsTableau( <obj> ) . . . . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsTableau">
##  <ManSection>
##  <Func Name="IsTableau" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a tableau and <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsTableau:= function(obj)
    return IsRec(obj) and IsBound(obj.isTableau) 
           and obj.isTableau = true;
end;


#############################################################################  
##  
#M  Print( <tableau> ) . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
TableauOps.Print:= function(self)
    Print("Tableau( ", self.rows, " )");
end;

#############################################################################
PartitionOps.PartialSums:= function(self)
    local   sum,  sums,  a;
    sum:= 0;
    sums:= [sum];
    for a in self.parts do
        sum:= sum + a;
        Add(sums, sum);
    od;
    return sums;
end;
      

#############################################################################
PartitionOps.CanonicalTableau:= function(self)
    local   sums;
    sums:= Call(self, "PartialSums");
    return Tableau(List([1..Length(self.parts)], i-> [sums[i]+1..sums[i+1]]));
end;

#############################################################################
TableauOps.Transposed:= function(self)
    local   rows,  i,  j;
    rows:= List(self.rows[1], x-> []);
    for i in [1..Length(self.rows)] do
        for j in [1..Length(self.rows[i])] do
            rows[j][i]:= self.rows[i][j];
        od;
    od;
    return Tableau(rows);
end;

#############################################################################
TableauOps.Permutation:= function(self)
    return PermList(Concatenation(self.rows));
end;


#############################################################################
TableauOps.Shape:= function(self)
    return Partition(List(self.rows), Length);
end;

#############################################################################
##
##  action of the symmetric group on tableaus
##
OnTableaus:= function(tableau, perm)
    return Tableau(List(tableau.rows, x-> OnTuples(x, perm)));
end;

#############################################################################
TableauOps.Size:= function(self)
    return Sum(self.rows, Length);
end;

#############################################################################
TableauOps.ICoordinates:= function(self)
    local   list,  i,  k;
    list:= [];
    for i in [1..Length(self.rows)] do
        for k in self.rows[i] do
            list[k]:= i;
        od;
    od;
    return list;
end;
    
#############################################################################
TableauOps.JCoordinates:= function(self)
    local   list,  row,  j;
    list:= [];
    for row in self.rows do
        for j in [1..Length(row)] do 
            list[row[j]]:= j;
        od;
    od;
    return list;
end;


#############################################################################
##
#W  can we avoid the explicit construction of the transposed tableau?
#W  how about testing whether the permutation of this tableau is
#W  a prefix of the permutation of this shape?
##
TableauOps.IsStandard:= function(self)
    return ForAll(self.rows, IsSet) and ForAll(Transposed(self).rows, IsSet);
end;

#############################################################################
##
##  compute the set of admissible adjacent transpositions.
##  here i stands for the transposition (i,i+1)
##  La: i and i+1 can be swapped iff they don't sit in the same row or column.
##
TableauOps.AdmissibleTranspositions:= function(self)
    local   ico,  jco;
    ico:= Call(self, "ICoordinates");
    jco:= Call(self, "JCoordinates");
    return Filtered([1..Length(ico)-1], 
                   k-> ico[k] <> ico[k+1] and jco[k]<>jco[k+1]);
end;

#############################################################################
##
##  which transpositions result in a standard tableau even further away
##  from the canonical one.
##
TableauOps.FurtherTranspositions:= function(self)
    local   ico,  jco;
    ico:= Call(self, "ICoordinates");
    jco:= Call(self, "JCoordinates");
    return Filtered([1..Length(ico)-1], 
                   k-> ico[k] < ico[k+1] and jco[k]<>jco[k+1]);
end;

#############################################################################
##
##  make all standard tableaus of a given shape
##
PartitionOps.StandardTableaus:=  function(self)
    local   orbit,  tab,  i,  new;
    
    ##  orbit algorithm
    orbit:= [Call(self, "CanonicalTableau")];
    for tab in orbit do
        for i in  Call(tab, "FurtherTranspositions") do
            new:= OnTableaus(tab, (i, i+1));
            if not new in orbit then
                Add(orbit, new);
            fi;
        od;
    od;
    return orbit;  #FIXME:  or Set(orbit)?
end;


#############################################################################
PartitionOps.RemovableBoxes:= function(self)
    local   l;
    l:= Length(self.parts);
    return Filtered([1..l], k-> k = l or self.parts[k] > self.parts[k+1]);
end;

#############################################################################
StandardTableaus:= function(n)
    return Union(List(Partitions(n), p-> Call(Partition(p), "StandardTableaus")));
end;

#############################################################################
TableauOps.Descents:= function(self)
    local   jco;
    jco:= Call(self, "JCoordinates");
    return Filtered([1..Length(jco)-1], i-> jco[i] < jco[i+1]);
end; 

TableauOps.MajorIndex:= function(self)
    return Sum(Call(self, "Descents"));    
end;
    


#############################################################################
##  
#O  ContentOps . . . . . . . . . . . . . . . . . . . . . .  operations record.
##  
ContentOps:= OperationsRecord("ContentOps");

#############################################################################
##  
#C  Content( <list> ) . . . . . . . . . . . . . . . . . . . constructor.
##  
##  <#GAPDoc Label="Content">
##  <ManSection>
##  <Func Name="Content" Arg="list"/>
##  <Returns>
##    a new content
##  </Returns>
##  <Description>
##    This is the simple constructor for contents.  It constructs and returns
##    the content consisting of  <A>list</A>.
##  <Example>
##  </Example>
##  </Description>
##  </ManSection>
##  <#/GAPDoc>
##
Content:= function(list)
    return 
      rec(
          isContent:= true,
          operations:= ContentOps,
          list:= list
          );
end;


#############################################################################
##
#F  IsContent( <obj> ) . . . . . . . . . . . . . . . . . . . . .  type check.
##
##  <#GAPDoc Label="IsContent">
##  <ManSection>
##  <Func Name="IsContent" Arg="obj"/>
##  <Returns>
##    <K>true</K> if <A>obj</A> is a content and <K>false</K> otherwise.
##  </Returns>
##  </ManSection>
##  <#/GAPDoc>
##                   
IsContent:= function(obj)
    return IsRec(obj) and IsBound(obj.isContent) 
           and obj.isContent = true;
end;


#############################################################################  
##  
#M  Print( <content> ) . . . . . . . . . . . . . . . . . . . . . . . . print.
##  
ContentOps.Print:= function(self)
    Print("Content( ", self.list, " )");
end;

#############################################################################
TableauOps.Content:= function(self)
    return Content(Call(self, "JCoordinates") - Call(self, "ICoordinates"));
end;

#############################################################################
ContentOps.Tableau:= function(self)
    local   n,  len,  rows,  k,  a,  l,  j,  i;
    
    # keep track of diagonal lengths [-n+1..-1,0,1..n-1]
    n:= Length(self.list);
    len:= 0*[1..2*n-1];
    rows:= [];  # initialize rows
    for k in [1..n] do
        a:= self.list[k];   # a = j - i
        l:= len[a+n];       # l = i - 1 if a > 0 and l = j - 1 else
        if a < 1  then
            j:= l + 1;
            i:= j - a;
            if j = 1 then
                rows[i]:= [];
            fi;
        else 
            i:= l + 1;
            j:= a + i;
        fi;
        rows[i][j]:= k;
        len[a+n]:= len[a+n] + 1;
    od;
    
    return Tableau(rows);
end;


#############################################################################
##
##  list the possible n+1-th entries for a Content of Length n
##
ContentOps.Next:= function(self)
    local   next,  reversed,  a,  j;
    next:= [];
    reversed:= Reversed(self.list);
    for a in [Minimum(self.list) - 1 .. Maximum(self.list) + 1] do
        j:= Position(reversed, a);
        if j = false or IsSubset(reversed{[1..j-1]}, [a+1, a-1]) then
            Add(next, a);
        fi;
    od;
    return next;
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
