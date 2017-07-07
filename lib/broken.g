#############################################################################
##
##  NBC Basis
##
##  want:
##
##  * Enumerator for basis.
##  * Express arbitrary subset in the basis.
##

#############################################################################
##
##  info
##
InfoBroken:= Print;

#############################################################################
##
##  partition set of roots (or rather their positions in roots)
##  according to hyperplanes
##
HyperplanesRoots:= function(roots)
    local   planes,  parts,  normal,  i,  n,  pos;

    planes:= [];
    parts:= [];

    # v \neq 0
    normal:= v-> v/v[PositionProperty(v, x-> x<>0)];

    for i in [1..Length(roots)] do
        n:= normal(roots[i]);
        pos:= Position(planes, n);
        if pos = false then
            Add(planes, n);
            Add(parts, [i]);
        else
            Add(parts[pos], i);
        fi;
    od;

    return rec(planes:= planes, parts:= parts);
end;

#############################################################################
##
##  How to add node m to the graph
##
EnlargedTree:= function(tree, vecs, m)

    local   ancestors,  mNode,  isUnbroken,  walker,  tree1;

    Print("m = ", m, "\n");

    ancestors:= [];

    mNode:= Node(m);

    # find largest index that makes set dependent, if any.
    isUnbroken:= function(set, y, m)
        local   l,  poss,  i;
        l:= Length(set) + 3;
        if m < Length(vecs) and l > Length(vecs[1]) then
            return false;
        fi;
        poss:= Copy(set);
        poss[l-2]:= y;
        poss[l-1]:= m;
        for i in [m+1..Length(vecs)] do
            poss[l]:= i;
            if RankMat(vecs{poss}) < l then
                return false;
            fi;
        od;
        return true;
    end;

    walker:= function(tree, tree1, depth, good)
        local   set,  y,  child,  child1,  i;

        #   determine this node's set
        set:= ancestors{[1..depth-1]};

        if depth > 0 then

           y:= ancestors[depth];
#           Print(set, "\r");

           # does set+m contain a broken circuit?
           good:= good and isUnbroken(set, y, m);
        fi;

        for child in tree.children do
            child1:= Node(child.index);

            if not IsBound(child.fiber) then
                child.fiber:= [];
            fi;

            ancestors[depth+1]:= child1.index;
            walker(child, child1, depth+1, good);

            # now compress child
            y:= Position(child.fiber, child1);
            if y = false then
                Add(child.fiber, child1);
            else
                child1:= child.fiber[y];
            fi;
            Add(tree1.children, child1);
        od;

        # add m as a child to this tree
        if good then
            Add(tree1.children, mNode);
        fi;

    end;

    tree1:= Node(0);
    walker(tree, tree1, 0, true);

    return tree1;
end;

#############################################################################
##
##  NBCBasis( vecs ) ... ultimate version
##
##
NBCBasis:= function(vecs)
    local   t0,  times,  tree,  i,  t1;

    t0:= Runtime();
    times:= [];
    tree:= Node(0);
    for i in [1..Length(vecs)] do
        tree:= EnlargedTree(tree, vecs, i);
        t1:= Runtime();
        Add(times, t1 - t0);
        Print("Size: ", Call(tree, "Size"), " SIZE: ", SIZE(tree), " time: ", t1 - t0, "\n");
        t0:= t1;
    od;
    Print("times: ", times, "\n");
    return tree;
end;

#############################################################################
##
##  how to write a (non-basis) set as combination of basis sets
##  given: a set, a basis, and a big enough list of broken circuits
##  (big enough so that every non-basic set considered contains
##  one of these broken circuits), and a list of extra elements
##  that turn broken circuits into circuits.  don't need W !?
##  input: NBC graph from above, all rooted paths are basis elements.
##  returns: a sparse list of coefficient/basis element pairs
##
NBCCoeffsSet:= function(set, basis, vecs)
    local   zeroVec,  mulVec,  normalVec,  addVec,  positionChild,
            nodeSet,  k,  sub,  big,  j,  sum,  poss,  i;

#    Print(">\c");

    zeroVec:= rec(sets:= [], vals:= []);

    # how to multiply vec by scalar
    mulVec:= function(h, vec)
        if h = 0 then
            return zeroVec;
        else
            return rec(sets:= ShallowCopy(vec.sets), vals:= List(vec.vals, x-> h * x));
        fi;
    end;

    # normalize vec in place (sort sets, ignore zero vals)
    normalVec:= function(vec)
        local   l,  sets,  vals,  i,  set,  val;

        l:= Length(vec.sets);
        SortParallel(vec.sets, vec.vals);

        sets:= [];
        vals:= [];

        i:= 1;
        while i <= l do
            set:= vec.sets[i];
            val:= 0;
            while i <= l and vec.sets[i] = set do
                val:= val + vec.vals[i];
                i:= i+1;
            od;
            if val <> 0 then
                Add(sets, set);
                Add(vals, val);
            fi;
        od;

        vec.sets:= sets;
        vec.vals:= vals;
        return vec;
    end;

    # how to add two vecs.
    addVec:= function(l, r)
        local   sum;
        sum:= rec(sets:= Concatenation(l.sets, r.sets),
                  vals:= Concatenation(l.vals, r.vals));
        return normalVec(sum);
    end;

    # how to find a particular child: binary search
    positionChild:= function(children, k)
        local   lo,  hi,  m;
        lo:= 0; hi:= Length(children) + 1;
        while hi > 1 + lo do
            m:= QuoInt(lo + hi, 2);
            if children[m].index > k then
                hi:= m;
            else
                lo:= m;
            fi;
        od;
        if lo > 0 and children[lo].index = k then
            return lo;
        else
            return false;
        fi;
    end;

    # how to locate set in basis
    nodeSet:= function(basis, set)
        local   node,  k,  pos;

        node:= basis;
        for k in [1..Length(set)] do
            pos:= positionChild(node.children, set[k]);
            if pos = false then
                # set{[1..k]} is broken
                return k;
            fi;
            node:= node.children[pos];
        od;

        # if we get here, set is basic.
        return true;
    end;

    k:= nodeSet(basis, set);

    # easy case, set is a  basis element.
    if k = true then
        Print("1\c");
        return rec(sets:= [set], vals:= [1]);
    fi;

    # now set is not basic and set{[1..k]} contains a broken circuit.
    # find the extra element.
    sub:= set{[1..k]};  sub[k+1]:= Length(vecs);
    while RankMat(vecs{sub}) > k do
        sub[k+1]:= sub[k+1] - 1;
    od;

    # if set also contains the extra element it is dependent hence 0
    # can this happen?
    if sub[k+1] in set then
        Print("0\c");
        return zeroVec;
    fi;

    # otherwise, there is a relation; choose sign so that set would
    # occur with -
    big:= Copy(set);
    j:= PositionSorted(big, sub[k+1]);
    big{[j..Length(big)]+1}:= big{[j..Length(big)]};
    big[j]:= sub[k+1];
    sum:= zeroVec;

#    Print("set: ", set, " sub: ", sub, " big: ", big, "\n");
    poss:= [1..Length(set)]+1;
    for i in [1..k] do
        sum:= addVec(sum, mulVec(-(-1)^(i-j), NBCCoeffsSet(big{poss}, basis, vecs)));
        poss[i]:= i;

    od;
#    Print("<\c");
    return sum;
end;

#############################################################################
##
##  find coeff of (basic) set  in decomposition of img
##
NBCCoeffBasic:= function(img, set, basis, vecs)

    local   positionChild,  nodeSet,  k,  sub,  null,  big,  j,  sum,
            poss,  i;

    # easy cases.
    if img = set then
#        Print("1\c");
        return 1;
    elif ForAny([1..Length(set)], i-> img[i] > set[i]) then
#        Print(".\c");
        return 0;
    fi;

    # how to find a particular child: binary search
    positionChild:= function(children, k)
        local   lo,  hi,  m;
        lo:= 0; hi:= Length(children) + 1;
        while hi > 1 + lo do
            m:= QuoInt(lo + hi, 2);
            if children[m].index > k then
                hi:= m;
            else
                lo:= m;
            fi;
        od;
        if lo > 0 and children[lo].index = k then
            return lo;
        else
            return false;
        fi;
    end;

    # how to locate set in basis
    nodeSet:= function(set)
        local   node,  k,  pos,  children;
        node:= basis;
        for k in [1..Length(set)] do
            pos:= positionChild(node.children, set[k]);
            if pos = false then
                # set{[1..k]} is broken
                return k;
            fi;
            node:= node.children[pos];
        od;

        # if we get here, set is basic.
        return true;
    end;

    k:= nodeSet(img);

    # easy case, img is a  basis element, but not the one we're lookin for
    # as img < set
    if k = true then
#        Print("0\c");
        return 0;
    fi;

    # now img is not basic and img{[1..k]} contains a broken circuit.
    # find the extra element.
    sub:= img{[1..k]};  sub[k+1]:= Length(vecs);
    null:= NullspaceMat(vecs{sub});
    while null = [] do
        sub[k+1]:= sub[k+1] - 1;
        null:= NullspaceMat(vecs{sub});
    od;

    # if img also contains the extra element it is dependent hence 0
    # can this happen?
    if sub[k+1] in img then
#        Print("!\c");
        return 0;
    fi;

    # otherwise, there is a relation; choose sign so that set would
    # occur with -
    null:= null[1];
    big:= Copy(img);
    j:= PositionSorted(big, sub[k+1]);
    big{[j..Length(big)]+1}:= big{[j..Length(big)]};
    big[j]:= sub[k+1];

    sum:= 0;

#    if k > 4 then Error(); fi;

    #    Print("img: ", img, " sub: ", sub, " big: ", big, "\n");
#    Print(">\c");
    poss:= [1..Length(set)]+1;
    for i in [1..k] do
        if null[i] <> 0 then
            sum:= sum - (-1)^(i-j) * NBCCoeffBasic(big{poss}, set, basis, vecs);
        fi;
        poss[i]:= i;
    od;
#    Print("<\c");

    return sum;
end;

#############################################################################
NBCDiagonalSet:= function(set, w, bas, vecs)
    local   img,  sgn;

    img:= OnTuples(set, w);
    sgn:= SignPerm(Sortex(img));
    return sgn * NBCCoeffBasic(img, set, bas, vecs);
end;

#############################################################################
TraceNBC:= function(bas, vecs, w)
    local   ancestors,  count,  walker;

    ancestors:= [];
    count:= 0;

    # DFS
    walker:= function(node, depth)
        local   set,  sum,  child;

        #   determine this node's set and contribution
        set:= ancestors{[1..depth]};
        sum:= NBCDiagonalSet(set, w, bas, vecs);

        # recurse
        for child in node.children do
            ancestors[depth+1]:= child.index;
            sum:= sum + walker(child, depth+1);
        od;

        count:= count + 1;
        if count mod 10000 = 0 then
            Print(count, "\r");
        fi;
        return sum;
    end;

    return walker(bas, 0);
end;

#############################################################################
OSCharacterValueCRG:= function(W, bas, i)
    local   hyp,  bas,  op,  phi,  ct,  cc,  w,  val;

    hyp:= HyperplanesRoots(W.roots);
#    bas:= NBCBasis(hyp.planes);
    op:= Operation(W, hyp.parts, OnSets);
    phi:= OperationHomomorphism(W, op);
    ct:= CharTable(W);
    cc:= ConjugacyClasses(W);
    w:= Representative(cc[i]);
    val:= TraceNBC(bas, hyp.planes, w^phi);
    Print("i = ", i, ": ", val, "\n");
    return val;
end;

OSCharacterCRG:= function(W)
    local   hyp,  bas,  op,  phi,  chi,  ct,  cc,  i,  w;

    hyp:= HyperplanesRoots(W.roots);
    bas:= NBCBasis(hyp.planes);
    op:= Operation(W, hyp.parts, OnSets);
    phi:= OperationHomomorphism(W, op);
    chi:= [Call(bas, "Size")];
    ct:= CharTable(W);
    cc:= ConjugacyClasses(W);
    for i in [2..Length(cc)] do
        w:= Representative(cc[i]);
        Add(chi, TraceNBC(bas, hyp.planes, w^phi));
        Print("i = ", i, ": ", chi[i], "\n");
    od;
    return Character(W, chi);
end;

