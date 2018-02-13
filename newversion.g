# internal for permuting matrices
PermuteMatrix:=function(M,p)
local A,v,i,j;
if not(IsTable(M)) then
  Error("The first argument is a matrix");
fi;
if not(IsPerm(p)) then
  Error("The second argument is a permutation");
fi;
v:=ListPerm(p,Length(M));
A:=List([1..Length(M)],i->List([1..Length(M)],j->0));
for i in [1..Length(M)-1] do
  for j in [i+1..Length(M)] do
    A[i][j]:=Maximum(M[v[i]][v[j]],M[v[j]][v[i]]);
  od;
od;
return A;
end;

#internal for permuting vectors
PermuteList:=function(M,p)
local A,v,i,j;
if not(IsList(M)) then
  Error("The first argument is a list");
fi;
if not(IsPerm(p)) then
  Error("The second argument is a permutation");
fi;
v:=ListPerm(p,Length(M));
A:=List([1..Length(M)],i->0);
for i in [1..Length(M)] do
    A[i]:=M[v[i]];
od;
return A;
end;


#chech if a matrix the matrix of an untwisted tree
IsUntwisted:=function(M)
  local n,h,i,k,check,j,l;
  if not(IsTable(M)) then
    Error("The argument is a matrix");
  fi;
  if not(ForAll(Union(M), IsInt)) then
    Error("The entries of the matrix must be integers");
  fi;
  check:=function(M)
    local h,i,j,k,l,s;
    h:=true;
    for i in [1..Length(M)-2] do
      for j in [i+1..Length(M)-1]  do
        for k in [j+1..Length(M)] do
          s:=[M[i][j],M[j][k],M[i][k]];
         h:=h and Length(Set(s))<=2 and Length(Filtered([1..Length(s)],i->s[i]=Set(s)[1]))>=2;
      od;
    od;
  od;
    return h;
  end;
  if not   IsUpperTriangularMat(M) then
    Error("The matrix does not correspond to a tree");
  fi;

  if not check(M) then
    Error("The matrix does not correspond to a tree");
  fi;
  n:=Length(M);
  h:=true;
  for i in [1..n-2] do
    for j in [i+1..n] do
      k:=infinity; for l in [i..j-1] do
      k:=Minimum(k,M[l][l+1]);
    od;
    h:=h and M[i][j]=k;
  od;
od;
  return h;
end;

# internal for permuting tree
PermuteTree:=function(tree,p)
  local edges, nodes, depth, level, k, id, i, j, pn, nd, leaves, sons, max, n, Mh,pnodes,pedges,t,v;

  nodes:=tree[1];
  edges:=tree[2];
  v:=ListPerm(p,Length(nodes[1][1]));
  pnodes:=[];
  for i in nodes do
Add(pnodes,Concatenation([PermuteList(i[1],p)],[i[2]]));
  od;
  pedges:=[];
  for j in edges do
    t:=StructuralCopy(j);
    t[1]:=Concatenation([PermuteList(j[1][1],p)],[j[1][2]]);
    t[2]:=Concatenation([PermuteList(j[2][1],p)],[j[2][2]]);
    Add(pedges,t);
  od;
  return [pnodes,pedges];
end;
#################################################
##
## ArfSemigroupFromMultiplicitySequence
## The input is a multiplicity sequence.
## The output is the Arf numerical semigroup with
## that multiplicity sequence
#################################################
ArfSemigroupFromMultiplicitySequence:=function(m)
  local ismultseq,inarf,i,ms,j,b,char,r;
  # tests whether x is in the Arf semigroup with multiplicity
  # sequence j
  inarf:=function(x,j)
      local l;
      if x>Sum(j) then
        return true;
      fi;
      if x=0 then
        return true;
      fi;
      if x<j[1] then
        return false;
      fi;
      l:=List([1..Length(j)], i-> Sum(j{[1..i]}));
      return x in l;
  end;

  ismultseq := function(m)
      local n;
      n:=Length(m);
      return ForAll([1..n-1], i-> inarf(m[i], m{[i+1..n]}));
  end;
  if not ismultseq(m) then
    Error("The argument must be a  multiplicity sequence");
  fi;
  ms:=Concatenation(m,[1,1]);
  r:=List(ms,_->0);
  for i in [1..Length(ms)] do
    b:=First([i+1..Length(ms)], j->ms[i]=Sum(ms{[i+1..j]}));
    if b=fail then
      b:=Length(ms);
    fi;
    for j in [i+1..b] do
      r[j]:=r[j]+1;
    od;
  od;
  i:=Filtered([1..Length(ms)-1], j->r[j]<r[j+1]);
  char:=List(i, j->Sum(ms{[1..j]}));
return  ArfNumericalSemigroupClosure(NumericalSemigroupByMinimalGenerators(char));
end;

#################################################
##
## arfCharactersOfArfNumericalSemigroup
## The input is an Arf numerical semigroup s.
## The output is the set of characters of
## s
#################################################
arfCharactersOfArfNumericalSemigroup:=function(s)
  local char,  ms,  inarf,i,j,  m, r, b;

  # tests whether x is in the Arf semigroup with multiplicity
  # sequence j
  inarf:=function(x,j)
      local l;
      if x>Sum(j) then
        return true;
      fi;
      if x=0 then
        return true;
      fi;
      if x<j[1] then
        return false;
      fi;
      l:=List([1..Length(j)], i-> Sum(j{[1..i]}));
      return x in l;
  end;


  if not(IsArfNumericalSemigroup(s)) then
    Error("The argument must be an Arf numerical semigroup");
  fi;

  ms:=Concatenation(MultiplicitySequenceOfNumericalSemigroup(s),[1]);
  r:=List(ms,_->0);
  for i in [1..Length(ms)] do
    b:=First([i+1..Length(ms)], j->ms[i]=Sum(ms{[i+1..j]}));
    if b=fail then
      b:=Length(ms);
    fi;
    for j in [i+1..b] do
      r[j]:=r[j]+1;
    od;
  od;
  i:=Filtered([1..Length(ms)-1], j->r[j]<r[j+1]);
  return List(i, j->Sum(ms{[1..j]}));
end;


#################################################
##
#F CompatibilityLevelOfMultiplicitySequences(M)
## The input is a list of two multiplicity sequences.
## The output is the maximum level where the tree
## can ramify. It can be infinite if both sequences are
## equal.
## Implementation done with G. Zito
#################################################
CompatibilityLevelOfMultiplicitySequences:=function(M)
  local ismultseq, k, s, max, D, i,j, inarf;


    # tests whether x is in the Arf semigroup with multiplicity
    # sequence j
    inarf:=function(x,j)
        local l;
        if x>Sum(j) then
          return true;
        fi;
        if x=0 then
          return true;
        fi;
        if x<j[1] then
          return false;
        fi;
        l:=List([1..Length(j)], i-> Sum(j{[1..i]}));
        return x in l;
    end;

  # tests if m is a multiplicity sequence
  ismultseq := function(m)
      local n;
      n:=Length(m);
      return ForAll([1..n-1], i-> inarf(m[i], m{[i+1..n]}));
  end;

  if not(IsTable(M)) then
    Error("The first argument must be a list of multiplicity sequences");
  fi;

  if Length(M)<>2 then
    Error("We are so far only considering Arf good semigroups in N^2");
  fi;

  if not(ForAll(Union(M), IsPosInt)) then
    Error("The first argument must be a list of multiplicity sequences");
  fi;

  if not(ForAll(M, ismultseq)) then
    Error("The first argument must be a list of multiplicity sequences");
  fi;

  s:=[];
  max:= Maximum(List(M, Length));

  for i in [1..2] do
    s[i]:=[];
    for j in [1..Length(M[i])] do
      s[i][j]:=First([j+1..Length(M[i])], k-> M[i][j]=Sum(M[i]{[j+1..k]}));
      if s[i][j]=fail then
        s[i][j]:=M[i][j]-Sum(M[i]{[j+1..Length(M[i])]})+Length(M[i])-j;
      else
        s[i][j]:=s[i][j]-j;
      fi;
    od;
  od;
  for i in [1..2] do
      s[i]:=Concatenation(s[i],List([Length(s[i])+1..max],_->1));
  od;

  D:=Filtered([1..max], j->s[1][j]<>s[2][j]);
  k:=[];
  if D=[] then
    k:=infinity;
  else
    k:=Minimum(Set(D, j->j+Minimum(s[1][j],s[2][j])));
  fi;
  return k;
end;
#####################################################
#F TreeFromMultiplicitySequenceListAndRamificationMatrix
## The input are a list of multiplicity sequences v and a ramification matrix M
## The ouput is the multiplicity tree corresponding to them described by a set of nodes and of edges
#####################################################
TreeFromMultiplicitySequenceListAndRamificationMatrix:=function(v,M)
local ismultseq,inarf,check,n,ags,ags1,UntwistingPermutation,vectorToTree;
# in the untwisted case recover a tree from the ramification vector
vectorToTree:=function(v,M)
  local edges, nodes, depth, level, k, id, i, j, pn, nd, leaves, sons, max, n, Mh,len;
  # length of a multiplicity sequence
  len := function(l)
    local fone;
    fone:=First([1..Length(l)], x->l[x]=1);
    if fone=fail then
      return Length(l);
    fi;
    if fone=1 then
      return 1;
    fi;
    return fone-1;
  end;
if v=[] then
  nodes:=[]; edges:=[];

  for i in [1..len(M[1])+1] do
    if i<len(M[1])+1 then
    Add(nodes,[[M[1][i]],[i]]);
  else Add(nodes,[[1],[i]]);
  fi;
  od;
  for i in [1..len(M[1])] do
    Add(edges,[nodes[i],nodes[i+1]]);
  od;

else
  max:= Maximum(List(M, Length));
  n:=Length(M);
  id:=IdentityMat(n);
  depth:=Maximum(Maximum(v)+1,max+1);

  Mh:=ShallowCopy(M);
  for i in [1..n] do
      Mh[i]:=Concatenation(Mh[i],List([Length(Mh[i])+1..depth],_->1));
  od;

  edges:=[];
  nodes:=[];
  leaves:=[];
  for level in [1..depth] do
    pn:=List([1..n], j->Mh[j][level]*id[j]);
    #Print(pn,"\n");
    nd:=pn[1];
    for j in [2..n] do
      if level<=v[j-1] then
        nd:=nd+pn[j];
      else
        if Sum(nd)=1 and not(nd in leaves) then
          Add(nodes,[nd,level]);
          Add(leaves,nd);
        fi;
        if Sum(nd)>1 then
          Add(nodes,[nd,level]);
        fi;
        nd:=pn[j];
        #Print("Nodes so far for ",v," ", nodes, "\n");
      fi;
    od;
    if Sum(nd)=1 and not(nd in leaves) then
      Add(nodes,[nd,level]);
      Add(leaves,nd);
    fi;
    if Sum(nd)>1 then
      Add(nodes,[nd,level]);
    fi;
    #Print("Nodes so far for ",v," ", nodes, "\n");
  od;

  for level in [1..depth-1] do
    pn:=Filtered(nodes, x->x[2]=level);
    for nd in pn do
      sons:=Filtered(nodes, x->(x[2]=level+1) and x[1]*nd[1]<>0);
      #Print("Nodes connected to ",nd," are ",sons,"\n");
      sons:=List(sons, x->[nd,x]);
      #Print("Adding edges ",sons);
      edges:=Union(edges, sons);
      #Print("New edges ", edges);
    od;
  od;
fi;
  return [nodes,edges];
end;
# find the permutation that transforms the matrix in an untwisted one
UntwistingPermutation:=function(M)
  local untwist,n,t,h,v;

  untwist:=function(N)
    local n,i,i1,v,j,p;
    n:=Length(N);  v:=List([1..n],i->i);
     i:=First([1..n-1],i1->Maximum(N[i1])<>N[i1][i1+1]);
     if i=fail then
      p:=PermList(v); else
    j:=n-First([0..n-1],i1->N[i][n-i1]=Maximum(N[i]));
      v[i+1]:=j; v[j]:=i+1;
p:=PermList(v);
    fi;
    return p;
  end;
  n:=Length(M);
  t:=StructuralCopy(M);
  h:=();
  while untwist(t)<>() do
    h:=untwist(t)*h; t:=StructuralCopy(PermuteMatrix(t,untwist(t)));
  od;
  return h;
end;
# tests whether x is in the Arf semigroup with multiplicity
# sequence j
inarf:=function(x,j)
    local l;
    if x>Sum(j) then
      return true;
    fi;
    if x=0 then
      return true;
    fi;
    if x<j[1] then
      return false;
    fi;
    l:=List([1..Length(j)], i-> Sum(j{[1..i]}));
    return x in l;
end;

# tests if m is a multiplicity sequence
ismultseq := function(m)
    local n;
    n:=Length(m);
    return ForAll([1..n-1], i-> inarf(m[i], m{[i+1..n]}));
end;
if not(IsTable(M)) then
  Error("The second argument is a matrix");
fi;
if not(ForAll(Union(M), IsInt)) then
  Error("The entries of the matrix must be integers");
fi;
# check if the matrix is compatible with a tree
check:=function(M)
  local h,i,j,k,l,s;
  h:=true;
  for i in [1..Length(M)-2] do
    for j in [i+1..Length(M)-1]  do
      for k in [j+1..Length(M)] do
        s:=[M[i][j],M[j][k],M[i][k]];
       h:=h and Length(Set(s))<=2 and Length(Filtered([1..Length(s)],i->s[i]=Set(s)[1]))>=2;
    od;
  od;
od;
  return h;
end;
if not   IsUpperTriangularMat(M) then
  Error("The matrix does not correspond to a tree");
fi;

if not check(M) then
  Error("The matrix does not correspond to a tree");
fi;
if not(IsTable(v)) then
  Error("The first argument must be a list of multiplicity sequences");
fi;


if not(ForAll(Union(v), IsPosInt)) then
  Error("The argument must be a list of multiplicity sequences");
fi;

if not(ForAll(v, ismultseq)) then
  Error("The argument must be a list of multiplicity sequences");
fi;
if Length(M)<>Length(v) then
  Error("There is a problem with dimensions");
fi;
n:=Length(M);

if not(ForAll(Cartesian([1..n],[1..n]), i->M[i[1]][i[2]]<=CompatibilityLevelOfMultiplicitySequences([v[i[1]],v[i[2]]]))) then
  Error("The arguments do not correspond to an Arf good semigroup (not compatible)");
fi;
return PermuteTree(vectorToTree(List([1..Length(M)-1],j->PermuteMatrix(M,UntwistingPermutation(M))[j][j+1]),PermuteList(v,UntwistingPermutation(M))),UntwistingPermutation(M)^(-1));
end;
############################################################
#F MultiplicityTreeToMultiplicitySequenceAndRamificationMatrix(t)
## t is the multiplicity tree of an Arf semigroup. The output is
## the list of multiplicity sequences with the matrix telling
## where these ramify in the tree
############################################################
MultiplicityTreeToMultiplicitySequenceAndRamificationMatrix:=function(t)
  local M, k, depth, nodes, edges, n, id, i, pathtoroot, cand, maxdepth, inarf, ismultseq, paths;


  # tests whether x is in the Arf semigroup with multiplicity
  # sequence j
  inarf:=function(x,j)
      local l;
      if x>Sum(j) then
        return true;
      fi;
      if x=0 then
        return true;
      fi;
      if x<j[1] then
        return false;
      fi;
      l:=List([1..Length(j)], i-> Sum(j{[1..i]}));
      return x in l;
  end;

  # tests if m is a multiplicity sequence
  ismultseq := function(m)
      local n;
      n:=Length(m);
      return ForAll([1..n-1], i-> inarf(m[i], m{[i+1..n]}));
  end;

  # determines the path from v to the root of the tree t
  pathtoroot:=function(v)
    local path, nv, e;
    path:=[v];
    nv:=v;
    while true do
      e:=First(edges, e->e[2]=nv);
      if e=fail then
        return path;
      fi;
      nv:=e[1];
      Add(path,nv);
    od;
    return path;
  end;


  if not(IsList(t)) and Length(t)<>2 then
    Error("The argument is a tree, given by a list: the first element is the list of nodes and second the list of edges");
  fi;

  nodes:=t[1];
  edges:=t[2];
  n:=Length(nodes[1][1]);
  id:=IdentityMat(n);
  depth:=[];#Maximum(List(nodes, x->x[2]));
  for i in [1..n] do
    cand:=Filtered(nodes, n-> n[1]=id[i]);
    if cand=[] then
      Error("The tree is not a multiplicity tree, node ", id[i], "missing");
    fi;
    depth[i]:=Maximum(List(cand, x->x[2]));
  od;
  maxdepth:=Maximum(depth);

  M:=[];
  paths:=[];
  for i in [1..n] do
    paths[i]:=Reversed(pathtoroot([id[i],depth[i]]));
    M[i]:=List(paths[i], x->x[1][i]);
  od;

  if not(ForAll(M, ismultseq)) then
    Error("The argument is not a multiplicity tree");
  fi;

  k:=List([1..n],i->List([1..n],j->0));
  for i in Filtered(Cartesian([1..n],[1..n]),j->j[1]<j[2]) do
    cand:=First(paths[i[1]], x->x[1][i[2]]=0);
    if cand=fail then
      Error("The argument is not a multiplicity tree");
    fi;
    k[i[1]][i[2]]:=cand[2]-1;
  od;
  if not(ForAll(Filtered(Cartesian([1..n],[1..n]),j->j[1]<j[2]), i->k[i[1]][i[2]]<=CompatibilityLevelOfMultiplicitySequences([M[i[1]],M[i[2]]]))) then
    Error("The tree is not compatible with any Arf good semigroup");
  fi;
  return [M,k];
end;

#####################################################
#F AllArfTreesWithGivenCollectionOfMultiplicitySequences
## The input are a list of multiplicity sequences
## The ouput is the set of all the multiplicity trees with this collection as branches
#####################################################
AllArfTreesWithGivenCollectionOfMultiplicitySequences:=function(M)
  local ismultseq, T, s, k, inarf, i, j, n, max, D, space, vectorToTree,nodes,edges, Mh, A,sons,v,Small,check,aux,ags,ags1,trees,len,UntwistingPermutation;

  # length of a multiplicity sequence
  len := function(l)
    local fone;
    fone:=First([1..Length(l)], x->l[x]=1);
    if fone=fail then
      return Length(l);
    fi;
    if fone=1 then
      return 1;
    fi;
    return fone-1;
  end;
  # find the permutation that transforms a matrix in an untwisted  one
  UntwistingPermutation:=function(M)
    local untwist,n,t,h,v,check;
    untwist:=function(N)
      local n,i,i1,v,j,p;
      n:=Length(N);  v:=List([1..n],i->i);
       i:=First([1..n-1],i1->Maximum(N[i1])<>N[i1][i1+1]);
       if i=fail then
        p:=PermList(v); else
      j:=n-First([0..n-1],i1->N[i][n-i1]=Maximum(N[i]));
        v[i+1]:=j; v[j]:=i+1;
  p:=PermList(v);
      fi;
      return p;
    end;
    n:=Length(M);
    t:=StructuralCopy(M);
    h:=();
    while untwist(t)<>() do
      h:=untwist(t)*h; t:=StructuralCopy(PermuteMatrix(t,untwist(t)));
    od;
    return h;
  end;
  # tests whether x is in the Arf semigroup with multiplicity
  # sequence j
  inarf:=function(x,j)
      local l;
      if x>Sum(j) then
        return true;
      fi;
      if x=0 then
        return true;
      fi;
      if x<j[1] then
        return false;
      fi;
      l:=List([1..Length(j)], i-> Sum(j{[1..i]}));
      return x in l;
  end;
Small:=function(vec)
local ags,i;
ags:=[];
if Length(vec)=1 then
  for i in [1..vec[1]] do
    Add(ags,[i]);
  od;
else for i in Small(vec{[1..Length(vec)-1]}) do
          for j in [1..vec[Length(vec)]] do
            Add(ags,Concatenation(i,[j]));
          od;
        od;
      fi;
  return ags;
end;
  # tests if m is a multiplicity sequence
  ismultseq := function(m)
      local n;
      n:=Length(m);
      return ForAll([1..n-1], i-> inarf(m[i], m{[i+1..n]}));
  end;
  aux:=function(N,w,u,v)
    local ags,A,i,k1,n,m,k2,a;
    if u=v then
      ags:=aux(N,w,u-1,Length(w)+1); else
      if u=1 then
        ags:=[];
        A:=List([1..Length(w)+1],i->List([1..Length(w)+1],j->0));
        for i in [1..Length(w)] do
          A[1][i+1]:=w[i];
        od;
          Add(ags,A);
        else
          ags:=[];
          for k1 in aux(N,w,u,v-1) do
            n:=1; m:=k1[1][u];
                      while k1[n][u]=k1[n][v] and n<u do
                       n:=n+1; m:=Maximum(m,k1[n][u]);
                                                    od;
              if n=u then
                for k2 in [m..N[u][v]] do
                a:=StructuralCopy(k1);
                a[u][v]:=k2;
                Add(ags,a);
              od;      else
              a:=StructuralCopy(k1); a[u][v]:=Minimum(k1[n][v],k1[n][u]);
              Add(ags,a);
            fi;
          od;
        fi;
      fi;

    return ags;
  end;


  if not(IsTable(M)) then
    Error("The argument must be a list of multiplicity sequences");
  fi;

  if Length(M)=1 then
      nodes:=[]; edges:=[];

      for i in [1..len(M[1])+1] do
        if i<len(M[1])+1 then
        Add(nodes,[[M[1][i]],[i]]);
      else Add(nodes,[[1],[i]]);
      fi;
      od;
      for i in [1..len(M[1])] do
        Add(edges,[nodes[i],nodes[i+1]]);
      od;


    return [[nodes,edges]];
  fi;

  if not(ForAll(Union(M), IsPosInt)) then
    Error("The argument must be a list of multiplicity sequences");
  fi;

  if not(ForAll(M, ismultseq)) then
    Error("The argument must be a list of multiplicity sequences");
  fi;
  n:=Length(M);
  A:=List([1..n],i->List([1..n],j->0));
  for i in [1..n-1] do
    for j in [i+1..n] do
      A[i][j]:=CompatibilityLevelOfMultiplicitySequences([M[i],M[j]]);
    od;
  od;


  check:=Filtered(Cartesian([1..n],[1..n]),i->A[i[1]][i[2]]=infinity);
  if not check=[] then
    for i in check do
      Info(InfoNumSgps, 1, "There will be infinitely many trees corresponding to the branches ",i[1]," and ",i[2],", we will only ouptput up to level", Length(M[i[1]]));
A[i[1]][i[2]]:=Length(M[i[1]]);
od;
  fi;
  ags:=[];
  v:=List([1..n-1],j->A[1][j+1]);
  for i in Small(v) do
    ags:=UnionSet(ags,aux(A,i,n-1,n));
  od;
  ags1:=[];
  for i in ags do
    Add(ags1,Concatenation([M],[i]));
  od;
#  trees:=[];
#  for i in ags1 do
    #Add(trees,PermutevectorToTree(List([1..Length(i[2])-1],j->PermuteMatrix(i[2],UntwistingPermutation(i[2]))[j][j+1]),PermuteList(i[1],UntwistingPermutation(i[2])),UntwistingPermutation(i[2])^(-1)));
#  od;
  return List(ags1,i->TreeFromMultiplicitySequenceListAndRamificationMatrix(i[1],i[2]));
end;
#####################################################
#F SmallElementsFromMultiplicitySequenceListAndRamificationMatrix
## The input are a collection of multiplicity sequences v and a ramification matrix M
## The ouput is the set of small elements of the corresponding Arf semigroup
#####################################################
SmallElementsFromMultiplicitySequenceListAndRamificationMatrix:=function(v,M)
local ismultseq,inarf,check,n,ags,ags1,i,VtoSE,UntwistingPermutation;
# find the permutation that transforms the matrix in an untwisted one
UntwistingPermutation:=function(M)
  local untwist,n,t,h,v;

  untwist:=function(N)
    local n,i,i1,v,j,p;
    n:=Length(N);  v:=List([1..n],i->i);
     i:=First([1..n-1],i1->Maximum(N[i1])<>N[i1][i1+1]);
     if i=fail then
      p:=PermList(v); else
    j:=n-First([0..n-1],i1->N[i][n-i1]=Maximum(N[i]));
      v[i+1]:=j; v[j]:=i+1;
p:=PermList(v);
    fi;
    return p;
  end;
  n:=Length(M);
  t:=StructuralCopy(M);
  h:=();
  while untwist(t)<>() do
    h:=untwist(t)*h; t:=StructuralCopy(PermuteMatrix(t,untwist(t)));
  od;
  return h;
end;
# tests whether x is in the Arf semigroup with multiplicity
# sequence j
inarf:=function(x,j)
    local l;
    if x>Sum(j) then
      return true;
    fi;
    if x=0 then
      return true;
    fi;
    if x<j[1] then
      return false;
    fi;
    l:=List([1..Length(j)], i-> Sum(j{[1..i]}));
    return x in l;
end;

# tests if m is a multiplicity sequence
ismultseq := function(m)
    local n;
    n:=Length(m);
    return ForAll([1..n-1], i-> inarf(m[i], m{[i+1..n]}));
end;
if not(IsTable(M)) then
  Error("The second argument is a matrix");
fi;
if not(ForAll(Union(M), IsInt)) then
  Error("The entries of the matrix must be integers");
fi;
check:=function(M)
  local h,i,j,k,l,s;
  h:=true;
  for i in [1..Length(M)-2] do
    for j in [i+1..Length(M)-1]  do
      for k in [j+1..Length(M)] do
        s:=[M[i][j],M[j][k],M[i][k]];
       h:=h and Length(Set(s))<=2 and Length(Filtered([1..Length(s)],i->s[i]=Set(s)[1]))>=2;
    od;
  od;
od;
  return h;
end;
# solve the problem for untwisted tree described by a collection and a vector
VtoSE:=function(M,k)
  local n,i,SEvec,vec,vectorToTree,ismultseq,inarf,Semigroupelem,len;
  # translates vectors of ramifications to tree

  # length of a multiplicity sequence
  len := function(l)
    local fone;
    fone:=First([1..Length(l)], x->l[x]=1);
    if fone=fail then
      return Length(l);
    fi;
    if fone=1 then
      return 1;
    fi;
    return fone-1;
  end;

  # translates vectors of ramifications to tree
  vectorToTree:=function(v,M)
    local edges, nodes, depth, level, k, id, i, j, pn, nd, leaves, sons, max, n, Mh,len;
    # length of a multiplicity sequence
    len := function(l)
      local fone;
      fone:=First([1..Length(l)], x->l[x]=1);
      if fone=fail then
        return Length(l);
      fi;
      if fone=1 then
        return 1;
      fi;
      return fone-1;
    end;
  if v=[] then
    nodes:=[]; edges:=[];
    for i in [1..len(M[1])+1] do
      if i<len(M[1])+1 then
      Add(nodes,[[M[1][i]],[i]]);
    else Add(nodes,[[1],[i]]);
    fi;
    od;
    for i in [1..len(M[1])] do
      Add(edges,[nodes[i],nodes[i+1]]);
    od;

  else
    max:= Maximum(List(M, Length));
    n:=Length(M);
    id:=IdentityMat(n);
    depth:=Maximum(Maximum(v)+1,max+1);

    Mh:=ShallowCopy(M);
    for i in [1..n] do
        Mh[i]:=Concatenation(Mh[i],List([Length(Mh[i])+1..depth],_->1));
    od;

    edges:=[];
    nodes:=[];
    leaves:=[];
    for level in [1..depth] do
      pn:=List([1..n], j->Mh[j][level]*id[j]);
      #Print(pn,"\n");
      nd:=pn[1];
      for j in [2..n] do
        if level<=v[j-1] then
          nd:=nd+pn[j];
        else
          if Sum(nd)=1 and not(nd in leaves) then
            Add(nodes,[nd,level]);
            Add(leaves,nd);
          fi;
          if Sum(nd)>1 then
            Add(nodes,[nd,level]);
          fi;
          nd:=pn[j];
          #Print("Nodes so far for ",v," ", nodes, "\n");
        fi;
      od;
      if Sum(nd)=1 and not(nd in leaves) then
        Add(nodes,[nd,level]);
        Add(leaves,nd);
      fi;
      if Sum(nd)>1 then
        Add(nodes,[nd,level]);
      fi;
      #Print("Nodes so far for ",v," ", nodes, "\n");
    od;

    for level in [1..depth-1] do
      pn:=Filtered(nodes, x->x[2]=level);
      for nd in pn do
        sons:=Filtered(nodes, x->(x[2]=level+1) and x[1]*nd[1]<>0);
        #Print("Nodes connected to ",nd," are ",sons,"\n");
        sons:=List(sons, x->[nd,x]);
        #Print("Adding edges ",sons);
        edges:=Union(edges, sons);
        #Print("New edges ", edges);
      od;
    od;
  fi;
    return [nodes,edges];
  end;

n:=Length(M);
Semigroupelem:=function(v)
  local ags,i,j;
  ags:=[];
  for i in [1..n] do
    for j in [1..v[i]] do
      if not Filtered(vectorToTree(k,M)[1],l->l[2]=j and l[1][i]<>0) in ags then
        Add(ags,Filtered(vectorToTree(k,M)[1],l->l[2]=j and l[1][i]<>0));
      fi;
    od;
  od;
  return Sum(List([1..Length(ags)],l->ags[l][1][1]));
end;
if n=1 then
  return List([1..Length(M[1])],l->[Sum(List([1..l],k->M[1][k]))]);
fi;
vec:=List([1..n],l->0);
vec[1]:=Maximum(len(M[1]),k[1]);
for i in [2..n-1] do
  vec[i]:=Maximum(len(M[i]),k[i],k[i-1]);
od;
  vec[n]:=Maximum(len(M[n]),k[n-1]);

SEvec:=function(cond,ram)
  local ags,i,j;
  ags:=[];
  if Length(cond)=1 then
    for i in [1..cond[Length(cond)]] do
      Add(ags,[i]);
    od;
    return ags;
  fi;
  for i in SEvec(cond{[1..Length(cond)-1]},ram{[1..Length(ram)-1]}) do
    if i[Length(cond)-1]<ram[Length(ram)] then
      Add(ags,Concatenation(i,[ i[Length(cond)-1]])); else
      for j in [ram[Length(ram)]..cond[Length(cond)]] do
        Add(ags,Concatenation(i,[j]));
      od;
      fi;
    od;
return ags;
end;
return List([1..Length(SEvec(vec,k))],l->Semigroupelem(SEvec(vec,k)[l]));
end;
if not   IsUpperTriangularMat(M) then
  Error("The matrix does not correspond to a tree");
fi;

if not check(M) then
  Error("The matrix does not correspond to a tree");
fi;
if not(IsTable(v)) then
  Error("The first argument must be a list of multiplicity sequences");
fi;


if not(ForAll(Union(v), IsPosInt)) then
  Error("The argument must be a list of multiplicity sequences");
fi;

if not(ForAll(v, ismultseq)) then
  Error("The argument must be a list of multiplicity sequences");
fi;
if Length(M)<>Length(v) then
  Error("There is a problem with dimensions");
fi;
n:=Length(M);

if not(ForAll(Cartesian([1..n],[1..n]), i->M[i[1]][i[2]]<=CompatibilityLevelOfMultiplicitySequences([v[i[1]],v[i[2]]]))) then
  Error("The arguments do not correspond to an Arf good semigroup (not compatible)");
fi;
ags:=VtoSE(PermuteList(v,UntwistingPermutation(M)),List([1..Length(M)-1],j->PermuteMatrix(M,UntwistingPermutation(M))[j][j+1]));
ags1:=[];
for i in ags do
  Add(ags1,PermuteList(i,UntwistingPermutation(M)^(-1)));
od;
return ags1;
end;
#####################################################
#F ArfClosureOfSetOfVectors(vs)
## vs is a set of vectors in the positive orthant.
## The ouput is a tree corresponding to the
## least (local) Arf good semigroup containing vs
#####################################################
ArfClosureOfSetOfVectors:=function(vs)
  local M, k, n, trvs, pos, U, MIN,i,j;

  pos:=function(h,i)
    local p;
    p:=First([1..Length(M[i])], j->Sum(M[i]{[1..j]})=h);
    if p<>fail then
      return p;
    fi;
    return Length(M[i])+h-Sum(M[i]);
  end;
  if not(IsRectangularTable(vs)) then
    Error("The input must be a list of vectors (lists)");
  fi;
  if not(ForAll(Union(vs), IsPosInt)) then
    Error("The vectors must have positive integer coordinates");
  fi;
  trvs:=TransposedMat(vs);
  if not(ForAll(trvs, v-> Gcd(v)=1)) then
    Error("The gcd of the coordinates must be 1 for all coordinates (infinite decreasing chain)");
  fi;

  n:=Length(vs[1]);
  if not(ForAll(Filtered(Cartesian([1..n],[1..n]),i->i[1]<i[2]), i->ForAny(vs, g-> g[i[1]]<>g[i[2]]))) then
    Error("There is not such an Arf good semigroup (infinite decreasing chain)");
  fi;

  M:=[];
  k:=[];

  M:=List([1..n], i->MultiplicitySequenceOfNumericalSemigroup(ArfNumericalSemigroupClosure(NumericalSemigroup(trvs[i]))));
  U:=Filtered(Filtered(Cartesian([1..n],[1..n]),i->i[1]<i[2]), j->ForAll(vs, g->pos(g[j[1]],j[1])=pos(g[j[2]],j[2])));
  k:=List([1..n],i->List([1..n],j->0));
  for i in [1..n-1] do
    for j in [i+1..n] do
    if not([i,j] in U) then
      k[i][j]:=Minimum(CompatibilityLevelOfMultiplicitySequences([M[i],M[j]]),
          Minimum(List(Filtered(vs, g->pos(g[i],i)<>pos(g[j],j)), g->Minimum(pos(g[i],i),pos(g[j],j)))));
    else
      k[i][j]:=CompatibilityLevelOfMultiplicitySequences([M[i],M[j]]);
    fi;
  od;
od;
  return [TreeFromMultiplicitySequenceListAndRamificationMatrix(M,k)];

end;
#####################################################
#F ArfClosureOfGoodsemigroup
## Se is the set of Small elements of a good semigroup
## The ouput is a tree corresponding to the
## least (local) Arf good semigroup containing the considered good semigroup
#####################################################
ArfClosureOfGoodsemigroup:=function(Se)
  local M, k, n, trvs,  U, MIN,i,vs,j,e;

  if not(IsRectangularTable(Se)) then
    Error("The input must be a list of vectors (lists)");
  fi;
  if not(ForAll(Union(Se), IsPosInt)) then
    Error("The vectors must have positive integer coordinates");
  fi;
  n:=Length(Se[1]);
 if not List([1..n],j->Maximum(List([1..Length(Se)],i->Se[i][j]))) in Se then
   Error("The input cannot be the set of small elements of a good semigroup (the conductor is missing)");
 fi;
 vs:=ShallowCopy(Se);
e:=List([1..n],i->List([1..n],j->0));
for i in [1..n] do
  e[i][i]:=1;
  Add(vs,e[i]+ List([1..n],j->Maximum(List([1..Length(Se)],i->Se[i][j]))));
od;
  return ArfClosureOfSetOfVectors(vs);
end;
#####################################################
#F ArfCharactersOfMultiplicitySequenceListAndRamificationMatrix
## The input are a collection of multiplicity sequences and a ramification matrix
## The ouput is a set of characters for the corresponding Arf semigroup S that is
## a set of vectors G such that Arf(G)=S
#####################################################
ArfCharactersOfMultiplicitySequenceListAndRamificationMatrix:=function(v,M)
  local arfchrpr,r,pchar,LB,H, ismultseq, inarf, minset3,i,j, l,ms, b,n, V, max,Coll, G,check,ags,ags1,minset1,p,k,UntwistingPermutation;
  # find the permutation that untwists a matrix
  UntwistingPermutation:=function(M)
    local untwist,n,t,h,v,check;

    untwist:=function(N)
      local n,i,i1,v,j,p;
      n:=Length(N);  v:=List([1..n],i->i);
       i:=First([1..n-1],i1->Maximum(N[i1])<>N[i1][i1+1]);
       if i=fail then
        p:=PermList(v); else
      j:=n-First([0..n-1],i1->N[i][n-i1]=Maximum(N[i]));
        v[i+1]:=j; v[j]:=i+1;
  p:=PermList(v);
      fi;
      return p;
    end;
    n:=Length(M);
    t:=StructuralCopy(M);
    h:=();
    while untwist(t)<>() do
      h:=untwist(t)*h; t:=StructuralCopy(PermuteMatrix(t,untwist(t)));
    od;
    return h;
  end;
  # tests whether x is in the Arf semigroup with multiplicity
  # sequence j
  inarf:=function(x,j)
      local l;
      if x>Sum(j) then
        return true;
      fi;
      if x=0 then
        return true;
      fi;
      if x<j[1] then
        return false;
      fi;
      l:=List([1..Length(j)], i-> Sum(j{[1..i]}));
      return x in l;
  end;

  # tests if m is a multiplicity sequence
  ismultseq := function(m)
      local n;
      n:=Length(m);
      return ForAll([1..n-1], i-> inarf(m[i], m{[i+1..n]}));
  end;

  check:=function(M)
    local h,i,j,k,l,s;
    h:=true;
    for i in [1..Length(M)-2] do
      for j in [i+1..Length(M)-1]  do
        for k in [j+1..Length(M)] do
          s:=[M[i][j],M[j][k],M[i][k]];
         h:=h and Length(Set(s))<=2 and Length(Filtered([1..Length(s)],i->s[i]=Set(s)[1]))>=2;
      od;
    od;
  od;
    return h;
  end;
  # function useful to find a solution on the untwisted case
  minset1:=function(s)
    local ags,M,i,j,k,minset;
    minset:=function(s)
      local ags,m,split,a,v,v1,k,matcher,finder,v2,A,i,j,l,l1,p;
      split:=function(s)
        local m,v;
        m:=Minimum(s);
        v:=Filtered([1..Length(s)],i->s[i]=m);
        v:=Concatenation([0],v,[Length(s)+1]);
        a:=List([1..Length(v)-1],i->s{[v[i]+1..v[i+1]-1]});
        return a;
      end;
    finder:=function(A,t)
      local ags,i;
      ags:=[];
      for i in A do
        if Length(Filtered(i,j->j=1))>=t then
          Add(ags,i);
        fi;
      od;
      return ags;
    end;
    matcher:=function(s,n)
      local S,A,i,v1,j,v,vec,l,l1;
      S:=Set(s);
      A:=Tuples([0,1],n);
      v:=[];
      for i in S do
        v1:=[]; for j in [1..Length(s)] do
                              if s[j]=i then
                                v1:=Concatenation(v1,[j]);
                              fi;
                            od;
        v:=Concatenation(v,[v1]);
      od;
      vec:=List([1..Length(s)],i->0);
      for l in [1..Length(S)] do
       for l1 in v[Length(S)+1-l] do
        vec[l1]:=finder(A,S[Length(S)+1-l])[1];
          RemoveSet(A,finder(A,S[Length(S)+1-l])[1]);
        od;
      od;
      return vec;
    end;
      if s=[] then
        ags:=[[infinity]]; else
        m:=Minimum(s);
        ags:=[];
        a:=split(s);
        v:=List([1..Length(a)],i->minset(a[i]));
        v1:=List([1..Length(a)],i->Length(minset(a[i])));
        for i in Filtered([1..Length(a)],i->a[i]=[]) do
          v1[i]:=0;
        od;
        k:=List([1..Length(a)],i->1);
        v2:=matcher(v1,Int(Ceil(Log2(Float(Length(s)+1)))));
        A:=List([1..Length(v2[1])],i->List([1..Length(a)],j->0));
        for i in [1..Length(v2[1])] do
          for j in [1..Length(a)] do
               if v2[j][i]=0 then
                 A[i][j]:=List([1..Length(a[j])+1],i1->m);
               else
                 A[i][j]:=v[j][k[j]]; k[j]:=Minimum(k[j]+1,Length(minset(a[j])));
               fi;
             od;
           od;
           for i in [1..Length(v2[1])] do
             l:=[];
             for j in [1..Length(a)] do
               l:=Concatenation(l,A[i][j]);
             od;
             Add(ags,l);
           od;
         fi;
      return ags;
    end; if s=[] then ags:=[]; else
    ags:=[];
    M:=Maximum(s)+1;
    for i in minset(s) do
      for j in Filtered([1..Length(i)],k->i[k]=infinity) do
        i[j]:=M;
        od;
        AddSet(ags,i);
      od;
    fi;
    return ags;
  end;
  if not(IsTable(v)) then
    Error("The first argument must be a list of multiplicity sequences");
  fi;
  if not(ForAll(Union(v), IsPosInt)) then
    Error("The argument must be a list of multiplicity sequences");
  fi;

  if not(ForAll(v, ismultseq)) then
    Error("The argument must be a list of multiplicity sequences");
  fi;
  if Length(v)=1 and M=[] then
    return arfCharactersOfArfNumericalSemigroup(ArfSemigroupFromMultiplicitySequence(v[1]));
  else
  if not   IsUpperTriangularMat(M) then
    Error("The matrix does not correspond to a tree");
  fi;

  if not check(M) then
    Error("The matrix does not correspond to a tree");
  fi;




  if Length(M)<>Length(v) then
    Error("There is a problem with dimensions");
  fi;
  n:=Length(M);

  if not(ForAll(Cartesian([1..n],[1..n]), i->M[i[1]][i[2]]<=CompatibilityLevelOfMultiplicitySequences([v[i[1]],v[i[2]]]))) then
    Error("The arguments do not correspond to an Arf good semigroup (not compatible)");
  fi;
  if not(IsTable(M)) then
    Error("The second argument is a matrix");
  fi;
  if not(ForAll(Union(M), IsInt)) then
    Error("The entries of the matrix must be integers");
  fi;
  V:=function(idx,M)
    local i,Mh;
    n:=Length(M);
  Mh:=ShallowCopy(M);
    for i in [1..n] do
      for j in [Length(Mh[i])..Maximum(Length(Mh[i]),idx[i])] do
        Mh[i]:=Concatenation(Mh[i],[1]);
      od;
    od;
      return List([1..n], i->Sum(Mh[i]{[1..idx[i]]}));
  end;
  n:=Length(v);
  p:=UntwistingPermutation(M);
  Coll:=PermuteList(v,p);
  k:=List([1..Length(v)-1],i->PermuteMatrix(M,p)[i][i+1]);
  r:=[];
  pchar:=[];
  for l in [1..n] do
    if Coll[l][Length(Coll[l])]=1 then
      ms:=Concatenation(Coll[l],[1]);
    else
      ms:=Concatenation(Coll[l],[1,1]);
    fi;
    r[l]:=List(ms,_->0);
    for i in [1..Length(ms)] do
      b:=First([i+1..Length(ms)], j->ms[i]=Sum(ms{[i+1..j]}));
      if b=fail then
        b:=Length(ms);
      fi;
      for j in [i+1..b] do
        r[l][j]:=r[l][j]+1;
      od;
    od;
    pchar[l]:=Filtered([1..Length(ms)-1], j->r[l][j]<r[l][j+1]);
  od;
  max:=Maximum(Union(pchar))+1;
  LB:=Maximum(List([1..n],j->Length(pchar[j])));
  G:=List([1..LB]);
  for i in [1..LB] do
    G[i]:=List([1..n]);
     for j in [1..n] do
       if i<=Length(pchar[j]) then
         G[i][j]:=pchar[j][i];
       else
         G[i][j]:=max;
       fi;
     od;
   od;
H:=List( Union(G,minset1(k)) , i->V(i,Coll));
fi;
  return List(H,i->PermuteList(i,p^(-1)));
end;
#################################################
##
#F UntwistedMultiplicityTreesWithConductor(C)
## Outputs the set of all the untwisted multiplicity trees
## associated to  Arf good semigroups with
## conductor C.
## This only handles the local case: C is positive
#################################################
UntwistedMultiplicityTreesWithConductor:=function(C)
  local ags, C2, ms1, ms2, car, pseq, min, M1, M2, k, k1, k2, flt, vectorToTree,
  m, t, mt1, mt2, bound, pt, c, len,MultiplicityTreeToMultiplicitySequenceAndRamificationVector;

  # length of a multiplicity sequence
  len := function(l)
    local fone;
    fone:=First([1..Length(l)], x->l[x]=1);
    if fone=fail then
      return Length(l);
    fi;
    if fone=1 then
      return 1;
    fi;
    return fone-1;
  end;
  # function that recover the ramification vectors from an untwisted tree
  MultiplicityTreeToMultiplicitySequenceAndRamificationVector:=function(t)
    local M, k, depth, nodes, edges, n, id, i, pathtoroot, cand, maxdepth, inarf, ismultseq, paths;


    # tests whether x is in the Arf semigroup with multiplicity
    # sequence j
    inarf:=function(x,j)
        local l;
        if x>Sum(j) then
          return true;
        fi;
        if x=0 then
          return true;
        fi;
        if x<j[1] then
          return false;
        fi;
        l:=List([1..Length(j)], i-> Sum(j{[1..i]}));
        return x in l;
    end;

    # tests if m is a multiplicity sequence
    ismultseq := function(m)
        local n;
        n:=Length(m);
        return ForAll([1..n-1], i-> inarf(m[i], m{[i+1..n]}));
    end;

    # determines the path from v to the root of the tree t
    pathtoroot:=function(v)
      local path, nv, e;
      path:=[v];
      nv:=v;
      while true do
        e:=First(edges, e->e[2]=nv);
        if e=fail then
          return path;
        fi;
        nv:=e[1];
        Add(path,nv);
      od;
      return path;
    end;


    if not(IsList(t)) and Length(t)<>2 then
      Error("The argument is a tree, given by a list: the first element is the list of nodes and second the list of edges");
    fi;

    nodes:=t[1];
    edges:=t[2];
    n:=Length(nodes[1][1]);
    id:=IdentityMat(n);
    depth:=[];#Maximum(List(nodes, x->x[2]));
    for i in [1..n] do
      cand:=Filtered(nodes, n-> n[1]=id[i]);
      if cand=[] then
        Error("The tree is not a multiplicity tree, node ", id[i], "missing");
      fi;
      depth[i]:=Maximum(List(cand, x->x[2]));
    od;
    maxdepth:=Maximum(depth);

    M:=[];
    paths:=[];
    for i in [1..n] do
      paths[i]:=Reversed(pathtoroot([id[i],depth[i]]));
      M[i]:=List(paths[i], x->x[1][i]);
    od;

    if not(ForAll(M, ismultseq)) then
      Error("The argument is not a multiplicity tree");
    fi;

    k:=[];
    for i in [1..n-1] do
      cand:=First(paths[i], x->x[1][i+1]=0);
      if cand=fail then
        Error("The argument is not a multiplicity tree");
      fi;
      k[i]:=cand[2]-1;
    od;
    if not(ForAll([1..n-1], i->k[i]<=CompatibilityLevelOfMultiplicitySequences([M[i],M[i+1]]))) then
      Error("The tree is not compatible with any Arf good semigroup");
    fi;
    return [M,k];
  end;
  # translates vectors of ramifications to untwisted tree
  vectorToTree:=function(v,M)
    local edges, nodes, depth, level, k, id, i, j, pn, nd, leaves, sons, max, n, Mh,len;
    # length of a multiplicity sequence
    len := function(l)
      local fone;
      fone:=First([1..Length(l)], x->l[x]=1);
      if fone=fail then
        return Length(l);
      fi;
      if fone=1 then
        return 1;
      fi;
      return fone-1;
    end;
  if v=[] then
    nodes:=[]; edges:=[];
    for i in [1..len(M[1])+1] do
      if i<len(M[1])+1 then
      Add(nodes,[[M[1][i]],[i]]);
    else Add(nodes,[[1],[i]]);
    fi;
    od;
    for i in [1..len(M[1])] do
      Add(edges,[nodes[i],nodes[i+1]]);
    od;

  else
    max:= Maximum(List(M, Length));
    n:=Length(M);
    id:=IdentityMat(n);
    depth:=Maximum(Maximum(v)+1,max+1);

    Mh:=ShallowCopy(M);
    for i in [1..n] do
        Mh[i]:=Concatenation(Mh[i],List([Length(Mh[i])+1..depth],_->1));
    od;

    edges:=[];
    nodes:=[];
    leaves:=[];
    for level in [1..depth] do
      pn:=List([1..n], j->Mh[j][level]*id[j]);
      #Print(pn,"\n");
      nd:=pn[1];
      for j in [2..n] do
        if level<=v[j-1] then
          nd:=nd+pn[j];
        else
          if Sum(nd)=1 and not(nd in leaves) then
            Add(nodes,[nd,level]);
            Add(leaves,nd);
          fi;
          if Sum(nd)>1 then
            Add(nodes,[nd,level]);
          fi;
          nd:=pn[j];
          #Print("Nodes so far for ",v," ", nodes, "\n");
        fi;
      od;
      if Sum(nd)=1 and not(nd in leaves) then
        Add(nodes,[nd,level]);
        Add(leaves,nd);
      fi;
      if Sum(nd)>1 then
        Add(nodes,[nd,level]);
      fi;
      #Print("Nodes so far for ",v," ", nodes, "\n");
    od;

    for level in [1..depth-1] do
      pn:=Filtered(nodes, x->x[2]=level);
      for nd in pn do
        sons:=Filtered(nodes, x->(x[2]=level+1) and x[1]*nd[1]<>0);
        #Print("Nodes connected to ",nd," are ",sons,"\n");
        sons:=List(sons, x->[nd,x]);
        #Print("Adding edges ",sons);
        edges:=Union(edges, sons);
        #Print("New edges ", edges);
      od;
    od;
  fi;
    return [nodes,edges];
  end;


  if not(IsListOfIntegersNS(C)) then
    Error("The input must be a list of positive integers");
  fi;
  if Length(C)>1 and not(ForAll(C, IsPosInt)) then
    Error("The input must be a list of positive integers or [0]");
  fi;

  # one dimensional case
  if Length(C)=1 then
    ms1:=ArfNumericalSemigroupsWithFrobeniusNumber(C[1]-1);
    ms1:=List(ms1, MultiplicitySequenceOfNumericalSemigroup);
    for m in ms1 do
      for k1 in [1.. Length(m)] do
        m[k1]:=[[m[k1]],k1];
      od;
      #m:=[m, List([1..Length(m)-1],i-> [m[i],m[i+1]])];
    od;
    return List(ms1, m->[m, List([1..Length(m)-1],i-> [m[i],m[i+1]])]);
  fi;

  # two dimensional case
  if Length(C)=2 then
    C2:=[C[1],C[2]];

    ms1:=List(ArfNumericalSemigroupsWithFrobeniusNumber(C2[1]-1), MultiplicitySequenceOfNumericalSemigroup);
    ms1:=List(ms1, l->l{[1..Length(l)-1]});
    ms2:=List(ArfNumericalSemigroupsWithFrobeniusNumber(C2[2]-1), MultiplicitySequenceOfNumericalSemigroup);
    ms2:=List(ms2, l->l{[1..Length(l)-1]});

    car:=Cartesian(ms1,ms2);
    ags:=[];
    for pseq in car do
      M1:=pseq[1];
      M2:=pseq[2];
      min:=Minimum(CompatibilityLevelOfMultiplicitySequences([M1,M2]), Minimum(Length(M1),Length(M2)));
      for k in [1.. min] do
        Add(ags,[[M1,M2],[k]]);
      od;
    od;


    ms1:=List(ArfNumericalSemigroupsWithFrobeniusNumber(C2[1]-1), MultiplicitySequenceOfNumericalSemigroup);

    for k2 in [0..C[2]-1] do
      ms2:=List(ArfNumericalSemigroupsWithFrobeniusNumber(k2-1), MultiplicitySequenceOfNumericalSemigroup);
      #ms2:=Concatenation([[1]],List(ms2, l->l{[1..Length(l)-1]}));
      car:=Cartesian(ms1,ms2);
      flt:=Filtered(car, M-> Length(M[2])+C[2]-k2-1 <= Minimum(Length(M[1])-1,CompatibilityLevelOfMultiplicitySequences(M)));
      ags:=Concatenation(ags, List(flt, M-> [M,[Length(M[2])-1+C[2]-k2]]));
    od;

    ms2:=List(ArfNumericalSemigroupsWithFrobeniusNumber(C2[2]-1), MultiplicitySequenceOfNumericalSemigroup);
    #ms2:=List(ms2, l->l{[1..Length(l)-1]});

    for k1 in [0..C[1]-1] do
      ms1:=List(ArfNumericalSemigroupsWithFrobeniusNumber(k1-1), MultiplicitySequenceOfNumericalSemigroup);
      #ms1:=Concatenation([[1]],List(ms1, l->l{[1..Length(l)-1]}));
      car:=Cartesian(ms1,ms2);
      flt:=Filtered(car, M-> Length(M[1])+C[1]-k1-1 <= Minimum(Length(M[2])-1,CompatibilityLevelOfMultiplicitySequences(M)));
      ags:=Concatenation(ags, List(flt, M-> [M,[Length(M[1])-1+C[1]-k1]]));
    od;

    for k1 in [0..C[1]-1] do
      for k2 in [0..C[2]-1] do
        ms1:=List(ArfNumericalSemigroupsWithFrobeniusNumber(k1-1), MultiplicitySequenceOfNumericalSemigroup);
        #ms1:=Concatenation([[1]],List(ms1, l->l{[1..Length(l)-1]}));
        ms2:=List(ArfNumericalSemigroupsWithFrobeniusNumber(k2-1), MultiplicitySequenceOfNumericalSemigroup);
        #ms2:=Concatenation([[1]],List(ms2, l->l{[1..Length(l)-1]}));
        car:=Cartesian(ms1,ms2);
        flt:=Filtered(car, M-> Length(M[1])+C[1]-k1 = Length(M[2])+C[2]-k2 and Length(M[2])-1+C[2]-k2<=CompatibilityLevelOfMultiplicitySequences(M));
        ags:=Concatenation(ags, List(flt, M-> [M,[Length(M[1])-1+C[1]-k1]]));
      od;
    od;

    return List(ags, a-> vectorToTree(a[2],a[1]));
  fi; #end of the two dimensional case

  t:=CeilingOfRational(Length(C)/2);

  ags:=[];

  #S_1^1(C)
  mt1:=UntwistedMultiplicityTreesWithConductor(C{[1..t]});
  if t=Length(C)-1 then
    if C[Length(C)]=1 then
      mt2:=UntwistedMultiplicityTreesWithConductor([0]);
    else
      mt2:=UntwistedMultiplicityTreesWithConductor(C{[t+1..Length(C)]});
    fi;
  else
    mt2:=UntwistedMultiplicityTreesWithConductor(C{[t+1..Length(C)]});
  fi;
  car :=Cartesian(mt1,mt2);
  for c in car do
    ms1:=MultiplicityTreeToMultiplicitySequenceAndRamificationVector(c[1]);
    ms2:=MultiplicityTreeToMultiplicitySequenceAndRamificationVector(c[2]);
    if t=Length(C)-1 then
      bound:=Minimum(Maximum(ms1[2][t-1], len(ms1[1][t])),
            len(ms2[1][1]),
            CompatibilityLevelOfMultiplicitySequences([ms1[1][t],ms2[1][1]]));
    else
      bound:=Minimum(Maximum(ms1[2][t-1], len(ms1[1][t])),
            Maximum(len(ms2[1][1]),ms2[2][1]),
            CompatibilityLevelOfMultiplicitySequences([ms1[1][t],ms2[1][1]]));
    fi;
    for pt in [1..bound] do
      Add(ags, [Concatenation(ms1[1],ms2[1]), Concatenation(ms1[2],[pt],ms2[2])]);
    od;
  od;

  #S_1^2(C)
  mt1:=UntwistedMultiplicityTreesWithConductor(C{[1..t]});
  for k1 in [1..C[t+1]-1] do
                if t=Length(C)-1 then
                    if k1=1 then
                               mt2:=UntwistedMultiplicityTreesWithConductor(Concatenation([0],C{[t+2..Length(C)]}));
                else
                               mt2:=UntwistedMultiplicityTreesWithConductor(Concatenation([k1],C{[t+2..Length(C)]}));
                fi;
    else
      mt2:=UntwistedMultiplicityTreesWithConductor(Concatenation([k1],C{[t+2..Length(C)]}));
    fi;
    car:=Cartesian(mt1,mt2);
    for c in car do
      ms1:=MultiplicityTreeToMultiplicitySequenceAndRamificationVector(c[1]);
      ms2:=MultiplicityTreeToMultiplicitySequenceAndRamificationVector(c[2]);
      if t=Length(C)-1 then
        pt:=len(ms2[1][1])+C[t+1]-k1;
      else
        pt:=Maximum(len(ms2[1][1]),ms2[2][1])+C[t+1]-k1;
      fi;
      if pt<= Minimum(Maximum(ms1[2][t-1], len(ms1[1][t])), CompatibilityLevelOfMultiplicitySequences([ms1[1][t],ms2[1][1]])) then
        Add(ags, [Concatenation(ms1[1],ms2[1]), Concatenation(ms1[2],[pt],ms2[2])]);
      fi;
    od;
  od;

  #S_2^1(C)

  mt2:=UntwistedMultiplicityTreesWithConductor(C{[t..Length(C)]});
  if t=2 then
   if C[1]=1 then
     mt1:=UntwistedMultiplicityTreesWithConductor([0]);
   else
     mt1:=UntwistedMultiplicityTreesWithConductor(C{[1..t-1]});
   fi;
  else
    mt1:=UntwistedMultiplicityTreesWithConductor(C{[1..t-1]});
  fi;
  car :=Cartesian(mt1,mt2);
  for c in car do
    ms1:=MultiplicityTreeToMultiplicitySequenceAndRamificationVector(c[1]);
    ms2:=MultiplicityTreeToMultiplicitySequenceAndRamificationVector(c[2]);
    if t=2 then
        bound:=Minimum(Length(ms1[1][1])-1,
              Maximum(Length(ms2[1][1])-1,ms2[2][1]),
              CompatibilityLevelOfMultiplicitySequences([ms1[1][1],ms2[1][1]]));
    else
      bound:=Minimum(Maximum(ms1[2][t-2], Length(ms1[1][t-1])-1),
            Maximum(Length(ms2[1][1])-1,ms2[2][1]),
            CompatibilityLevelOfMultiplicitySequences([ms1[1][t-1],ms2[1][1]]));
    fi;
    for pt in [1..bound] do #here pt is "ptminusone" we do not waste a variable
      Add(ags, [Concatenation(ms1[1],ms2[1]), Concatenation(ms1[2],[pt],ms2[2])]);
    od;
  od;

  #S_2^2
  mt2:=UntwistedMultiplicityTreesWithConductor(C{[t..Length(C)]});
  for k1 in [1..C[t-1]-1] do
    if t=2 then
      if  k1=1 then
        mt1:=UntwistedMultiplicityTreesWithConductor(Concatenation(C{[1..t-2]},[0]));
      else
        mt1:=UntwistedMultiplicityTreesWithConductor(Concatenation(C{[1..t-2]},[k1]));
      fi;
    else
      mt1:=UntwistedMultiplicityTreesWithConductor(Concatenation(C{[1..t-2]},[k1]));
    fi;
    car:=Cartesian(mt1,mt2);
    for c in car do
      ms1:=MultiplicityTreeToMultiplicitySequenceAndRamificationVector(c[1]);
      ms2:=MultiplicityTreeToMultiplicitySequenceAndRamificationVector(c[2]);
      if t=2 then
          pt:=len(ms1[1][1])+C[1]-k1;
      else
        pt:=Maximum(len(ms1[1][t-1]),ms1[2][t-2])+C[t-1]-k1;
      fi;
      if pt<= Minimum(Maximum(ms2[2][1], len(ms2[1][1])), CompatibilityLevelOfMultiplicitySequences([ms1[1][t-1],ms2[1][1]])) then
        Add(ags, [Concatenation(ms1[1],ms2[1]), Concatenation(ms1[2],[pt],ms2[2])]);
      fi;
    od;
  od;
  return Set(Set(ags), a->vectorToTree(a[2],a[1]));
end;





####################################################
### internal, for drawing
####################################################
treeToDot:=function(t)
  local digraph, n, e, str;

  str:=function(s)
    return Concatenation("\"",String(s),"\"");
  end;
  digraph:="graph T{\n";

  for n in t[1] do
    digraph:=Concatenation(digraph, str(n), "[label=\"", String(n[1]),"\"];\n" );
  od;

  for e in t[2] do
    digraph:=Concatenation(digraph, str(e[1]), "--", str(e[2]) ,";\n" );
  od;

  digraph:=Concatenation(digraph,"}");
  return digraph;
end;


splashTree:=function(t)
  local digraph, n, e, str, name;

  str:=function(s)
    return Concatenation("\"",String(s),"\"");
  end;
  digraph:="graph T{\n";

  for n in t[1] do
    digraph:=Concatenation(digraph, str(n), "[label=\"", String(n[1]),"\"];\n" );
  od;

  for e in t[2] do
    digraph:=Concatenation(digraph, str(e[1]), "--", str(e[2]) ,";\n" );
  od;

  digraph:=Concatenation(digraph,"}");


  name := Filename(DirectoryTemporary(), Concatenation("aperygraph", ".dot"));
  AppendTo(name, digraph);

  Exec("dot -Tpdf -o",Concatenation(name, ".pdf"),name);
  Exec("open ",Concatenation(name,".pdf"));

end;

htmlTrees:=function(ts, outname)
  local digraph, n, e, str, name, html, t,i;

  str:=function(s)
    return Concatenation("\"",String(s),"\"");
  end;

  html:="<!DOCTYPE html>\n<html>\n<head>\n<meta charset=\"utf-8\">\n <title>Multiplicity Trees</title>\n";
  html:=Concatenation(html, "<style>\n .content {\n display: inline-block;\n text-align: center;\n vertical-align: top;\n}\n</style></head>\n<body>\n<script  src=\"http://mdaines.github.io/viz.js/bower_components/viz.js/viz.js\">\n</script>\n");

  for i in [1..Length(ts)] do
    html:=Concatenation(html,"<span id=", str(i)," class='content'>Hola </span>\n");
  od;
  html:=Concatenation(html,"<script>\n");
  i:=1;
  for t in ts do
    digraph:="graph T{";

    for n in t[1] do
      digraph:=Concatenation(digraph, str(n), " [label=\"", String(n[1]),"\"];" );
    od;

    for e in t[2] do
      digraph:=Concatenation(digraph, str(e[1]), "--", str(e[2]) ,"; " );
    od;

    digraph:=Concatenation(digraph,"}");
    html:=Concatenation(html," document.getElementById(",str(i),").innerHTML =Viz('",digraph,"');\n");
    i:=i+1;
  od;

  html:=Concatenation(html, "</script>\n</body>\n</html>");

  name := Filename(DirectoryCurrent(), outname);
  Print("Saved to ",name,"\n");
  PrintTo(name, html);
  if ARCH_IS_MAC_OS_X() then
    Exec("open ",name);
  fi;
  if ARCH_IS_WINDOWS() then
    Exec("start firefox ",name);
  fi;
  return html;

end;

#####################################################
#F UntwistedMultiplicityTreesWithDimandGenus:=function(dim,gen)
## dim is a positive integer, gen is a non-negative integer
## The ouput is the set of the untwisted trees of the Arf local good semigroups
## with genus gen and dimension dim
#####################################################
UntwistedMultiplicityTreesWithDimandGenus:=function(dim,gen)
  local ags, C2, ms1, ms2, car, pseq, min, M1, M2, k, k1, k2, flt, vectorToTree,
  m, t, mt1, mt2, bound, p, c, arfNumericalSemigroupsWithGenus,len,MultiplicityTreeToMultiplicitySequenceAndRamificationVector;
    # function that recover the ramification vectors from an untwisted tree
  MultiplicityTreeToMultiplicitySequenceAndRamificationVector:=function(t)
    local M, k, depth, nodes, edges, n, id, i, pathtoroot, cand, maxdepth, inarf, ismultseq, paths;


    # tests whether x is in the Arf semigroup with multiplicity
    # sequence j
    inarf:=function(x,j)
        local l;
        if x>Sum(j) then
          return true;
        fi;
        if x=0 then
          return true;
        fi;
        if x<j[1] then
          return false;
        fi;
        l:=List([1..Length(j)], i-> Sum(j{[1..i]}));
        return x in l;
    end;

    # tests if m is a multiplicity sequence
    ismultseq := function(m)
        local n;
        n:=Length(m);
        return ForAll([1..n-1], i-> inarf(m[i], m{[i+1..n]}));
    end;

    # determines the path from v to the root of the tree t
    pathtoroot:=function(v)
      local path, nv, e;
      path:=[v];
      nv:=v;
      while true do
        e:=First(edges, e->e[2]=nv);
        if e=fail then
          return path;
        fi;
        nv:=e[1];
        Add(path,nv);
      od;
      return path;
    end;


    if not(IsList(t)) and Length(t)<>2 then
      Error("The argument is a tree, given by a list: the first element is the list of nodes and second the list of edges");
    fi;

    nodes:=t[1];
    edges:=t[2];
    n:=Length(nodes[1][1]);
    id:=IdentityMat(n);
    depth:=[];#Maximum(List(nodes, x->x[2]));
    for i in [1..n] do
      cand:=Filtered(nodes, n-> n[1]=id[i]);
      if cand=[] then
        Error("The tree is not a multiplicity tree, node ", id[i], "missing");
      fi;
      depth[i]:=Maximum(List(cand, x->x[2]));
    od;
    maxdepth:=Maximum(depth);

    M:=[];
    paths:=[];
    for i in [1..n] do
      paths[i]:=Reversed(pathtoroot([id[i],depth[i]]));
      M[i]:=List(paths[i], x->x[1][i]);
    od;

    if not(ForAll(M, ismultseq)) then
      Error("The argument is not a multiplicity tree");
    fi;

    k:=[];
    for i in [1..n-1] do
      cand:=First(paths[i], x->x[1][i+1]=0);
      if cand=fail then
        Error("The argument is not a multiplicity tree");
      fi;
      k[i]:=cand[2]-1;
    od;
    if not(ForAll([1..n-1], i->k[i]<=CompatibilityLevelOfMultiplicitySequences([M[i],M[i+1]]))) then
      Error("The tree is not compatible with any Arf good semigroup");
    fi;
    return [M,k];
  end;
  # length of a multiplicity sequence
  len := function(l)
    local fone;
    fone:=First([1..Length(l)], x->l[x]=1);
    if fone=fail then
      return Length(l);
    fi;
    if fone=1 then
      return 1;
    fi;
    return fone-1;
  end;

  # find all the Arf numerical semigroups with a given genus
  arfNumericalSemigroupsWithGenus:=function(g)
    local n, T, Gen, i,j,k, inarf, filt;

    # tests whether x is in the Arf semigroup with multiplicity
    # sequence j
    inarf:=function(x,j)
        local l;
        if x>Sum(j) then
          return true;
        fi;
        if x=0 then
          return true;
        fi;
        if x<j[1] then
          return false;
        fi;

        l:=List([1..Length(j)], i-> Sum(j{[1..i]}));
        return x in l;
    end;

    n:=g;

    if(not(IsInt(g))) then
      Error("The argument must be an integer");
    fi;

    if (g<0) then
      return [];
    fi;

    if n=0 then
      return [NumericalSemigroup(1)];
    fi;

    Gen:=List([[n+1]]);
    T:=[];
    for i in [1..n-1] do
      T[i]:=[[i+1]];
    od;

    for i in [1..n-1] do
      for j in T[i] do
        if inarf(n-i+1,j) then
            Add(Gen, Concatenation([n-i+1],j));
        fi;
        filt:= Filtered([j[1]..Int((n-i+2)/2)], x->inarf(x,j));
        for k in filt do
          Add(T[i+k-1],Concatenation([k],j));
        od;
      od;

    od;
    #return Cond;
    return List(Gen, j-> NumericalSemigroupBySmallElementsNC(Concatenation([0],List([1..Length(j)], i-> Sum(j{[1..i]})))));
  end;
  # translates vectors of ramifications to tree
  vectorToTree:=function(v,M)
    local edges, nodes, depth, level, k, id, i, j, pn, nd, leaves, sons, max, n, Mh,len;
    # length of a multiplicity sequence
    len := function(l)
      local fone;
      fone:=First([1..Length(l)], x->l[x]=1);
      if fone=fail then
        return Length(l);
      fi;
      if fone=1 then
        return 1;
      fi;
      return fone-1;
    end;
  if v=[] then
    nodes:=[]; edges:=[];
    for i in [1..len(M[1])+1] do
      if i<len(M[1])+1 then
      Add(nodes,[[M[1][i]],[i]]);
    else Add(nodes,[[1],[i]]);
    fi;
    od;
    for i in [1..len(M[1])] do
      Add(edges,[nodes[i],nodes[i+1]]);
    od;

  else
    max:= Maximum(List(M, Length));
    n:=Length(M);
    id:=IdentityMat(n);
    depth:=Maximum(Maximum(v)+1,max+1);

    Mh:=ShallowCopy(M);
    for i in [1..n] do
        Mh[i]:=Concatenation(Mh[i],List([Length(Mh[i])+1..depth],_->1));
    od;

    edges:=[];
    nodes:=[];
    leaves:=[];
    for level in [1..depth] do
      pn:=List([1..n], j->Mh[j][level]*id[j]);
      #Print(pn,"\n");
      nd:=pn[1];
      for j in [2..n] do
        if level<=v[j-1] then
          nd:=nd+pn[j];
        else
          if Sum(nd)=1 and not(nd in leaves) then
            Add(nodes,[nd,level]);
            Add(leaves,nd);
          fi;
          if Sum(nd)>1 then
            Add(nodes,[nd,level]);
          fi;
          nd:=pn[j];
          #Print("Nodes so far for ",v," ", nodes, "\n");
        fi;
      od;
      if Sum(nd)=1 and not(nd in leaves) then
        Add(nodes,[nd,level]);
        Add(leaves,nd);
      fi;
      if Sum(nd)>1 then
        Add(nodes,[nd,level]);
      fi;
      #Print("Nodes so far for ",v," ", nodes, "\n");
    od;

    for level in [1..depth-1] do
      pn:=Filtered(nodes, x->x[2]=level);
      for nd in pn do
        sons:=Filtered(nodes, x->(x[2]=level+1) and x[1]*nd[1]<>0);
        #Print("Nodes connected to ",nd," are ",sons,"\n");
        sons:=List(sons, x->[nd,x]);
        #Print("Adding edges ",sons);
        edges:=Union(edges, sons);
        #Print("New edges ", edges);
      od;
    od;
  fi;
    return [nodes,edges];
  end;

if not IsPosInt(gen) and not gen=0  then
  Error("The second input (genus) must be a non negative integer");
fi;

if not IsPosInt(dim)  then
  Error("The first input (dimension) must be a positive integer");
fi;

  # one dimensional case
  if dim=1 then
    ms1:=arfNumericalSemigroupsWithGenus(gen);
    ms1:=List(ms1, MultiplicitySequenceOfNumericalSemigroup);
    for m in ms1 do
      for k1 in [1.. Length(m)] do
        m[k1]:=[[m[k1]],k1];
      od;
      #m:=[m, List([1..Length(m)-1],i-> [m[i],m[i+1]])];
    od;
    return List(ms1, m->[m, List([1..Length(m)-1],i-> [m[i],m[i+1]])]);
  fi;



  t:=Int(Floor(Float(dim/2)));

  ags:=[];

for p in [1..gen-dim+2] do
    for k in [t-1..CeilingOfRational((gen-p-1)/2)] do
            mt1:=UntwistedMultiplicityTreesWithDimandGenus(t,k);
            mt2:=UntwistedMultiplicityTreesWithDimandGenus(dim-t,gen-p-k);
            car :=Cartesian(mt1,mt2);
                                for c in car do
                                ms1:=MultiplicityTreeToMultiplicitySequenceAndRamificationVector(c[1]);
                                ms2:=MultiplicityTreeToMultiplicitySequenceAndRamificationVector(c[2]);
                                     if p<=CompatibilityLevelOfMultiplicitySequences([ms1[1][t],ms2[1][1]]) then
                                           Add(ags, [Concatenation(ms1[1],ms2[1]), Concatenation(ms1[2],[p],ms2[2])]);
                                          Add(ags, Concatenation([Reversed(Concatenation(ms1[1],ms2[1]))],[Reversed(Concatenation(ms1[2],[p],ms2[2]))]));
                                     fi;
                                               od;
                                     od;
                          od;
  return Set(Set(ags), a->vectorToTree(a[2],a[1]));
end;

#####################################################
#F UntwistedMultiplicityTreesWithGenus:=function(gen)
## gen is a non-negative integer
## The ouput is the set of the untwisted trees of the Arf local good semigroups
## with genus gen in all dimensions
#####################################################
UntwistedMultiplicityTreesWithGenus:=function(gen)
local ags,i;
if not IsPosInt(gen) and not gen=0  then
  Error("The second input (genus) must be a non negative integer");
fi;
ags:=[];
for i in [1..gen+1] do
  ags:=Union(ags,UntwistedMultiplicityTreesWithDimandGenus(i,gen));
od;
return ags;
end;






#################################################
##
## MultiplicityTreesWithConductor
## The input is a positive vector C.
## The output is the set of all the trees of Arf good semigroups
## with C as conductor
#################################################
MultiplicityTreesWithConductor:=function(C)
  local ags,A,i,j,ags1;
  if not(IsListOfIntegersNS(C)) then
    Error("The input must be a list of positive integers");
  fi;
  if Length(C)>1 and not(ForAll(C, IsPosInt)) then
    Error("The input must be a list of positive integers or [0]");
  fi;

  ags:=[];
  A:=List(Filtered(Tuples([1..Length(C)],Length(C)),i->Length(Set(i))=Length(C)),j->PermList(j));
  for i in A do
    ags:=Concatenation(ags,List(UntwistedMultiplicityTreesWithConductor(PermuteList(C,i)),k->PermuteTree(k,i^(-1))));
  od;
return List(Set(List(ags,i->MultiplicityTreeToMultiplicitySequenceAndRamificationMatrix(i))),k->TreeFromMultiplicitySequenceListAndRamificationMatrix(k[1],k[2]));

end;
#################################################
##
##MultiplicitySequenceListAndRamificationMatrixWithConductor
## The input is a positive vector C.
## The output is the set of all the  Arf good semigroups
## with C as conductor described by the collection of multiplicity sequences and the ramification matrix
#################################################
MultiplicitySequenceListAndRamificationMatrixWithConductor:=function(C)
  local ags,A,i,j,ags1;
  if not(IsListOfIntegersNS(C)) then
    Error("The input must be a list of positive integers");
  fi;
  if Length(C)>1 and not(ForAll(C, IsPosInt)) then
    Error("The input must be a list of positive integers or [0]");
  fi;
  ags:=[];
  A:=List(Filtered(Tuples([1..Length(C)],Length(C)),i->Length(Set(i))=Length(C)),j->PermList(j));
  for i in A do
    ags:=Concatenation(ags,List(UntwistedMultiplicityTreesWithConductor(PermuteList(C,i)),k->PermuteTree(k,i^(-1))));
  od;
return Set(List(ags,i->MultiplicityTreeToMultiplicitySequenceAndRamificationMatrix(i)));

end;
#####################################################
#F MultiplicityTreesWithDimandGenus:=function(dim,gen)
## dim is a positive integer, gen is a non-negative integer
## The ouput is the set of the  trees of the Arf local good semigroups
## with genus gen and dimension dim
#####################################################
MultiplicityTreesWithDimandGenus:=function(dim,genus)
local ags,A,i,j,ags1;

if not IsPosInt(genus) and not genus=0  then
  Error("The second input (genus) must be a non negative integer");
fi;

if not IsPosInt(dim)  then
  Error("The first input (dimension) must be a positive integer");
fi;

ags:=[];
A:=List(Filtered(Tuples([1..dim],dim),i->Length(Set(i))=dim),j->PermList(j));
for i in A do
  ags:=Concatenation(ags,List(UntwistedMultiplicityTreesWithDimandGenus(dim,genus),k->PermuteTree(k,i)));
od;
return List(Set(List(ags,i->MultiplicityTreeToMultiplicitySequenceAndRamificationMatrix(i))),k->TreeFromMultiplicitySequenceListAndRamificationMatrix(k[1],k[2]));;
end;
MultiplicitySequenceListAndRamificationMatrixWithDimandGenus:=function(dim,genus)
local ags,A,i,j,ags1;

if not IsPosInt(genus) and not genus=0  then
  Error("The second input (genus) must be a non negative integer");
fi;

if not IsPosInt(dim)  then
  Error("The first input (dimension) must be a positive integer");
fi;

ags:=[];
A:=List(Filtered(Tuples([1..dim],dim),i->Length(Set(i))=dim),j->PermList(j));
for i in A do
  ags:=Concatenation(ags,List(UntwistedMultiplicityTreesWithDimandGenus(dim,genus),k->PermuteTree(k,i)));
od;
return Set(List(ags,i->MultiplicityTreeToMultiplicitySequenceAndRamificationMatrix(i)));
end;
#####################################################
#F MultiplicityTreesWithGenus:=function(gen)
## gen is a non-negative integer
## The ouput is the set of the  trees of the Arf local good semigroups
## with genus gen in all dimensions
#####################################################
MultiplicityTreesWithGenus:=function(gen)
local ags,i;
if not IsPosInt(gen) and not gen=0  then
  Error("The input (genus) must be a non negative integer");
fi;
ags:=[];
for i in [1..gen+1] do
  ags:=Union(ags,MultiplicityTreesWithDimandGenus(i,gen));
od;
return ags;
end;
