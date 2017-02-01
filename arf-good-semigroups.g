#################################################
##
#F MultiplicitySequenceListToTrees(M)
## The input is a list of multiplicity sequences,
## and the output is the list of all possible
## multiplicity trees for this list.
## Implementation done with G. Zito
#################################################
MultiplicitySequenceListToTrees:=function(M)
  local ismultseq, T, s, k, inarf, i, j, n, max, D, space, vectorToTree, Mh, sons;


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

  # translates vectors of ramifications to tree
  vectorToTree:=function(v)
    local edges, nodes, depth, level, k, id, j, pn, nd, leaves;

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
    return [nodes,edges];
  end;

  if not(IsTable(M)) then
    Error("The argument must be a list of multiplicity sequences");
  fi;

  if Length(M)<=1 then
    return [];
  fi;

  if not(ForAll(Union(M), IsPosInt)) then
    Error("The argument must be a list of multiplicity sequences");
  fi;

  if not(ForAll(M, ismultseq)) then
    Error("The argument must be a list of multiplicity sequences");
  fi;

  s:=[];
  n:=Length(M);
  max:= Maximum(List(M, Length));

  for i in [1..n] do
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
  for i in [1..n] do
      s[i]:=Concatenation(s[i],List([Length(s[i])+1..max],_->1));
  od;

  Info(InfoNumSgps,2,"s=",s);
  D:=List([1..n-1], i->Filtered([1..max], j->s[i][j]<>s[i+1][j]));
  k:=[];
  space:=[];
  for i in [1..n-1] do
    if D[i]=[] then
      k[i]:=infinity;
      space[i]:=[1..Length(M[i])];
      Info(InfoNumSgps, 1, "There will be infinitely many trees corresponding to the branches ",i," and ",i+1,", we will only ouptput up to level", Length(M[i]));
    else
      k[i]:=Minimum(Set(D[i], j->j+Minimum(s[i][j],s[i+1][j])));
      space[i]:=[1..k[i]];
    fi;
  od;
  Info(InfoNumSgps,2,"Discrepancy=",D);
  Info(InfoNumSgps,2,"k-vector=",k);

  T:=Cartesian(space);

  return List(T,vectorToTree);
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

############################################################
#F MultiplicityTreeToMultiplicitySequenceAndRamificationVector(t)
## t is the multiplicity of an Arf semigroup. The output is
## the list of multiplicity sequences with the vector telling
## where these ramify in the tree
############################################################
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

#################################################
##
#F ArfGoodSemigroupFromMultiplicitySequenceListAndRamificationLevel(M, level)
## The input is a list of two multiplicity sequences
## and a level where the tree ramifies.
## The level must be compatible with the multiplicity lists.
## The output is the Arf good semigroup corresponding
## to this tree.
## Implementation done with G. Zito
#################################################
ArfGoodSemigroupFromMultiplicitySequenceListAndRamificationLevel:=function(M, level)
  local C, gens, k, kk, R, B1, B2, Mh, i;

  if not(IsPosInt(level)) then
    Error("The second argument must be a positive integer");
  fi;

  k:=CompatibilityLevelOfMultiplicitySequences(M);
  if (level>k) then
    Error("The second argument is bigger than the compatibility level of the multiplicity sequences");
  fi;

  Mh:=ShallowCopy(M);
  for i in [1..2] do
      Mh[i]:=Concatenation(Mh[i],List([Length(Mh[i])+1..Maximum(Length(Mh[i]),level)],_->1));
  od;

  C:=[];
  C[1]:=Sum([1..Maximum(Length(M[1]),level)], k->Mh[1][k]);
  C[2]:=Sum([1..Maximum(Length(M[2]),level)], k->Mh[2][k]);
  Info(InfoNumSgps,2,"Conductor is ", C);

  R:=[Mh[1][1],Mh[2][1]];
  gens:=[[0,0],R,C];
  for k in [2..level] do
    R:=R+[Mh[1][k],Mh[2][k]];
    Add(gens,R);
  od;

  B1:=R;
  B2:=R;
  for k in [level+1..Maximum(Length(M[1]),level)] do
    B1:=B1+[Mh[1][k],0];
    Add(gens,B1);
    gens:=Concatenation(gens,B1+List([level+1..Maximum(Length(M[2]),level)], x->[0,Sum(M[2]{[level+1..x]})]));
  od;

  for k in [level+1..Maximum(Length(M[2]),level)] do
    B2:=B2+[0,Mh[2][k]];
    Add(gens,B2);
    gens:=Concatenation(gens,B2+List([level+1..Maximum(Length(M[1]),level)], x->[Sum(M[1]{[level+1..x]}),0]));
  od;
  Info(InfoNumSgps,2,"Small elements are ", gens);

  return GoodSemigroupBySmallElements(gens);
end;


#################################################
##
#F MultiplicityTreesWithConductor(C)
## Outputs the set of all multiplicity trees
## associated to all Arf good semigroups with
## conductor C.
## Implementation done with G. Zito
#################################################
MultiplicityTreesWithConductor:=function(C)
  local ags, C2, ms1, ms2, car, pseq, min, M1, M2, k, k1, k2, flt, vectorToTree;

  # translates vectors of ramifications to tree
  vectorToTree:=function(v,M)
    local edges, nodes, depth, level, k, id, i, j, pn, nd, leaves, sons, max, n, Mh;

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
    return [nodes,edges];
  end;


  if not(IsListOfIntegersNS(C)) then
    Error("The input must be a list of positive integers");
  fi;
  if not(ForAll(C, IsPosInt)) then
    Error("The input must be a list of positive integers");
  fi;

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

htmlTrees:=function(ts)
  local digraph, n, e, str, name, html, t,i;

  str:=function(s)
    return Concatenation("\"",String(s),"\"");
  end;

  html:="<!DOCTYPE html>\n<html>\n<head>\n<meta charset=\"utf-8\">\n <title>Multiplicity Trees</title>\n</head>\n<body>\n<script src=\"http://mdaines.github.io/viz.js/bower_components/viz.js/viz.js\"></script>\n";

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
    html:=Concatenation(html,"<div id=", str(i),">Hola </div>\n");
    html:=Concatenation(html,"<script>\n document.getElementById(",str(i),").innerHTML =Viz('",digraph,"');\n</script>\n");
    i:=i+1;
  od;

  html:=Concatenation(html, "</script>\n</body>\n</html>");

  name := Filename(DirectoryTemporary(), Concatenation("trees", ".html"));
  AppendTo(name, html);

  Exec("open ",Concatenation(name,".html"));

  return html;

end;