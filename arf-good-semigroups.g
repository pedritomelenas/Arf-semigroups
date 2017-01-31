MultiplicitySequenceListToTrees:=function(M)
  local ismultseq, T, s, k, inarf, i, n, max, D, space, vectorToTree, Mh, sons;


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
    local edges, nodes, depth, level, k, id, j, pn, nd;

    id:=IdentityMat(n);
    depth:=Maximum(Maximum(v)+1,max+1);
    edges:=[];
    nodes:=[];
    for level in [1..depth] do
      pn:=List([1..n], j->Mh[j][level]*id[j]);
      #Print(pn,"\n");
      nd:=pn[1];
      for j in [2..n] do
        if level<=v[j-1] then
          nd:=nd+pn[j];
        else
          Add(nodes,[nd,level]);
          nd:=pn[j];
          #Print("Nodes so far for ",v," ", nodes, "\n");
        fi;
      od;
      Add(nodes,[nd,level]);
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
      fi;
    od;
  od;
  for i in [1..n] do
      s[i]:=Concatenation(s[i],List([Length(s[i])+1..max],_->1));
  od;

  Mh:=ShallowCopy(M);
  for i in [1..n] do
      Mh[i]:=Concatenation(Mh[i],List([Length(Mh[i])+1..max+2],_->1));
  od;

  Info(InfoNumSgps,2,"Multiplicity sequences homogenized ",Mh);


  Info(InfoNumSgps,2,"s=",s);
  D:=List([1..n-1], i->Filtered([1..max], j->s[i][j]<>s[i+1][j]));
  k:=[];
  space:=[];
  for i in [1..n-1] do
    if D[i]=[] then
      k[i]:=Indeterminate(Rationals,i);
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
