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


arfNumericalSemigroupsWithFrobeniusNumber:=function(f)
  local n, T, Cond, i,j,k, inarf, filt;

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

  if(not(IsInt(f))) then
    Error("The argument must be an integer");
  fi;

  n:=f+1;
  if (n<0) or (n=1) then
    return [];
  fi;

  if n=0 then
    return [NumericalSemigroup(1)];
  fi;

  Cond:=List([[n]]);
  T:=[];
  for i in [2..n-2] do
    T[i]:=[[i]];
  od;

  for i in [2..n-2] do
    for j in T[i] do
      if inarf(n-i,j) then
          Add(Cond, Concatenation([n-i],j));
      fi;
      filt:= Filtered([j[1]..Int((n-i)/2)], x->inarf(x,j));
      for k in filt do
        Add(T[i+k],Concatenation([k],j));
      od;
    od;

  od;
  #return Cond;
  return List(Cond, j-> NumericalSemigroupBySmallElementsNC(Concatenation([0],List([1..Length(j)], i-> Sum(j{[1..i]})))));
end;


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


arfNumericalSemigroupsWithFrobeniusNumberUpTo:=function(f)
  local n, T, i,j,k, inarf, filt;


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

  if(not(IsInt(f))) then
    Error("The argument must be an integer");
  fi;

  n:=f+1;
  if (n<0) or (n=1) then
    return [];
  fi;

  if n=0 then
    return [NumericalSemigroup(1)];
  fi;

  T:=[];
  for i in [1..n] do
    T[i]:=[[i]];
  od;

  for i in [2..n-2] do
    for j in T[i] do
      filt:= Filtered([j[1]..n-i], x->inarf(x,j));
      for k in filt do
        Add(T[i+k],Concatenation([k],j));
      od;
    od;

  od;
  return List(Union(T),j-> NumericalSemigroupBySmallElementsNC(Concatenation([0],List([1..Length(j)], i-> Sum(j{[1..i]})))));
  #return List(Cond, j-> NumericalSemigroupBySmallElementsNC(Concatenation([0],List([1..Length(j)], i-> Sum(j{[1..i]})))));
end;


arfNumericalSemigroupsWithGenusUpTo:=function(g)
  local n, T, i,j,k, inarf, filt;

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

  T:=[];
  for i in [1..n] do
    T[i]:=[[i+1]];
  od;
  T[n+1]:=[[1]];

  for i in [1..n-1] do
    for j in T[i] do
      filt:= Filtered([j[1]..n-i+1], x->inarf(x,j));
      for k in filt do
        Add(T[i+k-1],Concatenation([k],j));
      od;
    od;

  od;
  return List(Union(T),j-> NumericalSemigroupBySmallElementsNC(Concatenation([0],List([1..Length(j)], i-> Sum(j{[1..i]})))));
  #return List(Gen, j-> NumericalSemigroupBySmallElementsNC(Concatenation([0],List([1..Length(j)], i-> Sum(j{[1..i]})))));
end;
