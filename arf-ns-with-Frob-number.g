arfNumericalSemigroupsWithFrobeniusNumber:=function(f)
  local n, T, Cond, i,j,k, arf, filt;

  arf:=function(x,j)
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
    Error("The argument cannot be the Frobenius number of any numerical semigroup");
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
      if arf(n-i,j) then
          Add(Cond, Concatenation([n-i],j));
      fi;
      filt:= Filtered([j[1]..Int((n-i)/2)], x->arf(x,j));
      for k in filt do
        Add(T[i+k],Concatenation([k],j));
      od;
    od;

  od;
  #return Cond;
  return List(Cond, j-> NumericalSemigroupBySmallElementsNC(Concatenation([0],List([1..Length(j)], i-> Sum(j{[1..i]})))));
end;


arfNumericalSemigroupsWithGenus:=function(g)
  local n, T, Gen, i,j,k, arf, filt;

  arf:=function(x,j)
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
    Error("The argument must be a nonnegative integer");
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
      if arf(n-i+1,j) then
          Add(Gen, Concatenation([n-i+1],j));
      fi;
      filt:= Filtered([j[1]..Int((n-i+2)/2)], x->arf(x,j));
      for k in filt do
        Add(T[i+k-1],Concatenation([k],j));
      od;
    od;

  od;
  #return Cond;
  return List(Gen, j-> NumericalSemigroupBySmallElementsNC(Concatenation([0],List([1..Length(j)], i-> Sum(j{[1..i]})))));
end;
