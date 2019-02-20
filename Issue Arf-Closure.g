ArfGoodSemigroupClosureold:=function(s)
  local s1, s2, t1, t2, sm, sma, c, included, i, cand, ca, c1, c2, gena, a, tail1, tail2, car;

  if not(IsGoodSemigroup(s)) then
    Error("The argument must be a good semigroup");
  fi;

  sm := SmallElementsOfGoodSemigroup(s);
  c:= Conductor(s);
  s1:=Set(sm, x->x[1]);
  s2:=Set(sm, x->x[2]);
  s1:=NumericalSemigroupBySmallElements(s1);
  s2:=NumericalSemigroupBySmallElements(s2);
  t1:=ArfNumericalSemigroupClosure(s1);
  t2:=ArfNumericalSemigroupClosure(s2);
  c1:=Conductor(t1);
  c2:=Conductor(t2);

  t1:=Intersection([0..c[1]],t1);
  t2:=Intersection([0..c[2]],t2);
  ca:=[c1,c2];

  i:=1;
  included:=true;
  while included do
    if i>Length(t1) or i>Length(t2) then
      i:=i-1;
      sma:=List([1..i], i->[t1[i],t2[i]]);
      return GoodSemigroupBySmallElements(sma);
    fi;
    sma:=Union(List([1..i], i->[t1[i],t2[i]]), Cartesian(t1{[i+1..Length(t1)]}, t2{[i+1..Length(t2)]}));
    if First(sm, x->not(x in sma))<> fail then
      included:=false;
    else
        i:=i+1;
    fi;
  od;
  i:=i-1;
  tail1:=Intersection(t1{[i+1..Length(t1)]},[0..c[1]]);
  tail2:=Intersection(t2{[i+1..Length(t2)]},[0..c[2]]);
  car:=Cartesian(tail1,tail2);
  sma:=Union(List([1..i], i->[t1[i],t2[i]]), car);

  return GoodSemigroupBySmallElements(sma);
end;

ArfGoodSemigroupClosurefix:=function(s)
  local CompatibilityLevelOfMultiplicitySequences, s1, s2, t1, t2, sm, sma, c, included, i, cand, ca, c1, c2, k, seq1, seq2, tail1, tail2, car;
    
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

  if not(IsGoodSemigroup(s)) then
    Error("The argument must be a good semigroup");
  fi;


  
  sm := SmallElementsOfGoodSemigroup(s);
  c:= Conductor(s);
  s1:=Set(sm, x->x[1]);
  s2:=Set(sm, x->x[2]);
  s1:=NumericalSemigroupBySmallElements(s1);
  s2:=NumericalSemigroupBySmallElements(s2);
  t1:=ArfNumericalSemigroupClosure(s1);
  t2:=ArfNumericalSemigroupClosure(s2);
  c1:=Conductor(t1);
  c2:=Conductor(t2);
  seq1:=MultiplicitySequenceOfNumericalSemigroup(t1);
  seq2:=MultiplicitySequenceOfNumericalSemigroup(t2);
  k:=CompatibilityLevelOfMultiplicitySequences([seq1,seq2]);
  
  t1:=Intersection([0..c[1]],t1);
  t2:=Intersection([0..c[2]],t2);
  ca:=[c1,c2];
  i:=1;
  included:=true;
  while included do
    if i>Length(t1) or i>Length(t2) then
      i:=i-1;
      sma:=List([1..i], i->[t1[i],t2[i]]);
      return GoodSemigroupBySmallElements(sma);
    fi;
    if i>k+1 then
      i:=i-1;
      sma:=List([1..i], i->[t1[i],t2[i]]);
      return GoodSemigroupBySmallElements(sma);
    fi;
    sma:=Union(List([1..i], i->[t1[i],t2[i]]), Cartesian(t1{[i+1..Length(t1)]}, t2{[i+1..Length(t2)]}));
    if First(sm, x->not(x in sma))<> fail then
      included:=false;
    else
        i:=i+1;
    fi;
  od;
  i:=i-1;
  tail1:=Intersection(t1{[i+1..Length(t1)]},[0..c[1]]);
  tail2:=Intersection(t2{[i+1..Length(t2)]},[0..c[2]]);
  car:=Cartesian(tail1,tail2);
  sma:=Union(List([1..i], i->[t1[i],t2[i]]), car);

  return GoodSemigroupBySmallElements(sma);
end;