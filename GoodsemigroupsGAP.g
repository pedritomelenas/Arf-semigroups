#####################################################
#F BoundForConductorOfGoodSemigroupsContainig:=function(vs)
## vs is a set of vectors
## The ouput is a bound (if there exists) for the conductor of a good semigroup containing vs
## (Based on Prop 11 "Embedding Dimension of a Good Semigroup of N^2")
#####################################################

BoundForConductorOfGoodSemigroupsContainig:=function(vs)
    local n,i,j,trvs,tent,conductor,alpha,m,c,delta,lambda,a, v, Scala;
    
    n:=Length(vs[1]);
    
    #The element in the of the input set of vector has to be the same length.
    if not(IsRectangularTable(vs)) then
      Error("The input must be a list of vectors (lists)");
    fi;

    #The semigroup has to be a subset of N^{n}.
    if not(ForAll(Union(vs), IsPosInt)) then
      Error("The vectors must have positive integer coordinates");
    fi;

    #On each component the Gcd of the elements has to be 1 (First Hypothesis of the Prop)
    trvs:=TransposedMat(vs);
    if not(ForAll(trvs, v-> Gcd(v)=1)) then
    Error("The gcd of the coordinates must be 1 for all coordinates (infinite decreasing chain)");
    fi;
    
    #Not all the elements can have the same couple of component equal (Second Hypothesis of the Prop)
    #Ex: (3,5,7,5),(2,9,8,9),(5,7,2,7) is not an ammissible set.
    if not(ForAll(Filtered(Cartesian([1..n],[1..n]),i->i[1]<i[2]), i->ForAny(vs, g-> g[i[1]]<>g[i[2]]))) then
      Error("There is not such an Arf good semigroup (infinite decreasing chain)");
    fi;

  #This function returns the conductors of the projections (with the convention that the conductor of N is 1)
  conductor:=function(l)
      if 1 in l then
        return 1;
      fi;
      return Conductor(NumericalSemigroup(l));
    end;


  #This function returns a couple of vectors that satisfy the claim of the Prop 
  tent:=function(vs,ind,ind1)
        local g,i,j,h,v1,u1,q1,q2,p1,indices,indices2,p,j1,j2;

        #Case of two-branches
        if Length(ind)=2 then
          #OPTIMIZED CHOICE
          g:=StructuralCopy(First(vs,i->i[ind[1]]<>i[ind[2]]));
          h:=StructuralCopy(First(vs,i->i[ind[2]]*g[ind[1]]<>i[ind[1]]*g[ind[2]]));
          for i in [1..Length(vs)] do
            for j in [i+1..Length(vs)] do
              if Lcm(vs[i][ind1],vs[j][ind1])<Lcm(g[ind1],h[ind1]) and vs[i][ind[1]]*vs[j][ind[2]]<>vs[i][ind[2]]*vs[j][ind[1]] then
                g:=StructuralCopy(vs[i]);
                h:=StructuralCopy(vs[j]);
              fi;
            od;
          od;
          # g:=First(vs,i->i[ind[1]]<>i[ind[2]]);
          # h:=First(vs,i->i[ind[2]]*g[ind[1]]<>i[ind[1]]*g[ind[2]]);
            
          #If g and h have the ind1 component equal, will be returned the couple (g,h) ordered respect the different component. 
          if g[ind1]=h[ind1] then
            return Set([g,h]);
            
            
            #If g and h have not the ind1 component equal we build from g and h a couple of vector in the 
            #semigroup with ind1 component equal, will be returned the couple (v1,u1) ordered respect the different component.
          else
            v1:=h*Lcm(h[ind1],g[ind1])/h[ind1];
            u1:=g*Lcm(h[ind1],g[ind1])/g[ind1];
            return Set([v1,u1]);
          fi;            
        fi;

        #if lenght(ind) is greater then 2
        j1:=First([1..Length(ind)],i->ind[i]<>ind1);
        j2:=First([1..Length(ind)],i->ind[i]<>ind1 and ind[i]<>j1);
    
        indices:=Concatenation(ind{[1..j1-1]},ind{[j1+1..Length(ind)]});
        p:=tent(vs,indices,ind1);
          
        if p[1][ind[j1]]<p[2][ind[j1]]  then
          return [p[1],p[2]];
        else 
          if p[1][ind[j1]]>p[2][ind[j1]] then
            q1:=List([1..Length(p[1])],i->Minimum(2*p[1][i],2*p[2][i]));
            q2:=List([1..Length(p[1])],i->p[1][i]+p[2][i]);
            return [q1,q2];
        
          else indices2:=Concatenation(ind{[1..j2-1]},ind{[j2+1..Length(ind)]});
            p1:=tent(vs,indices2,ind1);
            if p1[1][ind[j2]]<p1[2][ind[j2]]  then
              return [p1[1],p1[2]];
            else 
              if p1[1][ind[j2]]>p1[2][ind[j2]] then
                q1:=List([1..Length(p1[1])],i->Minimum(2*p1[1][i],2*p1[2][i]));
                q2:=List([1..Length(p1[1])],i->p1[1][i]+p1[2][i]);
                return [q1,q2];
              else
                v1:=List([1..Length(p1[1])],i->p[1][i]+p1[1][i]);
                u1:=List([1..Length(p1[1])],i->p[2][i]+p1[2][i]);
                return [v1,u1];
              fi;
            fi;
          fi;
        fi;
    end;

  #Computation of the list List of alpha_i
  alpha:=List([1..n],i->tent(vs,[1..n],i)[1]);
  #Computation ofthe list of m
  m:=List([1..n],i->alpha[i][i]);
  #Computation of c(i)
  c:=List(trvs,j1->conductor(j1));
  #Computation of the list of delta^(i)
  delta:=List([1..n],k->List(List([1..n],i->List([c[i]..c[i]+m[i]-1],j->
    FactorizationsIntegerWRTList(j,List(vs,j1->j1[i]))[1]))[k],i1->Sum([1..Length(i1)],j3->vs[j3]*i1[j3])));
  
  #Computation of the list of lambda^(0)
  lambda:=List([1..n],i->0);
  for i in [1..n] do
    a:=StructuralCopy(delta[i][1]);
    for j in delta[i] do
      a:=List([1..n],j1->Minimum(a[j1],j[j1]));
    od;
  lambda[i]:=StructuralCopy(a);
  od;


  #We have the bound of the conductor, obtained adding the Elements of the list lambda+alpha
  v:=Sum([1..n],k->(lambda+alpha)[k]);
  if n>2 then 
    return v;
  fi;
  Scala:=function(S,v,k)
    local U,T;
    U:=List([1..2],j->Filtered([1..Length(S)],i->S[i][j]<>infinity));
      T:=List([1..2],j->List(U[j],i->S[i][j]));
    return Filtered(List(FactorizationsIntegerWRTList(v[k]-1,T[k]),j->Sum(List([1..Length(j)],i->j[i]*S[U[k][i]]))),l-> l[3-k]>=v[3-k])<>[];
  end;
  while Filtered([1..2],i->Scala(S,v,i)=true)<>[] do
    v[Filtered([1..2],i->Scala(S,v,i)=true)[1]]:=v[Filtered([1..2],i->Scala(S,v,i)=true)[1]]-1;
  od;
  return v;

end;
    
#####################################################
#F BoundCond2:=function(S)
## S is a set of vectors of N^2
## The ouput is a bound (if there exists) for the conductor of a good semigroup containing S
#####################################################
 Scala:=function(S,v,k)
    local U,T;
    U:=List([1..2],j->Filtered([1..Length(S)],i->S[i][j]<>infinity));
      T:=List([1..2],j->List(U[j],i->S[i][j]));
    return Filtered(List(FactorizationsIntegerWRTList(v[k]-1,T[k]),
    j->Sum(List([1..Length(j)],i->j[i]*S[U[k][i]]))),
    l-> l[3-k]>=v[3-k])<>[];
  end;

BoundCond2:=function(S)
  local v,Scala;
  Scala:=function(S,v,k)
    local U,T;
    U:=List([1..2],j->Filtered([1..Length(S)],i->S[i][j]<>infinity));
      T:=List([1..2],j->List(U[j],i->S[i][j]));
    return Filtered(List(FactorizationsIntegerWRTList(v[k]-1,T[k]),j->Sum(List([1..Length(j)],i->j[i]*S[U[k][i]]))),l-> l[3-k]>=v[3-k])<>[];
  end;
  v:=BoundForConductorOfGoodSemigroupsContainig(S);
  while Filtered([1..2],i->Scala(S,v,i)=true)<>[] do
    v[Filtered([1..2],i->Scala(S,v,i)=true)[1]]:=v[Filtered([1..2],i->Scala(S,v,i)=true)[1]]-1;
  od;
  return v;
end;

