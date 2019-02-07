#####################################################
#F MinimumGS:=function(v,w)
## v and w are two vectors of the same length, the output is min(v,w)
#####################################################

MinimumGS:=function(v,w)
  return List([1..Length(v)],i->Minimum(v[i],w[i]));
end;





#####################################################
#F CompareGS:=function(v,w)
## v and w are two vectors of the same length, the output is true if v<=w, false otherwise
#####################################################

CompareGS:=function(v,w)
    return ForAll([1..Length(v)], i->v[i]<=w[i]);
end;





#####################################################
#F BoundForConductorOfGoodSemigroupsContainig:=function(vs)
## vs is a set of vectors
## The ouput is a bound (if there exists) for the conductor of a good semigroup containing vs
## (Based on Prop 11 "Embedding Dimension of a Good Semigroup")
#####################################################

BoundForConductorOfGoodSemigroupsContaining:=function(vs)
    local n,i,j,trvs,tent,conductor,alpha,m,c,delta,lambda,a,bound,Scale,Scalecond;
    
    n:=Length(vs[1]);
    
    #The element in the of the input set of vector has to be the same length.
    if not(IsRectangularTable(vs)) then
      #Error("The input must be a list of vectors (lists)");
      return fail;
    fi;

    #The semigroup has to be a subset of N^{n}.
    if not(ForAll(Union(vs), IsPosInt)) then
      #Error("The vectors must have positive integer coordinates");
      return fail;
    fi;

    #On each component the Gcd of the elements has to be 1 (First Hypothesis of the Prop)
    trvs:=TransposedMat(vs);
    if not(ForAll(trvs, v-> Gcd(v)=1)) then 
      #Error("The gcd of the coordinates must be 1 for all coordinates (infinite decreasing chain)");
       return fail; 
    fi;
    
    #Not all the elements can have the same couple of component equal (Second Hypothesis of the Prop)
    #Ex: (3,5,7,5),(2,9,8,9),(5,7,2,7) is not an ammissible set.
    if not(ForAll(Filtered(Cartesian([1..n],[1..n]),i->i[1]<i[2]), i->ForAny(vs, g-> g[i[1]]<>g[i[2]]))) then
      #Error("There is not such an Arf good semigroup (infinite decreasing chain)");
      return fail;
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

  #We can compute the bound of the conductor, adding the elements of the lists lambda+alpha.
  bound:=Sum([1..n],k->(lambda+alpha)[k]);


  #In case of more branches the function return this bound
  if n>2 then 
    return bound;
  fi;


  #Refining of the Bound in Case of Good Semigroup of N^2


  #The function Scale take in input the set of vector vs, the previous bound and the component k.
  #It returns true if the bound can be refined of the component k, otherwise it returns false.

  Scale:=function(S,bound,k)
      local U,T;

      U:=List([1..2],j->Filtered([1..Length(S)],i->S[i][j]<>infinity));
      T:=List([1..2],j->List(U[j],i->S[i][j]));
      
      return ForAny(List(FactorizationsIntegerWRTList(bound[k]-1,T[k]),j
                ->Sum(List([1..Length(j)],i->j[i]*S[U[k][i]]))),l-> l[3-k]>=bound[3-k]);
    
    end;

  #Now we check in which components it is possible to refine the conductor and we update the 
  #bound decreasing the component where is it possible to refine.
  Scalecond:=Filtered([1..2],i->Scale(vs,bound,i));
  while Scalecond<>[] do
  if Length(Scalecond)=2 then
  bound:=bound-1;
  else
  bound[Scalecond[1]]:=bound[Scalecond[1]]-1;
  fi;
  Scalecond:=Filtered([1..2],i->Scale(vs,bound,i));
  od;
  return bound;

end;
  




##########################################################
#An optimized function to compute the bound of the conductor in case of S subset of N^2
#It admits also element with infinite component
##########################################################



BoundForConductorOfGoodSemigroupsTwoContaining:=function(vs)
local Minimizza, BoundTemp, L,i,j;

#It is for vector of N^2, L is a set of vector with infinities, it creates a finite set of vector that
# can be used to compute BoundCond
Minimizza:=function(L)
  local ags,i,j,k,k1,i1,temp2,ind,L1,temp;

  ##NEED TO SET THIS AS MINIMUM
  
 # if ForAll(i->infinity in i) then
  #set a minimum, but i need check if have all infinities on a component
  #t1:=First(L,j->)
  #t2:=
  #ags:=[];
  #else
  #ags:[];
  #fi;
 
 ags:=[];
 
  #Building of a new sect of vector "ags"

  for i in L do
  #For all i, we create the list of the element which are not comparable with i
  k:=Filtered(L,j->i<>j and (not CompareGS(i,j) and (not CompareGS(j,i))));
  
  #we add to ags all the infimums of these incomparable elements
    for j in k do 
    ags:=Union(ags,[MinimumGS(i,j)]); 
    od;

  #we add to ags all the element without infinities
    if not infinity in i then
    ags:=Union(ags,[i]);

  #Here we treat the element that have infinity components, building  as infimum, an element under (or on the left)
  #the infinity which have to stay in the semigroup. 
    else     
    ind:=First([1,2],k1->i[k1]=infinity);
    temp2:=First(ags,k1->k1[3-ind]<>infinity); 
      if temp2<>fail then 
      ags:=Union(ags,[MinimumGS(i,CeilingOfRational(i[3-ind]/temp2[3-ind])*temp2)]); 
      fi;  
    fi;
  od;

i:=1;
k:=fail; 


while k=fail and i<=Length(ags) do 
k:=BoundForConductorOfGoodSemigroupsContaining(ags{[1..i]}); 
i:=i+1;
od;

if k=fail then
return fail; 

else
L1:=Filtered(L,j->infinity in j);

for i1 in L1 do
temp:=ShallowCopy(i1);
if temp[1]=infinity then 
temp[1]:=k[1]; 
ags:=Union(ags,[temp]); 
else
temp[2]:=k[2];  
ags:=Union(ags,[temp]);
fi;
od;

return ags;
fi;
end;

#It is as the last part of the first one, is a function of refining, it could be defined outide?
BoundTemp:=function(S,bound)
local Scale, Scalecond;

    Scale:=function(S,bound,k)
      local U,T;

      U:=List([1..2],j->Filtered([1..Length(S)],i->S[i][j]<>infinity));
      T:=List([1..2],j->List(U[j],i->S[i][j]));
      
      return ForAny(List(FactorizationsIntegerWRTList(bound[k]-1,T[k]),j
                ->Sum(List([1..Length(j)],i->j[i]*S[U[k][i]]))),l-> l[3-k]>=bound[3-k]);
    
    end;

  Scalecond:=Filtered([1..2],i->Scale(vs,bound,i));
  while Scalecond<>[] do
  if Length(Scalecond)=2 then
  bound:=bound-1;
  else
  bound[Scalecond[1]]:=bound[Scalecond[1]]-1;
  fi;
  Scalecond:=Filtered([1..2],i->Scale(vs,bound,i));
  od;
  return bound;

end;


L:=Minimizza(vs);
#L:=a;
if L=fail then 
return fail;

else
i:=1;
k:=fail;
  while k=fail and i<=Length(L) do 
  k:=BoundForConductorOfGoodSemigroupsContaining(L{[1..i]}); 
  i:=i+1;
  od;
    
  if k=fail then
  return fail;
  else
    for j in [i+1..Length(L)] do
    k1:=BoundTemp(L{[1..j]},k); 
    k:=k1; 
    od;
    return k;
  fi; 
fi;
end;


















