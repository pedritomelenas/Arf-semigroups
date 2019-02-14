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





##########################################################
#F IsContainedGS:=function(S1,S2)
## S1 and S2 are two good semigroups
## The ouput is "true" if S1 is contained in S2, false otherwise. 
##########################################################

IsContainedGS:=function(S1,S2)
  local i;
  #We order the elements of the good semigroups putting the conductor as last small element.
  Set(S1);
  Set(S2);
  #We start comparing the conductors, if the conductor of S2 it is not smaller than the conductor of S1 the answer is certainly false.
  #Otherwise we check if all the elements of S1 stay in S2.
  if CompareGS(S2[Length(S2)],S1[Length(S1)]) then
  return ForAll(S1, i->MinimumGS(i,S2[Length(S2)]) in S2); 
  fi;
  return false;
end;





#####################################################
#F BoundForConductorOfGoodSemigroupsContainig:=function(vs)
## vs is a set of vectors
## The ouput is a bound (if there exists) for the conductor of a good semigroup containing vs
## (Based on Prop 11 "Embedding Dimension of a Good Semigroup")
#####################################################

BoundForConductorOfGoodSemigroupsOfNdContaining:=function(vs)
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
#F BoundForConductorOfGoodSemigroupsOfNTwoContaining:=function(vs)
## vs is set of vectors of (N U {infinity})^2 (it admits also elements with infinite components).
## The ouput is a bound (if there exists) for the conductor of a good semigroup of N^2 containing vs
##########################################################

BoundForConductorOfGoodSemigroupsContaining:=function(vs)

  local BoundNaive,BoundRefine,FiniteSet,trvs,fvs,i,j,k,k1;



  ##########################################################
  #F BoundNaive:=function(vs)
  ## vs is set of vectors of N^2.
  ## The ouput is a non optimized bound (if there exists) for the conductor of a good semigroup of N^2 containing vs.
  ## Reference: Prop 11 "Embedding Dimension of a Good Semigroup"
  ##########################################################
  
  BoundNaive:=function(vs)
    local n,trvs,i,j,g,h,BuildAlpha,conductor,alpha,m,c,delta,lambda,a;

    n:=Length(vs[1]);
    
    #The element in the of the input set of vector has to be vectors of N^2.
    if not(IsRectangularTable(vs)) or n<>2 then
      #Error("The input must be a list of vectors of Lenght 2");
      return fail;
    fi;

    if not(ForAll(Union(vs), IsPosInt)) then
      #Error("The vectors must have positive integer components");
      return fail;
    fi;

    #On each component the Gcd of the elements has to be 1 (First Hypothesis of the Prop)
    trvs:=TransposedMat(vs);
    if not(ForAll(trvs, v-> Gcd(v)=1)) then 
      #Error("The gcd on each component must be 1");
       return fail; 
    fi;
    
    #Not all the elements can have the same couple of component equal (Second Hypothesis of the Prop)
    #Ex: (3,5,7,5),(2,9,8,9),(5,7,2,7) is not an ammissible set.
    if not(ForAll(Filtered(Cartesian([1..n],[1..n]),i->i[1]<i[2]), i->ForAny(vs, g-> g[i[1]]<>g[i[2]]))) then
      #Error("At least one element of the list must have different components");
      return fail;
    fi;

    
    #This function returns the conductors of the projections (with the convention that the conductor of N is 1)
    conductor:=function(l)
      if 1 in l then
        return 1;
      fi;
        return Conductor(NumericalSemigroup(l));
    end;


    #This function returns a couple of vectors that satisfy the Claim in the Proposition.
    BuildAlpha:=function(vs,ind)
        local g,i,j,h,v1,u1;

          #OPTIMIZED CHOICE (We build the two element that satisfy the condition as small as possible)
          g:=StructuralCopy(First(vs,i->i[1]<>i[2]));
          h:=StructuralCopy(First(vs,i->i[2]*g[1]<>i[1]*g[2]));
          for i in [1..Length(vs)] do
            for j in [i+1..Length(vs)] do
              if Lcm(vs[i][ind],vs[j][ind])<Lcm(g[ind],h[ind]) and vs[i][1]*vs[j][2]<>vs[i][2]*vs[j][1] then
                g:=StructuralCopy(vs[i]);
                h:=StructuralCopy(vs[j]);
              fi;
            od;
          od;
          
          #NAIVE CHOICHE
          # g:=First(vs,i->i[ind[1]]<>i[ind[2]]);
          # h:=First(vs,i->i[ind[2]]*g[ind[1]]<>i[ind[1]]*g[ind[2]]);
            
          #If g and h have the ind component equal, will be returned the couple (g,h) ordered respect the different component. 
          if g[ind]=h[ind] then
            return Set([g,h]);
          
          #If g and h have not the ind component equal we build from g and h a couple of vector in the 
          #semigroup with ind component equal, will be returned the couple (v1,u1) ordered respect the different component.
          else
            v1:=h*Lcm(h[ind],g[ind])/h[ind];
            u1:=g*Lcm(h[ind],g[ind])/g[ind];
            return Set([v1,u1]);
          fi;            
    end;

    #Computation of the list List of alpha_i
    alpha:=List([1..n],i->BuildAlpha(vs,i)[1]);

    #Computation of the list of m
    m:=List([1..n],i->alpha[i][i]);

    #Computation of c^(i)
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

    #We can compute the bound of the conductor, adding the elements of the lists lambda and alpha.
    return Sum([1..n],k->(lambda+alpha)[k]);
  end;


  ##########################################################
  #F BoundRefine:=function(vs)
  ## vs is a set of vectors of N^2, bound is a bound for the coductor of a good semigroup of N^2 containing the vector of vs.
  ## The ouput is an optimized bound for the conductor of a good semigroup of N^2 containing vs.
  ##########################################################
  
  BoundRefine:=function(vs,bound)
    local Scale, Scalecond;

    #The function Scale take in input the set of vector vs, the previous bound and the component that we want to refine.
    #It returns true if the bound can be refined of the component k, otherwise it returns false.
    Scale:=function(vs,bound,k)
      local U,T;

      U:=List([1..2],j->Filtered([1..Length(vs)],i->vs[i][j]<>infinity));
      T:=List([1..2],j->List(U[j],i->vs[i][j]));
      
      #Here we check if bound[k]-1 can be obtained as sum of element of vs, in this case the bound can be refined
      return ForAny(List(FactorizationsIntegerWRTList(bound[k]-1,T[k]),j
                ->Sum(List([1..Length(j)],i->j[i]*vs[U[k][i]]))),l-> l[3-k]>=bound[3-k]);
    
    end;

    #Now we apply Scale, updating the bound on the components where it is possible improve it.
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
  #F FiniteSet:=function(vs)
  ## vs is a set of vectors of (N U {infinity})^2
  ## The ouput is a set of vector of N^2 which contains the same good semigroups of vs and have the same bound for the conductor.
  ##########################################################

  FiniteSet:=function(vs)
    local m,fvs,i,j,k,i1,temp2,ind,L1,temp;


    #First of all we put in fvs a finite element(if exists) obtained from the element of vs (here we prefer take it not "too big")
    m:=Filtered(Cartesian([1..Length(vs)],[1..Length(vs)]),i->i[1]<i[2]);
    fvs:=[Minimum(List([1..Length(m)],i->MinimumGS(vs[m[i][1]],vs[m[i][2]])))];

    #Here we check if we found a finite element to add to fvs. If it not happens, it means that we have infinity
    #in all the elements on the same component, in this case it is not possible find a bound.
    if infinity in fvs[1] then
    #Error("The gcd on each component must be 1");
    return fail;
    fi;
    
    #We start to build the new set of vector "fvs".
    for i in vs do

      #We add to fvs all the finite elements.
      if not infinity in i then
      fvs:=Union(fvs,[i]);

      #Here we treat the element that have infinity components, building  as infimum, an element under (or on the left)
      #the infinity which have to stay in the semigroup. 
      else     
      ind:=First([1,2],k->i[k]=infinity);
      temp2:=First(fvs,k->k[3-ind]<>infinity); 
        if temp2<>fail then 
        fvs:=Union(fvs,[MinimumGS(i,CeilingOfRational(i[3-ind]/temp2[3-ind])*temp2)]); 
        fi;  
      fi;
    od;

    #Here we add the elements that corrispond to the infinities, with this strategy. We compute a bound for the conductor 
    #for the smallest set of fvs for which is possible (the previous step guarantees us that in fvs the projections)
    #and we change the infinitves on each component with the correspondent bound on the component
    i:=1;
    k:=fail; 
    SortBy(fvs, i -> i[1]+i[2]);

    while k=fail and i<=Length(fvs) do 
    k:=StructuralCopy(BoundNaive(fvs{[1..i]})); 
      if k<>fail then
      k:=StructuralCopy(BoundRefine(fvs{[1..i]},k));
      fi;
    i:=i+1;
    od;

    if k=fail then
    return fail; 

    else
    L1:=Filtered(vs,j->infinity in j);
      for i1 in L1 do
        temp:=ShallowCopy(i1);
        if temp[1]=infinity then 
        temp[1]:=k[1]; 
        fvs:=Union(fvs,[temp]); 
        else
        temp[2]:=k[2];  
        fvs:=Union(fvs,[temp]);
        fi;
      od;
    return fvs;
    fi;
  end;

  #First of all we transform vs in a set of finite vectors (if it is possible).
  fvs:=FiniteSet(vs);
  
  if fvs=fail then 
  return fail;
  
  #We compute a naive bound for the smallest subset of fsv and after we refine the bound adding the elements 
  #of fvs one by one. This is better then compute the refine bound directly on fvs, since in this way the Factorizations
  #in scala are "easier".
  else
  i:=1;
  k:=fail;
  
  while k=fail and i<=Length(fvs) do 
  k:=BoundNaive(fvs{[1..i]}); 
  i:=i+1;
  od;
    
  if k=fail then
  return fail;
  
  else
    for j in [i..Length(fvs)] do
    k1:=BoundRefine(fvs{[1..j]},k); 
    k:=k1; 
    od;
    return k;
  fi; 
  fi;
end;





#####################################################
#F IrriducibleAbsolutesofSemiring:=function(S)
## S is a good semigroup of N^2 given through its small elements
## The ouput is the set of its irreducible absolute points of the semiring \overline{S}
#####################################################

IrriducibleAbsolutesofSemiring:=function(S)
  local ElementsOnTheEdge,TransformToInf,c,Small,Irrabsf,Irrabsi,Infi,Edge,i;

  #This function check if an elements has a coordinate equal to the conductor
  ElementsOnTheEdge:=function(vs,c)
    return vs[1]=c[1] or vs[2]=c[2];
  end;

  #This function transforms the elements with a coordinate equal to the conductor in infinities
  TransformToInf:=function(vs,c)
    local a,i;
    a:=ShallowCopy(vs);
      for i in Filtered([1..2],j->vs[j]=c[j]) do
        a[i]:=infinity;
      od;
    return a;
  end;

  c:=Conductor(S);
  Small:=Difference(SmallElements(S),[[0,0]]);
  #Computation of finite irriducible absolutes
  Irrabsf:=IrreducibleMaximalElementsOfGoodSemigroup(S);


  #I take the elements of S different from the conductor but with a coordinate equal to this one.
  Edge:=Filtered(Small,k->k<>c and ElementsOnTheEdge(k,c));

  Infi:=[];
  #Here I add to ags the infinities in the square over the conductor (built considering the multiplicity)
  for i in [0..Small[1][1]-1] do
    Infi:=Union(Infi,[[c[1]+i,infinity]]); 
  od;

  for i in [0..Small[1][2]-1] do
    Infi:=Union(Infi,[[infinity,c[2]+i]]); 
  od;

  #Here we add to infinities under the conductor
  for i in Edge do
    Infi:=Union(Infi,[TransformToInf(i,c)]);
  od;

  #Computation of infinite irreducible absolutes
  Irrabsi:=Filtered(Infi,i->Filtered(Small,j->i-j in Infi)=[]);

  return  Union(Irrabsi,Irrabsf);
end;





#####################################################
#F SemiringGeneratedBy:=function(vs,cond)
## vs is a set of vector, cond is a couple [v1,v2]
## The ouput is the semiring generated by vs, with conductor cond
#####################################################  

SemiringGeneratedBy:=function(vs,cond)
  local SemiringGeneratedByNaive,AddVectors,Scalecond,S,i;

  #####################################################
  #F SemiringGeneratedByNaive:=function(vs,cond)
  ## vs is a set of vector, cond is a couple [v1,v2]
  ## The ouput is the semiring generated by vs, with conductor cond
  #####################################################

  SemiringGeneratedByNaive:=function(vs,cond)
    local Scalecond,ClosureRespectSumAndMinimimum,ags,agsc,temp;
    


    
    #This function add to vs, all the sums of two elements of vs, and all minimums of elements of vs under the conductor.
    ClosureRespectSumAndMinimimum:=function(vs,cond)
      local ags,i,j;
        ags:=ShallowCopy(vs);
        for i in [1..Length(ags)] do
          for j in [i..Length(ags)] do
            if not MinimumGS(ags[i]+ags[j],cond) in ags then 
            ags:=Concatenation(ags,[MinimumGS(ags[i]+ags[j],cond)]); 
            fi;
            if not MinimumGS(ags[i],ags[j]) in ags then 
            ags:=Concatenation(ags,[MinimumGS(ags[i],ags[j])]); 
            fi;
          od;
        od;
      return Set(ags);
    end;
            
    ags:=Union(ShallowCopy(vs),[cond]);
    agsc:=ClosureRespectSumAndMinimimum(ags,cond);

    while ags<>agsc do
      ags:=ShallowCopy(agsc);
      agsc:=ClosureRespectSumAndMinimimum(agsc,cond);
    od;

    temp:=[cond];
    while temp<>[] do
      cond:=ShallowCopy(temp);
      temp:=ScaleCond(agsc,temp);
    od;
    
    return Filtered(agsc,i->CompareGS(i,cond[1]));
  end;

  #####################################################
  #F AddVectors:=function(vs,u)
  ## vs is a set of vector that identify a semiring, u is a generic set of vector
  ## The ouput is the semiring generated by vs and u (this function is faster than apply SemiringGeneratedByNaive on Union(vs,u))
  #####################################################

  AddVectors:=function(vs,u)
    local ScaleCond,ClosureRespectSumAndMinimimuminUnion,ags,agsc,u1,cond,condS,temp;

    ClosureRespectSumAndMinimimuminUnion:=function(vs,u,cond)
        local ags,i,j,u1;
        ags:=ShallowCopy(vs);
          for i in ags do
            for j in u do
              if not MinimumGS(i+j,cond) in ags then
                ags:=Union(ags,[MinimumGS(i+j,cond)]);
              fi;
              if not MinimumGS(i,j) in ags then
                ags:=Union(ags,[MinimumGS(i,j)]);
              fi;
            od;
          od;
        return ags;
    end;

    ags:=ShallowCopy(Union(vs,u));
    condS:=vs[Length(vs)];
    agsc:=ClosureRespectSumAndMinimimuminUnion(ags,u,condS);
    while ags<>agsc do
      u1:=Filtered(agsc,i-> not i in ags);
      ags:=ShallowCopy(agsc);
      agsc:=ClosureRespectSumAndMinimimuminUnion(agsc,Union(u,u1),condS);
    od;
    temp:=[condS];    
    while temp<>[] do
      condS:=ShallowCopy(temp);
      temp:=path(agsc,temp);
    od;
    return Filtered(agsc,i->CompareGS(i,condS[1]));
  end;

  #This function starting to the greatest element of the list vs, produce the list of possible "real conductor" decreasing by one each component of the list cond.
  #Ex: If we have ...[35,35],[35,36],[36,34],[36,35],[36,36],[37,36]. With v:=[37,36], the function return the list [[36,35],[36,36]]. With v:=[[36,35],[36,36]]
  #it returns [[35,35],[35,36],[36,34]] and so on.

  ScaleCond:=function(vs,v)    
      local i,ags;
      ags:=[];
      for i in v do
      ags:=Union(ags,Filtered(vs,j->Sum(i)-1=Sum(j) and CompareGS(j,i)));
      od;
      return ags;
  end;

  S:=SemiringGeneratedByNaive([vs[1]],cond);
  for i in [2..Length(vs)] do
  S:=AddVectors(S,[vs[i]]);
  od;
  return S;
end;



############################################################################################################################################

#WORK IN PROGRESS...
############################################################################################################################################




















###################################################################################################################################
###
### FOR VERIFY THIRD PROPERTY
###
###################################################################################################################################

 #   ThirdP:=function(A) internal function that, given a subset of N^2, finds the couple of vectors where the third property of the good semigroups is not satisfied
  ThirdP:=function(A)
    local B,car,C,conductor,D,ind,ind2,F,k,i,screm;
      screm:=function(v)
      local a1,a2,i,k;
      k:=ShallowCopy(v);
      a1:=ShallowCopy(k[1][1]);
      a2:=ShallowCopy(k[1][2]);
      for i in [1..Length(a1)] do
        if i<>k[2] then a1[i]:=Minimum(a1[i],a2[i]); a2[i]:=Minimum(a1[i],a2[i]); fi; od;
      return [[a1,a2],k[2]];
      end;
  end;



###################################################################################################################################
###
### RANDOM FUNCTIONS
###
###################################################################################################################################
#Attenzione che può generare vettori uguali
RandomVectorsInteger:=function(n,L)
  local a;
  a:=List([1..n],i->[]);
  for i in [1..n] do
  a[i]:=List([1..Length(L)],i->Random(L[i]));
  od;
  return a;
end;
 

RandomGoodSemigroup:=function(m,cond)
  local S,b,temp;

  n:=Random([1..m[1]+m[2]-1]);
  L:=List([1..Length(cond)],i->[m[i]..cond[i]]);
  G:=Union(RandomVectorsInteger(n,L),[m]);
  S:=Good5(G,cond);
  temp:=ThirdP(S);
  while temp<>[] do
  S:=AddVectors(S,[RandomList(poss(Inverti(temp)[1],S))]);
  temp:=ThirdP(S);
  od;
  return S;
end;


RandomCandidati:=function(W)
  local S,cond,ags,a;
    S:=IrrAbs(W);
    cond:=condi2(W);
    #ags1:=Filtered(S,i->not 0 in massimo(S,i,cond) and not (conf(massimo2(S,i,cond),massimo(S,i,cond)) and #conf(massimo(S,i,cond),massimo2(S,i,cond)) ));
    #for i in ags1 do
    #ags1:=Union(ags1,Filtered(S,j->j[3-k]=massimo(S,i,cond)[k]));
    #S1:=Union(S1,Filtered(S,j-> j[k]=massimo(S,i,cond)[3-k]));
    ags:=[Essenziali(W)];
  a:=[Length(ags[1])..Minimum(Sum(W[1]),Length(S))];
  return RandomList(Candidati2(W,RandomList(a)));
end;

RandomCandidati2:=function(W)
  local S,cond,ags,a;
    S:=IrrAbs(W);
    cond:=condi2(W);
    #ags1:=Filtered(S,i->not 0 in massimo(S,i,cond) and not (conf(massimo2(S,i,cond),massimo(S,i,cond)) and #conf(massimo(S,i,cond),massimo2(S,i,cond)) ));
    #for i in ags1 do
    #ags1:=Union(ags1,Filtered(S,j->j[3-k]=massimo(S,i,cond)[k]));
    #S1:=Union(S1,Filtered(S,j-> j[k]=massimo(S,i,cond)[3-k]));
    ags:=[Essenziali(W)];
  a:=[Length(ags[1])..Minimum(Sum(W[1]),Length(S))];
  return RandomList(Candidati2(W,RandomList([CeilingOfRational((a[1]+a[Length(a)])/2)..a[Length(a)]])));
end;

RandomGen:=function(s)
    local m,n,a,b,coeff,degree,i,j;
  #  m:=RandomList([1..5]);
  m:=1;
    if m <0 then m:=m*(-1); fi;
      m:=m+1;
    n:=RandomList([1..5]);

      if n <0 then n:=n*(-1); fi;
        n:=n+2;

        a:=List([1..n],a->0);
        for i in [1..n] do
          b:=List([1..m],j->0);
          for j in [1..m] do
            degree:=RandomList([5..100]);  if degree<0 then degree:=degree*(-1); fi; degree:=degree+1;
            coeff:= List([1..degree+1],i->RandomList([RandomList([1..2]),0])*RandomList([RandomList([1..2]),0])); coeff[1]:=0;
  for k in [1..6] do coeff[k]:=0; od;
            u:=Indeterminate(Rationals,1);
          b[j]:=UnivariatePolynomial(Rationals,coeff,1)*u^(RandomList([RandomList([5..10]),0]));
        #b[j]:=UnivariatePolynomial(Rationals,coeff,1);
            if b[j]*2=b[j] then b[j]:=u^degree; fi;
          od;
          a[i]:=b;
        od;
    return a;
end;

Randomtest:=function(m,cond)
  local S,S1;
  Wtest:=RandomGoodSemigroup(m,cond);
  atest:=RandomCandidati(Wtest);
  temp:=BoundCond4(atest);
  if temp<>fail then
  S:=testa22(Wtest,atest,temp);
  else S:=testa22(Wtest,atest,Wtest[1]+Reversed(Wtest)[1]); fi;
  S1:=Intersection(List(S,i->IrrAbs(i)));
  return Intersection(S1,IrrAbs(Wtest))=Scartabili4(Wtest,atest);
  end;
  Essenziali:=function(W)
  local S;
  S:= List([1,2],i->Set(Esteso(W),j->j[i]));
  k:=List(S,i->MinimalGeneratingSystemOfNumericalSemigroup(NumericalSemigroupByGenerators(i)));
  return Filtered(IrrAbs(W),i->i[1] in k[1] and i[2] in k[2]);
end;

Randomtest2:=function(m,cond)
  local S,S1;
  Wtest:=RandomGoodSemigroup(m,cond);
  atest:=RandomCandidati(Wtest);


  S:=testa22(Wtest,atest,Wtest[1]+Reversed(Wtest)[1]);

  S1:=Intersection(List(S,i->IrrAbs(i)));
  return Intersection(S1,IrrAbs(Wtest))=Scartabili4(Wtest,atest);
end;