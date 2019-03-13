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
  local i,Small1,Small2;
  #We order the elements of the good semigroups putting the conductor as last small element.
  Small1:=SmallElementsOfGoodSemigroup(S1);
  Small2:=SmallElementsOfGoodSemigroup(S2);
  #We start comparing the conductors, if the conductor of S2 it is not smaller than the conductor of S1 the answer is certainly false.
  #Otherwise we check if all the elements of S1 stay in S2.
  if CompareGS(Conductor(S2),Conductor(S1)) then
  return ForAll(Small1, i->MinimumGS(i,Conductor(S2)) in Small2);
  fi;
  return false;
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
  local SemiringGeneratedByNaive,AddVectors,ScaleCond,S,i;


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

  #####################################################
  #F AddVectors:=function(vs,u)
  ## vs is a set of vector that identify a semiring, u is a generic set of vector
  ## The ouput is the semiring generated by vs and u (this function is faster than apply SemiringGeneratedByNaive on Union(vs,u))
  #####################################################

  AddVectors:=function(vs,u)
      local ClosureRespectSumAndMinimimuminUnion,ags,agsc,u1,cond,condS,temp;

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
        temp:=ScaleCond(agsc,temp);
      od;
      return Filtered(agsc,i->CompareGS(i,condS[1]));
  end;




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
### EDIM(S)
###
###################################################################################################################################



#####################################################
#F ALLtrack:=function(S)
## S is a good semigroup of N^2
## The ouput is the set of all tracks of S
#####################################################

AllTrack:=function(S)
  local I,RemoveLabels,GluePieceOfTrack,ComputePieceOfTrack,T,temp;

  #It glue a new piece of track to an existing track. T is the list of all piece of track. V is a list of two elements, V[1]
  #represents not complete tracks and V[2] the complete tracks.
  #The function add a new piece to the incomplete tracks and returns the updated V.
  GluePieceOfTrack:=function(T,V)
    local ags,temp,i,j;
    ags:=[[],[]];
    ags[2]:=ShallowCopy(V[2]);
    for i in V[1] do
      temp:=i[Length(i)];
      if temp="last" then
        ags[2]:=Union(ags[2],[i]);
      else
        for j in Filtered(T,k->k[1]=temp) do
          ags[1]:=Union(ags[1],[Concatenation(i,[j[2]])]);
        od;
      fi;
    od;
    return ags;
  end;

  #This funcion compute all possibles piece of track of a good semigroups having irriducible absolutes I
  ComputePieceOfTrack:=function(I)
    local IsAPOT,MaximalRed,ags,first,last,i;

    #It check if between two irreducible absolutes there is a piece of track. It check if  their minimum overcome
    #the maximum  in both direction or is equal to this one in entrambe le direzioni o coincide
    IsAPOT:=function(a,b)
        local min;
        if CompareGS(a[1],b[1]) or CompareGS(b[1],a[1]) then return false; else if a[1][1]>b[1][1] then return false; else

        min:=MinimumGS(a[1],b[1]); return min[2]>=a[3] and min[1]>=b[2];
        fi; fi;
    end;

    #Se (x,y) è irr assoluto ritorna (x1,y1), dove (x,y1) è il più grande irr assoluto sotto (x,y) e (x1,y) il più grande irr assoluto
    #a sinistra di (x,y).
    MaximalRed:=function(v,I)
      local Factorize,ind,temp,temp2,temp3;

      Factorize:=function(n,l)
          local a,b,ags,i,c,j,a1;

          if l=[] then
            return [];

          else
            a1:=Filtered([1..Length(l)],i->l[i]<>infinity);
            a:=List(a1,k->l[k]);
            b:=FactorizationsIntegerWRTList(n,a);
            ags:=[];
              for i in b do
                c:=List([1..Length(l)],o->0);
                j:=1;
                while j<=Length(a1) do
                  c[a1[j]]:=i[j]; j:=j+1;
                od;
                ags:=Union(ags,[c]);
              od;
            return ags;
          fi;

      end;

      if not v in I then
      return [0,0];

      else
        if infinity in v then
        temp3:=[0,0];
        ind:=First([1,2],i->v[i]<>infinity);
        temp3[3-ind]:=0;
        temp:=Filtered(I,i->i[ind]<v[ind]);
        temp2:=List(List(Factorize(v[ind],List(temp,i->i[ind])),j->Sum(List([1..Length(j)],k->j[k]*temp[k]))),k1->k1[3-ind]);

          if temp2=[] then
          temp3[ind]:=0;
          return Reversed(temp3);

          else
          temp3[ind]:=Maximum(temp2);
          return Reversed(temp3);
          fi;
        else
        temp3:=[0,0];

          for ind in [1,2] do
          temp:=Filtered(I,i->i[ind]<v[ind]);
          temp2:=List(List(Factorize(v[ind],List(temp,i->i[ind])),j->Sum(List([1..Length(j)],k->j[k]*temp[k]))),k1->k1[3-ind]);

            if temp2=[] then
            temp3[ind]:=0;
            else
            temp3[ind]:=Maximum(temp2);
            fi;
          od;
        return Reversed(temp3);
        fi;
      fi;
    end;


    #Se (x,y) è irr assoluto ritorna ((x,y),x1,y1), dove (x,y1) è il più grande irr assoluto sotto (x,y) e (x1,y) il più grande irr assoluto
    #a sinistra di (x,y).
    I:=List(I,i->Concatenation([i],MaximalRed(i,I)));

    #Aggiungiamo tutti i pezzi di tragitto
    ags:=List(Filtered(Cartesian(I,I),i->IsAPOT(i[1],i[2])),k->[k[1][1],k[2][1]]);

    #Aggiungiamo i punti di inizio e fine
    first:=Filtered(I,i->i[2]=0);
    last:=Filtered(I,i->i[3]=0);

    for i in first do
    ags:=Union(ags,[["first",i[1]]]);
    od;

    for i in last do
    ags:=Union(ags,[[i[1],"last"]]);
    od;

    return ags;
  end;

  #This function removes the label "first" and "last" in the tracks.
  RemoveLabels:=function(T)
    return List(T,i->Filtered(i,j->j<>"last" and j<>"first"));
  end;

  I:=IrriducibleAbsolutesofSemiring(S);
  T:=ComputePieceOfTrack(I);

  #The idea is create the list of all tracks, adding one by one the piece of tracks in all possible way, reccalling
  #GluePieceOfTrack until all possible track are completed (V[1]=[])
  temp:=[[["first"]],[]];
  temp:=GluePieceOfTrack(T,temp);

  while temp[1]<>[] do
  temp:=GluePieceOfTrack(T,temp);
  od;

  return RemoveLabels(temp[2]);

end;


#####################################################
#F ComputeMHS:=function(S)
## S is a good semigroup of N^2
## The ouput is the list of all Minimal Hitting Set of S
#####################################################

ComputeMHS:=function(S)
  local I,AllTrackInt,HittingSetsFromTrack;

  #This function takes the irriducible absolutes I of the good semigroup S and changes them in numbers
  #to increase the speed of the algorithm
  AllTrackInt:=function(S,I)
    local T,ChangeIrrInInt;

    #This function takes a list of irriducible absolutes and changes the elements of the list in numbers according to
    #their positions.
    ChangeIrrInInt:=function(T,v)
      local IntVert;
      #In internal function that given an irriducible absolute v assigns to it, the number of this position in the list T
      IntVert:=function(T,v)
        if not v in T then
        return fail;

        else
        return First([1..Length(T)],i->T[i]=v);
        fi;
      end;
      return List(v,j->IntVert(T,j));
    end;

    T:=AllTrack(S);
    return List(T,i->ChangeIrrInInt(I,i));
  end;

  #An algorithm that, given the list of all tracks T, of a good semigroup, compute all MHS
  HittingSetsFromTrack:=function(T)
    local m,D,i,j,k,ConcatenationWithoutRepetitions;

    #A function similar to concatenation but without repetition, we don't use "union" because it is faster
    ConcatenationWithoutRepetitions:=function(L)
      local i,ags,ConcatenationOfTwoListsWithoutRepetitions;

      ConcatenationOfTwoListsWithoutRepetitions:=function(S,T)
        local U,i;
        U:=ShallowCopy(S);
        for i in T do
          if not i in U then
          U:=Concatenation(U,[i]);
          fi;
        od;
        return U;
      end;

      ags:=[];
      for i in [1..Length(L)] do
        ags:=ConcatenationOfTwoListsWithoutRepetitions(ags,L[i]);
      od;
      return ags;
    end;

    m:=Length(T);
    D:=List([1..m+1],i->[[]]);

    for i in [2..m+1] do
      D[i]:=[];
      for j in D[i-1] do
        if Intersection(j,T[i-1])<>[] then
          Append(D[i],[j]);
        else
        Append(D[i],ConcatenationWithoutRepetitions(List(Filtered(T[i-1],k1->Filtered(D[i-1],i1->i1<>j and
        IsSubset(Concatenation(j,[k1]),i1))=[]),k->[Concatenation(j,[k])])));
        fi;
      od;
    od;

    return D[m+1];
  end;

  I:=IrriducibleAbsolutesofSemiring(S);
  return List(HittingSetsFromTrack(AllTrackInt(S,I)),i->I{i});
end;

ComputebEdimOfAGoodSemigroup:=function(S)
  local MHS;
  MHS:=ComputeMHS(S);
  SortBy(MHS,i->Length(i));
  return Length(MHS[1]);
end;

ComputeEdimOfAGoodSemigroup:=function(S)
  local MHS,stop,L,bedim,n,I,h,vr,H1;
  MHS:=ComputeMHS(S);
  bedim:=ComputebEdimOfAGoodSemigroup(S);
  I:=IrriducibleAbsolutesofSemiring(S);
  n:=bedim;
  H:=Filtered(MHS,i->Length(i)=n);
  while n<>Length(I) do

    vr:=VerifyReducibility(S,H);
    if vr<>fail then
      return [n,vr];
    fi;

    else
      
      for h in H do
        if(IsThereAMGSContainedInAndContaining(S,h)=false) then 
        return h;
        fi;
      od;

    n:=n+1;

    #Update H
    H1:=[];
    for h in H do
      for j in Difference(I,h)
        H1:=Concatenation(H1,Concatenation(h,j))
      od;
    od;
    H:=Union(H1,Filtered(MHS,i->Length(i)=n));

  od;
end;


#Verify Reducibility deve ritornare fail o un sor
testalista3:=function(S,L)
  local I;
  I:=IrriducibleAbsolutesofSemiring(S);
  return  Filtered(L,i->not VerifyConditionOfReducibility(S,i,I));
end;

#It checks if a set H satisfy the condition of reducibility (I_A(S)\subseteq red(H))
VerifyConditionOfReducibility:=function(S,H,I)
  local ClosureRespectReducibility;

  #It computes Red(H) (old Scartabili7)
  ClosureRespectReducibility:=function(S,H,I)
    local H1,temp;
    #We search the first irriducible absolute that is reducible by H
    temp:=First(I,i-> check4(H,i,S,I)); 
    if temp<> fail then
      H1:=Union(H,[temp]); 
    else
      H1:=H; 
    fi;
    #We consider the "closure" of H respect the reducibility
    while H<>H1 do
      H:=H1;
      temp:=First(I,i-> check4(H,i,S,I)); 

      if temp<> fail then 
        H1:=Union(H,[temp]); 
      else
        H1:=H; 
      fi; 
    od;
    return H1 ;
  end;

  return IsSubset(ClosureRespectReducibility(S,H,I),I);
end;



condi23:=function(S,H)
  local condi;

  condi:=function(S,v)
  local cond,condu,k,maximal,maximal2,maxi;
  maximal:=function(S,v,k)
   local U,T,w,i;
   U:=List([1..2],j->Filtered([1..Length(S)],i->S[i][j]<>infinity));
     T:=List([1..2],j->List(U[j],i->S[i][j]));
   return maxi(List(List(FactorizationsIntegerWRTList(v,T[k]),j->Sum(List([1..Length(j)],i->j[i]*S[U[k][i]]))),l1->l1[3-k]));;
  end;
   maximal2:=function(S,v,k)
    local U,T,w,i;
   U:=List([1..2],j->Filtered([1..Length(S)],i->S[i][j]<>infinity));
     T:=List([1..2],j->List(U[j],i->S[i][j]));
   return maxi(List(Filtered(List(FactorizationsIntegerWRTList(v,T[k]),j->Sum(List([1..Length(j)],i->j[i]*S[U[k][i]]))),l-> not infinity in l),l1->l1[3-k]));
   end;
   maxi:=function(l)
   if l=[] then return 0;
   else return Maximum(l); fi;
   end;
  condu:=StructuralCopy(S[Length(S)]);
  if not infinity in v then return List([1..2],k->maxi(Filtered(List(Filtered(S,i->i<>v and i[k]=v[k]),j->j[3-k]),j1->Filtered(S,j2->j2[3-k]=j1 and j2[k]>v[k])<>[]))); else
    k:=First([1..2],i->v[i]=infinity);
  cond:=StructuralCopy(S[Length(S)]);
  #cond[k]:=Maximum(Filtered(List(Filtered(S,i->i[3-k]=Minimum(v[3-k],condu[3k])),j->j[k]),k1->k1<cond[k]));
  cond[3-k]:=v[3-k];
  while MinimumGS(cond,condu) in S do
    cond[k]:=cond[k]-1;
  od;
    return cond[k]+1; fi;
  end;
  return List(H,j->condi(S,j));
end;

maxi:=function(l)
     if l=[] then return 0;
     else return Maximum(l); fi;
end;

massimo2:=function(S,v,cond)
        local U,T,w,i;
        U:=List([1..2],j->Filtered([1..Length(S)],i->S[i][j]<>infinity));
          T:=List([1..2],j->List(U[j],i->S[i][j]));
          w:=List(v,i->0);
          if infinity in v then
            k:=Filtered([1..2],i->v[i]<>infinity)[1];

          #a:=Filtered(List(List(List(Filtered(List(FactorizationsIntegerWRTList(v[k],T[k]),j->Sum(List([1..Length(j)],i->j[i]*S[U[k][i]]))),l-> not infinity in l),l1->l1[3-k]),l2->List(FactorizationsIntegerWRTList(l2,T[3-k]),j->Sum(List([1..Length(j)],i->j[i]*S[U[3-k][i]])))),l3->Maximum(List(l3,l4->l4[k]))),l5->l5>v[k]) <>[];
          w[k]:=maxi(List(Filtered(List(FactorizationsIntegerWRTList(v[k],T[k]),j->Sum(List([1..Length(j)],i->j[i]*S[U[k][i]]))),l-> not infinity in l),l1->l1[3-k]));

       else
        # a:= Union(List([1..2],k->Filtered(Union(List(Filtered(List(FactorizationsIntegerWRTList(v[k],T[k]),j->Sum(List([1..Length(j)],i->j[i]*S[U[k][i]]))),l1->l1[3-k]<v[3-k]),l2->List(FactorizationsIntegerWRTList(l2[3-k],T[3-k]),j->Sum(List([1..Length(j)],i->j[i]*S[U[3-k][i]]))))),l3->l3[k]>v[k])))<>[];

        w:=List([1..2],k->maxi(List(Filtered(List(FactorizationsIntegerWRTList(v[k],T[k]),j->Sum(List([1..Length(j)],i->j[i]*S[U[k][i]]))),l1->l1[3-k]<v[3-k]),l5->l5[3-k])));
         fi;

         return w;
end;
#S=eta,W=s
Controllare4:=function(v,W,S,I)
  local a,k,cond,m,a3;

  cond:=condi23(W,I);
  m:=massimo2(S,v,cond);

  if not infinity  in  v then
    a:=List([1..2],i->[]);
    a3:=Filtered([1..2],k->m[k]<>0);
    for k in a3 do
      a[k]:=Filtered([m[k]+1..v[3-k]-1],i->Filtered(W,j->j[3-k]=i and j[k]=v[k])<>[]);
    od;
  else
    k:=Filtered([1..2],i->v[i]<>infinity)[1];
    if m[k]=0 then 
      a:=[];
    else
      a:=Filtered([m[k]+1..cond[IndPos(I,v)]-1],i->Filtered(W,j-> j[3-k]=i and j[k]=Minimum(W[Length(W)][k],v[k]))<>[]);
    fi;
  fi;
  return a;
end;

check4:=function(S,v,W,H)
  local U,T,cond,m,k,i,a,a3,i1,j1,min,a4,a5,b,i3,temp;
  #local U,T
  #If the element stays in H (it is reducible by definition, it returns "false")
  if v in S then 
    return false; 
  else
    #If H contains only infinities the function returns "false"
    if ForAll(S,i->infinity in i) then 
      return false; 

    else
      #U is a list of two elements. In the i-th elements there is the list of the positions of the elements which have the i-th
      #coordinate differents from infinity. In T the position are substituted with the corrispective elements.
      # Example: H:=[[ 14, 7 ], [ 19, 6 ], [ 22, infinity ]];
      # U:=List([1..2],j->Filtered([1..Length(H)],i->H[i][j]<>infinity)); [ [ 1, 2, 3 ], [ 1, 2 ] ];

      U:=List([1..2],j->Filtered([1..Length(S)],i->S[i][j]<>infinity));
      T:=List([1..2],j->List(U[j],i->S[i][j]));

      #For all irreducible absolutes it returns a list with[M_U(alpha),M_R(alpha)] if it is finite and \tilde{y} if it is infinite.
      #If someone of these does not exists it returns 0

      cond:=condi23(W,H);

      #It computes [u(v),r(v)] (or only one of them in the infinite case)
      m:=massimo2(S,v,cond);

      #Finite Case
      if not infinity in v then
        #Here we compute all the elements in H that stay in H over u(v) and r(v) in this order (it is a list of two lists)  
        a4:=List([1..2],k->Filtered(List(FactorizationsIntegerWRTList(m[k],T[3-k]),
        j->Sum(List([1..Length(j)],i->j[i]*S[U[3-k][i]]))),l3->l3[k]>=v[k]));
        #It return the index for which we have u(v) and something over in H.
        a3:=Filtered([1..2],k->v[k] in List(a4[k],j->j[k]) and Length(Set(a4[k]))>1);
        #It trasforms a3 in a boolean vector (true if not empty)
        a:=List([1..2],i-> i in a3);

        if a3=[] then
          return false;
        else
          b:=Controllare4(v,W,S,H);
          a5:=Set(List(a3,i->[Length(b[i]),i]));
          a5:=Concatenation(a5,[[1,2]]);
          i1:=1;
          while a[a5[i1][2]] and i1<=Length(a3) do 
            a4:=b[a5[i1][2]];
            i3:=1;
              while a[a5[i1][2]] and i3<=Length(a4) do 
                a[a5[i1][2]]:=
                a[a5[i1][2]] and Filtered(List(FactorizationsIntegerWRTList(a4[i3],T[3-a5[i1][2]]),
                j->Sum(List([1..Length(j)],i->j[i]*S[U[3-a5[i1][2]][i]]))),l3->l3[a5[i1][2]]>v[a5[i1][2]])<>[];
                i3:=i3+1;
              od;
            i1:=i1+1; 
          od;
        fi;
      
      a:=Filtered(a,i->i)<>[];
      else
        k:=Filtered([1..2],i->v[i]<>infinity)[1];
        a3:=Filtered(List(FactorizationsIntegerWRTList(m[k],T[3-k]),
        j->Sum(List([1..Length(j)],i->j[i]*S[U[3-k][i]]))),l3->l3[k]>=v[k]);
        a:=v[k] in List(a3,j->j[k]) and Length(Set(a3))>1;
        if not a then 
          return a; 
        else 
          j1:=1; 
          a3:=Controllare4(v,W,S,H); 
          
          while a and j1<=Length(a3) do
            a:=a and Filtered(List(FactorizationsIntegerWRTList(a3[j1],T[3-k]),j->Sum(List([1..Length(j)],
            i->j[i]*S[U[3-k][i]]))),l3->l3[k]>v[k])<>[]; j1:=j1+1;
          od;

          min:=Minimum(List(S,i->i[3-k]));
          temp:=Maximum(cond[IndPos(H,v)],massimo2(S,v,cond)[k]);
          #temp:=massimo2(H,v,cond)[k];
          i1:=temp;

          while a and i1<=temp+min-1 do
            a:=a and Filtered(List(FactorizationsIntegerWRTList(i1,T[3-k]),
            j->Sum(List([1..Length(j)],i->j[i]*S[U[3-k][i]]))),l3->l3[k]>v[k])<>[];
            i1:=i1+1; 
          od;

        fi;
      fi;
      return a; 
    fi; 
  fi;
end;


Scartabili112:=function(W,S,cond,Abso,I)
  local H1,H,k,k1;

  H:=StructuralCopy(S);
  #We check if the condition I_A(S)\subseteq H is satisfied.
   if IsSubset(S,I) then 
    return S; 
   
   else
    k:=1; 
    k1:=Riducibilita23(W,H,Abso[k],cond,Abso); 
    while k<Length(Abso) and k1=[] do 
      k:=k+1; 
      k1:=Riducibilita23(W,H,Abso[k],cond,Abso); 
    od; 
    if k1<> []  then 
      H1:=Union(H,k1); 
    else
      H1:=H; 
    fi;
    while H<>H1 and not IsSubset(H1,I) do
      H:=H1;   
      k:=1; 
      k1:=Riducibilita23(W,H,Abso[k],cond,Abso); 
      
      while k<Length(Abso) and k1=[] do 
        k:=k+1; k1:=Riducibilita23(W,H,Abso[k],cond,Abso); 
      od; 
      if k1<> []  then H1:=Union(H,k1); else
      H1:=H; fi; od;

    return H1 ; fi;
end;


Riducibilita12:=function(W,S,v)
  local ind,temp,temp21,temp22,temp23,temp3;

  if infinity in v then
    temp3:=[0,0];
    ind:=First([1,2],i->v[i]<>infinity);
    temp3[3-ind]:=0;
    temp:=Filtered(S,i->IsInt(i[ind]) and i[ind]<=v[ind]);
  #   temp2:=List(List(Fattorizzazione(v[ind],List(temp,i->i[ind])),j->Sum(List([1..Length(j)],k->j[k]*temp[k]))),k1->k1[3-ind]);
  temp21:=List(Fattorizzazione(v[ind],List(temp,i->i[ind])),j->List([1..Length(j)],k->j[k]*temp[k])); if temp21=[] then temp3[ind]:=0; return temp3; else
  temp22:=List(List(temp21,j->Sum(FloatF(j))),k1->k1[3-ind]); if infinity in temp22 then temp3[ind]:=infinity; return temp3; else
  temp23:=List(List(temp21,j->Sum(j)),k1->k1[3-ind]); if Intero(Maximum(temp23))>Maximum(temp22) then

    temp3[ind]:=Maximum(temp23); else temp3[ind]:=Maximum(temp22); fi; fi; return temp3; fi; else
    temp3:=[0,0];
    for ind in [1,2] do
      temp:=Filtered(S,i->IsInt(i[ind]) and i[ind]<=v[ind]);
      temp21:=List(Fattorizzazione(v[ind],List(temp,i->i[ind])),j->List([1..Length(j)],k->j[k]*temp[k])); if temp21=[] then temp3[ind]:=0; return temp3; else
      temp22:=List(List(temp21,j->Sum(FloatF(j))),k1->k1[3-ind]); if infinity in temp22 then temp3[ind]:=infinity; else
      temp23:=List(List(temp21,j->Sum(j)),k1->k1[3-ind]); if Intero(Maximum(temp23))>Maximum(temp22) then

        temp3[ind]:=Maximum(temp23); else temp3[ind]:=Maximum(temp22); fi; fi;  fi;od; return temp3; fi;
end;

IndPos:=function(l,v)
  return First([1..Length(l)],i->l[i]=v);
end;

Riducibilita23:=function(W,S,v,cond,Abso)
  local W1,a,Substitution,v1,temp,temp2,temp3,ind,i1,k;

  Substitution:=function(v,i,new)
    local a;
    a:=ShallowCopy(v);
    a[i]:=new;
    return a;
  end;

  massimoIrr:=function(W,v,temp,ind,cond,Abso)
    if not infinity in v then
    return cond[IndPos(Abso,v)][ind];
    
    else
    return Maximum(temp[ind],cond[IndPos(Abso,v)][ind])+W[1][3-ind]-1; 
    fi;
  end;

  if v in S then 
    return []; 
  
  else
    W1:=Esteso(W);
    temp:= Riducibilita(W,S,v); 
    if v=Reversed(temp) then 
      return [v]; 
    else
      if temp=[0,0] then 
        return [];
      else
        temp2:=Filtered([1,2],j->temp[j]<>0 and temp[j]<>infinity);
        a:=[]; 
        i1:=1; 
        
        while  i1<=Length(temp2) do
          ind:=temp2[i1];
          temp3:=Filtered([temp[ind]..massimoIrr(W,v,temp,ind,cond,Abso)],k->MinimumGS(Substitution(v,3-ind,k),Reversed(W1)[1]) in W1);
          k:=1; 
          temp4:=Riducibilita12(W,S,Substitution(v,3-ind,temp3[k]))[3-ind]>v[ind];
          
            while temp4 and k<Length(temp3) do 
              k:=k+1;temp4:=Riducibilita12(W,S,Substitution(v,3-ind,temp3[k]))[3-ind]>v[ind];
            od;
          
          if temp4  
          then AddSet(a,v);
          else 
            if k<>1 and not Substitution(v,3-ind,temp3[k-1]) in S  then
              AddSet(a,Substitution(v,3-ind,temp3[k-1]));
            fi; 
          fi; 
          
          i1:=i1+1;
        od;
        return a; 
      fi;
    fi; 
  fi;
end;


###################################################################################################################################
###
### FOR VERIFY THIRD PROPERTY
###
###################################################################################################################################

#ThirdP:=function(A) internal function that, given a subset of N^2, finds the couple of vectors where the third property of the good semigroups is not satisfied
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









###################################################################################################################################
###
### MORE BRANCHES
###
###################################################################################################################################



ConductorOfAGoodSemigroupN:=function(W)
  Set(W);
  return Reversed(W)[1];
end;


IrreducibleAbsolutesofSemiringG:=function(W)
  local Substitution, ExtendedSmallElements, AbsolutesOfTheGoodSemigroupG,IrreduciblesOfTheGoodSemigroupG,TransformToInfGSN,W1,cond;
  Set(W);

  TransformToInfGSN:=function(v,c)
      local a,temp,i;
      a:=ShallowCopy(v);
      temp:=Filtered([1..Length(v)],i->v[i]=c[i]);
      for i in temp do
        a:=Substitution(a,i,infinity);
      od;
      return a;
  end;

  Substitution:=function(v,i,new)
    local a;
    a:=ShallowCopy(v);
    a[i]:=new;
    return a;
  end;

  ExtendedSmallElements:=function(W)
    local cond,S,i,j,k,inter;

    inter:=function(v,w)
      local ags,i,j,temp;
      if Length(v)=1 then
        ags:=[];
        for i in [v[1]..w[1]] do
          ags:=Union(ags,[[i]]);
        od;   else ags:=[];
          temp:=inter(v{[1..Length(v)-1]},w{[1..Length(v)-1]});
        for i in temp do
          for j in [v[Length(v)]..w[Length(v)]] do
            ags:=Union(ags,[Concatenation(i,[j])]);
          od;
        od;
      fi;
      return ags;
    end;

    cond:=Reversed(W)[1];
    S:=ShallowCopy(W);
    for k in [1..Length(cond)] do
      for i in Filtered(S,j->j[k]=cond[k]) do
        for j in [cond[k]+1..cond[k]+S[1][k]] do
          S:=Concatenation(S,[Substitution(i,k,j)]);
        od;
      od;
    od;
    #uno:=List([1..Length(cond)],i->1);
    return  Union(S,inter(Reversed(W)[1],Reversed(W)[1]+W[1]));
  end;

  AbsolutesOfTheGoodSemigroupG:=function(W1)
    local cond,IsAbsoluteOfTheGoodSemigroupN;

    IsAbsoluteOfTheGoodSemigroupN:=function(W,v)
      local ags,i,LessInDeltaN,LessOrEqualInDeltaN,MinimumGSList;




    return First([1..Length(v)],i->First(W,j1->j1<>v and v[i]=j1[i] and ForAll(Difference([1..Length(v)],[i]),
    k1->v[k1]<=j1[k1]))=fail)<>fail;
    end;

    #  W1:=ExtendedSmallElements(W);
    #  cond:=Reversed(W1)[1];
    #  W1:=List(W1,i->TransformToInfGSN(i,cond));
    return Filtered(W1,i-> IsAbsoluteOfTheGoodSemigroupN(W1,i));
  end;

  IrreduciblesOfTheGoodSemigroupG:=function(W1)
    local ags,i1,temp,cond,DifferenceGS;

    DifferenceGS:=function(v,w)
      local ags,i;
      ags:=[];
      for i in [1..Length(v)] do
        if v[i]=infinity and w[i]=infinity then
        ags:=Concatenation(ags,[infinity]);
        else
        ags:=Concatenation(ags,[v[i]-w[i]]);
        fi;
      od;
      return ags;
    end;

    ags:=[];
    for i1 in [1..Length(W1)] do
      temp:=W1[i1];
      if First([1..i1-1],j->DifferenceGS(temp,W1[j]) in W1)=fail then
        ags:=Concatenation(ags,[temp]);
      fi;
    od;
    return ags;
  end;
  W1:=ExtendedSmallElements(W);
  cond:=ConductorOfAGoodSemigroupN(W1);
  W1:=List(W1,i->TransformToInfGSN(i,cond));
  return   IrreduciblesOfTheGoodSemigroupG(AbsolutesOfTheGoodSemigroupG(W1));
end;
