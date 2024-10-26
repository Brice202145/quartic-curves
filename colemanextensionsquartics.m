vanishing_differentials_div:=function(points,data:e:=1);

  // Compute the regular one forms of which the
  // integrals vanish between all points in points.
  // NEW:  points is a suuport if divisor D, then computes
  // integrals by integrating from base point to each
  // point in the suport of D and summing.
  // As written, the first point is the basepoint and should
  // be a rational pont (not a divisor).

  Q:=data`Q; p:=data`p;

  g:=genus(Q,p);

  IP1Pi:=[];
  NIP1Pi:=[];
  for i:=1 to #points-2 do
  if not points[1]`inf then
      P := set_point(points[1]`x,points[1]`b[2],data);
      x1 := points[i+1]`x;
      b := points[i+1]`b;
      Q1 := set_point(x1,b[2],data);
      Ci, Ni := coleman_integrals_on_basis(P,Q1,data:e:=e);
      xj := points[i+2]`x;
      b := points[i+2]`b;
      Q2 := set_point(xj,b[2],data);
      Cij, Nij := coleman_integrals_on_basis(P,Q2,data:e:=e);
      Ci := Ci + Cij;
      Ni := Minimum(Ni,Nij);
    else 
      P := set_bad_point(points[1]`x,points[1]`b,points[1]`inf,data); 
      x1 := points[i+1]`x;
      b := points[i+1]`b;
      Q1 := set_point(x1,b[2],data);
      Ci, Ni := coleman_integrals_on_basis(P,Q1,data:e:=e);
      xj := points[i+2]`x;
      b := points[i+2]`b;
      Q2 := set_point(xj,b[2],data);
      Cij, Nij := coleman_integrals_on_basis(P,Q2,data:e:=e);
      Ci := Ci + Cij;
      Ni := Minimum(Ni,Nij);
    end if;
    IP1Pi[i] := Ci;
    NIP1Pi[i] := Ni;
  end for;
  Nint:=Minimum(NIP1Pi);

  K:=pAdicField(p,Nint);
  M:=ZeroMatrix(K,g,#points-1);
  for i:=1 to g do
    for j:=1 to #points-2 do
      M[i,j]:=K!reduce_mod_pN_Q(Rationals()!IP1Pi[j][i],p,Nint);
    end for;
  end for;

  v:=basis_kernel(M);

  return v,IP1Pi,NIP1Pi;

end function;
effective_chabauty_div:=function(data:Qpoints:=[],bound:=0,e:=1);

  // Carries out effective Chabauty for the curve given by data.
  // First does a point search up to height bound. Then uses the
  // points found to determine the vanishing differentials. Finally
  // goes over all residue disks mapping to points on the reduction
  // mod p and finds all common zeros of the vanishing differentials.

  if #Qpoints eq 0 then
    if bound eq 0 then
      error "have to specify either Qpoints or a bound for search";
    end if;
    Qpoints:=Q_points(data,bound);
  end if;

  for i:=1 to #Qpoints do
    _,index:=local_data(Qpoints[i],data);
    data:=update_minpolys(data,Qpoints[i]`inf,index);
    if is_bad(Qpoints[i],data) then
      if is_very_bad(Qpoints[i],data) then
        xt,bt,index:=local_coord(Qpoints[i],tadicprec(data,e),data);
        Qpoints[i]`xt:=xt;
        Qpoints[i]`bt:=bt;
        Qpoints[i]`index:=index;
      end if;
    else
      xt,bt,index:=local_coord(Qpoints[i],tadicprec(data,1),data);
      Qpoints[i]`xt:=xt;
      Qpoints[i]`bt:=bt;
      Qpoints[i]`index:=index;
    end if;
  end for;

  v,IP1Pi,NIP1Pi:=vanishing_differentials_div(Qpoints,data:e:=e);

  Qppoints,data:=Qp_points(data:points:=Qpoints);
  for i:=1 to #Qppoints do
    if is_bad(Qppoints[i],data) then
      xt,bt,index:=local_coord(Qppoints[i],tadicprec(data,e),data);
    else
      xt,bt,index:=local_coord(Qppoints[i],tadicprec(data,1),data);
    end if;
    Qppoints[i]`xt:=xt;
    Qppoints[i]`bt:=bt;
    Qppoints[i]`index:=index;
  end for;

  pointlist:=[];
  for i:=1 to #Qppoints do
    k:=0;
    for j:=1 to #Qpoints do
      if (Qppoints[i]`x eq Qpoints[j]`x) and (Qppoints[i]`b eq Qpoints[j]`b) and (Qppoints[i]`inf eq Qpoints[j]`inf) then
        k:=j;
      end if;
    end for;
    if k lt 2 then
      pts:=zeros_on_disk(Qpoints[1],Qppoints[i],v,data:e:=e);
    else
      pts:=zeros_on_disk(Qpoints[1],Qppoints[i],v,data:e:=e,integral:=[*IP1Pi[1],NIP1Pi[1]*]);
    end if;
    for j:=1 to #pts do
      pointlist:=Append(pointlist,pts[j]);
    end for;
  end for;
  return pointlist, v;

end function;
// Compute all integrals against basis differentials
// from a point P1  to a
// points Q1 and Q2, such that the divisor D:=Q1+Q2-2P1 
function coleman_integrals_on_basis_to_div(P1, Q1,Q2, data:e:=1)
  if not P1`inf then
      P := set_point(P1`x,P1`b[2],data);
      x1 := Q1`x;
      b := Q1`b;
      Q1 := set_point(x1,b[2],data);
      Ci, Ni := coleman_integrals_on_basis(P,Q1,data:e:=e);
      xj :=Q2`x;
      b := Q2`b;
      Q2 := set_point(xj,b[2],data);
      Cij, Nij := coleman_integrals_on_basis(P,Q2,data:e:=e);
      Ci := Ci + Cij;
      Ni := Minimum(Ni,Nij);
    else 
      P := set_bad_point(P1`x,P1`b,P1`inf,data); 
      x1 :=Q1`x;
      b := Q1`b;
      Q1 := set_point(x1,b[2],data);
      Ci, Ni := coleman_integrals_on_basis(P,Q1,data:e:=e);
      xj := Q2`x;
      b := Q2`b;
      Q2 := set_point(xj,b[2],data);
      Cij, Nij := coleman_integrals_on_basis(P,Q2,data:e:=e);
      C := Ci + Cij;
      N := Minimum(Ni,Nij);
    end if;
    return C, N;
end function;
// decide if divisor D  is a torsion divisor using coleman integrals.

function is_torsion(data, e, support)
    if #support lt 2  then
        Qpoints := Q_points(data, 1000);
        for P in Qpoints do
            if P`inf then
                infty := P;
            else
                Q := P;
            end if;
        end for;
        ints := coleman_integrals_on_basis(infty, Q, data:e:=e);
    else
        Qpoints := support;
        for P in Qpoints do
            if P`inf then
                P1 := P;
            else 
                P1 := Qpoints[1];
            end if;
        end for;
        ints := coleman_integrals_on_basis_to_div(P1, Qpoints[2],Qpoints[3], data:e:=e);
    end if;
    g:=data`g;
    I:=ElementToSequence(ints);
    Ibasis := I[1..g];
    is_tor := IsZero(Ibasis);
    return is_tor;
end function;
