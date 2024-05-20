first_split_prime:=function(f, d)
  // returns first rational prime coprime to disc which splits completely
  // in  Q(sqrt(c)).
 

  L:=SplittingField(f);
  OL := MaximalOrder(L);
  p := 5;
  while not IsTotallySplit(p,OL) or (d mod p eq 0) do
      p := NextPrime(p);
  end while;
  return p;
end function;

function good_divisor(f)
    P2<x,y,z> := ProjectiveSpace(Rationals(),2);
    C := Curve(P2,[Numerator(Evaluate(Q, [P2.1/P2.3, P2.2/P2.3])*P2.3^4)]);
    phi := iso<C -> C | [x,-y, z],[x,-y, z]>;
G := AutomorphismGroup(C,[phi]);
D,m1 := CurveQuotient(G);
points:=RationalPoints(D: Bound:=1000);
F,m2:=EllipticCurve(D, points[1]);
E, m3 := MinimalModel(F);
Fields := [QuadraticField(d) : d in [-10,-8,-7,-6,-5,-3,-2,-1,2,3,5,7,10]];
ptsE:=RationalPoints(E: Bound:=1000);
for i in [2..#ptsE] do
     P:=ptsE[i];
     if Order(P) eq 0 then     
	 P := Inverse(m3)(P);	
         fp:= P @@ m2;
         preimageofp:=fp @@ m1;
        RationalPoints_on_C:=Points(preimageofp);
	for K in Fields do 
		SK := ChangeRing(preimageofp, K);
		ptsK := Points(SK);
		if #ptsK gt #RationalPoints_on_C then
		      CK := ChangeRing(C, K);
		      points_C:=ptsK;
  for P in points_C do
 if P[2] ne 0 and P[3] ne 0 then
  FC<xC,yC> := FunctionField(C);
  D := Divisor(Decomposition(Divisor(xC))[4][1]);
  pts := Points(C:Bound:=100);
  D0 := Divisor(pts[1]);
  DP := D-2*D0;
  return Decomposition(DP);
  end if;
  end for;	
		end if;
	end for;
        end if;
        end for;
  end function;
