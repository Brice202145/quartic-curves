P2<x,y,z> := ProjectiveSpace(Rationals(),2);
f:=x^3*z - 2*x^2*y^2 - 4*x^2*z^2 + x*z^3 + y^4 + 2*y^2*z^2;
C:= Curve(P2,[f]);
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
         //print "P", P;        
	 P := Inverse(m3)(P);	
         fp:= P @@ m2;
         preimageofp:=fp @@ m1;
        RationalPoints_on_C:=Points(preimageofp);
	// print RationalPoints_on_C;
	for K in Fields do 
		SK := ChangeRing(preimageofp, K);
		ptsK := Points(SK);
		if #ptsK gt #RationalPoints_on_C then
					CK := ChangeRing(C, K);	
			print K, ptsK;
			
		end if;
	end for;
        end if;
        end for;
