function good_quartic(f)
/* This function takes as input a non-hyperelliptic curve of genus 3 given by C:f(x,y,z)=0 ,degr,ee(f):=4, 
 check whether the curve admits a non-trivial involution \phi:(x,y,z) to (x,-y,z).
 Returns the curve C if the quotient curve by C/<\phi> is an elliptic curve of rank 1 */

P2<x,y,z>:= ProjectiveSpace(Rationals(),2);
     C:= Curve(P2,[f]); 
     assert  # Points(C: Bound:=1000) ne 0;
     phi := iso<C -> C | [x,-y, z],[x,-y, z]>;
     G:= AutomorphismGroup(C);
     if #G eq 2 then
        G1:= AutomorphismGroup(C,[phi]);
         D,m1 := CurveQuotient(G);
         points:=RationalPoints(D: Bound:=1000);
         E,m:=EllipticCurve(D, points[1]);
         if RankBound(Jacobian(E)) eq 1 then
              return f, E;
           end if;
        end if;
end function;

function Hyperelliptic_polynomial(f)
/* This function takes as input the equation of the curve C which is of the form y^4-h(x,z)y^2+r(x,z)=0 where Degree(h):=2 and Degree(r):=4.
Return the affine quation of C and the polynomial defining the hyperelliptic curve H such that Jac(C)~Jac(E)xJac(H).*/
Q<x,y,z>:=PolynomialRing(Rationals(), 2);
T:=Terms(f,y);
     r,u :=Factorization(T[1]);
     h1:=Evaluate(T[3],[x,1,z]);
Coef:=Coefficients(h1);
 for i in [1..#Coef] do 
    v:=Coef[i] ;

 if v lt 0 then
      h:=-h1;
card_r:=#r;
     if card_r eq 1 then 
         f1:=u*r[1][1]; g1:=r[1][1];
     elif card_r eq 2 then 
          f1:=u*r[1][1]; g1:=r[2][1];
  
     elif  card_r eq 3 then 
          f1:=u*r[1][1]*r[2][1]; g1:=r[3][1];
   
     elif card_r eq 4 then
          f1:=u*r[1][1]*r[2][1]; g1:=r[3][1]*r[4][1];
        end if;
     if  Degree(f1) eq 2 and  Degree(g1)  eq 2  then
          fx := UnivariatePolynomial(Evaluate(f1, [x,0,1])); 
          gx:= UnivariatePolynomial(Evaluate(g1, [x,0,1])); 
          hx:= UnivariatePolynomial(Evaluate(h, [x,0,1]));
          A := Matrix(Rationals(),3,3,[Coefficient(fx,2),Coefficient(fx,1),Coefficient(fx,0),  Coefficient(hx,2),Coefficient(hx,1),Coefficient(hx,0),Coefficient(gx,2),Coefficient(gx,1),Coefficient(gx,0)]);
 if not IsSingular(A) then
              B:=A^ -1;
              a:=Polynomial([B[1,1], 2*B[2,1], B[3,1]],[1, x, x^2]);
              b:=Polynomial([B[1,2], 2*B[2,2], B[3,2]],[1, x, x^2]);
              c:=Polynomial([B[1,3], 2*B[2,3], B[3,3]],[1, x, x^2]);
              def_poly:=b*(b^2-a*c);
            Append(~L, [ Evaluate(f,[x,y,1]), def_poly]);

            end if;
       end if;
end if;
break i;
end for;
end for; 
