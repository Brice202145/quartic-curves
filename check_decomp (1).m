H := IntegralModel(HyperellipticCurve(8*x^6 + 4*x^5 - 16*x^4 - 26*x^3 + 18*x + 12));
JH := Jacobian(H);
P2<x,y,z> := ProjectiveSpace(Rationals(), 2);
f:=2*x^4 - 4*x^3*z - 3*x^2*y^2 + 7*x^2*z^2 + x*y^2*z + 4*x*z^3 + y^4 + 2*y^2*z^2 - 5*z^4;
C := Curve(P2, f);
sigma := iso<C->C | [x,-y,z], [x,-y,z]>;
D := CurveQuotient(AutomorphismGroup(C,[sigma]));
E := Jacobian(D);
H1 :=  QuadraticTwist(H, -1);
// Claim: JC is isogenous to E x JH. If this is true, then for all good
  // primes p, the zeta functions of the reductions factor as 
  // Zeta(C) = Zeta(E)*Zeta(H)
p := 1;
while p lt 50 do
  p +:= 1;
  try
    ZC := Numerator(ZetaFunction(ChangeRing(C, GF(p))));
    ZH := Numerator(ZetaFunction(ChangeRing(H, GF(p))));
    ZH1 := Numerator(ZetaFunction(ChangeRing(H1, GF(p))));
    ZE := Numerator(ZetaFunction(ChangeRing(E, GF(p))));
    "Zeta_E divides Zeta_C", IsDivisibleBy(ZC, ZE);
    "Zeta_H divides Zeta_C", IsDivisibleBy(ZC, ZH);
    "Zeta_H1 divides Zeta_C", IsDivisibleBy(ZC, ZH1);
    "p", p;
    //Factorisation(ZC); ZH, ZE;
    //ZC - ZH*ZE;
  catch e;

  end try;
end while;
   
 // So it looks like we need H1, not H
"rank of H1", RankBounds(Jacobian(H1)); 
