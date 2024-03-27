/*
Computes zeros of vanishing differentials, the candidate rational points and test the  known rational points with the candidate rational points.

Inputs     - f: quartic f defining curve C: y^4-h(x)y^2+r(x)=0 where Degree(h):=2 and 
Degree(r)<=4
	   - p: prime at which to do Chabauty-Coleman method
	   - parameters: parameters for precision and ramification

outputs - List of the all rational points, if successful

Run CC method at prime p with precision N and ramification e.
*/
/* importer load"coleman.m";*/

load"coleman.m";
load"colemanextensions.m";
parameters := AssociativeArray();
parameters["height"] := 1000;
parameters["precision"] := 10;
parameters["precision_inc"] := 5;
parameters["e"] := 40;
parameters["e_inc"] := 20;
parameters["max_e"] := 500;
parameters["max_prec"] := 15;
function quartic_points(f, parameters)
    P2 := ProjectiveSpace(Rationals(),2);
    C := Curve(P2,[Numerator(Evaluate(f, [P2.1/P2.3, P2.2/P2.3])*P2.3^4)]);
    points := PointSearch(C, parameters["height"]);
    return  points;
end function;

function chabauty_quartic(f, g, p, parameters)
    prec := parameters["precision"];
    e := parameters["e"];
    precision_inc := parameters["precision_inc"];
    e_inc := parameters["e_inc"];
    finished := false;
    precs := [prec];
    e_vals := [e];
    while e + e_inc le parameters["max_e"] do
        e := e + e_inc;
        Append(~e_vals, e);
    end while;
    while prec + precision_inc le parameters["max_prec"] do
        prec := prec + precision_inc;
        Append(~precs, prec + precision_inc);
    end while;
    for prec in precs do
        data := coleman_data(f, p, prec);
        for e in e_vals do
         if Degree(g) eq 1 then
            Qpoints := Q_points(data, parameters["height"]);
             try
                    L,v := effective_chabauty(data:Qpoints:=Qpoints, e:=e);
                    chabauty_data := [*L, Qpoints, p, prec, e*];
                    point_coords := [Qpoints[i]`x : i in [1..#Qpoints]];
                    candidates := [L[i]`x : i in [1..#L]];
                    b_values := [L[i]`b : i in [1..#L]];
                    if  #point_coords eq #candidates then
                        return true, chabauty_data, #v,  [], [];
                  else
                        for xP in point_coords do
                        for a in candidates do
                        N := Min(Precision(xP),Precision(a));
                              if N gt 0 then
                                  x_point := ChangePrecision(xP,N);
                                  x_cand := ChangePrecision(a,N);
                                  if Integers()!x_point eq Integers()!x_cand then
                                     idx := Index(candidates, a);
                                     Remove(~candidates, idx);
                                     Remove(~b_values, idx);
                                  end if;
                             else
                                if Integers()!xP eq Integers()!a then
                                   idx := Index(candidates, a);
                                   Remove(~candidates, idx);
                                   Remove(~b_values, idx);
                              end if;
                        end if;
                  end for;
               end for;
            return chabauty_data, #v, candidates, b_values;
       end if;
                catch err
                    print(err`Object);
                end try;
                else
                Qpoints := Q_points(data, parameters["height"]); // supp(div(g)) not defined over Q
                Qdivs := Q_divs(data, parameters["height"], g);
                try
                    L,v := effective_chabauty_with_Qdiv(data:Qpoints:=Qdivs, e:=e);
                    chabauty_data := [*L, Qpoints, p, prec, e*];
                    return true, chabauty_data, #v;
                catch err
                    print(err`Object);
                end try;
            end if;
            
        end for;
    end for;
    return false, [];
  end function;  
