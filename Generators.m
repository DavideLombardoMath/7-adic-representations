//===================================================
// Generators for finite-index subgroups of Jac(X_{E_i})(Q)
//===================================================

/*
In this file we hard-code generators of subgroups of finite index of
Jac(X_{E_i})(Q) for i=1, 2, 4. The companion file VerifyGenerators.m
checks that these degree-0 divisors do in fact generate a finite-index
subgroup of Jac(X_{E_i})(Q), by comparing them to the generators found
by 2-descent
*/

load "ModelsXE.m";
load "DivisorReduction.m";
load "Saturation.m";

//===================================================
// X_{E_1}
//===================================================

f1 := DefiningPolynomial(XE1);
R := Parent(f1);
x := R.1;
y := R.2;
z := R.3;


/*
Change model to that used during 2-descent
*/
M := Matrix(Rationals(),3,3,[1,0,1/3,-2,3,-10/3,0,0,-1/3]);
N := M^(-1);
f1 := 9*Evaluate(f1, [&+[N[i][j]*R.j : j in [1..3]] : i in [1..3] ]);

XE1_alternativemodel := Curve(ProjectiveSpace(R),f1);


/*
Define the generator
*/
XE1_D := Divisor(XE1_alternativemodel, ideal<R | [ x^2 - y*z, x*y - 21*x*z + 7*z^2, x*z + 1/7*y^2 - 3*y*z ]>) - 3*Divisor(XE1_alternativemodel![0,1,0]);


//===================================================
// X_{E_2}
//===================================================

f2 := DefiningPolynomial(XE2);
R := Parent(f2);
x := R.1;
y := R.2;
z := R.3;

/*
Define the generators
*/
I := ideal< R | [x^2 - 23/10*x*z + 3/5*y*z + 9/2*z^2, x*y + 9/5*x*z - 9/10*y*z - 12/5*z^2, x*z + 10/13*y^2 + 72/13*y*z + 79/13*z^2]>;
XE2_D1 := Divisor(XE2, I) - 3 * Divisor(XE2![0,1,0]);
XE2_D2 := Divisor(XE2![1,1,0]) - Divisor(XE2![0,1,0]);


//===================================================
// X_{E_4}
//===================================================

f4 := DefiningPolynomial(XE4);
R := Parent(f4);
x := R.1;
y := R.2;
z := R.3;

/*
Define the generators
*/
I := ideal< R | [    x^2 - 5488564319/12563367825*x*z - 610119053/12563367825*y*z + 437059948/12563367825*z^2,
    x*y - 19859147126/4187789275*x*z + 698544013/4187789275*y*z + 6710499692/4187789275*z^2,
    x*z + 4187789275/206392408638*y^2 - 15771228472/103196204319*y*z - 2661152096/7938169563*z^2]>;
XE4_D1 := Divisor(XE4, I) - 3 * Divisor(XE4![0,1,0]);
XE4_D2 := Divisor(XE4![0,0,1]) - Divisor(XE4![0,1,0]);

/*
Returns the above generators for (finite index subgroups of) J(X_{E_i})(Q).
*/
function RetrieveGenerators(i)
	if i eq 1 then
		return [XE1_D];
	end if;
	if i eq 2 then
		return [XE2_D1, XE2_D2];
	end if;
	if i eq 4 then
		return [XE4_D1, XE4_D2];
	end if;

	error "Index not in 1, 2, 4";
end function;