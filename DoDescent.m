//=================================================
// Apply 2-descent to each of the curves X_{E_i} to 
// compute the ranks of their Jacobians and also a
// system of generators of J(Q) up to finite index
//=================================================

load "ModelsXE.m";
load "TwoDescent.m";


R<x,y,z> := PolynomialRing(Rationals(), 3);


"===== X_{E_1} =====";

XE1 := ModelXE(E1);
f1 := DefiningEquation(XE1);

/*
Change model to one that is easier for the descent procedure to handle
*/
M := Matrix(Rationals(),3,3,[1,0,1/3,-2,3,-10/3,0,0,-1/3]);
N := M^(-1);
f1 := 9*Evaluate(f1, [&+[N[i][j]*R.j : j in [1..3]] : i in [1..3] ]);

FakeSelmer1, A1, XA, GA, gen1 := TwoDescentPlaneQuartic(f1 : ReturnKernel := true);


"===== X_{E_2} =====";
XE2 := ModelXE(E2);
f2 := DefiningEquation(XE2);

FakeSelmer2, A2, XA, GA, gen2 := TwoDescentPlaneQuartic(f2 : ReturnKernel := true);

/*
The bound shows that the rank is at most 2. We now check that D1 = (1 : 1 : 0) - (0 : 1 : 0) has non-trivial image in the fake Selmer group we just computed, and conclude that the rank is precisely two. Moreover, we also obtain that gen2 and D1 generate J(Q)/2J(Q).
*/

P1 := XA![1,1,0];
P2 := XA![0,1,0];
D1 := Divisor(P1)-Divisor(P2);
FF<u,v> := FunctionField(XA);

/*
Since the divisor (P1)-(P2) is not disjoint from the divisor of the function g, we move it in its equivalence class to make it so.
*/

D1 := D1 - Divisor( (v-1) / (u-2) );
D1 := D1 - Divisor( u/v - 1 );

gA := Evaluate(GA, [u,v,1]);

/*
Compute (a simplified representative for) the image of [D_1] in the fake Selmer group.
*/
res :=  EvaluateRationalFunctionOnGaloisOrbitDivisor(gA, D1);
res := SimplifyInAquot(res);

/*
We check that the image of [D_1] in the fake Selmer group is non-trivial, and in fact equivalent to the unique
non-trivial element of the fake Selmer group previously computed
*/
assert not AreEquivalentModuloSquaresAndRationals(A2!1, res);
assert AreEquivalentModuloSquaresAndRationals(FakeSelmer2[2], res);




"===== X_{E_4} =====";
XE4 := ModelXE(E4);
f4 := DefiningEquation(XE4);

FakeSelmer4, A4, XA, GA, gen4 := TwoDescentPlaneQuartic(f4 : ReturnKernel := true);

/*
The bound shows that the rank is at most 2. We now check that D1 = (0 : 0 : 1) - (0 : 1 : 0) has non-trivial image in the fake Selmer group we just computed, and conclude that the rank is precisely two. Moreover, we also obtain that gen4 and D1 generate J(Q)/2J(Q).
*/

P1 := XA![0,0,1];
P2 := XA![0,1,0];
D1 := Divisor(P1)-Divisor(P2);
FF<u,v> := FunctionField(XA);

/*
Since the divisor (P1)-(P2) is not disjoint from the divisor of the function g, we move it in its equivalence class to make it so.
*/
D1 := D1 - Divisor( u/v + 2/3 );
D1 := D1 - Divisor( v/u );

gA := Evaluate(GA, [u,v,1]);

/*
Compute (a simplified representative for) the image of [D_1] in the fake Selmer group.
*/
res :=  EvaluateRationalFunctionOnGaloisOrbitDivisor(gA, D1);
res := SimplifyInAquot(res);

/*
We check that the image of [D_1] in the fake Selmer group is non-trivial, and in fact equal to the unique
non-trivial element of the Selmer group previously computed
*/
assert not AreEquivalentModuloSquaresAndRationals(A4!1, res);
assert AreEquivalentModuloSquaresAndRationals(FakeSelmer4[2], res);





"===== X_{E_3} =====";
XE3 := ModelXE(E3);
f3 := DefiningEquation(XE3);

f3 := Evaluate(f3, [x, z, y]);
XE3 := Curve(ProjectiveSpace(Parent(f3)), [f3]);

FakeSelmer3, A3, XA, GA, gen3 := TwoDescentPlaneQuartic(f3 : ReturnKernel := true);


print "Algebra A_3:", A3;
print "Fake 2-Selmer group for X_{E_3}:", FakeSelmer3;
print "Generator of kernel J(Q)/2J(Q) --> Sel^2_{fake}:", gen3;


FF<u,v> := FunctionField(XA);
gA := Evaluate(GA, [u,v,1]);

P0 := XA![0, 1, 0];
P1 := XA![1, 1, 1];
P2 := XA![2, 1, 0];
P3 := XA![-1, 1, 0];

D1 := Divisor(P1) - Divisor(P0);
D2 := Divisor(P2) - Divisor(P0);
D3 := Divisor(P3) - Divisor(P0);

D2lindisj := D2 + Divisor( u-2 );
D2lindisj := D2lindisj + 2*Divisor( u/v+1 );

D3lindisj := D3 - Divisor( u/v+1 );

/*
We take two rational points on J(Q) and check that their images
in the fake 2-Selmer groups are non-trivial and distinct. This
implies that the image of J(Q)/2J(Q) --> Sel^2_{fake} has rank
at least two, hence J(Q)/2J(Q) has rank at least (hence exactly)
three
*/

res1 :=  EvaluateRationalFunctionOnGaloisOrbitDivisor(gA, D1);
res1 := SimplifyInAquot(res1);

DD := Divisor(u/v);
Q := Support(DD)[3];
D4 := Q - 2*Divisor(P0);
res4 :=  EvaluateRationalFunctionOnGaloisOrbitDivisor(gA, D4);
res4 := SimplifyInAquot(res4);

/*
Check that the elements we built are non-trivial and distinct
*/
assert not AreEquivalentModuloSquaresAndRationals(A3!1, res1);
assert not AreEquivalentModuloSquaresAndRationals(A3!1, res1);
assert not AreEquivalentModuloSquaresAndRationals(res1, res4);



/*
Various other tests, as sanity checks

res5 := EvaluateRationalFunctionOnGaloisOrbitDivisor(gA, D3lindisj+D4);
res5 := SimplifyInAquot(res5);
AreEquivalentModuloSquaresAndRationals(FakeSelmer3[4], res5);

res2 :=  EvaluateRationalFunctionOnGaloisOrbitDivisor(gA, D2lindisj);
res2 := SimplifyInAquot(res2);

AreEquivalentModuloSquaresAndRationals(FakeSelmer3[1], res2);
AreEquivalentModuloSquaresAndRationals(FakeSelmer3[2], res2);
AreEquivalentModuloSquaresAndRationals(FakeSelmer3[3], res2);
AreEquivalentModuloSquaresAndRationals(FakeSelmer3[4], res2);


res3 :=  EvaluateRationalFunctionOnGaloisOrbitDivisor(gA, D3lindisj);
res3 := SimplifyInAquot(res3);

AreEquivalentModuloSquaresAndRationals(FakeSelmer3[1], res3);
AreEquivalentModuloSquaresAndRationals(FakeSelmer3[2], res3);
AreEquivalentModuloSquaresAndRationals(FakeSelmer3[3], res3);
AreEquivalentModuloSquaresAndRationals(FakeSelmer3[4], res3);


IsPrincipal(0*D1 + 3*D2 + 6*D3 + (-2)*gen3);
IsPrincipal((-3)*D1 + 0*D2 + 3*D3 + 2*D4);
*/

