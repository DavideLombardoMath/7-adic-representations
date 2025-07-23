//===================================================
// We check that the points hard-coded in Generators.m
// generate a subgroup of J(Q) of the right rank
//===================================================

load "Generators.m";
load "ModelsXE.m";
load "TwoDescent.m"; 

//===================================================
// X_{E_1}
//===================================================

/*
We perform a 2-descent to retrieve a generator gen1 of J(Q)/2J(Q)
The 2-descent also shows that this F_2-vector space is 1-dimensional
*/

f1 := DefiningPolynomial(XE1_alternativemodel);
R := Parent(f1);
FakeSelmer1, A1, XA, GA, gen1 := TwoDescentPlaneQuartic(f1 : ReturnKernel := true);

/*
Convert gen1, which is formally a divisor over the field A_1, to a divisor over Q
*/
XE1 := PlaneCurve(f1);
IN := Ideal(Numerator(gen1));
IN := ChangeRing(IN, Rationals());
ID := Ideal(Denominator(gen1));
ID := ChangeRing(ID, Rationals());

INR := ideal<R | Generators(IN)>;
IDR := ideal<R | Generators(ID)>;

D1 := Divisor(XE1, INR) - Divisor(XE1, IDR);


/*
We construct an auxiliary degree-0 divisor D_aux
*/
FF<x,y> := FunctionField(XE1);
P0 := Divisor(XE1![0,1,0]);
P1 := [ P : P in Support(Divisor(x)) | Degree(P) eq 2 ];
D_aux := P1[1] - 2*P0;

/*
We check that 2D_1 \sim 3D_aux. This shows that D_1 is three times a
rational point in J(Q) \cong Z.
*/
assert IsPrincipal(2*D1 - 3*D_aux);

/*
Thus, there is a divisor D such that D_1 \sim 3*D and D_aux \sim 2*D
We compute a divisor D_3 linearly equivalent to D \sim D_1 - D_aux
that is of the simple form D' - 3*P_0. Also note that D_2 \in 2J(Q),
so D \sim D_1 + D_aux is equivalent to D_1 modulo 2J(Q), hence [D] is
a basis of J(Q)/2J(Q)
*/
T := D1 - D_aux + 3*Divisor(XE1![0,1,0]);
RRSpace, RRmap := RiemannRochSpace(T);
D3 := D1 - D_aux + Divisor(RRmap(RRSpace.1));

/*
The class [D_1] does not generate a saturated subgroup. In fact, it is three times D_3.
*/
assert IsLinearlyEquivalent(D1, 3*D3);

/*
We now compare D_3 \sim D_1 - D_aux with the generator hardcoded in Generators.m
*/

XE1_D1 := RetrieveGenerators(1)[1];

/*
Since D_3 and the XE1_D1 formally lie on different curves, we convert from one
to the other by going through the ideal defining XE1_D1
*/

IN := Ideal(Numerator(XE1_D1));
IN := ideal<R | Generators(IN)>;
ID := Ideal(Denominator(XE1_D1));
ID := ideal<R | Generators(ID)>;

XE1_D1 := Divisor(XE1, IN) - Divisor(XE1, ID);

assert D3 eq XE1_D1;






//===================================================
// X_{E_2}
//===================================================
load "ModelsXE.m";
f2 := DefiningPolynomial(XE2);
R := Parent(DefiningPolynomial(XE2));

/*
We perform a 2-descent to retrieve a generator gen2 of J(Q)/2J(Q)
The 2-descent also shows that this F_2-vector space is 2-dimensional,
with basis given by gen2 and D_2 = (P_1) - (P_0), see DoDescent.m
*/

FakeSelmer2, A2, XA, GA, gen2 := TwoDescentPlaneQuartic(f2 : ReturnKernel := true);

/*
Convert gen2, which is formally a divisor over the field A_2, to a divisor over Q
*/
XE2 := PlaneCurve(f2);
R := Parent(f2);

IN := Ideal(Numerator(gen2));
IN := ChangeRing(IN, Rationals());
ID := Ideal(Denominator(gen2));
ID := ChangeRing(ID, Rationals());

INR := ideal<R | Generators(IN)>;
IDR := ideal<R | Generators(ID)>;

D1 := Divisor(XE2, INR) - Divisor(XE2, IDR);


P0 := XE2![0,1,0];
P1 := XE2![1,1,0];
D2 := Divisor(P1) - Divisor(P0);

/*
It is not hard to show that <D_1, D_2> is not saturated.
We describe a set of generators of a slightly larger subgroup of J(Q).
*/

XE2FF<u,v> := FunctionField(XE2);
Q := [P : P in Support(Divisor(u*v-2)) | Degree(P) eq 2][1];
D_aux := Q - 2*Divisor(P0);

/*
We compute a divisor D_4 of the form D' - 3(P_0) that is linearly
equivalent to D_1 - 2*D_{aux}. Note that the class of D_4 in the
quotient J(Q)/2J(Q) is the same as the class of D_1, so <D_1, D_2>
and <D_4, D_2> both surject onto J(Q)/2J(Q), and therefore both
have finite index in J(Q).
*/
D3 := D1-2*D_aux;
RRspace, RRmap := RiemannRochSpace(D3 + 3*Divisor(P0));
f := RRmap(RRspace.1);
D4 := D3 + Divisor(f);


/*
We show that [D_1], [D_2] do not generate a saturated subgroup by expressing [D_1] in terms of [D_2], [D_4]: we have [D_1] = 3 * (2[D_2] - [D_4])
*/
assert IsLinearlyEquivalent(D1, 3*(2*D2 - D4));

/*
Finally, we compare these generators with those hard-coded in
Generators.m
*/

XE2_D1, XE2_D2 := Explode(RetrieveGenerators(2));

/*
These divisors formally lie on different curves, so we compare
them via their defining ideals
*/

IN := Ideal(Numerator(XE2_D1));
ID := Ideal(Denominator(XE2_D1));
IN := ideal<R | Generators(IN)>;
ID := ideal<R | Generators(ID)>;
XE2_D1 := Divisor(XE2, IN) - Divisor(XE2, ID);

assert D4 eq XE2_D1;

IN := Ideal(Numerator(XE2_D2));
ID := Ideal(Denominator(XE2_D2));
IN := ideal<R | Generators(IN)>;
ID := ideal<R | Generators(ID)>;
XE2_D2 := Divisor(XE2, IN) - Divisor(XE2, ID);

assert D2 eq XE2_D2;




//===================================================
// X_{E_4}
//===================================================
/*
We follow precisely the same steps as for X_{E_2}
*/

load "ModelsXE.m";
f4 := DefiningPolynomial(XE4);
R := Parent(DefiningPolynomial(XE4));

/*
We perform a 2-descent to retrieve a generator gen4 of J(Q)/2J(Q)
The 2-descent also shows that this F_2-vector space is 2-dimensional,
with basis given by gen4 and D_2 = (P_1) - (P_0), see DoDescent.m
*/

FakeSelmer4, A4, XA, GA, gen4 := TwoDescentPlaneQuartic(f4 : ReturnKernel := true);

/*
Convert gen4, which is formally a divisor over the field A_4, to a divisor over Q
*/
XE4 := PlaneCurve(f4);
R := Parent(f4);

IN := Ideal(Numerator(gen4));
IN := ChangeRing(IN, Rationals());
ID := Ideal(Denominator(gen4));
ID := ChangeRing(ID, Rationals());

INR := ideal<R | Generators(IN)>;
IDR := ideal<R | Generators(ID)>;

D1 := Divisor(XE4, INR) - Divisor(XE4, IDR);

P0 := XE4![0,1,0];
P1 := XE4![0,0,1];
D2 := Divisor(P1) - Divisor(P0);

/*
It is not hard to show that <D_1, D_2> is not saturated.
We describe a set of generators of a slightly larger subgroup of J(Q).
*/

XE4FF<u,v> := FunctionField(XE4);

Q := [P : P in Support(Divisor(u*v-1)) | Degree(P) eq 3][1];
D_aux := Q - 3*Divisor(P0);


/*
We compute a divisor D_4 of the form D' - 3(P_0) that is linearly
equivalent to D_1 - 2*D_{aux}. Note that the class of D_4 in the
quotient J(Q)/2J(Q) is the same as the class of D_1, so <D_1, D_2>
and <D_4, D_2> both surject onto J(Q)/2J(Q), and therefore both
have finite index in J(Q).
*/
D3 := D1-2*D_aux;
RRspace, RRmap := RiemannRochSpace(D3 + 3*Divisor(P0));
f := RRmap(RRspace.1);
D4 := D3 + Divisor(f);

/*
We show that [D_1], [D_2] do not generate a saturated subgroup by expressing [D_1] in terms of [D_2], [D_4]: we have [D_1] = -3 * [D_4]
*/
assert IsLinearlyEquivalent(D1, -3*D4);



/*
Finally, we compare these generators with those hard-coded in
Generators.m
*/

XE4_D1, XE4_D2 := Explode(RetrieveGenerators(4));

/*
These divisors formally lie on different curves, so we compare
them via their defining ideals
*/

IN := Ideal(Numerator(XE4_D1));
ID := Ideal(Denominator(XE4_D1));
IN := ideal<R | Generators(IN)>;
ID := ideal<R | Generators(ID)>;
XE4_D1 := Divisor(XE4, IN) - Divisor(XE4, ID);

assert D4 eq XE4_D1;

IN := Ideal(Numerator(XE4_D2));
ID := Ideal(Denominator(XE4_D2));
IN := ideal<R | Generators(IN)>;
ID := ideal<R | Generators(ID)>;
XE4_D2 := Divisor(XE4, IN) - Divisor(XE4, ID);

assert D2 eq XE4_D2;
