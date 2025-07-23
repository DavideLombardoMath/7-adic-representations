//================================================
// Solve some relevant Thue equations and filter
// points on modular curves of level 49
//================================================

load "FindOpenImage.m"; // Load Zywina's algorithm to compute the image of Galois representations associated to elliptic curves

// Define rational function field in two variables x, y
R<x,y> := FieldOfFractions(PolynomialRing(Rationals(),2));

// Define modular parameter t
t := x/y;

// Define j-invariant maps for the split and non-split Cartan modular curves of level 7
// j-invariant map for X_{sp}^+(7)
jsp := t*(t+1)^3*(t^2-5*t+1)^3*(t^2-5*t+8)^3*(t^4-5*t^3+8*t^2-7*t+7)^3 / (t^3-4* t^2+3*t+1)^7;

// j-invariant map for X_{ns}^+(7)
jnsp := 64*t^3*(t^2+7)^3*(t^2-7*t+14)^3*(5*t^2-14*t-7)^3 / (t^3-7*t^2+7*t+7)^7;

// Work in univariate polynomial ring over Z
R<x> := PolynomialRing(Integers());

// We solve the relevant Thue equations
f1 := x^3 - 7*x^2 + 7*x + 7;
T1 := Thue(f1); // Thue equation corresponding to f1

// Solutions to Thue equations corresponding to rational or low-norm integral points
solCns := Solutions(T1, 1) cat Solutions(T1, 8);
solGnsSharp := Solutions(T1, 7) cat Solutions(T1, 7*8);

f2 := x^3 - 4*x^2 + 3*x + 1;
T2 := Thue(f2); // Thue equation corresponding to f2
solGspSharp := Solutions(T2, 1) cat Solutions(T2, 7);

// Evaluate j-invariants at solutions of Thue equations
jCns := { Evaluate(jnsp, s) : s in solCns }; // candidate j-invariants for X_{ns}^+(49)
jGnsSharp := { Evaluate(jnsp, s) : s in solGnsSharp }; // candidate j-invariants for X_{ns}^#(49)
jGspSharp := { Evaluate(jsp, s) : s in solGspSharp | s[2] ne 0 }; // candidate j-invariants for X_{sp}^#(49), avoiding division by zero

// Filter jCns: remove any j not actually corresponding to a point on X_{ns}^+(49)
AreAllCM_Cns := true;
for j in jCns do
	E := EllipticCurveFromjInvariant(j);
	isCM := HasComplexMultiplication(E);
    if not isCM then
		G := FindOpenImage(E);
		if not (#BaseRing(G) mod 49 eq 0) then
			// #BaseRing(G) is the level of definition of the representation. If it's not divisible by 49, then the point is not on X_{ns}^+(49)
			Exclude(~jCns, j);
        else
            AreAllCM_Cns := false;
		end if;
	end if;
end for;

// Filter jGnsSharp: keep only those j-invariants corresponding to
// elliptic curve with adelic Galois image of level divisible by 49
AreAllCM_GnsSharp := true;
for j in jGnsSharp do
	E := EllipticCurveFromjInvariant(j);
	isCM := HasComplexMultiplication(E);
	if not isCM then
		G := FindOpenImage(E);
		if not (#BaseRing(G) mod 49 eq 0) then
			Exclude(~jGnsSharp, j);
        else
            AreAllCM_GnsSharp := false;
		end if;
	end if;
end for;

// Filter jGspSharp: same process for X_{sp}^#(49)
AreAllCM_GspSharp := true;
for j in jGspSharp do
	E := EllipticCurveFromjInvariant(j);
	isCM := HasComplexMultiplication(E);
	if not isCM then
		G := FindOpenImage(E);
		if not (#BaseRing(G) mod 49 eq 0) then
			Exclude(~jGspSharp, j);
        else
            AreAllCM_GspSharp := false;
		end if;
	end if;
end for;


"j-invariants for the curve X_{ns}^+(49):", jCns;
if AreAllCM_Cns then
    "Every j-invariant in the list above is CM";
end if;

"j-invariants for the curve X_{sp}^#(49):", jGspSharp;
if AreAllCM_GspSharp then
    "Every j-invariant in the list above is CM";
end if;

"j-invariants for the curve X_{ns}^#(49):", jGnsSharp;
if AreAllCM_GnsSharp then
    "Every j-invariant in the list above is CM";
end if;

"------------------------";

CMCns := [];
"Discriminants of the j-invariants for Cns+(49):";
for j in jCns do
    E := EllipticCurveFromjInvariant(j);
    _,Disc := HasComplexMultiplication(E);
    Append(~CMCns, Disc);
end for;
CMCns;

CMGspSharp := [];
"Discriminants of the j-invariants for Gsp#(49):";
for j in jGspSharp do
    E := EllipticCurveFromjInvariant(j);
    _,Disc := HasComplexMultiplication(E);
    Append(~CMGspSharp, Disc);
end for;
CMGspSharp;

CMGnsSharp := [];
"Discriminants of the j-invariants for Gns#(49):";
for j in jGnsSharp do
    E := EllipticCurveFromjInvariant(j);
    _,Disc := HasComplexMultiplication(E);
    Append(~CMGnsSharp, Disc);
end for;
CMGnsSharp;