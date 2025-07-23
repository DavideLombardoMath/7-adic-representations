// ============================================================
// Implementation of 2-descent on a plane quartic with special 
// properties, following the ideas of [PSS08].
// ============================================================

load "Cubic.m";
load "LinearAlgebra.m";
load "LocalConditions.m";

// ========================================================
// TwoDescentPlaneQuartic
//
// Perform a 2-descent on a plane quartic curve X over Q
// (under several assumptions).
//
// INPUT:
// - f             : homogeneous equation defining X
// - TestCubic     : optional, if true, verify that the cubic
//                   computed in the process has the desired properties
// - P             : optional, a rational base point
// - ReturnKernel  : optional, if true, return the kernel of the map
//                   J(Q)/2J(Q) → Sel^2_fake
//
// OUTPUT:
// - The fake 2-Selmer group of X
// - An auxiliary number field A
// - The base-change of X to A
// - A cubic inducing the map J(Q)/2J(Q) → Sel^2_fake
// - (if ReturnKernel = true) a generator of the kernel of
//   the map J(Q)/2J(Q) → Sel^2_fake
//
// ========================================================

function TwoDescentPlaneQuartic(f : TestCubic := false, P := [0,1,0], ReturnKernel := false)
    // Initialise basic objects
    R := Parent(f);
    S<u,v> := PolynomialRing(Rationals(), 2);
    T<t> := PolynomialRing(Rationals());
    X := Curve(ProjectiveSpace(R), [f]);

    /*
    Check that the component group at 7 has odd order. Since MAGMA's RegularModel
    is picky about equations, we normalise the curve accordingly.
    */
    den := Coefficients(f)[1];
    fTest7 := Evaluate(f, [R.1, den*R.2, den*R.3]);
    RM := RegularModel(PlaneCurve(fTest7), 7);
    assert #ComponentGroup(RM) mod 2 eq 1;

    evaluation := hom<R -> S | [u, v, 1]>;
    toOneVariable := hom<S -> T | [t, 0]>;

    /*
    Dehomogenise and take resultant of f with its Hessian
    to construct a number field over which a flex is defined
    */
    gDehom := evaluation(f);

    H := HessianMatrix(X);
    h := Determinant(H);
    hDehom := evaluation(h);

    res := toOneVariable(Resultant(gDehom, hDehom, v));
    K<u1> := NumberField(res);

    /*
    Compute flexes over K
    */
    XK := ChangeRing(X, K);
    FK := RationalPoints(Flexes(XK));

    mp := MinimalPolynomial(&+[ FK[i][1]/FK[i][3] : i in [1..3] ]);
    A := NumberField(mp);
    A := OptimisedRepresentation(A);
    print "Algebra A", A;
    if ClassNumber(A) gt 1 then
        error "Class number of A is not one";
    end if;

    /*
    Define the flexes and the base rational point
    */
    T1 := FK[1];
    T2 := FK[2];
    T3 := FK[3];
    P := XK!P;

    /*
    Compute the interpolating cubic passing through the T_i's
    with multiplicity at least 2 and through P with multiplicity at least 3
    */
    G := FindSpecialCubic(DefiningPolynomial(XK), T1, T2, T3, P);

    /*
    Optional test of multiplicities of G at the given points
    */
    if TestCubic then
        S := Scheme(ProjectiveSpace(Parent(G)), [G, DefiningPolynomial(XK)]);
        "Multiplicity of G at T1", Multiplicity(S, S!Coordinates(T1));
        "Multiplicity of G at T2", Multiplicity(S, S!Coordinates(T2));
        "Multiplicity of G at T3", Multiplicity(S, S!Coordinates(T3));
        "Multiplicity of G at P", Multiplicity(S, S!Coordinates(P));
    end if;

    /*
    Descend G to the field A
    */
    coefs := Coefficients(G);
    mons := Monomials(G);
    PA<X,Y,Z> := PolynomialRing(A, 3);
    mons := [PA!m : m in mons];
    _, emb := IsSubfield(A, K);
    coefsA := [PullBackToSubfieldByLinearAlgebra(A, K, emb, c) : c in coefs];
    GA := &+[mons[i]*coefsA[i] : i in [1..#coefsA]];

    XA := ChangeRing(XK, A);
    XAFF<x,y> := FunctionField(XA);

    /*
    Compute the divisor R - 3P as in [PSS08]
    */
    if ReturnKernel then
        S := Scheme(AmbientSpace(XA), [GA]);
        D := Divisor(XA, S);
        sup, mul := Support(D);

        /*
        Check that there is only one non-split divisor appearing with multiplicity 1
        This will be our divisor R
        */
        GoodIndices := [i : i in [1..#mul] | mul[i] eq 1];
        assert #GoodIndices eq 1;
        i := GoodIndices[1];
        R := sup[i];
        "Ideal defining R (to check rationality)", ChangeRing(Ideal(R), Rationals());
        KernelDescentMap := R - 3*Divisor(XA!Coordinates(P));

	/*
	The rest of this "if" checks that three Qbar points in the support of R
	do not all lie on the same line in the plane
	*/

	/*
	Descend the divisor R to Q
	*/
	XQ := Curve(ProjectiveSpace(Parent(f)), [f]);
	IR := ChangeRing(Ideal(R), Rationals());
	RQ := Divisor(XQ, ideal<Parent(f) | Generators(IR)>);

	/*
	Compute a number field over which all points in the
	support of R are defined
	*/
	suppRQ := Support(RQ);
	PRQ := RepresentativePoint(suppRQ[1]);
	KPR := Parent(PRQ[1]);
	KPR := NormalClosure(KPR);
	KPR := OptimisedRepresentation(KPR);

	/*
	Base-change both curve and divisor to KPR
	*/
	XKPR := ChangeRing(XQ, KPR);
	IRKPR := ChangeRing(Ideal(R), KPR);
	RKPR := Divisor(XKPR, ideal<Parent(DefiningEquation(XKPR)) | Generators(IRKPR)>);

	/*
	Get points of R over KPR
	*/
	suppRKPR := Support(RKPR);
	ptsRKPR := [RepresentativePoint(pt) : pt in suppRKPR];


	/*
	Check that the three points do not lie on a line
	*/
	M := Matrix(KPR, 3, 3, &cat[Coordinates(pt) : pt in ptsRKPR]);
	"The three points in the support of R do not lie on a line:", Determinant(M) ne 0;
	assert Determinant(M) ne 0;

    end if;

    /*
    List all elements in the F_2-vector space A* / (A*^2 · Q*) and keep
    those whose norm down to Q* is a square
    */
    Ps, gens, U, mU := Init2AdicData(A);
    ar := AllRepresentatives(P, gens, U, mU);
    H := [ x : x in ar | IsSquare(Norm(x)) ];
    H := RemoveEquivalentModSquaresAndRationals(H, A, Ps, gens, U, mU);

    /*
    Compute the local conditions at the prime 2
    */
    LocalFields, Maps := LocalDecomposition(A);
    bc := BaseChangeCubic(GA, LocalFields, Maps);
    "Factors of A tensor Q_2:", LocalFields;

    gls := GenerateLocalSelmer(XA, bc, reps);
    "F_2-dimension of local Selmer conditions at 2:", #gls;

    /*
    Filter elements of H which satisfy the local conditions at 2
    */
    HfilterQ2 := [];
    for h in H do
        hQ2 := [* m(h) : m in Maps *]; // map to local algebra
        if IsInSpanZ(hQ2, gls, reps) then
            Append(~HfilterQ2, h);
        end if;
    end for;
    "Number of elements in the fake Selmer group:", #HfilterQ2;

    if ReturnKernel then
        return HfilterQ2, A, XA, GA, KernelDescentMap;
    else
        return HfilterQ2, A, XA, GA;
    end if;
end function;
