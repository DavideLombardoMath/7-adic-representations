//=================================================
// This script defines models of twists of the Klein quartic corresponding to 
// the symplectic structures of elliptic curves E1, E2, E3, E4.
// The j-maps from these twists to P^1 are also computed.
//=================================================

E1 := EllipticCurve([0, -1, 0, -2, 1]);
E2 := EllipticCurve([0, 0, 0, -7, 7]);
E3 := EllipticCurve([0, -1, 0, -16, 29]);
E4 := EllipticCurve([0, -1, 0, -142, 701]);

/*
Returns the twist of the Klein quartic X(7) with respect to the
symplectic structure of the 7-torsion of E.
*/
function ModelXE(E)
    E := WeierstrassModel(E);
    as := aInvariants(E);
    a := as[4];
    b := as[5];
    R<x,y,z> := PolynomialRing(Rationals(), 3);
    f := a*x^4 + 7*b*x^3*z + 3*x^2*y^2 - 3*a^2*x^2*z^2 - 6*b*x*y*z^2
         - 5*a*b*x*z^3 + 2*y^3*z + 3*a*y^2*z^2 + 2*a^2*y*z^3 - 4*b^2*z^4;
    return Curve(ProjectiveSpace(R), MinimizeReducePlaneQuartic(f));
end function;

/*
Returns the twist of the Klein quartic X(7) corresponding to the
anti-symplectic structure of the 7-torsion of E.
*/
function ModelXEMinus(E)
    E := WeierstrassModel(E);
    as := aInvariants(E);
    a := as[4];
    b := as[5];
    R<x,y,z> := PolynomialRing(Rationals(), 3);
    f := -a^2*x^4 + a*(3*a^3 + 19*b^2)*y^4 + 3*z^4 + 6*a^2*y^2*z^2 + 6*a*z^2*x^2
         - 6*(a^3 + 6*b^2)*x^2*y^2 - 12*a*b*y^2*z*x + 18*b*z^2*x*y + 2*a*b*x^3*y
         - 12*b*x^3*z - 2*(4*a^3 + 21*b^2)*y^3*z + 2*a^2*b*y^3*x - 8*a*z^3*y;
    return Curve(ProjectiveSpace(R), MinimizeReducePlaneQuartic(f));
end function;

/*
Compute the standard covariant Psi6 associated to a given model of the Klein quartic.
*/
function Psi6(XE)
    return -1/54 * Determinant(HessianMatrix(XE));
end function;

/*
Compute the standard covariant Psi14 associated to a given model of the Klein quartic.
*/
function Psi14(XE)
    psi6 := Psi6(XE);
    psi6x := Derivative(psi6, 1);
    psi6y := Derivative(psi6, 2);
    psi6z := Derivative(psi6, 3);
    H := HessianMatrix(XE);
    M := Matrix(Parent(H[1][1]), 4, 4, [
        H[1][1], H[1][2], H[1][3], psi6x, 
        H[2][1], H[2][2], H[2][3], psi6y, 
        H[3][1], H[3][2], H[3][3], psi6z, 
        psi6x, psi6y, psi6z, 0
    ]);
    return 1/9 * Determinant(M);
end function;

/*
Differential operator used in the definition of Psi0.
*/
function DiffOperator(h)
    S := Parent(h);
    return Derivative(Derivative(Derivative(h, S.1), S.5), S.9) +
           Derivative(Derivative(Derivative(h, S.3), S.4), S.8) +
           Derivative(Derivative(Derivative(h, S.2), S.6), S.7) -
           (
               Derivative(Derivative(Derivative(h, S.1), S.6), S.8) +
               Derivative(Derivative(Derivative(h, S.2), S.4), S.9) +
               Derivative(Derivative(Derivative(h, S.3), S.5), S.7)
           );
end function;

/*
Compute the covariant Psi0 of the Klein quartic model.
*/
function Psi0(XE)
    h := DefiningPolynomial(XE);
    S<x1,y1,z1,x2,y2,z2,x3,y3,z3> := PolynomialRing(Rationals(), 9);
    R := Parent(h);
    hom1 := hom<R -> S | [x1,y1,z1]>;
    hom2 := hom<R -> S | [x2,y2,z2]>;
    hom3 := hom<R -> S | [x3,y3,z3]>;
    h1 := hom1(h);
    h2 := hom2(h);
    h3 := hom3(h);
    return 1/5184 * DiffOperator(DiffOperator(DiffOperator(DiffOperator(h1*h2*h3))));
end function;

/*
Return the j-map from the Klein quartic twist XE to the modular curve X(1).
*/
function jMapXE(XE)
    psi14 := Psi14(XE);
    psi0 := Psi0(XE);
    psi6 := Psi6(XE);
    return psi14^3 / (Rationals()!psi0 * psi6^7);
end function;

/*
Given an elliptic curve E, compute the j-invariants of small rational points
on the twist of X(7) corresponding to the symplectic structure of E[7].
*/
function PresumablyComputejInvariants(E)
    XE := ModelXE(E);
    j := jMapXE(XE);
    rp := RationalPoints(XE : Bound := 1000);
    return [ Evaluate(j, [P[1], P[2], P[3]]) : P in rp ];
end function;

/*
Compute the models of X_{E_i}, i=1,2,3,4
*/

XE1 := ModelXE(E1);
XE2 := ModelXE(E2);
XE3 := ModelXE(E3);
XE4 := ModelXE(E4);
