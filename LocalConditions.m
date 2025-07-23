// ============================================================
// Auxiliary functions to compute the local Selmer conditions at 2
// ============================================================

// ========================================================
// RandomQ2PointsOnQuartic
//
// Generate random Q_2-points on a plane quartic curve X over Q.
//
// INPUT:
// - X    : a projective plane quartic curve
// - n    : (half the) desired number of points
// - prec : 2-adic precision (optional, default = 100)
//
// OUTPUT:
// - A list of Q_2-points on X, represented as triples in Q_2^3
//
// METHOD:
// - Works on affine patches z = 1 and y = 1
// - Specializes F(x, y, 1) and F(x, 1, z) for random y and z values
// - Roots in Q_2 via MAGMA's Roots function
// - Filters out points too close to [0 : 1 : 0]
//
// ========================================================
function RandomQ2PointsOnQuartic(X, n : prec := 100)
    F := DefiningPolynomial(X);
    Qp := pAdicField(2, prec);
    R := BaseRing(Parent(F));
    P<x> := PolynomialRing(Qp); // Work in univariate ring after substitution

    points := {};

    // Affine patch z = 1
    while #points lt n do
        y := Random([-16..16]);
        h := hom<Parent(F) -> P | [ P.1, y, 1 ]>;
        F0 := h(F); // F(x, y, 1)

        if not IsZero(F0) then
            roots := Roots(F0);
            for r in roots do
                points := points join {<r[1], Qp!y, Qp!1>};
                if #points ge n then
                    break;
                end if;
            end for;
        end if;
    end while;

    // Affine patch y = 1
    while #points lt 2*n do
        z := Random([-16..16])+1;
        h := hom<Parent(F) -> P | [ P.1, 1, z ]>;
        F0 := h(F); // F(x, 1, z)

        if not IsZero(F0) then
            roots := Roots(F0);
            for r in roots do
                points := points join {<r[1], Qp!1, Qp!z>};
            end for;
        end if;
    end while;

    // Filter to avoid points too close to [0:1:0]
    points := [P : P in points | Valuation(P[1]) lt 6 or Valuation(P[2]-1) lt 6 or Valuation(P[3]) lt 6];

    return points;
end function;


// ========================================================
// EvaluateRationalFunctionOnDifferencePoints
//
// Evaluate a rational function f at the divisor P1 − P2.
//
// INPUT:
// - f  : a rational function on the curve
// - P1 : a Q_2-point given as a triple
// - P2 : a Q_2-point given as a triple
//
// OUTPUT:
// - The value f(P1) / f(P2)
//
// ========================================================
function EvaluateRationalFunctionOnDifferencePoints(f, P1, P2)
    return Evaluate(f, [P1[1], P1[2], P1[3]]) / Evaluate(f, [P2[1], P2[2], P2[3]]);
end function;


// ========================================================
// AttemptToGenerateLocalSelmer
//
// Attempt to generate a basis for the local Selmer conditions at 2.
//
// INPUT:
// - XA   : a base-changed quartic curve
// - bc   : a list of cubic forms representing the descent map
// - reps : representatives of Q_2^* / Q_2^{*2}
//
// OUTPUT:
// - basis : a basis (mod squares) for the subgroup of local images
// - test  : boolean indicating if the expected dimension was achieved
//
// NOTES:
// - This is a randomized procedure using random Q_2-points
// - The test may not always be reliable and should be verified
//
// ========================================================
function AttemptToGenerateLocalSelmer(XA, bc, reps)
    rps := RandomQ2PointsOnQuartic(XA, 7); // Random Q_2-points on X

    P0 := rps[1]; // Basepoint for computing differences
    LocalPoints := [* *];

    for i in [2..#rps] do
        Append(~LocalPoints, [* EvaluateRationalFunctionOnDifferencePoints(c, P0, rps[i]) : c in bc *]);
    end for;

    basis := BasisInZ(LocalPoints, reps);
    test := #basis eq 3 + (#bc - 1); // Expected dimension

    /*
        WARNING: the test above is a placeholder and might be incorrect for general curves.
        It works for all the curves X_{E_i} in the paper, but should be checked in general.
    */

    return basis, test;
end function;


// ========================================================
// GenerateLocalSelmer
//
// Repeatedly calls AttemptToGenerateLocalSelmer until it succeeds.
//
// INPUT:
// - XA   : a base-changed quartic curve
// - bc   : a list of cubic forms representing the descent map
// - reps : representatives of Q_2^* / Q_2^{*2}
//
// OUTPUT:
// - A basis for the local descent condition space
//
// ========================================================
function GenerateLocalSelmer(XA, bc, reps)
    test := false;
    while not test do
        gls, test := AttemptToGenerateLocalSelmer(XA, bc, reps);
    end while;
    return gls;
end function;