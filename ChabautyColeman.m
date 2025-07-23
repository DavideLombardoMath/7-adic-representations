//================================================
// Chabauty-Coleman computations for the curves X_{E_i}
// Run this file from a directory that contains the Balakrishnan-Tuitman
// implementation of Coleman integrals https://github.com/jtuitman/Coleman
//================================================


load "Generators.m";

// ======================================================================
// SupportPointsOverQp
//
// INPUT:
// - X : a curve defined over Q
// - D : a divisor on X
// - p : a prime number
//
// OUTPUT:
// - A list of coordinate sequences of the Q_p-rational points in the support of D
//
// DESCRIPTION:
// - For each point P in the support of the divisor D, determines all embeddings
//   of the residue field of P into Q_p and applies these to the coordinates
//   of a representative point. This yields the Q_p-rational points lying
//   over the support of D.
//
// METHOD:
// - If P is defined over Q, its coordinates are directly embedded into Q_p.
// - Otherwise, we compute all embeddings of the residue field into Q_p
//   via roots of its minimal polynomial, and apply them to the coordinates.
//
// ======================================================================

function SupportPointsOverQp(X, D, p)
    Qp := pAdicField(p : Precision := 50);

    result := [];

    for P in Support(D) do
        K := ResidueClassField(P);

        if Degree(K) eq 1 then
            // Point is rational: lift coordinates directly to Q_p
            coords := Coordinates(RepresentativePoint(P));
            coords_p := [ Qp!c : c in coords ];
            Append(~result, coords_p);
        else
            // Point defined over number field K
            mK := AbsoluteField(K);
            fK := DefiningPolynomial(mK);
            fQp := ChangeRing(fK, Qp);
            rts := [ r[1] : r in Roots(fQp) ];  // roots of defining poly in Q_p

            // Compute all embeddings of K into Q_p
            embeddings := [ hom<K -> Qp | rt> : rt in rts ];

            coords := Coordinates(RepresentativePoint(P));

            // Apply each embedding to the coordinates
            for emb in embeddings do
                coords_p := [ emb(c) : c in coords ];
                Append(~result, coords_p);
            end for;
        end if;
    end for;

    return result;
end function;




// ======================================================================
// Coleman integration on the curve X_{E_1}
// ======================================================================

// Define the plane model of X_{E_1} and its function field
f1 := DefiningEquation(XE1_alternativemodel);
XE1 := PlaneCurve(f1);
FF<x,y> := FunctionField(XE1);

// Retrieve our generator of a finite-index subgroup of J(Q)
D := Explode(RetrieveGenerators(1));

// Compute the support of the numerator of D over Q_p for p = 41
suppQp := SupportPointsOverQp(XE1, Numerator(D), 41);
Qp := Parent(suppQp[1][1]);

// Add the point at infinity [0:1:0]
suppQp := suppQp cat [ [Qp!0, 1, 0] ];

// ======================================================================
// Coleman integration setup
// ======================================================================

load "coleman.m";

"=========== X_{E_1} ===========";

// The code in coleman.m assumes affine coordinates and a monic polynomial in y
// We change coordinates: dehomogenise, change variable names and divide by
// leading coefficient
f1Coleman := Evaluate(f1, [x,1,y]) / (-196);

// Rewrite support points in affine coordinates for Coleman integration
suppColeman := [ [P[1]/P[2], P[3]/P[2], 1] : P in suppQp ];

// Parameters
p := 41;
N := 20;

// Initialize data structure for Coleman integration
data := coleman_data(f1Coleman, p, N);

// Set up the points as Coleman integration inputs
Q1, Q2, Q3, Q4 := Explode(suppColeman);

P1 := set_point(Q1[1], Q1[2], data);
P2 := set_point(Q2[1], Q2[2], data);
P3 := set_point(Q3[1], Q3[2], data);
P4 := set_point(Q4[1], Q4[2], data);  // base point

// ======================================================================
// Compute Coleman integrals from base point P4 to each point in the numerator of D
// ======================================================================

IP1P4, N2 := coleman_integrals_on_basis(P1, P4, data : e := 50);
IP2P4, N3 := coleman_integrals_on_basis(P2, P4, data : e := 50);
IP3P4, N4 := coleman_integrals_on_basis(P3, P4, data : e := 50);

// Use the lowest precision that gives consistent integrals
Nint := Min([N2, N3, N4]);

// Compute integrals along D as the sum of the three integrals from the 
// base point to the points in the support of Numerator(D)
IntAlongD := IP1P4 + IP2P4 + IP3P4;

// ======================================================================
// Determine vanishing differentials
// ======================================================================

K := pAdicField(p, Nint);
M := ZeroMatrix(K, 3, 1);

for i in [1..3] do
    M[i,1] := K!reduce_mod_pN_Q(Rationals()!IntAlongD[i], p, Nint);
end for;

// Compute the space of differentials vanishing along D
v := basis_kernel(M);

// ======================================================================
// There is a unique zero of the resulting differential in the residue disc of P4
// ======================================================================

"Number of zeroes in the residue disc of [0 : 1 : 0]:", 
    #zeros_on_disk(P4, P4, v, data);





// ======================================================================
// Coleman integration on the curve X_{E_2}
// ======================================================================

"=========== X_{E_2} ===========";


// Define the plane model of X_{E_2} and its function field
XE2 := ModelXE(E2);
f2 := DefiningEquation(XE2);

// Retrieve our two generators of a finite-index subgroup of J(Q)
D1, D2 := Explode(RetrieveGenerators(2));

// Prime of good reduction
p := 73;

// ======================================================================
// Coleman integration setup
// ======================================================================

// The implementation in coleman.m works in affine coordinates and
// assumes the defining equation is monic in y
f2Coleman := Evaluate(f2, [x,1,y]) / (-6);

// Parameters
N := 20;
data := coleman_data(f2Coleman, p, N);

// ======================================================================
// Prepare points for Coleman integration (support of D1, support of D2)
// ======================================================================

suppQp := SupportPointsOverQp(XE2, Numerator(D1), p);
Qp := Parent(suppQp[1][1]);

// Add the point at infinity [0:1:0]
suppQp := suppQp cat [ [Qp!0, 1, 0] ];

// Rewrite support points in affine coordinates for Coleman integration
suppColeman := [ [P[1]/P[2], P[3]/P[2], 1] : P in suppQp ];

// Set up the points for integration
Q1, Q2, Q3, Q4 := Explode(suppColeman);

P1 := set_point(Q1[1], Q1[2], data);
P2 := set_point(Q2[1], Q2[2], data);
P3 := set_point(Q3[1], Q3[2], data);
P4 := set_point(Q4[1], Q4[2], data);  // base point

// Point in the numerator of D2
suppQp := SupportPointsOverQp(XE2, Numerator(D2), p);
suppColeman := [ [P[1]/P[2], P[3]/P[2], 1] : P in suppQp ];
P5 := set_point(suppColeman[1][1], suppColeman[1][2], data);

// ======================================================================
// Compute integrals
// ======================================================================

// Integrals from base point P4 to support of D1 and D2
IP1P4, N1 := coleman_integrals_on_basis(P1, P4, data : e := 50);
IP2P4, N2 := coleman_integrals_on_basis(P2, P4, data : e := 50);
IP3P4, N3 := coleman_integrals_on_basis(P3, P4, data : e := 50);
IP5P4, N5 := coleman_integrals_on_basis(P5, P4, data : e := 50);

// Use the lowest precision among all integrals
Nint := Min([N1, N2, N3, N5]);

// Compute integrals along D1 as the sum of the three integrals from the 
// base point to the points in the support of Numerator(D1)
IntAlongD := IP1P4 + IP2P4 + IP3P4;

// ======================================================================
// Determine vanishing differentials
// ======================================================================

K := pAdicField(p, Nint);
M := ZeroMatrix(K, 3, 2);

for i in [1..3] do
    M[i,1] := K!reduce_mod_pN_Q(Rationals()!IntAlongD[i], p, Nint);
    M[i,2] := K!reduce_mod_pN_Q(Rationals()!IP5P4[i], p, Nint);
end for;

// Compute the space of differentials vanishing along both D1 and D2
v := basis_kernel(M);

// ======================================================================
// Count common zeros of the resulting differential in relevant residue discs
// ======================================================================

"Number of zeroes in the residue disc of [0 : 1 : 0]:", 
    #zeros_on_disk(P4, P4, v, data);

"Number of zeroes in the residue disc of [1 : 1 : 0]:", 
    #zeros_on_disk(P4, P5, v, data);




// ======================================================================
// Coleman integration on the curve X_{E_4}
// ======================================================================

"=========== X_{E_4} ===========";

// Define the plane model of X_{E_4} and its function field
XE4 := ModelXE(E4);
f4 := DefiningEquation(XE4);

// Retrieve our two generators of a finite-index subgroup of J(Q)
D1, D2 := Explode(RetrieveGenerators(4));

// Prime of good reduction
p := 31;

// D1 does not split over Q_p, but 2*D1 does. Since 2 is invertible mod p,
// this does not affect the Chabauty-Coleman computation. We replace D1
// with a suitable representative of 2*D1 of the form R-3(P_0), where R
// has degree 3
function CanonicalRepresentativeDivisorClass(D, P0)
    C := Curve(D);
    P0 := C!P0;
    RRspace, RRmap := RiemannRochSpace(D + 3*Divisor(P0));
    f := RRmap(RRspace.1);
    return D + Divisor(f);
end function;

P0 := XE4![0,1,0];
D1 := CanonicalRepresentativeDivisorClass(2*D1, [0,1,0]);

// ======================================================================
// Coleman integration setup
// ======================================================================

// Use affine coordinates [x : y : y + 1] for this model of the curve
f4Coleman := Evaluate(f4, [x, y, y+1]);

// Parameters
N := 20;
data := coleman_data(f4Coleman, p, N);

// ======================================================================
// Prepare points for Coleman integration (support of D1, support of D2)
// ======================================================================

suppQp := SupportPointsOverQp(XE4, Numerator(D1), p);
assert #suppQp eq 3;

Qp := Parent(suppQp[1][1]);

// Add the point at infinity [0 : 1 : 0] as base point
suppQp := suppQp cat [ [Qp!0, 1, 0] ];

// Rewrite support points in affine coordinates for Coleman integration
// Note that the change of variables is compatible with our affine coordinates
suppColeman := [ [ P[1] / (-P[2] + P[3]), P[2] / (-P[2] + P[3]), 1 ] : P in suppQp ];

// Set up the points for integration
Q1, Q2, Q3, Q4 := Explode(suppColeman);

P1 := set_point(Q1[1], Q1[2], data);
P2 := set_point(Q2[1], Q2[2], data);
P3 := set_point(Q3[1], Q3[2], data);
P4 := set_point(Q4[1], Q4[2], data);	// base point

// ======================================================================
// Compute integrals for D1 and D2
// ======================================================================

// Support point for D2
suppQp := SupportPointsOverQp(XE4, Numerator(D2), p);
suppColeman := [ [ P[1] / (-P[2] + P[3]), P[2] / (-P[2] + P[3]), 1 ] : P in suppQp ];
P5 := set_point(suppColeman[1][1], suppColeman[1][2], data);

// Integrals from base point P1 to support of D1 and D2
IP1P4, N1 := coleman_integrals_on_basis(P1, P4, data : e := 50);
IP2P4, N2 := coleman_integrals_on_basis(P2, P4, data : e := 50);
IP3P4, N3 := coleman_integrals_on_basis(P3, P4, data : e := 50);
IP5P4, N5 := coleman_integrals_on_basis(P5, P4, data : e := 50);

// Use the lowest precision among all integrals
Nint := Min([N1, N2, N3, N5]);

// Compute integrals along D1 as the sum of the three integrals from the 
// base point to the points in the support of Numerator(D1)
IntAlongD := IP1P4 + IP2P4 + IP3P4;

// ======================================================================
// Determine vanishing differentials
// ======================================================================

K := pAdicField(p, Nint);
M := ZeroMatrix(K, 3, 2);

for i in [1..3] do
    M[i,1] := K!reduce_mod_pN_Q(Rationals()!IntAlongD[i], p, Nint);
    M[i,2] := K!reduce_mod_pN_Q(Rationals()!IP5P4[i], p, Nint);
end for;

// Compute the space of differentials vanishing along both D1 and D2
v := basis_kernel(M);

// ======================================================================
// Count common zeros of the resulting differential in relevant residue discs
// ======================================================================

"Number of zeroes in the residue disc of [0 : 1 : 0]:", 
    #zeros_on_disk(P4, P4, v, data);

"Number of zeroes in the residue disk of [0 : 0 : 1]:", 
    #zeros_on_disk(P4, P5, v, data);
