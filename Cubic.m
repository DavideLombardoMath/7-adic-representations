// ============================================================
// This script implements two main functions:
// - FindSpecialCubic: given a plane quartic with four marked points
//   T_1, T_2, T_3, P, find a plane cubic that goes through them
//   with multiplicities at least 2, 2, 2, 3.
// - EvaluateRationalFunctionOnGaloisOrbitDivisor: evaluates a rational
//   function f at a Galois-stable divisor disjoint from div(f)
// ============================================================


// ============================================================
// GradientAt(F, pt)
//
// INPUT:
//   F  : homogeneous form in A[x,y,z]
//   pt : point on which to evaluate gradient (coordinates in A^3)
//
// OUTPUT:
//   Gradient vector ?F(pt) = [?F/?x(pt), ?F/?y(pt), ?F/?z(pt)]
// ============================================================
function GradientAt(F, pt)
    coords := Coordinates(pt);  // [x0, y0, z0] ? A^3
    return [Evaluate(Derivative(F, i), coords) : i in [1..3]];
end function;


// ============================================================
// GradientOfMonomialAt(m, pt)
//
// INPUT:
//   m  : degree-3 monomial in A[x,y,z]
//   pt : point on which to evaluate gradient (coordinates in A^3)
//
// OUTPUT:
//   Gradient vector ?m(pt) = [?m/?x(pt), ?m/?y(pt), ?m/?z(pt)]
// ============================================================
function GradientOfMonomialAt(m, pt)
    coords := Coordinates(pt);
    return [Evaluate(Derivative(m, i), coords) : i in [1..3]];
end function;


// ============================================================
// HessianOfMonomialAt(m, pt)
//
// INPUT:
//   m  : degree-3 monomial in A[x,y,z]
//   pt : point on which to evaluate Hessian (coordinates in A^3)
//
// OUTPUT:
//   3×3 Hessian matrix H with entries H[i,j] = ?²m/?x_i?x_j(pt)
// ============================================================
function HessianOfMonomialAt(m, pt)
    coords := Coordinates(pt);
    Hvals := [];
    for i in [1..3] do
        for j in [1..3] do
            Append(~Hvals, Evaluate(Derivative(Derivative(m, i), j), coords));
        end for;
    end for;
    return Matrix(3, 3, Hvals);
end function;

// ============================================================
// FindSpecialCubic(F, T1, T2, T3, P)
//
// INPUT:
//   F  : homogeneous quartic in A[x,y,z] defining X ? P²_A
//   T1, T2, T3, P : four A-rational points on X
//
// OUTPUT:
//   A homogeneous cubic G ? A[x,y,z] such that
//     div_X(G) = 2·(T1 + T2 + T3) + 3·P
//   i.e., G has multiplicity = 2 at each T_i and = 3 at P.
// ============================================================

function FindSpecialCubic(F, T1, T2, T3, P)
    PA := Parent(F);
    A := BaseRing(PA);
    X := Curve(ProjectiveSpace(PA), F);

    mon_basis := MonomialsOfDegree(PA, 3); // 10 degree-3 monomials
    N := #mon_basis;

    rows := [];

    // 1) Vanishing at T1, T2, T3, P (4 conditions)
    for pt in [T1, T2, T3, P] do
        coords := Coordinates(pt);
        Append(~rows, [Evaluate(m, coords) : m in mon_basis]);
    end for;

    // 2) First-order tangency: ?G(pt) proportional to ?F(pt)
    for pt in [T1, T2, T3, P] do
        gF := GradientAt(F, pt);

        // For each pair of gradient components, impose cross-product = 0
        row1 := []; row2 := []; row3 := [];
        for k in [1..N] do
            gmk := GradientOfMonomialAt(mon_basis[k], pt);
            Append(~row1, gF[1]*gmk[2] - gF[2]*gmk[1]);
            Append(~row2, gF[1]*gmk[3] - gF[3]*gmk[1]);
            Append(~row3, gF[2]*gmk[3] - gF[3]*gmk[2]);
        end for;
        Append(~rows, row1); Append(~rows, row2); Append(~rows, row3);
    end for;

    // 3) Second-order contact at P: D_t²(G)(P) = 0 for tangent direction t
    // Handle all three cases depending on which coordinate of P is nonzero.
    gF_P := GradientAt(F, P);
    HessF := HessianMatrix(X);
    HessF := Evaluate(HessF, Coordinates(P));

    function SecondOrderRow(coordIndex, gF_P, HessF)
        rows := [];
        // Tangent vector t depends on coordIndex (1-based: 1=x,2=y,3=z)
        // Construct t from gradient components
        if coordIndex eq 1 then
            tP := [0, -gF_P[3], gF_P[2]];
            partDeriv1 := 2; partDeriv2 := 3;
        elif coordIndex eq 2 then
            tP := [-gF_P[3], 0, gF_P[1]];
            partDeriv1 := 1; partDeriv2 := 3;
        else // coordIndex eq 3
            tP := [-gF_P[2], gF_P[1], 0];
            partDeriv1 := 1; partDeriv2 := 2;
        end if;

        // Working in affine coordinates, we impose vanishing of Hessian
        for partCase in [1,2] do
            finalRow := [];
            for k in [1..N] do
                Hk := HessianOfMonomialAt(mon_basis[k], P);
                if partCase eq 1 then
                    ActualH := gF_P[partDeriv1] * Hk - Evaluate(Derivative(mon_basis[k], partDeriv1), Coordinates(P)) * HessF;
                else
                    ActualH := gF_P[partDeriv2] * Hk - Evaluate(Derivative(mon_basis[k], partDeriv2), Coordinates(P)) * HessF;
                end if;
                s := &+[ tP[i] * ActualH[i,j] * tP[j] : i,j in [1..3] ];
                Append(~finalRow, s);
            end for;
            Append(~rows, finalRow);
        end for;
	return rows;
    end function;

    if P[1] ne 0 then rows := rows cat SecondOrderRow(1, gF_P, HessF); end if;
    if P[2] ne 0 then rows := rows cat SecondOrderRow(2, gF_P, HessF); end if;
    if P[3] ne 0 then rows := rows cat SecondOrderRow(3, gF_P, HessF); end if;

    // 4) Solve the linear system for coefficients of G
    M := Matrix(A, rows);
    Nsp := Nullspace(Transpose(M));
    if Dimension(Nsp) ne 1 then
        error "No unique (up to scale) cubic satisfies the prescribed conditions.";
    end if;

    v := Basis(Nsp)[1];
    coeffs := Eltseq(v);

    // Construct cubic G = sum coeffs[k]*mon_basis[k]
    G := &+[ coeffs[k] * mon_basis[k] : k in [1..N] ];
    return G;
end function;



// ============================================================
// PullBackToSubfieldByLinearAlgebra(A, K, emb, k)
//
// INPUT:
//   A   : subfield of K with embedding emb : A ? K
//   K   : field extension of A
//   emb : embedding A ? K
//   k   : element of K in image of emb
//
// OUTPUT:
//   Unique a ? A such that emb(a) = k
// ============================================================
function PullBackToSubfieldByLinearAlgebra(A, K, emb, k)
    QA := Rationals();
    dimK := Degree(K);

    n := Degree(A);
    a := A.1;
    basisA := [a^i : i in [0..n-1]];

    V, map := KSpace(K, QA);

    // Matrix of coordinates of emb(basisA) in K over Q
    images_coords := [map(emb(b)) : b in basisA];
    mat := Matrix(QA, n, dimK, [images_coords[i][j] : j in [1..dimK], i in [1..n]]);

    rhs := Vector(QA, map(k));

    bool, coeffs := IsConsistent(mat, rhs);
    if not bool then
        error "Element is not in the image of the subfield";
    end if;

    // Reconstruct element in A
    return &+[coeffs[i]*basisA[i] : i in [1..n]];
end function;


// ============================================================
// BaseChangeCubic(GA, LocalFields, Maps)
//
// INPUT:
//   GA          : cubic polynomial over number field A
//   LocalFields : list of local fields (factors of A \otimes Q2)
//   Maps        : list of embeddings A ? LocalFields[i]
//
// OUTPUT:
//   List of base-changed cubics over each LocalField
// ============================================================
function BaseChangeCubic(GA, LocalFields, Maps)
    results := [* *];

    for i in [1..#LocalFields] do
        L := LocalFields[i];
        phi := Maps[i];

        RL<X,Y,Z> := PolynomialRing(L, 3);

        // Base change GA: apply phi to coefficients, keep variables as X,Y,Z
        MapCoords := hom<Parent(GA)->RL | [X, Y, Z]>;
        mons := Monomials(GA);
        mons_L := [MapCoords(m) : m in mons];
        coefs_L := [phi(c) : c in Coefficients(GA)];

        Append(~results, &+[mons_L[i] * coefs_L[i] : i in [1..#mons_L]]);
    end for;

    return results;
end function;

// ============================================================
// EvaluateRationalFunctionOnGaloisOrbitDivisor(f, D)
//
// INPUT:
//   f : non-zero rational function on curve C
//   D : divisor on C, Galois-stable and supported away from div(f)
//
// OUTPUT:
//   The value f(D) = ? N_{L_i/K}(f(P_i))^{n_i} in the base field K,
//   where each point P_i is a representative of a Galois orbit
//   appearing in D and L_i is a field of definition for P_i
// ============================================================
function EvaluateRationalFunctionOnGaloisOrbitDivisor(f, D)
    K := BaseRing(Curve(D));
    result := K!1;

    supp, mults := Support(D);

    for i in [1..#supp] do
        P := supp[i];
        n := mults[i];

        Q := RepresentativePoint(P);
        val := Evaluate(f, Q);
        if val eq 0 then
            error "Function f has a zero/pole at point", P;
        end if;

        // Norm down to base field if needed
        if Parent(val) ne K then
            N := Norm(val);
        else
            N := val;
        end if;

        result *:= N^n;
    end for;

    return result;
end function;

