// ============================================================
// This script implements linear algebra in the F_2-vector spaces A* / A^{*2} Q*
// and its local version, (A \otimes Q_2)* / (A \otimes Q_2)^{*2} Q_2*.
// It also describes the localisation map from the former to the latter.
// ============================================================

/*
============================================================================
LINEAR ALGEBRA IN THE DESCENT GROUP
============================================================================ 
*/

// ============================================================
// SimplifyInAquot
//
// INPUT:
//   a  : an element of the number field A
//
// OUTPUT:
//   a1 : a simplified representative of the class of a in 
//        A* / (A^{*2} · Q*), obtained by:
//          (1) clearing rational denominators,
//          (2) multiplying odd-power primes by their residue characteristic,
//          (3) removing even-power prime divisors when principal
// ============================================================
function SimplifyInAquot(a)
    a1 := Numerator(a); // Extract the numerator
    A := Parent(a1);
    O := MaximalOrder(A);
    I := ideal< O | a1 >;
    fac := Factorization(I);

    PrimesAlreadySeen := [];

    // Multiply a1 by q for each q dividing an odd power of a prime ideal in its factorization
    for pair in fac do
        P, e := Explode(pair);
        if IsOdd(e) then
            q := Characteristic(ResidueClassField(P));
            if not q in PrimesAlreadySeen then
                Append(~PrimesAlreadySeen, q);
                a1 *:= q;
            end if;
        end if;
    end for;

    // Refactor the modified a1
    I2 := ideal< O | a1 >;
    fac2 := Factorization(I2);

    // Simplify using principal ideals
    for pair in fac2 do
        P, e := Explode(pair);
        isPrin, p := IsPrincipal(P);
        if isPrin then
            if IsEven(e) then
                a1 *:= p^(-e);
            else
                a1 *:= p^(1 - e);
            end if;
        end if;
    end for;

    return a1;
end function;

// ============================================================
// UnitExponentsParityBrute
// 
// Given a unit u in the number field A, returns parity of its exponents in a unit basis modulo squares.
//
// INPUT:
// - u  : a unit in the maximal order of the number field A
// - U  : abstract unit group of O
// - mU : isomorphism from U to the unit group of A
//
// OUTPUT:
// - A list [e₁, ..., e_r] ∈ {0,1}^r such that u * g₁^{e₁} * ... * g_r^{e_r} ∈ A^{*2}
//
// NOTE:
// - Brute-force method: tries all 2^r combinations.
// ============================================================
function UnitExponentsParityBrute(u, U, mU)
    A := Parent(u);

    // Image of the unit group generators under mU
    gens := [ mU(U.i) : i in [1..Ngens(U)] ];
    r := #gens;

    // Brute-force search over all 2^r possible combinations of exponents modulo 2
    for bits in [0..2^r - 1] do
        u0 := A!1;
        
        // Build product of generators according to the bit pattern
        for i in [1..r] do
            if ((bits div 2^(i-1)) mod 2) eq 1 then
                u0 *:= gens[i];
            end if;
        end for;

        // Check if u * u0 is a square
        if IsSquare(u * u0) then
            // Extract parity vector
            e := [ ((bits div 2^(i-1)) mod 2) : i in [1..r] ];
            
            // If U.1 has order divisible by 4, return all exponents
            // Otherwise, drop the first one (the torsion part: if the
            // order of the torsion subgroup is not divisible by 4,
            // every finite-order unit is rational modulo squares)
            return (Order(U.1) mod 4 ne 0) select e[2..#e] else e;
        end if;
    end for;

    error "No suitable exponent vector found.";
end function;


// ========================================================
// Init2AdicData
// 
// Initialize 2-adic data for a number field A.
//
// INPUT:
// - A   : a number field
//
// OUTPUT:
// - P   : list of prime ideals of A lying over 2
// - gens: generators of these prime ideals (assumed to be principal)
// - U   : abstract unit group of the ring of integers O_A
// - mU  : isomorphism from U to the unit group of O_A
//
// ========================================================
function Init2AdicData(A)
    // Get the maximal order of the number field A
    O := MaximalOrder(A);

    // Compute all primes of O above 2
    P := [ t[1] : t in Decomposition(O, 2) ];

    // Get generators of the corresponding principal ideals
    gens := [];
    for p in P do
        _, gen := IsPrincipal(p);  // gen is a generator of the ideal p
        Append(~gens, gen);
    end for;

    // Get the unit group of O and the associated map
    U, mU := UnitGroup(O);

    return P, gens, U, mU;
end function;


// ========================================================
// PresentationModSquares
//
// Represent an element of A* modulo squares and Q*.
//
// INPUT:
// - a    : an element of A*, only divisible by primes above 2
// - P    : list of prime ideals of A over 2
// - gens : generators of the prime ideals P
// - U    : abstract unit group of O_A
// - mU   : isomorphism from U to the unit group of O_A
//
// OUTPUT:
// - A binary vector: mod 2 valuations at primes over 2,
//   followed by the parities of unit exponents. This gives
//   an explicit presentation of a in terms of known generators,
//   modulo squares and rational scalars.
//
// ========================================================
function PresentationModSquares(a, P, gens, U, mU)
    A := Parent(a);
    r := #P;

    // Simplify a to a representative in A* / (A^{*2} · Q^*)
    a := SimplifyInAquot(a);

    // Compute mod 2 valuations at each prime in P
    v := [ Valuation(a, p) mod 2 : p in P ];

    // Remove the contribution of primes appearing in the factorisation of a
    // The result is a unit
    u := A!a;
    for i in [1..r] do
        if v[i] eq 1 then
            u /:= gens[i];
        end if;
    end for;

    // Find the parity of unit exponents such that u * product(gens^exponent) is a square
    unit_parities := UnitExponentsParityBrute(u, U, mU);

    // Concatenate valuations and unit parities to form the full presentation
    return v cat unit_parities;
end function;


// ========================================================
// AllRepresentatives
//
// Compute representatives for the quotient A* / (A^{*2} · Q*).
//
// INPUT:
// - P    : list of prime ideals of A over 2
// - gens : generators of the prime ideals P
// - U    : abstract unit group of O_A
// - mU   : isomorphism from U to the unit group of O_A
//
// OUTPUT:
// - A list of elements of A* representing all classes in
//   A* modulo squares and rational scalars.
//
// ========================================================
function AllRepresentatives(P, gens, U, mU)
    r := #gens;

    // Determine which unit generators to use depending on torsion order
    // As above, if 4 does not divide the torsion order, we don't need
    // to take into account the roots of unity, because they are
    // rational modulo squares
    unit_gens := (Order(U.1) mod 4 ne 0)
        select [ mU(U.i) : i in [2..Ngens(U)] ]
        else [ mU(U.i) : i in [1..Ngens(U)] ];
    s := #unit_gens;

    reps := [];

    // Loop through all combinations of exponent vectors mod 2
    for x in CartesianPower({0,1}, r + s) do
        p_part := &*[ gens[i]^x[i] : i in [1..r] ];                      // product over prime generators
        u_part := &*[ unit_gens[j]^x[r + j] : j in [1..s] ];            // product over unit generators
        Append(~reps, p_part * u_part);                                 // full representative
    end for;

    return reps;
end function;

// ========================================================
// AreEquivalentModuloSquaresAndRationals
//
// Decide whether two elements are equal modulo squares and
// rational scalars in the number field A.
//
// INPUT:
// - h1, h2 : elements of A, assumed to lie in O and have norm
//           equal to a power of 2
//
// OUTPUT:
// - true if h1 and h2 are equal modulo A^{*2} · Q*
//
// ========================================================
function AreEquivalentModuloSquaresAndRationals(h1, h2)
	return &or[
		IsSquare(h1*h2),
		IsSquare(-h1*h2),
		IsSquare(2*h1*h2),
		IsSquare(-2*h1*h2)
	];
end function;

// ========================================================
// RemoveEquivalentModSquaresAndRationals
//
// Remove duplicates modulo squares and rational scalars
// from a list of elements in the ring of integers of A.
//
// INPUT:
// - H     : list of elements of O_A
// - P     : primes above 2 in A
// - gens  : generators of those primes
// - U, mU : unit group data
//
// OUTPUT:
// - A list containing exactly one representative for each
//   class in A^* / (A^{*2} · Q^*) of elements of H
//
// ========================================================
function RemoveEquivalentModSquaresAndRationals(H, A, P, gens, U, mU)
    unique := [];

    // Iterate over all elements in H
    for h in H do
        // Check if h is NOT equivalent modulo squares and rationals to any element in unique
        if forall{u : u in unique | not AreEquivalentModuloSquaresAndRationals(h, u)} then
            Append(~unique, h);  // Add h to unique if it is genuinely new
        end if;
    end for;

    return unique;
end function;


/*
============================================================================
LINEAR ALGEBRA IN Z := (A \otimes Q_2)* / (A \otimes Q_2)^{*2} Q_2*
============================================================================
*/

// ========================================================
// LocalDecomposition
//
// Compute the 2-adic completions of a number field A,
// together with the embeddings of A into each completion.
//
// INPUT:
// - A      : a number field
// - p      : (optional) prime number to decompose (default: 2)
// - prec   : (optional) 2-adic precision (default: 100)
//
// OUTPUT:
// - list   : list of local fields A_i = Q_2[x]/(g_i)
// - maps   : list of embeddings A → A_i
//
// ========================================================
function LocalDecomposition(A : p := 2, prec := 100)
    Qp := pAdicField(p, prec);          // Create p-adic field Q_p with given precision
    Rp<x> := PolynomialRing(Qp);       // Polynomial ring over Q_p
    h := Rp!DefiningPolynomial(A);     // Defining polynomial of the number field A
    fac := Factorization(h);            // Factor polynomial over Q_p

    fields := [* *];                   // List to hold local fields
    maps   := [* *];                   // List to hold embeddings A -> local fields

    for f in fac do
        g := f[1];
        B := LocalField(Qp, g);        // Local field defined by factor g
        Append(~fields, B);
        Append(~maps, hom< A -> B | B.1 >); // Embedding from A to B sending generator to B.1
    end for;

    return fields, maps;
end function;


/*
List of representatives of Q_2^* / Q_2^{*2}. This is used
several times as follows: u = v modulo (Q_2* and squares)
is equivalent to u = r*v modulo squares for some r in reps
*/
reps := [1, 3, 5, 7, 2, 6, 10, 14];

// ========================================================
// EqualInZ
//
// Decide whether two elements are equal in the group
// (A \otimes Q_2)^* / (A \otimes Q_2)^{*2}·Q_2^*.
//
// INPUT:
// - x, y   : elements of (A \otimes Q_2)^*
// - reps   : a system of representatives for Q_2* / Q_2^{*2}
//
// OUTPUT:
// - true iff x = y in (A \otimes Q_2)^* / (A \otimes Q_2)^{*2}·Q_2^*
//
// ========================================================
function EqualInZ(x, y, reps)
    assert #x eq #y;  // Ensure vectors x and y have the same length

    for r in reps do
        // Check if for all components i, r * x[i] / y[i] is a square
        if forall{i : i in [1..#x] | IsSquare(r * x[i] / y[i])} then
            return true;
        end if;
    end for;

    return false;
end function;

// ========================================================
// AreLinearlyIndependent
//
// Check whether the given vectors in Z are linearly independent.
//
// INPUT:
// - v    : a list of vectors over Z
// - reps : a system of representatives for Q_2* / Q_2^{*2}
//
// OUTPUT:
// - true iff the vectors are linearly independent
//
// ========================================================
function AreLinearlyIndependent(v, reps)
    n := #v;
    if n eq 0 then 
        return true; 
    end if;

    d := #v[1];
    assert forall{x : x in v | #x eq d};  // Ensure all vectors have the same dimension

    // Iterate over all non-empty subsets of the set {1..n}
    for coeffs in Subsets({1..n}) do
        if #coeffs eq 0 then 
            continue; 
        end if;

        // Start with the identity vector (all ones)
        prod := [ Parent(v[1][1])!1 : _ in [1..d] ];

        // Multiply components for vectors indexed by coeffs
        for i in coeffs do
            for j in [1..d] do
                prod[j] *:= v[i][j];
            end for;
        end for;

        // If the product equals the identity vector (mod reps), then vectors are dependent
        if EqualInZ(prod, [1 : _ in [1..d]], reps) then
            return false;
        end if;
    end for;

    // No nontrivial product equals identity => vectors are independent
    return true;
end function;

// ========================================================
// IsInMultiplicativeSpan
//
// Test whether an element of Z lies in the multiplicative span of a given list.
//
// INPUT:
// - x         : an element of Z
// - generators: a list of elements of Z
// - reps      : a system of representatives for Q_2* / Q_2^{*2}
//
// OUTPUT:
// - true iff x is in the multiplicative span of the generators
//
// ========================================================
function IsInSpanZ(x, generators, reps)
    n := #generators;
    if n eq 0 then
        return EqualInZ(x, [* One(Parent(x[i])) : i in [1..#x] *], reps);
    end if;

    d := #x;
    assert forall{y : y in generators | #y eq d};

    for coeffs in Subsets({1..n}) do
        // Start with the identity element
        w := [* One(Parent(x[i])) : i in [1..d] *];

        for i in coeffs do
            for j in [1..d] do
                w[j] *:= generators[i][j];
            end for;
        end for;

        // Compare with x
        if EqualInZ(w, x, reps) then
            return true;
        end if;
    end for;

    return false;
end function;

// ========================================================
// MaximalLinearlyIndependentSubset
//
// Extract a basis from a list of vectors in Z.
//
// INPUT:
// - vectors : a list of elements of Z
// - reps      : a system of representatives for Q_2* / Q_2^{*2}
//
// OUTPUT:
// - a list of vectors forming a basis of the Z-subgroup generated by the input
//
// ========================================================
function BasisInZ(vectors, reps)
    basis := [];

    for x in vectors do
        if not IsInSpanZ(x, basis, reps) then
            Append(~basis, x);
        end if;
    end for;

    return basis;
end function;