//===================================================
// This script verifies the isomorphisms between the 
// Galois representations attached to cusp forms of 
// levels 196, 392, and 784.
//===================================================

//------------------------
// Sturm bound
//------------------------
function SturmBound(k, N)
    m := Integers()!( N * &*[ (1+1/p) : p in PrimeFactors(N) ] );
    return Floor(k * m / 12);
end function;


//------------------------
// Find cusp form by Fourier coefficients
//------------------------
function MatchCuspForm(NewformSpace, WhichCoefficients, CoefficientsValue)
    matches := [f[1] : f in NewformSpace | 
                &and[Coefficient(f[1], WhichCoefficients[i]) eq CoefficientsValue[i] : i in [1..#CoefficientsValue] ]];
    if #matches eq 1 then
        return matches[1];
    elif #matches eq 0 then
        error "No cusp form found!";
    else
        error "More than one cusp form found!";
    end if;
end function;


//------------------------
// Prime splitting of 7 and projections modulo the prime ideals
//------------------------
function PrimeSplittingAt7(f)
    K := Parent(Coefficient(f, 1));
    O := MaximalOrder(K);
    beta := O!(K.1);
    I7 := ideal<O | 7>;
    P := Factorisation(I7);
    p1, p2 := Explode([x[1] : x in P]);
    // Normalise so that beta \equiv 3 mod p1
    if not (beta-3 in p1) then
	p3 := p1;
	p1 := p2;
	p2 := p3;
    end if;
    cf1, proj1 := ResidueClassField(p1);
    cf2, proj2 := ResidueClassField(p2);
    return [* cf1, proj1 *], [* cf2, proj2 *];

end function;


//------------------------
// Check that the coefficient a_n of fA, fB matches with
// that of fC for all n up to (10 times) the Sturm bound
//------------------------
function CheckCongruences(fA, fB, fC, projA, projB, k, N)
    bound := 10 * SturmBound(k, N);
    O := MaximalOrder(Parent(Coefficient(fC, 1)));
    for n in [1..bound] do
        cA := projA(O!Coefficient(fA, n));
        cC := projA(O!Coefficient(fC, n));
        assert cA eq cC;

        cB := projB(O!Coefficient(fB, n));
        cC := projB(O!Coefficient(fC, n));
        assert cB eq cC;
    end for;
    return true;
end function;


//------------------------
// Level 196
//------------------------
chi := DirichletCharacter("196.1");
S := CuspForms(chi, 2);
N := Newforms(S);

f1 := MatchCuspForm(N, [3, 9], [-1, -2]);
f2 := MatchCuspForm(N, [3, 9], [1, -2]);
f3 := MatchCuspForm(N, [11], [4]);

F1, F2 := PrimeSplittingAt7(f3);
CheckCongruences(f1, f2, f3, F1[2], F2[2], 2, 196);


//------------------------
// Level 392: load newforms
//------------------------
chi := DirichletCharacter("392.1");
S := CuspForms(chi, 2);
N := Newforms(S);

//------------------------
// Level 392: first triple
//------------------------
f4 := MatchCuspForm(N, [3, 5, 9], [-3, 1, 6]);
f5 := MatchCuspForm(N, [3, 5, 9], [3, -1, 6]);
f6 := MatchCuspForm(N, [9, 11], [-1, 6]);

F1, F2 := PrimeSplittingAt7(f6);
CheckCongruences(f4, f5, f6, F2[2], F1[2], 2, 392);


//------------------------
// Level 392: second triple
//------------------------
f7 := MatchCuspForm(N, [3, 5, 9], [-1, -1, -2]);
f8 := MatchCuspForm(N, [3, 5, 9], [1, 1, -2]);
f9 := MatchCuspForm(N, [9, 11], [5, -4]);

F1, F2 := PrimeSplittingAt7(f9);
CheckCongruences(f7, f8, f9, F1[2], F2[2], 2, 392);


//------------------------
// Level 784: load newforms
//------------------------
chi := DirichletCharacter("784.1");
S := CuspForms(chi, 2);
N := Newforms(S);

f15 := MatchCuspForm(N, [9, 11, 13], [-2, 3, 2]);
f16 := MatchCuspForm(N, [9, 11, 13], [-2, 3, -2]);
f17 := MatchCuspForm(N, [9, 11], [5, -4]);

f18 := MatchCuspForm(N, [9, 11, 13], [6, 1, 2]);
f19 := MatchCuspForm(N, [9, 11, 13], [6, 1, -2]);
f20 := MatchCuspForm(N, [9, 11], [-1, -6]);

f23 := MatchCuspForm(N, [9, 11, 13], [-2, -3, 6]);
f24 := MatchCuspForm(N, [9, 11, 13], [-2, -3, -6]);
f25 := MatchCuspForm(N, [9, 11], [5, 4]);


//------------------------
// Level 784: check f15, f16, f17
//------------------------
F1, F2 := PrimeSplittingAt7(f17);
CheckCongruences(f15, f16, f17, F1[2], F2[2], 2, 784);


//------------------------
// Level 784: check f18, f19, f20
//------------------------
F1, F2 := PrimeSplittingAt7(f20);
CheckCongruences(f18, f19, f20, F2[2], F1[2], 2, 784);


//------------------------
// Level 784: check f23, f24, f25
//------------------------
F1, F2 := PrimeSplittingAt7(f25);
CheckCongruences(f23, f24, f25, F1[2], F2[2], 2, 784);
