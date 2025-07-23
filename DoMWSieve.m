//===================================================
// Run the Mordell-Weil sieve on X_{E_i} for i=1,2,4
//===================================================

load "ModelsXE.m";
load "Generators.m";
load "MWSieve.m";
load "Saturation.m";

"Checking saturation";
"=== X_{E_1} ===";
sat1 := BoundIndex(XE1_alternativemodel, RetrieveGenerators(1) : TargetList := [2, 3, 7, 11, 29], Bound := 100 );
"The subgroup <D> is saturated at least at the following primes:", sat1;

"=== X_{E_2} ===";
sat2 := BoundIndex(XE2, RetrieveGenerators(2) : TargetList := [2, 3, 37]);
"The subgroup <D_1, D_2> is saturated at least at the following primes:", sat2;

"=== X_{E_4} ===";
sat4 := BoundIndex(XE4, RetrieveGenerators(4) : TargetList := [2, 3, 5]);
"The subgroup <D_1, D_2> is saturated at least at the following primes:", sat4;


//===================================================
// X_{E_1}
//===================================================
"=== X_{E_1} ===";
X := XE1_alternativemodel;
P0 := X![0,1,0];
gens := RetrieveGenerators(1);
p := 41;
MWSievePts := MWSieve(X, P0, gens, p, [53, 71] : SaturatedPrimes := sat1 );
print "All rational points on X_{E_1} lie in the following residue classes mod", p, ":", [P[1] : P in MWSievePts] ;


//===================================================
// X_{E_2}
//===================================================
"=== X_{E_2} ===";
X := XE2;
P0 := X![0,1,0];
gens := RetrieveGenerators(2);
p := 73;
MWSievePts := MWSieve(X, P0, gens, p, [] : SaturatedPrimes := sat2);
print "All rational points on X_{E_2} lie in the following residue classes mod", p, ":", [P[1] : P in MWSievePts] ;


//===================================================
// X_{E_4}
//===================================================
"=== X_{E_4} ===";
X := XE4;
P0 :=  X![0,1,0];
gens := RetrieveGenerators(4);
p := 31;
MWSievePts := MWSieve(X, P0, gens, p, [3] : SaturatedPrimes := {2, 3, 5, 7, 11} );
print "All rational points on X_{E_2} lie in the following residue classes mod", p, ":", [P[1] : P in MWSievePts] ;
