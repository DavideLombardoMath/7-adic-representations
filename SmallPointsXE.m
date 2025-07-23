//=================================================
// This script computes the rational points of small height 
// on each curve X_{E_i} and the corresponding j-invariants. 
// It also checks that X_{E_2}^-, X_{E_3}^- have no 
// Q_2-rational points
//=================================================


load "ModelsXE.m";

/*
j-invariants of points with small height
*/

"j-invariants of small points on X_{E_1}";
PresumablyComputejInvariants(E1);
"j-invariants of small points on X_{E_2}";
PresumablyComputejInvariants(E2);
"j-invariants of small points on X_{E_3}";
PresumablyComputejInvariants(E3);
"j-invariants of small points on X_{E_4}";
PresumablyComputejInvariants(E4);

XE1 := ModelXE(E1);
XE1m := ModelXEMinus(E1);

XE2 := ModelXE(E2);
XE2m := ModelXEMinus(E2);

XE3 := ModelXE(E3);
XE3m := ModelXEMinus(E3);

XE4 := ModelXE(E4);
XE4m := ModelXEMinus(E4);


/*
Check that X_{E_2}^- and X_{E_3}^- have no 2-adic points
*/
assert not IsLocallySolvable(XE2m, 2);
assert not IsLocallySolvable(XE3m, 2);

/*
Alternatively, check that the local symplectic criterion applies
*/
GaloisRepresentation(E2, 2);
GaloisRepresentation(E3, 2);
