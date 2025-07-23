# MAGMA Code for: On 7-adic Galois Representations for Elliptic Curves over Q

This repository contains MAGMA code accompanying the article  
**"On 7-adic Galois representations for elliptic curves over Q."**

Most of the relevant theoretical background is explained in the paper:  
*Twists of X(7) and primitive solutions to x² + y³ = z⁷*  
by Poonen, Schaefer, and Stoll.

---

## Goals of the Code

- **Lemma 2.11**: Show that any elliptic curve E/Q with mod 49 image in Gns#(49) satisfies _j(E) ≡ 0 mod 49_.
- **Isomorphisms of Galois representations**: Verify isomorphisms among the Galois representations arising from modular forms using the Sturm bound (Section 4).
- **Proposition 4.17**: Prove that the elliptic curve E associated with a specific mod 7 modular form _f_ has complex multiplication.
- **Model Computations**: Compute models for the curves XE1–XE4 and for the corresponding j-maps.
- **2-Descent**: Compute the rank of the Jacobians of the curves XE1-XE4 via two-descent.
- **Mordell–Weil Sieve**: Restrict the sets of Fₚ-rational points on the curves XE1, XE2, XE4 that are reductions of Q-rational points.
- **Chabauty–Coleman Method**: Determine rational points on XE1, XE2, XE4 using Coleman integration.

See Section 6 of the article for details on two-descent, the Mordell-Weil sieve, and Coleman integration.

---

## Running the Code

Download the full folder. The following external repositories are also required:

- https://github.com/jtuitman/Coleman
- https://github.com/davidzywina/OpenImage

### Files and Their Roles

- `49.147.9.a.1.m`: Proves Lemma 2.11 using a model of X_ns#(49) from the LMFDB (https://beta.lmfdb.org/ModularCurve/Q/49.147.9.a.1/).
- `SturmBound.m`: Verifies isomorphisms between representations coming from modular form (see Section 4).
- `EllipticCurveOverQrootminus7.m`: Proves Proposition 4.17 by computing the extension degree [K(E[7]) : K], where K = ℚ(√–7).
- `ModelsXE.m`: Computes models of XE1–XE4 and the corresponding j-maps.
- `DoDescent.m`: Performs 2-descent on the Jacobians of XE1-XE4 to show that the ranks of J(XE1), J(XE2), J(XE3), J(XE4) are respectively 1, 2, 3, 2. Further computes a finite-index subgroup of J(Q) in each case. Requires:
  - `ModelsXE.m`
  - `TwoDescent.m` (calls `Cubic.m`, `LinearAlgebra.m`, `LocalConditions.m`)
- `VerifyGenerators.m`: The file VerifyGenerators.m verifies that the points in J(XE1)(Q), J(XE2)(Q) and J(XE4)(Q) hard-coded in Generators.m generate a subgroup that contains the one found by DoDescent.m. This ensures that the subgroup used in the Mordell–Weil sieve is large enough to capture all known rational points.
- `DoMWSieve.m`: Runs the Mordell–Weil sieve. The algorithm computes a small set of F_p-rational points on each curve, containing the reductions modulo p of all Q-rational points. The prime p is chosen to be suitable for the Coleman integration performed in the next step. The number of points in this set always matches the expected number of Q-rational points. Requires:
  - `ModelsXE.m`
  - `Generators.m` (returns generators of a subgroup Z ⊆ J(Q))
  - `Saturation.m` (checks saturation of Z at suitable primes)
  - `MWSieve.m` (actual Mordell-Weil sieve)
- `ChabautyColeman.m`: Computes rational points on XE1, XE2, XE4 using the Chabauty-Coleman method. The algorithm computes the number of points in each p-adic residue disc centered at the points found by DoMWSieve.m. The output confirms that each disc contains exactly one Q-point, thereby verifying that the claimed Q-rational points are indeed the only rational points on the curve.
  - Needs the implementation of Coleman integrals provided by https://github.com/jtuitman/Coleman.
- `FinalThueStep.m`: The output of FinalThueStep.m is a list of j-invariants including those of the rational points on the modular curve corresponding to each of the groups C_ns^+(49), G_{sp}^#(49), and G_{ns}^#(49). The algorithm verifies that these j-invariants correspond to elliptic curves with complex multiplication and provides the order of CM in each case. Note that these lists may include additional j-invariants beyond those corresponding to rational points; for further details, see the proof of Corollary 3.7.
  - Place inside the _main_ folder from repository https://github.com/davidzywina/OpenImage.


