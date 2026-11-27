/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.GLn.Branching.Branching

/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Continuity of the Schur matrix in its argument. -/

/-- Over a topological commutative ring R, the map sending a tuple g of square matrices to its
Schur matrix S_κ(g) is continuous. -/
@[fun_prop] lemma continuous_schur {Φ n κ R} [Fintype Φ] [∀ τ, Fintype (n τ)] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] : Continuous (@schur Φ R _ _ n n _ _ κ) :=
  .congr (by simp [Matrix.map, MvPolynomial.eval_eq]; fun_prop) fun g ↦
  funext (PolyRep.genericMatrixAt_map_evalMat g) ▸ (schur_map .refl ..).symm
