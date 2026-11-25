/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.GLn.SchurModule.SchurMatrix

/-! Part of: Standard basis theorem for Schur (dual Weyl) modules over any ring, with character
(known result; see Lib.GLn.SchurModule.MinorBasis).

This file: Rational representation of a product of GL_n on Weyl's lattice, twisted by
determinants. -/

/-- The monoid homomorphism from ∏_τ GL(n_τ,R) to square matrices sending g to ∏_τ
det(g_τ)^{e_τ} times the Schur matrix of g, for integers e_τ. -/
noncomputable def weylRep {Φ R} [CommRing R] [Fintype Φ] {n : Φ → _}
    [∀ τ, Fintype (n τ)] κ (e : Φ → ℤ) := MonoidHom.mk ⟨fun g : ∀ τ, GL (n τ) R ↦
  (∏ τ, (g τ).det ^ e τ) • schur κ (g · |>.1), by simp⟩ (by simp [mul_zpow, smul_mul_smul])
