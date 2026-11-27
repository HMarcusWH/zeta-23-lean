/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.Weil.Unramified.SphericalHecke

/-! Set-up used by: Cusp forms: rapid decay, finite dimension, Poincaré series; algebraic modular
forms.

This file: Two normalisations of the Hecke polynomial are reciprocal to each other. -/

lemma eval_heckePoly {E n} [Field E] [NumberField E] [Fintype n] (w : FinPlace E) t {x} (h :
  x ≠ 0) : (heckePoly w.q (Fintype.card n) t).eval x = x ^ Fintype.card n * heckePolyEval n w t
  x⁻¹ := by erw [Polynomial.eval_finsetSum, Finset.mul_sum]; congr!; simp_all [pow_sub₀]; ring
