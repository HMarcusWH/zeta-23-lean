/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.General.Algebra.JetChainRule
import Zeta23Arithmetic.Lib.Weil.Fock.EntireTheta

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: The Fischer pairing is preserved by an injective renaming of the variables. -/

/-- The jet pairing P(∂)F(0) of a polynomial P with a power series F over a commutative ring is
unchanged when both are renamed along an injective map of variables. -/
lemma jet_rename {σ τ R} (e : σ ↪ τ) [CommRing R] {P Q} (h : .rename e P = Q) F :
    jet R Q (F.rename e) = jet R P F := h ▸ P.induction_on' (by
  simp [MvPolynomial.rename_monomial, ← Finsupp.embDomain_eq_mapDomain, Finsupp.prod]) (by aesop)
