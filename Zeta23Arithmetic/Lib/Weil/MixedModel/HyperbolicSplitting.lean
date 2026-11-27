/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.Weil.MixedModel.ZeroTermLaw

/-! Part of: Schrödinger and mixed models of the Weil representation; action of parabolic subgroups
(known result; see Lib.Weil.MixedModel.ZeroTermLaw).

This file: Standard polarisation of the hyperbolic space as a splitting. -/

/-- The splitting of hyperbolic space of rank 2p over the zero space, with l the first p and k
the last p basis vectors. -/
noncomputable def hyperbolicSplitting E p [Field E] [CMType E] [WeilData E] [Fintype p] :
  (hypSpace E p).Splitting (stdSpace E Empty)
  p := by use .fromRows 0 1, .fromRows 1 0, 0 <;> first | (ext ⟨⟩; done) | simp +arith
