/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.CM.Sigma.PadicSeriesDefs
import Zeta23Arithmetic.Lib.DiscreteSeries.CuspKernel.BesselSchurBound
import Zeta23Arithmetic.Lib.Weil.Periods.DegreeOfT

/-! General lemmas of group theory (textbook or folklore).

This file: Index of a finite product of subgroups is the product of indices. -/

lemma index_pi_univ {I G} [Fintype I] [∀ i, Group (G i)] H :
    (@Subgroup.pi I G _ .univ H).index = ∏ i, (H i).index :=
  (Nat.card_congr (QuotientGroup.leftRel_pi H ▸ Setoid.piQuotientEquiv _) ▸ Nat.card_pi :)
