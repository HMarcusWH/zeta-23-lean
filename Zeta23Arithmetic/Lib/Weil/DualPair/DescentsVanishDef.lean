/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.Weil.DualPair.Lift
import Zeta23Arithmetic.Lib.Weil.DualPair.PairReal

/-! A step of the proof of: Theta kernels of unitary dual pairs: functoriality, seesaw, growth,
rapid decay.

This file: Predicate: all theta descents with data vacuum at given places vanish. -/

/-- All descents g ↦ ∫θ(ω_{a,1}(g,h)f)Y(h)dh of Y from U(V) to U(W) vanish, for data f that are
the vacuum at the places of S ∪ S̄. -/
def DescentsVanish {E n m} [Field E] [CMType E] [WeilData E] [Fintype n] [Fintype m] {s t} (W :
  Space E n s) (V : Space E m t) a S Y := ∀ f, Space.projOn _ S f = f →
  Space.lift (pairThetaKer W V a 1).swap f Y = 0
