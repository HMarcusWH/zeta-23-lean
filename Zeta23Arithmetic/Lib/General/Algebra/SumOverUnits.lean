/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.General.NumberTheory.ClassNumberBound

/-! General lemmas of commutative and general algebra (textbook or folklore).

This file: Sum over Z/N, N prime, splits as zero term plus sum over units. -/

lemma sum_eq_add_sum_units {N} [Fact N.Prime] {V} [AddCommMonoid V] (f : ZMod N → V) : ∑ c, f c =
  f 0 +
  ∑ c : _ˣ, f c.1 := by simp [Fintype.sum_eq_add_sum_subtype_ne f 0, ← unitsEquivNeZero.sum_comp]
