/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.Adelic.Unitary.SpaceGram

/-! General lemmas of linear algebra and matrices (textbook or folklore).

Part of: Adelic Weil representation of a unitary group and the invariant theta functional (known
result; see Lib.Weil.DualPair.PairSplitting).

This file: The element of an adelic unitary group with a given isometric matrix. -/


variable {E} [Field E] [NumberField E] [NumberField.IsCMField E] {n} [Fintype n] {s : n → _}

/-- The element of the adelic unitary group of signs s given by an adelic matrix m with m*εm =
ε, ε the standard form. -/
noncomputable def G.ofMat m h := (toUnitary.symm (U.of isUnit_stdForm m h) : G E s)

@[simp] lemma G.mat_ofMat m h : (ofMat m h : G E s).mat = m := rfl
