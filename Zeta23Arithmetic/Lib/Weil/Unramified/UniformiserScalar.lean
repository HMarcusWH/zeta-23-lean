/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.ClassField.HeckeL.AutCharLFunction

/-! Part of: Commutativity of the spherical Hecke algebra of GL_n; Eichler commutation relation
(known result; see Lib.General.LinearAlgebra.ColumnLattices).

This file: Scalar by which a uniformiser acts in the Weil representation. -/

/-- The complex number χ(ϖ_w)·q_w^{k/2}, where χ = `AutChar.spaceChar` a k is the Hecke character x
↦ a(x/x̄)υ(x)^{−k} and ϖ_w the chosen uniformiser at w. -/
noncomputable def AutChar.frobValue {E : Type} [Field E] [CMType E] [WeilData E] (a : AutChar E) n
    [Fintype n] w := (a.spaceChar (Fintype.card n)).atUnif w * √w.q ^ Fintype.card n
