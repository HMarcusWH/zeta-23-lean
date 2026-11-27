/-
Copyright 2026 Anthropic, PBC. Apache License, Version 2.0.
Adapted from the Alpoge/Claude/Anthropic proof, lsernau/grh-lean,
commit 72fead102f663d5c7a407964a13dc0cf9d977207.
Modified: relocated module imports into Zeta23Arithmetic; declarations and
proof bodies retained. ArithmeticOnly additionally omits the final endpoints.
Original license, notice, and attribution in this directory tree.
-/
import Zeta23Arithmetic.Lib.Adelic.CuspForms.DeltaForms

/-! Part of: Twisted theta forms lie on one line (see New.Rows.LineArithmetic).

This file: for products of polynomials, weights add and norm bounds multiply. -/

variable {Φ n : Type} [Fintype Φ] [Fintype n]

/-- F is the polynomial of some coordinate vector ξ of weight κ, and, if p holds, ξ has squared
norm at most b. -/
def HasWeightNormLe (p : Prop) κ F b := ∃ ξ, toPoly (Φ := Φ) n κ ξ = F ∧ (p → weylNormSq ξ ≤ b)

lemma HasWeightNormLe.prod {p ι} {s : Finset ι} {κ F b} :
  (∀ i ∈ s, @HasWeightNormLe Φ n _ _ p (κ i) (F i) (b i)) →
  HasWeightNormLe p (s.sum κ) (s.prod F) (s.prod b) := s.induction_on (by simpa using ⟨weylEval _
  _ 0, by simp [weylKernel, highestPoly, tableauPoly, weylNormSq, PolyRep.star_weylEval]⟩) <| by
  simp_intro _ _ _ i; apply_rw [i]
  exact fun ⟨_, e⟩ ⟨_, f⟩ ↦ e.1 ▸ f.1 ▸ (range_toPoly.ge (by simp [SetLike.mul_mem_graded,
    diagramWeight_add, nablaFam, ← range_toPoly])).imp fun _ z ↦
    ⟨z, by grind [(weylNormSq_le_mul_of_toPoly_eq z).trans, weylNormSq_nonneg, mul_le_mul]⟩
