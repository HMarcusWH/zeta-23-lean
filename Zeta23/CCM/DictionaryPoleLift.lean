import Zeta23.CCM.DictionaryFiniteExpansion

noncomputable section

namespace Zeta23.CCM

open Matrix Set MeasureTheory
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-! # Finite dictionary pole-channel lift

Phase J1 of the deterministic R003 completion.  This module lifts the already
proved basis pole identity through the finite dictionary expansion.  Only finite
sum algebra is used.
-/

/-- The pole channel of the full finite dictionary is the coefficient
contraction of the fork-owned pole component. -/
theorem dictionaryPoleRHS_dictionaryTest
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    dictionaryPoleRHS (dictionaryTest N u L) =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          ((poleComponent (centeredIndex N i) (centeredIndex N j) L : ℝ) : ℂ) *
          u j := by
  unfold dictionaryPoleRHS
  rw [paperFT_dictionaryTest_eq_basis_sum N u hL (Complex.I / 2),
    paperFT_dictionaryTest_eq_basis_sum N u hL (-Complex.I / 2),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [← dictionaryPoleRHS_basis hL
    (centeredIndex N i) (centeredIndex N j)]
  unfold dictionaryPoleRHS
  ring

end Zeta23.CCM
