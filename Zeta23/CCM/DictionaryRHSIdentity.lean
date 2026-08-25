import Zeta23.CCM.DictionaryArchLift

noncomputable section

namespace Zeta23.CCM

open Matrix Set MeasureTheory
open scoped BigOperators ComplexConjugate ArithmeticFunction

/-! # Deterministic finite-dictionary RHS identity

Phase K of the R003 completion.  All analytic and support obligations have been
discharged by the preceding channel lifts; this module performs only the final
finite algebra identifying the three literature channels with
`dictionaryMatrix = finiteMatrix + 2*cCorrection*I`.
-/

/-- Complex-coefficient deterministic assembly theorem. -/
theorem dictionaryRHS_dictionaryTest_eq_quadraticForm
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    {L : ℝ} (hL : 0 < L) :
    Zeta23.EF.literatureRHS (dictionaryTest N u L) =
      quadraticForm (dictionaryMatrix L N) u := by
  rw [literatureRHS_eq_dictionaryChannels,
    dictionaryPoleRHS_dictionaryTest N u hL,
    dictionaryPrimeRHS_dictionaryTest N u hL,
    dictionaryArchRHS_dictionaryTest N u hL,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  unfold quadraticForm
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [dictionaryMatrix_apply, finiteMatrix_apply]
  unfold entry
  push_cast
  ring

/-- Advertised real-coefficient R003 endpoint. -/
theorem literatureRHS_dictionaryTest_eq_quadraticForm
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L) :
  Zeta23.EF.literatureRHS
    (dictionaryTest N (fun i => (u i : ℂ)) L) =
  quadraticForm
    (dictionaryMatrix L N)
    (fun i => (u i : ℂ)) := by
  exact dictionaryRHS_dictionaryTest_eq_quadraticForm
    N (fun i => (u i : ℂ)) hL

end Zeta23.CCM
