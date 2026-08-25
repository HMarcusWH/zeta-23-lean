import Zeta23.CCM.DictionaryArchOffDiagonal
import Zeta23.CCM.DictionaryArchDiagonalEvaluation

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set

/-! # All-entry archimedean packaging

This module is Phase H of the deterministic R003 completion.  The diagonal and
off-diagonal analytic work is already compiler-proved upstream; the only role
here is to package those two cases into the uniform basis contracts consumed by
the finite dictionary lift.
-/

/-- Every dictionary basis entry has an integrable full-`mu` literature
integrand.  The proof is only a diagonal/off-diagonal dispatch. -/
theorem integrable_paperFT_dictionaryBasisTest_mul_mu
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    Integrable (fun τ : ℝ =>
      Zeta23.paperFT (dictionaryBasisTest n m L) (τ : ℂ) *
        (Zeta23.mu τ : ℂ)) := by
  by_cases hnm : n = m
  · subst m
    exact integrable_paperFT_dictionaryBasisTest_diag_mul_mu hL n
  · exact integrable_paperFT_dictionaryBasisTest_mul_mu_of_ne hL hnm

/-- Uniform entrywise literature archimedean identity.  The only diagonal
addition is the scalar identity correction `2*cCorrection(L)`. -/
theorem dictionaryArchRHS_basis
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    dictionaryArchRHS (dictionaryBasisTest n m L) =
      ((-archComponent n m L +
        (if n = m then 2 * cCorrection L else 0) : ℝ) : ℂ) := by
  by_cases hnm : n = m
  · subst m
    simpa using dictionaryArchRHS_basis_diag hL n
  · simpa [hnm] using dictionaryArchRHS_basis_of_ne hL hnm

end Zeta23.CCM
