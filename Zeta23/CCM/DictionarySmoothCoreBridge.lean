import Zeta23.CCM.DictionaryRHSIdentity
import Zeta23.CCM.DictionaryResidualSecondOrderGluing
import Zeta23.WeilEF.Main

noncomputable section

namespace Zeta23.CCM

open Set
open scoped BigOperators

/-!
# Smooth-core explicit-formula bridge

On the codimension-one real coefficient hyperplane
`coefficientSumReal N u = 0`, the universal tent seam vanishes identically.
The production dictionary test is therefore exactly the already-proved `C²`,
compactly supported residual, so the concrete zeta literature explicit formula
applies without any tent mollification or limiting argument.

This module proves only the restricted H0 bridge.  It does not prove the tent
explicit formula, the full dictionary explicit formula, an unrestricted
zero-side matrix identity, positivity, or the Riemann hypothesis.
-/

/-- On the smooth core, the production dictionary test is exactly its smooth residual. -/
theorem dictionaryTest_eq_dictionaryResidualTest_of_coefficientSum_eq_zero
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L)
    (hu : coefficientSumReal N u = 0) :
    dictionaryTest N (fun i => (u i : ℂ)) L = dictionaryResidualTest N u L := by
  funext y
  rw [dictionaryTest_ofReal_eq_tent_add_residual N u hL y]
  simp [hu, dictionaryResidualTest]

/-- The production dictionary itself is an admissible `EF_lit` test on the smooth core. -/
theorem dictionaryTest_admissible_of_coefficientSum_eq_zero
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L)
    (hu : coefficientSumReal N u = 0) :
    ContDiff ℝ 2 (dictionaryTest N (fun i => (u i : ℂ)) L) ∧
      HasCompactSupport (dictionaryTest N (fun i => (u i : ℂ)) L) := by
  rw [dictionaryTest_eq_dictionaryResidualTest_of_coefficientSum_eq_zero N u hL hu]
  exact dictionaryResidualTest_admissible N u hL

/-- Absolute convergence of the concrete zeta zero sum for a smooth-core dictionary test. -/
theorem dictionaryTransform_zero_sum_summable_of_coefficientSum_eq_zero
    (hs : ZetaSeam)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L)
    (hu : coefficientSumReal N u = 0) :
    Summable (fun ρ : (zetaZeros hs).carrier =>
      ((zetaZeros hs).mult ρ : ℂ) *
        dictionaryTransform N (fun i => (u i : ℂ)) L (gammaOf ρ)) := by
  have hadm := dictionaryTest_admissible_of_coefficientSum_eq_zero N u hL hu
  have hEF := Zeta23.WeilEF.EF_lit_zeta hs
  simpa [dictionaryTransform] using
    (hEF (dictionaryTest N (fun i => (u i : ℂ)) L) hadm.1 hadm.2).1

/-- On the smooth core, the concrete zeta zero sum equals the literature RHS. -/
theorem dictionaryTransform_zero_sum_eq_literatureRHS_of_coefficientSum_eq_zero
    (hs : ZetaSeam)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L)
    (hu : coefficientSumReal N u = 0) :
    (∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        dictionaryTransform N (fun i => (u i : ℂ)) L (gammaOf ρ)) =
      Zeta23.EF.literatureRHS (dictionaryTest N (fun i => (u i : ℂ)) L) := by
  have hadm := dictionaryTest_admissible_of_coefficientSum_eq_zero N u hL hu
  have hEF := Zeta23.WeilEF.EF_lit_zeta hs
  simpa [dictionaryTransform] using
    (hEF (dictionaryTest N (fun i => (u i : ℂ)) L) hadm.1 hadm.2).2

/-- H0 endpoint: the smooth-core zeta zero sum is exactly the production dictionary quadratic form. -/
theorem zeroSum_dictionaryTest_zero_sum_eq_quadraticForm
    (hs : ZetaSeam)
    (N : ℕ)
    (u : Fin (2 * N + 1) → ℝ)
    {L : ℝ} (hL : 0 < L)
    (hu : coefficientSumReal N u = 0) :
    (∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        dictionaryTransform N (fun i => (u i : ℂ)) L (gammaOf ρ)) =
      quadraticForm
        (dictionaryMatrix L N)
        (fun i => (u i : ℂ)) := by
  calc
    (∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        dictionaryTransform N (fun i => (u i : ℂ)) L (gammaOf ρ)) =
        Zeta23.EF.literatureRHS (dictionaryTest N (fun i => (u i : ℂ)) L) :=
      dictionaryTransform_zero_sum_eq_literatureRHS_of_coefficientSum_eq_zero
        hs N u hL hu
    _ = quadraticForm
        (dictionaryMatrix L N)
        (fun i => (u i : ℂ)) :=
      literatureRHS_dictionaryTest_eq_quadraticForm N u hL

end Zeta23.CCM

#print axioms Zeta23.CCM.zeroSum_dictionaryTest_zero_sum_eq_quadraticForm
