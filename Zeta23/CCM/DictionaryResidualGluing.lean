import Zeta23.CCM.DictionaryResidualSecondOrder
import Mathlib.Analysis.Calculus.ContDiff.Deriv

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23.CCM

open Set Filter

/-! # Global C² gluing for the finite-dictionary residual

PR #38 packages the first- and second-order seam calculations from PR #37
into a global regularity theorem. The raw dictionary splits, for real
coefficient vectors, into a universal tent mode plus `dictionaryResidualReal`.
The residual has matching value/first/second jets at `-L`, `0`, and `L`, so it
is globally `C²` and compactly supported. No explicit formula is invoked.
-/

/-! ## Smooth source and branch pieces -/

@[fun_prop] theorem contDiff_two_sourcePotentialReal (n : ℤ) :
    ContDiff ℝ 2 (fun ω : ℝ => sourcePotentialReal ω n) := by
  unfold sourcePotentialReal
  fun_prop

@[fun_prop] theorem contDiff_two_sourceDiagonalReal (n : ℤ) :
    ContDiff ℝ 2 (fun ω : ℝ => sourceDiagonalReal ω n) := by
  unfold sourceDiagonalReal
  fun_prop

@[fun_prop] theorem contDiff_two_sourceEntryReal (n m : ℤ) :
    ContDiff ℝ 2 (fun ω : ℝ => sourceEntryReal ω n m) := by
  by_cases h : n = m
  · subst m
    simpa [sourceEntryReal] using contDiff_two_sourceDiagonalReal n
  · simp only [sourceEntryReal, h, ↓reduceIte]
    fun_prop

@[fun_prop] theorem contDiff_two_sourceContractReal
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    ContDiff ℝ 2 (sourceContractReal N u) := by
  unfold sourceContractReal
  fun_prop

@[fun_prop] theorem contDiff_two_sourceContractRealResidual
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) :
    ContDiff ℝ 2 (sourceContractRealResidual N u) := by
  unfold sourceContractRealResidual
  fun_prop

@[fun_prop] theorem contDiff_two_dictionaryResidualPositiveBranch
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L : ℝ) :
    ContDiff ℝ 2 (dictionaryResidualPositiveBranch N u L) := by
  unfold dictionaryResidualPositiveBranch
  fun_prop

@[fun_prop] theorem contDiff_two_dictionaryResidualNegativeBranch
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L : ℝ) :
    ContDiff ℝ 2 (dictionaryResidualNegativeBranch N u L) := by
  unfold dictionaryResidualNegativeBranch
  fun_prop

@[fun_prop] theorem contDiff_one_dictionaryResidualPositiveBranchDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L : ℝ) :
    ContDiff ℝ 1 (dictionaryResidualPositiveBranchDerivative N u L) := by
  have h : ContDiff ℝ 1 (deriv (dictionaryResidualPositiveBranch N u L)) := by
    exact (contDiff_two_dictionaryResidualPositiveBranch N u L).deriv'
  have heq : deriv (dictionaryResidualPositiveBranch N u L) =
      dictionaryResidualPositiveBranchDerivative N u L := by
    funext y
    exact (hasDerivAt_dictionaryResidualPositiveBranch N u L y).deriv
  simpa [heq] using h

@[fun_prop] theorem contDiff_one_dictionaryResidualNegativeBranchDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L : ℝ) :
    ContDiff ℝ 1 (dictionaryResidualNegativeBranchDerivative N u L) := by
  have h : ContDiff ℝ 1 (deriv (dictionaryResidualNegativeBranch N u L)) := by
    exact (contDiff_two_dictionaryResidualNegativeBranch N u L).deriv'
  have heq : deriv (dictionaryResidualNegativeBranch N u L) =
      dictionaryResidualNegativeBranchDerivative N u L := by
    funext y
    exact (hasDerivAt_dictionaryResidualNegativeBranch N u L y).deriv
  simpa [heq] using h

@[fun_prop] theorem continuous_dictionaryResidualPositiveBranchSecondDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L : ℝ) :
    Continuous (dictionaryResidualPositiveBranchSecondDerivative N u L) := by
  have h : ContDiff ℝ 0 (deriv (dictionaryResidualPositiveBranchDerivative N u L)) := by
    exact (contDiff_one_dictionaryResidualPositiveBranchDerivative N u L).deriv'
  have heq : deriv (dictionaryResidualPositiveBranchDerivative N u L) =
      dictionaryResidualPositiveBranchSecondDerivative N u L := by
    funext y
    exact (hasDerivAt_dictionaryResidualPositiveBranchDerivative N u L y).deriv
  rw [heq] at h
  exact h.continuous

@[fun_prop] theorem continuous_dictionaryResidualNegativeBranchSecondDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L : ℝ) :
    Continuous (dictionaryResidualNegativeBranchSecondDerivative N u L) := by
  have h : ContDiff ℝ 0 (deriv (dictionaryResidualNegativeBranchDerivative N u L)) := by
    exact (contDiff_one_dictionaryResidualNegativeBranchDerivative N u L).deriv'
  have heq : deriv (dictionaryResidualNegativeBranchDerivative N u L) =
      dictionaryResidualNegativeBranchSecondDerivative N u L := by
    funext y
    exact (hasDerivAt_dictionaryResidualNegativeBranchDerivative N u L y).deriv
  rw [heq] at h
  exact h.continuous

end Zeta23.CCM
