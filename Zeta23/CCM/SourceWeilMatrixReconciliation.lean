import Zeta23.CCM.CutoffFreeMatrix

noncomputable section

namespace Zeta23.CCM

open MeasureTheory
open scoped Interval ArithmeticFunction

/-!
# G1-B0: source Weil-matrix normalization reconciliation

This module isolates the scalar normalization seam discovered after G1-A.

The Connes--Consani--Moscovici source first defines the archimedean matrix
entry through equation (4.4).  On the diagonal, substituting
`q(U_n,U_n)(x) = 2(1-x/L) cos(2*pi*n*x/L)` yields the regularized primitive
represented below by `sourceEq44GammaL`: the integral with the
`exp(-x/2)` subtraction plus `wCorrection(L)`.

The printed equation (4.14) instead matches the repository's historical
`gammaL`, which contains one additional `cCorrection(L)`.

This file does not declare either source display to be a typo.  It theorem-locks
their exact algebraic relation and proves that the equation-(4.4)-normalized
finite source formula is exactly the independently defined `cutoffFreeMatrix`.

Claim firewall: this is a source-formula normalization reconciliation only.
It does not yet formalize the multiplicative kappa map, PsiSharp, the ambient
external QW_lambda form, form-core density, Rayleigh--Ritz, positivity, Suzuki,
or RH.
-/

/-- Archimedean diagonal primitive obtained from the source equation-(4.4)
normalization after inserting the diagonal hard-window correlation.

The point value at zero is the removable-value convention already used by the
repository's `gammaL`; changing one point does not change the interval
integral. -/
def sourceEq44GammaL (n : ℤ) (L : ℝ) : ℝ :=
  (∫ x in (0 : ℝ)..L,
    (if x = 0 then 1 / 4
    else (Real.cos (2 * Real.pi * (n : ℝ) * x / L) - Real.exp (-x / 2))
      * archDensity x))
  + wCorrection L

/-- The source equation-(4.4) primitive is exactly the independent
cutoff-free primitive. -/
theorem sourceEq44GammaL_eq_cutoffFreeGammaL
    (n : ℤ) (L : ℝ) :
    sourceEq44GammaL n L = cutoffFreeGammaL n L := by
  unfold sourceEq44GammaL cutoffFreeGammaL gammaL
  ring

/-- Exact reconciliation with the printed equation-(4.14) convention:
the historical `gammaL` contains one additional `cCorrection(L)`. -/
theorem gammaL_eq_sourceEq44GammaL_add_correction
    (n : ℤ) (L : ℝ) :
    gammaL n L = sourceEq44GammaL n L + cCorrection L := by
  unfold gammaL sourceEq44GammaL
  ring

/-- Archimedean source entry with the diagonal normalized directly from
source equation (4.4).  The off-diagonal divided-difference channel is
unchanged. -/
def sourceEq44ArchComponent (n m : ℤ) (L : ℝ) : ℝ :=
  if n = m then
    2 * sourceEq44GammaL n L - 2 * betaL n L
  else
    (alphaL m L - alphaL n L) / ((n - m : ℤ) : ℝ)

/-- The equation-(4.4)-normalized archimedean source entry is exactly the
cutoff-free archimedean entry. -/
theorem sourceEq44ArchComponent_eq_cutoffFreeArchComponent
    (n m : ℤ) (L : ℝ) :
    sourceEq44ArchComponent n m L =
      cutoffFreeArchComponent n m L := by
  by_cases h : n = m
  · subst m
    simp [sourceEq44ArchComponent, cutoffFreeArchComponent,
      sourceEq44GammaL_eq_cutoffFreeGammaL]
  · simp [sourceEq44ArchComponent, cutoffFreeArchComponent, h]

/-- The printed equation-(4.14) archimedean convention differs from the
equation-(4.4) source normalization only on the diagonal, by
`2*cCorrection(L)`. -/
theorem archComponent_eq_sourceEq44ArchComponent_add_two_correction
    (n m : ℤ) (L : ℝ) :
    archComponent n m L =
      sourceEq44ArchComponent n m L +
        (if n = m then 2 * cCorrection L else 0) := by
  rw [sourceEq44ArchComponent_eq_cutoffFreeArchComponent,
    cutoffFreeArchComponent_eq_archComponent_sub_two_correction]
  ring

/-- Full finite source formula obtained by combining the equation-(4.4)
archimedean normalization with the already theorem-authoritative pole and
finite prime-power channels. -/
def sourceEq44ReconciledEntry (n m : ℤ) (L : ℝ) : ℝ :=
  poleComponent n m L -
    sourceEq44ArchComponent n m L -
    primeComponent n m L

/-- The source equation-(4.4)-reconciled scalar entry is exactly the
cutoff-free entry. -/
theorem sourceEq44ReconciledEntry_eq_cutoffFreeEntry
    (n m : ℤ) (L : ℝ) :
    sourceEq44ReconciledEntry n m L = cutoffFreeEntry n m L := by
  rw [sourceEq44ReconciledEntry, cutoffFreeEntry,
    sourceEq44ArchComponent_eq_cutoffFreeArchComponent]

/-- Full centered finite matrix in the source equation-(4.4) normalization. -/
def sourceEq44ReconciledMatrix (L : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  fun i j =>
    (sourceEq44ReconciledEntry
      (centeredIndex N i) (centeredIndex N j) L : ℂ)

@[simp] theorem sourceEq44ReconciledMatrix_apply
    (L : ℝ) (N : ℕ) (i j : Fin (2 * N + 1)) :
    sourceEq44ReconciledMatrix L N i j =
      (sourceEq44ReconciledEntry
        (centeredIndex N i) (centeredIndex N j) L : ℂ) := rfl

/-- **G1-B0 production endpoint.**

The full centered finite source formula normalized directly from equation
(4.4) is exactly the independently defined cutoff-free matrix. -/
theorem sourceEq44ReconciledMatrix_eq_cutoffFreeMatrix
    (L : ℝ) (N : ℕ) :
    sourceEq44ReconciledMatrix L N = cutoffFreeMatrix L N := by
  ext i j
  simp [sourceEq44ReconciledMatrix,
    sourceEq44ReconciledEntry_eq_cutoffFreeEntry]

/-- The same source-normalized matrix differs from the historical
`finiteMatrix` convention by exactly the diagonal scalar already isolated in
PR #65. -/
theorem sourceEq44ReconciledMatrix_eq_finiteMatrix_add_correction
    (L : ℝ) (N : ℕ) :
    sourceEq44ReconciledMatrix L N =
      finiteMatrix L N +
        ((2 * cCorrection L : ℝ) : ℂ) •
          (1 : Matrix
            (Fin (2 * N + 1))
            (Fin (2 * N + 1)) ℂ) := by
  rw [sourceEq44ReconciledMatrix_eq_cutoffFreeMatrix,
    cutoffFreeMatrix_eq_finiteMatrix_add_correction]

/-- Source-facing lambda wrapper, preserving the exact convention
`L = 2*log(lambda)`. -/
def sourceEq44ReconciledMatrixOfLambda (lam : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  sourceEq44ReconciledMatrix (2 * Real.log lam) N

/-- Lambda-parameter version of the G1-B0 endpoint. -/
theorem sourceEq44ReconciledMatrixOfLambda_eq_cutoffFreeMatrixOfLambda
    (lam : ℝ) (N : ℕ) :
    sourceEq44ReconciledMatrixOfLambda lam N =
      cutoffFreeMatrixOfLambda lam N := by
  simp [sourceEq44ReconciledMatrixOfLambda, cutoffFreeMatrixOfLambda,
    sourceEq44ReconciledMatrix_eq_cutoffFreeMatrix]

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceEq44GammaL_eq_cutoffFreeGammaL
#print axioms Zeta23.CCM.gammaL_eq_sourceEq44GammaL_add_correction
#print axioms Zeta23.CCM.sourceEq44ArchComponent_eq_cutoffFreeArchComponent
#print axioms Zeta23.CCM.archComponent_eq_sourceEq44ArchComponent_add_two_correction
#print axioms Zeta23.CCM.sourceEq44ReconciledEntry_eq_cutoffFreeEntry
#print axioms Zeta23.CCM.sourceEq44ReconciledMatrix_eq_cutoffFreeMatrix
#print axioms Zeta23.CCM.sourceEq44ReconciledMatrix_eq_finiteMatrix_add_correction
#print axioms Zeta23.CCM.sourceEq44ReconciledMatrixOfLambda_eq_cutoffFreeMatrixOfLambda
