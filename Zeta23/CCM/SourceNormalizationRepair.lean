import Zeta23.CCM.SourceWeilMatrixReconciliation
import Zeta23.CCM.DictionaryArchDiagonal
import Zeta23.CCM.Displacement

noncomputable section

namespace Zeta23.CCM

open Matrix MeasureTheory Set
open scoped Interval

/-!
# Canonical source-normalization repair

PR #71 isolated an inconsistency in the later printed Section-4 normalization
chain of Connes--Consani--Moscovici.

The historical repository objects `cCorrectionIntegrand`, `cCorrection`,
`gammaL`, `entry`, and `finiteMatrix` are intentionally left unchanged:
they encode the literal printed-(4.14) convention and remain useful for theorem
history and scalar-shift identities.

The direct source authority is equation (4.4), already formalized by PR #71 as
`sourceEq44Matrix`, and proved there equal to `cutoffFreeMatrix`.

This module makes that semantic distinction explicit:

* `legacyPrinted*` names expose the historical printed normalization.
* `sourceEq411DerivedCorrection` is the correction integral forced by the
  rho-weighted algebra of equation (4.11).
* `canonicalSourceGammaL` and `canonicalSourceMatrix` are the direct
  equation-(4.4) / cutoff-free convention.
* the exact legacy-to-canonical scalar shift is theorem-locked under the new
  names.
* the R004 displacement theorem is re-exported on the canonical source matrix,
  using scalar-shift invariance rather than relabelling the legacy object.

Claim firewall: no theorem in this module identifies an ambient external
`QW_lambda`, `PsiSharp`, or form-core object with a finite matrix.
-/

/-- Historical printed correction integrand from the literal equation-(4.11)
transcription.  The name is an alias only; the old definition is frozen. -/
abbrev legacyPrintedCorrectionIntegrand : ℝ → ℝ :=
  cCorrectionIntegrand

/-- Historical printed correction integral.  Frozen for theorem compatibility. -/
abbrev legacyPrintedCorrection : ℝ → ℝ :=
  cCorrection

/-- Historical printed-(4.14) diagonal primitive. -/
abbrev legacyPrintedGammaL : ℤ → ℝ → ℝ :=
  gammaL

/-- Historical printed-normalization finite matrix.  This is no longer the
canonical direct-source label. -/
abbrev legacyPrintedMatrix (L : ℝ) (N : ℕ) :=
  finiteMatrix L N

/-- Correction integral actually forced by subtracting the two rho-weighted
integrands in equation (4.11). -/
def sourceEq411DerivedCorrection (L : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..L, sourceEq411DerivedCorrectionIntegrand x

/-- Correct integrated version of the equation-(4.11) algebra.

This theorem uses the correction forced by the two displayed rho-weighted
integrands themselves.  It does not use the printed `cCorrection`. -/
theorem sourceEq411_corrected_integrated_rewrite
    (n : ℤ) {L : ℝ} (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L, sourceEq411LhsIntegrand n L x) =
      (∫ x in (0 : ℝ)..L, sourceEq411RhsCosMinusOneIntegrand n L x) +
        sourceEq411DerivedCorrection L := by
  let freq : ℝ := 2 * Real.pi * (n : ℝ) / L
  have hderivedBaseOn :
      IntegrableOn
        (fun x : ℝ => (1 - Real.exp (-x / 2)) * archDensity x)
        (Ioi 0) :=
    integrableOn_one_sub_exp_mul_archDensity_Ioi
  have hderivedBaseInt :
      IntervalIntegrable
        (fun x : ℝ => (1 - Real.exp (-x / 2)) * archDensity x)
        volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le]
    exact hderivedBaseOn.mono_set fun x hx => hx.1
  have hderivedInt :
      IntervalIntegrable sourceEq411DerivedCorrectionIntegrand volume 0 L := by
    refine hderivedBaseInt.congr_uIoo ?_
    intro x hx
    rw [uIoo_of_le hL.le] at hx
    have hxne : x ≠ 0 := ne_of_gt hx.1
    simp [sourceEq411DerivedCorrectionIntegrand, hxne]
  have hrhsBaseOn :
      IntegrableOn
        (fun x : ℝ =>
          -(archDensity x * (1 - Real.cos (freq * x))))
        (Ioi 0) :=
    (integrableOn_archDensity_mul_one_sub_cos_Ioi freq).neg
  have hrhsBaseInt :
      IntervalIntegrable
        (fun x : ℝ =>
          -(archDensity x * (1 - Real.cos (freq * x))))
        volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hL.le]
    exact hrhsBaseOn.mono_set fun x hx => hx.1
  have hrhsInt :
      IntervalIntegrable
        (sourceEq411RhsCosMinusOneIntegrand n L)
        volume 0 L := by
    refine hrhsBaseInt.congr_uIoo ?_
    intro x hx
    rw [uIoo_of_le hL.le] at hx
    have hxne : x ≠ 0 := ne_of_gt hx.1
    have hfreq :
        freq * x = 2 * Real.pi * (n : ℝ) * x / L := by
      dsimp [freq]
      field_simp [hL.ne']
    simp [sourceEq411RhsCosMinusOneIntegrand, hxne, hfreq]
    ring
  calc
    (∫ x in (0 : ℝ)..L, sourceEq411LhsIntegrand n L x)
        = ∫ x in (0 : ℝ)..L,
            (sourceEq411RhsCosMinusOneIntegrand n L x +
              sourceEq411DerivedCorrectionIntegrand x) := by
            apply intervalIntegral.integral_congr_uIoo
            intro x hx
            exact sourceEq411_integrand_decomposition n L x
    _ = (∫ x in (0 : ℝ)..L, sourceEq411RhsCosMinusOneIntegrand n L x) +
          ∫ x in (0 : ℝ)..L, sourceEq411DerivedCorrectionIntegrand x := by
          rw [intervalIntegral.integral_add hrhsInt hderivedInt]
    _ = (∫ x in (0 : ℝ)..L, sourceEq411RhsCosMinusOneIntegrand n L x) +
          sourceEq411DerivedCorrection L := rfl

/-- Canonical direct-source diagonal primitive. -/
def canonicalSourceGammaL (n : ℤ) (L : ℝ) : ℝ :=
  sourceEq44GammaL n L

/-- Canonical gamma written in the equivalent corrected equation-(4.11)
right-hand representation. -/
theorem canonicalSourceGammaL_eq_rhs_add_derivedCorrection
    (n : ℤ) {L : ℝ} (hL : 0 < L) :
    canonicalSourceGammaL n L =
      (∫ x in (0 : ℝ)..L, sourceEq411RhsCosMinusOneIntegrand n L x) +
        sourceEq411DerivedCorrection L + wCorrection L := by
  unfold canonicalSourceGammaL sourceEq44GammaL
  rw [sourceEq411_corrected_integrated_rewrite n hL]

/-- Direct source equation-(4.4) matrix, with the independently audited
cutoff-free convention as its canonical repository representation. -/
def canonicalSourceMatrix (L : ℝ) (N : ℕ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  cutoffFreeMatrix L N

/-- The canonical source alias is exactly the raw equation-(4.4) matrix. -/
theorem canonicalSourceMatrix_eq_sourceEq44Matrix
    (L : ℝ) (N : ℕ) :
    canonicalSourceMatrix L N = sourceEq44Matrix L N := by
  rw [canonicalSourceMatrix, sourceEq44Matrix_eq_cutoffFreeMatrix]

/-- The canonical source matrix is exactly the deterministic dictionary matrix. -/
theorem canonicalSourceMatrix_eq_dictionaryMatrix
    (L : ℝ) (N : ℕ) :
    canonicalSourceMatrix L N = dictionaryMatrix L N := by
  exact cutoffFreeMatrix_eq_dictionaryMatrix L N

/-- Exact semantic repair theorem.

The historical printed-normalization matrix differs from the canonical direct
source matrix by the already-discovered scalar diagonal correction. -/
theorem canonicalSourceMatrix_eq_legacyPrintedMatrix_add_correction
    (L : ℝ) (N : ℕ) :
    canonicalSourceMatrix L N =
      legacyPrintedMatrix L N +
        ((2 * legacyPrintedCorrection L : ℝ) : ℂ) •
          (1 : Matrix
            (Fin (2 * N + 1))
            (Fin (2 * N + 1)) ℂ) := by
  simpa [canonicalSourceMatrix] using
    cutoffFreeMatrix_eq_finiteMatrix_add_correction L N

/-- Canonical-source displacement theorem.

The scalar legacy-to-canonical shift commutes with the centered index diagonal,
so the exact R004 displacement generator is unchanged. -/
theorem canonicalSourceMatrix_displacement
    {L : ℝ} (hL : 0 < L) (N : ℕ) :
    indexMatrix N * canonicalSourceMatrix L N -
        canonicalSourceMatrix L N * indexMatrix N =
      vecMulVec (displacementVector L N) (fun _ => 1) -
        vecMulVec (fun _ => 1) (displacementVector L N) := by
  have hA :
      canonicalSourceMatrix L N =
        (1 : ℂ) • finiteMatrix L N +
          ((2 * cCorrection L : ℝ) : ℂ) •
            (1 : Matrix
              (Fin (2 * N + 1))
              (Fin (2 * N + 1)) ℂ) := by
    simpa [canonicalSourceMatrix] using
      cutoffFreeMatrix_eq_finiteMatrix_add_correction L N
  have hM :
      Zeta23.ExceptionalZero.displacement
          (indexMatrix N) (finiteMatrix L N) =
        vecMulVec (displacementVector L N) (fun _ => 1) -
          vecMulVec (fun _ => 1) (displacementVector L N) := by
    simpa [Zeta23.ExceptionalZero.displacement] using
      finiteMatrix_displacement hL N
  have h :=
    Zeta23.ExceptionalZero.displacement_eq_of_eq_smul_add_scalar
      (D := indexMatrix N)
      (M := finiteMatrix L N)
      (A := canonicalSourceMatrix L N)
      (g := displacementVector L N)
      (u := fun _ => (1 : ℂ))
      (k := (1 : ℂ))
      (c := ((2 * cCorrection L : ℝ) : ℂ))
      hA hM
  simpa [Zeta23.ExceptionalZero.displacement] using h

/-- Rank form of the canonical source displacement theorem. -/
theorem rank_canonicalSourceMatrix_displacement_le_two
    {L : ℝ} (hL : 0 < L) (N : ℕ) :
    (indexMatrix N * canonicalSourceMatrix L N -
      canonicalSourceMatrix L N * indexMatrix N).rank ≤ 2 := by
  have hA :
      canonicalSourceMatrix L N =
        (1 : ℂ) • finiteMatrix L N +
          ((2 * cCorrection L : ℝ) : ℂ) •
            (1 : Matrix
              (Fin (2 * N + 1))
              (Fin (2 * N + 1)) ℂ) := by
    simpa [canonicalSourceMatrix] using
      cutoffFreeMatrix_eq_finiteMatrix_add_correction L N
  have hM :
      Zeta23.ExceptionalZero.displacement
          (indexMatrix N) (finiteMatrix L N) =
        vecMulVec (displacementVector L N) (fun _ => 1) -
          vecMulVec (fun _ => 1) (displacementVector L N) := by
    simpa [Zeta23.ExceptionalZero.displacement] using
      finiteMatrix_displacement hL N
  have h :=
    Zeta23.ExceptionalZero.rank_displacement_le_two_of_eq_smul_add_scalar
      (D := indexMatrix N)
      (M := finiteMatrix L N)
      (A := canonicalSourceMatrix L N)
      (g := displacementVector L N)
      (u := fun _ => (1 : ℂ))
      (k := (1 : ℂ))
      (c := ((2 * cCorrection L : ℝ) : ℂ))
      hA hM
  simpa [Zeta23.ExceptionalZero.displacement] using h

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceEq411_corrected_integrated_rewrite
#print axioms Zeta23.CCM.canonicalSourceGammaL_eq_rhs_add_derivedCorrection
#print axioms Zeta23.CCM.canonicalSourceMatrix_eq_sourceEq44Matrix
#print axioms Zeta23.CCM.canonicalSourceMatrix_eq_dictionaryMatrix
#print axioms Zeta23.CCM.canonicalSourceMatrix_eq_legacyPrintedMatrix_add_correction
#print axioms Zeta23.CCM.canonicalSourceMatrix_displacement
#print axioms Zeta23.CCM.rank_canonicalSourceMatrix_displacement_le_two
