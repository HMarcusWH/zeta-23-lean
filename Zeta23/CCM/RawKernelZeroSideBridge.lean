import Zeta23.CCM.DictionaryZeroSideDisplacement
import Zeta23.CCM.DictionaryZeroSideMatrix

noncomputable section

namespace Zeta23.CCM

open Matrix
open MeasureTheory

/-!
# Historical raw-kernel zero-side bridge

The R002-D / R004 historical diagnostic used the original even two-sided
`kernel`, while the production R003 dictionary uses exactly one half of that
kernel.  After the exact production zero-side bridge is available, the old
raw-kernel normalization can be recovered by scaling.

This module deliberately introduces a neutral `rawKernelZeroSideMatrix`, not a
`Gram` object: no positivity statement is proved here.  It also does not
identify this centered truncated-character family with the general taper-grid
matrix used by R002-A.
-/

/-- The historical raw kernel is exactly twice the production basis test. -/
theorem kernel_eq_two_mul_dictionaryBasisTest
    (n m : ℤ) (L y : ℝ) :
    kernel n m L y = 2 * dictionaryBasisTest n m L y := by
  simp [dictionaryBasisTest]

/-- The paper transform of the historical raw kernel is exactly twice the
corresponding production spectral-matrix entry.

The positive-aperture hypothesis keeps this statement on the production
legality domain of the compactly supported kernel. -/
theorem paperFT_kernel_eq_two_mul_dictionarySpectralMatrix_apply
    (N : ℕ) (i j : Fin (2 * N + 1))
    {L : ℝ} (_hL : 0 < L) (z : ℂ) :
    Zeta23.paperFT
        (kernel (centeredIndex N i) (centeredIndex N j) L) z =
      2 * dictionarySpectralMatrix N L z i j := by
  rw [Zeta23.paperFT_def]
  unfold dictionarySpectralMatrix
  rw [Zeta23.paperFT_def]
  have hfun :
      (fun y : ℝ =>
        kernel (centeredIndex N i) (centeredIndex N j) L y *
          Complex.exp (Complex.I * z * y)) =
      (fun y : ℝ =>
        (2 : ℂ) *
          (dictionaryBasisTest
              (centeredIndex N i) (centeredIndex N j) L y *
            Complex.exp (Complex.I * z * y))) := by
    funext y
    rw [kernel_eq_two_mul_dictionaryBasisTest]
    ring
  rw [hfun, Zeta23.integral_const_mul_C]

/-- Every historical raw-kernel zero-side entry is absolutely summable.

No direct application of the C² explicit-formula theorem to the piecewise-C¹
raw kernel occurs here; legality is inherited from the already-proved
production basis-entry series and the exact factor-two transform identity. -/
theorem rawKernel_zero_entry_summable
    (hs : ZetaSeam)
    (N : ℕ) (i j : Fin (2 * N + 1))
    {L : ℝ} (hL : 0 < L) :
    Summable
      (fun ρ : (zetaZeros hs).carrier =>
        ((zetaZeros hs).mult ρ : ℂ) *
          Zeta23.paperFT
            (kernel
              (centeredIndex N i)
              (centeredIndex N j) L)
            (gammaOf ρ)) := by
  have h :=
    (dictionarySpectralMatrix_zero_entry_summable hs N i j hL).mul_left
      (2 : ℂ)
  have heq :
      (fun ρ : (zetaZeros hs).carrier =>
        ((zetaZeros hs).mult ρ : ℂ) *
          Zeta23.paperFT
            (kernel
              (centeredIndex N i)
              (centeredIndex N j) L)
            (gammaOf ρ)) =
      (fun ρ : (zetaZeros hs).carrier =>
        (2 : ℂ) *
          (((zetaZeros hs).mult ρ : ℂ) *
            dictionarySpectralMatrix N L (gammaOf ρ) i j)) := by
    funext ρ
    rw [paperFT_kernel_eq_two_mul_dictionarySpectralMatrix_apply
      N i j hL (gammaOf ρ)]
    ring
  rw [heq]
  exact h

/-- The theorem-authoritative zero-side matrix for the historical unhalved
`qBasis/kernel` convention. -/
def rawKernelZeroSideMatrix
    (hs : ZetaSeam) (N : ℕ) (L : ℝ) :
    Matrix (Fin (2 * N + 1)) (Fin (2 * N + 1)) ℂ :=
  fun i j =>
    ∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        Zeta23.paperFT
          (kernel
            (centeredIndex N i)
            (centeredIndex N j) L)
          (gammaOf ρ)

/-- Core historical/production reconciliation: the raw-kernel zero-side matrix
is exactly twice the production zero-side matrix. -/
theorem rawKernelZeroSideMatrix_eq_two_smul_zeroSideMatrix
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    rawKernelZeroSideMatrix hs N L =
      (2 : ℂ) • zeroSideMatrix hs N L := by
  funext i j
  change
    (∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        Zeta23.paperFT
          (kernel
            (centeredIndex N i)
            (centeredIndex N j) L)
          (gammaOf ρ)) =
      2 *
        (∑' ρ : (zetaZeros hs).carrier,
          ((zetaZeros hs).mult ρ : ℂ) *
            dictionarySpectralMatrix N L (gammaOf ρ) i j)
  have hscaled :=
    (dictionarySpectralMatrix_zero_entry_summable hs N i j hL).hasSum.mul_left
      (2 : ℂ)
  calc
    (∑' ρ : (zetaZeros hs).carrier,
      ((zetaZeros hs).mult ρ : ℂ) *
        Zeta23.paperFT
          (kernel
            (centeredIndex N i)
            (centeredIndex N j) L)
          (gammaOf ρ)) =
        ∑' ρ : (zetaZeros hs).carrier,
          (2 : ℂ) *
            (((zetaZeros hs).mult ρ : ℂ) *
              dictionarySpectralMatrix N L (gammaOf ρ) i j) := by
          apply tsum_congr
          intro ρ
          rw [paperFT_kernel_eq_two_mul_dictionarySpectralMatrix_apply
            N i j hL (gammaOf ρ)]
          ring
    _ = 2 *
        (∑' ρ : (zetaZeros hs).carrier,
          ((zetaZeros hs).mult ρ : ℂ) *
            dictionarySpectralMatrix N L (gammaOf ρ) i j) :=
      hscaled.tsum_eq

/-- The raw-kernel zero side is twice the deterministic production dictionary
matrix. -/
theorem rawKernelZeroSideMatrix_eq_two_smul_dictionaryMatrix
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    rawKernelZeroSideMatrix hs N L =
      (2 : ℂ) • dictionaryMatrix L N := by
  rw [rawKernelZeroSideMatrix_eq_two_smul_zeroSideMatrix hs N hL,
    zeroSideMatrix_eq_dictionaryMatrix hs N hL]

/-- Registry-facing corrected historical normalization.

This is the exact theorem successor to the old numerically refuted
`M = 1/2 * WeilGram` statement:
the raw-kernel zero side equals `2*M + 4*cCorrection(L)*I`. -/
theorem rawKernelZeroSideMatrix_eq_two_finiteMatrix_add_four_correction
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    rawKernelZeroSideMatrix hs N L =
      (2 : ℂ) • finiteMatrix L N +
        ((4 * cCorrection L : ℝ) : ℂ) •
          (1 : Matrix
            (Fin (2 * N + 1))
            (Fin (2 * N + 1)) ℂ) := by
  rw [rawKernelZeroSideMatrix_eq_two_smul_zeroSideMatrix hs N hL,
    zeroSideMatrix_eq_finiteMatrix_add_correction hs N hL]
  ext i j
  simp [Matrix.smul_apply]
  ring

/-- Historical raw-kernel displacement: the production divided-difference
commutator is rescaled by exactly two. -/
theorem rawKernelZeroSideMatrix_displacement
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    indexMatrix N * rawKernelZeroSideMatrix hs N L -
        rawKernelZeroSideMatrix hs N L * indexMatrix N =
      (2 : ℂ) •
        (vecMulVec (displacementVector L N) (fun _ => 1) -
          vecMulVec (fun _ => 1) (displacementVector L N)) := by
  rw [rawKernelZeroSideMatrix_eq_two_smul_zeroSideMatrix hs N hL]
  rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [← smul_sub]
  rw [zeroSideMatrix_displacement hs N hL]

/-- Rank form of the historical raw-kernel displacement theorem. -/
theorem rank_rawKernelZeroSideMatrix_displacement_le_two
    (hs : ZetaSeam)
    (N : ℕ)
    {L : ℝ} (hL : 0 < L) :
    (indexMatrix N * rawKernelZeroSideMatrix hs N L -
      rawKernelZeroSideMatrix hs N L * indexMatrix N).rank ≤ 2 := by
  have hA :
      rawKernelZeroSideMatrix hs N L =
        (2 : ℂ) • finiteMatrix L N +
          ((4 * cCorrection L : ℝ) : ℂ) •
            (1 : Matrix
              (Fin (2 * N + 1))
              (Fin (2 * N + 1)) ℂ) :=
    rawKernelZeroSideMatrix_eq_two_finiteMatrix_add_four_correction hs N hL
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
      (A := rawKernelZeroSideMatrix hs N L)
      (g := displacementVector L N)
      (u := fun _ => (1 : ℂ))
      (k := (2 : ℂ))
      (c := ((4 * cCorrection L : ℝ) : ℂ))
      hA hM
  simpa [Zeta23.ExceptionalZero.displacement] using h

end Zeta23.CCM

#print axioms Zeta23.CCM.kernel_eq_two_mul_dictionaryBasisTest
#print axioms Zeta23.CCM.paperFT_kernel_eq_two_mul_dictionarySpectralMatrix_apply
#print axioms Zeta23.CCM.rawKernel_zero_entry_summable
#print axioms Zeta23.CCM.rawKernelZeroSideMatrix_eq_two_smul_zeroSideMatrix
#print axioms Zeta23.CCM.rawKernelZeroSideMatrix_eq_two_finiteMatrix_add_four_correction
#print axioms Zeta23.CCM.rawKernelZeroSideMatrix_displacement
#print axioms Zeta23.CCM.rank_rawKernelZeroSideMatrix_displacement_le_two
