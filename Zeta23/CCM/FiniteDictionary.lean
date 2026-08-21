import Zeta23.CCM.SourceMatrix
import Zeta23.ExplicitFormula

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-! # Finite Guinand--Weil dictionary

The finite dictionary is built directly on the theorem-authoritative elementary
source matrix.  The canonical Lean-side transform is `Zeta23.paperFT`; external
Groskin code remains a regression oracle only and is not imported here.

PR #36 closes the basic finite/topological API needed before the explicit-formula
admissibility work: a reusable quadratic form, exact endpoint normalization,
evenness, compact support, and continuity of the raw dictionary test.
-/

/-- Reusable finite complex quadratic form with the project's fixed conjugation convention. -/
def quadraticForm {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℂ) (u : ι → ℂ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (u i) * A i j * u j

/-- Squared coefficient mass in complex form.  Each summand is `conj(u_i) * u_i`. -/
def coefficientMass (N : ℕ) (u : Fin (2 * N + 1) → ℂ) : ℂ :=
  ∑ i, (starRingEnd ℂ) (u i) * u i

/-- Quadratic contraction of one elementary source matrix against centered
coefficients `u`.  This is the finite source-side kernel before any explicit
formula is invoked. -/
def sourceContract (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (ω : ℝ) : ℂ :=
  quadraticForm (sourceMatrix ω N) u

/-- Alias emphasizing the dictionary role of the source contraction. -/
def dictionaryKernel (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (ω : ℝ) : ℂ :=
  sourceContract N u ω

@[simp] theorem sourceContract_zero (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    sourceContract N u 0 = 0 := by
  simp [sourceContract, quadraticForm]

@[simp] theorem dictionaryKernel_zero (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    dictionaryKernel N u 0 = 0 := by
  simp [dictionaryKernel]

/-- At the right source endpoint `ω = 1`, the contraction is twice the
coefficient mass because `sourceMatrix 1 = 2I`. -/
theorem sourceContract_one (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    sourceContract N u 1 = 2 * coefficientMass N u := by
  rw [sourceContract, sourceMatrix_one]
  unfold quadraticForm coefficientMass
  simp only [smul_apply, one_apply]
  calc
    (∑ i, ∑ j, (starRingEnd ℂ) (u i) * ((2 : ℂ) * if i = j then 1 else 0) * u j) =
        ∑ i, (starRingEnd ℂ) (u i) * 2 * u i := by
          apply Finset.sum_congr rfl
          intro i hi
          simp
    _ = ∑ i, 2 * ((starRingEnd ℂ) (u i) * u i) := by
          apply Finset.sum_congr rfl
          intro i hi
          ring
    _ = 2 * ∑ i, (starRingEnd ℂ) (u i) * u i := by
          rw [Finset.mul_sum]

@[simp] theorem dictionaryKernel_one (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    dictionaryKernel N u 1 = 2 * coefficientMass N u := by
  simpa [dictionaryKernel] using sourceContract_one N u

/-- PR #34's sign-locked source convention lifts directly to quadratic
contractions.  Thus the dictionary kernel at `ω = 1-y/L` is exactly the
quadratic contraction of the fork-owned `qBasis` kernels. -/
theorem sourceContract_one_sub_eq_qBasisContract
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (y L : ℝ) :
    sourceContract N u (1 - y / L) =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          (qBasis (centeredIndex N i) (centeredIndex N j) y L : ℂ) * u j := by
  simp [sourceContract, quadraticForm, sourceMatrix_apply, sourceEntry_one_sub_eq_qBasis]

/-- Compact physical-space dictionary test.  The factor `1/2` matches the
Groskin/paper Fourier-transform convention. -/
def dictionaryTest (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (L : ℝ) : ℝ → ℂ :=
  fun y =>
    if |y| ≤ L then
      (1 / 2 : ℂ) * dictionaryKernel N u (1 - |y| / L)
    else
      0

/-- Canonical finite-dictionary transform in the inherited explicit-formula
normalization.  No competing Fourier convention is introduced internally. -/
def dictionaryTransform (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (L : ℝ) (z : ℂ) : ℂ :=
  Zeta23.paperFT (dictionaryTest N u L) z

/-- Inside the aperture, the physical-space test is exactly a quadratic
contraction of the existing CCM kernel family. -/
theorem dictionaryTest_eq_qBasisContract_of_abs_le
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) {L y : ℝ} (hy : |y| ≤ L) :
    dictionaryTest N u L y =
      (1 / 2 : ℂ) *
        ∑ i, ∑ j,
          (starRingEnd ℂ) (u i) *
            (qBasis (centeredIndex N i) (centeredIndex N j) |y| L : ℂ) * u j := by
  simp [dictionaryTest, hy, dictionaryKernel,
    sourceContract_one_sub_eq_qBasisContract]

/-- The raw dictionary test vanishes outside its aperture. -/
theorem dictionaryTest_eq_zero_of_lt_abs
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (L y : ℝ) (hy : L < |y|) :
    dictionaryTest N u L y = 0 := by
  simp [dictionaryTest, not_le.mpr hy]

/-- The dictionary test is even by construction. -/
@[simp] theorem dictionaryTest_neg
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (L y : ℝ) :
    dictionaryTest N u L (-y) = dictionaryTest N u L y := by
  simp [dictionaryTest]

/-- At the center of a positive aperture, the test equals the coefficient mass. -/
theorem dictionaryTest_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) {L : ℝ} (hL : 0 < L) :
    dictionaryTest N u L 0 = coefficientMass N u := by
  simp [dictionaryTest, hL.le, dictionaryKernel_one]
  ring

/-- The right aperture endpoint vanishes exactly. -/
@[simp] theorem dictionaryTest_right_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) {L : ℝ} (hL : 0 < L) :
    dictionaryTest N u L L = 0 := by
  simp [dictionaryTest, abs_of_pos hL, hL.ne']

/-- The left aperture endpoint vanishes exactly. -/
@[simp] theorem dictionaryTest_left_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) {L : ℝ} (hL : 0 < L) :
    dictionaryTest N u L (-L) = 0 := by
  simpa using dictionaryTest_right_endpoint N u hL

/-- The function support is contained in the closed aperture interval. -/
theorem dictionaryTest_support_subset
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (L : ℝ) :
    Function.support (dictionaryTest N u L) ⊆ Icc (-L) L := by
  intro y hy
  have habs : |y| ≤ L := by
    by_contra h
    have hlt : L < |y| := lt_of_not_ge h
    exact hy (dictionaryTest_eq_zero_of_lt_abs N u L y hlt)
  exact (abs_le.mp habs)

/-- The raw dictionary test has compact support for every real `L`. -/
theorem dictionaryTest_hasCompactSupport
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (L : ℝ) :
    HasCompactSupport (dictionaryTest N u L) := by
  refine HasCompactSupport.intro isCompact_Icc ?_
  intro y hy
  by_contra hzero
  exact hy (dictionaryTest_support_subset N u L hzero)

/-- Continuous dependence of the source potential on its source coordinate. -/
@[fun_prop] theorem continuous_sourcePotential (n : ℤ) :
    Continuous (fun ω : ℝ => sourcePotential ω n) := by
  unfold sourcePotential
  fun_prop

/-- Continuous dependence of the diagonal source data on its source coordinate. -/
@[fun_prop] theorem continuous_sourceDiagonal (n : ℤ) :
    Continuous (fun ω : ℝ => sourceDiagonal ω n) := by
  unfold sourceDiagonal
  fun_prop

/-- Each elementary source entry varies continuously in `ω`. -/
@[fun_prop] theorem continuous_sourceEntry (n m : ℤ) :
    Continuous (fun ω : ℝ => sourceEntry ω n m) := by
  by_cases h : n = m
  · subst m
    simpa only [sourceEntry_self] using continuous_sourceDiagonal n
  · have heq : (fun ω : ℝ => sourceEntry ω n m) =
        fun ω => (sourcePotential ω n - sourcePotential ω m) / (((n - m : ℤ) : ℂ)) := by
      funext ω
      exact sourceEntry_of_ne ω h
    rw [heq]
    fun_prop

/-- Each finite source-matrix entry varies continuously in `ω`. -/
@[fun_prop] theorem continuous_sourceMatrix_apply
    (N : ℕ) (i j : Fin (2 * N + 1)) :
    Continuous (fun ω : ℝ => sourceMatrix ω N i j) := by
  simpa only [sourceMatrix_apply] using
    continuous_sourceEntry (centeredIndex N i) (centeredIndex N j)

/-- The finite source contraction is continuous in the source coordinate. -/
@[fun_prop] theorem continuous_sourceContract
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    Continuous (sourceContract N u) := by
  unfold sourceContract quadraticForm
  fun_prop

/-- The dictionary kernel is continuous in the source coordinate. -/
@[fun_prop] theorem continuous_dictionaryKernel
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    Continuous (dictionaryKernel N u) := by
  simpa [dictionaryKernel] using continuous_sourceContract N u

/-- Continuous clamped source coordinate used to remove the piecewise boundary
from the continuity proof. -/
def dictionaryApertureCoord (L y : ℝ) : ℝ :=
  max 0 (1 - |y| / L)

@[fun_prop] theorem continuous_dictionaryApertureCoord (L : ℝ) :
    Continuous (dictionaryApertureCoord L) := by
  unfold dictionaryApertureCoord
  fun_prop

/-- For positive aperture, the original piecewise test equals the continuous
clamped-coordinate representation. -/
theorem dictionaryTest_eq_clamped
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) {L : ℝ} (hL : 0 < L) (y : ℝ) :
    dictionaryTest N u L y =
      (1 / 2 : ℂ) * dictionaryKernel N u (dictionaryApertureCoord L y) := by
  by_cases hy : |y| ≤ L
  · have hdiv : |y| / L ≤ 1 := (div_le_one hL).2 hy
    have hnonneg : 0 ≤ 1 - |y| / L := sub_nonneg.mpr hdiv
    simp [dictionaryTest, dictionaryApertureCoord, hy, max_eq_right hnonneg]
  · have hylt : L < |y| := lt_of_not_ge hy
    have hdiv : 1 < |y| / L := (one_lt_div hL).2 hylt
    have hnonpos : 1 - |y| / L ≤ 0 := le_of_lt (sub_neg.mpr hdiv)
    simp [dictionaryTest, dictionaryApertureCoord, hy, max_eq_left hnonpos]

/-- The raw finite dictionary test is continuous for positive aperture.  It is
not claimed to be globally `C^1` or `C^2`; that analytic seam is the next PR. -/
theorem continuous_dictionaryTest
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) {L : ℝ} (hL : 0 < L) :
    Continuous (dictionaryTest N u L) := by
  have heq : dictionaryTest N u L =
      fun y => (1 / 2 : ℂ) * dictionaryKernel N u (dictionaryApertureCoord L y) := by
    funext y
    exact dictionaryTest_eq_clamped N u hL y
  rw [heq]
  fun_prop

end Zeta23.CCM
