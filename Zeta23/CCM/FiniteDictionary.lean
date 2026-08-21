import Zeta23.CCM.SourceMatrix
import Zeta23.ExplicitFormula

noncomputable section

namespace Zeta23.CCM

open Matrix
open scoped BigOperators ComplexConjugate

/-! # Finite Guinand--Weil dictionary

This module starts the exact finite dictionary on top of PR #34's elementary
source matrix.  The canonical Lean-side transform is `Zeta23.paperFT`; the
external Groskin implementation is a regression oracle only and is not imported
here.

The first layer is deliberately coefficient-agnostic: `u` is a vector on the
full centered grid `-N,...,N`.  The paper's reversal-even embedding
`v -> u`, its trigonometric-polynomial/Volterra representation, and the compact
Fourier-side convention are subsequent theorems in this PR.
-/

/-- Quadratic contraction of one elementary source matrix against centered
coefficients `u`.  This is the finite source-side kernel before any explicit
formula is invoked. -/
def sourceContract (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (ω : ℝ) : ℂ :=
  ∑ i, ∑ j, (starRingEnd ℂ) (u i) * sourceMatrix ω N i j * u j

/-- Alias emphasizing the dictionary role of the source contraction. -/
def dictionaryKernel (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (ω : ℝ) : ℂ :=
  sourceContract N u ω

@[simp] theorem sourcePotential_zero (n : ℤ) : sourcePotential 0 n = 0 := by
  simp [sourcePotential]

@[simp] theorem sourceDiagonal_zero (n : ℤ) : sourceDiagonal 0 n = 0 := by
  simp [sourceDiagonal]

@[simp] theorem sourceEntry_zero (n m : ℤ) : sourceEntry 0 n m = 0 := by
  simp [sourceEntry, dividedDifferenceEntry]

@[simp] theorem sourceMatrix_zero (N : ℕ) :
    sourceMatrix 0 N = 0 := by
  ext i j
  simp [sourceMatrix_apply]

@[simp] theorem sourceContract_zero (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    sourceContract N u 0 = 0 := by
  simp [sourceContract]

@[simp] theorem dictionaryKernel_zero (N : ℕ) (u : Fin (2 * N + 1) → ℂ) :
    dictionaryKernel N u 0 = 0 := by
  simp [dictionaryKernel]

/-- PR #34's sign-locked source convention lifts directly to quadratic
contractions.  Thus the dictionary kernel at `ω = 1-y/L` is exactly the
quadratic contraction of the fork-owned `qBasis` kernels. -/
theorem sourceContract_one_sub_eq_qBasisContract
    (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (y L : ℝ) :
    sourceContract N u (1 - y / L) =
      ∑ i, ∑ j,
        (starRingEnd ℂ) (u i) *
          (qBasis (centeredIndex N i) (centeredIndex N j) y L : ℂ) * u j := by
  simp [sourceContract, sourceMatrix_apply, sourceEntry_one_sub_eq_qBasis]

/-- Compact physical-space dictionary test.  For positive aperture `L`, its
support is intended to lie in `[-L,L]`; support/continuity are proved later in
this PR.  The factor `1/2` is chosen so that its paper Fourier transform matches
Groskin's `g_v` convention after evenness is established. -/
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

end Zeta23.CCM
