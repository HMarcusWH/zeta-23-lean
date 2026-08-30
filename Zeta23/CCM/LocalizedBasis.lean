import Zeta23.CCM.Kernel
import Zeta23.CCM.FiniteMatrix
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

noncomputable section

namespace Zeta23.CCM

open Complex
open scoped BigOperators
open intervalIntegral

/-!
# Localized Fourier basis and hard-window correlation

This module installs the function-space geometry underneath the finite CCM
kernel.  It deliberately stops before the localized Weil form itself.

For a positive aperture `L`, the normalized Fourier character on an interval
of length `L` is

`U_n(x) = L^(-1/2) exp(2π i n x / L)`.

The real symmetrized overlap of two such characters across a shift
`0 <= y <= L` reduces to the exact `qBasis` formula already used by the
finite CCM matrix.

No explicit formula, zero sum, positivity, finite-to-infinite argument, or RH
statement is used here.
-/

/-- Normalized Fourier character on an interval of length `L`.  The ambient
interval/support is supplied by later Galerkin modules; this definition records
the normalized mode itself. -/
def localizedMode (L : ℝ) (n : ℤ) (x : ℝ) : ℂ :=
  ((1 / Real.sqrt L : ℝ) : ℂ) *
    Complex.exp (Complex.I * (((2 * Real.pi * (n : ℝ) * x / L : ℝ) : ℂ)))

/-- Finite centered Fourier combination corresponding to the repository's
`Fin (2*N+1)` coefficient coordinates. -/
def localizedFiniteFunction
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (x : ℝ) : ℂ :=
  ∑ i, u i * localizedMode L (centeredIndex N i) x

/-- Real symmetrized normalized hard-window character overlap.

The phase is what one gets from
`U_n(x) * conj(U_m(x+y))` after cancelling the two `L^(-1/2)`
normalizations.  Writing the overlap this way isolates the only integral
needed for the G0 basis calculation and avoids importing the Weil form itself.
-/
def hardWindowCharacterCorrelation
    (n m : ℤ) (y L : ℝ) : ℝ :=
  (2 / L) *
    ∫ x in (0 : ℝ)..(L - y),
      Real.cos
        (2 * Real.pi *
          ((((n - m : ℤ) : ℝ) * x - (m : ℝ) * y) / L))

/-- Elementary affine-cosine interval integral used by the off-diagonal
character-overlap calculation. -/
theorem integral_cos_affine
    (a b s t : ℝ) (ha : a ≠ 0) :
    (∫ x in s..t, Real.cos (a * x + b)) =
      (Real.sin (a * t + b) - Real.sin (a * s + b)) / a := by
  have hmul :
      a * (∫ x in s..t, Real.cos (a * x + b)) =
        Real.sin (a * t + b) - Real.sin (a * s + b) := by
    rw [intervalIntegral.mul_integral_comp_mul_add]
    simp
  apply (eq_div_iff ha).2
  simpa [mul_comm] using hmul

/-- The normalized hard-window Fourier-character overlap is exactly the
existing CCM `qBasis` entry formula. -/
theorem hardWindowCharacterCorrelation_eq_qBasis
    (n m : ℤ) {L y : ℝ} (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    hardWindowCharacterCorrelation n m y L = qBasis n m y L := by
  have hL0 : L ≠ 0 := ne_of_gt hL
  by_cases hnm : n = m
  · subst m
    simp only [hardWindowCharacterCorrelation, qBasis, if_pos, sub_self, Int.cast_zero,
      zero_mul, zero_sub]
    have hconst :
        (∫ _x in (0 : ℝ)..(L - y),
            Real.cos (2 * Real.pi * (-(n : ℝ) * y / L))) =
          (L - y) * Real.cos (2 * Real.pi * ((n : ℝ) * y / L)) := by
      rw [intervalIntegral.integral_const]
      rw [show -(n : ℝ) * y / L = -((n : ℝ) * y / L) by ring]
      simp [Real.cos_neg]
    rw [hconst]
    field_simp [hL0]
    ring
  · have hnmZ : n - m ≠ 0 := sub_ne_zero.mpr hnm
    have hnmR : (((n - m : ℤ) : ℝ)) ≠ 0 := by exact_mod_cast hnmZ
    let a : ℝ := 2 * Real.pi * (((n - m : ℤ) : ℝ)) / L
    let b : ℝ := -(2 * Real.pi * (m : ℝ) * y / L)
    have ha : a ≠ 0 := by
      dsimp [a]
      exact div_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hnmR) hL0
    have hphase :
        (fun x : ℝ =>
          2 * Real.pi *
            ((((n - m : ℤ) : ℝ) * x - (m : ℝ) * y) / L)) =
        fun x => a * x + b := by
      funext x
      dsimp [a, b]
      field_simp [hL0]
      ring
    rw [hardWindowCharacterCorrelation, hphase, integral_cos_affine a b 0 (L - y) ha]
    have hend :
        a * (L - y) + b =
          (((n - m : ℤ) : ℝ) * (2 * Real.pi)) -
            2 * Real.pi * (n : ℝ) * y / L := by
      dsimp [a, b]
      field_simp [hL0]
      push_cast
      ring
    have hstart :
        a * 0 + b = -(2 * Real.pi * (m : ℝ) * y / L) := by
      simp [b]
    rw [hend, hstart]
    have hsinEnd :
        Real.sin
            ((((n - m : ℤ) : ℝ) * (2 * Real.pi)) -
              2 * Real.pi * (n : ℝ) * y / L) =
          -Real.sin (2 * Real.pi * (n : ℝ) * y / L) := by
      simpa using
        (Real.sin_int_mul_two_pi_sub (n - m)
          (2 * Real.pi * (n : ℝ) * y / L))
    rw [hsinEnd, Real.sin_neg]
    simp only [qBasis, if_neg hnm]
    dsimp [a]
    field_simp [hL0, hnmR, Real.pi_ne_zero]
    push_cast
    ring

/-- Centered finite-index wrapper: the exact correlation kernel used by the
`Fin (2*N+1)` matrix coordinates is `qBasis` on the corresponding centered
Fourier indices. -/
theorem hardWindowCharacterCorrelation_centered_eq_qBasis
    (N : ℕ) (i j : Fin (2 * N + 1))
    {L y : ℝ} (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    hardWindowCharacterCorrelation
        (centeredIndex N i) (centeredIndex N j) y L =
      qBasis (centeredIndex N i) (centeredIndex N j) y L :=
  hardWindowCharacterCorrelation_eq_qBasis _ _ hL hy0 hyL

/-- Production half-normalization firewall.  The existing dictionary basis test
is one half of the full hard-window kernel; G1 must preserve this convention
when attaching the localized Weil functional. -/
theorem two_mul_dictionaryBasisTest_eq_kernel
    (n m : ℤ) (L y : ℝ) :
    2 * dictionaryBasisTest n m L y = kernel n m L y := by
  simp [dictionaryBasisTest]
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.integral_cos_affine
#print axioms Zeta23.CCM.hardWindowCharacterCorrelation_eq_qBasis
#print axioms Zeta23.CCM.hardWindowCharacterCorrelation_centered_eq_qBasis
#print axioms Zeta23.CCM.two_mul_dictionaryBasisTest_eq_kernel
