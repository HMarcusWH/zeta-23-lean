import Zeta23.CCM.LocalizedFiniteSpace
import Zeta23.Defs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact rational representation of the native finite Fourier transform

The source vector is the unchanged hard zero-extension from `[0,L]`, with
`localizedMode` normalized by `L^(-1/2)`. The paper transform uses `exp(I*z*x)`.
Consequently the rational denominators have a plus sign: `z + (2*pi/L)*n`.
The formula below is stated away from the finitely many modal poles. This
condition does not exclude the full lattice on which the common exponential
factor vanishes. No density, C1, or RH premise is used.
-/

noncomputable section

namespace Zeta23.OPICARound20

open Complex MeasureTheory Set
open scoped BigOperators
open CCM

/-- The common exponential factor, with the exact native mode normalization. -/
def finiteFourierScale (L : ℝ) (z : ℂ) : ℂ :=
  (Complex.exp (Complex.I * z * (L : ℂ)) - 1) /
    (Complex.I * (Real.sqrt L : ℂ))

private theorem localizedMode_mul_paperKernel (L : ℝ) (n : ℤ) (x : ℝ) (z : ℂ) :
    localizedMode L n x * Complex.exp (Complex.I * z * (x : ℂ)) =
      ((1 / Real.sqrt L : ℝ) : ℂ) *
        Complex.exp ((Complex.I *
          (z + ((2 * Real.pi / L : ℝ) : ℂ) * (n : ℂ))) * (x : ℂ)) := by
  unfold localizedMode
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  ring

private theorem paperModeRate_endpoint {L : ℝ} (hL : 0 < L) (n : ℤ) (z : ℂ) :
    (Complex.I * (z + ((2 * Real.pi / L : ℝ) : ℂ) * (n : ℂ))) * (L : ℂ) =
      Complex.I * z * (L : ℂ) + (n : ℂ) * (2 * Real.pi * Complex.I) := by
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr hL.ne']

/-- The exact interval integral of one unchanged mode, away from its resonance. -/
theorem intervalIntegral_localizedMode_mul_paperKernel {L : ℝ} (hL : 0 < L)
    (n : ℤ) (z : ℂ)
    (hn : z + ((2 * Real.pi / L : ℝ) : ℂ) * (n : ℂ) ≠ 0) :
    (∫ x in (0 : ℝ)..L,
      localizedMode L n x * Complex.exp (Complex.I * z * (x : ℂ))) =
      finiteFourierScale L z *
        (1 / (z + ((2 * Real.pi / L : ℝ) : ℂ) * (n : ℂ))) := by
  simp_rw [localizedMode_mul_paperKernel]
  rw [intervalIntegral.integral_const_mul,
    integral_exp_mul_complex (mul_ne_zero Complex.I_ne_zero hn),
    paperModeRate_endpoint hL]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I]
  simp only [mul_one, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  unfold finiteFourierScale
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Retain the native hard window exactly before evaluating its transform. -/
theorem paperFT_localizedFiniteVector_eq_intervalIntegral
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ) (z : ℂ) :
    paperFT (localizedFiniteVector L K u) z =
      ∫ x in (0 : ℝ)..L,
        localizedFiniteFunction L K u x * Complex.exp (Complex.I * z * (x : ℂ)) := by
  unfold paperFT
  have hf : (fun x : ℝ =>
      localizedFiniteVector L K u x * Complex.exp (Complex.I * z * (x : ℂ))) =
    (Icc (0 : ℝ) L).indicator (fun x =>
      localizedFiniteFunction L K u x * Complex.exp (Complex.I * z * (x : ℂ))) := by
    funext x
    rw [localizedFiniteVector_eq_indicator]
    by_cases hx : x ∈ Icc (0 : ℝ) L <;> simp [hx]
  rw [hf, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL.le]

/-- Exact finite-Fourier rational identity at every nonmodal complex point.
It holds for arbitrary coefficients, without boundary-flatness or positivity. -/
theorem paperFT_localizedFiniteVector_eq_rational
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ) (z : ℂ)
    (hz : ∀ i : Fin (2 * K + 1),
      z + ((2 * Real.pi / L : ℝ) : ℂ) * (centeredIndex K i : ℂ) ≠ 0) :
    paperFT (localizedFiniteVector L K u) z =
      ((Complex.exp (Complex.I * z * (L : ℂ)) - 1) /
        (Complex.I * (Real.sqrt L : ℂ))) *
      ∑ i, u i / (z + ((2 * Real.pi / L : ℝ) : ℂ) * (centeredIndex K i : ℂ)) := by
  rw [paperFT_localizedFiniteVector_eq_intervalIntegral hL]
  have hf : (fun x : ℝ => localizedFiniteFunction L K u x *
      Complex.exp (Complex.I * z * (x : ℂ))) =
    (fun x => ∑ i, u i * (localizedMode L (centeredIndex K i) x *
      Complex.exp (Complex.I * z * (x : ℂ)))) := by
    funext x
    simp only [localizedFiniteFunction, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hf, intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul,
      intervalIntegral_localizedMode_mul_paperKernel hL _ z (hz _)]
    unfold finiteFourierScale
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [div_eq_mul_inv]
    ring
  · intro i hi
    apply Continuous.intervalIntegrable
    unfold localizedMode
    fun_prop

/-- A genuine modal resonance lies on the complete exponential resonance lattice. -/
theorem paperKernel_eq_one_of_modal_resonance {L : ℝ} (hL : 0 < L)
    (n : ℤ) (z : ℂ)
    (hz : z + ((2 * Real.pi / L : ℝ) : ℂ) * (n : ℂ) = 0) :
    Complex.exp (Complex.I * z * (L : ℂ)) = 1 := by
  have h := paperModeRate_endpoint hL n z
  rw [hz, mul_zero, zero_mul] at h
  have he : Complex.I * z * (L : ℂ) = (-n : ℤ) * (2 * Real.pi * Complex.I) := by
    push_cast
    linear_combination -h
  rw [he, Complex.exp_int_mul_two_pi_mul_I]

/-- Excluding the whole exponential resonance lattice excludes each modal pole. -/
theorem paperModeDenominator_ne_zero_of_exp_ne_one {L : ℝ} (hL : 0 < L)
    (z : ℂ) (hz : Complex.exp (Complex.I * z * (L : ℂ)) ≠ 1) (n : ℤ) :
    z + ((2 * Real.pi / L : ℝ) : ℂ) * (n : ℂ) ≠ 0 := by
  intro hn
  exact hz (paperKernel_eq_one_of_modal_resonance hL n z hn)

theorem finiteFourierScale_ne_zero {L : ℝ} (hL : 0 < L)
    (z : ℂ) (hz : Complex.exp (Complex.I * z * (L : ℂ)) ≠ 1) :
    finiteFourierScale L z ≠ 0 := by
  unfold finiteFourierScale
  exact div_ne_zero (sub_ne_zero.mpr hz)
    (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hL).ne'))

/-- At a point outside the entire exponential resonance lattice, transform
vanishing is exactly rational-sum vanishing. This condition is stronger than
merely avoiding the finite set of modal poles. -/
theorem paperFT_localizedFiniteVector_zero_iff_rational_sum_zero
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ) (z : ℂ)
    (hz : Complex.exp (Complex.I * z * (L : ℂ)) ≠ 1) :
    paperFT (localizedFiniteVector L K u) z = 0 ↔
      (∑ i, u i / (z + ((2 * Real.pi / L : ℝ) : ℂ) * (centeredIndex K i : ℂ))) = 0 := by
  rw [paperFT_localizedFiniteVector_eq_rational hL K u z
    (fun i => paperModeDenominator_ne_zero_of_exp_ne_one hL z hz (centeredIndex K i))]
  change finiteFourierScale L z * _ = 0 ↔ _
  simp only [mul_eq_zero, finiteFourierScale_ne_zero hL z hz, false_or]

/-- Nonmodal points on the full resonance lattice are automatic transform
zeros for every coefficient vector. They cannot be used as rational zero samples. -/
theorem paperFT_localizedFiniteVector_eq_zero_at_nonmodal_resonance
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ) (z : ℂ)
    (hz : ∀ i : Fin (2 * K + 1),
      z + ((2 * Real.pi / L : ℝ) : ℂ) * (centeredIndex K i : ℂ) ≠ 0)
    (he : Complex.exp (Complex.I * z * (L : ℂ)) = 1) :
    paperFT (localizedFiniteVector L K u) z = 0 := by
  rw [paperFT_localizedFiniteVector_eq_rational hL K u z hz, he]
  simp

end Zeta23.OPICARound20

#print axioms Zeta23.OPICARound20.intervalIntegral_localizedMode_mul_paperKernel
#print axioms Zeta23.OPICARound20.paperFT_localizedFiniteVector_eq_intervalIntegral
#print axioms Zeta23.OPICARound20.paperFT_localizedFiniteVector_eq_rational

#print axioms Zeta23.OPICARound20.paperKernel_eq_one_of_modal_resonance

#print axioms Zeta23.OPICARound20.paperModeDenominator_ne_zero_of_exp_ne_one

#print axioms Zeta23.OPICARound20.finiteFourierScale_ne_zero

#print axioms Zeta23.OPICARound20.paperFT_localizedFiniteVector_zero_iff_rational_sum_zero

#print axioms Zeta23.OPICARound20.paperFT_localizedFiniteVector_eq_zero_at_nonmodal_resonance
