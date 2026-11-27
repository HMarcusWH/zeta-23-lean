import Zeta23.OPICASupport.FourierBridge.FiniteFourierRational

/-!
# Modal values of the exact native finite Fourier transform

The rational formula excludes modal poles. This module evaluates those points
directly by integration, keeping the resonant contribution rather than making
an invalid zero-over-zero simplification.
-/

noncomputable section

namespace Zeta23.OPICARound20

open Complex MeasureTheory Set CCM
open scoped BigOperators

theorem intervalIntegral_localizedMode_mul_paperKernel_at_resonance
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    (∫ x in (0 : ℝ)..L, localizedMode L n x *
      Complex.exp (Complex.I * (-((2 * Real.pi / L : ℝ) : ℂ) * (n : ℂ)) * (x : ℂ))) =
      (Real.sqrt L : ℂ) := by
  have hf (x : ℝ) : localizedMode L n x *
      Complex.exp (Complex.I * (-((2 * Real.pi / L : ℝ) : ℂ) * (n : ℂ)) * (x : ℂ)) =
      ((1 / Real.sqrt L : ℝ) : ℂ) := by
    unfold localizedMode
    rw [mul_assoc, ← Complex.exp_add]
    have he : Complex.I * (((2 * Real.pi * (n : ℝ) * x / L : ℝ) : ℂ)) +
        Complex.I * (-((2 * Real.pi / L : ℝ) : ℂ) * (n : ℂ)) * (x : ℂ) = 0 := by
      push_cast
      ring
    rw [he, Complex.exp_zero, mul_one]
  simp_rw [hf]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]
  rw [← Complex.ofReal_mul]
  congr 1
  have hs : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  field_simp
  nlinarith [Real.sq_sqrt hL.le]

/-- At its modal point, the native transform reads exactly one coefficient,
with the unchanged `sqrt L` normalization. -/
theorem paperFT_localizedFiniteVector_at_modal_point
    {L : ℝ} (hL : 0 < L) (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (j : Fin (2 * K + 1)) :
    paperFT (localizedFiniteVector L K u)
      (-((2 * Real.pi / L : ℝ) : ℂ) * (centeredIndex K j : ℂ)) =
      (Real.sqrt L : ℂ) * u j := by
  let z : ℂ := -((2 * Real.pi / L : ℝ) : ℂ) * (centeredIndex K j : ℂ)
  change paperFT (localizedFiniteVector L K u) z = _
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
  · simp_rw [intervalIntegral.integral_const_mul]
    rw [Finset.sum_eq_single j]
    · rw [show z = -((2 * Real.pi / L : ℝ) : ℂ) * (centeredIndex K j : ℂ) from rfl,
        intervalIntegral_localizedMode_mul_paperKernel_at_resonance hL]
      ring
    · intro i hi hij
      have hω : ((2 * Real.pi / L : ℝ) : ℂ) ≠ 0 :=
        Complex.ofReal_ne_zero.mpr
          (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hL.ne')
      have hden : z + ((2 * Real.pi / L : ℝ) : ℂ) * (centeredIndex K i : ℂ) ≠ 0 := by
        intro hzero
        have hdiff : ((2 * Real.pi / L : ℝ) : ℂ) *
            ((centeredIndex K i : ℂ) - (centeredIndex K j : ℂ)) = 0 := by
          dsimp [z] at hzero
          linear_combination hzero
        have heq : (centeredIndex K i : ℂ) = (centeredIndex K j : ℂ) :=
          sub_eq_zero.mp ((mul_eq_zero.mp hdiff).resolve_left hω)
        apply hij
        apply centeredIndex_injective K
        exact_mod_cast heq
      rw [intervalIntegral_localizedMode_mul_paperKernel hL _ z hden]
      have hexp : Complex.exp (Complex.I * z * (L : ℂ)) = 1 :=
        paperKernel_eq_one_of_modal_resonance hL (centeredIndex K j) z (by dsimp [z]; ring)
      simp [finiteFourierScale, hexp]
    · simp
  · intro i hi
    apply Continuous.intervalIntegrable
    unfold localizedMode
    fun_prop

end Zeta23.OPICARound20

#print axioms Zeta23.OPICARound20.intervalIntegral_localizedMode_mul_paperKernel_at_resonance
#print axioms Zeta23.OPICARound20.paperFT_localizedFiniteVector_at_modal_point
