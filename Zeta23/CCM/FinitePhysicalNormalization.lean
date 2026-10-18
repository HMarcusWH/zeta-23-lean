import Zeta23.CCM.OriginalDetectorFinitePhysicalNorm

/-! Generic scalar and true-norm normalization of the actual finite Fourier synthesis. -/

noncomputable section

open Set Complex MeasureTheory
open scoped Topology

namespace Zeta23.CCM

def finitePhysicalSynthesis (L : ℝ) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ → ℂ :=
  localizedFiniteVector L K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) v)

def finiteNormalizedCoefficients {K : ℕ}
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) : EuclideanSpace ℂ (Fin (2 * K + 1)) :=
  ((‖v‖⁻¹ : ℝ) : ℂ) • v

theorem finitePhysicalSynthesis_smul (L : ℝ) (K : ℕ) (c : ℂ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    finitePhysicalSynthesis L K (c • v) = c • finitePhysicalSynthesis L K v := by
  funext x
  change (∑ i : Fin (2 * K + 1), (c * v i) * localizedZeroExtendedMode L (centeredIndex K i) x) =
    c * ∑ i : Fin (2 * K + 1), v i * localizedZeroExtendedMode L (centeredIndex K i) x
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finitePhysicalSynthesis_energy {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    (∫ x : ℝ, ‖finitePhysicalSynthesis L K v x‖ ^ 2) = ‖v‖ ^ 2 := by
  have he : (fun x : ℝ => ‖finitePhysicalSynthesis L K v x‖ ^ 2) =
      (Icc (0 : ℝ) L).indicator (fun x => ‖localizedFiniteFunction L K
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) v) x‖ ^ 2) := by
    funext x
    simp only [finitePhysicalSynthesis, localizedFiniteVector_eq_indicator]
    by_cases hx : x ∈ Icc (0 : ℝ) L
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      norm_num
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hL.le]
  exact localizedFiniteFunction_energy_eq_norm_sq hL K v

theorem finiteNormalizedCoefficients_norm {K : ℕ}
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) (hv : v ≠ 0) :
    ‖finiteNormalizedCoefficients v‖ = 1 := by
  unfold finiteNormalizedCoefficients
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (norm_nonneg v)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem finitePhysicalSynthesis_normalized (L : ℝ) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    finitePhysicalSynthesis L K (finiteNormalizedCoefficients v) =
      ((‖v‖⁻¹ : ℝ) : ℂ) • finitePhysicalSynthesis L K v :=
  finitePhysicalSynthesis_smul L K _ v

theorem finitePhysicalSynthesis_normalized_energy {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1))) (hv : v ≠ 0) :
    (∫ x : ℝ, ‖finitePhysicalSynthesis L K (finiteNormalizedCoefficients v) x‖ ^ 2) = 1 := by
  rw [finitePhysicalSynthesis_energy hL, finiteNormalizedCoefficients_norm v hv]
  norm_num

/-- Cancellation of an already-paid positive physical normalization is
proved for an arbitrary vector, including the harmless zero totalization. -/
theorem finitePhysicalSynthesis_cancel_original_normalization (L : ℝ) (K : ℕ)
    (η : ℝ) (hη : 0 < η) (v : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    (fun x : ℝ => (((η * ‖v‖)⁻¹ : ℝ) : ℂ) *
      ((η : ℂ) * finitePhysicalSynthesis L K v x)) =
      finitePhysicalSynthesis L K (finiteNormalizedCoefficients v) := by
  rw [finitePhysicalSynthesis_normalized]
  funext x
  change (((η * ‖v‖)⁻¹ : ℝ) : ℂ) * ((η : ℂ) * finitePhysicalSynthesis L K v x) =
    ((‖v‖⁻¹ : ℝ) : ℂ) * finitePhysicalSynthesis L K v x
  rw [← mul_assoc, ← Complex.ofReal_mul]
  congr 1
  congr 1
  rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hη.ne', mul_one]

end Zeta23.CCM

#print axioms Zeta23.CCM.finitePhysicalSynthesis_smul
#print axioms Zeta23.CCM.finitePhysicalSynthesis_energy
#print axioms Zeta23.CCM.finiteNormalizedCoefficients_norm
#print axioms Zeta23.CCM.finitePhysicalSynthesis_normalized
#print axioms Zeta23.CCM.finitePhysicalSynthesis_normalized_energy
#print axioms Zeta23.CCM.finitePhysicalSynthesis_cancel_original_normalization
