import Zeta23.OPICARound4.AdaptiveBudget
import Zeta23.OPICARound4.NativeConcentrationBudget
import Zeta23.OPICARound4.OddReciprocalSource

noncomputable section
namespace Zeta23.OPICARound4.Validation
open CCM MeasureTheory
open scoped Interval

/-- Exact native cost root, independent of the coefficient-space dimension. -/
example (K : ℕ) {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω ≤ 1) :
    ‖nativeSourceAtom K ω‖ ≤ 2 := nativeSourceAtom_norm_le_two K h0 h1

example (K : ℕ) {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω ≤ 1)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖sourceAtomPairing K h u ω‖ ≤
      Real.sqrt (sourceConcentration K ω h * sourceConcentration K ω u) :=
  native_source_mixed_concentration_bound K h0 h1 h u

example (K : ℕ) {ω : ℝ} (h0 : 0 ≤ ω) (h1 : ω ≤ 1)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖(sourceMatrix ω K).toEuclideanLin u‖ ^ 2 ≤ 2 * sourceConcentration K ω u :=
  native_source_square_concentration_full K h0 h1 u

example (K : ℕ) {ω : ℝ} (h0 : 0 ≤ ω) (hhalf : ω ≤ 1 / 2)
    (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖(sourceMatrix ω K).toEuclideanLin u‖ ^ 2 ≤ sourceConcentration K ω u :=
  native_source_square_concentration_half K h0 hhalf u

/-- Endpoint multiplicity control: full aperture carries twice the coefficient
energy. Extending the half-range carrier estimate would contradict this. -/
example (K : ℕ) (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceConcentration K 1 u = 2 * ‖u‖ ^ 2 := by
  simp only [sourceConcentration, sub_self, add_zero]
  change (∫ t in (0 : ℝ)..1, ‖localizedFiniteFunction 1 K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) u) t‖ ^ 2) +
    (∫ t in (0 : ℝ)..1, ‖localizedFiniteFunction 1 K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) u) t‖ ^ 2) = 2 * ‖u‖ ^ 2
  simp only [localizedFiniteFunction_unit_energy_eq_norm_sq]
  ring

example (K : ℕ) (u : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourceExchangeMinus K 1 u = 0 := by
  simp [sourceExchangeMinus]

/-- This consumer requires the actual even resolvent/Riesz test in the odd
orientation, with its physical norm and variation preserved. -/
example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    let u := (poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam).symm
      (poleNeutralCorrectedCubicRieszVector L K)
    correctedSourceTest L K u ∈ nativeAdaptiveTestClass L
      (2 * ‖correctedSourceRow L K‖ * ‖u‖) (nativeCorrectedVariation L K u) :=
  actual_odd_resolvent_adaptive_membership hL K hK lam hlam

/-- The response-facing odd input is reciprocal and has a signed conjugate
source identity; it is not the Riesz-input support test above. -/
example {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    poleNeutralCubicPairingFunctional L K (poleNeutralOddAdjointShiftedRay hL K hK lam hlam) =
      -(starRingEnd ℂ) (poleNeutralCorrectedCubicSource L K
        (nativeOddReciprocalInput hL K hK lam hlam)) :=
  native_odd_response_eq_reciprocal_source hL K hK lam hlam

end Zeta23.OPICARound4.Validation

-- BEGIN SOURCE DECLARATION TYPES AND TRANSITIVE AXIOM AUDIT

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSourceAtom"
#check @Zeta23.OPICARound4.nativeSourceAtom
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSourceAtom"
#print axioms Zeta23.OPICARound4.nativeSourceAtom

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSourceAtom_symmetric"
#check @Zeta23.OPICARound4.nativeSourceAtom_symmetric
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSourceAtom_symmetric"
#print axioms Zeta23.OPICARound4.nativeSourceAtom_symmetric

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSourceAtom_norm_le_two"
#check @Zeta23.OPICARound4.nativeSourceAtom_norm_le_two
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSourceAtom_norm_le_two"
#print axioms Zeta23.OPICARound4.nativeSourceAtom_norm_le_two

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeSourceAtom_apply_norm"
#check @Zeta23.OPICARound4.nativeSourceAtom_apply_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeSourceAtom_apply_norm"
#print axioms Zeta23.OPICARound4.nativeSourceAtom_apply_norm

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_mixed_norm"
#check @Zeta23.OPICARound4.native_source_mixed_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_mixed_norm"
#print axioms Zeta23.OPICARound4.native_source_mixed_norm

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.primeSourceCoordinate_mem_unit"
#check @Zeta23.OPICARound4.primeSourceCoordinate_mem_unit
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.primeSourceCoordinate_mem_unit"
#print axioms Zeta23.OPICARound4.primeSourceCoordinate_mem_unit

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativePrimeMass"
#check @Zeta23.OPICARound4.nativePrimeMass
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativePrimeMass"
#print axioms Zeta23.OPICARound4.nativePrimeMass

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_row_budget"
#check @Zeta23.OPICARound4.native_prime_row_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_row_budget"
#print axioms Zeta23.OPICARound4.native_prime_row_budget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeCompleteRowBudget"
#check @Zeta23.OPICARound4.nativeCompleteRowBudget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeCompleteRowBudget"
#print axioms Zeta23.OPICARound4.nativeCompleteRowBudget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeCompleteRowBudget_nonneg"
#check @Zeta23.OPICARound4.nativeCompleteRowBudget_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeCompleteRowBudget_nonneg"
#print axioms Zeta23.OPICARound4.nativeCompleteRowBudget_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_complete_row_budget"
#check @Zeta23.OPICARound4.native_complete_row_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_complete_row_budget"
#print axioms Zeta23.OPICARound4.native_complete_row_budget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_corrected_riesz_budget"
#check @Zeta23.OPICARound4.native_corrected_riesz_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_corrected_riesz_budget"
#print axioms Zeta23.OPICARound4.native_corrected_riesz_budget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_inverse_adjoint_cost"
#check @Zeta23.OPICARound4.native_inverse_adjoint_cost
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_inverse_adjoint_cost"
#print axioms Zeta23.OPICARound4.native_inverse_adjoint_cost

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_even_complete_signed_budget"
#check @Zeta23.OPICARound4.native_even_complete_signed_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_even_complete_signed_budget"
#print axioms Zeta23.OPICARound4.native_even_complete_signed_budget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_complete_signed_budget"
#check @Zeta23.OPICARound4.native_odd_complete_signed_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_complete_signed_budget"
#print axioms Zeta23.OPICARound4.native_odd_complete_signed_budget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceFiniteFourier"
#check @Zeta23.OPICARound4.sourceFiniteFourier
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceFiniteFourier"
#print axioms Zeta23.OPICARound4.sourceFiniteFourier

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceFiniteFourier_continuous"
#check @Zeta23.OPICARound4.sourceFiniteFourier_continuous
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceFiniteFourier_continuous"
#print axioms Zeta23.OPICARound4.sourceFiniteFourier_continuous

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangePlus"
#check @Zeta23.OPICARound4.sourceExchangePlus
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangePlus"
#print axioms Zeta23.OPICARound4.sourceExchangePlus

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangeMinus"
#check @Zeta23.OPICARound4.sourceExchangeMinus
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangeMinus"
#print axioms Zeta23.OPICARound4.sourceExchangeMinus

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceConcentration"
#check @Zeta23.OPICARound4.sourceConcentration
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceConcentration"
#print axioms Zeta23.OPICARound4.sourceConcentration

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangeMixed"
#check @Zeta23.OPICARound4.sourceExchangeMixed
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangeMixed"
#print axioms Zeta23.OPICARound4.sourceExchangeMixed

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceConcentration_eq_plus_add_minus"
#check @Zeta23.OPICARound4.sourceConcentration_eq_plus_add_minus
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceConcentration_eq_plus_add_minus"
#print axioms Zeta23.OPICARound4.sourceConcentration_eq_plus_add_minus

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchange_nonneg"
#check @Zeta23.OPICARound4.sourceExchange_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchange_nonneg"
#print axioms Zeta23.OPICARound4.sourceExchange_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceConcentration_nonneg"
#check @Zeta23.OPICARound4.sourceConcentration_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceConcentration_nonneg"
#print axioms Zeta23.OPICARound4.sourceConcentration_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceConcentration_le_two_norm_sq"
#check @Zeta23.OPICARound4.sourceConcentration_le_two_norm_sq
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceConcentration_le_two_norm_sq"
#print axioms Zeta23.OPICARound4.sourceConcentration_le_two_norm_sq

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceConcentration_le_norm_sq_of_half"
#check @Zeta23.OPICARound4.sourceConcentration_le_norm_sq_of_half
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceConcentration_le_norm_sq_of_half"
#print axioms Zeta23.OPICARound4.sourceConcentration_le_norm_sq_of_half

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangeMixed_self_eq_native"
#check @Zeta23.OPICARound4.sourceExchangeMixed_self_eq_native
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangeMixed_self_eq_native"
#print axioms Zeta23.OPICARound4.sourceExchangeMixed_self_eq_native

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_energy_eq_exchange_difference"
#check @Zeta23.OPICARound4.native_source_energy_eq_exchange_difference
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_energy_eq_exchange_difference"
#print axioms Zeta23.OPICARound4.native_source_energy_eq_exchange_difference

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangeMixed_norm_sq_le"
#check @Zeta23.OPICARound4.sourceExchangeMixed_norm_sq_le
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangeMixed_norm_sq_le"
#print axioms Zeta23.OPICARound4.sourceExchangeMixed_norm_sq_le

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceFiniteFourier_eq_sum_exp"
#check @Zeta23.OPICARound4.sourceFiniteFourier_eq_sum_exp
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceFiniteFourier_eq_sum_exp"
#print axioms Zeta23.OPICARound4.sourceFiniteFourier_eq_sum_exp

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.sourceExchangeMixed_eq_native"
#check @Zeta23.OPICARound4.sourceExchangeMixed_eq_native
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.sourceExchangeMixed_eq_native"
#print axioms Zeta23.OPICARound4.sourceExchangeMixed_eq_native

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_mixed_concentration_bound"
#check @Zeta23.OPICARound4.native_source_mixed_concentration_bound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_mixed_concentration_bound"
#print axioms Zeta23.OPICARound4.native_source_mixed_concentration_bound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_square_concentration_full"
#check @Zeta23.OPICARound4.native_source_square_concentration_full
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_square_concentration_full"
#print axioms Zeta23.OPICARound4.native_source_square_concentration_full

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_square_concentration_half"
#check @Zeta23.OPICARound4.native_source_square_concentration_half
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_square_concentration_half"
#print axioms Zeta23.OPICARound4.native_source_square_concentration_half

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativePrimeConcentrationBudget"
#check @Zeta23.OPICARound4.nativePrimeConcentrationBudget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativePrimeConcentrationBudget"
#print axioms Zeta23.OPICARound4.nativePrimeConcentrationBudget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_concentration_budget"
#check @Zeta23.OPICARound4.native_prime_concentration_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_concentration_budget"
#print axioms Zeta23.OPICARound4.native_prime_concentration_budget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_half_coordinate_iff"
#check @Zeta23.OPICARound4.native_prime_half_coordinate_iff
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_half_coordinate_iff"
#print axioms Zeta23.OPICARound4.native_prime_half_coordinate_iff

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeLatePrimePowers"
#check @Zeta23.OPICARound4.nativeLatePrimePowers
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeLatePrimePowers"
#print axioms Zeta23.OPICARound4.nativeLatePrimePowers

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeOldPrimePowers"
#check @Zeta23.OPICARound4.nativeOldPrimePowers
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeOldPrimePowers"
#print axioms Zeta23.OPICARound4.nativeOldPrimePowers

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_power_regime_partition"
#check @Zeta23.OPICARound4.native_prime_power_regime_partition
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_power_regime_partition"
#print axioms Zeta23.OPICARound4.native_prime_power_regime_partition

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_late_prime_concentration"
#check @Zeta23.OPICARound4.native_late_prime_concentration
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_late_prime_concentration"
#print axioms Zeta23.OPICARound4.native_late_prime_concentration

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_old_prime_concentration"
#check @Zeta23.OPICARound4.native_old_prime_concentration
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_old_prime_concentration"
#print axioms Zeta23.OPICARound4.native_old_prime_concentration

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_late_mixed_concentration_cost"
#check @Zeta23.OPICARound4.native_late_mixed_concentration_cost
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_late_mixed_concentration_cost"
#print axioms Zeta23.OPICARound4.native_late_mixed_concentration_cost

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_old_mixed_concentration_cost"
#check @Zeta23.OPICARound4.native_old_mixed_concentration_cost
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_old_mixed_concentration_cost"
#print axioms Zeta23.OPICARound4.native_old_mixed_concentration_cost

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_concentration_budget_regime_fallback"
#check @Zeta23.OPICARound4.native_prime_concentration_budget_regime_fallback
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_concentration_budget_regime_fallback"
#print axioms Zeta23.OPICARound4.native_prime_concentration_budget_regime_fallback

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_complete_concentration_budget"
#check @Zeta23.OPICARound4.native_complete_concentration_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_complete_concentration_budget"
#print axioms Zeta23.OPICARound4.native_complete_concentration_budget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_corrected_source_concentration_real_interval"
#check @Zeta23.OPICARound4.native_corrected_source_concentration_real_interval
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_corrected_source_concentration_real_interval"
#print axioms Zeta23.OPICARound4.native_corrected_source_concentration_real_interval

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_concentration_real_interval"
#check @Zeta23.OPICARound4.native_odd_concentration_real_interval
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_concentration_real_interval"
#print axioms Zeta23.OPICARound4.native_odd_concentration_real_interval

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.psi_eq_sum_Icc_two"
#check @Zeta23.OPICARound4.psi_eq_sum_Icc_two
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.psi_eq_sum_Icc_two"
#print axioms Zeta23.OPICARound4.psi_eq_sum_Icc_two

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.prime_log_mem_interval"
#check @Zeta23.OPICARound4.prime_log_mem_interval
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.prime_log_mem_interval"
#print axioms Zeta23.OPICARound4.prime_log_mem_interval

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.psi_exp_eq_sum_steps"
#check @Zeta23.OPICARound4.psi_exp_eq_sum_steps
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.psi_exp_eq_sum_steps"
#print axioms Zeta23.OPICARound4.psi_exp_eq_sum_steps

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.prime_log_abel"
#check @Zeta23.OPICARound4.prime_log_abel
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.prime_log_abel"
#print axioms Zeta23.OPICARound4.prime_log_abel

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.intervalIntegrable_psi_exp_mul"
#check @Zeta23.OPICARound4.intervalIntegrable_psi_exp_mul
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.intervalIntegrable_psi_exp_mul"
#print axioms Zeta23.OPICARound4.intervalIntegrable_psi_exp_mul

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.exp_neg_log_half_eq_inv_sqrt"
#check @Zeta23.OPICARound4.exp_neg_log_half_eq_inv_sqrt
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.exp_neg_log_half_eq_inv_sqrt"
#print axioms Zeta23.OPICARound4.exp_neg_log_half_eq_inv_sqrt

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.prime_discrepancy_log_integral"
#check @Zeta23.OPICARound4.prime_discrepancy_log_integral
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.prime_discrepancy_log_integral"
#print axioms Zeta23.OPICARound4.prime_discrepancy_log_integral

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceTestDerivative"
#check @Zeta23.OPICARound4.correctedSourceTestDerivative
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceTestDerivative"
#print axioms Zeta23.OPICARound4.correctedSourceTestDerivative

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.correctedSourceTestDerivative_continuous"
#check @Zeta23.OPICARound4.correctedSourceTestDerivative_continuous
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.correctedSourceTestDerivative_continuous"
#print axioms Zeta23.OPICARound4.correctedSourceTestDerivative_continuous

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_prime_discrepancy_integral"
#check @Zeta23.OPICARound4.native_prime_discrepancy_integral
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_prime_discrepancy_integral"
#print axioms Zeta23.OPICARound4.native_prime_discrepancy_integral

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeAdaptiveTestClass"
#check @Zeta23.OPICARound4.nativeAdaptiveTestClass
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeAdaptiveTestClass"
#print axioms Zeta23.OPICARound4.nativeAdaptiveTestClass

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.UniformPrimeDiscrepancyBound"
#check @Zeta23.OPICARound4.UniformPrimeDiscrepancyBound
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.UniformPrimeDiscrepancyBound"
#print axioms Zeta23.OPICARound4.UniformPrimeDiscrepancyBound

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeCorrectedVariation"
#check @Zeta23.OPICARound4.nativeCorrectedVariation
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeCorrectedVariation"
#print axioms Zeta23.OPICARound4.nativeCorrectedVariation

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_inverse_gap_norm"
#check @Zeta23.OPICARound4.native_inverse_gap_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_inverse_gap_norm"
#print axioms Zeta23.OPICARound4.native_inverse_gap_norm

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_even_ray_gap_norm"
#check @Zeta23.OPICARound4.actual_even_ray_gap_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_even_ray_gap_norm"
#print axioms Zeta23.OPICARound4.actual_even_ray_gap_norm

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_resolvent_gap_norm"
#check @Zeta23.OPICARound4.actual_odd_resolvent_gap_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_resolvent_gap_norm"
#print axioms Zeta23.OPICARound4.actual_odd_resolvent_gap_norm

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeCorrectedVariation_nonneg"
#check @Zeta23.OPICARound4.nativeCorrectedVariation_nonneg
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeCorrectedVariation_nonneg"
#print axioms Zeta23.OPICARound4.nativeCorrectedVariation_nonneg

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_source_selected_membership"
#check @Zeta23.OPICARound4.native_source_selected_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_source_selected_membership"
#print axioms Zeta23.OPICARound4.native_source_selected_membership

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_even_ray_adaptive_membership"
#check @Zeta23.OPICARound4.actual_even_ray_adaptive_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_even_ray_adaptive_membership"
#print axioms Zeta23.OPICARound4.actual_even_ray_adaptive_membership

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_resolvent_adaptive_membership"
#check @Zeta23.OPICARound4.actual_odd_resolvent_adaptive_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_resolvent_adaptive_membership"
#print axioms Zeta23.OPICARound4.actual_odd_resolvent_adaptive_membership

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_even_ray_priced_membership"
#check @Zeta23.OPICARound4.actual_even_ray_priced_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_even_ray_priced_membership"
#print axioms Zeta23.OPICARound4.actual_even_ray_priced_membership

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_resolvent_priced_membership"
#check @Zeta23.OPICARound4.actual_odd_resolvent_priced_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_resolvent_priced_membership"
#print axioms Zeta23.OPICARound4.actual_odd_resolvent_priced_membership

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeArchContinuumRow"
#check @Zeta23.OPICARound4.nativeArchContinuumRow
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeArchContinuumRow"
#print axioms Zeta23.OPICARound4.nativeArchContinuumRow

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_adaptive_complete_budget"
#check @Zeta23.OPICARound4.native_adaptive_complete_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_adaptive_complete_budget"
#print axioms Zeta23.OPICARound4.native_adaptive_complete_budget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_real_shift_inverse_symmetric"
#check @Zeta23.OPICARound4.native_real_shift_inverse_symmetric
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_real_shift_inverse_symmetric"
#print axioms Zeta23.OPICARound4.native_real_shift_inverse_symmetric

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.nativeOddReciprocalInput"
#check @Zeta23.OPICARound4.nativeOddReciprocalInput
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.nativeOddReciprocalInput"
#print axioms Zeta23.OPICARound4.nativeOddReciprocalInput

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_response_eq_reciprocal_source"
#check @Zeta23.OPICARound4.native_odd_response_eq_reciprocal_source
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_response_eq_reciprocal_source"
#print axioms Zeta23.OPICARound4.native_odd_response_eq_reciprocal_source

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_response_complete_arithmetic"
#check @Zeta23.OPICARound4.native_odd_response_complete_arithmetic
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_response_complete_arithmetic"
#print axioms Zeta23.OPICARound4.native_odd_response_complete_arithmetic

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_reciprocal_adaptive_membership"
#check @Zeta23.OPICARound4.actual_odd_reciprocal_adaptive_membership
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_reciprocal_adaptive_membership"
#print axioms Zeta23.OPICARound4.actual_odd_reciprocal_adaptive_membership

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.actual_odd_reciprocal_gap_norm"
#check @Zeta23.OPICARound4.actual_odd_reciprocal_gap_norm
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.actual_odd_reciprocal_gap_norm"
#print axioms Zeta23.OPICARound4.actual_odd_reciprocal_gap_norm

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_adaptive_response_budget"
#check @Zeta23.OPICARound4.native_odd_adaptive_response_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_adaptive_response_budget"
#print axioms Zeta23.OPICARound4.native_odd_adaptive_response_budget

#eval IO.println "OPICA4_TYPE_BEGIN Zeta23.OPICARound4.native_odd_response_lt_one_of_adaptive_budget"
#check @Zeta23.OPICARound4.native_odd_response_lt_one_of_adaptive_budget
#eval IO.println "OPICA4_TYPE_END Zeta23.OPICARound4.native_odd_response_lt_one_of_adaptive_budget"
#print axioms Zeta23.OPICARound4.native_odd_response_lt_one_of_adaptive_budget
