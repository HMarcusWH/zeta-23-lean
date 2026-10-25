import Zeta23.OPICAFollowup.Consumers

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Zeta23 Zeta23.CCM Zeta23.OPICA Zeta23.ExceptionalZero Zeta23.OPICAFollowup
namespace IndependentArithmeticPhysical

theorem expected_literal_raw_high_mask :
    Tendsto (fun T : ℝ => Real.log (1+max
      (∫ t in Icc (T-2*Real.log T) T,
        finiteHighPair (nativeRawPaletteDrive 1 1) (driveIndexBound T)
          (balancedInverseCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T)) 2)
          (balancedInverseCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T)) 2)
          (fun u : ℝ => Real.exp (Real.sqrt u)) t) 0)/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) :=
  fixed_two_factor_mask_rate_theta.1

theorem expected_literal_absorbed_high_mask :
    Tendsto (fun T : ℝ => Real.log (1+max
      (∫ t in Icc (T-2*Real.log T) T,
        finiteHighPair (nativeAbsorbedPaletteDrive 1 2 1 (by norm_num)) (driveIndexBound T)
          ((nativeLargeCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T))^2 : ArithmeticFunction ℝ))
          ((nativeLargeCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T))^2 : ArithmeticFunction ℝ))
          (fun u : ℝ => Real.exp (Real.sqrt u)) t) 0)/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) :=
  fixed_two_factor_mask_rate_theta.2

theorem expected_quiet_full_original_domain
    (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop)
    (quiet :
      (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
        Real.log (1+max (nativeRawHigh 1 2 1 (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon) ∨
      (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
        Real.log (1+max (nativeAbsorbedHigh 1 2 1 (by norm_num)
          (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon)) :
    nativeZeroDisplacementSup=0 ∧
    (∀ epsilon : ℝ, 0 < epsilon → MemLp
      (fun t : ℝ => ((Real.exp (-epsilon*t)*primeFieldFamily 0 t : ℝ) : ℂ)) 2 volume) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      (∫⁻ t : ℝ in Ici 0, ENNReal.ofReal
        (Real.exp (-2*epsilon*t)*|primeFieldFamily 0 t|^2)) < ∞) ∧
    RiemannHypothesis := by
  have h := quiet_balanced_observation_implies_native_cut time cofinal quiet
  refine ⟨h.1,h.2.1,?_,h.2.2.2.2⟩
  simpa only [NativeOriginalPrimeFieldAllDampedIntegral,
    sourceFamily_zero_eq_original.2.1] using h.2.2.2.1

theorem expected_zero_supremum_all_positive_dampings
    (theta_zero : nativeZeroDisplacementSup=0) :
    ∀ epsilon : ℝ, 0 < epsilon → MemLp
      (fun t : ℝ => ((Real.exp (-epsilon*t)*primeFieldFamily 0 t : ℝ) : ℂ)) 2 volume :=
  originalPrimeField_allDampedL2_of_native_theta_zero theta_zero

/-- The upper law is precisely as strong as zero displacement. This is a
logical strength audit; no independent quiet upper law is supplied. -/
theorem complete_quiet_upper_iff_zero_supremum
    (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop) :
    ((∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
      Real.log (1+max (nativeRawHigh 1 2 1 (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon) ∨
     (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
      Real.log (1+max (nativeAbsorbedHigh 1 2 1 (by norm_num)
        (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon)) ↔
      nativeZeroDisplacementSup=0 := by
  constructor
  · intro quiet
    exact (quiet_balanced_observation_implies_native_cut time cofinal quiet).1
  · intro theta_zero
    left
    intro epsilon hepsilon
    have h := (tendsto_order.1
      (fixed_two_factor_mask_rate_theta.1.comp cofinal)).2 epsilon
      (by simpa only [theta_zero] using hepsilon)
    filter_upwards [h] with n hn
    exact le_of_lt hn

/-- This auxiliary sequence is an adversarial logical control, not a native
prime-field observation. Every finite quiet prefix can coexist with rate one. -/
theorem finite_quiet_samples_do_not_supply_cofinal_upper (N : ℕ) :
    ∃ rate : ℕ → ℝ, (∀ n ≤ N, rate n=0) ∧ Tendsto rate atTop (𝓝 1) := by
  refine ⟨fun n => if n ≤ N then 0 else 1,?_,?_⟩
  · intro n hn
    exact if_pos hn
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop N] with n hn
    simp [not_le_of_gt hn]

#print axioms IndependentArithmeticPhysical.expected_literal_raw_high_mask
#print axioms IndependentArithmeticPhysical.expected_literal_absorbed_high_mask
#print axioms IndependentArithmeticPhysical.expected_quiet_full_original_domain
#print axioms IndependentArithmeticPhysical.expected_zero_supremum_all_positive_dampings
#print axioms IndependentArithmeticPhysical.complete_quiet_upper_iff_zero_supremum
#print axioms IndependentArithmeticPhysical.finite_quiet_samples_do_not_supply_cofinal_upper
end IndependentArithmeticPhysical
