import Zeta23.OPICAFollowup.BoundaryAmplitude

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.generic_forced_profile_unique`
and `Zeta23.OPICAFollowup.generic_boundary_amplitude` (F3).

Definition audits pin the boundary amplitude ζ(ρ)/b_ρ and the generic forced profile
h̃ = 1 - S_ρ/b_ρ - ζ(ρ) x^(ρ-1)/b_ρ built from the actual finite sums, with its explicit
derivative. Both roots are restated in full. Domain consumers check:
- at an actual off-line zero with 1/2 < Re ρ < 1 the generic profile is the zero profile, and the
  two routes (F2 and F3) to the forced log-resolvent agree;
- the plateau diagnostic: a nonzero boundary amplitude means h̃ ≢ 1 on (0, 1), and h̃ is then
  unbounded near 0, so it is not a sharp-gap profile;
- no L¹ assertion is possible in general: if ζ(1 - ρ) ≠ 0 then h̃ is not integrable on (1, ∞),
  because its retained homogeneous term x^(-ρ) is not;
- the generic profile is the only log-form-domain solution of the actual force equation. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real SchwartzMap
open Zeta23.OPICAFollowup
namespace OPICABoundaryAmplitudeIndependent

/-! ### Definition audits -/

theorem audit_boundaryAmplitude (ρ : ℂ) :
    boundaryAmplitude ρ = riemannZeta ρ / normalizationBrho ρ := rfl

theorem audit_genericForcedProfile (ρ : ℂ) (x : ℝ) :
    genericForcedProfile ρ x =
      (1 - finiteSumSrho ρ |x| / normalizationBrho ρ) -
        riemannZeta ρ / normalizationBrho ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) := rfl

theorem audit_genericForcedProfileDeriv (ρ : ℂ) (x : ℝ) :
    genericForcedProfileDeriv ρ x =
      zeroProfileDeriv ρ x - riemannZeta ρ / normalizationBrho ρ * ((ρ - 1) * (x : ℂ) ^ (ρ - 2)) := rfl

theorem audit_normalizationBrho (ρ : ℂ) : normalizationBrho ρ = (1 - 2 * ρ) / (ρ * (1 - ρ)) := rfl

/-! ### Restated roots -/

theorem expected_generic_forced_profile_unique {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    (him : ρ.im ≠ 0) :
    LogFormDomain (genericForcedProfile ρ) (genericForcedProfileDeriv ρ) ∧
    (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * genericForcedProfileDeriv ρ x * deriv φ x) =
        spectralKappa ρ * ((∫ x in Ioi (0 : ℝ), (genericForcedProfile ρ x - 1) * φ x) +
          ∑' n : ℕ, φ (n + 1))) ∧
    (∀ g g' : ℝ → ℂ, LogFormDomain g g' →
      (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
        (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * g' x * deriv φ x) =
          spectralKappa ρ * ((∫ x in Ioi (0 : ℝ), (g x - 1) * φ x) + ∑' n : ℕ, φ (n + 1))) →
      ∀ x : ℝ, 0 < x → g x = genericForcedProfile ρ x) ∧
    LogH1 (logUnitary (genericForcedProfile ρ))
      (logUnitaryDeriv (genericForcedProfile ρ) (genericForcedProfileDeriv ρ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ),
      (∫ t, logUnitaryDeriv (genericForcedProfile ρ) (genericForcedProfileDeriv ρ) t * deriv φ t) +
        (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (genericForcedProfile ρ) t * φ t =
          spectralKappa ρ * nativeLogForce φ) ∧
    (∀ D D' : ℝ → ℂ, LogH1 D D' →
      (∀ φ : 𝓢(ℝ, ℂ), (∫ t, D' t * deriv φ t) + (1 / 4 - spectralKappa ρ) * ∫ t, D t * φ t =
        spectralKappa ρ * nativeLogForce φ) → D = logUnitary (genericForcedProfile ρ)) ∧
    (∀ ξ : ℝ, logFourier (logUnitary (genericForcedProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ)) ∧
    logUnitary (genericForcedProfile ρ) = nativeLogResolvent (spectralKappa ρ) ∧
    (∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖genericForcedProfile ρ x‖ ≤ (1 + ‖boundaryAmplitude ρ‖) * x ^ (ρ.re - 1)) ∧
    (∀ x : ℝ, 0 < x → x < 1 →
      ‖genericForcedProfileDeriv ρ x‖ = ‖boundaryAmplitude ρ * (ρ - 1)‖ * x ^ (ρ.re - 2)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖genericForcedProfile ρ x‖ ≤ C * x ^ (-ρ.re)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖genericForcedProfileDeriv ρ x‖ ≤ C * x ^ (-ρ.re - 1)) :=
  generic_forced_profile_unique h12 h1 him

theorem expected_generic_boundary_amplitude {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    boundaryAmplitude ρ = riemannZeta ρ / normalizationBrho ρ ∧
    normalizationBrho ρ = (1 - 2 * ρ) / spectralKappa ρ ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, genericForcedProfile ρ x = 1 - boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1)) ∧
    ((∀ x ∈ Ioo (0 : ℝ) 1, genericForcedProfile ρ x = 1) ↔ riemannZeta ρ = 0) ∧
    (riemannZeta ρ = 0 → genericForcedProfile ρ = zeroProfile ρ) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖genericForcedProfile ρ x - (-(riemannZeta (1 - ρ) / normalizationBrho ρ) * (x : ℂ) ^ (-ρ) +
        spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2))‖ ≤ C * x ^ (-3 : ℝ)) :=
  generic_boundary_amplitude h12 h1

/-! ### Domain consumers -/

/-- At an actual off-line zero with 1/2 < Re ρ < 1 the generic profile is the zero profile, and the
F2 and F3 identifications of the forced log-resolvent agree. -/
theorem expected_actual_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    (him : ρ.im ≠ 0) :
    genericForcedProfile ρ = zeroProfile ρ ∧
    logUnitary (zeroProfile ρ) = nativeLogResolvent (spectralKappa ρ) ∧
    logUnitary (genericForcedProfile ρ) = logUnitary (zeroProfile ρ) := by
  have hE := (generic_boundary_amplitude h12 h1).2.2.2.2.1 hz
  have hF3 := (generic_forced_profile_unique h12 h1 him).2.2.2.2.2.2.2.1
  rw [hE] at hF3
  exact ⟨hE, hF3, by rw [hE]⟩

/-- A nonzero boundary amplitude destroys the plateau, and h̃ is then unbounded near 0. -/
theorem expected_no_plateau {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) (hζ : riemannZeta ρ ≠ 0) :
    (∃ x ∈ Ioo (0 : ℝ) 1, genericForcedProfile ρ x ≠ 1) ∧
    ∀ B : ℝ, ∃ x ∈ Ioo (0 : ℝ) 1, B < ‖genericForcedProfile ρ x‖ := by
  obtain ⟨-, -, hBA, hiff, -⟩ := generic_boundary_amplitude h12 h1
  refine ⟨?_, fun B => ?_⟩
  · by_contra h
    exact hζ (hiff.mp fun x hx => not_not.mp fun hne => h ⟨x, hx, hne⟩)
  · have h0 : 0 < ρ.re := by linarith
    have hh : ρ ≠ 1 / 2 := fun h => by rw [h] at h12; norm_num at h12
    obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
    have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
    have hA : 0 < ‖boundaryAmplitude ρ‖ := norm_pos_iff.mpr (div_ne_zero hζ hb)
    -- choose x small so that ‖A‖ x^(Re ρ - 1) > B + 1
    set r := 1 - ρ.re
    have hr : 0 < r := by simp only [r]; linarith
    set y := (max B 0 + 2) / ‖boundaryAmplitude ρ‖
    have hy : 0 < y := by positivity
    set x := min (1 / 2) (y ^ (-(1 / r))) with hxdef
    have hx0 : 0 < x := lt_min (by norm_num) (Real.rpow_pos_of_pos hy _)
    have hx1 : x < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    refine ⟨x, ⟨hx0, hx1⟩, ?_⟩
    rw [hBA x ⟨hx0, hx1⟩]
    have hp : ‖(x : ℂ) ^ (ρ - 1)‖ = x ^ (-r) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp [r]
    have hpow : y ≤ x ^ (-r) := by
      have hle : x ≤ y ^ (-(1 / r)) := min_le_right _ _
      have := Real.rpow_le_rpow_of_nonpos hx0 hle (by linarith : -r ≤ 0)
      rwa [← Real.rpow_mul hy.le, show -(1 / r) * -r = 1 by field_simp, Real.rpow_one] at this
    have hbig : max B 0 + 2 ≤ ‖boundaryAmplitude ρ‖ * x ^ (-r) := by
      calc max B 0 + 2 = ‖boundaryAmplitude ρ‖ * y := by simp only [y]; field_simp
        _ ≤ _ := by gcongr
    have htri : ‖boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1)‖ - 1 ≤
        ‖1 - boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1)‖ := by
      have := norm_sub_norm_le (boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1)) 1
      rw [norm_one, norm_sub_rev] at this; linarith
    rw [norm_mul, hp] at htri
    linarith [le_max_left B 0]

/-- No L¹ assertion in general: when ζ(1 - ρ) ≠ 0 the generic profile is not integrable on (1, ∞). -/
theorem expected_not_integrable {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    (hζ' : riemannZeta (1 - ρ) ≠ 0) :
    ¬ IntegrableOn (genericForcedProfile ρ) (Ioi 1) := by
  intro hI
  have h0 : 0 < ρ.re := by linarith
  have hh : ρ ≠ 1 / 2 := fun h => by rw [h] at h12; norm_num at h12
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
  obtain ⟨-, -, -, -, -, C, hC0, hC⟩ := generic_boundary_amplitude h12 h1
  set c := -(riemannZeta (1 - ρ) / normalizationBrho ρ)
  have hc : c ≠ 0 := neg_ne_zero.mpr (div_ne_zero hζ' hb)
  -- the Bernoulli term and the remainder are integrable on (1, ∞)
  have hB : IntegrableOn (fun x : ℝ => spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2)) (Ioi 1) := by
    refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul
      (‖spectralKappa ρ‖ / 2)).mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun x hx => ?_))
    · exact ((measurable_const.mul (Complex.measurable_ofReal.comp measurable_bernoulliTwo)).div
        (measurable_const.mul (Complex.measurable_ofReal.pow_const 2))).aestronglyMeasurable
    · have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
      rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0, Real.rpow_neg hx0.le, Real.rpow_two]
      have := abs_bernoulliTwo_le x
      have hx2 : 0 < x ^ 2 := by positivity
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [norm_nonneg (spectralKappa ρ)]
  have hmeas : AEStronglyMeasurable (fun x : ℝ => c * (x : ℂ) ^ (-ρ) +
      spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2)) (volume.restrict (Ioi 1)) :=
    ((measurable_const.mul (Complex.measurable_ofReal.pow_const _)).add
      ((measurable_const.mul (Complex.measurable_ofReal.comp measurable_bernoulliTwo)).div
        (measurable_const.mul (Complex.measurable_ofReal.pow_const 2)))).aestronglyMeasurable
  have hR : IntegrableOn (fun x : ℝ => genericForcedProfile ρ x -
      (c * (x : ℂ) ^ (-ρ) + spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2))) (Ioi 1) :=
    Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) one_pos).const_mul C)
      (hI.aestronglyMeasurable.sub hmeas)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => hC x (le_of_lt hx)))
  have hpow : IntegrableOn (fun x : ℝ => c * (x : ℂ) ^ (-ρ)) (Ioi 1) :=
    ((hI.sub hR).sub hB).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  have hnorm : IntegrableOn (fun x : ℝ => x ^ (-ρ.re)) (Ioi 1) := by
    refine (hpow.norm.const_mul ‖c‖⁻¹).congr ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    simp only
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, ← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc), one_mul]
    simp
  have := (integrableOn_Ioi_rpow_iff one_pos).mp hnorm
  linarith

end OPICABoundaryAmplitudeIndependent

#print axioms Zeta23.OPICAFollowup.generic_forced_profile_unique
#print axioms Zeta23.OPICAFollowup.generic_boundary_amplitude
#print axioms OPICABoundaryAmplitudeIndependent.audit_genericForcedProfile
#print axioms OPICABoundaryAmplitudeIndependent.expected_generic_forced_profile_unique
#print axioms OPICABoundaryAmplitudeIndependent.expected_generic_boundary_amplitude
#print axioms OPICABoundaryAmplitudeIndependent.expected_actual_zero
#print axioms OPICABoundaryAmplitudeIndependent.expected_no_plateau
#print axioms OPICABoundaryAmplitudeIndependent.expected_not_integrable
