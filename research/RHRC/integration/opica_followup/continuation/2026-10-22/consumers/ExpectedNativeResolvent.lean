import Zeta23.OPICAFollowup.NativeResolvent

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.native_forced_resolvent_unique`,
`Zeta23.OPICAFollowup.native_sample_stieltjes_identity` and
`Zeta23.OPICAFollowup.native_profile_spectral_norms` (F2).

Definition audits pin the forced log-resolvent as the inverse log-Fourier transform of the actual
quotient κ ζ(1/2 + iξ)/(a(ξ) - κ), the log profile e^(t/2) h(e^t) and the sample defect
b = Σ_{n ≥ 1} h(n) - 1/2. All three roots are restated in full. Domain consumers check:
- an actual off-line zero (Re ρ ≠ 1/2, Im ρ ≠ 0, as the statement requires) has nonreal κ, so its log
  profile is the forced log-resolvent and b = κ M(κ);
- for such a zero b ≠ 0 and Im(b/κ)/Im κ = ∫ dω/|a - κ|² > 0, with b/κ = M(κ) identified with the
  Stage 12 sampling ratio, so the two derivations of (S2.4) agree;
- the forced log-resolvent itself is an H¹ weak solution;
- the diagonal mixed pairing N(ρ, ρ) is the norm formula, cast to ℂ;
- at the conjugate zero conj ρ (conjugate coincidence) the undivided identity forces
  b_{conj ρ} = conj b_ρ, which is consistent with M(conj κ) = conj M(κ);
- at a critical-line zero (κ on the cut, where no root is asserted) the supporting undivided
  identity reads (ξ² - (Im ρ)²) 𝓕_log ψ(ξ) = κ ζ(1/2 + iξ); both sides vanish at ξ = Im ρ. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real SchwartzMap
open Zeta23.OPICAFollowup
namespace OPICANativeResolventIndependent

/-! ### Definition audits -/

theorem audit_nativeLogResolvent (κ : ℂ) (t : ℝ) :
    nativeLogResolvent κ t = 1 / (2 * π) * ∫ ξ : ℝ, cexp (((ξ * t : ℝ) : ℂ) * I) *
      (κ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - κ)) := rfl

theorem audit_logUnitary (h : ℝ → ℂ) (t : ℝ) :
    logUnitary h t = (Real.exp (t / 2) : ℂ) * h (Real.exp t) := rfl

theorem audit_profileSampleDefect (ρ : ℂ) :
    profileSampleDefect ρ = (∑' n : ℕ, zeroProfile ρ (n + 1)) - 1 / 2 := rfl

theorem audit_spectralKappa (ρ : ℂ) : spectralKappa ρ = ρ * (1 - ρ) := rfl

/-! ### Restated roots -/

theorem expected_native_forced_resolvent_unique {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    LogH1 (logUnitary (zeroProfile ρ)) (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv φ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (zeroProfile ρ) t * φ t =
        spectralKappa ρ * nativeLogForce φ) ∧
    (∀ D D' : ℝ → ℂ, LogH1 D D' →
      (∀ φ : 𝓢(ℝ, ℂ), (∫ t, D' t * deriv φ t) + (1 / 4 - spectralKappa ρ) * ∫ t, D t * φ t =
        spectralKappa ρ * nativeLogForce φ) → D = logUnitary (zeroProfile ρ)) ∧
    (∀ ξ : ℝ, logFourier (logUnitary (zeroProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ)) ∧
    logUnitary (zeroProfile ρ) = nativeLogResolvent (spectralKappa ρ) :=
  native_forced_resolvent_unique hz h0 h1 hκ

theorem expected_native_sample_stieltjes_identity {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    profileSampleDefect ρ = (∑' n : ℕ, zeroProfile ρ (n + 1)) - 1 / 2 ∧
    (∀ n : ℕ, ∫ x in (n : ℝ)..(n + 1), ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x =
      zeroProfile ρ ((n : ℝ) + 1) - ∫ x in (n : ℝ)..(n + 1), zeroProfile ρ x) ∧
    IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x) (Ioi 0) ∧
    profileSampleDefect ρ = ∫ x in Ioi (0 : ℝ), ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x ∧
    profileSampleDefect ρ = ∫ t, sawtoothWeight t *
      (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t - logUnitary (zeroProfile ρ) t / 2) ∧
    ‖profileSampleDefect ρ‖ ≤ (∫ t, ‖sawtoothWeight t‖ ^ 2) ^ (1 / 2 : ℝ) *
      ((∫ t, ‖logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t‖ ^ 2) +
        1 / 4 * ∫ t, ‖logUnitary (zeroProfile ρ) t‖ ^ 2) ^ (1 / 2 : ℝ) ∧
    (∀ t, starRingEnd ℂ (sawtoothWeight t) = sawtoothWeight t) ∧
    profileSampleDefect ρ = 1 / (2 * π) * ∫ ξ : ℝ, starRingEnd ℂ (logFourier sawtoothWeight ξ) *
      (((ξ : ℂ) * I - 1 / 2) * logFourier (logUnitary (zeroProfile ρ)) ξ) ∧
    profileSampleDefect ρ = spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ) :=
  native_sample_stieltjes_identity hz h0 h1 hκ

theorem expected_native_profile_spectral_norms {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : (spectralKappa ρ).im ≠ 0) :
    ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 =
      ‖spectralKappa ρ‖ ^ 2 *
        ∫ ξ, (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    logForm (zeroProfileDeriv ρ) =
      ‖spectralKappa ρ‖ ^ 2 * ∫ ξ, spectralEnergy ξ *
        (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 =
      ‖spectralKappa ρ‖ ^ 2 * ((arithmeticStieltjes (spectralKappa ρ)).im / (spectralKappa ρ).im) ∧
    (∀ σ : ℂ, riemannZeta σ = 0 → 0 < σ.re → σ.re < 1 → spectralKappa σ ∈ spectralResolventSet →
      profileGram ρ σ = spectralKappa ρ * starRingEnd ℂ (spectralKappa σ) *
        ∫ ξ, (((spectralEnergy ξ : ℂ) - spectralKappa ρ) *
          ((spectralEnergy ξ : ℂ) - starRingEnd ℂ (spectralKappa σ)))⁻¹ ∂arithmeticSpectralMeasure ∧
      profileFormGram ρ σ = spectralKappa ρ * starRingEnd ℂ (spectralKappa σ) *
        ∫ ξ, (spectralEnergy ξ : ℂ) * (((spectralEnergy ξ : ℂ) - spectralKappa ρ) *
          ((spectralEnergy ξ : ℂ) - starRingEnd ℂ (spectralKappa σ)))⁻¹ ∂arithmeticSpectralMeasure ∧
      (spectralKappa ρ - starRingEnd ℂ (spectralKappa σ)) * profileGram ρ σ =
        starRingEnd ℂ (spectralKappa σ) * profileSampleDefect ρ -
          spectralKappa ρ * starRingEnd ℂ (profileSampleDefect σ)) ∧
    ‖profileSampleDefect ρ‖ ≤ ‖spectralKappa ρ‖ * (1 + ‖spectralKappa ρ‖ / |(spectralKappa ρ).im|) *
      (Real.log (2 * π) - Real.eulerMascheroniConstant) :=
  native_profile_spectral_norms hz h0 h1 hκ

/-! ### Domain consumers -/

lemma offline_kappa_im {ρ : ℂ} (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) : (spectralKappa ρ).im ≠ 0 := by
  have hk : (spectralKappa ρ).im = (1 - 2 * ρ.re) * ρ.im := by
    simp only [spectralKappa, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    ring
  rw [hk]
  exact mul_ne_zero (fun h => hre (by linarith)) him

/-- An actual off-line zero has nonreal κ: its log profile is the forced log-resolvent and
b = κ M(κ). -/
theorem expected_offline_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    (spectralKappa ρ).im ≠ 0 ∧
    logUnitary (zeroProfile ρ) = nativeLogResolvent (spectralKappa ρ) ∧
    profileSampleDefect ρ = spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ) := by
  have hk := offline_kappa_im hre him
  exact ⟨hk, (native_forced_resolvent_unique hz h0 h1 (Or.inl hk)).2.2.2.2,
    (native_sample_stieltjes_identity hz h0 h1 (Or.inl hk)).2.2.2.2.2.2.2.2⟩

/-- For nonreal κ the sample defect is nonzero, b/κ = M(κ), and the Stage 12 sampling ratio
Im(b/κ)/Im κ = N/|κ|² equals the measure ratio ∫ dω/|a - κ|² > 0. -/
theorem expected_sample_ratio {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : (spectralKappa ρ).im ≠ 0) :
    profileSampleDefect ρ / spectralKappa ρ = arithmeticStieltjes (spectralKappa ρ) ∧
    (profileSampleDefect ρ / spectralKappa ρ).im / (spectralKappa ρ).im =
      ∫ ξ, (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    0 < (profileSampleDefect ρ / spectralKappa ρ).im / (spectralKappa ρ).im ∧
    profileSampleDefect ρ ≠ 0 := by
  have hk0 : spectralKappa ρ ≠ 0 := fun h => hκ (by rw [h, Complex.zero_im])
  have hb := (native_sample_stieltjes_identity hz h0 h1 (Or.inl hκ)).2.2.2.2.2.2.2.2
  obtain ⟨-, hIm, hpos, -⟩ := arithmetic_stieltjes_sign_budget hκ
  have hM : profileSampleDefect ρ / spectralKappa ρ = arithmeticStieltjes (spectralKappa ρ) := by
    rw [hb]; field_simp
  refine ⟨hM, by rw [hM, hIm], by rw [hM, hIm]; exact hpos, fun h0b => ?_⟩
  have : (arithmeticStieltjes (spectralKappa ρ)).im = 0 := by
    rw [← hM, h0b, zero_div, Complex.zero_im]
  rw [this, zero_div] at hIm
  linarith

/-- The forced log-resolvent is itself an H¹ weak solution of the forced equation. -/
theorem expected_resolvent_weak_solution {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    LogH1 (nativeLogResolvent (spectralKappa ρ)) (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ)) ∧
    ∀ φ : 𝓢(ℝ, ℂ), (∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv φ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, nativeLogResolvent (spectralKappa ρ) t * φ t =
        spectralKappa ρ * nativeLogForce φ := by
  obtain ⟨hD, hW, -, -, hEq⟩ := native_forced_resolvent_unique hz h0 h1 hκ
  rw [← hEq]
  exact ⟨hD, hW⟩

/-- The diagonal mixed pairing is the norm formula: N(ρ, ρ) = ∫ |h|² = |κ|² ∫ dω/|a - κ|². -/
theorem expected_diagonal_gram {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : (spectralKappa ρ).im ≠ 0) :
    profileGram ρ ρ = ((∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨hN, -, -, hmix, -⟩ := native_profile_spectral_norms hz h0 h1 hκ
  rw [(hmix ρ hz h0 h1 (Or.inl hκ)).1, hN, Complex.ofReal_mul, ← integral_complex_ofReal]
  have hk : spectralKappa ρ * starRingEnd ℂ (spectralKappa ρ) = ((‖spectralKappa ρ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; ring
  rw [hk]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  have hc : (spectralEnergy ξ : ℂ) - starRingEnd ℂ (spectralKappa ρ) =
      starRingEnd ℂ ((spectralEnergy ξ : ℂ) - spectralKappa ρ) := by
    rw [map_sub, Complex.conj_ofReal]
  simp only
  rw [hc, Complex.mul_conj']
  push_cast; ring

/-- Conjugate coincidence: conj ρ is again an actual zero with κ(conj ρ) = conj κ(ρ); the undivided
identity at (ρ, conj ρ) has vanishing left side and forces b_{conj ρ} = conj b_ρ, which matches
M(conj κ) = conj M(κ) on the measure side. -/
theorem expected_conjugate_coincidence {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : (spectralKappa ρ).im ≠ 0) :
    spectralKappa (starRingEnd ℂ ρ) = starRingEnd ℂ (spectralKappa ρ) ∧
    profileSampleDefect (starRingEnd ℂ ρ) = starRingEnd ℂ (profileSampleDefect ρ) := by
  have hzc : riemannZeta (starRingEnd ℂ ρ) = 0 := by rw [riemannZeta_conj, hz, map_zero]
  have hkc : spectralKappa (starRingEnd ℂ ρ) = starRingEnd ℂ (spectralKappa ρ) := by
    simp only [spectralKappa, map_mul, map_sub, map_one]
  have hκc : (spectralKappa (starRingEnd ℂ ρ)).im ≠ 0 := by
    rw [hkc, Complex.conj_im]; exact neg_ne_zero.mpr hκ
  have h0c : 0 < (starRingEnd ℂ ρ).re := by rwa [Complex.conj_re]
  have h1c : (starRingEnd ℂ ρ).re < 1 := by rwa [Complex.conj_re]
  refine ⟨hkc, ?_⟩
  obtain ⟨-, -, -, hmix, -⟩ := native_profile_spectral_norms hzc h0c h1c hκc
  have hU := (hmix ρ hz h0 h1 (Or.inl hκ)).2.2
  rw [hkc, sub_self, zero_mul] at hU
  have hk0 : starRingEnd ℂ (spectralKappa ρ) ≠ 0 := by
    intro h; apply hκ; rw [← Complex.conj_conj (spectralKappa ρ), h, map_zero, Complex.zero_im]
  have := mul_left_cancel₀ hk0 (sub_eq_zero.mp hU.symm)
  exact this

/-- At a critical-line zero the supporting undivided identity holds with multiplier ξ² - (Im ρ)²,
and both of its sides vanish at ξ = Im ρ (the quotient is not formed there). -/
theorem expected_critical_line_undivided {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hre : ρ.re = 1 / 2) :
    (∀ ξ : ℝ, (((ξ ^ 2 - ρ.im ^ 2 : ℝ)) : ℂ) * logFourier (logUnitary (zeroProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I)) ∧
    spectralKappa ρ * riemannZeta (1 / 2 + ρ.im * I) = 0 := by
  have hρ : ρ = (1 / 2 : ℂ) + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hk : spectralKappa ρ = ((1 / 4 + ρ.im ^ 2 : ℝ) : ℂ) := by
    rw [spectralKappa]
    conv_lhs => rw [hρ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  refine ⟨fun ξ => ?_, ?_⟩
  · have h := logFourier_zeroProfile_undivided hz h0 h1 ξ
    rw [hk, spectralEnergy] at h
    rw [hk, ← h]
    push_cast; ring
  · rw [← hρ, hz, mul_zero]

end OPICANativeResolventIndependent

#print axioms Zeta23.OPICAFollowup.native_forced_resolvent_unique
#print axioms Zeta23.OPICAFollowup.native_sample_stieltjes_identity
#print axioms Zeta23.OPICAFollowup.native_profile_spectral_norms
#print axioms OPICANativeResolventIndependent.audit_nativeLogResolvent
#print axioms OPICANativeResolventIndependent.expected_native_forced_resolvent_unique
#print axioms OPICANativeResolventIndependent.expected_native_sample_stieltjes_identity
#print axioms OPICANativeResolventIndependent.expected_native_profile_spectral_norms
#print axioms OPICANativeResolventIndependent.expected_offline_zero
#print axioms OPICANativeResolventIndependent.expected_sample_ratio
#print axioms OPICANativeResolventIndependent.expected_resolvent_weak_solution
#print axioms OPICANativeResolventIndependent.expected_diagonal_gram
#print axioms OPICANativeResolventIndependent.expected_conjugate_coincidence
#print axioms OPICANativeResolventIndependent.expected_critical_line_undivided
