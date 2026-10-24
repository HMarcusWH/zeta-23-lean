import Zeta23.OPICAFollowup.Consumers

/- Independent full-type and physical-definition consumer for the original F1-F3 root.
All hypotheses concern the actual zeta function and the full strip. No off-line zero
is asserted to exist. Definition audits prevent synthetic source/measure substitution.
The original word/jet consumer is separately replayed by ExpectedWordJet. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff
open Zeta23.OPICAFollowup
namespace OPICAForceSamplingIndependent

theorem audit_spectralKappa (ρ : ℂ) : spectralKappa ρ = ρ * (1 - ρ) := rfl

theorem audit_logFourier (f : ℝ → ℂ) (ξ : ℝ) :
    logFourier f ξ = ∫ t, cexp (-((ξ * t : ℝ) : ℂ) * I) * f t := rfl

theorem audit_force : nativeLogForce =
    -(TemperedDistribution.derivCLM ℂ sawtoothWeightTD) - (1 / 2 : ℂ) • sawtoothWeightTD := rfl

theorem audit_density : arithmeticSpectralMeasure =
    volume.withDensity (fun ξ : ℝ => ENNReal.ofReal
      (‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (2 * π))) := rfl

theorem audit_sample (ρ : ℂ) :
    profileSampleDefect ρ = (∑' n : ℕ, zeroProfile ρ (n + 1)) - 1 / 2 := rfl

theorem audit_boundary (ρ : ℂ) :
    boundaryAmplitude ρ = riemannZeta ρ / normalizationBrho ρ := rfl

theorem audit_generic (ρ : ℂ) (x : ℝ) :
    genericForcedProfile ρ x =
      (1 - finiteSumSrho ρ |x| / normalizationBrho ρ) -
        riemannZeta ρ / normalizationBrho ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) := rfl

theorem expected_actual_force_sampling_consumer {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : (spectralKappa ρ).im ≠ 0) :
    (∀ (f : ℝ → ℂ) (ξ : ℝ), logFourier f ξ = 𝓕 f (ξ / (2 * π))) ∧
    (∀ (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      nativeLogForce (hc.toSchwartzMap hφ) =
        ∑' n : ℕ, ((((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * φ (Real.log (n + 1)) -
          ∫ t, (Real.exp (t / 2) : ℂ) * φ t) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (𝓕 nativeLogForce) φ = ∫ η : ℝ, riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) * φ η) ∧
    (∀ ξ : ℝ, -(1 / 2 + ξ * I) * logFourier sawtoothWeight ξ = riemannZeta (1 / 2 + ξ * I)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv φ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (zeroProfile ρ) t * φ t =
        spectralKappa ρ * nativeLogForce φ) ∧
    (∀ ξ : ℝ, logFourier (logUnitary (zeroProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ)) ∧
    (∀ η : ℝ, 𝓕 (logUnitary (zeroProfile ρ)) η =
      spectralKappa ρ * riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) /
        ((spectralEnergy (2 * π * η) : ℂ) - spectralKappa ρ)) ∧
    arithmeticSpectralMeasure =
      volume.withDensity (fun ξ : ℝ => ENNReal.ofReal (‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (2 * π))) ∧
    profileSampleDefect ρ = spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ) ∧
    (∃ ρ' : ℂ, (ρ' = ρ ∨ ρ' = 1 - ρ) ∧ 1 / 2 < ρ'.re ∧ ρ'.re < 1 ∧ riemannZeta ρ' = 0 ∧
      spectralKappa ρ' = spectralKappa ρ ∧ boundaryAmplitude ρ' = 0 ∧
      genericForcedProfile ρ' = zeroProfile ρ' ∧
      logUnitary (genericForcedProfile ρ') = logUnitary (zeroProfile ρ)) ∧
    (∀ c : ℂ, ¬ ∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = c * ∫ x in Ioi 0, zeroProfile ρ x * φ x) :=
  actual_force_sampling_consumer hz h0 h1 hκ

/-- Every hypothetical off-line strip zero lies in the actual theorem domain. -/
theorem offline_kappa {ρ : ℂ} (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    (spectralKappa ρ).im ≠ 0 := by
  have h : (spectralKappa ρ).im = (1 - 2 * ρ.re) * ρ.im := by
    simp only [spectralKappa, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  rw [h]
  exact mul_ne_zero (by intro he; apply hre; linarith) him

/-- The sample identity and the actual nonhomogeneous Euler obstruction coexist.
This exercises the full root at an actual source with no extra spectral packet. -/
theorem actual_offline_domain {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    profileSampleDefect ρ = spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ) ∧
    (∀ c : ℂ, ¬ ∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = c * ∫ x in Ioi 0, zeroProfile ρ x * φ x) := by
  obtain ⟨_, _, _, _, _, _, _, _, hs, _, hn⟩ :=
    expected_actual_force_sampling_consumer hz h0 h1 (offline_kappa hre him)
  exact ⟨hs, hn⟩

/-- Both sides of the critical line choose the same κ node, with the actual
right-half-strip representative and zero boundary amplitude. -/
theorem actual_right_representative {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    ∃ σ : ℂ, (σ = ρ ∨ σ = 1 - ρ) ∧ 1 / 2 < σ.re ∧ σ.re < 1 ∧
      riemannZeta σ = 0 ∧ spectralKappa σ = spectralKappa ρ ∧ boundaryAmplitude σ = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨σ, ha, hb, hc, hd, he, hf, _, _⟩, _⟩ :=
    expected_actual_force_sampling_consumer hz h0 h1 (offline_kappa hre him)
  exact ⟨σ, ha, hb, hc, hd, he, hf⟩

end OPICAForceSamplingIndependent

#print axioms Zeta23.OPICAFollowup.actual_force_sampling_consumer
#print axioms OPICAForceSamplingIndependent.expected_actual_force_sampling_consumer
#print axioms OPICAForceSamplingIndependent.audit_spectralKappa
#print axioms OPICAForceSamplingIndependent.audit_logFourier
#print axioms OPICAForceSamplingIndependent.audit_force
#print axioms OPICAForceSamplingIndependent.audit_density
#print axioms OPICAForceSamplingIndependent.audit_sample
#print axioms OPICAForceSamplingIndependent.audit_boundary
#print axioms OPICAForceSamplingIndependent.audit_generic
#print axioms OPICAForceSamplingIndependent.offline_kappa
#print axioms OPICAForceSamplingIndependent.actual_offline_domain
#print axioms OPICAForceSamplingIndependent.actual_right_representative
