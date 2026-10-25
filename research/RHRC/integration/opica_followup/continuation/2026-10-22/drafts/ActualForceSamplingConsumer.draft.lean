import Zeta23.OPICAFollowup.BoundaryAmplitude

/- DRAFT, not a root claim and not compiled by any runner or workflow. Proposed body of the original
root `Zeta23.OPICAFollowup.actual_force_sampling_consumer` (F1-F3 composition). It compiles in this
standalone wrapper against the installed BoundaryAmplitude module (see drafts/README.md). To install,
move the `ForceSampling` section into Zeta23/OPICAFollowup/Consumers.lean, add
`import Zeta23.OPICAFollowup.BoundaryAmplitude` there (allowed by BUILD_MANIFEST), re-verify the
existing W01 word/jet consumer, then add an independent consumer, negative controls and a stage record. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff

namespace Zeta23.OPICAFollowup

section ForceSampling

/-- F1-F3 composed on an actual zero with nonreal κ (every off-line zero): the two Fourier
conventions, the actual lattice force on compact log tests and its transform, the log-unitary
profile with its weak forced equation and arithmetic quotient (in both conventions), the spectral
density, the sample identity b = κ M(κ), and the generic boundary amplitude at the right-half-strip
representative ρ' ∈ {ρ, 1 - ρ} (which has the same κ). The profile is forced: no constant multiple
of it is the Euler image, so this is not a homogeneous eigenproblem. -/
theorem actual_force_sampling_consumer {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
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
      eulerImage ρ φ = c * ∫ x in Ioi 0, zeroProfile ρ x * φ x) := by
  have hR : spectralKappa ρ ∈ spectralResolventSet := Or.inl hκ
  have him_k : (spectralKappa ρ).im = (1 - 2 * ρ.re) * ρ.im := by
    simp only [spectralKappa, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    ring
  have hre : ρ.re ≠ 1 / 2 := fun h => hκ (by rw [him_k, h]; ring)
  have him : ρ.im ≠ 0 := fun h => hκ (by rw [him_k, h, mul_zero])
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hz' : riemannZeta (1 - ρ) = 0 := by
    have hn : ∀ n : ℕ, ρ ≠ -n := fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [riemannZeta_one_sub hn hρ1, hz, mul_zero]
  obtain ⟨-, hW, -, hq, hEq⟩ := native_forced_resolvent_unique hz h0 h1 hR
  have hb := (native_sample_stieltjes_identity hz h0 h1 hR).2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, hnot, -⟩ := zero_profile_not_homogeneous_operator_vector ρ hz h0 h1
  obtain ⟨-, -, hw, hF⟩ := sawtooth_actual_mellin_fourier
  refine ⟨logFourier_eq_fourier, (sawtooth_integrable_force_identity).2.2.2.2.2.1, hF, hw, hW, hq,
    fun η => ?_, rfl, hb, ?_, hnot⟩
  · have h := hq (2 * π * η)
    rw [logFourier_eq_fourier, show 2 * π * η / (2 * π) = η by field_simp] at h
    exact h
  · -- the right-half-strip representative
    have hpick : ∃ ρ' : ℂ, (ρ' = ρ ∨ ρ' = 1 - ρ) ∧ 1 / 2 < ρ'.re ∧ ρ'.re < 1 ∧ riemannZeta ρ' = 0 ∧
        spectralKappa ρ' = spectralKappa ρ ∧ ρ'.im ≠ 0 := by
      rcases lt_or_gt_of_ne hre with hlt | hgt
      · refine ⟨1 - ρ, Or.inr rfl, by simp; linarith, by simp; linarith, hz', by
          simp only [spectralKappa]; ring, by simpa using him⟩
      · exact ⟨ρ, Or.inl rfl, hgt, h1, hz, rfl, him⟩
    obtain ⟨ρ', hρ', h12', h1', hz'', hk', him'⟩ := hpick
    have hBA := generic_boundary_amplitude h12' h1'
    have hgen := hBA.2.2.2.2.1 hz''
    have hA : boundaryAmplitude ρ' = 0 := by rw [boundaryAmplitude, hz'', zero_div]
    have hF3 := (generic_forced_profile_unique h12' h1' him').2.2.2.2.2.2.2.1
    refine ⟨ρ', hρ', h12', h1', hz'', hk', hA, hgen, ?_⟩
    rw [hF3, hk', hEq]

end ForceSampling

end Zeta23.OPICAFollowup
