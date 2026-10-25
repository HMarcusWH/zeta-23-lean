import Zeta23.OPICAFollowup.NativeResolvent
open Set MeasureTheory Filter Complex
open scoped Topology Real SchwartzMap
open Zeta23.OPICAFollowup
-- (1) the log-Fourier quotient has denominator a - kappa, not a + kappa
theorem bad_quotient_sign {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : spectralKappa ρ ∈ spectralResolventSet) (ξ : ℝ) :
    logFourier (logUnitary (zeroProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) + spectralKappa ρ) :=
  (native_forced_resolvent_unique hz h0 h1 hκ).2.2.2.1 ξ
-- (2) the weak equation has 1/4 - kappa, not 1/4 + kappa
theorem bad_weak_sign {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : spectralKappa ρ ∈ spectralResolventSet) (φ : 𝓢(ℝ, ℂ)) :
    (∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv φ t) +
      (1 / 4 + spectralKappa ρ) * ∫ t, logUnitary (zeroProfile ρ) t * φ t =
        spectralKappa ρ * nativeLogForce φ :=
  (native_forced_resolvent_unique hz h0 h1 hκ).2.1 φ
-- (3) the identification needs kappa off the cut (no critical-line principal value is asserted)
theorem bad_no_resolvent_hypothesis {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    logUnitary (zeroProfile ρ) = nativeLogResolvent (spectralKappa ρ) :=
  (native_forced_resolvent_unique hz h0 h1).2.2.2.2
-- (4) the sample is kappa M(kappa), not M(kappa)
theorem bad_sample_no_kappa {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    profileSampleDefect ρ = arithmeticStieltjes (spectralKappa ρ) :=
  (native_sample_stieltjes_identity hz h0 h1 hκ).2.2.2.2.2.2.2.2
-- (5) the sample is + kappa M(kappa), not - kappa M(kappa)
theorem bad_sample_sign {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    profileSampleDefect ρ = -(spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ)) :=
  (native_sample_stieltjes_identity hz h0 h1 hκ).2.2.2.2.2.2.2.2
-- (6) the cell endpoint term is h(n + 1), not h(n)
theorem bad_cell_endpoint {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : spectralKappa ρ ∈ spectralResolventSet) (n : ℕ) :
    ∫ x in (n : ℝ)..(n + 1), ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x =
      zeroProfile ρ (n : ℝ) - ∫ x in (n : ℝ)..(n + 1), zeroProfile ρ x :=
  (native_sample_stieltjes_identity hz h0 h1 hκ).2.1 n
-- (7) the Fourier pairing carries the conjugate of the weight transform
theorem bad_pairing_no_conj {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    profileSampleDefect ρ = 1 / (2 * π) * ∫ ξ : ℝ, logFourier sawtoothWeight ξ *
      (((ξ : ℂ) * I - 1 / 2) * logFourier (logUnitary (zeroProfile ρ)) ξ) :=
  (native_sample_stieltjes_identity hz h0 h1 hκ).2.2.2.2.2.2.2.1
-- (8) the norm carries the factor |kappa|^2
theorem bad_norm_factor {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : (spectralKappa ρ).im ≠ 0) :
    ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 =
      ∫ ξ, (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure :=
  (native_profile_spectral_norms hz h0 h1 hκ).1
-- (9) the Euler form carries the weight a(xi)
theorem bad_form_weight {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : (spectralKappa ρ).im ≠ 0) :
    logForm (zeroProfileDeriv ρ) = ‖spectralKappa ρ‖ ^ 2 *
      ∫ ξ, (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure :=
  (native_profile_spectral_norms hz h0 h1 hκ).2.1
-- (10) the mixed pairing has conj kappa_sigma, not kappa_sigma
theorem bad_mixed_no_conj {ρ σ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : (spectralKappa ρ).im ≠ 0) (hzσ : riemannZeta σ = 0) (h0σ : 0 < σ.re) (h1σ : σ.re < 1)
    (hκσ : spectralKappa σ ∈ spectralResolventSet) :
    profileGram ρ σ = spectralKappa ρ * spectralKappa σ *
      ∫ ξ, (((spectralEnergy ξ : ℂ) - spectralKappa ρ) *
        ((spectralEnergy ξ : ℂ) - spectralKappa σ))⁻¹ ∂arithmeticSpectralMeasure :=
  ((native_profile_spectral_norms hz h0 h1 hκ).2.2.2.1 σ hzσ h0σ h1σ hκσ).1
-- (11) the (F2.5) budget carries the factor 1 + |kappa|/|Im kappa|
theorem bad_budget_factor {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : (spectralKappa ρ).im ≠ 0) :
    ‖profileSampleDefect ρ‖ ≤ ‖spectralKappa ρ‖ * (‖spectralKappa ρ‖ / |(spectralKappa ρ).im|) *
      (Real.log (2 * π) - Real.eulerMascheroniConstant) :=
  (native_profile_spectral_norms hz h0 h1 hκ).2.2.2.2
