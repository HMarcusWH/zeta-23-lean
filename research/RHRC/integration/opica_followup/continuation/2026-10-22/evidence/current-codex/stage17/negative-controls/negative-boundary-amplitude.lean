import Zeta23.OPICAFollowup.BoundaryAmplitude
open Set MeasureTheory Filter Complex
open scoped Topology Real SchwartzMap
open Zeta23.OPICAFollowup
-- (1) near zero the homogeneous power enters with a minus sign
theorem bad_near_zero_sign {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    ∀ x ∈ Ioo (0 : ℝ) 1, genericForcedProfile ρ x = 1 + boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1) :=
  (generic_boundary_amplitude h12 h1).2.2.1
-- (2) the plateau holds exactly when zeta(rho) = 0, not when zeta(rho) != 0
theorem bad_plateau_direction {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    (∀ x ∈ Ioo (0 : ℝ) 1, genericForcedProfile ρ x = 1) ↔ riemannZeta ρ ≠ 0 :=
  (generic_boundary_amplitude h12 h1).2.2.2.1
-- (3) the retained term at infinity is x^(-rho) with zeta(1 - rho), not x^(rho - 1) with zeta(rho)
theorem bad_tail_power {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖genericForcedProfile ρ x - (-(riemannZeta ρ / normalizationBrho ρ) * (x : ℂ) ^ (ρ - 1) +
        spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2))‖ ≤ C * x ^ (-3 : ℝ) :=
  (generic_boundary_amplitude h12 h1).2.2.2.2.2
-- (4) the log-form-domain theorem needs Re rho > 1/2 (x^(rho - 1) is not L2 near 0 otherwise)
theorem bad_domain_strip {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0) :
    LogFormDomain (genericForcedProfile ρ) (genericForcedProfileDeriv ρ) :=
  (generic_forced_profile_unique h0 h1 him).1
-- (5) uniqueness and the resolvent identification need Im rho != 0 (kappa off the cut)
theorem bad_no_im {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    logUnitary (genericForcedProfile ρ) = nativeLogResolvent (spectralKappa ρ) :=
  (generic_forced_profile_unique h12 h1).2.2.2.2.2.2.2.1
-- (6) the Fourier quotient has denominator a - kappa, not a + kappa
theorem bad_quotient {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0) (ξ : ℝ) :
    logFourier (logUnitary (genericForcedProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) + spectralKappa ρ) :=
  (generic_forced_profile_unique h12 h1 him).2.2.2.2.2.2.1 ξ
-- (7) the force equation carries the integer atoms (the comb), not only the continuum term
theorem bad_no_comb {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0) {φ : ℝ → ℂ}
    (hφ : PositiveAxisTest φ) :
    (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * genericForcedProfileDeriv ρ x * deriv φ x) =
      spectralKappa ρ * ∫ x in Ioi (0 : ℝ), (genericForcedProfile ρ x - 1) * φ x :=
  (generic_forced_profile_unique h12 h1 him).2.1 φ hφ
-- (8) the resolvent parameter is kappa, not its conjugate
theorem bad_conj_resolvent {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0) :
    logUnitary (genericForcedProfile ρ) = nativeLogResolvent (starRingEnd ℂ (spectralKappa ρ)) :=
  (generic_forced_profile_unique h12 h1 him).2.2.2.2.2.2.2.1
-- (9) the near-zero bound has exponent Re rho - 1, not Re rho (h is not bounded near 0)
theorem bad_near_zero_exponent {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0) :
    ∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖genericForcedProfile ρ x‖ ≤ (1 + ‖boundaryAmplitude ρ‖) * x ^ ρ.re :=
  (generic_forced_profile_unique h12 h1 him).2.2.2.2.2.2.2.2.1
