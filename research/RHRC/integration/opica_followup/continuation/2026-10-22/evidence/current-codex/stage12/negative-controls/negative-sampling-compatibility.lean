import Zeta23.OPICAFollowup.SamplingCompatibility
open Set MeasureTheory Filter Complex
open scoped Topology ComplexConjugate ComplexOrder
open Zeta23.OPICAFollowup
-- (1) the sample enters conjugated: Q_ij = kappa_i (N_ij + conj b_j), not kappa_i (N_ij + b_j)
theorem bad_unconjugated_sample {ι : Type*} (ρ : ι → ℂ) (hz : ∀ i, riemannZeta (ρ i) = 0)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) (i j : ι) :
    profileFormGram (ρ i) (ρ j) = spectralKappa (ρ i) * (profileGram (ρ i) (ρ j) + profileSampleDefect (ρ j)) :=
  (native_sampling_gram_identity ρ hz h0 h1).2.2.2.2.2.2.1 i j
-- (2) the second form carries conj kappa_j, not kappa_j
theorem bad_unconjugated_kappa {ι : Type*} (ρ : ι → ℂ) (hz : ∀ i, riemannZeta (ρ i) = 0)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) (i j : ι) :
    profileFormGram (ρ i) (ρ j) = spectralKappa (ρ j) * (profileGram (ρ i) (ρ j) + profileSampleDefect (ρ i)) :=
  (native_sampling_gram_identity ρ hz h0 h1).2.2.2.2.2.2.2 i j
-- (3) the continuum term removes 1/2: b = S - 1/2, not S
theorem bad_no_half {ι : Type*} (ρ : ι → ℂ) (hz : ∀ i, riemannZeta (ρ i) = 0)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) (i j : ι) :
    profileFormGram (ρ i) (ρ j) = spectralKappa (ρ i) * (profileGram (ρ i) (ρ j) + conj (profileSample (ρ j))) :=
  (native_sampling_gram_identity ρ hz h0 h1).2.2.2.2.2.2.1 i j
-- (4) the half-line integral of each profile is 1/2, not 1
theorem bad_half_line_integral {ι : Type*} (ρ : ι → ℂ) (hz : ∀ i, riemannZeta (ρ i) = 0)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) (i : ι) :
    ∫ x in Ioi (0 : ℝ), zeroProfile (ρ i) x = 1 :=
  (native_sampling_gram_identity ρ hz h0 h1).2.2.2.1 i
-- (5) the outer boundary term tends to 0, not to kappa
theorem bad_boundary_limit {ι : Type*} (ρ : ι → ℂ) (hz : ∀ i, riemannZeta (ρ i) = 0)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) (i j : ι) :
    Tendsto (fun N : ℕ => (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 *
      -(srhoCellDeriv (ρ i) N ((N : ℝ) + 1) / normalizationBrho (ρ i)) *
        conj (zeroProfile (ρ j) ((N : ℝ) + 1))) atTop (𝓝 (spectralKappa (ρ i))) :=
  (native_sampling_gram_identity ρ hz h0 h1).2.2.2.2.2.1 i j
-- (6) the form bound is Q - N/4, not Q - N/2
theorem bad_form_constant {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (hz : ∀ i, riemannZeta (ρ i) = 0)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) :
    (Matrix.of fun i j => profileFormGram (ρ i) (ρ j) - profileGram (ρ i) (ρ j) / 2).PosSemidef :=
  (native_sampling_form_positive ρ hz h0 h1).2.2.1
-- (7) the divided identity needs a nonzero denominator
theorem bad_divided_no_hypothesis {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (hz : ∀ i, riemannZeta (ρ i) = 0)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) (i j : ι) :
    profileGram (ρ i) (ρ j) / (spectralKappa (ρ i) * conj (spectralKappa (ρ j))) =
      (profileSampleDefect (ρ i) / spectralKappa (ρ i) -
        conj (profileSampleDefect (ρ j) / spectralKappa (ρ j))) /
          (spectralKappa (ρ i) - conj (spectralKappa (ρ j))) :=
  (native_sampling_form_positive ρ hz h0 h1).2.2.2.2.1 i j
-- (8) Im M / Im kappa = +N/|kappa|^2, not -N/|kappa|^2
theorem bad_sign_s24 {ι : Type*} [Fintype ι] (ρ : ι → ℂ) (hz : ∀ i, riemannZeta (ρ i) = 0)
    (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) (i : ι) (hi : (spectralKappa (ρ i)).im ≠ 0) :
    (profileSampleDefect (ρ i) / spectralKappa (ρ i)).im / (spectralKappa (ρ i)).im =
      -(∫ x in Ioi (0 : ℝ), ‖zeroProfile (ρ i) x‖ ^ 2) / ‖spectralKappa (ρ i)‖ ^ 2 :=
  ((native_sampling_form_positive ρ hz h0 h1).2.2.2.2.2 i hi).1
-- (9) the actual zero hypothesis is required
theorem bad_no_zero {ι : Type*} (ρ : ι → ℂ) (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) (i j : ι) :
    profileFormGram (ρ i) (ρ j) = spectralKappa (ρ i) * (profileGram (ρ i) (ρ j) + conj (profileSampleDefect (ρ j))) :=
  (native_sampling_gram_identity ρ h0 h1).2.2.2.2.2.2.1 i j
-- (10) the finite countercontrol needs nonreal parameters (A - kappa I invertible)
theorem bad_control_real_parameters {ι m : Type*} [Fintype ι] [Fintype m] (a g : m → ℝ)
    (ha : ∀ k, 0 < a k) (κ : ι → ℂ) (i j : ι) :
    ∑ k, (a k : ℂ) * controlVector a g (κ i) k * conj (controlVector a g (κ j) k) =
      κ i * (∑ k, controlVector a g (κ i) k * conj (controlVector a g (κ j) k) +
        conj (∑ k, (g k : ℂ) * controlVector a g (κ j) k)) :=
  (finite_countercontrol a g ha κ).2.2.1 i j
