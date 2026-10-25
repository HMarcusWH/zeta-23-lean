import Zeta23.OPICAFollowup.RenormalizedCoPoisson
open MeasureTheory Set Complex Filter
open scoped FourierTransform SchwartzMap Topology
open Zeta23.OPICAFollowup
-- (1) self-duality needs the zero equation ζ(ρ) = 0
theorem bad_no_zero (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    𝓕 ((zeroMeasure ρ).distributionOfLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1)) =
      (zeroMeasure ρ).distributionOfLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1) :=
  (zero_measure_exact_properties ρ h0 h1 hh).2.2.2.2.2.2.1
-- (2) the atom at 1 is -1, not +1
theorem bad_atom_sign (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hh : ρ ≠ 1 / 2) : (zeroMeasure ρ).rePart.positive {1} = 1 :=
  (zero_measure_exact_properties ρ hz h0 h1 hh).2.2.2.2.2.2.2.2.2.2.1.1
-- (3) b_ρ = 1/ρ - 1/(1-ρ), not 1/ρ + 1/(1-ρ)
theorem bad_normalizer (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hh : ρ ≠ 1 / 2) : normalizationBrho ρ = 1 / ρ + 1 / (1 - ρ) :=
  (zero_measure_exact_properties ρ hz h0 h1 hh).2.1
-- (4) the critical point ρ = 1/2 is excluded (b_ρ = 0 there)
theorem bad_half (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    normalizationBrho ρ ≠ 0 :=
  (zero_measure_exact_properties ρ hz h0 h1).2.2.1
-- (5) the exact gap is (-1, 1), not (-2, 2)
theorem bad_wide_gap (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hh : ρ ≠ 1 / 2) : (zeroMeasure ρ).variationControl (Ioo (-2) 2) = 0 :=
  (zero_measure_exact_properties ρ hz h0 h1 hh).2.2.2.2.2.2.2.2.1
-- (6) the construction subtracts b_ρ D_0; dropping it is not the same measure
theorem bad_no_comb_correction (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hh : ρ ≠ 1 / 2) (φ : 𝓢(ℝ, ℂ)) : (zeroMeasure ρ).integral φ =
      (coPoissonFamily (ρ - 1 / 2) φ - 1 / (1 - ρ) * (φ 0 + ∫ x, φ x)) / normalizationBrho ρ :=
  (zero_measure_exact_properties ρ hz h0 h1 hh).2.2.2.1 φ
