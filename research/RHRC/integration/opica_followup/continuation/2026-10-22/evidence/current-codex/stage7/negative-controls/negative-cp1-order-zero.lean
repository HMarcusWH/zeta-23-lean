import Zeta23.OPICAFollowup.RenormalizedCoPoisson
open MeasureTheory Set Complex Filter
open scoped FourierTransform SchwartzMap Topology
open Zeta23.OPICAFollowup
-- (1) the limit origin atom is 1/ρ, not 1/(1-ρ)
theorem bad_origin_coefficient (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (K : Set ℝ)
    (hK : IsCompact K) (E : Set ℝ) (hE : MeasurableSet E) :
    (coPoissonLimitMeasure ρ h0).compactRestriction K hK E =
      (∫ x in E ∩ K, (finiteSumSrho ρ |x| + riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) +
        1 / (1 - ρ))) + (E ∩ K).indicator (fun _ => 1 / (1 - ρ)) 0 :=
  (renormalized_copoisson_order_zero ρ h0 h1).2.2.2.1 K hK E hE
-- (2) the ζ(ρ)|x|^(ρ-1) term cannot be dropped from the limit density
theorem bad_missing_zeta_term (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonFamily (ρ - 1 / 2) φ =
      (∫ x, (finiteSumSrho ρ |x| + 1 / (1 - ρ)) * φ x) + 1 / ρ * φ 0 :=
  (renormalized_copoisson_order_zero ρ h0 h1).2.2.2.2.2.2.2 φ
-- (3) the domain is not widened to Re ρ ≤ 1
theorem bad_closed_strip (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re ≤ 1) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonFamily (ρ - 1 / 2) φ = (coPoissonLimitMeasure ρ h0).integral φ :=
  (renormalized_copoisson_order_zero ρ h0 h1).2.2.2.2.2.2.1 φ
-- (4) the cutoff origin atom is (1 - e^(-ρT))/ρ, not (1 + e^(-ρT))/ρ
theorem bad_cutoff_atom (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (T : ℝ) (hT : 0 ≤ T)
    (φ : 𝓢(ℝ, ℂ)) : (coPoissonCutoff ρ T).integral φ =
      (∫ x, coPoissonCutoffDensity ρ T x * φ x) + (1 + cexp (-ρ * T)) / ρ * φ 0 :=
  (renormalized_copoisson_order_zero ρ h0 h1).2.1 T hT φ
-- (5) the cutoff is the actual K_t cutoff, not the cutoff of A_t alone
theorem bad_synthetic_cutoff (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (T : ℝ) (hT : 0 ≤ T)
    (φ : 𝓢(ℝ, ℂ)) : (coPoissonCutoff ρ T).integral φ =
      ∫ t in (0 : ℝ)..T, cexp (-(ρ - 1 / 2) * t) * coPoissonA t φ :=
  (renormalized_copoisson_order_zero ρ h0 h1).1 T hT φ
-- (6) the parameter is λ = ρ - 1/2, not λ = ρ
theorem bad_parameter (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonFamily ρ φ = (coPoissonLimitMeasure ρ h0).integral φ :=
  (renormalized_copoisson_order_zero ρ h0 h1).2.2.2.2.2.2.1 φ
