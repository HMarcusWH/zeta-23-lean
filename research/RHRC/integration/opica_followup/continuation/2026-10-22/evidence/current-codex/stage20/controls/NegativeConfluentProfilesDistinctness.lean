import Zeta23.OPICAFollowup.ConfluentProfiles

noncomputable section
open Complex
open scoped SchwartzMap FourierTransform
open Zeta23.OPICAFollowup
/-! Deliberate negative consumer: it omits the required reflection quotient. -/
example {r : ℕ} (ρ : Fin r → ℂ) (hz : ∀ j, riemannZeta (ρ j) = 0)
    (h0 : ∀ j, 0 < (ρ j).re) (h1 : ∀ j, (ρ j).re < 1) :
    LinearIndependent ℂ (fun p : (j : Fin r) × Fin (zeroJetOrder (ρ j)) =>
      (normalizedZeroMeasureJet (ρ p.1) (p.2 : ℕ)).distributionOfLinearGrowth
        (normalizedZeroMeasureJet_hasLinearGrowth (h0 p.1) (h1 p.1)
          (zero_ne_half (hz p.1)) p.2.isLt)) := by
  exact finite_zero_jet_independent ρ hz h0 h1

