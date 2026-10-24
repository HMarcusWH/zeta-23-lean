import Zeta23.OPICAFollowup.ConfluentProfiles

noncomputable section
open Complex Finset
open Zeta23.OPICAFollowup
/-! Deliberate negative consumer: it drops the affine-basis determinant sign. -/
example {r : ℕ} (κ : Fin r → ℂ) (hκ : Function.Injective κ)
    (hκ0 : ∀ j, κ j ≠ 0) (m : Fin r → ℕ) :
    (profileJetMatrix κ m).det =
      (∏ j, κ j ^ m j) * ∏ j, ∏ i ∈ Iio j, (κ j - κ i) ^ (m i * m j) := by
  exact profile_jet_confluent_determinant κ hκ hκ0 m
