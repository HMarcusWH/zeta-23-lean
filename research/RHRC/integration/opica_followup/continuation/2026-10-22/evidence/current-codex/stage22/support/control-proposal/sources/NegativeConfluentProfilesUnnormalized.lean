import Zeta23.OPICAFollowup.ConfluentProfiles

noncomputable section
open Complex Finset
open Zeta23.OPICAFollowup
/-! Deliberate negative consumer: raw parameter derivatives are substituted
for the normalized 1/k! jet columns while retaining the claimed determinant. -/
example {r : ℕ} (κ : Fin r → ℂ) (hκ : Function.Injective κ)
    (hκ0 : ∀ j, κ j ≠ 0) (m : Fin r → ℕ) :
    (Matrix.of (fun n i : Fin (∑ j, m j) =>
      iteratedDeriv (((Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm i).2 : ℕ)
        (fun w : ℂ => w * (1 / 4 - w) ^ (n : ℕ))
        (κ ((Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm i).1))).det =
      (-1 : ℂ) ^ ((∑ j, m j) * ((∑ j, m j) - 1) / 2) *
        (∏ j, κ j ^ m j) * ∏ j, ∏ i ∈ Iio j, (κ j - κ i) ^ (m i * m j) := by
  exact profile_jet_confluent_determinant κ hκ hκ0 m
