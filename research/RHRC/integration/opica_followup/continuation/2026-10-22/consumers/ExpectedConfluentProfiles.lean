import Zeta23.OPICAFollowup.ConfluentProfiles

noncomputable section
open Set MeasureTheory Filter Complex Finset
open scoped Topology SchwartzMap FourierTransform
namespace OPICAConfluentProfilesIndependent
open Zeta23.OPICAFollowup

/-- Independent full determinant type: the matrix entries and both exact
grouped products are written explicitly. -/
theorem expected_profile_jet_confluent_determinant {r : ℕ} (κ : Fin r → ℂ)
    (hκ : Function.Injective κ) (hκ0 : ∀ j, κ j ≠ 0) (m : Fin r → ℕ) :
    (Matrix.of (fun n i : Fin (∑ j, m j) =>
      iteratedDeriv (((Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm i).2 : ℕ)
        (fun w : ℂ => w * (1 / 4 - w) ^ (n : ℕ))
        (κ ((Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm i).1) /
          ((((Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm i).2 : ℕ).factorial : ℂ))).det =
      (-1 : ℂ) ^ ((∑ j, m j) * ((∑ j, m j) - 1) / 2) *
        (∏ j, κ j ^ m j) * ∏ j, ∏ i ∈ Iio j, (κ j - κ i) ^ (m i * m j) := by
  exact profile_jet_confluent_determinant κ hκ hκ0 m

/-- Independent full physical type, retaining every actual zero hypothesis,
the reflection quotient, and exactly the available multiplicity jets. -/
theorem expected_finite_zero_jet_independent {r : ℕ} (ρ : Fin r → ℂ)
    (hz : ∀ j, riemannZeta (ρ j) = 0)
    (h0 : ∀ j, 0 < (ρ j).re) (h1 : ∀ j, (ρ j).re < 1)
    (hdist : Function.Injective (fun j => (ρ j) * (1 - ρ j))) :
    LinearIndependent ℂ (fun p : (j : Fin r) × Fin (zeroJetOrder (ρ j)) =>
      (normalizedZeroMeasureJet (ρ p.1) (p.2 : ℕ)).distributionOfLinearGrowth
        (normalizedZeroMeasureJet_hasLinearGrowth (h0 p.1) (h1 p.1)
          (zero_ne_half (hz p.1)) p.2.isLt)) := by
  exact finite_zero_jet_independent ρ hz h0 h1 hdist

theorem expected_exact_local_column {r : ℕ} (κ : Fin r → ℂ) (m : Fin r → ℕ)
    (n : Fin (∑ j, m j)) (j : Fin r) (k : Fin (m j)) :
    profileJetMatrix κ m n (Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupIndex m ⟨j, k⟩) =
      iteratedDeriv (k : ℕ) (fun w : ℂ => w * (1 / 4 - w) ^ (n : ℕ)) (κ j) /
        ((k : ℕ).factorial : ℂ) := by
  have he : (Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm
      (Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupIndex m ⟨j, k⟩) = ⟨j, k⟩ :=
    (Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm_apply_apply ⟨j, k⟩
  have hkcol := congrArg (fun p : (j : Fin r) × Fin (m j) => (p.2 : ℕ)) he
  have hjcol := congrArg (fun p : (j : Fin r) × Fin (m j) => p.1) he
  unfold profileJetMatrix
  rw [hkcol, hjcol]

#print axioms OPICAConfluentProfilesIndependent.expected_profile_jet_confluent_determinant
#print axioms OPICAConfluentProfilesIndependent.expected_finite_zero_jet_independent
#print axioms OPICAConfluentProfilesIndependent.expected_exact_local_column
end OPICAConfluentProfilesIndependent



