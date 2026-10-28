import Zeta23.OPICARound3.CofinalSimultaneousNegative
import Zeta23.OPICARound3.Validation.NeutralParityCover

noncomputable section

namespace Zeta23.OPICARound3.Validation

open CCM

theorem cofinally_both_neutral_negative_of_off_line_zero_consumer
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ 0 < L ∧ ∃ K : ℕ, 3 ≤ K ∧
      Zeta23.OPICARound3.BothNeutralNegative L K := by
  exact Zeta23.OPICARound3.cofinally_both_neutral_negative_of_off_line_zero ρ hoff R

/-- Both nonzero physical witnesses use the same aperture, finite cutoff
and complete source matrix. This consumer retains both literal pole moments. -/
theorem simultaneous_physical_witnesses_consumer
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ 0 < L ∧ ∃ K : ℕ, 3 ≤ K ∧
      ∃ u v : EuclideanSpace ℂ (Fin (2 * K + 1)), u ≠ 0 ∧ v ≠ 0 ∧
        u ∈ euclideanEvenBoundaryFlatSubspace K ∧ v ∈ euclideanOddBoundaryFlatSubspace K ∧
        canonicalPoleExponentialMoment 1 L K ((EuclideanSpace.equiv _ ℂ) u) = 0 ∧
        canonicalPoleExponentialMoment (-1) L K ((EuclideanSpace.equiv _ ℂ) u) = 0 ∧
        canonicalPoleExponentialMoment 1 L K ((EuclideanSpace.equiv _ ℂ) v) = 0 ∧
        canonicalPoleExponentialMoment (-1) L K ((EuclideanSpace.equiv _ ℂ) v) = 0 ∧
        (quadraticForm (canonicalSourceMatrix L K) ((EuclideanSpace.equiv _ ℂ) u)).re < 0 ∧
        (quadraticForm (canonicalSourceMatrix L K) ((EuclideanSpace.equiv _ ℂ) v)).re < 0 := by
  obtain ⟨L, hRL, hL, K, hK, he, ho⟩ :=
    Zeta23.OPICARound3.cofinally_both_neutral_negative_of_off_line_zero ρ hoff R
  obtain ⟨u, hune, hulegal, hup, hum, huq⟩ := even_negative_physical_consumer hL K he
  obtain ⟨v, hvne, hvlegal, hvp, hvm, hvq⟩ := odd_negative_physical_consumer hL K ho
  exact ⟨L, hRL, hL, K, hK, u, v, hune, hvne, hulegal, hvlegal, hup, hum, hvp, hvm, huq, hvq⟩

end Zeta23.OPICARound3.Validation

#print axioms Zeta23.OPICARound3.Validation.cofinally_both_neutral_negative_of_off_line_zero_consumer
#print axioms Zeta23.OPICARound3.Validation.simultaneous_physical_witnesses_consumer
