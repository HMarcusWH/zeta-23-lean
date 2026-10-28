import Zeta23.OPICARound3.NeutralParityCover

noncomputable section

namespace Zeta23.OPICARound3.Validation

open CCM

theorem neutral_parity_cover_of_off_line_zero_consumer
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ∃ L₀ : ℝ, 0 < L₀ ∧ ∀ L : ℝ, L₀ < L →
      ∃ K : ℕ, 3 ≤ K ∧
        (Zeta23.OPICARound3.EvenNeutralNegative L K ∨
          Zeta23.OPICARound3.OddNeutralNegative L K) := by
  exact Zeta23.OPICARound3.neutral_parity_cover_of_off_line_zero ρ hoff

/-- Independent physical consumer: the native predicate really supplies
both original exponential moments, legal parity and negative whole form. -/
theorem even_negative_physical_consumer {L : ℝ} (hL : 0 < L) (K : ℕ)
    (h : Zeta23.OPICARound3.EvenNeutralNegative L K) :
    ∃ u : EuclideanSpace ℂ (Fin (2 * K + 1)), u ≠ 0 ∧
      u ∈ euclideanEvenBoundaryFlatSubspace K ∧
      canonicalPoleExponentialMoment 1 L K ((EuclideanSpace.equiv _ ℂ) u) = 0 ∧
      canonicalPoleExponentialMoment (-1) L K ((EuclideanSpace.equiv _ ℂ) u) = 0 ∧
      (quadraticForm (canonicalSourceMatrix L K) ((EuclideanSpace.equiv _ ℂ) u)).re < 0 := by
  obtain ⟨u, hu, hp, hneg⟩ := (evenNeutralNegative_iff_ambient L K).mp h
  let v : euclideanEvenBoundaryFlatSubspace K := ⟨u, hu⟩
  have hv : v ∈ poleNeutralEvenSubspace L K := (mem_poleNeutralEvenSubspace L K v).mpr hp
  have hphysical := (poleNeutralEven_iff_exponentialMoments hL K v).mp hv
  refine ⟨u, negative_fullCanonicalEnergy_ne_zero hneg, hu, hphysical.1, hphysical.2, ?_⟩
  rw [quadraticForm_re_eq_re_inner_apply_self]
  exact hneg

theorem odd_negative_physical_consumer {L : ℝ} (hL : 0 < L) (K : ℕ)
    (h : Zeta23.OPICARound3.OddNeutralNegative L K) :
    ∃ u : EuclideanSpace ℂ (Fin (2 * K + 1)), u ≠ 0 ∧
      u ∈ euclideanOddBoundaryFlatSubspace K ∧
      canonicalPoleExponentialMoment 1 L K ((EuclideanSpace.equiv _ ℂ) u) = 0 ∧
      canonicalPoleExponentialMoment (-1) L K ((EuclideanSpace.equiv _ ℂ) u) = 0 ∧
      (quadraticForm (canonicalSourceMatrix L K) ((EuclideanSpace.equiv _ ℂ) u)).re < 0 := by
  obtain ⟨u, hu, hp, hneg⟩ := (oddNeutralNegative_iff_ambient L K).mp h
  let v : euclideanOddBoundaryFlatSubspace K := ⟨u, hu⟩
  have hv : v ∈ poleNeutralOddSubspace L K := (mem_poleNeutralOddSubspace L K v).mpr hp
  have hphysical := (poleNeutralOdd_iff_exponentialMoments hL K v).mp hv
  refine ⟨u, negative_fullCanonicalEnergy_ne_zero hneg, hu, hphysical.1, hphysical.2, ?_⟩
  rw [quadraticForm_re_eq_re_inner_apply_self]
  exact hneg

end Zeta23.OPICARound3.Validation

#print axioms Zeta23.OPICARound3.Validation.neutral_parity_cover_of_off_line_zero_consumer
#print axioms Zeta23.OPICARound3.Validation.even_negative_physical_consumer
#print axioms Zeta23.OPICARound3.Validation.odd_negative_physical_consumer
