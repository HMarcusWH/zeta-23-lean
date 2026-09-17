import Zeta23.CCM.ParitySourceMomentFourCoercivity
import Zeta23.CCM.RegularFirstBadParitySourceMomentRigidity

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained quantitative Pair-D coercivity

This module specializes the generic quantitative Pair-D theorem to the exact
retained even shifted first-bad trial.

On the even-selected + odd-good branch the same retained canonical state now
carries:

* quantitative sourceMoment/M4 coercivity;
* quantitative sourceMoment/seventh-jet orientation;
* strict global-source/local-jet anti-alignment;
* an active, nondegenerate Riesz-8/Riesz-9 boundary whenever the arithmetic
  endpoint scalar is nonzero.

The simultaneous odd-bad branch remains open. The odd-selected first-bad
branch remains open. No endpoint-scalar sign, negative-root exclusion,
finite-to-infinite closure, or RH theorem is asserted.
-/

/-- Retained quantitative sourceMoment/M4 coercivity.

The exact canonical coupling must compensate for at least the transported
negative eigenenergy on the centered-index odd image. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceMomentMomentFour_coercive_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    -c.lam *
        ‖euclideanEvenToOddIndexLinearMap
          (c.firstBad.Nstar + 1) c.evenShiftedTrial‖ ^ 2 ≤
      Complex.re
        (star
            (explicitCanonicalSourceMoment
              c.firstBad.L (c.firstBad.Nstar + 1)
              c.evenShiftedTrial) *
          centeredMoment (c.firstBad.Nstar + 1) 4
            (evenBoundaryFlatRawCoefficients
              (c.firstBad.Nstar + 1) c.evenShiftedTrial)) := by
  have hveig :=
    (c.evenShiftedTrial_eigenmode_of_even hp).2
  exact
    neg_lam_mul_evenToOdd_norm_sq_le_re_star_explicitCanonicalSourceMoment_mul_momentFour_of_even_eigenmode_of_not_oddBad
      c.firstBad.L_pos
      (c.firstBad.Nstar + 1)
      (Nat.succ_le_succ c.firstBad.one_le_Nstar)
      hveig hodd

/-- Retained quantitative sourceMoment/seventh-jet upper bound. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceMomentMixedJet_re_le_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    Complex.re
        (star
            (explicitCanonicalSourceMoment
              c.firstBad.L (c.firstBad.Nstar + 1)
              c.evenShiftedTrial) *
          iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0) ≤
      2 * (2 * Real.pi) ^ 6 * c.lam *
        ‖euclideanEvenToOddIndexLinearMap
          (c.firstBad.Nstar + 1) c.evenShiftedTrial‖ ^ 2 := by
  have hveig :=
    (c.evenShiftedTrial_eigenmode_of_even hp).2
  change
    Complex.re
        (star
            (explicitCanonicalSourceMoment
              c.firstBad.L (c.firstBad.Nstar + 1)
              c.evenShiftedTrial) *
          iteratedDeriv 7
            (quadraticNormalSourceAtom
              (c.firstBad.Nstar + 1) c.evenShiftedTrial) 0) ≤
      2 * (2 * Real.pi) ^ 6 * c.lam *
        ‖euclideanEvenToOddIndexLinearMap
          (c.firstBad.Nstar + 1) c.evenShiftedTrial‖ ^ 2
  exact
    re_star_explicitCanonicalSourceMoment_mul_seventhJet_le_two_pi_six_mul_lam_norm_sq_of_even_eigenmode_of_not_oddBad
      c.firstBad.L_pos
      (c.firstBad.Nstar + 1)
      (Nat.succ_le_succ c.firstBad.one_le_Nstar)
      hveig hodd

/-- Headline retained anti-alignment theorem.

On the retained even-selected odd-good branch, the complete canonical source
functional and the local seventh mixed source jet of the same source observable
have strictly negative Hermitian pairing. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceMomentMixedJet_re_neg_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    Complex.re
        (star
            (explicitCanonicalSourceMoment
              c.firstBad.L (c.firstBad.Nstar + 1)
              c.evenShiftedTrial) *
          iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0) < 0 := by
  obtain ⟨hvne, hveig⟩ :=
    c.evenShiftedTrial_eigenmode_of_even hp
  change
    Complex.re
        (star
            (explicitCanonicalSourceMoment
              c.firstBad.L (c.firstBad.Nstar + 1)
              c.evenShiftedTrial) *
          iteratedDeriv 7
            (quadraticNormalSourceAtom
              (c.firstBad.Nstar + 1) c.evenShiftedTrial) 0) < 0
  exact
    re_star_explicitCanonicalSourceMoment_mul_seventhJet_neg_of_even_negative_eigenmode_of_not_oddBad
      c.firstBad.L_pos
      (c.firstBad.Nstar + 1)
      (Nat.succ_le_succ c.firstBad.one_le_Nstar)
      c.lam_neg hvne hveig hodd

/-- Pair-D fork in the global-source/local-jet formulation.

Either the odd successor is itself bad, or the exact same retained source
observable has strictly negative sourceMoment/seventh-jet orientation. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.oddBad_or_sourceMomentMixedJet_re_neg_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1) ∨
      Complex.re
        (star
            (explicitCanonicalSourceMoment
              c.firstBad.L (c.firstBad.Nstar + 1)
              c.evenShiftedTrial) *
          iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0) < 0 := by
  by_cases hodd :
      ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)
  · exact Or.inl hodd
  · exact Or.inr
      (c.evenShiftedSourceMomentMixedJet_re_neg_of_even_of_not_oddBad
        hp hodd)

/-- On the retained even-selected odd-good branch the #163 Riesz boundary can
vanish only when the arithmetic endpoint scalar itself vanishes.

The mixed seventh jet is already known to be nonzero on this branch, so the
jet factor can no longer absorb the boundary. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEight_eq_nine_iff_endpointScalar_eq_zero_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    canonicalRieszSourceChannelEnergy
        c.firstBad.L 8 (c.firstBad.Nstar + 1)
        (c.evenShiftedTrial :
          EuclideanSpace ℂ
            (Fin (2 * (c.firstBad.Nstar + 1) + 1))) =
      canonicalRieszSourceChannelEnergy
        c.firstBad.L 9 (c.firstBad.Nstar + 1)
        (c.evenShiftedTrial :
          EuclideanSpace ℂ
            (Fin (2 * (c.firstBad.Nstar + 1) + 1))) ↔
      canonicalPolePrimeRieszEndpointScalar c.firstBad.L 8 = 0 := by
  let J : ℂ :=
    iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0
  have hJne : J ≠ 0 := by
    simpa [J] using
      c.evenShiftedMixedSourceSeventhJet_ne_zero_of_even_of_not_oddBad
        hp hodd
  have hnormSqNe : Complex.normSq J ≠ 0 := by
    intro hzero
    apply hJne
    exact Complex.normSq_eq_zero.mp hzero
  have hid :=
    c.evenShiftedRieszEightNine_eq_mixedJetBoundary
  change
    2 * (2 * Real.pi) ^ 4 *
        (canonicalRieszSourceChannelEnergy
            c.firstBad.L 8 (c.firstBad.Nstar + 1)
            (c.evenShiftedTrial :
              EuclideanSpace ℂ
                (Fin (2 * (c.firstBad.Nstar + 1) + 1))) -
          canonicalRieszSourceChannelEnergy
            c.firstBad.L 9 (c.firstBad.Nstar + 1)
            (c.evenShiftedTrial :
              EuclideanSpace ℂ
                (Fin (2 * (c.firstBad.Nstar + 1) + 1)))) =
      canonicalPolePrimeRieszEndpointScalar c.firstBad.L 8 *
        Complex.normSq J at hid
  constructor
  · intro h89
    have hprod :
        canonicalPolePrimeRieszEndpointScalar c.firstBad.L 8 *
            Complex.normSq J = 0 := by
      calc
        canonicalPolePrimeRieszEndpointScalar c.firstBad.L 8 *
            Complex.normSq J =
          2 * (2 * Real.pi) ^ 4 *
            (canonicalRieszSourceChannelEnergy
                c.firstBad.L 8 (c.firstBad.Nstar + 1)
                (c.evenShiftedTrial :
                  EuclideanSpace ℂ
                    (Fin (2 * (c.firstBad.Nstar + 1) + 1))) -
              canonicalRieszSourceChannelEnergy
                c.firstBad.L 9 (c.firstBad.Nstar + 1)
                (c.evenShiftedTrial :
                  EuclideanSpace ℂ
                    (Fin (2 * (c.firstBad.Nstar + 1) + 1)))) := hid.symm
        _ = 0 := by
          rw [h89, sub_self, mul_zero]
    exact
      (mul_eq_zero.mp hprod).resolve_right hnormSqNe
  · intro hscalar
    have hzero :
        2 * (2 * Real.pi) ^ 4 *
            (canonicalRieszSourceChannelEnergy
                c.firstBad.L 8 (c.firstBad.Nstar + 1)
                (c.evenShiftedTrial :
                  EuclideanSpace ℂ
                    (Fin (2 * (c.firstBad.Nstar + 1) + 1))) -
              canonicalRieszSourceChannelEnergy
                c.firstBad.L 9 (c.firstBad.Nstar + 1)
                (c.evenShiftedTrial :
                  EuclideanSpace ℂ
                    (Fin (2 * (c.firstBad.Nstar + 1) + 1)))) = 0 := by
      rw [hid, hscalar, zero_mul]
    have hscaleNe :
        2 * (2 * Real.pi) ^ 4 ≠ 0 := by
      positivity
    have hdiff :
        canonicalRieszSourceChannelEnergy
            c.firstBad.L 8 (c.firstBad.Nstar + 1)
            (c.evenShiftedTrial :
              EuclideanSpace ℂ
                (Fin (2 * (c.firstBad.Nstar + 1) + 1))) -
          canonicalRieszSourceChannelEnergy
            c.firstBad.L 9 (c.firstBad.Nstar + 1)
            (c.evenShiftedTrial :
              EuclideanSpace ℂ
                (Fin (2 * (c.firstBad.Nstar + 1) + 1))) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hscaleNe
    exact sub_eq_zero.mp hdiff

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceMomentMomentFour_coercive_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceMomentMixedJet_re_le_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceMomentMixedJet_re_neg_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddBad_or_sourceMomentMixedJet_re_neg_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEight_eq_nine_iff_endpointScalar_eq_zero_of_even_of_not_oddBad
