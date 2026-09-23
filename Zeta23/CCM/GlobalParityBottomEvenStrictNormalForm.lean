import Zeta23.CCM.GlobalParityBottomRetainedGeometry
import Zeta23.CCM.RegularFirstBadGammaObstruction

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — strict-even global-bottom normal form

Global-bottom selection does not by itself exclude a bad successor.  Its value
is that strict spectral separation replaces the historical "odd successor good
at zero" premise by positivity of the shifted odd operator.

This module records the strongest immediate real consequences already forced by
the strict-even ground state.  They are normal-form constraints, not a branch
exclusion.
-/

/-- In the strict-even global-ground branch the source scalar has positive
product with the completed-source scalar. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedEvenStrict_source_mul_completed_pos
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hground :
      c.lam =
        parityRayleighBottom .even c.firstBad.L
          (c.firstBad.Nstar + 1))
    (hstrict :
      parityRayleighBottom .even c.firstBad.L
          (c.firstBad.Nstar + 1) <
        parityRayleighBottom .odd c.firstBad.L
          (c.firstBad.Nstar + 1)) :
    0 <
      c.retainedRealSourceScalar *
        c.retainedRealCompletedSourceScalar := by
  obtain ⟨_hSM4, hSG, hf⟩ :=
    c.retainedGlobalBottomEvenStrictPackage hp hground hstrict
  have hq := c.retainedOddShellCenter_pos
  rw [hf]
  have hprod :
      0 <
        c.retainedOddShellCenter *
          (c.retainedRealSourceScalar *
            c.retainedRealCrossParityGamma) :=
    mul_pos hq hSG
  simpa [mul_assoc, mul_left_comm, mul_comm] using hprod

/-- Expanded completed-source form:
S*M4 - S^2*C is strictly positive in the strict-even global-ground branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedEvenStrict_correctedFourth_pos
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hground :
      c.lam =
        parityRayleighBottom .even c.firstBad.L
          (c.firstBad.Nstar + 1))
    (hstrict :
      parityRayleighBottom .even c.firstBad.L
          (c.firstBad.Nstar + 1) <
        parityRayleighBottom .odd c.firstBad.L
          (c.firstBad.Nstar + 1)) :
    0 <
      c.retainedRealSourceScalar * c.retainedRealMomentFour -
        c.retainedRealSourceScalar ^ 2 *
          c.retainedOddResolventCorrection := by
  have h :=
    c.retainedEvenStrict_source_mul_completed_pos
      hp hground hstrict
  rw [RegularCellMinimalNegativeEnergyCertificate.retainedRealCompletedSourceScalar] at h
  nlinarith

/-- Gamma and M4 have the same nonzero orientation in the strict-even branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedEvenStrict_gamma_mul_momentFour_pos
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hground :
      c.lam =
        parityRayleighBottom .even c.firstBad.L
          (c.firstBad.Nstar + 1))
    (hstrict :
      parityRayleighBottom .even c.firstBad.L
          (c.firstBad.Nstar + 1) <
        parityRayleighBottom .odd c.firstBad.L
          (c.firstBad.Nstar + 1)) :
    0 <
      c.retainedRealCrossParityGamma *
        c.retainedRealMomentFour := by
  obtain ⟨hSM4, hSG, _hf⟩ :=
    c.retainedGlobalBottomEvenStrictPackage hp hground hstrict
  rcases (mul_pos_iff.mp hSG) with hSGpos | hSGneg
  · rcases (mul_pos_iff.mp hSM4) with hSMpos | hSMneg
    · exact mul_pos hSGpos.2 hSMpos.2
    · exfalso
      linarith
  · rcases (mul_pos_iff.mp hSM4) with hSMpos | hSMneg
    · exfalso
      linarith
    · exact mul_pos_of_neg_of_neg hSGneg.2 hSMneg.2

/-- Compact strict-even orientation package.  Every listed scalar is nonzero;
the source, Gamma, M4, and completed source all share one real sign. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedEvenStrict_orientationPackage
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hground :
      c.lam =
        parityRayleighBottom .even c.firstBad.L
          (c.firstBad.Nstar + 1))
    (hstrict :
      parityRayleighBottom .even c.firstBad.L
          (c.firstBad.Nstar + 1) <
        parityRayleighBottom .odd c.firstBad.L
          (c.firstBad.Nstar + 1)) :
    0 < c.retainedRealSourceScalar * c.retainedRealMomentFour ∧
    0 < c.retainedRealSourceScalar * c.retainedRealCrossParityGamma ∧
    0 < c.retainedRealSourceScalar * c.retainedRealCompletedSourceScalar ∧
    0 < c.retainedRealCrossParityGamma * c.retainedRealMomentFour ∧
    0 ≤ c.retainedOddResolventCorrection := by
  obtain ⟨hSM4, hSG, _hf⟩ :=
    c.retainedGlobalBottomEvenStrictPackage hp hground hstrict
  exact ⟨
    hSM4,
    hSG,
    c.retainedEvenStrict_source_mul_completed_pos hp hground hstrict,
    c.retainedEvenStrict_gamma_mul_momentFour_pos hp hground hstrict,
    c.retainedOddResolventCorrection_nonneg
  ⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedEvenStrict_source_mul_completed_pos
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedEvenStrict_correctedFourth_pos
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedEvenStrict_gamma_mul_momentFour_pos
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedEvenStrict_orientationPackage
