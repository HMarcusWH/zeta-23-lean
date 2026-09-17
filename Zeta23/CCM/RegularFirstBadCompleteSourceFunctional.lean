import Zeta23.CCM.CanonicalQuadraticNormalSourceFunctional
import Zeta23.CCM.RegularFirstBadPairDCoercivity

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained complete-source functional

This module rewrites the merged-green PR #209 anti-alignment theorem through
the exact complete functional representation. No new sign information is
introduced: the value is the same production source moment on the same retained
state and the jet is the same seventh jet of the same source observable.
-/

/-- Exact complete-functional representation on the retained even shifted
trial. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedExplicitCanonicalSourceMoment_eq_completeSourceFunctional
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial =
      canonicalQuadraticNormalSourceFunctional
        c.firstBad.L c.evenShiftedQuadraticNormalSourceAtom := by
  change
    explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial =
      canonicalQuadraticNormalSourceFunctional c.firstBad.L
        (quadraticNormalSourceAtom
          (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  exact
    explicitCanonicalSourceMoment_eq_completeSourceFunctional
      c.firstBad.L_pos (c.firstBad.Nstar + 1) (by omega)
      c.evenShiftedTrial

/-- Retained strict anti-alignment written entirely as a complete-functional /
local-jet statement on one source observable. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCompleteSourceFunctionalMixedJet_re_neg_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    Complex.re
        (star
            (canonicalQuadraticNormalSourceFunctional
              c.firstBad.L c.evenShiftedQuadraticNormalSourceAtom) *
          iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0) < 0 := by
  have h :=
    c.evenShiftedSourceMomentMixedJet_re_neg_of_even_of_not_oddBad hp hodd
  rw [c.evenShiftedExplicitCanonicalSourceMoment_eq_completeSourceFunctional] at h
  exact h

/-- Complete-functional Pair-D fork: either the odd successor is already bad,
or the exact complete arithmetic functional is strictly anti-aligned with the
seventh local jet of the same retained source observable. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.oddBad_or_completeSourceFunctionalMixedJet_re_neg_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1) ∨
      Complex.re
        (star
            (canonicalQuadraticNormalSourceFunctional
              c.firstBad.L c.evenShiftedQuadraticNormalSourceAtom) *
          iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0) < 0 := by
  by_cases hodd :
      ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)
  · exact Or.inl hodd
  · exact Or.inr
      (c.evenShiftedCompleteSourceFunctionalMixedJet_re_neg_of_even_of_not_oddBad
        hp hodd)

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedExplicitCanonicalSourceMoment_eq_completeSourceFunctional
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedCompleteSourceFunctionalMixedJet_re_neg_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddBad_or_completeSourceFunctionalMixedJet_re_neg_of_even
