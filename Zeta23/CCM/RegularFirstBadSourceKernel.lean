import Zeta23.CCM.CanonicalQuadraticNormalSourceKernel
import Zeta23.CCM.RegularFirstBadCompleteSourceFunctional

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained source-kernel interface

This module rewrites the merged-green PR #209 anti-alignment theorem through
the exact source-coordinate kernel representation.  No new sign or magnitude
information is introduced.
-/

/-- Exact source-kernel representation on the retained even shifted trial. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedExplicitCanonicalSourceMoment_eq_sourceKernelRHS
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial =
      quadraticNormalSourceKernelRHS
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial := by
  exact
    explicitCanonicalSourceMoment_eq_sourceKernelRHS
      c.firstBad.L_pos (c.firstBad.Nstar + 1) (by omega)
      c.evenShiftedTrial

/-- Retained strict anti-alignment written with the explicit source-coordinate
kernel on the same source observable. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceKernelMixedJet_re_neg_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    Complex.re
        (star
            (quadraticNormalSourceKernelRHS
              c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial) *
          iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0) < 0 := by
  have h :=
    c.evenShiftedSourceMomentMixedJet_re_neg_of_even_of_not_oddBad hp hodd
  rw [c.evenShiftedExplicitCanonicalSourceMoment_eq_sourceKernelRHS] at h
  exact h

/-- Source-kernel Pair-D fork: either the odd successor is already bad, or the
exact continuous-plus-prime source kernel is strictly anti-aligned with the
seventh local jet of the same retained source observable. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.oddBad_or_sourceKernelMixedJet_re_neg_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1) ∨
      Complex.re
        (star
            (quadraticNormalSourceKernelRHS
              c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial) *
          iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0) < 0 := by
  by_cases hodd :
      ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)
  · exact Or.inl hodd
  · exact Or.inr
      (c.evenShiftedSourceKernelMixedJet_re_neg_of_even_of_not_oddBad hp hodd)

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceKernelMixedJet_re_neg_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddBad_or_sourceKernelMixedJet_re_neg_of_even
