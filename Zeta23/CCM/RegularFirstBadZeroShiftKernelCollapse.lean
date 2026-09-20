import Zeta23.CCM.CrossParityCorrectionFunctionalCollapse
import Zeta23.CCM.RegularFirstBadZeroShiftKernelBalance

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: predecessor-kernel direction collapse

PR #226 also collapses the two predecessor-kernel directions used by the
retained regular first-bad zero-shift balance. This is useful before
bi-regularization, where the relevant kernel coordinates need not vanish.

On the stronger bi-regular retained state the index kernel coordinate is already
zero, so this module is a classification/compression result rather than the
principal terminal obstruction.
-/

/-- The exact odd cubic-generator kernel coordinate is the same scalar multiple
of the transported even-shell kernel coordinate as its predecessor vector. -/
theorem oddCubicGeneratorKernelPart_eq_neg_kappa_smul_indexKernelPart
    (L : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    oddCubicGeneratorKernelPart L N =
      -(crossParityCubicCorrectionKappa N) •
        oddIndexCubicShellKernelPart L N := by
  unfold oddCubicGeneratorKernelPart oddIndexCubicShellKernelPart
  exact
    map_oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul
      N hN (intrinsicPredecessorKernelPart .odd L N)

/-- Retained even-selected / odd-good zero-shift kernel balance after the two
kernel directions are collapsed to one. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenZeroShiftKernelBalance_factorized_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (xPlus : intrinsicParityPredecessorSubspace .even c.firstBad.Nstar)
    (hxPlus :
      intrinsicPredecessorBlock .even c.firstBad.L c.firstBad.Nstar xPlus =
        intrinsicShellToPredecessor .even c.firstBad.L c.firstBad.Nstar
          (intrinsicCubicShellPart .even c.firstBad.Nstar)) :
    (cubicZeroShiftShellResponseScalar .even
        c.firstBad.L c.firstBad.Nstar xPlus -
      crossParityCubicCorrectionKappa c.firstBad.Nstar *
        explicitCanonicalSourceMoment
          c.firstBad.L (c.firstBad.Nstar + 1)
          (cubicZeroShiftTrialVector .even
            c.firstBad.L c.firstBad.Nstar xPlus)) •
      oddIndexCubicShellKernelPart
        c.firstBad.L c.firstBad.Nstar = 0 := by
  have hbal :=
    c.evenZeroShiftKernelBalance_of_even_of_not_oddBad
      hp hodd xPlus hxPlus
  rw [oddCubicGeneratorKernelPart_eq_neg_kappa_smul_indexKernelPart
    c.firstBad.L c.firstBad.Nstar c.firstBad.one_le_Nstar] at hbal
  calc
    (cubicZeroShiftShellResponseScalar .even
        c.firstBad.L c.firstBad.Nstar xPlus -
      crossParityCubicCorrectionKappa c.firstBad.Nstar *
        explicitCanonicalSourceMoment
          c.firstBad.L (c.firstBad.Nstar + 1)
          (cubicZeroShiftTrialVector .even
            c.firstBad.L c.firstBad.Nstar xPlus)) •
        oddIndexCubicShellKernelPart
          c.firstBad.L c.firstBad.Nstar =
      cubicZeroShiftShellResponseScalar .even
          c.firstBad.L c.firstBad.Nstar xPlus •
        oddIndexCubicShellKernelPart
          c.firstBad.L c.firstBad.Nstar +
      explicitCanonicalSourceMoment
          c.firstBad.L (c.firstBad.Nstar + 1)
          (cubicZeroShiftTrialVector .even
            c.firstBad.L c.firstBad.Nstar xPlus) •
        (-(crossParityCubicCorrectionKappa c.firstBad.Nstar) •
          oddIndexCubicShellKernelPart
            c.firstBad.L c.firstBad.Nstar) := by
      module
    _ = 0 := hbal

/-- Exhaustive pre-bi-regular classification of the factorized retained kernel
balance: either the exceptional scalar equality holds or the common kernel
correction direction vanishes. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenZeroShiftScalarExceptional_or_indexKernel_eq_zero
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (xPlus : intrinsicParityPredecessorSubspace .even c.firstBad.Nstar)
    (hxPlus :
      intrinsicPredecessorBlock .even c.firstBad.L c.firstBad.Nstar xPlus =
        intrinsicShellToPredecessor .even c.firstBad.L c.firstBad.Nstar
          (intrinsicCubicShellPart .even c.firstBad.Nstar)) :
    cubicZeroShiftShellResponseScalar .even
        c.firstBad.L c.firstBad.Nstar xPlus =
        crossParityCubicCorrectionKappa c.firstBad.Nstar *
          explicitCanonicalSourceMoment
            c.firstBad.L (c.firstBad.Nstar + 1)
            (cubicZeroShiftTrialVector .even
              c.firstBad.L c.firstBad.Nstar xPlus) ∨
      oddIndexCubicShellKernelPart
        c.firstBad.L c.firstBad.Nstar = 0 := by
  have hfac :=
    c.evenZeroShiftKernelBalance_factorized_of_even_of_not_oddBad
      hp hodd xPlus hxPlus
  rcases smul_eq_zero.mp hfac with hscalar | hkernel
  · left
    exact sub_eq_zero.mp hscalar
  · exact Or.inr hkernel

end Zeta23.CCM

#print axioms Zeta23.CCM.oddCubicGeneratorKernelPart_eq_neg_kappa_smul_indexKernelPart
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenZeroShiftKernelBalance_factorized_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenZeroShiftScalarExceptional_or_indexKernel_eq_zero
