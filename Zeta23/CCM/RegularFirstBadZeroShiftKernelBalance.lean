import Zeta23.CCM.GoodSectorKernelAnnihilation
import Zeta23.CCM.ZeroShiftCrossParityTransfer
import Zeta23.CCM.CrossParitySecularKernelDichotomy
import Zeta23.CCM.RegularFirstBadCrossParityRiesz

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained zero-shift kernel balance

This module composes three independently established pieces of the retained
first-bad state:

* the selected even branch has a regular zero-shift cubic preimage;
* the odd-good successor branch annihilates the actual odd cubic shell-coupling
  kernel coordinate;
* the old zero-shift cross-parity transport expresses that shell-coupling
  kernel coordinate as a linear combination of the transported even-shell
  correction and the exact odd cubic-generator correction used by #218/#219.

The resulting vector identity is

  sigma_+ * K_-(d) + mu_0 * K_-(a) = 0,

where sigma_+ is the even zero-shift shell response, mu_0 is the exact
zero-shift production source moment, d is the centered-index shell correction,
and a is the #218 odd cubic-generator predecessor correction.

The selected negative root already forces re(sigma_+) < 0, so sigma_+ is
nonzero.  Consequently the #219 regular branch K_-(a)=0 forces K_-(d)=0,
while K_-(d) != 0 forces the #219 resonant branch and a nonzero zero-shift
source moment.

Firewall: K_-(d)=0 is not itself a contradiction.  In particular, if the odd
projected predecessor kernel is trivial then both kernel coordinates vanish
vacuously.  This module therefore supplies a new compatibility equation but
does not exclude the regular branch, the resonant branch, simultaneous odd
badness, the odd-selected branch, any negative root, or RH.
-/

/-- Canonical odd predecessor-kernel coordinate of the correction carried by
the centered-index image of the even cubic shell. -/
def oddIndexCubicShellKernelPart
    (L : ℝ) (N : ℕ) :
    LinearMap.ker (intrinsicPredecessorBlock .odd L N) :=
  intrinsicPredecessorKernelPart .odd L N
    (oddIndexCubicShellPredecessorPart N)

/-- At the retained even-selected negative root, every selected even zero-shift
preimage has a strictly negative canonical shell response. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenZeroShiftShellResponse_re_neg_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (xPlus : intrinsicParityPredecessorSubspace .even c.firstBad.Nstar)
    (hxPlus :
      intrinsicPredecessorBlock .even c.firstBad.L c.firstBad.Nstar xPlus =
        intrinsicShellToPredecessor .even c.firstBad.L c.firstBad.Nstar
          (intrinsicCubicShellPart .even c.firstBad.Nstar)) :
    Complex.re
      (cubicZeroShiftShellResponseScalar .even
        c.firstBad.L c.firstBad.Nstar xPlus) < 0 := by
  have hsec :=
    c.evenSecularRoot_of_even hp
  have hroot :
      cubicExplicitSchurScalar
          .even c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .even)
          c.lam c.lam_neg = 0 :=
    (cubicExplicitSchurScalar_eq_zero_iff_cubicSecularScalar_eq_zero
      .even c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      c.lam c.lam_neg).2 hsec
  exact
    cubicZeroShiftShellResponseScalar_re_neg_of_explicit_root
      .even c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      xPlus hxPlus c.lam c.lam_neg hroot

/-- The retained even zero-shift shell response is nonzero. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenZeroShiftShellResponse_ne_zero_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (xPlus : intrinsicParityPredecessorSubspace .even c.firstBad.Nstar)
    (hxPlus :
      intrinsicPredecessorBlock .even c.firstBad.L c.firstBad.Nstar xPlus =
        intrinsicShellToPredecessor .even c.firstBad.L c.firstBad.Nstar
          (intrinsicCubicShellPart .even c.firstBad.Nstar)) :
    cubicZeroShiftShellResponseScalar .even
        c.firstBad.L c.firstBad.Nstar xPlus ≠ 0 := by
  intro hsigma
  have hneg :=
    c.evenZeroShiftShellResponse_re_neg_of_even hp xPlus hxPlus
  rw [hsigma] at hneg
  simpa using hneg

/-- Retained post-#219 zero-shift kernel balance.  Odd successor goodness kills
the actual odd cubic shell-coupling kernel coordinate, and the old exact
cross-parity transport then constrains the same source-correction kernel
coordinate K_-(a) that appears in the #219 regular/resonant dichotomy. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenZeroShiftKernelBalance_of_even_of_not_oddBad
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
          c.firstBad.L c.firstBad.Nstar xPlus •
        oddIndexCubicShellKernelPart
          c.firstBad.L c.firstBad.Nstar +
      explicitCanonicalSourceMoment
          c.firstBad.L (c.firstBad.Nstar + 1)
          (cubicZeroShiftTrialVector .even
            c.firstBad.L c.firstBad.Nstar xPlus) •
        oddCubicGeneratorKernelPart
          c.firstBad.L c.firstBad.Nstar = 0 := by
  have hcouple :
      cubicCouplingKernelPart .odd
          c.firstBad.L c.firstBad.Nstar = 0 :=
    cubicCouplingKernelPart_eq_zero_of_not_parityBad
      .odd c.firstBad.L c.firstBad.Nstar
      c.firstBad.one_le_Nstar hodd
  have htransport :=
    oddCubicCouplingKernelPart_eq_evenZeroShiftResponse_add_source
      c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      xPlus hxPlus
  rw [hcouple] at htransport
  simpa [oddIndexCubicShellKernelPart, oddCubicGeneratorKernelPart] using
    htransport.symm

/-- On the retained even-selected / odd-good branch, the #219 regular source
correction branch K_-(a)=0 forces the transported even-shell correction to be
regular as well: K_-(d)=0. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.oddIndexCubicShellKernelPart_eq_zero_of_even_of_not_oddBad_of_generatorKernel_eq_zero
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (xPlus : intrinsicParityPredecessorSubspace .even c.firstBad.Nstar)
    (hxPlus :
      intrinsicPredecessorBlock .even c.firstBad.L c.firstBad.Nstar xPlus =
        intrinsicShellToPredecessor .even c.firstBad.L c.firstBad.Nstar
          (intrinsicCubicShellPart .even c.firstBad.Nstar))
    (hka :
      oddCubicGeneratorKernelPart
        c.firstBad.L c.firstBad.Nstar = 0) :
    oddIndexCubicShellKernelPart
      c.firstBad.L c.firstBad.Nstar = 0 := by
  have hbal :=
    c.evenZeroShiftKernelBalance_of_even_of_not_oddBad
      hp hodd xPlus hxPlus
  rw [hka, smul_zero, add_zero] at hbal
  have hsigma :=
    c.evenZeroShiftShellResponse_ne_zero_of_even hp xPlus hxPlus
  exact (smul_eq_zero.mp hbal).resolve_left hsigma

/-- Contrapositive form: a nonzero transported even-shell kernel coordinate
forces the exact #219 odd cubic-generator correction into its resonant branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.oddCubicGeneratorKernelPart_ne_zero_of_even_of_not_oddBad_of_indexKernel_ne_zero
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (xPlus : intrinsicParityPredecessorSubspace .even c.firstBad.Nstar)
    (hxPlus :
      intrinsicPredecessorBlock .even c.firstBad.L c.firstBad.Nstar xPlus =
        intrinsicShellToPredecessor .even c.firstBad.L c.firstBad.Nstar
          (intrinsicCubicShellPart .even c.firstBad.Nstar))
    (hkd :
      oddIndexCubicShellKernelPart
        c.firstBad.L c.firstBad.Nstar ≠ 0) :
    oddCubicGeneratorKernelPart
      c.firstBad.L c.firstBad.Nstar ≠ 0 := by
  intro hka
  exact hkd
    (c.oddIndexCubicShellKernelPart_eq_zero_of_even_of_not_oddBad_of_generatorKernel_eq_zero
      hp hodd xPlus hxPlus hka)

/-- If the transported even-shell correction has a nonzero odd kernel
coordinate, the same zero-shift balance also forces the exact zero-shift source
moment to be nonzero. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenZeroShiftSourceMoment_ne_zero_of_even_of_not_oddBad_of_indexKernel_ne_zero
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (xPlus : intrinsicParityPredecessorSubspace .even c.firstBad.Nstar)
    (hxPlus :
      intrinsicPredecessorBlock .even c.firstBad.L c.firstBad.Nstar xPlus =
        intrinsicShellToPredecessor .even c.firstBad.L c.firstBad.Nstar
          (intrinsicCubicShellPart .even c.firstBad.Nstar))
    (hkd :
      oddIndexCubicShellKernelPart
        c.firstBad.L c.firstBad.Nstar ≠ 0) :
    explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1)
        (cubicZeroShiftTrialVector .even
          c.firstBad.L c.firstBad.Nstar xPlus) ≠ 0 := by
  intro hmu
  have hbal :=
    c.evenZeroShiftKernelBalance_of_even_of_not_oddBad
      hp hodd xPlus hxPlus
  rw [hmu, zero_smul, add_zero] at hbal
  have hsigma :=
    c.evenZeroShiftShellResponse_ne_zero_of_even hp xPlus hxPlus
  have hkd0 :
      oddIndexCubicShellKernelPart
        c.firstBad.L c.firstBad.Nstar = 0 :=
    (smul_eq_zero.mp hbal).resolve_left hsigma
  exact hkd hkd0

/-- The retained even-selected certificate supplies an actual even zero-shift
preimage on which the post-#219 balance and strict negative response hold. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.exists_evenZeroShiftKernelBalance_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    ∃ xPlus : intrinsicParityPredecessorSubspace .even c.firstBad.Nstar,
      intrinsicPredecessorBlock .even c.firstBad.L c.firstBad.Nstar xPlus =
          intrinsicShellToPredecessor .even c.firstBad.L c.firstBad.Nstar
            (intrinsicCubicShellPart .even c.firstBad.Nstar) ∧
      Complex.re
          (cubicZeroShiftShellResponseScalar .even
            c.firstBad.L c.firstBad.Nstar xPlus) < 0 ∧
      cubicZeroShiftShellResponseScalar .even
            c.firstBad.L c.firstBad.Nstar xPlus •
          oddIndexCubicShellKernelPart
            c.firstBad.L c.firstBad.Nstar +
        explicitCanonicalSourceMoment
            c.firstBad.L (c.firstBad.Nstar + 1)
            (cubicZeroShiftTrialVector .even
              c.firstBad.L c.firstBad.Nstar xPlus) •
          oddCubicGeneratorKernelPart
            c.firstBad.L c.firstBad.Nstar = 0 := by
  have hregEven :
      IntrinsicPredecessorRegular
        .even c.firstBad.L c.firstBad.Nstar := by
    simpa [hp] using c.firstBad.regular
  obtain ⟨xPlus, hxPlus, _hunique⟩ :=
    existsUnique_cubicZeroShiftPreimage_of_regular
      .even c.firstBad.L c.firstBad.Nstar hregEven
  refine ⟨xPlus, hxPlus, ?_, ?_⟩
  · exact c.evenZeroShiftShellResponse_re_neg_of_even hp xPlus hxPlus
  · exact
      c.evenZeroShiftKernelBalance_of_even_of_not_oddBad
        hp hodd xPlus hxPlus

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenZeroShiftShellResponse_re_neg_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenZeroShiftKernelBalance_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddIndexCubicShellKernelPart_eq_zero_of_even_of_not_oddBad_of_generatorKernel_eq_zero
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.exists_evenZeroShiftKernelBalance_of_even_of_not_oddBad
