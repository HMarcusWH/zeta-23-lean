import Zeta23.CCM.ZeroShiftSchurClassification
import Zeta23.CCM.RegularFirstBadCanonicalEnergy

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained zero-shift Schur classification

This module specializes the generic exact zero-shift Schur classification to
the retained regular cell-minimal first-bad certificate.

Whole-cell first-bad ancestry already gives predecessor nonnegativity in either
reversal parity at the retained predecessor size, so the classification can be
used for either successor parity without assuming which parity was selected.

In particular, the previously opaque simultaneous odd-bad branch now splits
exactly into:

* resonant odd badness: the actual odd cubic shell coupling has nonzero
  predecessor-kernel coordinate;
* regular odd badness: an odd zero-shift preimage exists and its Schur endpoint
  has strictly negative real part.

This classifies the branch but does not exclude either alternative.

Firewalls:
* the shell-coupling kernel coordinate is not the #219 source-correction kernel
  coordinate and not the #220 transported-index correction;
* no selected-parity symmetry is assumed;
* no negative-root exclusion, finite-to-infinite closure, or RH theorem is
  claimed.
-/

/-- Retained first-bad specialization of the exact bad-sector Schur
classification for an arbitrary successor parity. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.successorParityBad_iff_cubicCouplingResonant_or_zeroShiftEndpoint_neg
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (p : ReversalParity) :
    ParityBad p c.firstBad.L (c.firstBad.Nstar + 1) ↔
      cubicCouplingKernelPart p
          c.firstBad.L c.firstBad.Nstar ≠ 0 ∨
        ∃ x₀ : intrinsicParityPredecessorSubspace p c.firstBad.Nstar,
          intrinsicPredecessorBlock p c.firstBad.L c.firstBad.Nstar x₀ =
              intrinsicShellToPredecessor p
                c.firstBad.L c.firstBad.Nstar
                (intrinsicCubicShellPart p c.firstBad.Nstar) ∧
          Complex.re
            (cubicZeroShiftSchurEndpoint p
              c.firstBad.L c.firstBad.Nstar x₀) < 0 := by
  exact
    parityBad_iff_cubicCouplingKernelPart_ne_zero_or_exists_zeroShiftEndpoint_neg
      p c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity p)

/-- Retained first-bad specialization of the exact good-sector Schur
classification for an arbitrary successor parity. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.not_successorParityBad_iff_exists_zeroShiftPreimage_endpoint_nonnegative
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (p : ReversalParity) :
    (¬ ParityBad p c.firstBad.L (c.firstBad.Nstar + 1)) ↔
      ∃ x₀ : intrinsicParityPredecessorSubspace p c.firstBad.Nstar,
        intrinsicPredecessorBlock p c.firstBad.L c.firstBad.Nstar x₀ =
            intrinsicShellToPredecessor p
              c.firstBad.L c.firstBad.Nstar
              (intrinsicCubicShellPart p c.firstBad.Nstar) ∧
        0 ≤ Complex.re
          (cubicZeroShiftSchurEndpoint p
            c.firstBad.L c.firstBad.Nstar x₀) := by
  exact
    not_parityBad_iff_exists_cubicZeroShiftPreimage_endpoint_nonnegative
      p c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity p)

/-- Route-facing odd specialization: simultaneous odd badness is exactly
resonant odd shell coupling or regular odd coupling with negative zero-shift
endpoint. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.oddBad_iff_oddCubicCouplingResonant_or_zeroShiftEndpoint_neg
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1) ↔
      cubicCouplingKernelPart .odd
          c.firstBad.L c.firstBad.Nstar ≠ 0 ∨
        ∃ xMinus : intrinsicParityPredecessorSubspace .odd c.firstBad.Nstar,
          intrinsicPredecessorBlock .odd
              c.firstBad.L c.firstBad.Nstar xMinus =
            intrinsicShellToPredecessor .odd
              c.firstBad.L c.firstBad.Nstar
              (intrinsicCubicShellPart .odd c.firstBad.Nstar) ∧
          Complex.re
            (cubicZeroShiftSchurEndpoint .odd
              c.firstBad.L c.firstBad.Nstar xMinus) < 0 := by
  exact c.successorParityBad_iff_cubicCouplingResonant_or_zeroShiftEndpoint_neg
    .odd

/-- Route-facing odd-good specialization: odd goodness is exactly existence of
an odd zero-shift preimage with nonnegative Schur endpoint. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.not_oddBad_iff_exists_oddZeroShiftPreimage_endpoint_nonnegative
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    (¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) ↔
      ∃ xMinus : intrinsicParityPredecessorSubspace .odd c.firstBad.Nstar,
        intrinsicPredecessorBlock .odd
            c.firstBad.L c.firstBad.Nstar xMinus =
          intrinsicShellToPredecessor .odd
            c.firstBad.L c.firstBad.Nstar
            (intrinsicCubicShellPart .odd c.firstBad.Nstar) ∧
        0 ≤ Complex.re
          (cubicZeroShiftSchurEndpoint .odd
            c.firstBad.L c.firstBad.Nstar xMinus) := by
  exact c.not_successorParityBad_iff_exists_zeroShiftPreimage_endpoint_nonnegative
    .odd

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.successorParityBad_iff_cubicCouplingResonant_or_zeroShiftEndpoint_neg
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.not_successorParityBad_iff_exists_zeroShiftPreimage_endpoint_nonnegative
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddBad_iff_oddCubicCouplingResonant_or_zeroShiftEndpoint_neg
