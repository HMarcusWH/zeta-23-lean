import Zeta23.CCM.RegularFirstBadCrossParityDiskSecularIntersection
import Zeta23.CCM.RegularFirstBadSourceKernel

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained source-kernel forbidden quadrant

PR #234 eliminates the retained fourth moment on the selected-even / odd-good
branch and proves the sharp alternative

  B <= ||c_-||^2 * Re(S)
  or
  (B - ||c_-||^2 * Re(S))^2 <= normSq(S) * R_sharp.

PR #213 identifies the same retained source moment exactly with the canonical
continuous-plus-prime source kernel.

This module packages those results into two real arithmetic observables:

  D := B - ||c_-||^2 * Re(S),
  E := D^2 - normSq(S) * R_sharp.

Hence odd-good implies D <= 0 or E <= 0.  Equivalently, simultaneous strict
positivity D>0 and E>0 forces the odd successor to be bad.

This is an interface theorem, not new arithmetic sign information.  No claim
that D>0 or E>0 is made here.  The simultaneous odd-bad branch, odd-selected
branch, parity-complete retained exclusion, terminal Mathlib RH seam, and RH
remain open.
-/

/-- Exact sharp radius from the post-#233/#234 retained Gram geometry. -/
def
    RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernelSharpRadiusSq
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) : ℝ :=
  let a := oddCubicGeneratorPredecessorPart c.firstBad.Nstar
  let R :=
    shiftedIntrinsicPredecessorResolvent
      .odd c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  cubicShellRealEnergy .odd c.firstBad.L c.firstBad.Nstar *
    (Complex.re C + c.lam * ‖R a‖ ^ 2)

/-- Center deficit for the exact canonical source kernel on the retained state.

Strict positivity means the direct center branch of the #234 compatibility
alternative is unavailable. -/
def
    RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernelCenterDeficit
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) : ℝ :=
  let S :=
    quadraticNormalSourceKernelRHS
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let shell :=
    (intrinsicCubicShellPart .odd c.firstBad.Nstar :
      euclideanParityBoundaryFlatSubspace .odd
        (c.firstBad.Nstar + 1))
  let uMinus :=
    cubicSecularTrialVector
      .odd c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  (-c.lam) * ‖uMinus‖ ^ 2 -
    ‖shell‖ ^ 2 * Complex.re S

/-- Sharp radius excess for the exact canonical source kernel.

Strict positivity means the radius-compensation branch of the #234
compatibility alternative is unavailable. -/
def
    RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernelSharpExcess
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) : ℝ :=
  let S :=
    quadraticNormalSourceKernelRHS
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  c.retainedSourceKernelCenterDeficit ^ 2 -
    Complex.normSq S * c.retainedSourceKernelSharpRadiusSq

/-- Source-kernel form of the merged-green PR #234 compatibility theorem.

On the selected-even / odd-good branch, the exact canonical source kernel
cannot lie in the positive-positive (D,E) quadrant. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernelDeficit_or_excess_nonpos_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    c.retainedSourceKernelCenterDeficit ≤ 0 ∨
      c.retainedSourceKernelSharpExcess ≤ 0 := by
  have h :=
    c.evenShiftedSourceRealPartOrSharpRadius_of_even_of_not_oddBad hp hodd
  rw [c.evenShiftedExplicitCanonicalSourceMoment_eq_sourceKernelRHS] at h
  simpa [retainedSourceKernelCenterDeficit,
    retainedSourceKernelSharpExcess,
    retainedSourceKernelSharpRadiusSq,
    sub_nonpos] using h

/-- Flagship contradiction interface.

If independent canonical arithmetic proves both exact retained source-kernel
observables strictly positive, then the odd successor cannot be good: it must
already be bad. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.oddBad_of_even_of_sourceKernelDeficit_pos_of_sharpExcess_pos
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hD : 0 < c.retainedSourceKernelCenterDeficit)
    (hE : 0 < c.retainedSourceKernelSharpExcess) :
    ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1) := by
  by_contra hodd
  have h :=
    c.retainedSourceKernelDeficit_or_excess_nonpos_of_even_of_not_oddBad
      hp hodd
  rcases h with hD' | hE'
  · linarith
  · linarith

/-- Equivalent forbidden-quadrant form on the odd-good branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.not_retainedSourceKernelForbiddenQuadrant_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    ¬ (
      0 < c.retainedSourceKernelCenterDeficit ∧
      0 < c.retainedSourceKernelSharpExcess
    ) := by
  intro hpos
  rcases hpos with ⟨hD, hE⟩
  exact hodd
    (c.oddBad_of_even_of_sourceKernelDeficit_pos_of_sharpExcess_pos
      hp hD hE)

/-- Same-state package: on the selected-even / odd-good branch the exact
canonical source kernel simultaneously obeys the forbidden-quadrant
compatibility law and the previously proved strict seventh-jet
anti-alignment. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceKernelCompatibilityPackage_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    (c.retainedSourceKernelCenterDeficit ≤ 0 ∨
      c.retainedSourceKernelSharpExcess ≤ 0) ∧
      Complex.re
        (star
            (quadraticNormalSourceKernelRHS
              c.firstBad.L (c.firstBad.Nstar + 1)
              c.evenShiftedTrial) *
          iteratedDeriv 7 c.evenShiftedQuadraticNormalSourceAtom 0) < 0 := by
  exact ⟨
    c.retainedSourceKernelDeficit_or_excess_nonpos_of_even_of_not_oddBad
      hp hodd,
    c.evenShiftedSourceKernelMixedJet_re_neg_of_even_of_not_oddBad
      hp hodd
  ⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernelDeficit_or_excess_nonpos_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddBad_of_even_of_sourceKernelDeficit_pos_of_sharpExcess_pos
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.not_retainedSourceKernelForbiddenQuadrant_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceKernelCompatibilityPackage_of_even_of_not_oddBad
