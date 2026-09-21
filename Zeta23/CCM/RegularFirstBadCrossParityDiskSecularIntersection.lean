import Zeta23.CCM.ComplexDiskHalfPlane
import Zeta23.CCM.RegularFirstBadCrossParityGramDisk
import Zeta23.CCM.RegularFirstBadCrossParitySecularCompletion

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained disk / secular intersection

PR #218/#219 gives, on the retained selected-even / odd-good state, the exact
completed odd-secular half-plane

  (-lam) * ||u_-||^2 <= Re(star(S) * (M4 - S*C)).

PR #233 gives the sharp retained Gram disk

  |q - (M4 - S*C)|^2
    <= E_c * (Re(C) + lam * ||R a||^2).

This module intersects those two constraints.  The fourth moment `M4`
disappears from the final necessary condition: either the disk center itself
pays the secular floor, or the squared center deficit is bounded by the sharp
Gram radius.

Firewall: this is still a necessary condition on the selected-even / odd-good
branch.  It does not prove the intersection empty, does not address the
simultaneous odd-bad or odd-selected branches, and does not prove RH.
-/

/-- The cubic-shell self center is real and projects a source coefficient onto
its real part with the shell norm squared as scalar weight. -/
theorem re_star_mul_cubicShellSelf_eq_norm_sq_mul_re
    (S : ℂ) (N : ℕ) :
    Complex.re
        (star S *
          inner ℂ
            (intrinsicCubicShellPart .odd N :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))
            (intrinsicCubicShellPart .odd N :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) =
      ‖(intrinsicCubicShellPart .odd N :
          euclideanParityBoundaryFlatSubspace .odd (N + 1))‖ ^ 2 *
        Complex.re S := by
  rw [inner_self_eq_norm_sq_to_K]
  simp [Complex.mul_re, Complex.star_def]
  ring

/-- Sharp M4-free retained compatibility law.

The completed source value `M4 - S*C` must lie both in the #233 sharp Gram
disk around the shell center and in the #218 completed secular half-plane.
Therefore either the shell center already meets the secular floor or the
squared projection deficit is paid for by the sharp disk radius. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedDiskSecularIntersectionSharp_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    let S :=
      explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
    let q :=
      inner ℂ
        (intrinsicCubicShellPart .odd c.firstBad.Nstar :
          euclideanParityBoundaryFlatSubspace .odd
            (c.firstBad.Nstar + 1))
        (intrinsicCubicShellPart .odd c.firstBad.Nstar :
          euclideanParityBoundaryFlatSubspace .odd
            (c.firstBad.Nstar + 1))
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
    let Ec := cubicShellRealEnergy .odd c.firstBad.L c.firstBad.Nstar
    let uMinus :=
      cubicSecularTrialVector
        .odd c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
    let B := (-c.lam) * ‖uMinus‖ ^ 2
    let radiusSq := Ec * (Complex.re C + c.lam * ‖R a‖ ^ 2)
    B ≤ Complex.re (star S * q) ∨
      (B - Complex.re (star S * q)) ^ 2 ≤
        Complex.normSq S * radiusSq := by
  let S :=
    explicitCanonicalSourceMoment
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  let q :=
    inner ℂ
      (intrinsicCubicShellPart .odd c.firstBad.Nstar :
        euclideanParityBoundaryFlatSubspace .odd
          (c.firstBad.Nstar + 1))
      (intrinsicCubicShellPart .odd c.firstBad.Nstar :
        euclideanParityBoundaryFlatSubspace .odd
          (c.firstBad.Nstar + 1))
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
  let Ec := cubicShellRealEnergy .odd c.firstBad.L c.firstBad.Nstar
  let uMinus :=
    cubicSecularTrialVector
      .odd c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let B := (-c.lam) * ‖uMinus‖ ^ 2
  let radiusSq := Ec * (Complex.re C + c.lam * ‖R a‖ ^ 2)
  let F := M4 - S * C
  have hbudget :=
    c.evenShiftedCrossParitySecularBudget_of_even_of_not_oddBad hp hodd
  dsimp only at hbudget
  change B ≤ Complex.re (star S * F) at hbudget
  have hdisk :=
    c.evenShiftedCrossParitySourceGramDiskSharp_of_even_of_not_oddBad hp hodd
  dsimp only at hdisk
  change
    ‖q - M4 + S * C‖ ^ 2 ≤ radiusSq at hdisk
  have hcenter : q - F = q - M4 + S * C := by
    dsimp [F]
    ring
  rw [← hcenter] at hdisk
  exact
    complexDisk_halfPlane_support_dichotomy
      hdisk hbudget

/-- Outer M4-free retained compatibility law obtained from the simpler #233
outer Gram disk. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedDiskSecularIntersection_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    let S :=
      explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
    let q :=
      inner ℂ
        (intrinsicCubicShellPart .odd c.firstBad.Nstar :
          euclideanParityBoundaryFlatSubspace .odd
            (c.firstBad.Nstar + 1))
        (intrinsicCubicShellPart .odd c.firstBad.Nstar :
          euclideanParityBoundaryFlatSubspace .odd
            (c.firstBad.Nstar + 1))
    let C :=
      oddCubicGeneratorResolventQuadratic
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
    let Ec := cubicShellRealEnergy .odd c.firstBad.L c.firstBad.Nstar
    let uMinus :=
      cubicSecularTrialVector
        .odd c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
    let B := (-c.lam) * ‖uMinus‖ ^ 2
    B ≤ Complex.re (star S * q) ∨
      (B - Complex.re (star S * q)) ^ 2 ≤
        Complex.normSq S * (Ec * Complex.re C) := by
  let S :=
    explicitCanonicalSourceMoment
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  let q :=
    inner ℂ
      (intrinsicCubicShellPart .odd c.firstBad.Nstar :
        euclideanParityBoundaryFlatSubspace .odd
          (c.firstBad.Nstar + 1))
      (intrinsicCubicShellPart .odd c.firstBad.Nstar :
        euclideanParityBoundaryFlatSubspace .odd
          (c.firstBad.Nstar + 1))
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let Ec := cubicShellRealEnergy .odd c.firstBad.L c.firstBad.Nstar
  let uMinus :=
    cubicSecularTrialVector
      .odd c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let B := (-c.lam) * ‖uMinus‖ ^ 2
  let F := M4 - S * C
  have hbudget :=
    c.evenShiftedCrossParitySecularBudget_of_even_of_not_oddBad hp hodd
  dsimp only at hbudget
  change B ≤ Complex.re (star S * F) at hbudget
  have hdisk :=
    c.evenShiftedCrossParitySourceGramDisk_of_even_of_not_oddBad hp hodd
  dsimp only at hdisk
  change
    ‖q - M4 + S * C‖ ^ 2 ≤ Ec * Complex.re C at hdisk
  have hcenter : q - F = q - M4 + S * C := by
    dsimp [F]
    ring
  rw [← hcenter] at hdisk
  exact
    complexDisk_halfPlane_support_dichotomy
      hdisk hbudget

/-- Human-facing sharp form with the shell center projected explicitly onto
`Re S`.  This removes the last complex shell-center product from the
statement. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceRealPartOrSharpRadius_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    let S :=
      explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
    let shell :=
      (intrinsicCubicShellPart .odd c.firstBad.Nstar :
        euclideanParityBoundaryFlatSubspace .odd
          (c.firstBad.Nstar + 1))
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
    let Ec := cubicShellRealEnergy .odd c.firstBad.L c.firstBad.Nstar
    let uMinus :=
      cubicSecularTrialVector
        .odd c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
    let B := (-c.lam) * ‖uMinus‖ ^ 2
    let radiusSq := Ec * (Complex.re C + c.lam * ‖R a‖ ^ 2)
    B ≤ ‖shell‖ ^ 2 * Complex.re S ∨
      (B - ‖shell‖ ^ 2 * Complex.re S) ^ 2 ≤
        Complex.normSq S * radiusSq := by
  have h :=
    c.evenShiftedDiskSecularIntersectionSharp_of_even_of_not_oddBad hp hodd
  dsimp only at h
  rw [re_star_mul_cubicShellSelf_eq_norm_sq_mul_re] at h
  simpa using h

end Zeta23.CCM

#print axioms Zeta23.CCM.re_star_mul_cubicShellSelf_eq_norm_sq_mul_re
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedDiskSecularIntersectionSharp_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedDiskSecularIntersection_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceRealPartOrSharpRadius_of_even_of_not_oddBad
