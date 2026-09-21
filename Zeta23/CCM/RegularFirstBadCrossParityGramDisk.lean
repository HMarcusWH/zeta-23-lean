import Zeta23.CCM.CanonicalGoodSectorGram
import Zeta23.CCM.ShiftedPredecessorResolventEnergy
import Zeta23.CCM.RegularFirstBadCrossParitySourceBalance

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained cross-parity Gram disk

PR #231 proved the exact retained selected-even / odd-good source balance

  q - J = M4 - S C,

where `J` is now the canonical odd shell coupling evaluated at the shifted
resolvent of the odd cubic-generator predecessor part.

The good odd successor sector also supplies canonical Gram control.  Combining
those two facts places the actual retained source state inside the exact disk

  |q - M4 + S C|^2 <= E_c E_A(R a).

The shifted-resolvent energy identity sharpens the right-hand side to

  E_c (Re C + lam ||R a||^2),

and `lam < 0` gives the simpler outer disk

  |q - M4 + S C|^2 <= E_c Re C.

The sharp negative-shift term is theorem-locked before it is discarded.

Firewall: this constrains the retained selected-even / odd-good branch but does
not by itself prove that the disk is empty.  The simultaneous-bad branch,
opposite selected parity, parity-complete exclusion, the terminal RH seam, and
RH all remain open.
-/

/-- The exact #231 retained source balance, combined with good-sector Gram
control, bounds the retained source center by the predecessor energy of the
same shifted-resolvent state. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceGramDiskEnergy_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
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
    ‖q - M4 + S * C‖ ^ 2 ≤
      cubicShellRealEnergy .odd c.firstBad.L c.firstBad.Nstar *
        intrinsicPredecessorRealEnergy
          .odd c.firstBad.L c.firstBad.Nstar (R a) := by
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
  let J :=
    cubicShellCoupling .odd c.firstBad.L c.firstBad.Nstar (R a)
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let Ec := cubicShellRealEnergy .odd c.firstBad.L c.firstBad.Nstar
  change
    ‖q - M4 + S * C‖ ^ 2 ≤
      Ec *
        intrinsicPredecessorRealEnergy
          .odd c.firstBad.L c.firstBad.Nstar (R a)
  have hbalance :=
    c.evenShiftedCrossParitySourceBalance_of_even_of_not_oddBad hp hodd
  change q - J = M4 - S * C at hbalance
  have hcenter : q - M4 + S * C = J := by
    calc
      q - M4 + S * C = q - (M4 - S * C) := by ring
      _ = q - (q - J) := by rw [← hbalance]
      _ = J := by ring
  have hdet :=
    cubicOneStepDeterminant_nonnegative_of_not_parityBad
      hodd (R a)
  change
    0 ≤
      Ec *
          intrinsicPredecessorRealEnergy
            .odd c.firstBad.L c.firstBad.Nstar (R a) -
        ‖J‖ ^ 2 at hdet
  rw [hcenter]
  exact sub_nonneg.mp hdet

/-- Sharp retained source Gram disk.  The negative-shift correction is retained
exactly instead of being discarded. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceGramDiskSharp_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
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
    ‖q - M4 + S * C‖ ^ 2 ≤
      cubicShellRealEnergy .odd c.firstBad.L c.firstBad.Nstar *
        (Complex.re C + c.lam * ‖R a‖ ^ 2) := by
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
  change
    ‖q - M4 + S * C‖ ^ 2 ≤
      Ec * (Complex.re C + c.lam * ‖R a‖ ^ 2)
  have henergy :=
    c.evenShiftedCrossParitySourceGramDiskEnergy_of_even_of_not_oddBad
      hp hodd
  change
    ‖q - M4 + S * C‖ ^ 2 ≤
      Ec *
        intrinsicPredecessorRealEnergy
          .odd c.firstBad.L c.firstBad.Nstar (R a) at henergy
  have hres :=
    intrinsicPredecessorRealEnergy_shiftedIntrinsicPredecessorResolvent_eq
      .odd c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg a
  change
    intrinsicPredecessorRealEnergy
        .odd c.firstBad.L c.firstBad.Nstar (R a) =
      Complex.re C + c.lam * ‖R a‖ ^ 2 at hres
  rw [hres] at henergy
  exact henergy

/-- Simpler outer retained source disk obtained by dropping the nonpositive
negative-shift correction from the sharp radius. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceGramDisk_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
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
    ‖q - M4 + S * C‖ ^ 2 ≤
      cubicShellRealEnergy .odd c.firstBad.L c.firstBad.Nstar *
        Complex.re C := by
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
  change
    ‖q - M4 + S * C‖ ^ 2 ≤ Ec * Complex.re C
  have hsharp :=
    c.evenShiftedCrossParitySourceGramDiskSharp_of_even_of_not_oddBad hp hodd
  change
    ‖q - M4 + S * C‖ ^ 2 ≤
      Ec * (Complex.re C + c.lam * ‖R a‖ ^ 2) at hsharp
  have hEc : 0 ≤ Ec := by
    simpa [Ec] using
      cubicShellRealEnergy_nonnegative_of_not_parityBad hodd
  have hshift : c.lam * ‖R a‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (le_of_lt c.lam_neg) (sq_nonneg _)
  have hinside :
      Complex.re C + c.lam * ‖R a‖ ^ 2 ≤ Complex.re C := by
    linarith
  have hright :
      Ec * (Complex.re C + c.lam * ‖R a‖ ^ 2) ≤
        Ec * Complex.re C :=
    mul_le_mul_of_nonneg_left hinside hEc
  exact hsharp.trans hright

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceGramDiskEnergy_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceGramDiskSharp_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceGramDisk_of_even_of_not_oddBad
