import Zeta23.CCM.CrossParityCorrectionSourceCoupling
import Zeta23.CCM.RegularFirstBadCrossParityRiesz
import Zeta23.CCM.RegularFirstBadCrossParitySecularCompletion

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: retained cross-parity source balance

This module composes the retained even-selected cross-parity completion with
the #229 correction/source-coupling bridge.

On the same retained negative-root state,

  star(F_-) * q = star(S) * (M4 - S*C),
  F_- = Gamma * S,
  star(Gamma) * q = q - J,

where `J` is the canonical shell/source coupling evaluated at the resolvent
of the odd cubic-generator predecessor direction.

The factor-preserving theorem is unconditional beyond selected-even.  The
factor is cancelled only under an explicit nonzero-source hypothesis, and the
existing odd-good theorem supplies that hypothesis on the retained odd-good
branch.

No domination inequality, source-coupling sign, negative-root exclusion, or RH
claim is made.
-/

/-- Exact factor-preserving retained source balance.  No division by the
retained source moment is used. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceBalanceFactored_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    let S :=
      explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
    let M4 :=
      centeredMoment (c.firstBad.Nstar + 1) 4
        (evenBoundaryFlatRawCoefficients
          (c.firstBad.Nstar + 1) c.evenShiftedTrial)
    star S *
        (inner ℂ
            (intrinsicCubicShellPart .odd c.firstBad.Nstar :
              euclideanParityBoundaryFlatSubspace .odd
                (c.firstBad.Nstar + 1))
            (intrinsicCubicShellPart .odd c.firstBad.Nstar :
              euclideanParityBoundaryFlatSubspace .odd
                (c.firstBad.Nstar + 1)) -
          cubicShellCoupling .odd c.firstBad.L c.firstBad.Nstar
            (shiftedIntrinsicPredecessorResolvent
              .odd c.firstBad.L_pos c.firstBad.Nstar
              (c.firstBad.predecessorNonnegative_anyParity .odd)
              c.lam c.lam_neg
              (oddCubicGeneratorPredecessorPart c.firstBad.Nstar))) =
      star S *
        (M4 - S *
          oddCubicGeneratorResolventQuadratic
            c.firstBad.L_pos c.firstBad.Nstar
            (c.firstBad.predecessorNonnegative_anyParity .odd)
            c.lam c.lam_neg) := by
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
  let Gamma :=
    crossParitySecularGamma
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let F :=
    cubicSecularScalar
      .odd c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  change star S * (q - J) = star S * (M4 - S * C)
  have hcompletion :
      star F * q = star S * (M4 - S * C) := by
    exact c.evenShiftedCrossParitySecularCompletion hp
  have htransfer :
      F = Gamma * S := by
    exact c.oddSecularScalar_eq_gamma_mul_explicitSource_of_even hp
  have hgamma :
      star Gamma * q = q - J := by
    exact
      star_crossParitySecularGamma_mul_shellInner_eq_shellInner_sub_cubicShellCoupling
        c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
  have htransferStar := congrArg (starRingEnd ℂ) htransfer
  rw [map_mul] at htransferStar
  change star F = star Gamma * star S at htransferStar
  calc
    star S * (q - J) =
        star S * (star Gamma * q) := by rw [hgamma]
    _ = (star Gamma * star S) * q := by ring
    _ = star F * q := by
      rw [← htransferStar]
    _ = star S * (M4 - S * C) := hcompletion

/-- Cancelling an explicitly nonzero retained source moment yields the exact
same-state source balance. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceBalance_of_even_of_source_ne_zero
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hS :
      explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial ≠ 0) :
    let S :=
      explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
    let M4 :=
      centeredMoment (c.firstBad.Nstar + 1) 4
        (evenBoundaryFlatRawCoefficients
          (c.firstBad.Nstar + 1) c.evenShiftedTrial)
    inner ℂ
        (intrinsicCubicShellPart .odd c.firstBad.Nstar :
          euclideanParityBoundaryFlatSubspace .odd
            (c.firstBad.Nstar + 1))
        (intrinsicCubicShellPart .odd c.firstBad.Nstar :
          euclideanParityBoundaryFlatSubspace .odd
            (c.firstBad.Nstar + 1)) -
      cubicShellCoupling .odd c.firstBad.L c.firstBad.Nstar
        (shiftedIntrinsicPredecessorResolvent
          .odd c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .odd)
          c.lam c.lam_neg
          (oddCubicGeneratorPredecessorPart c.firstBad.Nstar)) =
    M4 - S *
      oddCubicGeneratorResolventQuadratic
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg := by
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
  change q - J = M4 - S * C
  have hfact :
      star S * (q - J) = star S * (M4 - S * C) := by
    exact c.evenShiftedCrossParitySourceBalanceFactored_of_even hp
  have hstarS : star S ≠ 0 :=
    star_ne_zero.mpr hS
  have hmul :
      star S * ((q - J) - (M4 - S * C)) = 0 := by
    calc
      star S * ((q - J) - (M4 - S * C)) =
          star S * (q - J) - star S * (M4 - S * C) := by ring
      _ = 0 := by rw [hfact, sub_self]
  have hdiff :
      (q - J) - (M4 - S * C) = 0 :=
    (mul_eq_zero.mp hmul).resolve_left hstarS
  exact sub_eq_zero.mp hdiff

/-- On the retained even-selected, odd-good branch the existing nonvanishing
theorem supplies the only hypothesis needed to cancel the source factor. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceBalance_of_even_of_not_oddBad
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
    inner ℂ
        (intrinsicCubicShellPart .odd c.firstBad.Nstar :
          euclideanParityBoundaryFlatSubspace .odd
            (c.firstBad.Nstar + 1))
        (intrinsicCubicShellPart .odd c.firstBad.Nstar :
          euclideanParityBoundaryFlatSubspace .odd
            (c.firstBad.Nstar + 1)) -
      cubicShellCoupling .odd c.firstBad.L c.firstBad.Nstar
        (shiftedIntrinsicPredecessorResolvent
          .odd c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .odd)
          c.lam c.lam_neg
          (oddCubicGeneratorPredecessorPart c.firstBad.Nstar)) =
    M4 - S *
      oddCubicGeneratorResolventQuadratic
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg := by
  have hS :=
    c.explicitSourceMoment_ne_zero_of_even_of_not_oddBad hp hodd
  exact
    c.evenShiftedCrossParitySourceBalance_of_even_of_source_ne_zero hp hS

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceBalanceFactored_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceBalance_of_even_of_source_ne_zero
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedCrossParitySourceBalance_of_even_of_not_oddBad
