import Zeta23.CCM.GlobalFirstBadParityBottomAlignment
import Zeta23.CCM.GlobalParityBottomSourceMoment
import Zeta23.CCM.RegularFirstBadGammaObstruction

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — retained geometry at a strict even global ground

Once a retained negative-energy certificate has been reselected so that its
stored shift is the true even parity bottom, strict separation from the odd
bottom replaces the historical odd-good-at-zero premise in several important
places.

The source moment and fourth moment have a strictly positive pairing, the
source moment is nonzero, the source-balance factor can therefore be cancelled,
and the exact Gamma/source product has positive orientation.  All of this can
hold even when the odd successor remains bad at zero.
-/

/-- Source/M4 pairing at an even-aligned global ground. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedSourceMomentMomentFour_pos_of_evenGround_strict
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
      Complex.re
        (star
            (explicitCanonicalSourceMoment
              c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial) *
          centeredMoment (c.firstBad.Nstar + 1) 4
            (evenBoundaryFlatRawCoefficients
              (c.firstBad.Nstar + 1) c.evenShiftedTrial)) := by
  obtain ⟨hvne, hveig⟩ :=
    c.evenShiftedTrial_eigenmode_of_even hp
  have hveigGround :
      parityCompressedCanonical .even c.firstBad.L
          (c.firstBad.Nstar + 1) c.evenShiftedTrial =
        (parityRayleighBottom .even c.firstBad.L
          (c.firstBad.Nstar + 1) : ℂ) • c.evenShiftedTrial := by
    change
      evenCompressedCanonical c.firstBad.L
          (c.firstBad.Nstar + 1) c.evenShiftedTrial =
        (parityRayleighBottom .even c.firstBad.L
          (c.firstBad.Nstar + 1) : ℂ) • c.evenShiftedTrial
    rw [← hground]
    exact hveig
  have hK : 2 ≤ c.firstBad.Nstar + 1 := by
    simpa using Nat.succ_le_succ c.firstBad.one_le_Nstar
  exact
    re_star_source_mul_momentFour_pos_of_evenGround_strict
      c.firstBad.L_pos (c.firstBad.Nstar + 1) hK
      c.evenShiftedTrial hvne hveigGround hstrict

theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedSourceMoment_ne_zero_of_evenGround_strict
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
    explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial ≠ 0 := by
  have hpos :=
    c.retainedSourceMomentMomentFour_pos_of_evenGround_strict
      hp hground hstrict
  intro hzero
  rw [hzero] at hpos
  norm_num at hpos

theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedMomentFour_ne_zero_of_evenGround_strict
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
    centeredMoment (c.firstBad.Nstar + 1) 4
        (evenBoundaryFlatRawCoefficients
          (c.firstBad.Nstar + 1) c.evenShiftedTrial) ≠ 0 := by
  have hpos :=
    c.retainedSourceMomentMomentFour_pos_of_evenGround_strict
      hp hground hstrict
  intro hzero
  rw [hzero] at hpos
  norm_num at hpos

/-- Generalize the old odd-good completed-source/Gamma identity: source
nonvanishing is the actual algebraic premise needed for the cancellation. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealCompletedSourceScalar_eq_shellCenter_mul_gamma_of_even_of_source_ne_zero
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hS :
      explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial ≠ 0) :
    c.retainedRealCompletedSourceScalar =
      c.retainedOddShellCenter * c.retainedRealCrossParityGamma := by
  let Gamma :=
    crossParitySecularGamma
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  let shell :=
    (intrinsicCubicShellPart .odd c.firstBad.Nstar :
      euclideanParityBoundaryFlatSubspace .odd
        (c.firstBad.Nstar + 1))
  let qC := inner ℂ shell shell
  let J :=
    cubicShellCoupling .odd c.firstBad.L c.firstBad.Nstar
      (shiftedIntrinsicPredecessorResolvent
        .odd c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg
        (oddCubicGeneratorPredecessorPart c.firstBad.Nstar))
  let M4 :=
    centeredMoment (c.firstBad.Nstar + 1) 4
      (evenBoundaryFlatRawCoefficients
        (c.firstBad.Nstar + 1) c.evenShiftedTrial)
  let S :=
    explicitCanonicalSourceMoment
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  let C :=
    oddCubicGeneratorResolventQuadratic
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  have hgamma :
      star Gamma * qC = qC - J := by
    simpa only [Gamma, qC, J] using
      (star_crossParitySecularGamma_mul_shellInner_eq_shellInner_sub_cubicShellCoupling
        c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg)
  have hbalance :
      qC - J = M4 - S * C := by
    simpa only [qC, J, M4, S, C] using
      c.evenShiftedCrossParitySourceBalance_of_even_of_source_ne_zero hp hS
  have hF :
      M4 - S * C = (c.retainedRealCompletedSourceScalar : ℂ) := by
    simpa [M4, S, C] using
      c.evenShiftedCompletedSource_eq_realScalar_of_even hp
  have hGamma :
      Gamma = (c.retainedRealCrossParityGamma : ℂ) := by
    simpa [Gamma] using c.retainedCrossParitySecularGamma_eq_realScalar
  have hGammaStar :
      star Gamma = (c.retainedRealCrossParityGamma : ℂ) := by
    rw [hGamma]
    simp
  have hq0 :
      inner ℂ shell shell = (c.retainedOddShellCenter : ℂ) := by
    simpa [shell,
      RegularCellMinimalNegativeEnergyCertificate.retainedOddShellCenter]
      using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) shell)
  have hq :
      qC = (c.retainedOddShellCenter : ℂ) := by
    simpa only [qC] using hq0
  have hcomplex :
      (c.retainedRealCrossParityGamma : ℂ) *
          (c.retainedOddShellCenter : ℂ) =
        (c.retainedRealCompletedSourceScalar : ℂ) := by
    calc
      (c.retainedRealCrossParityGamma : ℂ) *
          (c.retainedOddShellCenter : ℂ) =
        star Gamma * qC := by rw [← hGammaStar, ← hq]
      _ = qC - J := hgamma
      _ = M4 - S * C := hbalance
      _ = (c.retainedRealCompletedSourceScalar : ℂ) := hF
  have hre := congrArg Complex.re hcomplex
  simp at hre
  nlinarith

/-- Strict even ground separation gives the Gamma/source orientation without
assuming that the odd successor is good at zero. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealSource_mul_gamma_pos_of_evenGround_strict
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
    0 < c.retainedRealSourceScalar * c.retainedRealCrossParityGamma := by
  have hbelow :
      c.lam <
        parityRayleighBottom .odd c.firstBad.L
          (c.firstBad.Nstar + 1) := by
    rw [hground]
    exact hstrict
  have hpos :=
    cubicSecularScalar_shellPairing_pos_of_lt_parityBottom
      .odd c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg hbelow
  have htransfer :=
    c.oddSecularScalar_eq_gamma_mul_explicitSource_of_even hp
  have hGamma :=
    c.retainedCrossParitySecularGamma_eq_realScalar
  have hSource :=
    c.evenShiftedSourceMoment_eq_realScalar_of_even hp
  have hq :
      inner ℂ
          (intrinsicCubicShellPart .odd c.firstBad.Nstar :
            euclideanParityBoundaryFlatSubspace .odd
              (c.firstBad.Nstar + 1))
          (intrinsicCubicShellPart .odd c.firstBad.Nstar :
            euclideanParityBoundaryFlatSubspace .odd
              (c.firstBad.Nstar + 1)) =
        (c.retainedOddShellCenter : ℂ) := by
    let shell :=
      (intrinsicCubicShellPart .odd c.firstBad.Nstar :
        euclideanParityBoundaryFlatSubspace .odd
          (c.firstBad.Nstar + 1))
    simpa [shell,
      RegularCellMinimalNegativeEnergyCertificate.retainedOddShellCenter]
      using (inner_self_eq_norm_sq_to_K (𝕜 := ℂ) shell)
  rw [htransfer, hGamma, hSource, hq] at hpos
  have hqpos := c.retainedOddShellCenter_pos
  norm_num at hpos
  have hprodq :
      0 <
        (c.retainedRealSourceScalar * c.retainedRealCrossParityGamma) *
          c.retainedOddShellCenter := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hpos
  rcases (mul_pos_iff.mp hprodq) with hpp | hnn
  · exact hpp.1
  · exfalso
    linarith [hqpos, hnn.2]

/-- Compact strict-even ground package. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedGlobalBottomEvenStrictPackage
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
    let S := c.retainedRealSourceScalar
    let M4 := c.retainedRealMomentFour
    let Gamma := c.retainedRealCrossParityGamma
    0 < S * M4 ∧
    0 < S * Gamma ∧
    c.retainedRealCompletedSourceScalar =
      c.retainedOddShellCenter * Gamma := by
  have hSM4c :=
    c.retainedSourceMomentMomentFour_pos_of_evenGround_strict
      hp hground hstrict
  have hScomplex :=
    c.evenShiftedSourceMoment_eq_realScalar_of_even hp
  have hMcomplex :=
    c.evenShiftedMomentFour_eq_realScalar_of_even hp
  rw [hScomplex, hMcomplex] at hSM4c
  norm_num at hSM4c
  have hS :=
    c.retainedSourceMoment_ne_zero_of_evenGround_strict hp hground hstrict
  have hcompleted :=
    c.retainedRealCompletedSourceScalar_eq_shellCenter_mul_gamma_of_even_of_source_ne_zero
      hp hS
  exact ⟨hSM4c,
    c.retainedRealSource_mul_gamma_pos_of_evenGround_strict hp hground hstrict,
    hcompleted⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedSourceMomentMomentFour_pos_of_evenGround_strict
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedRealCompletedSourceScalar_eq_shellCenter_mul_gamma_of_even_of_source_ne_zero
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedRealSource_mul_gamma_pos_of_evenGround_strict
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedGlobalBottomEvenStrictPackage
