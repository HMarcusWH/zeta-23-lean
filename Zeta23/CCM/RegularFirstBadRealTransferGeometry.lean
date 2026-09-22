import Zeta23.CCM.CrossParitySecularRealTransfer
import Zeta23.CCM.RegularFirstBadCompletedSourceRealGeometry
import Zeta23.CCM.RegularFirstBadCrossParitySourceBalance

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Retained real transfer geometry

The generic safe negative-shift transfer coefficients are real.  This module
specializes that result to the retained first-bad state and composes it with
the already-proved retained source balance and PR #237 real completed-source
corridor.

On the selected-even / odd-good branch the completed-source scalar becomes
exactly q*Gamma, the retained source scalar and Gamma have the same strict
orientation, and the sharp disk becomes

  q^2 * (1 - Gamma)^2 <= Rsharp.

No sign of Gamma itself, no sharp-radius/shell barrier, no branch exclusion,
negative-root exclusion, parity-complete closure, or RH claim is asserted.
-/

/-- Real coordinate of the retained safe cross-parity Gamma coefficient. -/
def
    RegularCellMinimalNegativeEnergyCertificate.retainedRealCrossParityGamma
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) : ℝ :=
  Complex.re
    (crossParitySecularGamma
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg)

/-- The retained complex Gamma coefficient is exactly its real scalar
coordinate. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedCrossParitySecularGamma_eq_realScalar
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    crossParitySecularGamma
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg =
      (c.retainedRealCrossParityGamma : ℂ) := by
  have him :=
    crossParitySecularGamma_im_eq_zero
      c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  apply Complex.ext
  · simp [RegularCellMinimalNegativeEnergyCertificate.retainedRealCrossParityGamma]
  · simpa [RegularCellMinimalNegativeEnergyCertificate.retainedRealCrossParityGamma]
      using him

/-- On the selected-even / odd-good retained state the real completed source is
exactly the positive shell center times the real transfer coefficient Gamma. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealCompletedSourceScalar_eq_shellCenter_mul_gamma_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
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
      c.evenShiftedCrossParitySourceBalance_of_even_of_not_oddBad hp hodd
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
  have hq :
      qC = (c.retainedOddShellCenter : ℂ) := by
    change inner ℂ shell shell = ((‖shell‖ ^ 2 : ℝ) : ℂ)
    calc
      inner ℂ shell shell = (‖shell‖ : ℂ) ^ 2 :=
        inner_self_eq_norm_sq_to_K (𝕜 := ℂ) shell
      _ = ((‖shell‖ ^ 2 : ℝ) : ℂ) := by norm_num
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

/-- The retained source scalar and retained Gamma have strictly positive
product on the selected-even / odd-good branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealSource_mul_gamma_pos_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    0 < c.retainedRealSourceScalar * c.retainedRealCrossParityGamma := by
  have hbudget :=
    c.retainedCompletedSourceBudget_real_of_even_of_not_oddBad hp hodd
  have hB := c.retainedOddShiftBudget_pos
  have hq := c.retainedOddShellCenter_pos
  have hf :=
    c.retainedRealCompletedSourceScalar_eq_shellCenter_mul_gamma_of_even_of_not_oddBad
      hp hodd
  rw [hf] at hbudget
  have hprod :
      0 <
        c.retainedOddShellCenter *
          (c.retainedRealSourceScalar * c.retainedRealCrossParityGamma) := by
    have hsf :
        0 <
          c.retainedRealSourceScalar *
            (c.retainedOddShellCenter * c.retainedRealCrossParityGamma) :=
      lt_of_lt_of_le hB hbudget
    simpa [mul_assoc, mul_left_comm, mul_comm] using hsf
  rcases (mul_pos_iff.mp hprod) with hpos | hneg
  · exact hpos.2
  · exfalso
    linarith

/-- On the retained selected-even / odd-good branch, source positivity is
exactly Gamma positivity. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealSourceScalar_pos_iff_gamma_pos_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    0 < c.retainedRealSourceScalar ↔
      0 < c.retainedRealCrossParityGamma := by
  have hprod :=
    c.retainedRealSource_mul_gamma_pos_of_even_of_not_oddBad hp hodd
  constructor <;> intro h
  · rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · exact hpos.2
    · linarith
  · rcases (mul_pos_iff.mp hprod) with hpos | hneg
    · exact hpos.1
    · linarith

/-- The retained sharp Gram disk in the real Gamma coordinate. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedGammaSharpDisk_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    c.retainedOddShellCenter ^ 2 *
        (1 - c.retainedRealCrossParityGamma) ^ 2 ≤
      c.retainedSourceKernelSharpRadiusSq := by
  have h :=
    c.retainedCompletedSourceSharpDisk_real_of_even_of_not_oddBad hp hodd
  have hf :=
    c.retainedRealCompletedSourceScalar_eq_shellCenter_mul_gamma_of_even_of_not_oddBad
      hp hodd
  rw [hf] at h
  calc
    c.retainedOddShellCenter ^ 2 *
        (1 - c.retainedRealCrossParityGamma) ^ 2 =
      (c.retainedOddShellCenter -
        c.retainedOddShellCenter * c.retainedRealCrossParityGamma) ^ 2 := by
          ring
    _ ≤ c.retainedSourceKernelSharpRadiusSq := h

/-- Compact retained real transfer corridor. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealTransferCorridor_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    0 < c.retainedOddShellCenter ∧
    c.retainedRealCompletedSourceScalar =
      c.retainedOddShellCenter * c.retainedRealCrossParityGamma ∧
    0 < c.retainedRealSourceScalar * c.retainedRealCrossParityGamma ∧
    c.retainedOddShellCenter ^ 2 *
        (1 - c.retainedRealCrossParityGamma) ^ 2 ≤
      c.retainedSourceKernelSharpRadiusSq := by
  exact ⟨
    c.retainedOddShellCenter_pos,
    c.retainedRealCompletedSourceScalar_eq_shellCenter_mul_gamma_of_even_of_not_oddBad
      hp hodd,
    c.retainedRealSource_mul_gamma_pos_of_even_of_not_oddBad hp hodd,
    c.retainedGammaSharpDisk_of_even_of_not_oddBad hp hodd
  ⟩

/-- The existing sharp-radius/shell barrier is a sufficient route to positive
retained Gamma.  The barrier premise itself is not proved here. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealCrossParityGamma_pos_of_sharpRadius_le_shellCenter_sq
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (hbarrier :
      c.retainedSourceKernelSharpRadiusSq ≤
        c.retainedOddShellCenter ^ 2) :
    0 < c.retainedRealCrossParityGamma := by
  have hs :=
    c.retainedRealSourceScalar_pos_of_sharpRadius_le_shellCenter_sq
      hp hodd hbarrier
  exact
    (c.retainedRealSourceScalar_pos_iff_gamma_pos_of_even_of_not_oddBad
      hp hodd).mp hs

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedCrossParitySecularGamma_eq_realScalar
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedRealCompletedSourceScalar_eq_shellCenter_mul_gamma_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedRealSource_mul_gamma_pos_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedRealSourceScalar_pos_iff_gamma_pos_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedGammaSharpDisk_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedRealTransferCorridor_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedRealCrossParityGamma_pos_of_sharpRadius_le_shellCenter_sq
