import Zeta23.CCM.RegularFirstBadRealTransferGeometry
import Zeta23.CCM.RegularFirstBadSourceKernelRealPhase

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Retained Gamma obstruction normal form

PR #239 proves that the canonical safe negative-shift transfer coefficients are
real and that the retained selected-even / odd-good state satisfies

  f = q * Gamma,
  s * Gamma > 0,
  q^2 * (1 - Gamma)^2 <= Rsharp.

This module turns those facts into an explicit obstruction normal form.

The main consequences are:

* the retained center deficit is exactly `D = B - q*s`;
* the real transfer coefficients satisfy
  `6*Gamma + (2*N-1)*Alpha = 2*N+5`;
* `Gamma > 1` is equivalent to `Alpha < 1`;
* `Gamma < 0` forces the strict radius escape `q^2 < Rsharp`;
* `0 < Gamma <= 1` forces `D <= 0`;
* therefore a positive center deficit can survive only through one of two
  transfer escapes:
    - `Gamma < 0` together with `q^2 < Rsharp`, or
    - `Gamma > 1`, equivalently `Alpha < 1`.

No sign of Gamma or Alpha is proved unconditionally.  No radius barrier,
branch exclusion, negative-root exclusion, parity-complete closure, or RH
claim is asserted.
-/

/-- Exact real-coordinate form of the retained center deficit. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernelCenterDeficit_eq_realTransferCoordinates
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    c.retainedSourceKernelCenterDeficit =
      c.retainedOddShiftBudget -
        c.retainedOddShellCenter * c.retainedRealSourceScalar := by
  rfl

/-- Real coordinate of the retained safe cross-parity Alpha coefficient. -/
def
    RegularCellMinimalNegativeEnergyCertificate.retainedRealCrossParityAlpha
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) : ℝ :=
  Complex.re
    (crossParitySecularAlpha
      c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg)

/-- The retained complex Alpha coefficient is exactly its real scalar
coordinate. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedCrossParitySecularAlpha_eq_realScalar
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    crossParitySecularAlpha
        c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg =
      (c.retainedRealCrossParityAlpha : ℂ) := by
  have him :=
    crossParitySecularAlpha_im_eq_zero
      c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  apply Complex.ext
  · simp [RegularCellMinimalNegativeEnergyCertificate.retainedRealCrossParityAlpha]
  · simpa [RegularCellMinimalNegativeEnergyCertificate.retainedRealCrossParityAlpha]
      using him

/-- Retained real one-coefficient transfer relation. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealAlphaGammaAffine
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    (6 : ℝ) * c.retainedRealCrossParityGamma +
        (2 * (c.firstBad.Nstar : ℝ) - 1) *
          c.retainedRealCrossParityAlpha =
      2 * (c.firstBad.Nstar : ℝ) + 5 := by
  have h :=
    six_mul_crossParitySecularGamma_add_index_mul_alpha
      c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  rw [c.retainedCrossParitySecularGamma_eq_realScalar,
    c.retainedCrossParitySecularAlpha_eq_realScalar] at h
  have hre := congrArg Complex.re h
  norm_num at hre
  simpa using hre

/-- The high-Gamma branch is exactly the low-Alpha branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedGamma_gt_one_iff_alpha_lt_one
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    1 < c.retainedRealCrossParityGamma ↔
      c.retainedRealCrossParityAlpha < 1 := by
  have hlin := c.retainedRealAlphaGammaAffine
  have hN :
      (1 : ℝ) ≤ (c.firstBad.Nstar : ℝ) := by
    exact_mod_cast c.firstBad.one_le_Nstar
  have hcoeff :
      0 < 2 * (c.firstBad.Nstar : ℝ) - 1 := by
    linarith
  constructor <;> intro h <;> nlinarith

/-- A negative retained Gamma cannot remain inside the shell-radius barrier:
the sharp radius must strictly exceed the shell-center square. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedGamma_neg_implies_shellCenter_sq_lt_sharpRadius
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (hGamma :
      c.retainedRealCrossParityGamma < 0) :
    c.retainedOddShellCenter ^ 2 <
      c.retainedSourceKernelSharpRadiusSq := by
  have hdisk :=
    c.retainedGammaSharpDisk_of_even_of_not_oddBad hp hodd
  have hq := c.retainedOddShellCenter_pos
  have hq2 : 0 < c.retainedOddShellCenter ^ 2 :=
    sq_pos_of_pos hq
  have hfactor :
      0 <
        (1 - c.retainedRealCrossParityGamma) ^ 2 - 1 := by
    nlinarith [sq_nonneg c.retainedRealCrossParityGamma]
  have hstrict :
      c.retainedOddShellCenter ^ 2 <
        c.retainedOddShellCenter ^ 2 *
          (1 - c.retainedRealCrossParityGamma) ^ 2 := by
    have hmul := mul_pos hq2 hfactor
    nlinarith
  exact lt_of_lt_of_le hstrict hdisk

/-- The completed-source budget bounds the exact center deficit by the
source-scaled Gamma displacement from the shell center. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedCenterDeficit_le_source_shell_gammaGap
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    c.retainedSourceKernelCenterDeficit ≤
      c.retainedRealSourceScalar * c.retainedOddShellCenter *
        (c.retainedRealCrossParityGamma - 1) := by
  have h :=
    c.retainedSourceKernelCenterDeficit_le_source_mul_completedOffset
      hp hodd
  have hf :=
    c.retainedRealCompletedSourceScalar_eq_shellCenter_mul_gamma_of_even_of_not_oddBad
      hp hodd
  calc
    c.retainedSourceKernelCenterDeficit ≤
        c.retainedRealSourceScalar *
          (c.retainedRealCompletedSourceScalar -
            c.retainedOddShellCenter) := h
    _ =
        c.retainedRealSourceScalar * c.retainedOddShellCenter *
          (c.retainedRealCrossParityGamma - 1) := by
      rw [hf]
      ring

/-- The positive unit interval for Gamma is a nonpositive-center-deficit
regime. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedCenterDeficit_nonpos_of_gamma_pos_of_gamma_le_one
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (hGammaPos :
      0 < c.retainedRealCrossParityGamma)
    (hGammaLe :
      c.retainedRealCrossParityGamma ≤ 1) :
    c.retainedSourceKernelCenterDeficit ≤ 0 := by
  have hbound :=
    c.retainedCenterDeficit_le_source_shell_gammaGap hp hodd
  have hs :
      0 < c.retainedRealSourceScalar :=
    (c.retainedRealSourceScalar_pos_iff_gamma_pos_of_even_of_not_oddBad
      hp hodd).2 hGammaPos
  have hq := c.retainedOddShellCenter_pos
  have hsq :
      0 ≤ c.retainedRealSourceScalar * c.retainedOddShellCenter :=
    mul_nonneg (le_of_lt hs) (le_of_lt hq)
  have hgap :
      c.retainedRealCrossParityGamma - 1 ≤ 0 :=
    sub_nonpos.mpr hGammaLe
  have hrhs :
      c.retainedRealSourceScalar * c.retainedOddShellCenter *
          (c.retainedRealCrossParityGamma - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hsq hgap
  exact le_trans hbound hrhs

/-- A negative Gamma forces the entire retained real source/completed-source
orientation negative, together with the strict sharp-radius escape. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedGamma_negative_regime
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (hGamma :
      c.retainedRealCrossParityGamma < 0) :
    c.retainedRealSourceScalar < 0 ∧
    c.retainedRealCompletedSourceScalar < 0 ∧
    c.retainedRealMomentFour < 0 ∧
    c.retainedOddShellCenter ^ 2 <
      c.retainedSourceKernelSharpRadiusSq := by
  have hsg :=
    c.retainedRealSource_mul_gamma_pos_of_even_of_not_oddBad hp hodd
  have hs : c.retainedRealSourceScalar < 0 := by
    rcases (mul_pos_iff.mp hsg) with hpos | hneg
    · linarith
    · exact hneg.1
  have hf :=
    c.retainedRealCompletedSourceScalar_eq_shellCenter_mul_gamma_of_even_of_not_oddBad
      hp hodd
  have hq := c.retainedOddShellCenter_pos
  have hfneg : c.retainedRealCompletedSourceScalar < 0 := by
    rw [hf]
    exact mul_neg_of_pos_of_neg hq hGamma
  have hsm :=
    c.retainedRealSource_mul_momentFour_pos_of_even_of_not_oddBad hp hodd
  have hm : c.retainedRealMomentFour < 0 := by
    rcases (mul_pos_iff.mp hsm) with hpos | hneg
    · linarith
    · exact hneg.2
  exact ⟨
    hs,
    hfneg,
    hm,
    c.retainedGamma_neg_implies_shellCenter_sq_lt_sharpRadius hp hodd hGamma
  ⟩

/-- In the high-Gamma branch, the source and fourth moment are positive, the
completed source lies strictly beyond the shell center, and Alpha is below one. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedGamma_gt_one_regime
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (hGamma :
      1 < c.retainedRealCrossParityGamma) :
    0 < c.retainedRealSourceScalar ∧
    c.retainedOddShellCenter < c.retainedRealCompletedSourceScalar ∧
    0 < c.retainedRealMomentFour ∧
    c.retainedRealCrossParityAlpha < 1 := by
  have hGammaPos : 0 < c.retainedRealCrossParityGamma := lt_trans zero_lt_one hGamma
  have hs :
      0 < c.retainedRealSourceScalar :=
    (c.retainedRealSourceScalar_pos_iff_gamma_pos_of_even_of_not_oddBad
      hp hodd).2 hGammaPos
  have hf :=
    c.retainedRealCompletedSourceScalar_eq_shellCenter_mul_gamma_of_even_of_not_oddBad
      hp hodd
  have hq := c.retainedOddShellCenter_pos
  have hqf :
      c.retainedOddShellCenter < c.retainedRealCompletedSourceScalar := by
    rw [hf]
    nlinarith
  have hsm :=
    c.retainedRealSource_mul_momentFour_pos_of_even_of_not_oddBad hp hodd
  have hm : 0 < c.retainedRealMomentFour := by
    rcases (mul_pos_iff.mp hsm) with hpos | hneg
    · exact hpos.2
    · linarith
  have ha :
      c.retainedRealCrossParityAlpha < 1 :=
    c.retainedGamma_gt_one_iff_alpha_lt_one.mp hGamma
  exact ⟨hs, hqf, hm, ha⟩

/-- Flagship transfer-obstruction dichotomy for the positive-deficit branch.

If the exact retained center deficit is positive while the odd successor is
still good, then Gamma must escape the closed unit interval in one of two
qualitatively different ways:

* negative Gamma, which already forces `q^2 < Rsharp`; or
* Gamma greater than one, equivalently Alpha less than one.

This does not prove that the center deficit is positive. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedPositiveCenterDeficit_transferEscape
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1))
    (hD :
      0 < c.retainedSourceKernelCenterDeficit) :
    (c.retainedRealCrossParityGamma < 0 ∧
      c.retainedOddShellCenter ^ 2 <
        c.retainedSourceKernelSharpRadiusSq) ∨
    (1 < c.retainedRealCrossParityGamma ∧
      c.retainedRealCrossParityAlpha < 1) := by
  rcases lt_trichotomy c.retainedRealCrossParityGamma 0 with
      hGammaNeg | hGammaZero | hGammaPos
  · exact Or.inl ⟨
      hGammaNeg,
      c.retainedGamma_neg_implies_shellCenter_sq_lt_sharpRadius
        hp hodd hGammaNeg
    ⟩
  · have hprod :=
      c.retainedRealSource_mul_gamma_pos_of_even_of_not_oddBad hp hodd
    rw [hGammaZero, mul_zero] at hprod
    linarith
  · by_cases hGammaHigh : 1 < c.retainedRealCrossParityGamma
    · exact Or.inr ⟨
        hGammaHigh,
        c.retainedGamma_gt_one_iff_alpha_lt_one.mp hGammaHigh
      ⟩
    · have hGammaLe :
          c.retainedRealCrossParityGamma ≤ 1 :=
        le_of_not_gt hGammaHigh
      have hDle :=
        c.retainedCenterDeficit_nonpos_of_gamma_pos_of_gamma_le_one
          hp hodd hGammaPos hGammaLe
      linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedRealAlphaGammaAffine
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedGamma_gt_one_iff_alpha_lt_one
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedGamma_neg_implies_shellCenter_sq_lt_sharpRadius
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedCenterDeficit_nonpos_of_gamma_pos_of_gamma_le_one
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedGamma_negative_regime
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedGamma_gt_one_regime
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedPositiveCenterDeficit_transferEscape
