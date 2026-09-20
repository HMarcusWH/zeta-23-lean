import Zeta23.CCM.CrossParityCorrectionFunctionalCollapse
import Zeta23.CCM.ZeroShiftCrossParityTransfer

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: zero-shift one-coefficient collapse

The PR #226 predecessor identity is inserted directly into the selected
zero-shift overlap coefficients. Since the predecessor correction occupies the
second inner-product slot, the exact complex scalar is transported linearly,
without conjugation.

The resulting direct zero-shift transfer has one free transfer coefficient.
No sign, nonzeroness, branch exclusion, or RH claim is made here.
-/

/-- Exact affine dependence of the selected zero-shift transfer coefficients. -/
theorem crossParityZeroShiftGamma_eq_one_add_kappa_mul_one_sub_alpha
    (N : ℕ) (hN : 1 ≤ N)
    (xMinus : intrinsicParityPredecessorSubspace .odd N) :
    crossParityZeroShiftGamma N xMinus =
      1 + crossParityCubicCorrectionKappa N *
        (1 - crossParityZeroShiftAlpha N xMinus) := by
  have hcorr :=
    oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul N hN
  have hinner := congrArg
    (fun y : intrinsicParityPredecessorSubspace .odd N =>
      inner ℂ
        (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
        (y : euclideanParityBoundaryFlatSubspace .odd (N + 1)))
    hcorr
  have hinner' :
      inner ℂ
          (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((oddCubicGeneratorPredecessorPart N :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        -(crossParityCubicCorrectionKappa N) *
          inner ℂ
            (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
            ((oddIndexCubicShellPredecessorPart N :
                intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
    calc
      inner ℂ
          (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          ((oddCubicGeneratorPredecessorPart N :
              intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) =
        inner ℂ
          (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (((-(crossParityCubicCorrectionKappa N)) •
              oddIndexCubicShellPredecessorPart N :
                intrinsicParityPredecessorSubspace .odd N) :
            euclideanParityBoundaryFlatSubspace .odd (N + 1)) := hinner
      _ = inner ℂ
          (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
          (-(crossParityCubicCorrectionKappa N) •
            ((oddIndexCubicShellPredecessorPart N :
                intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1))) := by
            rfl
      _ = -(crossParityCubicCorrectionKappa N) *
          inner ℂ
            (xMinus : euclideanParityBoundaryFlatSubspace .odd (N + 1))
            ((oddIndexCubicShellPredecessorPart N :
                intrinsicParityPredecessorSubspace .odd N) :
              euclideanParityBoundaryFlatSubspace .odd (N + 1)) := by
            exact inner_smul_right _ _ _
  unfold crossParityZeroShiftGamma crossParityZeroShiftAlpha
  rw [hinner']
  ring

/-- Integer-coefficient form of the selected zero-shift alpha/Gamma relation. -/
theorem six_mul_crossParityZeroShiftGamma_add_index_mul_alpha
    (N : ℕ) (hN : 1 ≤ N)
    (xMinus : intrinsicParityPredecessorSubspace .odd N) :
    (6 : ℂ) * crossParityZeroShiftGamma N xMinus +
        (2 * (N : ℂ) - 1) * crossParityZeroShiftAlpha N xMinus =
      2 * (N : ℂ) + 5 := by
  rw [crossParityZeroShiftGamma_eq_one_add_kappa_mul_one_sub_alpha
    N hN xMinus]
  unfold crossParityCubicCorrectionKappa
  ring

/-- Direct zero-shift cross-parity transfer with Gamma eliminated. -/
theorem cubicZeroShiftShellResponseScalar_crossParity_oneCoefficient
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (xPlus : intrinsicParityPredecessorSubspace .even N)
    (hxPlus : intrinsicPredecessorBlock .even L N xPlus =
      intrinsicShellToPredecessor .even L N
        (intrinsicCubicShellPart .even N))
    (xMinus : intrinsicParityPredecessorSubspace .odd N)
    (hxMinus : intrinsicPredecessorBlock .odd L N xMinus =
      intrinsicShellToPredecessor .odd L N
        (intrinsicCubicShellPart .odd N)) :
    cubicZeroShiftShellResponseScalar .odd L N xMinus =
      (1 + crossParityCubicCorrectionKappa N) *
          explicitCanonicalSourceMoment L (N + 1)
            (cubicZeroShiftTrialVector .even L N xPlus) +
        crossParityZeroShiftAlpha N xMinus *
          (cubicZeroShiftShellResponseScalar .even L N xPlus -
            crossParityCubicCorrectionKappa N *
              explicitCanonicalSourceMoment L (N + 1)
                (cubicZeroShiftTrialVector .even L N xPlus)) := by
  rw [cubicZeroShiftShellResponseScalar_crossParity_explicitSource_transfer
    hL N hN xPlus hxPlus xMinus hxMinus]
  rw [crossParityZeroShiftGamma_eq_one_add_kappa_mul_one_sub_alpha
    N hN xMinus]
  ring

/-- Denominator-free direct zero-shift one-coefficient transfer. -/
theorem six_mul_cubicZeroShiftShellResponseScalar_crossParity_oneCoefficient
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (xPlus : intrinsicParityPredecessorSubspace .even N)
    (hxPlus : intrinsicPredecessorBlock .even L N xPlus =
      intrinsicShellToPredecessor .even L N
        (intrinsicCubicShellPart .even N))
    (xMinus : intrinsicParityPredecessorSubspace .odd N)
    (hxMinus : intrinsicPredecessorBlock .odd L N xMinus =
      intrinsicShellToPredecessor .odd L N
        (intrinsicCubicShellPart .odd N)) :
    (6 : ℂ) * cubicZeroShiftShellResponseScalar .odd L N xMinus =
      crossParityZeroShiftAlpha N xMinus *
          ((6 : ℂ) * cubicZeroShiftShellResponseScalar .even L N xPlus -
            (2 * (N : ℂ) - 1) *
              explicitCanonicalSourceMoment L (N + 1)
                (cubicZeroShiftTrialVector .even L N xPlus)) +
        (2 * (N : ℂ) + 5) *
          explicitCanonicalSourceMoment L (N + 1)
            (cubicZeroShiftTrialVector .even L N xPlus) := by
  rw [cubicZeroShiftShellResponseScalar_crossParity_explicitSource_transfer
    hL N hN xPlus hxPlus xMinus hxMinus]
  have hcoeff :=
    six_mul_crossParityZeroShiftGamma_add_index_mul_alpha N hN xMinus
  linear_combination
    explicitCanonicalSourceMoment L (N + 1)
      (cubicZeroShiftTrialVector .even L N xPlus) * hcoeff

end Zeta23.CCM

#print axioms Zeta23.CCM.crossParityZeroShiftGamma_eq_one_add_kappa_mul_one_sub_alpha
#print axioms Zeta23.CCM.six_mul_crossParityZeroShiftGamma_add_index_mul_alpha
#print axioms Zeta23.CCM.cubicZeroShiftShellResponseScalar_crossParity_oneCoefficient
#print axioms Zeta23.CCM.six_mul_cubicZeroShiftShellResponseScalar_crossParity_oneCoefficient
