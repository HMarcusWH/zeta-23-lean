import Zeta23.CCM.CrossParityCorrectionFunctionalCollapse
import Zeta23.CCM.CrossParitySecularTransferCore

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: safe secular one-coefficient collapse

The PR #226 predecessor identity propagates through the existing safe odd
predecessor resolvent functional. Thus the negative-shift cross-parity
coefficients alpha and Gamma are affine-dependent, and the exact secular
transfer has only one free transfer coefficient.

No zero-shift limit is taken here. No sign of alpha, Gamma, the defect, or any
source moment is asserted.
-/

/-- Exact affine dependence of the safe negative-shift transfer coefficients. -/
theorem crossParitySecularGamma_eq_one_add_kappa_mul_one_sub_alpha
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    crossParitySecularGamma hL N hprevOdd lam hlam =
      1 + crossParityCubicCorrectionKappa N *
        (1 - crossParitySecularAlpha hL N hprevOdd lam hlam) := by
  unfold crossParitySecularGamma crossParitySecularAlpha
  have hcorr :=
    map_oddCubicGeneratorPredecessorPart_eq_neg_kappa_smul
      N hN (oddSafeSecularCorrectionFunctional hL N hprevOdd lam hlam)
  simp only [smul_eq_mul] at hcorr
  rw [hcorr]
  ring

/-- Integer-coefficient form of the safe alpha/Gamma relation. -/
theorem six_mul_crossParitySecularGamma_add_index_mul_alpha
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    (6 : ℂ) * crossParitySecularGamma hL N hprevOdd lam hlam +
        (2 * (N : ℂ) - 1) *
          crossParitySecularAlpha hL N hprevOdd lam hlam =
      2 * (N : ℂ) + 5 := by
  rw [crossParitySecularGamma_eq_one_add_kappa_mul_one_sub_alpha
    hL N hN hprevOdd lam hlam]
  unfold crossParityCubicCorrectionKappa
  field_simp
  ring

/-- Safe cross-parity secular transfer with Gamma eliminated. -/
theorem cubicSecularScalar_odd_eq_oneCoefficient_crossParity
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicSecularScalar .odd hL N hprevOdd lam hlam =
      (1 + crossParityCubicCorrectionKappa N) *
          evenParityCubicDefectFunctional L (N + 1)
            (cubicSecularTrialVector .even hL N hprevEven lam hlam) +
        crossParitySecularAlpha hL N hprevOdd lam hlam *
          (cubicSecularScalar .even hL N hprevEven lam hlam -
            crossParityCubicCorrectionKappa N *
              evenParityCubicDefectFunctional L (N + 1)
                (cubicSecularTrialVector .even hL N hprevEven lam hlam)) := by
  rw [cubicSecularScalar_odd_eq_alpha_mul_even_add_gamma_mul_defect
    hL N hN hprevEven hprevOdd lam hlam]
  rw [crossParitySecularGamma_eq_one_add_kappa_mul_one_sub_alpha
    hL N hN hprevOdd lam hlam]
  ring

/-- Denominator-free safe one-coefficient transfer. -/
theorem six_mul_cubicSecularScalar_odd_eq_oneCoefficient_crossParity
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprevEven :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hprevOdd :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .odd N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    (6 : ℂ) * cubicSecularScalar .odd hL N hprevOdd lam hlam =
      crossParitySecularAlpha hL N hprevOdd lam hlam *
          ((6 : ℂ) * cubicSecularScalar .even hL N hprevEven lam hlam -
            (2 * (N : ℂ) - 1) *
              evenParityCubicDefectFunctional L (N + 1)
                (cubicSecularTrialVector .even hL N hprevEven lam hlam)) +
        (2 * (N : ℂ) + 5) *
          evenParityCubicDefectFunctional L (N + 1)
            (cubicSecularTrialVector .even hL N hprevEven lam hlam) := by
  rw [cubicSecularScalar_odd_eq_alpha_mul_even_add_gamma_mul_defect
    hL N hN hprevEven hprevOdd lam hlam]
  have hcoeff :=
    six_mul_crossParitySecularGamma_add_index_mul_alpha
      hL N hN hprevOdd lam hlam
  linear_combination
    evenParityCubicDefectFunctional L (N + 1)
      (cubicSecularTrialVector .even hL N hprevEven lam hlam) * hcoeff

end Zeta23.CCM

#print axioms Zeta23.CCM.crossParitySecularGamma_eq_one_add_kappa_mul_one_sub_alpha
#print axioms Zeta23.CCM.six_mul_crossParitySecularGamma_add_index_mul_alpha
#print axioms Zeta23.CCM.cubicSecularScalar_odd_eq_oneCoefficient_crossParity
#print axioms Zeta23.CCM.six_mul_cubicSecularScalar_odd_eq_oneCoefficient_crossParity
