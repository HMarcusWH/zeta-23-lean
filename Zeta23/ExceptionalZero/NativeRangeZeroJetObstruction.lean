import Zeta23.ExceptionalZero.NativeZeroJetAnalyticFactors
import Zeta23.CCM.NativeCausalAnalyticObstruction

/-!
# The concrete multiplicity-aware causal witness for every off-line zero

The functional-equation involution is used before choosing positive
damping. The witness is the actual causal polynomial-exponential L2 vector
of degree m−1. Physical-transform identification remains necessary before
claiming that this witness annihilates the actual range and sees the input.
-/

noncomputable section

open Complex Set MeasureTheory
open scoped Topology

namespace Zeta23.ExceptionalZero

def nativeZeroJetRightZero (rho : zetaZeroConfig.carrier) : zetaZeroConfig.carrier :=
  if 1 / 2 < (rho : ℂ).re then rho else zetaOneSubEquiv rho

theorem nativeZeroJetRightZero_eq_or_oneSub (rho : zetaZeroConfig.carrier) :
    (nativeZeroJetRightZero rho : ℂ) = (rho : ℂ) ∨
      (nativeZeroJetRightZero rho : ℂ) = 1 - (rho : ℂ) := by
  unfold nativeZeroJetRightZero
  split_ifs <;> simp only [zetaOneSubEquiv_coe, or_true, true_or, eq_self]

theorem nativeZeroJetRightZero_re_gt_half (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    1 / 2 < (nativeZeroJetRightZero rho : ℂ).re := by
  unfold nativeZeroJetRightZero
  split_ifs with hright
  · exact hright
  · simp only [zetaOneSubEquiv_coe, Complex.sub_re, Complex.one_re]
    have hleft : (rho : ℂ).re < 1 / 2 := lt_of_le_of_ne (le_of_not_gt hright) hoff
    linarith

theorem nativeZeroJetRightZero_mult (rho : zetaZeroConfig.carrier) :
    zeroMult (nativeZeroJetRightZero rho : ℂ) = zeroMult (rho : ℂ) := by
  unfold nativeZeroJetRightZero
  split_ifs
  · rfl
  · exact zetaOneSubEquiv_mult rho

def nativeZeroJetDamping (rho : zetaZeroConfig.carrier) : ℝ :=
  ((nativeZeroJetRightZero rho : ℂ).re - 1 / 2) / 2

theorem nativeZeroJetDamping_pos (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) : 0 < nativeZeroJetDamping rho := by
  unfold nativeZeroJetDamping
  linarith [nativeZeroJetRightZero_re_gt_half rho hoff]

theorem nativeZeroJetDamping_lt_centered_re (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    nativeZeroJetDamping rho < (nativeZeroJetRightZero rho : ℂ).re - 1 / 2 := by
  unfold nativeZeroJetDamping
  linarith [nativeZeroJetRightZero_re_gt_half rho hoff]

def nativeZeroJetParameter (rho : zetaZeroConfig.carrier) : ℂ :=
  (nativeZeroJetRightZero rho : ℂ) - 1 / 2 - (nativeZeroJetDamping rho : ℂ)

theorem nativeZeroJetParameter_re_pos (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) : 0 < (nativeZeroJetParameter rho).re := by
  unfold nativeZeroJetParameter
  have hhalf : (1 / 2 : ℂ).re = (1 / 2 : ℝ) := by norm_num
  rw [Complex.sub_re, Complex.sub_re, Complex.ofReal_re, hhalf]
  exact sub_pos.mpr (nativeZeroJetDamping_lt_centered_re rho hoff)

theorem nativeZeroJetParameter_add_damping (rho : zetaZeroConfig.carrier) :
    nativeZeroJetParameter rho + (nativeZeroJetDamping rho : ℂ) =
      (nativeZeroJetRightZero rho : ℂ) - 1 / 2 := by
  unfold nativeZeroJetParameter
  ring

def nativeZeroJetAdjointWitness (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) : CCM.nativeCompletionCausalL2 :=
  CCM.nativeCausalExponentialWitness (nativeZeroJetParameter rho)
    (nativeZeroJetParameter_re_pos rho hoff) (zeroMult (rho : ℂ) - 1)

theorem nativeZeroJetAdjointWitness_ne_zero (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) : nativeZeroJetAdjointWitness rho hoff ≠ 0 :=
  CCM.nativeCausalExponentialWitness_ne_zero _ _ _

/-- The literal physical-input pairing retains every polynomial degree
and the exact damping shift at the selected actual right-side zero. -/
theorem nativeZeroJetAdjointWitness_inner_completedInput (rho : zetaZeroConfig.carrier)
    (hoff : (rho : ℂ).re ≠ 1 / 2) :
    inner ℂ (nativeZeroJetAdjointWitness rho hoff)
        (CCM.nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le) =
      ∫ t : ℝ, (t : ℂ) ^ (zeroMult (rho : ℂ) - 1) *
        Complex.exp (-((nativeZeroJetRightZero rho : ℂ) - 1 / 2) * (t : ℂ)) *
          (CCM.nativeCompletedInput t : ℂ) := by
  unfold nativeZeroJetAdjointWitness
  rw [CCM.nativeCausalExponentialWitness_inner_completedInput,
    nativeZeroJetParameter_add_damping]

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.nativeZeroJetRightZero_re_gt_half
#print axioms Zeta23.ExceptionalZero.nativeZeroJetRightZero_mult
#print axioms Zeta23.ExceptionalZero.nativeZeroJetDamping_pos
#print axioms Zeta23.ExceptionalZero.nativeZeroJetAdjointWitness_ne_zero
#print axioms Zeta23.ExceptionalZero.nativeZeroJetAdjointWitness_inner_completedInput
