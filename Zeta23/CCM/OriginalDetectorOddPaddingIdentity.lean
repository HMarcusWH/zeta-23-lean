import Zeta23.CCM.FinitePhysicalNormalization
import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNativeProducer
import Zeta23.CCM.OriginalDetectorFinitePhaseNativeProducer
import Zeta23.CCM.OriginalDetectorPaddedFinitePositivity

/-! Exact transport of odd primitive padding cancellation through P and normalization. -/

noncomputable section

open Set Complex
open scoped Topology

namespace Zeta23.CCM

private theorem poleKilled_reflected_difference {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (L : ℝ) :
    Zeta23.ExceptionalZero.poleKilled (fun x => f x - f (L - x)) =
      fun x => Zeta23.ExceptionalZero.poleKilled f x - Zeta23.ExceptionalZero.poleKilled f (L - x) := by
  have hf2 : ContDiff ℝ 2 f :=
    hf.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hr2 : ContDiff ℝ 2 (fun x : ℝ => f (L - x)) :=
    hf2.comp (contDiff_const.sub contDiff_id)
  funext x
  have he : iteratedDeriv 2 (fun y : ℝ => f y - f (L - y)) x =
      iteratedDeriv 2 f x - iteratedDeriv 2 f (L - x) := by
    rw [iteratedDeriv_fun_sub hf2.contDiffAt hr2.contDiffAt, iteratedDeriv_comp_const_sub]
    norm_num
  simp only [iteratedDeriv_succ, iteratedDeriv_zero] at he
  unfold Zeta23.ExceptionalZero.poleKilled
  rw [he]
  ring

private theorem finiteFunction_injective {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u v : Fin (2 * K + 1) → ℂ)
    (h : localizedFiniteFunction L K u = localizedFiniteFunction L K v) : u = v := by
  let w : EuclideanSpace ℂ (Fin (2 * K + 1)) := WithLp.toLp 2 (u - v)
  have hw : localizedFiniteFunction L K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) w) = 0 := by
    funext x
    change (∑ i, (u i - v i) * localizedMode L (centeredIndex K i) x) = 0
    simp only [sub_mul, Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (congrFun h x)
  have he := localizedFiniteFunction_energy_eq_norm_sq hL K w
  rw [hw] at he
  simp only [Pi.zero_apply, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), intervalIntegral.integral_zero] at he
  have hw0 : w = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp he.symm)
  funext i
  have hi := congrArg (fun z : EuclideanSpace ℂ (Fin (2 * K + 1)) => z i) hw0
  exact sub_eq_zero.mp hi

theorem originalDetectorOddPadding_P_image_eq (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    (fun x => Zeta23.ExceptionalZero.poleKilled
      (originalDetectorPaddedFiniteWindowImage UniversalSinc.fixedScale L c (by linarith)) x -
      Zeta23.ExceptionalZero.poleKilled
        (originalDetectorPaddedFiniteWindowImage UniversalSinc.fixedScale L c (by linarith)) (L - x)) =
    (fun x => Zeta23.ExceptionalZero.poleKilled
      (originalDetectorFiniteWindowImage UniversalSinc.fixedScale L c (by linarith)) x -
      Zeta23.ExceptionalZero.poleKilled
        (originalDetectorFiniteWindowImage UniversalSinc.fixedScale L c (by linarith)) (L - x)) := by
  have hp : ContDiff ℝ (⊤ : ℕ∞)
      (originalDetectorPaddedFiniteWindowImage UniversalSinc.fixedScale L c (by linarith)) :=
    (originalDetectorPaddedFiniteWindow_contDiff L).mul
      (originalDetectorPaddedRawFourierPartialSum_contDiff _ _ _ _)
  have hu : ContDiff ℝ (⊤ : ℕ∞)
      (originalDetectorFiniteWindowImage UniversalSinc.fixedScale L c (by linarith)) :=
    (originalDetectorFiniteWindow_contDiff L).mul
      (originalDetectorDividedLobeFourierPartialSum_contDiff _ _ _ _)
  have hprim :
      (fun x => originalDetectorPaddedFiniteWindowImage UniversalSinc.fixedScale L c (by linarith) x -
        originalDetectorPaddedFiniteWindowImage UniversalSinc.fixedScale L c (by linarith) (L - x)) =
      (fun x => originalDetectorFiniteWindowImage UniversalSinc.fixedScale L c (by linarith) x -
        originalDetectorFiniteWindowImage UniversalSinc.fixedScale L c (by linarith) (L - x)) := by
    funext x
    simpa only [originalDetectorPaddedFinitePhasePrimitive, Complex.ofReal_neg, Complex.ofReal_one,
      neg_one_mul, sub_eq_add_neg] using
      originalDetectorPaddedFiniteOddPrimitive_padding_cancels UniversalSinc.fixedScale L c (by linarith) x
  have he := congrArg Zeta23.ExceptionalZero.poleKilled hprim
  rw [poleKilled_reflected_difference hp, poleKilled_reflected_difference hu] at he
  exact he

theorem originalDetectorOddPadding_coefficients_eq (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    originalDetectorPaddedFinitePhaseVector (-1) L c (by linarith) =
      originalDetectorFinitePhaseVector (-1) L c (by linarith) := by
  apply (EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ).injective
  apply finiteFunction_injective (by linarith) (originalDetectorQuarticCutoff L)
  funext x
  rw [originalDetectorPaddedFinitePhaseVector_physical_formula,
    originalDetectorFinitePhaseVector_physical_formula,
    localizedFiniteFunction_originalDetectorPaddedFinitePoleImageCoefficients UniversalSinc.fixedScale c hL,
    localizedFiniteFunction_originalDetectorFinitePoleImageCoefficients UniversalSinc.fixedScale c hL]
  simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_one_mul, sub_eq_add_neg] using
    congrFun (originalDetectorOddPadding_P_image_eq c hL) x

theorem originalDetectorOddPadding_mass_eq (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ‖originalDetectorPaddedFinitePhaseVector (-1) L c (by linarith)‖ ^ 2 =
      ‖originalDetectorFinitePhaseVector (-1) L c (by linarith)‖ ^ 2 :=
  congrArg (fun v => ‖v‖ ^ 2) (originalDetectorOddPadding_coefficients_eq c hL)

theorem originalDetectorOddPadding_unitVector_eq (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    originalDetectorPaddedFinitePhaseUnitVector (-1) L c (by linarith) =
      originalDetectorFinitePhaseUnitVector (-1) L c (by linarith) := by
  unfold originalDetectorPaddedFinitePhaseUnitVector originalDetectorFinitePhaseUnitVector
  rw [originalDetectorOddPadding_coefficients_eq c hL]

theorem originalDetectorOddPadding_normalizedPhysical_eq (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    finitePhysicalSynthesis L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFinitePhaseUnitVector (-1) L c (by linarith)) =
    finitePhysicalSynthesis L (originalDetectorQuarticCutoff L)
      (originalDetectorFinitePhaseUnitVector (-1) L c (by linarith)) := by
  rw [originalDetectorOddPadding_unitVector_eq c hL]

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorOddPadding_P_image_eq
#print axioms Zeta23.CCM.originalDetectorOddPadding_coefficients_eq
#print axioms Zeta23.CCM.originalDetectorOddPadding_mass_eq
#print axioms Zeta23.CCM.originalDetectorOddPadding_unitVector_eq
#print axioms Zeta23.CCM.originalDetectorOddPadding_normalizedPhysical_eq
