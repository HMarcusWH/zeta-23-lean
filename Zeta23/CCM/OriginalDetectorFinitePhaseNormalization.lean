import Zeta23.CCM.OriginalDetectorFinitePhaseNormControl
import Zeta23.CCM.OriginalDetectorFinitePhaseCarrier

/-! # Cofinal true-norm normalization of the actual finite phase trials -/

noncomputable section

open Set Complex Filter
open scoped Topology

namespace Zeta23.CCM

def originalDetectorFinitePhaseUnitVector (σ L c : ℝ) (hL : 0 < L) :=
  ((‖originalDetectorFinitePhaseVector σ L c hL‖⁻¹ : ℝ) : ℂ) •
    originalDetectorFinitePhaseVector σ L c hL

/-- One actual aperture threshold works for both original phases. The
mass is the genuine physical mass under the original source normalization. -/
theorem exists_originalDetectorFinitePhase_mass_control_threshold :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ (σ a : ℝ) (hσ : σ = 1 ∨ σ = -1)
      (ha : UniversalSinc.fixedScale < a)
      (hLp : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a),
      L0 ≤ Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a →
      (1 / 2 < Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization ^ 2 *
        ‖originalDetectorFinitePhaseVector σ
          (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
          Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hLp‖ ^ 2 ∧
      Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization ^ 2 *
        ‖originalDetectorFinitePhaseVector σ
          (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
          Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hLp‖ ^ 2 < 3 / 2) := by
  have hlim := originalDetectorFinitePhaseMassErrorBudget_mul_exp_tendsto_zero 1 0
  simp only [zero_mul, Real.exp_zero, mul_one] at hlim
  obtain ⟨B, hB⟩ := eventually_atTop.1
    (hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
  refine ⟨max 2 B, le_max_left _ _, ?_⟩
  intro σ a hσ ha hLp hlarge
  have hsmall := hB (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
    ((le_max_right _ _).trans hlarge)
  have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have hsame : originalDetectorFinitePhaseMassErrorBudget σ
      (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) =
      originalDetectorFinitePhaseMassErrorBudget 1 (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) := by
    simp only [originalDetectorFinitePhaseMassErrorBudget, hs, abs_one]
  have herr := originalDetectorFinitePhase_mass_error_le hσ ha hLp
  rw [hsame] at herr
  have hh := abs_lt.1 (herr.trans_lt hsmall)
  constructor <;> linarith [hh.1, hh.2]

/-- Both actual phase vectors are nonzero and their literal true-norm
normalizations have norm one beyond one source-derived aperture threshold. -/
theorem exists_originalDetectorFinitePhase_unit_threshold :
    ∃ L0 : ℝ, 2 ≤ L0 ∧ ∀ (σ a : ℝ) (hσ : σ = 1 ∨ σ = -1)
      (ha : UniversalSinc.fixedScale < a)
      (hLp : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a),
      L0 ≤ Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a →
      (originalDetectorFinitePhaseVector σ
        (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
        Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hLp ≠ 0 ∧
      ‖originalDetectorFinitePhaseUnitVector σ
        (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
        Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hLp‖ = 1) := by
  obtain ⟨L0, hL0, hcontrol⟩ := exists_originalDetectorFinitePhase_mass_control_threshold
  refine ⟨L0, hL0, ?_⟩
  intro σ a hσ ha hLp hlarge
  have hmass := (hcontrol σ a hσ ha hLp hlarge).1
  have hv : originalDetectorFinitePhaseVector σ
      (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
      Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hLp ≠ 0 := by
    intro hz
    rw [hz, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hmass
    norm_num at hmass
  refine ⟨hv, ?_⟩
  unfold originalDetectorFinitePhaseUnitVector
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 (norm_nonneg _)), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- True native normalization preserves the proved trial higher moments.
This does not impose a higher-moment condition on any selected ground. -/
theorem originalDetectorFinitePhaseUnitVector_moment_zero_lt_six
    (σ c : ℝ) {L : ℝ} (hL : 2 ≤ L) {r : ℕ} (hr : r < 6) :
    centeredMoment (originalDetectorQuarticCutoff L) r
      ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
        (originalDetectorFinitePhaseUnitVector σ L c (by linarith))) = 0 := by
  have heq : centeredMoment (originalDetectorQuarticCutoff L) r
      ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
        (originalDetectorFinitePhaseUnitVector σ L c (by linarith))) =
      ((‖originalDetectorFinitePhaseVector σ L c (by linarith)‖⁻¹ : ℝ) : ℂ) *
        centeredMoment (originalDetectorQuarticCutoff L) r
          (originalDetectorFinitePhaseRaw σ L c (by linarith)) := by
    unfold centeredMoment originalDetectorFinitePhaseUnitVector
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change _ * (_ * originalDetectorFinitePhaseRaw σ L c (by linarith) i) = _
    ring
  rw [heq, originalDetectorFinitePhaseRaw_moment_zero_lt_six σ c hL hr, mul_zero]

theorem originalDetectorFinitePhaseUnitVector_native_poles_zero
    (σ c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    canonicalPoleEvenFunctional L (originalDetectorQuarticCutoff L)
      (originalDetectorFinitePhaseUnitVector σ L c (by linarith)) = 0 ∧
    canonicalPoleOddFunctional L (originalDetectorQuarticCutoff L)
      (originalDetectorFinitePhaseUnitVector σ L c (by linarith)) = 0 := by
  have hp := originalDetectorFinitePhaseVector_native_poles_zero σ c hL
  simp only [originalDetectorFinitePhaseUnitVector, map_smul, hp.1, hp.2, smul_zero, and_self]

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_originalDetectorFinitePhase_mass_control_threshold
#print axioms Zeta23.CCM.exists_originalDetectorFinitePhase_unit_threshold
#print axioms Zeta23.CCM.originalDetectorFinitePhaseUnitVector_moment_zero_lt_six
#print axioms Zeta23.CCM.originalDetectorFinitePhaseUnitVector_native_poles_zero
