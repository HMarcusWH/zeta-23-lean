import Zeta23.CCM.OriginalDetectorPaddedFinitePhysicalUnitBridge
import Zeta23.CCM.OriginalDetectorPaddedFiniteNativeFormRate
import Zeta23.CCM.OriginalDetectorPaddedFiniteH1Rate

/-! The requested concrete native-form rate of the exact normalized physical image. -/

noncomputable section

open Set Complex Filter
open scoped Topology

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

def originalDetectorPaddedNativeEnergy (σ a : ℝ) (hL : 0 < fixedOriginalSincTrialAperture a) : ℝ :=
  (inner ℂ ((canonicalSourceMatrix (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))).toEuclideanLin
    (originalDetectorPaddedFinitePhaseUnitVector σ (fixedOriginalSincTrialAperture a)
      fixedOriginalSincLobeCenter hL))
    (originalDetectorPaddedFinitePhaseUnitVector σ (fixedOriginalSincTrialAperture a)
      fixedOriginalSincLobeCenter hL)).re

def originalDetectorOriginalWeilEnergy (σ a : ℝ) : ℝ :=
  (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a)).re

theorem originalDetectorPaddedFiniteNativeForm_concrete_rate :
    ∃ L0 : ℝ, 4 ≤ L0 ∧ ∀ (σ a : ℝ) (hσ : σ = 1 ∨ σ = -1)
      (ha : UniversalSinc.fixedScale < a) (hL : 0 < fixedOriginalSincTrialAperture a),
      L0 ≤ fixedOriginalSincTrialAperture a →
      |originalDetectorPaddedNativeEnergy σ a hL - originalDetectorOriginalWeilEnergy σ a| ≤
        (1 + fixedOriginalSincTrialAperture a) * (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
          Real.exp (fixedOriginalSincTrialAperture a / 2 -
            originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
              originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) := by
  obtain ⟨Lm, hLm, hmass⟩ := exists_originalDetectorPaddedFinitePhase_mass_control_threshold
  obtain ⟨B, hB⟩ := eventually_atTop.1 (eventually_lt_retained_quartic_envelope
    UniversalSinc.fixedScale
      (originalDetectorPaddedFiniteNormalizedNativeFormErrorBudget_mul_quarticWeight_tendsto_zero 0))
  refine ⟨max 4 (max Lm B), le_max_left _ _, ?_⟩
  intro σ a hσ ha hL hlarge
  let L := fixedOriginalSincTrialAperture a
  have h4 : 4 ≤ L := (le_max_left _ _).trans hlarge
  have hm := (hmass σ a hσ ha hL
    ((le_max_left Lm B).trans ((le_max_right 4 _).trans hlarge))).1
  have he := originalDetectorPaddedFinitePhaseUnit_native_form_error_le hσ ha hL hm
  have henv := hB L ((le_max_right Lm B).trans ((le_max_right 4 _).trans hlarge))
  have hp : (1 : ℝ) ≤ L ^ (17 / 2 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hpre : 1 ≤ (1 + L) * L ^ (17 / 2 : ℝ) := by nlinarith
  have hexp : Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
      originalDetectorQuarticRootScale L) ≤
      Real.exp (L / 2 - originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
        originalDetectorQuarticRootScale L) := Real.exp_le_exp.mpr (by linarith)
  exact he.trans (henv.le.trans (hexp.trans (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hpre (Real.exp_pos _).le)))

/-- The two actual errors share one threshold depending only on the fixed source. -/
theorem originalDetectorPaddedFinitePhysicalUnit_common_error_rates :
    ∃ L0 : ℝ, 4 ≤ L0 ∧ ∀ (σ a : ℝ) (hσ : σ = 1 ∨ σ = -1)
      (ha : UniversalSinc.fixedScale < a) (hL : 0 < fixedOriginalSincTrialAperture a),
      L0 ≤ fixedOriginalSincTrialAperture a →
      originalDetectorPhysicalH1Error (originalDetectorPaddedFinitePhysicalUnit σ a hL)
          (fixedOriginalSincPhaseTrial σ a) ≤
        (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
          Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
            originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) ∧
      |originalDetectorPaddedNativeEnergy σ a hL - originalDetectorOriginalWeilEnergy σ a| ≤
        (1 + fixedOriginalSincTrialAperture a) * (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
          Real.exp (fixedOriginalSincTrialAperture a / 2 -
            originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
              originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) := by
  obtain ⟨Lf, hLf, hform⟩ := originalDetectorPaddedFiniteNativeForm_concrete_rate
  obtain ⟨Lm, hLm, hmass⟩ := exists_originalDetectorPaddedFinitePhase_mass_control_threshold
  obtain ⟨B, hB⟩ := eventually_atTop.1 (eventually_lt_retained_quartic_envelope
    UniversalSinc.fixedScale (originalDetectorPaddedFiniteH1ErrorBudget_mul_quarticWeight_tendsto_zero 0))
  refine ⟨max Lf (max Lm B), hLf.trans (le_max_left _ _), ?_⟩
  intro σ a hσ ha hL hlarge
  have hflarge := (le_max_left Lf _).trans hlarge
  have hmlarge := (le_max_left Lm B).trans ((le_max_right Lf _).trans hlarge)
  have hblarge := (le_max_right Lm B).trans ((le_max_right Lf _).trans hlarge)
  have h4 : 4 ≤ fixedOriginalSincTrialAperture a := hLf.trans hflarge
  have hm := (hmass σ a hσ ha hL hmlarge).1
  have hm' : 1 / 2 < (originalDetectorPaddedFinitePhysicalNorm σ a hL) ^ 2 := by
    convert! hm using 1 <;> unfold originalDetectorPaddedFinitePhysicalNorm <;> ring
  have herr := originalDetectorPaddedFinitePhysicalUnit_H1_error_le hσ ha hL h4 hm'
  have henv := hB (fixedOriginalSincTrialAperture a) hblarge
  have hp : (1 : ℝ) ≤ (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) :=
    Real.one_le_rpow (by linarith) (by norm_num)
  refine ⟨herr.trans (henv.le.trans ?_), hform σ a hσ ha hL hflarge⟩
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hp
    (Real.exp_pos (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
      originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a))).le

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFiniteNativeForm_concrete_rate
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhysicalUnit_common_error_rates
