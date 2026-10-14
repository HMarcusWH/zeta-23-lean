import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNativeTransport

/-!
# Actual per-phase cofinal native unit-depth producer

The source, fixed quartic cutoff, reflection, legal native carriers,
normalization and Weil padding are all the proved constructions. This
producer takes an actual off-line zero and produces either requested phase
at arbitrarily late apertures. It supplies no RH closing law.
-/

noncomputable section

open Set Complex MeasureTheory Filter
open scoped Topology

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

private theorem exists_originalPhase_depth_four
    (ρ : zetaZeroConfig.carrier) {β σ : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (hσ : σ = 1 ∨ σ = -1) (R : ℝ) :
    ∃ a : ℝ, UniversalSinc.fixedScale < a ∧ max R 4 < fixedOriginalSincTrialAperture a ∧
      (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a)).re ≤
        -4 * Real.exp (β * fixedOriginalSincTrialAperture a) := by
  have hoff : (ρ : ℂ).re ≠ 1 / 2 := by
    intro heq
    rw [heq, sub_self, abs_zero] at hβρ
    linarith
  let B := 4 * fixedOriginalSincKernelL2Mass *
    Real.exp (2 * β * fixedOriginalSincLobeCenter) + |fixedOriginalSincCorrelationReal 0| + 1
  let A := max (max R 4) UniversalSinc.fixedScale + 1
  have hexc := fixedOriginalSincCorrelation_two_signed_late_excursions_of_off_line_zero
    ρ hoff hβρ A B
  have hexists : ∃ a : ℝ, A < a ∧
      σ * fixedOriginalSincCorrelationReal a < -(B * Real.exp (2 * β * a)) := by
    rcases hσ with hs | hs
    · simpa only [hs, one_mul] using hexc.2
    · obtain ⟨a, ha, hv⟩ := hexc.1
      refine ⟨a, ha, ?_⟩
      rw [hs]
      nlinarith
  obtain ⟨a, ha, hv⟩ := hexists
  have hasep : UniversalSinc.fixedScale < a := by
    dsimp [A] at ha
    linarith [le_max_right (max R (4 : ℝ)) UniversalSinc.fixedScale]
  have ha0 : 0 < a := UniversalSinc.fixedScale_pos.trans hasep
  have hlate : max R 4 < fixedOriginalSincTrialAperture a := by
    dsimp [A] at ha
    dsimp [fixedOriginalSincTrialAperture, fixedOriginalSincLobeCenter]
    linarith [le_max_left (max R (4 : ℝ)) UniversalSinc.fixedScale, UniversalSinc.fixedScale_pos]
  refine ⟨a, hasep, hlate, ?_⟩
  rw [fixedOriginalSincPhaseTrial_Weil_re hσ]
  apply (div_le_iff₀ fixedOriginalSincKernelL2Mass_pos).mpr
  have hE1 : 1 ≤ Real.exp (2 * β * a) := Real.one_le_exp_iff.mpr (by positivity)
  have hCabs := le_abs_self (fixedOriginalSincCorrelationReal 0)
  have hAbsE : |fixedOriginalSincCorrelationReal 0| ≤
      |fixedOriginalSincCorrelationReal 0| * Real.exp (2 * β * a) :=
    le_mul_of_one_le_right (abs_nonneg _) hE1
  have hExp : Real.exp (β * fixedOriginalSincTrialAperture a) =
      Real.exp (2 * β * fixedOriginalSincLobeCenter) * Real.exp (2 * β * a) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [fixedOriginalSincTrialAperture]
    ring
  rw [hExp]
  dsimp [B] at hv
  nlinarith [Real.exp_pos (2 * β * a)]

/-- Actual produced data: every vector in these fields is the literal
fixed-cutoff true-norm normalized source phase, rather than an arbitrary
trial supplied to a consumer theorem. -/
structure OriginalDetectorPaddedFinitePhaseData (β σ R : ℝ) where
  separation : ℝ
  aperture_pos : 0 < fixedOriginalSincTrialAperture separation
  separation_gt_scale : UniversalSinc.fixedScale < separation
  late : max R 4 < fixedOriginalSincTrialAperture separation
  unit : ‖originalDetectorPaddedFinitePhaseUnitVector σ (fixedOriginalSincTrialAperture separation)
    fixedOriginalSincLobeCenter aperture_pos‖ = 1
  depth : (inner ℂ ((canonicalSourceMatrix (fixedOriginalSincTrialAperture separation)
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture separation))).toEuclideanLin
    (originalDetectorPaddedFinitePhaseUnitVector σ (fixedOriginalSincTrialAperture separation)
      fixedOriginalSincLobeCenter aperture_pos))
    (originalDetectorPaddedFinitePhaseUnitVector σ (fixedOriginalSincTrialAperture separation)
      fixedOriginalSincLobeCenter aperture_pos)).re ≤
    -Real.exp (β * fixedOriginalSincTrialAperture separation)

/-- For each actual phase separately, an off-line zero produces native
unit vectors of the requested exponential depth at cofinally late output
apertures and exactly `ceil(L^4)` cutoff. -/
theorem originalDetectorPaddedFinitePhase_producer
    (ρ : zetaZeroConfig.carrier) {β σ : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (hσ : σ = 1 ∨ σ = -1) (R : ℝ) :
    Nonempty (OriginalDetectorPaddedFinitePhaseData β σ R) := by
  obtain ⟨Lm, hLm, hmass⟩ := exists_originalDetectorPaddedFinitePhase_mass_control_threshold
  obtain ⟨Lu, hLu, hunit⟩ := exists_originalDetectorPaddedFinitePhase_unit_threshold
  have hWlim := originalDetectorPaddedFinitePhaseWeilErrorBudget_mul_exp_tendsto_zero 0
  simp only [zero_mul, Real.exp_zero, mul_one] at hWlim
  obtain ⟨Lw, hWsmall⟩ := eventually_atTop.1
    (hWlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  let R' := max R (max Lm (max Lu Lw))
  obtain ⟨a, ha, hlate, hdeep⟩ := exists_originalPhase_depth_four ρ hβ hβρ hσ R'
  let L := fixedOriginalSincTrialAperture a
  have hR : R ≤ R' := le_max_left _ _
  have hLall : max Lm (max Lu Lw) < L :=
    (le_max_right R (max Lm (max Lu Lw))).trans_lt ((le_max_left R' 4).trans_lt hlate)
  have hLmL : Lm ≤ L := ((le_max_left Lm (max Lu Lw)).trans hLall.le)
  have hLuL : Lu ≤ L := ((le_max_left Lu Lw).trans (le_max_right Lm (max Lu Lw))).trans hLall.le
  have hLwL : Lw ≤ L := ((le_max_right Lu Lw).trans (le_max_right Lm (max Lu Lw))).trans hLall.le
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (hLm.trans hLmL)
  have ha0 : 0 ≤ a := UniversalSinc.fixedScale_pos.le.trans ha.le
  have hm := hmass σ a hσ ha hLpos hLmL
  have hu := hunit σ a hσ ha hLpos hLuL
  have hWerror := originalDetectorPaddedFinitePhase_Weil_error_le hσ ha hLpos
  have hWlt : ‖zetaZeroConfig.W (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLpos)
      (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLpos) -
      zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a)‖ < 1 :=
    hWerror.trans_lt (hWsmall L hLwL)
  have hRe : (zetaZeroConfig.W (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLpos)
      (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLpos)).re -
      (zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a)).re < 1 := by
    exact (Complex.re_le_norm _).trans_lt hWlt
  have hE1 : 1 ≤ Real.exp (β * L) := Real.one_le_exp_iff.mpr (mul_nonneg hβ.le hLpos.le)
  have hfinite : (zetaZeroConfig.W (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLpos)
      (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLpos)).re ≤ -3 * Real.exp (β * L) := by
    linarith
  refine ⟨⟨a, hLpos, ha, ?_, hu.2, ?_⟩⟩
  · exact (max_le_max_right 4 hR).trans_lt hlate
  · rw [originalDetectorPaddedFinitePhaseUnitVector_nativeEnergy_eq_Weil_div_mass ha0 σ hLpos hu.1]
    apply (div_le_iff₀ (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hm.1)).mpr
    have hmul := mul_le_mul_of_nonneg_left
      (hm.2.le.trans (by norm_num : (3 / 2 : ℝ) ≤ 3)) (Real.exp_pos (β * L)).le
    linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhase_producer
