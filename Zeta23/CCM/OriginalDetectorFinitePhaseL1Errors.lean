import Zeta23.CCM.OriginalDetectorFinitePhaseApproximation
import Zeta23.CCM.OriginalDetectorFinitePhaseCarrier
import Zeta23.CCM.BoundaryFlatApproximation

/-! # Paid full-line errors for the actual hard-window phase image -/

noncomputable section

open Set Complex MeasureTheory
open scoped Topology

namespace Zeta23.CCM

theorem iteratedDeriv_localizedFiniteVector_eq_formula_on_interval
    {L : ℝ} (hL : 0 < L) (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (hu : BoundaryFlatCoefficients N u) {r : ℕ} (hr : r ≤ 2)
    {x : ℝ} (hx : x ∈ Icc 0 L) :
    iteratedDeriv r (localizedFiniteVector L N u) x =
      iteratedDeriv r (localizedFiniteFunction L N u) x := by
  interval_cases r
  · simp only [iteratedDeriv_zero, localizedFiniteVector_eq_indicator, Set.indicator_of_mem hx]
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [deriv_localizedFiniteVector_eq_indicator_firstJet N u hL hu, Set.indicator_of_mem hx]
    exact (hasDerivAt_localizedFiniteFunction L N u x).deriv.symm
  · simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [deriv_deriv_localizedFiniteVector_eq_indicator_secondJet N u hL hu, Set.indicator_of_mem hx]
    rw [deriv_eq (hasDerivAt_localizedFiniteFunction L N u)]
    exact (hasDerivAt_localizedFiniteFirstJet L N u x).deriv.symm

def originalDetectorFiniteOriginalPhaseHard (σ a : ℝ)
    (hL : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) : ℝ → ℂ :=
  fun x => (Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ) *
    localizedFiniteVector (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a))
      ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff
        (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) + 1)) ℂ)
          (originalDetectorFinitePhaseVector σ
            (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
            Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hL)) x

theorem originalDetectorFiniteOriginalPhaseHard_contDiff
    {a : ℝ} (ha : 0 ≤ a) (σ : ℝ)
    (hLp : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) :
    ContDiff ℝ 2 (originalDetectorFiniteOriginalPhaseHard σ a hLp) := by
  have hL2 : 2 ≤ Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a := by
    unfold Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture
      Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter
    linarith [UniversalSinc.fixedScale_pos]
  apply contDiff_const.mul
  apply contDiff_localizedFiniteVector_of_boundaryFlat _ _ hLp
  rw [originalDetectorFinitePhaseVector_raw]
  exact originalDetectorFinitePhaseRaw_boundaryFlat σ _ hL2

private theorem tsupport_iteratedDeriv_subset (r : ℕ) (f : ℝ → ℂ) :
    tsupport (iteratedDeriv r f) ⊆ tsupport f := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact tsupport_deriv_subset.trans ih

/-- Actual hard-window full-line L1 jet errors. The seam derivatives are
proved by the exact finite boundary-flat equations, and support restricts
the integral to the literal aperture. No L1 error is a caller premise. -/
theorem originalDetectorFiniteOriginalPhaseHard_integral_jet_error_le
    {a : ℝ} (ha : UniversalSinc.fixedScale < a) (σ : ℝ)
    (hLp : 0 < Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a)
    {r : ℕ} (hr : r ≤ 2) :
    (∫ x : ℝ, ‖iteratedDeriv r (originalDetectorFiniteOriginalPhaseHard σ a hLp -
      Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a) x‖) ≤
      Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a *
        (Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization * (1 + |σ|) *
          originalDetectorFinitePoleImageJetBudget UniversalSinc.fixedScale
            (Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a) r) := by
  let L := Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture a
  let p := originalDetectorFiniteOriginalPhaseHard σ a hLp
  let h := Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial σ a
  have ha0 : 0 ≤ a := UniversalSinc.fixedScale_pos.le.trans ha.le
  have hL2 : 2 ≤ L := by
    dsimp [L, Zeta23.ExceptionalZero.fixedOriginalSincTrialAperture,
      Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter]
    linarith [UniversalSinc.fixedScale_pos]
  have hp : ContDiff ℝ 2 p := originalDetectorFiniteOriginalPhaseHard_contDiff ha0 σ hLp
  have hh : ContDiff ℝ 2 h := Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_contDiff σ a
  have hpc : ∀ x ∉ Icc (0 : ℝ) L, p x = 0 := by
    intro x hx
    dsimp [p, originalDetectorFiniteOriginalPhaseHard]
    rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hx, mul_zero]
  have hhc : ∀ x ∉ Icc (0 : ℝ) L, h x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hm
    have hb := Zeta23.ExceptionalZero.fixedOriginalSincPhaseTrial_support ha σ hm
    exact hx ⟨by linarith [hb.1], by linarith [hb.2]⟩
  have hsupp : tsupport (p - h) ⊆ Icc (0 : ℝ) L := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hout
    exact hx (by simp [Pi.sub_apply, hpc x hout, hhc x hout])
  have hjetcont : Continuous (iteratedDeriv r (p - h)) := by
    apply (hp.sub hh).continuous_iteratedDeriv r
    exact_mod_cast hr
  apply integral_norm_le_length_mul_of_support_Icc hLp.le hjetcont
  · exact subset_closure.trans ((tsupport_iteratedDeriv_subset r (p - h)).trans hsupp)
  · intro x hx
    have hpr : ContDiff ℝ r p := hp.of_le (by exact_mod_cast hr)
    have hhr : ContDiff ℝ r h := hh.of_le (by exact_mod_cast hr)
    rw [iteratedDeriv_sub hpr.contDiffAt hhr.contDiffAt]
    have hlocal : iteratedDeriv r p x =
        iteratedDeriv r (originalDetectorFiniteOriginalPhaseApprox σ a hLp) x := by
      let u := (EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
        (originalDetectorFinitePhaseVector σ L Zeta23.ExceptionalZero.fixedOriginalSincLobeCenter hLp)
      change iteratedDeriv r (fun y => (Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ) *
        localizedFiniteVector L (originalDetectorQuarticCutoff L) u y) x =
        iteratedDeriv r (fun y => (Zeta23.ExceptionalZero.fixedOriginalSincTrialNormalization : ℂ) *
          localizedFiniteFunction L (originalDetectorQuarticCutoff L) u y) x
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_const_mul_field]
      congr 1
      apply iteratedDeriv_localizedFiniteVector_eq_formula_on_interval hLp _ _ _ hr hx
      dsimp only [u]
      rw [originalDetectorFinitePhaseVector_raw]
      exact originalDetectorFinitePhaseRaw_boundaryFlat σ _ hL2
    rw [hlocal, norm_sub_rev]
    exact originalDetectorFiniteOriginalPhaseApprox_iteratedDeriv_error_le ha0 σ r hx

end Zeta23.CCM

#print axioms Zeta23.CCM.iteratedDeriv_localizedFiniteVector_eq_formula_on_interval
#print axioms Zeta23.CCM.originalDetectorFiniteOriginalPhaseHard_contDiff
#print axioms Zeta23.CCM.originalDetectorFiniteOriginalPhaseHard_integral_jet_error_le
