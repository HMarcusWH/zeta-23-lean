import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseL1Errors
import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNormControl
import Zeta23.CCM.OriginalDetectorOriginalPhaseL1Bounds
import Zeta23.ExceptionalZero.WeilContinuity

/-!
# Actual Weil padding for the original fixed-cutoff finite phase image

All error bounds and original-source constants are proved upstream. The
concrete zeta Weil continuity theorem is applied to those actual functions.
No Weil approximation or source decay is an input premise.
-/

noncomputable section

open Set Complex MeasureTheory Filter
open scoped Topology

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

def originalDetectorPaddedFinitePhaseL1ErrorBudget (L : ℝ) (r : ℕ) : ℝ :=
  2 * fixedOriginalSincTrialNormalization * L *
    originalDetectorPaddedFinitePoleImageJetBudget UniversalSinc.fixedScale L r

def originalDetectorPaddedFinitePhaseWeilErrorBudget (L : ℝ) : ℝ :=
  let E0 := originalDetectorPaddedFinitePhaseL1ErrorBudget L 0
  let E2 := originalDetectorPaddedFinitePhaseL1ErrorBudget L 2
  let H0 := originalDetectorOriginalPhaseL1JetBudget 0
  let H2 := originalDetectorOriginalPhaseL1JetBudget 2
  Real.exp L * zetaInvSqZeroMass * ((E0 + E2) * (E0 + H0) + (H0 + H2) * E0)

private theorem phase_L1_error_le_common_budget
    {σ a : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : UniversalSinc.fixedScale < a)
    (hLp : 0 < fixedOriginalSincTrialAperture a) {r : ℕ} (hr : r ≤ 2) :
    (∫ x : ℝ, ‖iteratedDeriv r (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLp -
      fixedOriginalSincPhaseTrial σ a) x‖) ≤
        originalDetectorPaddedFinitePhaseL1ErrorBudget (fixedOriginalSincTrialAperture a) r := by
  have hs : |σ| = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have he := originalDetectorPaddedFiniteOriginalPhaseHard_integral_jet_error_le ha σ hLp hr
  rw [hs] at he
  convert he using 1 <;> unfold originalDetectorPaddedFinitePhaseL1ErrorBudget <;> ring

/-- The genuine zeta Weil diagonal of the actual hard finite phase has
the source-derived padding bound at exactly the mandated quartic cutoff. -/
theorem originalDetectorPaddedFinitePhase_Weil_error_le
    {σ a : ℝ} (hσ : σ = 1 ∨ σ = -1) (ha : UniversalSinc.fixedScale < a)
    (hLp : 0 < fixedOriginalSincTrialAperture a) :
    ‖zetaZeroConfig.W (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLp)
        (originalDetectorPaddedFiniteOriginalPhaseHard σ a hLp) -
      zetaZeroConfig.W (fixedOriginalSincPhaseTrial σ a) (fixedOriginalSincPhaseTrial σ a)‖ ≤
        originalDetectorPaddedFinitePhaseWeilErrorBudget (fixedOriginalSincTrialAperture a) := by
  let L := fixedOriginalSincTrialAperture a
  let p := originalDetectorPaddedFiniteOriginalPhaseHard σ a hLp
  let h := fixedOriginalSincPhaseTrial σ a
  let E0 := originalDetectorPaddedFinitePhaseL1ErrorBudget L 0
  let E2 := originalDetectorPaddedFinitePhaseL1ErrorBudget L 2
  let H0 := originalDetectorOriginalPhaseL1JetBudget 0
  let H2 := originalDetectorOriginalPhaseL1JetBudget 2
  have ha0 : 0 ≤ a := UniversalSinc.fixedScale_pos.le.trans ha.le
  have hp : ContDiff ℝ 2 p := originalDetectorPaddedFiniteOriginalPhaseHard_contDiff ha0 σ hLp
  have hh : ContDiff ℝ 2 h := fixedOriginalSincPhaseTrial_contDiff σ a
  have hpsupp : ∀ x, p x ≠ 0 → |x| ≤ L := by
    intro x hx
    have hv : localizedFiniteVector L (originalDetectorQuarticCutoff L)
        ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
          (originalDetectorPaddedFinitePhaseVector σ L fixedOriginalSincLobeCenter hLp)) x ≠ 0 := by
      intro hz
      apply hx
      change (fixedOriginalSincTrialNormalization : ℂ) * _ = 0
      rw [hz, mul_zero]
    have hb := localizedFiniteVector_support_subset L _ _ hv
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hhsupp : ∀ x, h x ≠ 0 → |x| ≤ L := by
    intro x hx
    have ht : x ∈ tsupport (fixedOriginalSincPhaseTrial σ a) := subset_closure hx
    have hb := fixedOriginalSincPhaseTrial_support ha σ ht
    rw [abs_of_nonneg (by linarith [hb.1] : (0 : ℝ) ≤ x)]
    linarith [hb.2]
  have he0 : (∫ x : ℝ, ‖(p - h) x‖) ≤ E0 := by
    simpa only [iteratedDeriv_zero] using phase_L1_error_le_common_budget hσ ha hLp (r := 0) (by norm_num)
  have he2 : (∫ x : ℝ, ‖deriv (deriv (p - h)) x‖) ≤ E2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      phase_L1_error_le_common_budget hσ ha hLp (r := 2) (by norm_num)
  have hH0 : (∫ x : ℝ, ‖h x‖) ≤ H0 := by
    simpa only [iteratedDeriv_zero] using fixedOriginalSincPhaseTrial_originalPhase_L1_bound hσ a 0
  have hH2 : (∫ x : ℝ, ‖deriv (deriv h) x‖) ≤ H2 := by
    simpa only [iteratedDeriv_succ, iteratedDeriv_zero] using
      fixedOriginalSincPhaseTrial_originalPhase_L1_bound hσ a 2
  have hpI : Integrable p volume := hp.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_support_subset_abs hpsupp)
  have hhI : Integrable h volume := hh.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_support_subset_abs hhsupp)
  have heI : Integrable (p - h) volume := hpI.sub hhI
  have hP0 : (∫ x : ℝ, ‖p x‖) ≤ E0 + H0 := by
    have htri (x : ℝ) : ‖p x‖ ≤ ‖(p - h) x‖ + ‖h x‖ := by
      convert norm_add_le ((p - h) x) (h x) using 1 <;> simp only [Pi.sub_apply, sub_add_cancel]
    calc
      _ ≤ ∫ x : ℝ, ‖(p - h) x‖ + ‖h x‖ := integral_mono hpI.norm (heI.norm.add hhI.norm) htri
      _ = (∫ x : ℝ, ‖(p - h) x‖) + ∫ x : ℝ, ‖h x‖ := integral_add heI.norm hhI.norm
      _ ≤ _ := add_le_add he0 hH0
  have hE0n : 0 ≤ E0 := (integral_nonneg (fun x => norm_nonneg ((p - h) x))).trans he0
  have hE2n : 0 ≤ E2 := (integral_nonneg (fun x => norm_nonneg (deriv (deriv (p - h)) x))).trans he2
  have hH0n : 0 ≤ H0 := (integral_nonneg (fun x => norm_nonneg (h x))).trans hH0
  have hH2n : 0 ≤ H2 := (integral_nonneg (fun x => norm_nonneg (deriv (deriv h) x))).trans hH2
  have hfirst := mul_le_mul (add_le_add he0 he2) hP0
    (integral_nonneg (fun x => norm_nonneg (p x))) (add_nonneg hE0n hE2n)
  have hsecond := mul_le_mul (add_le_add hH0 hH2) he0
    (integral_nonneg (fun x => norm_nonneg ((p - h) x))) (add_nonneg hH0n hH2n)
  have hW := zeta_W_self_sub_self_norm_le_commonSupport hLp.le hp hh hpsupp hhsupp
  exact hW.trans (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond)
    (mul_nonneg (Real.exp_pos L).le zetaInvSqZeroMass_nonneg))

theorem originalDetectorPaddedFinitePhaseL1ErrorBudget_mul_exp_tendsto_zero (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFinitePhaseL1ErrorBudget L r * Real.exp (β * L))
      atTop (𝓝 0) := by
  have hh := (originalDetectorPaddedFinitePoleImageJetBudget_mul_aperture_exp_tendsto_zero
    UniversalSinc.fixedScale r β).const_mul (2 * fixedOriginalSincTrialNormalization)
  simpa only [mul_zero, originalDetectorPaddedFinitePhaseL1ErrorBudget, mul_assoc] using hh

/-- The actual Weil padding survives every requested fixed linear
exponential loss, despite the growing common-support aperture. -/
theorem originalDetectorPaddedFinitePhaseWeilErrorBudget_mul_exp_tendsto_zero (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFinitePhaseWeilErrorBudget L * Real.exp (β * L))
      atTop (𝓝 0) := by
  let H0 := originalDetectorOriginalPhaseL1JetBudget 0
  let H2 := originalDetectorOriginalPhaseL1JetBudget 2
  have hE0 := originalDetectorPaddedFinitePhaseL1ErrorBudget_mul_exp_tendsto_zero 0 (β + 1)
  have hE2 := originalDetectorPaddedFinitePhaseL1ErrorBudget_mul_exp_tendsto_zero 2 (β + 1)
  have hzero := originalDetectorPaddedFinitePhaseL1ErrorBudget_mul_exp_tendsto_zero 0 0
  simp only [zero_mul, Real.exp_zero, mul_one] at hzero
  have hsum : Tendsto (fun L : ℝ =>
      (originalDetectorPaddedFinitePhaseL1ErrorBudget L 0 + originalDetectorPaddedFinitePhaseL1ErrorBudget L 2) *
        Real.exp ((β + 1) * L)) atTop (𝓝 0) := by
    simpa only [add_zero, ← add_mul] using hE0.add hE2
  have hbounded : Tendsto (fun L : ℝ => originalDetectorPaddedFinitePhaseL1ErrorBudget L 0 + H0)
      atTop (𝓝 H0) := by simpa only [zero_add] using hzero.add_const H0
  have hlim := ((hsum.mul hbounded).add (hE0.const_mul (H0 + H2))).const_mul zetaInvSqZeroMass
  simp only [mul_zero, zero_mul, add_zero] at hlim
  convert! hlim using 1
  ext L
  unfold originalDetectorPaddedFinitePhaseWeilErrorBudget
  dsimp [H0, H2]
  have he : Real.exp ((β + 1) * L) = Real.exp L * Real.exp (β * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhase_Weil_error_le
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhaseL1ErrorBudget_mul_exp_tendsto_zero
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePhaseWeilErrorBudget_mul_exp_tendsto_zero
