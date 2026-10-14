import Zeta23.CCM.OriginalDetectorPaddedFiniteWindowImageJets
import Zeta23.CCM.OriginalDetectorPositiveFourierPadding

/-! # Exponential padding for the actual finite image and all its jets -/

noncomputable section

open Filter
open scoped Topology

namespace Zeta23.CCM

/-- Multiplication by the fixed window preserves decay faster than every
linear exponential, at every prescribed finite derivative order. -/
theorem originalDetectorPaddedFiniteWindowImageJetBudget_mul_exp_tendsto_zero
    (s : ℝ) (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFiniteWindowImageJetBudget s L r *
      Real.exp (β * L)) atTop (𝓝 0) := by
  have hf : Tendsto (fun L : ℝ => 8 * Real.pi / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hi (i : ℕ) : Tendsto (fun L : ℝ => (Nat.choose r i : ℝ) *
      (8 * Real.pi / L) ^ i *
      (originalDetectorPaddedRawFourierJetTailBudget s L (r - i) * Real.exp (β * L)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using ((hf.pow i).const_mul (Nat.choose r i : ℝ)).mul
      (originalDetectorPaddedRawFourierJetTailBudget_mul_exp_tendsto_zero s (r - i) β)
  have hsum := tendsto_finsetSum (Finset.range (r + 1)) (fun i _ => hi i)
  simp only [Finset.sum_const_zero] at hsum
  convert! hsum using 1
  ext L
  unfold originalDetectorPaddedFiniteWindowImageJetBudget
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Every prescribed positive exponential is eventually a strict padding
budget for the actual finite image's genuine derivative error. -/
theorem originalDetectorPaddedFiniteWindowImageJetBudget_eventually_lt_exp
    (s : ℝ) (r : ℕ) (β : ℝ) :
    ∀ᶠ L : ℝ in atTop, originalDetectorPaddedFiniteWindowImageJetBudget s L r <
      Real.exp (-β * L) := by
  have hlim := originalDetectorPaddedFiniteWindowImageJetBudget_mul_exp_tendsto_zero s r β
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with L hL
  have hcancel : Real.exp (β * L) * Real.exp (-β * L) = 1 := by
    rw [← Real.exp_add]
    have he : β * L + -β * L = 0 := by ring
    rw [he, Real.exp_zero]
  have hm := mul_lt_mul_of_pos_right hL (Real.exp_pos (-β * L))
  simpa only [mul_assoc, hcancel, mul_one, one_mul] using hm

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorPaddedFiniteWindowImageJetBudget_mul_exp_tendsto_zero
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteWindowImageJetBudget_eventually_lt_exp
