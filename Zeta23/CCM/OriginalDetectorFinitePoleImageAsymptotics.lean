import Zeta23.CCM.OriginalDetectorFinitePoleImageTransport
import Zeta23.CCM.OriginalDetectorFiniteWindowImageAsymptotics

/-! # Arbitrary exponential padding for the actual finite pole-killed image -/

noncomputable section

open Filter
open scoped Topology

namespace Zeta23.CCM

/-- The actual `Pq` jet error budget beats every fixed linear exponential. -/
theorem originalDetectorFinitePoleImageJetBudget_mul_exp_tendsto_zero
    (s : ℝ) (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorFinitePoleImageJetBudget s L r *
      Real.exp (β * L)) atTop (𝓝 0) := by
  have hhigh := originalDetectorFiniteWindowImageJetBudget_mul_exp_tendsto_zero s (r + 2) β
  have hlow := (originalDetectorFiniteWindowImageJetBudget_mul_exp_tendsto_zero s r β).const_mul
    (1 / 4 : ℝ)
  have hsum := hhigh.add hlow
  simp only [mul_zero, add_zero] at hsum
  convert! hsum using 1
  ext L
  unfold originalDetectorFinitePoleImageJetBudget
  ring

/-- Every positive exponential scale is eventually strict padding for
the actual pole-killed finite-image error, with no supplied rate premise. -/
theorem originalDetectorFinitePoleImageJetBudget_eventually_lt_exp
    (s : ℝ) (r : ℕ) (β : ℝ) :
    ∀ᶠ L : ℝ in atTop, originalDetectorFinitePoleImageJetBudget s L r <
      Real.exp (-β * L) := by
  have hlim := originalDetectorFinitePoleImageJetBudget_mul_exp_tendsto_zero s r β
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with L hL
  have hcancel : Real.exp (β * L) * Real.exp (-β * L) = 1 := by
    rw [← Real.exp_add]
    have he : β * L + -β * L = 0 := by ring
    rw [he, Real.exp_zero]
  have hm := mul_lt_mul_of_pos_right hL (Real.exp_pos (-β * L))
  simpa only [mul_assoc, hcancel, mul_one, one_mul] using hm

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorFinitePoleImageJetBudget_mul_exp_tendsto_zero
#print axioms Zeta23.CCM.originalDetectorFinitePoleImageJetBudget_eventually_lt_exp
