import Zeta23.CCM.OriginalDetectorFourierTailBounds

/-!
# The fixed quartic cutoff beats every linear exponential loss

These estimates concern the actual source-derived Fourier tail budget and
the literal `ceil(L^4)-4` cutoff. The comparison applies to every fixed
finite jet order and every real linear exponential rate.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Zeta23.CCM

/-- The fixed quartic degree makes its square-root frequency scale
eventually dominate every prescribed linear aperture scale. -/
theorem originalDetectorRawCutoff_sqrt_eventually_ge_mul (A : ℝ) :
    ∀ᶠ L : ℝ in atTop, A * L ≤ Real.sqrt ((originalDetectorRawCutoff L : ℝ) / L) := by
  filter_upwards [eventually_ge_atTop (max 2 (2 * A ^ 2))] with L hL
  have hL2 : 2 ≤ L := (le_max_left _ _).trans hL
  have hLA : 2 * A ^ 2 ≤ L := (le_max_right _ _).trans hL
  apply Real.le_sqrt_of_sq_le
  calc
    (A * L) ^ 2 = A ^ 2 * L ^ 2 := by ring
    _ ≤ (L / 2) * L ^ 2 :=
      mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    _ = L ^ 3 / 2 := by ring
    _ ≤ (originalDetectorRawCutoff L : ℝ) / L := originalDetectorRawCutoff_div_lower hL2

/-- After any fixed linear exponential rescaling, the proved tail budget
still tends to zero. This pays arbitrary rates, rather than only a single
preselected aperture rate. -/
theorem originalDetectorDividedLobeFourierJetTailBudget_mul_exp_tendsto_zero
    (s : ℝ) (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorDividedLobeFourierJetTailBudget s L r *
      Real.exp (β * L)) atTop (𝓝 0) := by
  let k := originalDetectorDividedLobeFourierDecayRate s
  let C := 320 * originalDetectorDividedLobeFourierJetDecayConstant s r / k ^ 3
  let A := 4 * (|β| + 1) / k
  have hk : 0 < k := originalDetectorDividedLobeFourierDecayRate_pos s
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg (mul_nonneg (by norm_num)
      (originalDetectorDividedLobeFourierJetDecayConstant_nonneg s r)) (pow_pos hk 3).le
  have hlim : Tendsto (fun L : ℝ => C * (L ^ 8 * Real.exp (-L))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 8).const_mul C
  apply squeeze_zero' _ _ hlim
  · filter_upwards [] with L
    unfold originalDetectorDividedLobeFourierJetTailBudget
    positivity
  · filter_upwards [eventually_ge_atTop (2 : ℝ),
      originalDetectorRawCutoff_sqrt_eventually_ge_mul A] with L hL hbound
    have hscale := mul_le_mul_of_nonneg_left hbound (show 0 ≤ k / 4 by positivity)
    have hKA : (k / 4) * (A * L) = (|β| + 1) * L := by
      dsimp [A]
      field_simp
    rw [hKA] at hscale
    have hβ : β * L ≤ |β| * L :=
      mul_le_mul_of_nonneg_right (le_abs_self β) (by linarith)
    have hexp : -(k / 4) * Real.sqrt ((originalDetectorRawCutoff L : ℝ) / L) +
        β * L ≤ -L := by linarith
    change C * L ^ 8 * Real.exp (-(k / 4) *
      Real.sqrt ((originalDetectorRawCutoff L : ℝ) / L)) * Real.exp (β * L) ≤ _
    rw [mul_assoc, ← Real.exp_add]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 hexp) (mul_nonneg hC (pow_nonneg (by linarith) _))

/-- The source-derived budget eventually lies strictly below every
requested positive exponential padding scale. -/
theorem originalDetectorDividedLobeFourierJetTailBudget_eventually_lt_exp
    (s : ℝ) (r : ℕ) (β : ℝ) :
    ∀ᶠ L : ℝ in atTop, originalDetectorDividedLobeFourierJetTailBudget s L r <
      Real.exp (-β * L) := by
  have hlim := originalDetectorDividedLobeFourierJetTailBudget_mul_exp_tendsto_zero s r β
  filter_upwards [hlim.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))] with L hL
  have hcancel : Real.exp (β * L) * Real.exp (-β * L) = 1 := by
    rw [← Real.exp_add]
    have he : β * L + -β * L = 0 := by ring
    rw [he, Real.exp_zero]
  have hm := mul_lt_mul_of_pos_right hL (Real.exp_pos (-β * L))
  simpa only [mul_assoc, hcancel, mul_one, one_mul] using hm

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorRawCutoff_sqrt_eventually_ge_mul
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierJetTailBudget_mul_exp_tendsto_zero
#print axioms Zeta23.CCM.originalDetectorDividedLobeFourierJetTailBudget_eventually_lt_exp
