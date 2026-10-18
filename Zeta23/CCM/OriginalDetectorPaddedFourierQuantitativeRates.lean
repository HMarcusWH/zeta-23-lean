import Zeta23.CCM.OriginalDetectorPaddedFinitePoleImageAsymptotics

/-! A retained source-only stretched-exponential margin at the literal cutoff. -/

noncomputable section

open Filter
open scoped Topology

namespace Zeta23.CCM

def originalDetectorQuarticRootScale (L : ℝ) : ℝ :=
  Real.sqrt ((originalDetectorRawCutoff L : ℝ) / L)

def originalDetectorRetainedDecayRate (s : ℝ) : ℝ :=
  originalDetectorDividedLobeFourierDecayRate s / 8

theorem originalDetectorRetainedDecayRate_pos (s : ℝ) :
    0 < originalDetectorRetainedDecayRate s :=
  div_pos (originalDetectorDividedLobeFourierDecayRate_pos s) (by norm_num)

def originalDetectorQuarticErrorWeight (s L β : ℝ) : ℝ :=
  Real.exp (originalDetectorRetainedDecayRate s * originalDetectorQuarticRootScale L + β * L)

theorem originalDetectorRawTailBudget_mul_quarticWeight_tendsto_zero
    (s : ℝ) (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorDividedLobeFourierJetTailBudget s L r *
      originalDetectorQuarticErrorWeight s L β) atTop (𝓝 0) := by
  let k := originalDetectorDividedLobeFourierDecayRate s
  let C := 320 * originalDetectorDividedLobeFourierJetDecayConstant s r / k ^ 3
  let A := 8 * (|β| + 1) / k
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
    unfold originalDetectorDividedLobeFourierJetTailBudget originalDetectorQuarticErrorWeight
    positivity
  · filter_upwards [eventually_ge_atTop (2 : ℝ),
      originalDetectorRawCutoff_sqrt_eventually_ge_mul A] with L hL hbound
    have hscale := mul_le_mul_of_nonneg_left hbound (show 0 ≤ k / 8 by positivity)
    have hKA : (k / 8) * (A * L) = (|β| + 1) * L := by
      dsimp [A]
      field_simp
    rw [hKA] at hscale
    have hβ : β * L ≤ |β| * L :=
      mul_le_mul_of_nonneg_right (le_abs_self β) (by linarith)
    have hexp : -(k / 4) * originalDetectorQuarticRootScale L +
        (k / 8 * originalDetectorQuarticRootScale L + β * L) ≤ -L := by
      unfold originalDetectorQuarticRootScale
      linarith
    change C * L ^ 8 * Real.exp (-(k / 4) * originalDetectorQuarticRootScale L) *
      Real.exp (k / 8 * originalDetectorQuarticRootScale L + β * L) ≤ _
    rw [mul_assoc, ← Real.exp_add]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.2 hexp) (mul_nonneg hC (pow_nonneg (by linarith) _))

theorem originalDetectorPaddedRawTailBudget_mul_quarticWeight_tendsto_zero
    (s : ℝ) (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedRawFourierJetTailBudget s L r *
      originalDetectorQuarticErrorWeight s L β) atTop (𝓝 0) := by
  simpa only [originalDetectorPaddedRawFourierJetTailBudget, originalDetectorPositivePadding,
    add_mul, add_zero] using
    (originalDetectorRawTailBudget_mul_quarticWeight_tendsto_zero s r β).add
      (originalDetectorRawTailBudget_mul_quarticWeight_tendsto_zero s 0 β)

theorem originalDetectorPaddedWindowBudget_mul_quarticWeight_tendsto_zero
    (s : ℝ) (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFiniteWindowImageJetBudget s L r *
      originalDetectorQuarticErrorWeight s L β) atTop (𝓝 0) := by
  have hf : Tendsto (fun L : ℝ => 8 * Real.pi / L) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hi (i : ℕ) : Tendsto (fun L : ℝ => (Nat.choose r i : ℝ) *
      (8 * Real.pi / L) ^ i * (originalDetectorPaddedRawFourierJetTailBudget s L (r - i) *
        originalDetectorQuarticErrorWeight s L β)) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((hf.pow i).const_mul (Nat.choose r i : ℝ)).mul
      (originalDetectorPaddedRawTailBudget_mul_quarticWeight_tendsto_zero s (r - i) β)
  have hsum := tendsto_finsetSum (Finset.range (r + 1)) (fun i _ => hi i)
  simp only [Finset.sum_const_zero] at hsum
  convert! hsum using 1
  ext L
  unfold originalDetectorPaddedFiniteWindowImageJetBudget
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem originalDetectorPaddedPoleBudget_mul_quarticWeight_tendsto_zero
    (s : ℝ) (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => originalDetectorPaddedFinitePoleImageJetBudget s L r *
      originalDetectorQuarticErrorWeight s L β) atTop (𝓝 0) := by
  have hh := (originalDetectorPaddedWindowBudget_mul_quarticWeight_tendsto_zero s r β).const_mul
    (1 / 4 : ℝ)
  have hs := (originalDetectorPaddedWindowBudget_mul_quarticWeight_tendsto_zero s (r + 2) β).add hh
  simp only [mul_zero, add_zero] at hs
  convert! hs using 1
  ext L
  unfold originalDetectorPaddedFinitePoleImageJetBudget
  ring

theorem originalDetectorPaddedPoleBudget_mul_aperture_quarticWeight_tendsto_zero
    (s : ℝ) (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ => L * originalDetectorPaddedFinitePoleImageJetBudget s L r *
      originalDetectorQuarticErrorWeight s L β) atTop (𝓝 0) := by
  have hfast := originalDetectorPaddedPoleBudget_mul_quarticWeight_tendsto_zero s r (β + 1)
  have hprod := hfast.mul (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)
  simp only [mul_zero] at hprod
  convert! hprod using 1
  ext L
  simp only [pow_one]
  have he : originalDetectorQuarticErrorWeight s L (β + 1) * Real.exp (-L) =
      originalDetectorQuarticErrorWeight s L β := by
    unfold originalDetectorQuarticErrorWeight
    rw [← Real.exp_add]
    congr 1
    ring
  rw [mul_mul_mul_comm, he]
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorRawTailBudget_mul_quarticWeight_tendsto_zero
#print axioms Zeta23.CCM.originalDetectorPaddedPoleBudget_mul_quarticWeight_tendsto_zero
#print axioms Zeta23.CCM.originalDetectorPaddedPoleBudget_mul_aperture_quarticWeight_tendsto_zero
