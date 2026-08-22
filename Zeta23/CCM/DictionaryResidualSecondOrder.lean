import Zeta23.CCM.DictionaryResidualBranches

noncomputable section

namespace Zeta23.CCM

/-! # Second derivatives of the smooth residual branches

`DictionaryResidualBranches` exposes the two interior branches of the physical
residual and proves their first derivatives match at the three seams.  This file
propagates the source-coordinate second derivative through the two affine
physical coordinates.  The endpoint second derivatives vanish because the
source residual has a zero second jet at `ω = 0`; the two center second
derivatives agree without requiring the second source jet at `ω = 1` to vanish.

No explicit formula is invoked here.
-/

/-- Second derivative of the positive physical residual branch. -/
def dictionaryResidualPositiveBranchSecondDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ((sourceContractRealResidualSecondDerivative N u (1 - y / L) * (-(1 / L)))
      * (-(1 / L)))

/-- Second derivative of the negative physical residual branch. -/
def dictionaryResidualNegativeBranchSecondDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ((sourceContractRealResidualSecondDerivative N u (1 + y / L) * (1 / L))
      * (1 / L))

/-- The positive branch derivative is differentiable with the expected second
chain-rule factor. -/
theorem hasDerivAt_dictionaryResidualPositiveBranchDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) :
    HasDerivAt (dictionaryResidualPositiveBranchDerivative N u L)
      (dictionaryResidualPositiveBranchSecondDerivative N u L y) y := by
  unfold dictionaryResidualPositiveBranchDerivative
    dictionaryResidualPositiveBranchSecondDerivative
  have hdiv : HasDerivAt (fun t : ℝ => t / L) (1 / L) y := by
    simpa using (hasDerivAt_id y).div_const L
  have hinner0 := hdiv.neg
  have hinner1 := hinner0.const_add (1 : ℝ)
  have hinner : HasDerivAt (fun t : ℝ => 1 - t / L) (-(1 / L)) y := by
    simpa [sub_eq_add_neg] using hinner1
  have hR0 :=
    (differentiableAt_sourceContractRealResidualDerivative N u (1 - y / L)).hasDerivAt
  have hR : HasDerivAt (sourceContractRealResidualDerivative N u)
      (sourceContractRealResidualSecondDerivative N u (1 - y / L)) (1 - y / L) := by
    simpa [sourceContractRealResidualSecondDerivative] using hR0
  have hcomp := hR.comp y hinner
  have hscaled := hcomp.mul_const (-(1 / L))
  simpa using hscaled.const_mul (1 / 2 : ℝ)

/-- The negative branch derivative is differentiable with the opposite affine
orientation. -/
theorem hasDerivAt_dictionaryResidualNegativeBranchDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) :
    HasDerivAt (dictionaryResidualNegativeBranchDerivative N u L)
      (dictionaryResidualNegativeBranchSecondDerivative N u L y) y := by
  unfold dictionaryResidualNegativeBranchDerivative
    dictionaryResidualNegativeBranchSecondDerivative
  have hdiv : HasDerivAt (fun t : ℝ => t / L) (1 / L) y := by
    simpa using (hasDerivAt_id y).div_const L
  have hinner0 := hdiv.const_add (1 : ℝ)
  have hinner : HasDerivAt (fun t : ℝ => 1 + t / L) (1 / L) y := by
    simpa using hinner0
  have hR0 :=
    (differentiableAt_sourceContractRealResidualDerivative N u (1 + y / L)).hasDerivAt
  have hR : HasDerivAt (sourceContractRealResidualDerivative N u)
      (sourceContractRealResidualSecondDerivative N u (1 + y / L)) (1 + y / L) := by
    simpa [sourceContractRealResidualSecondDerivative] using hR0
  have hcomp := hR.comp y hinner
  have hscaled := hcomp.mul_const (1 / L)
  simpa using hscaled.const_mul (1 / 2 : ℝ)

/-- The positive branch has zero second derivative where it meets the zero
exterior at `y=L`. -/
@[simp] theorem dictionaryResidualPositiveBranchSecondDerivative_right_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    dictionaryResidualPositiveBranchSecondDerivative N u L L = 0 := by
  have hL0 : L ≠ 0 := hL.ne'
  have harg : 1 - L / L = (0 : ℝ) := by
    rw [div_self hL0]
    norm_num
  rw [dictionaryResidualPositiveBranchSecondDerivative, harg,
    sourceContractRealResidualSecondDerivative_zero]
  ring

/-- The negative branch has zero second derivative where it meets the zero
exterior at `y=-L`. -/
@[simp] theorem dictionaryResidualNegativeBranchSecondDerivative_left_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    dictionaryResidualNegativeBranchSecondDerivative N u L (-L) = 0 := by
  have hL0 : L ≠ 0 := hL.ne'
  have harg : 1 + (-L) / L = (0 : ℝ) := by
    rw [neg_div, div_self hL0]
    norm_num
  rw [dictionaryResidualNegativeBranchSecondDerivative, harg,
    sourceContractRealResidualSecondDerivative_zero]
  ring

/-- The two interior branches have the same second derivative at the folded
center.  No vanishing claim is made for the source second jet at `ω = 1`. -/
theorem dictionaryResidualBranchSecondDerivatives_agree_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L : ℝ) :
    dictionaryResidualPositiveBranchSecondDerivative N u L 0 =
      dictionaryResidualNegativeBranchSecondDerivative N u L 0 := by
  unfold dictionaryResidualPositiveBranchSecondDerivative
    dictionaryResidualNegativeBranchSecondDerivative
  simp

end Zeta23.CCM
