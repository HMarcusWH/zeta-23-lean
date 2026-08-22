import Zeta23.CCM.DictionaryRegularity

noncomputable section

namespace Zeta23.CCM

/-! # Smooth branches of the finite-dictionary residual

The source-coordinate jet calculation isolates the only first-order nonsmooth
mode.  This file unfolds the remaining physical residual into its two smooth
interior branches and the zero exterior branch.  The branch derivatives match
at `-L`, `0`, and `L`; global gluing is deliberately left to the next step.

No explicit formula is invoked here.
-/

/-- Inside a positive aperture the clamp is inactive. -/
theorem dictionaryApertureCoord_eq_one_sub_of_abs_le
    {L y : ℝ} (hL : 0 < L) (hy : |y| ≤ L) :
    dictionaryApertureCoord L y = 1 - |y| / L := by
  unfold dictionaryApertureCoord
  have hdiv : |y| / L ≤ 1 := (div_le_one hL).2 hy
  rw [max_eq_right (sub_nonneg.mpr hdiv)]

/-- Strictly outside a positive aperture the clamp is zero. -/
theorem dictionaryApertureCoord_eq_zero_of_lt_abs
    {L y : ℝ} (hL : 0 < L) (hy : L < |y|) :
    dictionaryApertureCoord L y = 0 := by
  unfold dictionaryApertureCoord
  have hdiv : 1 < |y| / L := (one_lt_div hL).2 hy
  rw [max_eq_left (le_of_lt (sub_neg.mpr hdiv))]

@[simp] theorem dictionaryApertureCoord_zero (L : ℝ) :
    dictionaryApertureCoord L 0 = 1 := by
  simp [dictionaryApertureCoord]

@[simp] theorem dictionaryApertureCoord_right_endpoint {L : ℝ} (hL : 0 < L) :
    dictionaryApertureCoord L L = 0 := by
  simp [dictionaryApertureCoord, abs_of_pos hL, hL.ne']

@[simp] theorem dictionaryApertureCoord_left_endpoint {L : ℝ} (hL : 0 < L) :
    dictionaryApertureCoord L (-L) = 0 := by
  simp [dictionaryApertureCoord, abs_of_pos hL, hL.ne']

/-- Positive interior branch, before gluing at the center and right endpoint. -/
def dictionaryResidualPositiveBranch
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * sourceContractRealResidual N u (1 - y / L)

/-- Negative interior branch, before gluing at the center and left endpoint. -/
def dictionaryResidualNegativeBranch
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * sourceContractRealResidual N u (1 + y / L)

/-- On the nonnegative half of the aperture the physical residual is exactly
its positive smooth branch. -/
theorem dictionaryResidualReal_eq_positiveBranch
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    dictionaryResidualReal N u L y = dictionaryResidualPositiveBranch N u L y := by
  unfold dictionaryResidualReal dictionaryResidualPositiveBranch
  have habs : |y| ≤ L := by simpa [abs_of_nonneg hy0] using hyL
  rw [dictionaryApertureCoord_eq_one_sub_of_abs_le hL habs, abs_of_nonneg hy0]

/-- On the nonpositive half of the aperture the physical residual is exactly
its negative smooth branch. -/
theorem dictionaryResidualReal_eq_negativeBranch
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hyL : -L ≤ y) (hy0 : y ≤ 0) :
    dictionaryResidualReal N u L y = dictionaryResidualNegativeBranch N u L y := by
  unfold dictionaryResidualReal dictionaryResidualNegativeBranch
  have habs : |y| ≤ L := by
    rw [abs_of_nonpos hy0]
    linarith
  rw [dictionaryApertureCoord_eq_one_sub_of_abs_le hL habs, abs_of_nonpos hy0]
  congr 2
  ring

/-- The physical residual vanishes strictly outside the aperture. -/
theorem dictionaryResidualReal_eq_zero_of_lt_abs
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hy : L < |y|) :
    dictionaryResidualReal N u L y = 0 := by
  unfold dictionaryResidualReal
  rw [dictionaryApertureCoord_eq_zero_of_lt_abs hL hy]
  simp

/-- The residual meets the zero exterior continuously at the right endpoint. -/
@[simp] theorem dictionaryResidualReal_right_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    dictionaryResidualReal N u L L = 0 := by
  unfold dictionaryResidualReal
  rw [dictionaryApertureCoord_right_endpoint hL]
  simp

/-- The residual meets the zero exterior continuously at the left endpoint. -/
@[simp] theorem dictionaryResidualReal_left_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    dictionaryResidualReal N u L (-L) = 0 := by
  unfold dictionaryResidualReal
  rw [dictionaryApertureCoord_left_endpoint hL]
  simp

/-- Exact derivative of the positive residual branch. -/
def dictionaryResidualPositiveBranchDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (sourceContractRealResidualDerivative N u (1 - y / L) * (-1 / L))

/-- Exact derivative of the negative residual branch. -/
def dictionaryResidualNegativeBranchDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    (sourceContractRealResidualDerivative N u (1 + y / L) * (1 / L))

/-- The positive physical branch is differentiable with the chain-rule
normalization locked explicitly. -/
theorem hasDerivAt_dictionaryResidualPositiveBranch
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) :
    HasDerivAt (dictionaryResidualPositiveBranch N u L)
      (dictionaryResidualPositiveBranchDerivative N u L y) y := by
  unfold dictionaryResidualPositiveBranch dictionaryResidualPositiveBranchDerivative
  have hdiv : HasDerivAt (fun t : ℝ => t / L) (1 / L) y := by
    simpa using (hasDerivAt_id y).div_const L
  have hinner0 := hdiv.neg
  have hinner1 := hinner0.const_add (1 : ℝ)
  have hinner : HasDerivAt (fun t : ℝ => 1 - t / L) (-1 / L) y := by
    simpa [sub_eq_add_neg] using hinner1
  have hcomp :=
    (hasDerivAt_sourceContractRealResidual N u (1 - y / L)).comp y hinner
  simpa using hcomp.const_mul (1 / 2 : ℝ)

/-- The negative physical branch is differentiable with the opposite inner
orientation. -/
theorem hasDerivAt_dictionaryResidualNegativeBranch
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) :
    HasDerivAt (dictionaryResidualNegativeBranch N u L)
      (dictionaryResidualNegativeBranchDerivative N u L y) y := by
  unfold dictionaryResidualNegativeBranch dictionaryResidualNegativeBranchDerivative
  have hdiv : HasDerivAt (fun t : ℝ => t / L) (1 / L) y := by
    simpa using (hasDerivAt_id y).div_const L
  have hinner0 := hdiv.const_add (1 : ℝ)
  have hinner : HasDerivAt (fun t : ℝ => 1 + t / L) (1 / L) y := by
    simpa using hinner0
  have hcomp :=
    (hasDerivAt_sourceContractRealResidual N u (1 + y / L)).comp y hinner
  simpa using hcomp.const_mul (1 / 2 : ℝ)

/-- The positive branch has zero derivative at the center seam. -/
@[simp] theorem dictionaryResidualPositiveBranchDerivative_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L : ℝ) :
    dictionaryResidualPositiveBranchDerivative N u L 0 = 0 := by
  simp [dictionaryResidualPositiveBranchDerivative]

/-- The negative branch has the same zero derivative at the center seam. -/
@[simp] theorem dictionaryResidualNegativeBranchDerivative_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L : ℝ) :
    dictionaryResidualNegativeBranchDerivative N u L 0 = 0 := by
  simp [dictionaryResidualNegativeBranchDerivative]

/-- The positive branch derivative also vanishes where it meets the zero
exterior at `y=L`. -/
@[simp] theorem dictionaryResidualPositiveBranchDerivative_right_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    dictionaryResidualPositiveBranchDerivative N u L L = 0 := by
  have hL0 : L ≠ 0 := hL.ne'
  have harg : 1 - L / L = (0 : ℝ) := by
    rw [div_self hL0]
    norm_num
  rw [dictionaryResidualPositiveBranchDerivative, harg,
    sourceContractRealResidualDerivative_zero]
  ring

/-- The negative branch derivative vanishes where it meets the zero exterior at
`y=-L`. -/
@[simp] theorem dictionaryResidualNegativeBranchDerivative_left_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    dictionaryResidualNegativeBranchDerivative N u L (-L) = 0 := by
  have hL0 : L ≠ 0 := hL.ne'
  have harg : 1 + (-L) / L = (0 : ℝ) := by
    rw [neg_div, div_self hL0]
    norm_num
  rw [dictionaryResidualNegativeBranchDerivative, harg,
    sourceContractRealResidualDerivative_zero]
  ring

end Zeta23.CCM
