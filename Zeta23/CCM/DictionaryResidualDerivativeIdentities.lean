import Zeta23.CCM.DictionaryResidualFirstOrderGluing

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23.CCM

/-- The global residual derivative agrees with the negative branch on the closed
negative half-aperture, including both seam values. -/
theorem dictionaryResidualRealDerivative_eq_negativeBranchDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hyL : -L ≤ y) (hy0 : y ≤ 0) :
    dictionaryResidualRealDerivative N u L y =
      dictionaryResidualNegativeBranchDerivative N u L y := by
  by_cases hEq : y = -L
  · subst y
    simp [dictionaryResidualRealDerivative,
      dictionaryResidualNegativeBranchDerivative_left_endpoint N u hL]
  · have hgt : -L < y := lt_of_le_of_ne hyL (Ne.symm hEq)
    simp [dictionaryResidualRealDerivative, not_le.mpr hgt, hy0]

/-- The global residual derivative agrees with the positive branch on the closed
positive half-aperture, including both seam values. -/
theorem dictionaryResidualRealDerivative_eq_positiveBranchDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    dictionaryResidualRealDerivative N u L y =
      dictionaryResidualPositiveBranchDerivative N u L y := by
  by_cases h0 : y = 0
  · subst y
    have hnleft : ¬ (0 : ℝ) ≤ -L := by linarith
    simp [dictionaryResidualRealDerivative, hnleft,
      dictionaryResidualNegativeBranchDerivative_zero,
      dictionaryResidualPositiveBranchDerivative_zero]
  by_cases hEq : y = L
  · subst y
    have hnleft : ¬ L ≤ -L := by linarith
    have hnzero : ¬ L ≤ 0 := by linarith
    rw [dictionaryResidualPositiveBranchDerivative_right_endpoint N u hL]
    simp [dictionaryResidualRealDerivative, hnleft, hnzero]
  · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm h0)
    have hylt : y < L := lt_of_le_of_ne hyL hEq
    have hnleft : ¬ y ≤ -L := by linarith
    simp [dictionaryResidualRealDerivative, hnleft, not_le.mpr hypos, hylt]

/-- The global residual derivative vanishes on the left exterior branch. -/
theorem dictionaryResidualRealDerivative_eq_zero_of_left
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ} (hy : y ≤ -L) :
    dictionaryResidualRealDerivative N u L y = 0 := by
  simp [dictionaryResidualRealDerivative, hy]

/-- The global residual derivative vanishes on the right exterior branch. -/
theorem dictionaryResidualRealDerivative_eq_zero_of_right
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hy : L ≤ y) :
    dictionaryResidualRealDerivative N u L y = 0 := by
  have hnleft : ¬ y ≤ -L := by linarith
  have hnzero : ¬ y ≤ 0 := by linarith
  have hnlt : ¬ y < L := not_lt.mpr hy
  simp [dictionaryResidualRealDerivative, hnleft, hnzero, hnlt]

end Zeta23.CCM
