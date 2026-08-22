import Zeta23.CCM.DictionaryResidualGluing

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23.CCM

open Set Filter

/-! ## Exterior zero identities -/

private theorem dictionaryResidualReal_eq_zero_of_right
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hy : L ≤ y) :
    dictionaryResidualReal N u L y = 0 := by
  rcases hy.eq_or_lt with hEq | hLt
  · subst y
    exact dictionaryResidualReal_right_endpoint N u hL
  · have hy0 : 0 ≤ y := le_trans hL.le hy
    exact dictionaryResidualReal_eq_zero_of_lt_abs N u hL (by simpa [abs_of_nonneg hy0] using hLt)

private theorem dictionaryResidualReal_eq_zero_of_left
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hy : y ≤ -L) :
    dictionaryResidualReal N u L y = 0 := by
  rcases hy.eq_or_lt with hEq | hLt
  · subst y
    exact dictionaryResidualReal_left_endpoint N u hL
  · have hy0 : y < 0 := by linarith
    have habs : |y| = -y := abs_of_neg hy0
    exact dictionaryResidualReal_eq_zero_of_lt_abs N u hL (by rw [habs]; linarith)

/-! ## Global first derivative -/

/-- Piecewise first derivative of the physical residual.  Boundary values are
chosen to be zero, which agrees with the interior branch jets. -/
def dictionaryResidualRealDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) : ℝ :=
  if y ≤ -L then 0
  else if y ≤ 0 then dictionaryResidualNegativeBranchDerivative N u L y
  else if y < L then dictionaryResidualPositiveBranchDerivative N u L y
  else 0

private theorem dictionaryResidualRealDerivative_eq_negativeBranchDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hyL : -L ≤ y) (hy0 : y ≤ 0) :
    dictionaryResidualRealDerivative N u L y =
      dictionaryResidualNegativeBranchDerivative N u L y := by
  by_cases hEq : y = -L
  · subst y
    simp [dictionaryResidualRealDerivative, hL.le,
      dictionaryResidualNegativeBranchDerivative_left_endpoint N u hL]
  · have hgt : -L < y := lt_of_le_of_ne hyL (Ne.symm hEq)
    simp [dictionaryResidualRealDerivative, not_le.mpr hgt, hy0]

private theorem dictionaryResidualRealDerivative_eq_positiveBranchDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    dictionaryResidualRealDerivative N u L y =
      dictionaryResidualPositiveBranchDerivative N u L y := by
  by_cases h0 : y = 0
  · subst y
    simp [dictionaryResidualRealDerivative]
  by_cases hEq : y = L
  · subst y
    simp [dictionaryResidualRealDerivative, hL.le,
      dictionaryResidualPositiveBranchDerivative_right_endpoint N u hL]
  · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm h0)
    have hylt : y < L := lt_of_le_of_ne hyL hEq
    have hnleft : ¬ y ≤ -L := by linarith
    simp [dictionaryResidualRealDerivative, hnleft, not_le.mpr hypos, hylt]

private theorem dictionaryResidualRealDerivative_eq_zero_of_left
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ} (hy : y ≤ -L) :
    dictionaryResidualRealDerivative N u L y = 0 := by
  simp [dictionaryResidualRealDerivative, hy]

private theorem dictionaryResidualRealDerivative_eq_zero_of_right
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hy : L ≤ y) :
    dictionaryResidualRealDerivative N u L y = 0 := by
  have hnleft : ¬ y ≤ -L := by linarith
  have hnzero : ¬ y ≤ 0 := by linarith
  have hnlt : ¬ y < L := not_lt.mpr hy
  simp [dictionaryResidualRealDerivative, hnleft, hnzero, hnlt]

private theorem hasDerivAt_dictionaryResidualReal_left_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (dictionaryResidualReal N u L) 0 (-L) := by
  have hext0 : HasDerivWithinAt (fun _ : ℝ => 0) 0 (Iic (-L)) (-L) :=
    (hasDerivAt_const (-L) (0 : ℝ)).hasDerivWithinAt
  have hext : HasDerivWithinAt (dictionaryResidualReal N u L) 0 (Iic (-L)) (-L) :=
    hext0.congr_of_mem
      (fun y hy => (dictionaryResidualReal_eq_zero_of_left N u hL hy).symm)
      (by simp)
  have hint0 : HasDerivAt (dictionaryResidualNegativeBranch N u L) 0 (-L) := by
    simpa using hasDerivAt_dictionaryResidualNegativeBranch N u L (-L)
  have hint : HasDerivWithinAt (dictionaryResidualReal N u L) 0 (Icc (-L) 0) (-L) :=
    hint0.hasDerivWithinAt.congr_of_mem
      (fun y hy => (dictionaryResidualReal_eq_negativeBranch N u hL hy.1 hy.2).symm)
      (by constructor <;> linarith)
  have hmem : Iic (-L) ∪ Icc (-L) 0 ∈ 𝓝 (-L) := by
    apply mem_of_superset (Iio_mem_nhds (show -L < 0 by linarith))
    intro y hy
    by_cases h : y ≤ -L
    · exact Or.inl h
    · exact Or.inr ⟨le_of_not_ge h, le_of_lt hy⟩
  exact (hext.union hint).hasDerivAt hmem

private theorem hasDerivAt_dictionaryResidualReal_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (dictionaryResidualReal N u L) 0 0 := by
  have hneg0 : HasDerivAt (dictionaryResidualNegativeBranch N u L) 0 0 := by
    simpa using hasDerivAt_dictionaryResidualNegativeBranch N u L 0
  have hneg : HasDerivWithinAt (dictionaryResidualReal N u L) 0 (Icc (-L) 0) 0 :=
    hneg0.hasDerivWithinAt.congr_of_mem
      (fun y hy => (dictionaryResidualReal_eq_negativeBranch N u hL hy.1 hy.2).symm)
      (by constructor <;> linarith)
  have hpos0 : HasDerivAt (dictionaryResidualPositiveBranch N u L) 0 0 := by
    simpa using hasDerivAt_dictionaryResidualPositiveBranch N u L 0
  have hpos : HasDerivWithinAt (dictionaryResidualReal N u L) 0 (Icc 0 L) 0 :=
    hpos0.hasDerivWithinAt.congr_of_mem
      (fun y hy => (dictionaryResidualReal_eq_positiveBranch N u hL hy.1 hy.2).symm)
      (by constructor <;> linarith)
  have hmem : Icc (-L) 0 ∪ Icc 0 L ∈ 𝓝 (0 : ℝ) := by
    apply mem_of_superset (Ioo_mem_nhds (show -L < 0 by linarith) hL)
    intro y hy
    by_cases h : y ≤ 0
    · exact Or.inl ⟨le_of_lt hy.1, h⟩
    · exact Or.inr ⟨le_of_not_ge h, le_of_lt hy.2⟩
  exact (hneg.union hpos).hasDerivAt hmem

private theorem hasDerivAt_dictionaryResidualReal_right_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (dictionaryResidualReal N u L) 0 L := by
  have hint0 : HasDerivAt (dictionaryResidualPositiveBranch N u L) 0 L := by
    simpa using hasDerivAt_dictionaryResidualPositiveBranch N u L L
  have hint : HasDerivWithinAt (dictionaryResidualReal N u L) 0 (Icc 0 L) L :=
    hint0.hasDerivWithinAt.congr_of_mem
      (fun y hy => (dictionaryResidualReal_eq_positiveBranch N u hL hy.1 hy.2).symm)
      (by constructor <;> linarith)
  have hext0 : HasDerivWithinAt (fun _ : ℝ => 0) 0 (Ici L) L :=
    (hasDerivAt_const L (0 : ℝ)).hasDerivWithinAt
  have hext : HasDerivWithinAt (dictionaryResidualReal N u L) 0 (Ici L) L :=
    hext0.congr_of_mem
      (fun y hy => (dictionaryResidualReal_eq_zero_of_right N u hL hy).symm)
      (by simp)
  have hmem : Icc 0 L ∪ Ici L ∈ 𝓝 L := by
    apply mem_of_superset (Ioi_mem_nhds hL)
    intro y hy
    by_cases h : y ≤ L
    · exact Or.inl ⟨le_of_lt hy, h⟩
    · exact Or.inr (le_of_not_ge h)
  exact (hint.union hext).hasDerivAt hmem

/-- Exact global first derivative of the residual for positive aperture. -/
theorem hasDerivAt_dictionaryResidualReal
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) (y : ℝ) :
    HasDerivAt (dictionaryResidualReal N u L)
      (dictionaryResidualRealDerivative N u L y) y := by
  by_cases hleft : y < -L
  · have hev : dictionaryResidualReal N u L =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
      filter_upwards [Iio_mem_nhds hleft] with z hz
      exact dictionaryResidualReal_eq_zero_of_left N u hL (le_of_lt hz)
    have h := (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev.symm
    simpa [dictionaryResidualRealDerivative, le_of_lt hleft] using h
  by_cases hleftEq : y = -L
  · subst y
    simpa [dictionaryResidualRealDerivative] using
      hasDerivAt_dictionaryResidualReal_left_endpoint N u hL
  have hgtLeft : -L < y := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hleftEq)
  by_cases hneg : y < 0
  · have hev : dictionaryResidualReal N u L =ᶠ[𝓝 y]
        dictionaryResidualNegativeBranch N u L := by
      filter_upwards [Ioo_mem_nhds hgtLeft hneg] with z hz
      exact dictionaryResidualReal_eq_negativeBranch N u hL (le_of_lt hz.1) (le_of_lt hz.2)
    have h := (hasDerivAt_dictionaryResidualNegativeBranch N u L y).congr_of_eventuallyEq hev.symm
    have hnleft : ¬ y ≤ -L := not_le.mpr hgtLeft
    simpa [dictionaryResidualRealDerivative, hnleft, le_of_lt hneg] using h
  by_cases hzero : y = 0
  · subst y
    simpa [dictionaryResidualRealDerivative, hL.le] using
      hasDerivAt_dictionaryResidualReal_zero N u hL
  have hypos : 0 < y := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
  by_cases hpos : y < L
  · have hev : dictionaryResidualReal N u L =ᶠ[𝓝 y]
        dictionaryResidualPositiveBranch N u L := by
      filter_upwards [Ioo_mem_nhds hypos hpos] with z hz
      exact dictionaryResidualReal_eq_positiveBranch N u hL (le_of_lt hz.1) (le_of_lt hz.2)
    have h := (hasDerivAt_dictionaryResidualPositiveBranch N u L y).congr_of_eventuallyEq hev.symm
    have hnleft : ¬ y ≤ -L := by linarith
    have hnzero : ¬ y ≤ 0 := not_le.mpr hypos
    simpa [dictionaryResidualRealDerivative, hnleft, hnzero, hpos] using h
  by_cases hrightEq : y = L
  · subst y
    simpa [dictionaryResidualRealDerivative, hL.le] using
      hasDerivAt_dictionaryResidualReal_right_endpoint N u hL
  · have hright : L < y := lt_of_le_of_ne (le_of_not_gt hpos) (Ne.symm hrightEq)
    have hev : dictionaryResidualReal N u L =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
      filter_upwards [Ioi_mem_nhds hright] with z hz
      exact dictionaryResidualReal_eq_zero_of_right N u hL (le_of_lt hz)
    have h := (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev.symm
    have hnleft : ¬ y ≤ -L := by linarith
    have hnzero : ¬ y ≤ 0 := by linarith
    have hnlt : ¬ y < L := by linarith
    simpa [dictionaryResidualRealDerivative, hnleft, hnzero, hnlt] using h

end Zeta23.CCM
