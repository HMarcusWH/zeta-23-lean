import Zeta23.CCM.DictionaryResidualDerivativeIdentities
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23.CCM

open Set Filter
open scoped Topology ContDiff

/-! ## Global second derivative -/

/-- Piecewise second derivative of the residual.  The branch values agree at
`0` and vanish at the two outer endpoints by PR #37. -/
def dictionaryResidualRealSecondDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L y : ℝ) : ℝ :=
  if y ≤ -L then 0
  else if y ≤ 0 then dictionaryResidualNegativeBranchSecondDerivative N u L y
  else if y < L then dictionaryResidualPositiveBranchSecondDerivative N u L y
  else 0

private theorem dictionaryResidualRealSecondDerivative_eq_negativeBranchSecondDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hyL : -L ≤ y) (hy0 : y ≤ 0) :
    dictionaryResidualRealSecondDerivative N u L y =
      dictionaryResidualNegativeBranchSecondDerivative N u L y := by
  by_cases hEq : y = -L
  · subst y
    rw [dictionaryResidualNegativeBranchSecondDerivative_left_endpoint N u hL]
    simp [dictionaryResidualRealSecondDerivative]
  · have hgt : -L < y := lt_of_le_of_ne hyL (Ne.symm hEq)
    simp [dictionaryResidualRealSecondDerivative, not_le.mpr hgt, hy0]

private theorem dictionaryResidualRealSecondDerivative_eq_positiveBranchSecondDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hy0 : 0 ≤ y) (hyL : y ≤ L) :
    dictionaryResidualRealSecondDerivative N u L y =
      dictionaryResidualPositiveBranchSecondDerivative N u L y := by
  by_cases h0 : y = 0
  · subst y
    have hnleft : ¬ (0 : ℝ) ≤ -L := by linarith
    simp [dictionaryResidualRealSecondDerivative, hnleft,
      dictionaryResidualBranchSecondDerivatives_agree_zero N u L]
  by_cases hEq : y = L
  · subst y
    have hnleft : ¬ L ≤ -L := by linarith
    have hnzero : ¬ L ≤ 0 := by linarith
    rw [dictionaryResidualPositiveBranchSecondDerivative_right_endpoint N u hL]
    simp [dictionaryResidualRealSecondDerivative, hnleft, hnzero]
  · have hypos : 0 < y := lt_of_le_of_ne hy0 (Ne.symm h0)
    have hylt : y < L := lt_of_le_of_ne hyL hEq
    have hnleft : ¬ y ≤ -L := by linarith
    simp [dictionaryResidualRealSecondDerivative, hnleft, not_le.mpr hypos, hylt]

private theorem dictionaryResidualRealSecondDerivative_eq_zero_of_left
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ} (hy : y ≤ -L) :
    dictionaryResidualRealSecondDerivative N u L y = 0 := by
  simp [dictionaryResidualRealSecondDerivative, hy]

private theorem dictionaryResidualRealSecondDerivative_eq_zero_of_right
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L y : ℝ}
    (hL : 0 < L) (hy : L ≤ y) :
    dictionaryResidualRealSecondDerivative N u L y = 0 := by
  have hnleft : ¬ y ≤ -L := by linarith
  have hnzero : ¬ y ≤ 0 := by linarith
  have hnlt : ¬ y < L := not_lt.mpr hy
  simp [dictionaryResidualRealSecondDerivative, hnleft, hnzero, hnlt]

private theorem hasDerivAt_dictionaryResidualRealDerivative_left_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (dictionaryResidualRealDerivative N u L) 0 (-L) := by
  have hext0 : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) (Iic (-L)) (-L) :=
    (hasDerivAt_const (-L) (0 : ℝ)).hasDerivWithinAt
  have hext : HasDerivWithinAt (dictionaryResidualRealDerivative N u L) 0 (Iic (-L)) (-L) :=
    hext0.congr_of_mem
      (fun y hy => dictionaryResidualRealDerivative_eq_zero_of_left N u hy)
      (by simp)
  have hint0 : HasDerivAt (dictionaryResidualNegativeBranchDerivative N u L) 0 (-L) := by
    exact (hasDerivAt_dictionaryResidualNegativeBranchDerivative N u L (-L)).congr_deriv
      (dictionaryResidualNegativeBranchSecondDerivative_left_endpoint N u hL)
  have hint : HasDerivWithinAt (dictionaryResidualRealDerivative N u L) 0 (Icc (-L) 0) (-L) :=
    hint0.hasDerivWithinAt.congr_of_mem
      (fun y hy => dictionaryResidualRealDerivative_eq_negativeBranchDerivative N u hL hy.1 hy.2)
      (by constructor <;> linarith)
  have hmem : Iic (-L) ∪ Icc (-L) 0 ∈ 𝓝 (-L) := by
    apply mem_of_superset (Iio_mem_nhds (show -L < 0 by linarith))
    intro y hy
    by_cases h : y ≤ -L
    · exact Or.inl h
    · exact Or.inr ⟨le_of_not_ge h, le_of_lt hy⟩
  exact (hext.union hint).hasDerivAt hmem

private theorem hasDerivAt_dictionaryResidualRealDerivative_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (dictionaryResidualRealDerivative N u L)
      (dictionaryResidualNegativeBranchSecondDerivative N u L 0) 0 := by
  have hneg0 : HasDerivWithinAt (dictionaryResidualNegativeBranchDerivative N u L)
      (dictionaryResidualNegativeBranchSecondDerivative N u L 0) (Icc (-L) 0) 0 :=
    (hasDerivAt_dictionaryResidualNegativeBranchDerivative N u L 0).hasDerivWithinAt
  have hneg : HasDerivWithinAt (dictionaryResidualRealDerivative N u L)
      (dictionaryResidualNegativeBranchSecondDerivative N u L 0) (Icc (-L) 0) 0 :=
    hneg0.congr_of_mem
      (fun y hy => dictionaryResidualRealDerivative_eq_negativeBranchDerivative N u hL hy.1 hy.2)
      (by constructor <;> linarith)
  have hpos0 : HasDerivAt (dictionaryResidualPositiveBranchDerivative N u L)
      (dictionaryResidualPositiveBranchSecondDerivative N u L 0) 0 :=
    hasDerivAt_dictionaryResidualPositiveBranchDerivative N u L 0
  have hpos0' : HasDerivAt (dictionaryResidualPositiveBranchDerivative N u L)
      (dictionaryResidualNegativeBranchSecondDerivative N u L 0) 0 := by
    rw [dictionaryResidualBranchSecondDerivatives_agree_zero N u L]
    exact hpos0
  have hpos : HasDerivWithinAt (dictionaryResidualRealDerivative N u L)
      (dictionaryResidualNegativeBranchSecondDerivative N u L 0) (Icc 0 L) 0 :=
    hpos0'.hasDerivWithinAt.congr_of_mem
      (fun y hy => dictionaryResidualRealDerivative_eq_positiveBranchDerivative N u hL hy.1 hy.2)
      (by constructor <;> linarith)
  have hmem : Icc (-L) 0 ∪ Icc 0 L ∈ 𝓝 (0 : ℝ) := by
    apply mem_of_superset (Ioo_mem_nhds (show -L < 0 by linarith) hL)
    intro y hy
    by_cases h : y ≤ 0
    · exact Or.inl ⟨le_of_lt hy.1, h⟩
    · exact Or.inr ⟨le_of_not_ge h, le_of_lt hy.2⟩
  exact (hneg.union hpos).hasDerivAt hmem

private theorem hasDerivAt_dictionaryResidualRealDerivative_right_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    HasDerivAt (dictionaryResidualRealDerivative N u L) 0 L := by
  have hint0 : HasDerivAt (dictionaryResidualPositiveBranchDerivative N u L) 0 L := by
    exact (hasDerivAt_dictionaryResidualPositiveBranchDerivative N u L L).congr_deriv
      (dictionaryResidualPositiveBranchSecondDerivative_right_endpoint N u hL)
  have hint : HasDerivWithinAt (dictionaryResidualRealDerivative N u L) 0 (Icc 0 L) L :=
    hint0.hasDerivWithinAt.congr_of_mem
      (fun y hy => dictionaryResidualRealDerivative_eq_positiveBranchDerivative N u hL hy.1 hy.2)
      (by constructor <;> linarith)
  have hext0 : HasDerivWithinAt (fun _ : ℝ => (0 : ℝ)) (0 : ℝ) (Ici L) L :=
    (hasDerivAt_const L (0 : ℝ)).hasDerivWithinAt
  have hext : HasDerivWithinAt (dictionaryResidualRealDerivative N u L) 0 (Ici L) L :=
    hext0.congr_of_mem
      (fun y hy => dictionaryResidualRealDerivative_eq_zero_of_right N u hL hy)
      (by simp)
  have hmem : Icc 0 L ∪ Ici L ∈ 𝓝 L := by
    apply mem_of_superset (Ioi_mem_nhds hL)
    intro y hy
    by_cases h : y ≤ L
    · exact Or.inl ⟨le_of_lt hy, h⟩
    · exact Or.inr (le_of_not_ge h)
  exact (hint.union hext).hasDerivAt hmem

/-- Exact second derivative packaged as the derivative of the global first derivative. -/
theorem hasDerivAt_dictionaryResidualRealDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) (y : ℝ) :
    HasDerivAt (dictionaryResidualRealDerivative N u L)
      (dictionaryResidualRealSecondDerivative N u L y) y := by
  by_cases hleft : y < -L
  · have hev : dictionaryResidualRealDerivative N u L =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
      filter_upwards [Iio_mem_nhds hleft] with z hz
      exact dictionaryResidualRealDerivative_eq_zero_of_left N u (le_of_lt hz)
    have h := (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
    simpa [dictionaryResidualRealSecondDerivative, le_of_lt hleft] using h
  by_cases hleftEq : y = -L
  · subst y
    simpa [dictionaryResidualRealSecondDerivative] using
      hasDerivAt_dictionaryResidualRealDerivative_left_endpoint N u hL
  have hgtLeft : -L < y := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hleftEq)
  by_cases hneg : y < 0
  · have hev : dictionaryResidualRealDerivative N u L =ᶠ[𝓝 y]
        dictionaryResidualNegativeBranchDerivative N u L := by
      filter_upwards [Ioo_mem_nhds hgtLeft hneg] with z hz
      exact dictionaryResidualRealDerivative_eq_negativeBranchDerivative N u hL
        (le_of_lt hz.1) (le_of_lt hz.2)
    have h := (hasDerivAt_dictionaryResidualNegativeBranchDerivative N u L y).congr_of_eventuallyEq hev
    have hnleft : ¬ y ≤ -L := not_le.mpr hgtLeft
    simpa [dictionaryResidualRealSecondDerivative, hnleft, le_of_lt hneg] using h
  by_cases hzero : y = 0
  · subst y
    have hnleft : ¬ (0 : ℝ) ≤ -L := by linarith
    simpa [dictionaryResidualRealSecondDerivative, hnleft] using
      hasDerivAt_dictionaryResidualRealDerivative_zero N u hL
  have hypos : 0 < y := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
  by_cases hpos : y < L
  · have hev : dictionaryResidualRealDerivative N u L =ᶠ[𝓝 y]
        dictionaryResidualPositiveBranchDerivative N u L := by
      filter_upwards [Ioo_mem_nhds hypos hpos] with z hz
      exact dictionaryResidualRealDerivative_eq_positiveBranchDerivative N u hL
        (le_of_lt hz.1) (le_of_lt hz.2)
    have h := (hasDerivAt_dictionaryResidualPositiveBranchDerivative N u L y).congr_of_eventuallyEq hev
    have hnleft : ¬ y ≤ -L := by linarith
    have hnzero : ¬ y ≤ 0 := not_le.mpr hypos
    simpa [dictionaryResidualRealSecondDerivative, hnleft, hnzero, hpos] using h
  by_cases hrightEq : y = L
  · subst y
    have hnleft : ¬ L ≤ -L := by linarith
    have hnzero : ¬ L ≤ 0 := by linarith
    simpa [dictionaryResidualRealSecondDerivative, hnleft, hnzero] using
      hasDerivAt_dictionaryResidualRealDerivative_right_endpoint N u hL
  · have hright : L < y := lt_of_le_of_ne (le_of_not_gt hpos) (Ne.symm hrightEq)
    have hev : dictionaryResidualRealDerivative N u L =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
      filter_upwards [Ioi_mem_nhds hright] with z hz
      exact dictionaryResidualRealDerivative_eq_zero_of_right N u hL (le_of_lt hz)
    have h := (hasDerivAt_const y (0 : ℝ)).congr_of_eventuallyEq hev
    have hnleft : ¬ y ≤ -L := by linarith
    have hnzero : ¬ y ≤ 0 := by linarith
    have hnlt : ¬ y < L := by linarith
    simpa [dictionaryResidualRealSecondDerivative, hnleft, hnzero, hnlt] using h

/-! ## Continuity of the global second derivative -/

private theorem continuousAt_dictionaryResidualRealSecondDerivative_left_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (dictionaryResidualRealSecondDerivative N u L) (-L) := by
  have hext0 : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Iic (-L)) (-L) :=
    continuousAt_const.continuousWithinAt
  have hext : ContinuousWithinAt (dictionaryResidualRealSecondDerivative N u L) (Iic (-L)) (-L) :=
    hext0.congr_of_mem
      (fun y hy => dictionaryResidualRealSecondDerivative_eq_zero_of_left N u hy)
      (by simp)
  have hint0 : ContinuousWithinAt (dictionaryResidualNegativeBranchSecondDerivative N u L)
      (Icc (-L) 0) (-L) :=
    (continuous_dictionaryResidualNegativeBranchSecondDerivative N u L).continuousAt.continuousWithinAt
  have hint : ContinuousWithinAt (dictionaryResidualRealSecondDerivative N u L) (Icc (-L) 0) (-L) :=
    hint0.congr_of_mem
      (fun y hy => dictionaryResidualRealSecondDerivative_eq_negativeBranchSecondDerivative N u hL hy.1 hy.2)
      (by constructor <;> linarith)
  have hmem : Iic (-L) ∪ Icc (-L) 0 ∈ 𝓝 (-L) := by
    apply mem_of_superset (Iio_mem_nhds (show -L < 0 by linarith))
    intro y hy
    by_cases h : y ≤ -L
    · exact Or.inl h
    · exact Or.inr ⟨le_of_not_ge h, le_of_lt hy⟩
  exact (hext.union hint).continuousAt hmem

private theorem continuousAt_dictionaryResidualRealSecondDerivative_zero
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (dictionaryResidualRealSecondDerivative N u L) 0 := by
  have hneg0 : ContinuousWithinAt (dictionaryResidualNegativeBranchSecondDerivative N u L)
      (Icc (-L) 0) 0 :=
    (continuous_dictionaryResidualNegativeBranchSecondDerivative N u L).continuousAt.continuousWithinAt
  have hneg : ContinuousWithinAt (dictionaryResidualRealSecondDerivative N u L) (Icc (-L) 0) 0 :=
    hneg0.congr_of_mem
      (fun y hy => dictionaryResidualRealSecondDerivative_eq_negativeBranchSecondDerivative N u hL hy.1 hy.2)
      (by constructor <;> linarith)
  have hpos0 : ContinuousWithinAt (dictionaryResidualPositiveBranchSecondDerivative N u L)
      (Icc 0 L) 0 :=
    (continuous_dictionaryResidualPositiveBranchSecondDerivative N u L).continuousAt.continuousWithinAt
  have hpos : ContinuousWithinAt (dictionaryResidualRealSecondDerivative N u L) (Icc 0 L) 0 :=
    hpos0.congr_of_mem
      (fun y hy => dictionaryResidualRealSecondDerivative_eq_positiveBranchSecondDerivative N u hL hy.1 hy.2)
      (by constructor <;> linarith)
  have hmem : Icc (-L) 0 ∪ Icc 0 L ∈ 𝓝 (0 : ℝ) := by
    apply mem_of_superset (Ioo_mem_nhds (show -L < 0 by linarith) hL)
    intro y hy
    by_cases h : y ≤ 0
    · exact Or.inl ⟨le_of_lt hy.1, h⟩
    · exact Or.inr ⟨le_of_not_ge h, le_of_lt hy.2⟩
  exact (hneg.union hpos).continuousAt hmem

private theorem continuousAt_dictionaryResidualRealSecondDerivative_right_endpoint
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    ContinuousAt (dictionaryResidualRealSecondDerivative N u L) L := by
  have hint0 : ContinuousWithinAt (dictionaryResidualPositiveBranchSecondDerivative N u L)
      (Icc 0 L) L :=
    (continuous_dictionaryResidualPositiveBranchSecondDerivative N u L).continuousAt.continuousWithinAt
  have hint : ContinuousWithinAt (dictionaryResidualRealSecondDerivative N u L) (Icc 0 L) L :=
    hint0.congr_of_mem
      (fun y hy => dictionaryResidualRealSecondDerivative_eq_positiveBranchSecondDerivative N u hL hy.1 hy.2)
      (by constructor <;> linarith)
  have hext0 : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Ici L) L :=
    continuousAt_const.continuousWithinAt
  have hext : ContinuousWithinAt (dictionaryResidualRealSecondDerivative N u L) (Ici L) L :=
    hext0.congr_of_mem
      (fun y hy => dictionaryResidualRealSecondDerivative_eq_zero_of_right N u hL hy)
      (by simp)
  have hmem : Icc 0 L ∪ Ici L ∈ 𝓝 L := by
    apply mem_of_superset (Ioi_mem_nhds hL)
    intro y hy
    by_cases h : y ≤ L
    · exact Or.inl ⟨le_of_lt hy, h⟩
    · exact Or.inr (le_of_not_ge h)
  exact (hint.union hext).continuousAt hmem

@[fun_prop] theorem continuous_dictionaryResidualRealSecondDerivative
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    Continuous (dictionaryResidualRealSecondDerivative N u L) := by
  rw [continuous_iff_continuousAt]
  intro y
  by_cases hleft : y < -L
  · have hev : dictionaryResidualRealSecondDerivative N u L =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
      filter_upwards [Iio_mem_nhds hleft] with z hz
      exact dictionaryResidualRealSecondDerivative_eq_zero_of_left N u (le_of_lt hz)
    exact continuousAt_const.congr_of_eventuallyEq hev
  by_cases hleftEq : y = -L
  · subst y
    exact continuousAt_dictionaryResidualRealSecondDerivative_left_endpoint N u hL
  have hgtLeft : -L < y := lt_of_le_of_ne (le_of_not_gt hleft) (Ne.symm hleftEq)
  by_cases hneg : y < 0
  · have hev : dictionaryResidualRealSecondDerivative N u L =ᶠ[𝓝 y]
        dictionaryResidualNegativeBranchSecondDerivative N u L := by
      filter_upwards [Ioo_mem_nhds hgtLeft hneg] with z hz
      exact dictionaryResidualRealSecondDerivative_eq_negativeBranchSecondDerivative N u hL
        (le_of_lt hz.1) (le_of_lt hz.2)
    exact (continuous_dictionaryResidualNegativeBranchSecondDerivative N u L).continuousAt.congr_of_eventuallyEq hev
  by_cases hzero : y = 0
  · subst y
    exact continuousAt_dictionaryResidualRealSecondDerivative_zero N u hL
  have hypos : 0 < y := lt_of_le_of_ne (le_of_not_gt hneg) (Ne.symm hzero)
  by_cases hpos : y < L
  · have hev : dictionaryResidualRealSecondDerivative N u L =ᶠ[𝓝 y]
        dictionaryResidualPositiveBranchSecondDerivative N u L := by
      filter_upwards [Ioo_mem_nhds hypos hpos] with z hz
      exact dictionaryResidualRealSecondDerivative_eq_positiveBranchSecondDerivative N u hL
        (le_of_lt hz.1) (le_of_lt hz.2)
    exact (continuous_dictionaryResidualPositiveBranchSecondDerivative N u L).continuousAt.congr_of_eventuallyEq hev
  by_cases hrightEq : y = L
  · subst y
    exact continuousAt_dictionaryResidualRealSecondDerivative_right_endpoint N u hL
  · have hright : L < y := lt_of_le_of_ne (le_of_not_gt hpos) (Ne.symm hrightEq)
    have hev : dictionaryResidualRealSecondDerivative N u L =ᶠ[𝓝 y] (fun _ : ℝ => 0) := by
      filter_upwards [Ioi_mem_nhds hright] with z hz
      exact dictionaryResidualRealSecondDerivative_eq_zero_of_right N u hL (le_of_lt hz)
    exact continuousAt_const.congr_of_eventuallyEq hev

/-- The rank-one-regularized physical residual is globally `C²`. -/
@[fun_prop] theorem contDiff_two_dictionaryResidualReal
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ 2 (dictionaryResidualReal N u L) := by
  have hdiff : Differentiable ℝ (dictionaryResidualReal N u L) :=
    fun y => (hasDerivAt_dictionaryResidualReal N u hL y).differentiableAt
  have hderiv : deriv (dictionaryResidualReal N u L) =
      dictionaryResidualRealDerivative N u L := by
    funext y
    exact (hasDerivAt_dictionaryResidualReal N u hL y).deriv
  have hdiff1 : Differentiable ℝ (dictionaryResidualRealDerivative N u L) :=
    fun y => (hasDerivAt_dictionaryResidualRealDerivative N u hL y).differentiableAt
  have hderiv1 : deriv (dictionaryResidualRealDerivative N u L) =
      dictionaryResidualRealSecondDerivative N u L := by
    funext y
    exact (hasDerivAt_dictionaryResidualRealDerivative N u hL y).deriv
  have hcd1 : ContDiff ℝ 1 (dictionaryResidualRealDerivative N u L) := by
    rw [contDiff_one_iff_deriv]
    rw [hderiv1]
    exact ⟨hdiff1, continuous_dictionaryResidualRealSecondDerivative N u hL⟩
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl]
  refine (contDiff_succ_iff_deriv).2 ⟨hdiff, ?_, ?_⟩
  · simp
  · rw [hderiv]
    exact hcd1

/-! ## Compact support and complex adapter -/

/-- The residual support stays inside the original aperture. -/
theorem dictionaryResidualReal_support_subset
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    Function.support (dictionaryResidualReal N u L) ⊆ Icc (-L) L := by
  intro y hy
  have habs : |y| ≤ L := by
    by_contra h
    have hlt : L < |y| := lt_of_not_ge h
    exact hy (dictionaryResidualReal_eq_zero_of_lt_abs N u hL hlt)
  exact abs_le.mp habs

/-- The residual is compactly supported. -/
theorem dictionaryResidualReal_hasCompactSupport
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (dictionaryResidualReal N u L) := by
  refine HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc ?_
  intro y hy
  by_contra hzero
  exact hy (dictionaryResidualReal_support_subset N u hL hzero)

/-- Complex-valued wrapper in exactly the codomain expected by `EF_lit`. -/
def dictionaryResidualTest
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) (L : ℝ) : ℝ → ℂ :=
  fun y => (dictionaryResidualReal N u L y : ℂ)

/-- The complex residual wrapper is `C²`. -/
theorem contDiff_two_dictionaryResidualTest
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ 2 (dictionaryResidualTest N u L) := by
  have hreal := contDiff_two_dictionaryResidualReal N u hL
  simpa [dictionaryResidualTest, Function.comp_def] using
    Complex.ofRealCLM.contDiff.comp hreal

/-- The complex residual wrapper is compactly supported in the same aperture. -/
theorem dictionaryResidualTest_hasCompactSupport
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    HasCompactSupport (dictionaryResidualTest N u L) := by
  refine HasCompactSupport.intro (K := Icc (-L) L) isCompact_Icc ?_
  intro y hy
  by_contra hzero
  have hr : dictionaryResidualReal N u L y ≠ 0 := by
    intro hz
    apply hzero
    simp [dictionaryResidualTest, hz]
  exact hy (dictionaryResidualReal_support_subset N u hL hr)

/-- Production admissibility package for the smooth residual component. -/
theorem dictionaryResidualTest_admissible
    (N : ℕ) (u : Fin (2 * N + 1) → ℝ) {L : ℝ} (hL : 0 < L) :
    ContDiff ℝ 2 (dictionaryResidualTest N u L) ∧
      HasCompactSupport (dictionaryResidualTest N u L) :=
  ⟨contDiff_two_dictionaryResidualTest N u hL,
    dictionaryResidualTest_hasCompactSupport N u hL⟩

end Zeta23.CCM
