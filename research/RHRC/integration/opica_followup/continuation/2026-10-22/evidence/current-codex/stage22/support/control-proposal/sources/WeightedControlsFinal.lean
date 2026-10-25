import Zeta23.OPICAFollowup.FiniteSpanSeparation

noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace IndependentWeightedBudgetControls
open Zeta23.OPICA Zeta23.OPICAFollowup.FixedBudgetSupport

/-- An auxiliary measure control, not an actual zero measure. It satisfies
growth and gap while the sinc weight loses its lattice atom. Selfduality is
therefore essential to the faithful actual-span argument. -/
def diracTwo : LocallyFiniteSignedMeasure where
  positive := Measure.dirac 2
  negative := 0
  positive_locallyFinite := inferInstance
  negative_locallyFinite := inferInstance
  mutuallySingular := Measure.MutuallySingular.zero_right

theorem diracTwo_growth : diracTwo.HasLinearGrowth := by
  refine ⟨1,by norm_num,fun R hR => ?_⟩
  have h : (Measure.dirac (2 : ℝ)).real (Icc (-R) R) ≤
      (Measure.dirac (2 : ℝ)).real univ :=
    measureReal_mono (subset_univ _) (by finiteness)
  simp only [diracTwo,LocallyFiniteSignedMeasure.totalVariation,add_zero]
  simpa using h.trans (by simp; linarith)

theorem diracTwo_gap : diracTwo.HasUnitGap := by
  constructor <;> norm_num [diracTwo,Measure.dirac_apply']

theorem diracTwo_nonzero_positive : diracTwo.positive ≠ 0 := by
  intro h
  have := congrArg (fun μ : Measure ℝ => μ univ) h
  norm_num [diracTwo] at this

theorem diracTwo_weighted_zero : sincWeightedSigned diracTwo diracTwo_growth=0 := by
  ext E hE
  rw [sincWeightedSigned_apply _ _ _ hE]
  have hs : sincSquared (2 : ℝ)=0 := sincSquared_int_zero (by norm_num : (2 : ℤ) ≠ 0)
  simp only [diracTwo,integral_zero_measure,sub_zero,VectorMeasure.zero_apply]
  rw [←integral_indicator hE,integral_dirac]
  simp [Set.indicator_apply,hs]

theorem diracTwo_not_selfdual : ¬ diracTwo.FourierSelfdual diracTwo_growth := by
  intro h
  exact diracTwo_nonzero_positive
    ((sincWeightedSigned_zero_iff_zero diracTwo diracTwo_growth h diracTwo_gap).mp
      diracTwo_weighted_zero).1

#print axioms IndependentWeightedBudgetControls.diracTwo_weighted_zero
#print axioms IndependentWeightedBudgetControls.diracTwo_not_selfdual
end IndependentWeightedBudgetControls
