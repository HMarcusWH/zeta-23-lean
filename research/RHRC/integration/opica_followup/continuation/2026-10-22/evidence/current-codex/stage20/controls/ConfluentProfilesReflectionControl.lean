import Zeta23.OPICAFollowup.ConfluentProfiles

noncomputable section
open MeasureTheory Complex
open scoped SchwartzMap FourierTransform
namespace OPICAGroupedReflectionControl
open Zeta23.OPICAFollowup

/-- Counting an actual zero and its reflection as separate k=0 columns
produces a genuine dependence of the actual physical embedded measures. -/
theorem reflection_duplicate_actual_not_independent (ρ : ℂ)
    (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    let hr0 : 0 < (1 - ρ).re := by simp; linarith
    let hr1 : (1 - ρ).re < 1 := by simp; linarith
    let hh := zero_ne_half hz
    let hhr : 1 - ρ ≠ 1 / 2 := by intro h; apply hh; linear_combination -h
    let hk : 0 < zeroJetOrder ρ := by
      exact (Nat.zero_lt_one.trans_le (one_le_zeroJetOrder hz (strip_ne h0 h1).2))
    let hkr : 0 < zeroJetOrder (1 - ρ) := by rw [zeroJetOrder_one_sub h0 h1]; exact hk
    ¬LinearIndependent ℂ ![
      (normalizedZeroMeasureJet ρ 0).distributionOfLinearGrowth
        (normalizedZeroMeasureJet_hasLinearGrowth h0 h1 hh hk),
      (normalizedZeroMeasureJet (1 - ρ) 0).distributionOfLinearGrowth
        (normalizedZeroMeasureJet_hasLinearGrowth hr0 hr1 hhr hkr)] := by
  dsimp only
  intro hLI
  have hr0 : 0 < (1 - ρ).re := by simp; linarith
  have hr1 : (1 - ρ).re < 1 := by simp; linarith
  have hh := zero_ne_half hz
  have hhr : 1 - ρ ≠ 1 / 2 := by intro h; apply hh; linear_combination -h
  have hk : 0 < zeroJetOrder ρ :=
    Nat.zero_lt_one.trans_le (one_le_zeroJetOrder hz (strip_ne h0 h1).2)
  have hkr : 0 < zeroJetOrder (1 - ρ) := by rw [zeroJetOrder_one_sub h0 h1]; exact hk
  have hT :
      (normalizedZeroMeasureJet (1 - ρ) 0).distributionOfLinearGrowth
        (normalizedZeroMeasureJet_hasLinearGrowth hr0 hr1 hhr hkr) =
        (normalizedZeroMeasureJet ρ 0).distributionOfLinearGrowth
          (normalizedZeroMeasureJet_hasLinearGrowth h0 h1 hh hk) := by
    ext φ
    simp only [LocallyFiniteComplexMeasure.distributionOfLinearGrowth_apply,
      normalizedZeroMeasureJet_one_sub]
  have hi : (0 : Fin 2) = 1 := hLI.injective (by simpa using hT.symm)
  norm_num at hi

#print axioms OPICAGroupedReflectionControl.reflection_duplicate_actual_not_independent
end OPICAGroupedReflectionControl

