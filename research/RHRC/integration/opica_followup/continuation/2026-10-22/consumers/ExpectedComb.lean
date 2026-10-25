import Zeta23.OPICAFollowup.DilatedComb

/-! Independent full-type and actual-domain consumers for the original comb root. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal
namespace Zeta23.OPICAFollowup

theorem expected_dilated_comb_fourier :
    ∀ t : ℝ,
      (∀ R : ℝ, 0≤R → dilatedCombMeasure t (Icc (-R) R)≤
        ENNReal.ofReal (Real.exp (t/2)*(3+2*Real.exp (-t)*R))) ∧
      (∀ f : SchwartzMap ℝ ℂ, Summable (fun n : ℤ => f (Real.exp t*(n:ℝ))) ∧
        dilatedCombDistribution t f=(Real.exp (t/2):ℂ)*∑' n : ℤ, f (Real.exp t*(n:ℝ))) ∧
      𝓕 (dilatedCombDistribution t)=dilatedCombDistribution (-t) :=
  dilated_comb_fourier

theorem expected_comb_actual_carrier (t : ℝ) :
    dilatedCombMeasure t=
      ENNReal.ofReal (Real.exp (t/2)) •
        Measure.map (fun n : ℤ => Real.exp t*(n:ℝ)) (Measure.count : Measure ℤ) := rfl

theorem expected_comb_origin_amplitude (t : ℝ) :
    dilatedCombMeasure t ({0} : Set ℝ)=ENNReal.ofReal (Real.exp (t/2)) :=
  dilatedCombMeasure_origin t

theorem expected_comb_unit_selfdual : 𝓕 (dilatedComb 0)=dilatedComb 0 := by
  simpa only [neg_zero] using (dilated_comb_fourier 0).2.2

theorem expected_comb_positive_negative_lattice (t : ℝ) (n : ℤ) :
    scaledLatticePoint t (-n)=-scaledLatticePoint t n := by
  simp [scaledLatticePoint]

theorem expected_comb_negative_dilation :
    𝓕 (dilatedComb (-Real.log 2))=dilatedComb (Real.log 2) := by
  simpa only [neg_neg] using (dilated_comb_fourier (-Real.log 2)).2.2

theorem expected_comb_absolute_pairing (t : ℝ) (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => ‖f (Real.exp t*(n:ℝ))‖) ∧
      dilatedComb t f=combPairing t f :=
  ⟨(dilatedComb_schwartz_summable t f).norm,dilatedComb_apply t f⟩

#print axioms Zeta23.OPICAFollowup.dilated_comb_fourier
#print axioms Zeta23.OPICAFollowup.expected_dilated_comb_fourier
#print axioms Zeta23.OPICAFollowup.dilatedCombMeasure_origin
#print axioms Zeta23.OPICAFollowup.expected_comb_absolute_pairing
#print axioms Zeta23.OPICAFollowup.expected_comb_negative_dilation

end Zeta23.OPICAFollowup
