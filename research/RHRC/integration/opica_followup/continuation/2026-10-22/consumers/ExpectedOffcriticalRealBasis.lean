import Zeta23.OPICAFollowup.FiniteSpanSeparation

noncomputable section
open Set MeasureTheory Complex
open scoped Topology SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan
open Zeta23.OPICAFollowup.OffcriticalRealBasis
namespace IndependentOffcriticalRealBasis

lemma singleton_physical_parts {ρ : ℂ} (hz : riemannZeta ρ=0)
    (h0 : 0<ρ.re) (h1 : ρ.re<1) (c : ℂ) (φ : 𝓢(ℝ,ℂ)) :
    (FiniteSpan.zeroJetRealSpan [(c,ρ,0)]).distributionOfLinearGrowth
      (zeroJetRealSpan_growth _ (valid_singleton _ (validZeroth hz h0 h1 c))) φ =
      (c.re : ℂ)*(normalizedZeroMeasureJet ρ 0).rePart.distributionOfLinearGrowth
        ((normalizedZeroMeasureJet ρ 0).re_hasLinearGrowth
          (normalizedZeroMeasureJet_hasLinearGrowth h0 h1 (zero_ne_half hz)
            (one_le_zeroJetOrder hz (strip_ne_one h1)))) φ -
      (c.im : ℂ)*(normalizedZeroMeasureJet ρ 0).imPart.distributionOfLinearGrowth
        ((normalizedZeroMeasureJet ρ 0).im_hasLinearGrowth
          (normalizedZeroMeasureJet_hasLinearGrowth h0 h1 (zero_ne_half hz)
            (one_le_zeroJetOrder hz (strip_ne_one h1)))) φ := by
  rw [singleton_realification hz h0 h1 c φ,normalizedZeroMeasureJet_conj h0 h1 (zero_ne_half hz)]
  change (c*(_+I*_) + starRingEnd ℂ c * starRingEnd ℂ (_+I*_))/2 = _
  simp only [LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply,
    complexSchwartzConj_apply,integral_conj,map_add,map_sub,map_mul,Complex.conj_conj,Complex.conj_I]
  conv_lhs => rw [←Complex.re_add_im c]
  simp only [map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
  ring_nf
  simp only [Complex.I_sq]
  ring

theorem actual_real_imaginary_pair_independent {ρ : ℂ} (hz : riemannZeta ρ=0)
    (h0 : 0<ρ.re) (h1 : ρ.re<1) (hk : (ρ*(1-ρ)).im≠0) :
    LinearIndependent ℝ ![
      (normalizedZeroMeasureJet ρ 0).rePart.distributionOfLinearGrowth
        ((normalizedZeroMeasureJet ρ 0).re_hasLinearGrowth
          (normalizedZeroMeasureJet_hasLinearGrowth h0 h1 (zero_ne_half hz)
            (one_le_zeroJetOrder hz (strip_ne_one h1)))),
      (normalizedZeroMeasureJet ρ 0).imPart.distributionOfLinearGrowth
        ((normalizedZeroMeasureJet ρ 0).im_hasLinearGrowth
          (normalizedZeroMeasureJet_hasLinearGrowth h0 h1 (zero_ne_half hz)
            (one_le_zeroJetOrder hz (strip_ne_one h1))))] := by
  have h := canonicalBasis_independent hz h0 h1 hk
  convert h using 1
  funext i
  fin_cases i <;> ext φ
  · simpa [canonicalBasis] using (singleton_physical_parts hz h0 h1 1 φ).symm
  · simpa [canonicalBasis] using (singleton_physical_parts hz h0 h1 (-I) φ).symm

theorem actual_two_coefficient_euclidean_negative_budget {ρ : ℂ}
    (hz : riemannZeta ρ=0) (h0 : 0<ρ.re) (h1 : ρ.re<1) (hk : (ρ*(1-ρ)).im≠0) :
    ∃ cρ : ℝ, 0<cρ ∧ ∀ a b : ℝ,
      cρ*Real.sqrt (a^2+b^2) ≤
        ∫ x in (Set.range (fun m : ℤ => (m : ℝ)))ᶜ, sincSquared x
          ∂(actualZeroJetSum [((a : ℂ),ρ,0),((b : ℂ)*(-I),ρ,0)]).rePart.negative := by
  exact canonical_pair_negative_mass_budget hz h0 h1 hk

theorem actual_no_nonzero_positive_combination {ρ : ℂ}
    (hz : riemannZeta ρ=0) (h0 : 0<ρ.re) (h1 : ρ.re<1) (hk : (ρ*(1-ρ)).im≠0)
    (a b : ℝ)
    (hpos : (actualZeroJetSum [((a : ℂ),ρ,0),((b : ℂ)*(-I),ρ,0)]).rePart.OffLatticeNonnegative) :
    a=0 ∧ b=0 := by
  exact canonical_pair_no_positive_combination hz h0 h1 hk a b hpos

lemma actual_offcritical_kappa {ρ : ℂ} (hz : riemannZeta ρ=0)
    (h0 : 0<ρ.re) (h1 : ρ.re<1) (hre : ρ.re≠1/2) : (spectralKappa ρ).im≠0 := by
  have him : ρ.im≠0 := by
    intro him
    have heq : ρ=(ρ.re : ℂ) := by
      apply Complex.ext <;> simp [him]
    exact Zeta23.ExceptionalZero.riemannZeta_ne_zero_of_real_critical_strip h0 h1 (heq ▸ hz)
  have heq : (spectralKappa ρ).im=(1-2*ρ.re)*ρ.im := by
    simp only [spectralKappa,Complex.mul_im,Complex.sub_re,Complex.sub_im,
      Complex.one_re,Complex.one_im]
    ring
  rw [heq]
  exact mul_ne_zero (by intro he; apply hre; linarith) him

/-- An actual off-critical strip zero supplies the nonreal κ hypothesis:
no separate nonzero-ordinate or basis-independence assumption is required. -/
theorem actual_offcritical_negative_mass_restriction {ρ : ℂ}
    (hz : riemannZeta ρ=0) (h0 : 0<ρ.re) (h1 : ρ.re<1) (hre : ρ.re≠1/2) :
    ∃ cρ : ℝ, 0<cρ ∧ ∀ a b : ℝ,
      (cρ*Real.sqrt (a^2+b^2) ≤
        ∫ x in (Set.range (fun m : ℤ => (m : ℝ)))ᶜ, sincSquared x
          ∂(actualZeroJetSum [((a : ℂ),ρ,0),((b : ℂ)*(-I),ρ,0)]).rePart.negative) ∧
      ((actualZeroJetSum [((a : ℂ),ρ,0),((b : ℂ)*(-I),ρ,0)]).rePart.OffLatticeNonnegative →
        a=0 ∧ b=0) := by
  have hk := actual_offcritical_kappa hz h0 h1 hre
  obtain ⟨c,hc,hbound⟩ := actual_two_coefficient_euclidean_negative_budget hz h0 h1 hk
  exact ⟨c,hc,fun a b => ⟨hbound a b,actual_no_nonzero_positive_combination hz h0 h1 hk a b⟩⟩

theorem actual_offcritical_real_imaginary_pair_independent {ρ : ℂ} (hz : riemannZeta ρ=0)
    (h0 : 0<ρ.re) (h1 : ρ.re<1) (hre : ρ.re≠1/2) :
    LinearIndependent ℝ ![
      (normalizedZeroMeasureJet ρ 0).rePart.distributionOfLinearGrowth
        ((normalizedZeroMeasureJet ρ 0).re_hasLinearGrowth
          (normalizedZeroMeasureJet_hasLinearGrowth h0 h1 (zero_ne_half hz)
            (one_le_zeroJetOrder hz (strip_ne_one h1)))),
      (normalizedZeroMeasureJet ρ 0).imPart.distributionOfLinearGrowth
        ((normalizedZeroMeasureJet ρ 0).im_hasLinearGrowth
          (normalizedZeroMeasureJet_hasLinearGrowth h0 h1 (zero_ne_half hz)
            (one_le_zeroJetOrder hz (strip_ne_one h1))))] := by
  exact actual_real_imaginary_pair_independent hz h0 h1 (actual_offcritical_kappa hz h0 h1 hre)

#print axioms IndependentOffcriticalRealBasis.actual_offcritical_real_imaginary_pair_independent
#print axioms IndependentOffcriticalRealBasis.actual_offcritical_kappa
#print axioms IndependentOffcriticalRealBasis.actual_offcritical_negative_mass_restriction
#print axioms IndependentOffcriticalRealBasis.actual_real_imaginary_pair_independent
#print axioms IndependentOffcriticalRealBasis.actual_two_coefficient_euclidean_negative_budget
#print axioms IndependentOffcriticalRealBasis.actual_no_nonzero_positive_combination
end IndependentOffcriticalRealBasis


