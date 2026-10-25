import Zeta23.OPICAFollowup.FiniteSpanSeparation

noncomputable section
open Set MeasureTheory Complex
open scoped Topology SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan
open Zeta23.OPICAFollowup.OffcriticalRealBasis
namespace OffcriticalControls

/-- The collision is an identity of the actual measures. At real κ,
conjugation is either identity or the existing ρ↦1−ρ reflection. -/
lemma real_kappa_conjugate_same_measure (ρ : ℂ) (hk : (spectralKappa ρ).im=0) :
    normalizedZeroMeasureJet (starRingEnd ℂ ρ) 0 = normalizedZeroMeasureJet ρ 0 := by
  have hm : (1-2*ρ.re)*ρ.im=0 := by
    calc
      (1-2*ρ.re)*ρ.im = (spectralKappa ρ).im := by
        simp only [spectralKappa,Complex.mul_im,Complex.sub_re,Complex.sub_im,
          Complex.one_re,Complex.one_im]
        ring
      _ = 0 := hk
  rcases mul_eq_zero.mp hm with hre|him
  · have hc : starRingEnd ℂ ρ=1-ρ := by
      apply Complex.ext <;> simp <;> linarith
    rw [hc,normalizedZeroMeasureJet_one_sub]
  · have hc : starRingEnd ℂ ρ=ρ := by
      apply Complex.ext <;> simp [him]
    rw [hc]

/-- Positive boundary control: the actual canonical imaginary direction
vanishes whenever κ is real, so nonreal κ cannot be deleted from the pair theorem. -/
theorem canonical_imaginary_zero_of_real_kappa {ρ : ℂ} (hz : riemannZeta ρ=0)
    (h0 : 0<ρ.re) (h1 : ρ.re<1) (hk : (spectralKappa ρ).im=0) :
    (FiniteSpan.zeroJetRealSpan [(-I,ρ,0)]).distributionOfLinearGrowth
      (zeroJetRealSpan_growth _ (valid_singleton _ (validZeroth hz h0 h1 (-I)))) = 0 := by
  ext φ
  rw [singleton_realification hz h0 h1 (-I) φ,real_kappa_conjugate_same_measure ρ hk]
  simp only [map_neg,Complex.conj_I,neg_neg,ContinuousLinearMap.zero_apply]
  ring

theorem canonical_pair_dependent_of_real_kappa {ρ : ℂ} (hz : riemannZeta ρ=0)
    (h0 : 0<ρ.re) (h1 : ρ.re<1) (hk : (spectralKappa ρ).im=0) :
    ¬ LinearIndependent ℝ (fun i =>
      (FiniteSpan.zeroJetRealSpan (canonicalBasis ρ i)).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (canonicalBasis_valid hz h0 h1 i))) := by
  intro hind
  apply LinearIndependent.ne_zero (1 : Fin 2) hind
  simpa [canonicalBasis] using canonical_imaginary_zero_of_real_kappa hz h0 h1 hk

#print axioms OffcriticalControls.real_kappa_conjugate_same_measure
#print axioms OffcriticalControls.canonical_imaginary_zero_of_real_kappa
#print axioms OffcriticalControls.canonical_pair_dependent_of_real_kappa
end OffcriticalControls
