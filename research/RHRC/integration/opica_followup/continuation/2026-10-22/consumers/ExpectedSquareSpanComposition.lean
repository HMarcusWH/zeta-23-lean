import Zeta23.OPICAFollowup.Consumers

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup.SquareSpanExpected
open Zeta23.OPICA

/-- Literal actual zero profile at plateau one, actual multiplicity-bounded
finite zero-jet measures, and an arbitrary Euclidean-temperate lattice measure. -/
theorem full_actual_square_jet_lattice_composition (ρ:ℂ) (hz:riemannZeta ρ=0)
    (h0:0<ρ.re) (h1:ρ.re<1) (data:List (ℂ × ℂ × ℕ))
    (hdata:∀j∈data,riemannZeta j.2.1=0 ∧ 0<j.2.1.re ∧ j.2.1.re<1 ∧
      j.2.2<zeroJetOrder j.2.1)
    (σ:LocallyFiniteComplexMeasure) [σ.totalVariation.HasTemperateGrowth]
    (hσ:σ.totalVariation (Set.range (fun n:ℤ=>(n:ℝ)))ᶜ=0) :
    let hp := zero_profile_regular_selfdual ρ hz h0 h1
    let hv : Tendsto (zeroProfile ρ) (cocompact ℝ) (𝓝 0) := by
      rw [←hp.2.2.2.2.2.1]; exact Real.zero_at_infty_fourier _
    let Tτ := (squareGapJordan (zeroProfile ρ) 1 hp.2.1).distributionOfLinearGrowth
      (squareGapJordan_growth hp.2.1 hv 1)
    let Tν := (FiniteSpan.actualZeroJetSum data).rePart.distributionOfLinearGrowth
      (FiniteSpan.zeroJetRealSpan_growth data hdata)
    𝓕 (Tτ+Tν+SquarePhysicalSupport.correctionDistribution σ) ≠
      Tτ+Tν+SquarePhysicalSupport.correctionDistribution σ := by
  exact actual_square_zero_jet_lattice_barrier ρ hz h0 h1 data hdata σ hσ

end Zeta23.OPICAFollowup.SquareSpanExpected
#print axioms Zeta23.OPICAFollowup.SquareSpanExpected.full_actual_square_jet_lattice_composition
