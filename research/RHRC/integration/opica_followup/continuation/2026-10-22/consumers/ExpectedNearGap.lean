import Zeta23.OPICAFollowup.NearGapLimits

/- Independent HT2 consumers for the actual locally finite Jordan measure.
The controlled weak limit and both CT1 family/normalized-limit roots remain OPEN. -/
noncomputable section
open Set MeasureTheory
open scoped SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace OPICAStageTwoExpected

theorem expected_near_gap_full_physical_type (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth)
    (hself : 𝓕 (nu.distributionOfLinearGrowth hnu)=nu.distributionOfLinearGrowth hnu)
    (a R d : ℝ) (ha : 0<a) (ha1 : a≤1)
    (hgapPos : nu.positive (Ioo (-a) a)=0)
    (hgapNeg : nu.negative (Ioo (-a) a)=0)
    (hoff : nu.negative (Set.range (fun n : ℤ => (n:ℝ)))ᶜ=0)
    (hR : 1≤R) (hd : 0<d) (hdhalf : d≤1/2) :
    nu.negative {x : ℝ | |x|≤R ∧ d≤Metric.infDist x (Set.range (fun n : ℤ => (n:ℝ)))}=0 ∧
    nu.positive.real {x : ℝ | |x|≤R ∧ d≤Metric.infDist x (Set.range (fun n : ℤ => (n:ℝ)))}≤
      (Real.pi^2*R^2/(4*d^2))*(1-a)*(nu.positive+nu.negative).real (Icc (-1) 1) := by
  exact near_gap_mass_bound nu hnu hself ha ha1 ⟨hgapPos,hgapNeg⟩ hoff hR hd hdhalf

theorem expected_common_linear_constant (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    (C a R d : ℝ) (_hC : 0≤C)
    (hlinear : ∀ S : ℝ, 0≤S → nu.totalVariation.real (Icc (-S) S)≤C*(1+S))
    (ha : 0<a) (ha1 : a≤1) (hgap : hasNearGap nu a)
    (hoff : nu.OffLatticeNonnegative) (hR : 1≤R) (hd : 0<d) (hdhalf : d≤1/2) :
    nu.positive.real (signedBudgetRegion R d)≤
      (Real.pi^2*R^2*C/(2*d^2))*(1-a) := by
  have hlocal : nu.totalVariation.real (Icc (-1) 1)≤2*C := by
    simpa only [show (1:ℝ)+1=2 by norm_num,mul_comm] using hlinear 1 (by norm_num)
  calc
    _ ≤ (Real.pi^2*R^2/(4*d^2))*(1-a)*nu.totalVariation.real (Icc (-1) 1) :=
      (near_gap_mass_bound nu hnu hself ha ha1 hgap hoff hR hd hdhalf).2
    _ ≤ (Real.pi^2*R^2/(4*d^2))*(1-a)*(2*C) :=
      mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = _ := by field_simp; ring

theorem expected_critical_gap_zero_region (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    (hgap : nu.HasUnitGap) (hoff : nu.OffLatticeNonnegative)
    (R d : ℝ) (hR : 1≤R) (hd : 0<d) (hdhalf : d≤1/2) :
    nu.negative (signedBudgetRegion R d)=0 ∧
    nu.positive.real (signedBudgetRegion R d)=0 := by
  have h := near_gap_mass_bound nu hnu hself (a:=1) (by norm_num) le_rfl hgap hoff hR hd hdhalf
  refine ⟨h.1,le_antisymm ?_ (by positivity)⟩
  simpa only [sub_self,mul_zero,zero_mul] using h.2

theorem expected_half_distance_endpoint (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    (a R : ℝ) (ha : 0<a) (ha1 : a≤1) (hgap : hasNearGap nu a)
    (hoff : nu.OffLatticeNonnegative) (hR : 1≤R) :
    nu.positive.real (signedBudgetRegion R (1/2))≤
      (Real.pi^2*R^2)*(1-a)*nu.totalVariation.real (Icc (-1) 1) := by
  have h := (near_gap_mass_bound nu hnu hself ha ha1 hgap hoff hR
    (by norm_num : (0:ℝ)<1/2) le_rfl).2
  norm_num only [show (4:ℝ)*(1/2)^2=1 by norm_num,div_one] at h
  exact h

end OPICAStageTwoExpected
#print axioms Zeta23.OPICAFollowup.near_gap_mass_bound
#print axioms OPICAStageTwoExpected.expected_near_gap_full_physical_type
#print axioms OPICAStageTwoExpected.expected_common_linear_constant
#print axioms OPICAStageTwoExpected.expected_critical_gap_zero_region
#print axioms OPICAStageTwoExpected.expected_half_distance_endpoint
