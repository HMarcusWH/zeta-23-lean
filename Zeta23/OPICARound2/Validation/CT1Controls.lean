import Zeta23.OPICARound2.CT1Controls

noncomputable section
open Set Filter
open scoped Topology
open Zeta23.OPICAFollowup

namespace Zeta23.OPICARound2.Validation

theorem ct1_actual_family_identity (L : ℝ) :
    nearGapCombDistribution L = dilatedCombDistribution L + dilatedCombDistribution (-L)
      - (2*(Real.cosh (L/2):ℂ)) • dilatedCombDistribution 0 := by
  simpa [nearGapExplicitDilationDistribution] using nearGapCombDistribution_eq_explicit L

theorem ct1_expected_scalar_classification (L : ℕ→ℝ) (c : ℕ→ℂ)
    (nonzero : ∀ j, L j ≠ 0) (zeroLimit : Tendsto L atTop (𝓝 0))
    (U : TemperedDistribution ℝ ℂ)
    (limitOnTests : ∀ φ : SchwartzMap ℝ ℂ,
      Tendsto (fun j => c j * nearGapCombDistribution (L j) φ) atTop (𝓝 (U φ))) :
    ∃ a : ℂ, Tendsto (fun j => c j * (L j : ℂ)^2) atTop (𝓝 a) ∧
      U = a • ct1NormalizedLimit :=
  ct1_scalar_limit_classification L c nonzero zeroLimit U limitOnTests

theorem ct1_expected_integer_neighborhood_order_zero (L : ℕ→ℝ) (c : ℕ→ℂ)
    (nonzero : ∀ j, L j ≠ 0) (zeroLimit : Tendsto L atTop (𝓝 0))
    (U : TemperedDistribution ℝ ℂ)
    (limitOnTests : ∀ φ : SchwartzMap ℝ ℂ,
      Tendsto (fun j => c j * nearGapCombDistribution (L j) φ) atTop (𝓝 (U φ)))
    (n : ℤ) (hn : n ≠ 0)
    (localBound : ∃ r : ℝ, 0<r ∧ ∃ C : ℝ, ∀ φ : SchwartzMap ℝ ℂ,
      tsupport φ ⊆ Icc ((n:ℝ)-r) ((n:ℝ)+r) →
      ‖U φ‖ ≤ C*SchwartzMap.seminorm ℝ 0 0 φ) : U=0 :=
  ct1_order_zero_scalar_limit_is_zero L c nonzero zeroLimit U limitOnTests n hn localBound

theorem ct1_actual_nonzero_test :
    ct1NormalizedLimit (ct1BumpTest 1 (ε:=1/4) (by norm_num))=2 := by
  simpa using ct1NormalizedLimit_bumpTest 1 (ε:=1/4) (by norm_num) (by norm_num)

theorem ct1_actual_limit_delta_series (φ : SchwartzMap ℝ ℂ) :
    HasSum (fun n : ℤ => ((n:ℂ)^2 • TemperedDistribution.derivCLM ℂ
      (TemperedDistribution.derivCLM ℂ (TemperedDistribution.delta (n:ℝ))) -
      (2*(n:ℂ)) • TemperedDistribution.derivCLM ℂ
        (TemperedDistribution.delta (n:ℝ))) φ) (ct1NormalizedLimit φ) :=
  ct1NormalizedLimit_hasSum_delta φ

#print axioms Zeta23.OPICARound2.ct1_scalar_limit_classification
#print axioms Zeta23.OPICARound2.ct1_scalar_order_zero_at_integer
#print axioms Zeta23.OPICARound2.ct1_order_zero_scalar_limit_is_zero

end Zeta23.OPICARound2.Validation
