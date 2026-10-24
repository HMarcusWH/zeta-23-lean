import Zeta23.OPICAFollowup.SquareDefect

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ContDiff
namespace Zeta23.OPICAFollowup

/-- Expected rejection: support of an unrelated measure does not constrain T. -/
example (σ : LocallyFiniteComplexMeasure) (T : TemperedDistribution ℝ ℂ)
    (hσ : σ.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ=0)
    (φ : 𝓢(ℝ,ℂ)) (hφ : ∀ n : ℤ, φ n=0) : T φ=0 := by
  exact TemperedLatticeBridge.extension_annihilates_lattice_zero σ T hσ φ hφ

end Zeta23.OPICAFollowup
