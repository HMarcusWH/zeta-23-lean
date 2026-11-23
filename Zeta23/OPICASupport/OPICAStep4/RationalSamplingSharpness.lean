import Zeta23.OPICASupport.OPICAStep4.BoundaryFlatRationalSampling

/-!
# A sharpness control at cutoff two

One distinct nonpole sample does not suffice on the two-dimensional native
boundary-flat space.  These are exact complex-number equalities, not numerical
floating-point checks and not assertions about the Fourier exponential factor.
-/

noncomputable section

namespace Zeta23.OPICARound20

open CCM

def rationalSamplingSharpnessCoefficients : Fin 5 → ℂ := ![-5, 12, -6, -4, 3]

theorem rationalSamplingSharpness_boundaryFlat :
    BoundaryFlatCoefficients 2 rationalSamplingSharpnessCoefficients := by
  norm_num [BoundaryFlatCoefficients, centeredMoment, centeredIndex,
    rationalSamplingSharpnessCoefficients, Fin.sum_univ_succ]

theorem rationalSamplingSharpness_nonzero : rationalSamplingSharpnessCoefficients ≠ 0 := by
  intro h
  have hz := congrFun h (0 : Fin 5)
  norm_num [rationalSamplingSharpnessCoefficients] at hz

theorem rationalSamplingSharpness_zero_sample :
    finiteCauchySum (fun i => (centeredIndex 2 i : ℂ))
      rationalSamplingSharpnessCoefficients (1 / 2) = 0 := by
  norm_num [finiteCauchySum, centeredIndex, rationalSamplingSharpnessCoefficients,
    Fin.sum_univ_succ]

theorem rationalSamplingSharpness_nonzero_sample :
    finiteCauchySum (fun i => (centeredIndex 2 i : ℂ))
      rationalSamplingSharpnessCoefficients (3 / 2) ≠ 0 := by
  norm_num [finiteCauchySum, centeredIndex, rationalSamplingSharpnessCoefficients,
    Fin.sum_univ_succ]

theorem rationalSamplingSharpness_sample_is_not_pole :
    ∀ i : Fin 5, (1 / 2 : ℂ) ≠ (centeredIndex 2 i : ℂ) := by
  norm_num [Fin.forall_fin_succ, centeredIndex]

end Zeta23.OPICARound20
