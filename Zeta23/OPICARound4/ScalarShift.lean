import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

noncomputable section

namespace Zeta23.OPICARound4

/-- A common scalar shift does not change the relative intertwining defect.
This is a countermodel control, NOT an authorized modification of the zeta source. -/
theorem common_scalar_shift_invariant
    {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [AddCommGroup F] [Module ℂ F]
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F)
    (D : E →ₗ[ℂ] F) (c : ℂ) :
    (B - c • LinearMap.id).comp D -
      D.comp (A - c • LinearMap.id) = B.comp D - D.comp A := by
  ext x
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, map_sub, map_smul]
  abel

/-- The corrected source row is shift-invariant only on an orthogonal input.
No absolute spectral-sign inference follows. -/
theorem orthogonal_source_row_shift
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (M : F →ₗ[ℂ] F) (c : ℂ) (h u : F)
    (hu : inner ℂ h u = 0) :
    inner ℂ h ((M - c • (LinearMap.id : F →ₗ[ℂ] F)) u) = inner ℂ h (M u) := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_sub_right, inner_smul_right, hu, mul_zero, sub_zero]

end Zeta23.OPICARound4
