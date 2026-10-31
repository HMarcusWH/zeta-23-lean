import Zeta23.CCM.CanonicalPoleNeutralShiftedSecular
import Zeta23.OPICARound4.WitnessNorms

noncomputable section

namespace Zeta23.OPICARound4
open CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- Absolute energy is fixed by the canonical equation-(4.4) matrix on the same
physical vector. Relative intertwining alone does not supply this identity. -/
theorem even_absolute_energy_anchor (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    (inner ℂ (poleNeutralEvenCompressedCanonical L K u) u).re =
      Complex.re (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin u.val.val) u.val.val) :=
  congrArg Complex.re (inner_poleNeutralEvenCompressedCanonical_self L K u)

theorem odd_absolute_energy_anchor (L : ℝ) (K : ℕ)
    (u : poleNeutralOddSubspace L K) :
    (inner ℂ (poleNeutralOddCompressedCanonical L K u) u).re =
      Complex.re (inner ℂ ((canonicalSourceMatrix L K).toEuclideanLin u.val.val) u.val.val) :=
  congrArg Complex.re (inner_poleNeutralOddCompressedCanonical_self L K u)

/-- A common shift changes the absolute zero level by its full physical norm. -/
theorem real_scalar_shift_energy {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E →ₗ[ℂ] E) (c : ℝ) (u : E) :
    (inner ℂ ((A - (c : ℂ) • (LinearMap.id : E →ₗ[ℂ] E)) u) u).re =
      (inner ℂ (A u) u).re - c * ‖u‖ ^ 2 := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_sub_left, Complex.sub_re]
  rw [re_inner_ofReal_smul_self]

/-- Exact scalar-shift control: identical relative defect coexists with negative
absolute energy. This is a synthetic countermodel, not a modified zeta source. -/
theorem scalar_shift_negative_control :
    let A : ℂ →ₗ[ℂ] ℂ := LinearMap.id
    let B : ℂ →ₗ[ℂ] ℂ := LinearMap.id
    let D : ℂ →ₗ[ℂ] ℂ := LinearMap.id
    B.comp D - D.comp A =
      (B - (2 : ℂ) • LinearMap.id).comp D -
        D.comp (A - (2 : ℂ) • LinearMap.id) ∧
    0 < (inner ℂ (A 1) 1).re ∧
    (inner ℂ ((A - (2 : ℂ) • (LinearMap.id : ℂ →ₗ[ℂ] ℂ)) (1 : ℂ)) (1 : ℂ)).re < 0 := by
  dsimp
  constructor
  · ext z
    simp
  · norm_num [inner, RCLike.inner_apply]

end Zeta23.OPICARound4
