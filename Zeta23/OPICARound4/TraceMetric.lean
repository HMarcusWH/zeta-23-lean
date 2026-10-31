import Zeta23.CCM.CanonicalPoleNeutralShiftedSecular
import Mathlib.LinearAlgebra.Trace
import Mathlib.Tactic

noncomputable section

namespace Zeta23.OPICARound4
open CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [FiniteDimensional ℂ F]

/-- Trace displacement of an algebraic rank-one transport. The transfer is an
arbitrary linear equivalence and carries no isometry premise. -/
theorem rank_one_trace_displacement
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (D : E ≃ₗ[ℂ] F)
    (g : F) (f : E →ₗ[ℂ] ℂ) (h : RankOneIntertwining A B D g f) :
    LinearMap.trace ℂ F B - LinearMap.trace ℂ E A = f (D.symm g) := by
  have hm : B - D.conj A = (f.comp D.symm.toLinearMap).smulRight g := by
    ext w
    simpa only [LinearMap.sub_apply, LinearEquiv.conj_apply,
      LinearMap.smulRight_apply, LinearMap.comp_apply, LinearEquiv.apply_symm_apply]
      using! h (D.symm w)
  have ht := congrArg (LinearMap.trace ℂ F) hm
  rw [map_sub, LinearMap.trace_conj', LinearMap.trace_smulRight] at ht
  exact ht

/-- Rank-two metric commutator written as a form identity. It retains both
nonunitary transfer costs; replacing D by a unitary is not licensed. -/
theorem rank_one_metric_identity
    (A : E →ₗ[ℂ] E) (B : F →ₗ[ℂ] F) (D : E ≃ₗ[ℂ] F)
    (g : F) (f : E →ₗ[ℂ] ℂ) (hB : B.IsSymmetric)
    (h : RankOneIntertwining A B D g f) (x y : E) :
    inner ℂ (D (A x)) (D y) - inner ℂ (D x) (D (A y)) =
      f y * inner ℂ (D x) g - star (f x) * inner ℂ g (D y) := by
  have hx : B (D x) = D (A x) + f x • g := (sub_eq_iff_eq_add').mp (h x)
  have hy : B (D y) = D (A y) + f y • g := (sub_eq_iff_eq_add').mp (h y)
  have hs := hB (D x) (D y)
  rw [hx, hy, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    starRingEnd_apply] at hs
  linear_combination hs

/-- S04 trace identity on the unchanged actual even-to-odd source. -/
theorem native_even_trace_displacement {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) :
    LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
      LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K) =
      poleNeutralCorrectedCubicSource L K
        ((poleNeutralIndexEquiv hL K (by omega)).symm (poleNeutralCubicCompressionVector L K)) := by
  simpa only [poleNeutralCorrectedCubicFunctional_apply] using!
    (rank_one_trace_displacement (E := poleNeutralEvenSubspace L K)
      (F := poleNeutralOddSubspace L K)
      (poleNeutralEvenCompressedCanonical L K) (poleNeutralOddCompressedCanonical L K)
      (poleNeutralIndexEquiv hL K (show 1 ≤ K by omega))
      (poleNeutralCubicCompressionVector L K) (poleNeutralCorrectedCubicFunctional L K)
      (canonicalPoleNeutralRankOneIntertwining hL K (by omega)))

/-- The adjoint branch has reversed trace displacement and its genuine minus
source. The even formula cannot be substituted by swapping parity labels. -/
theorem native_odd_trace_displacement {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) :
    LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K) -
      LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) =
      -poleNeutralCubicPairingFunctional L K
        ((poleNeutralIndexAdjointEquiv hL K hK).symm (poleNeutralCorrectedCubicRieszVector L K)) := by
  have hzero : RankOneIntertwining (poleNeutralOddCompressedCanonical L K)
      (poleNeutralEvenCompressedCanonical L K) (poleNeutralIndexAdjointEquiv hL K hK)
      (-poleNeutralCorrectedCubicRieszVector L K) (poleNeutralCubicPairingFunctional L K) := by
    intro w
    have ha := poleNeutral_adjoint_rankOne_identity hL K hK w
    change poleNeutralEvenCompressedCanonical L K ((poleNeutralIndexLinearMap hL K).adjoint w) -
      (poleNeutralIndexLinearMap hL K).adjoint (poleNeutralOddCompressedCanonical L K w) = _
    rw [smul_neg, ← ha]
    abel
  have hr := rank_one_trace_displacement
    (E := poleNeutralOddSubspace L K) (F := poleNeutralEvenSubspace L K)
    (poleNeutralOddCompressedCanonical L K) (poleNeutralEvenCompressedCanonical L K)
    (poleNeutralIndexAdjointEquiv hL K hK) (-poleNeutralCorrectedCubicRieszVector L K)
    (poleNeutralCubicPairingFunctional L K)
    hzero
  simpa only [map_neg] using! hr

end Zeta23.OPICARound4
