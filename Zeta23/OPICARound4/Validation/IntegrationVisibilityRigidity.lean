import Zeta23.OPICARound4.VisibilityRigidity
import Mathlib.LinearAlgebra.Matrix.Hermitian

noncomputable section
namespace Zeta23.OPICARound4.Validation
open CCM
open scoped Matrix

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

set_option backward.isDefEq.respectTransparency false

theorem native_even_zero_residue_classification {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (β : GroupedSpectrum (poleNeutralOddCompressedCanonical L K))
    (hc : nativeEvenGroupedResidue hL K hK β = 0) :
    nativeOddGroupedProjector L K β (poleNeutralCubicCompressionVector L K) = 0 ∨
      ((poleNeutralCorrectedCubicFunctional L K).comp
        (poleNeutralIndexEquiv hL K (by omega)).symm.toLinearMap).comp
          (nativeOddGroupedProjector L K β) = 0 := by
  letI := poleNeutralEven_innerProductSpace L K
  letI := poleNeutralOdd_innerProductSpace L K
  have hh := (grouped_residue_zero_iff_input_or_output_invisible
    (E := poleNeutralEvenSubspace L K) (F := poleNeutralOddSubspace L K)
    (poleNeutralEvenCompressedCanonical_isSymmetric L K)
    (poleNeutralOddCompressedCanonical_isSymmetric L K)
    (poleNeutralIndexEquiv hL K (by omega)) (poleNeutralCubicCompressionVector L K)
    (poleNeutralCorrectedCubicFunctional L K)
    (canonicalPoleNeutralRankOneIntertwining hL K (by omega)) β).mp hc
  simpa only [GroupedInputInvisible, GroupedOutputInvisible, nativeOddGroupedProjector] using! hh

theorem native_odd_zero_residue_classification {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (β : GroupedSpectrum (poleNeutralEvenCompressedCanonical L K))
    (hc : nativeOddGroupedResidue hL K hK β = 0) :
    nativeEvenGroupedProjector L K β (-poleNeutralCorrectedCubicRieszVector L K) = 0 ∨
      ((poleNeutralCubicPairingFunctional L K).comp
        (poleNeutralIndexAdjointEquiv hL K hK).symm.toLinearMap).comp
          (nativeEvenGroupedProjector L K β) = 0 := by
  letI := poleNeutralEven_innerProductSpace L K
  letI := poleNeutralOdd_innerProductSpace L K
  have hh := (grouped_residue_zero_iff_input_or_output_invisible
    (E := poleNeutralOddSubspace L K) (F := poleNeutralEvenSubspace L K)
    (poleNeutralOddCompressedCanonical_isSymmetric L K)
    (poleNeutralEvenCompressedCanonical_isSymmetric L K)
    (poleNeutralIndexAdjointEquiv hL K hK) (-poleNeutralCorrectedCubicRieszVector L K)
    (poleNeutralCubicPairingFunctional L K) (native_odd_rank_one_unshifted hL K hK) β).mp hc
  simpa only [GroupedInputInvisible, GroupedOutputInvisible, nativeEvenGroupedProjector] using! hh

/-- General cross observations retain a genuine cancellation category. The
corresponding rank-one update is defective, so it lies outside the full model. -/
theorem general_cross_observation_cancellation :
    dotProduct (![1, -1] : Fin 2 → ℂ) (![1, 1] : Fin 2 → ℂ) = 0 ∧
    (![1, -1] : Fin 2 → ℂ) ≠ 0 ∧ (![1, 1] : Fin 2 → ℂ) ≠ 0 ∧
    (let N : Matrix (Fin 2) (Fin 2) ℂ := !![-1, 1; -1, 1];
      N = -Matrix.vecMulVec (![1, 1] : Fin 2 → ℂ) (![1, -1] : Fin 2 → ℂ) ∧
        N ≠ 0 ∧ N * N = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [dotProduct, Fin.sum_univ_two]
  · intro h
    have hh := congrFun h 0
    norm_num at hh
  · intro h
    have hh := congrFun h 0
    norm_num at hh
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.vecMulVec]
  · intro h
    have hh := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℂ => N 0 0) h
    norm_num at hh
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

#check @grouped_residue_zero_iff_input_or_output_invisible
#print axioms native_even_zero_residue_classification
#print axioms native_odd_zero_residue_classification
#print axioms general_cross_observation_cancellation

end Zeta23.OPICARound4.Validation
