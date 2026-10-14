import Zeta23.CCM.CanonicalDeepThresholdGap
import Zeta23.CCM.NativeDeepThresholdSimplicity

/-!
The canonical M12 interface composes the actual bottom-only gap selector,
least crossing, four predecessor inverses, and selected-parity simplicity.
The gap core lives below the actual trial-depth bridge to keep this
dependency direction acyclic. The original trial is supplied unchanged.
-/

noncomputable section

namespace Zeta23.CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

theorem exists_bottomAvoidingThreshold {L : ℝ} (hL : 0 < L)
    (Kd : ℕ) (hKd : 3 ≤ Kd) (D : ℝ) (hD : 0 < D) :
    ∃ eta : ℝ, D / 3 < eta ∧ eta < D / 2 ∧
      ∀ K : ℕ, (hK : 3 ≤ K) → K ≤ Kd →
        nativeDeepThresholdGap D Kd ≤ |poleNeutralGlobalRayleighBottom L K hL hK + eta| :=
  exists_nativeDeepThreshold_bottom_separator hL Kd hKd D hD

/-- The least crossing data includes its actual unit ground, earlier
bottom gaps, predecessor lower bounds, and empty first predecessor clause. -/
theorem exists_least_deepPoleNeutralCutoff {L : ℝ} (hL : 0 < L)
    (Kd : ℕ) (hKd : 3 ≤ Kd) (D : ℝ) (hD : 0 < D)
    (p : EuclideanSpace ℂ (Fin (2 * Kd + 1)))
    (hlegal : p ∈ euclideanBoundaryFlatSubspace Kd)
    (hpEven : canonicalPoleEvenFunctional L Kd p = 0)
    (hpOdd : canonicalPoleOddFunctional L Kd p = 0) (hpUnit : ‖p‖ = 1)
    (hpDepth : (inner ℂ ((canonicalSourceMatrix L Kd).toEuclideanLin p) p).re ≤ -D) :
    Nonempty (NativeDeepThresholdGroundData L Kd D hL) :=
  exists_nativeDeepThresholdGround_of_given_trial hL Kd hKd D hD
    p hlegal hpEven hpOdd hpUnit hpDepth

/-- Both ground-relative inverse bounds are 6(Kd-1)/D; the distinct
detector-shift inverses have bound 12(Kd-1)/D. None is assumed as input. -/
theorem deepThreshold_predecessor_inverse_bound {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL) :
    ∃ r : NativeDeepThresholdInverseData s,
      ‖r.evenGround.symm.toLinearMap.toContinuousLinearMap‖ ≤ 6 * ((Kd - 1 : ℕ) : ℝ) / D ∧
      ‖r.oddGround.symm.toLinearMap.toContinuousLinearMap‖ ≤ 6 * ((Kd - 1 : ℕ) : ℝ) / D ∧
      ‖r.evenDetector.symm.toLinearMap.toContinuousLinearMap‖ ≤ 12 * ((Kd - 1 : ℕ) : ℝ) / D ∧
      ‖r.oddDetector.symm.toLinearMap.toContinuousLinearMap‖ ≤ 12 * ((Kd - 1 : ℕ) : ℝ) / D := by
  let r := nativeDeepThresholdInverseData hD s
  exact ⟨r, r.evenGround_inverse_bound, r.oddGround_inverse_bound,
    r.evenDetector_inverse_bound, r.oddDetector_inverse_bound⟩

/-- Simplicity belongs to the actual selected parity. The statement
preserves the even/odd alternative and allows a tie between the parities. -/
theorem deepThreshold_selectedParity_simple {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL) :
    (Module.finrank ℂ (Module.End.eigenspace
        (poleNeutralEvenCompressedCanonical L s.cutoff) (s.lam : ℂ)) = 1 ∧
      ∃ u : poleNeutralEvenSubspace L s.cutoff, ‖u‖ = 1 ∧
        poleNeutralEvenCompressedCanonical L s.cutoff u = (s.lam : ℂ) • u) ∨
    (Module.finrank ℂ (Module.End.eigenspace
        (poleNeutralOddCompressedCanonical L s.cutoff) (s.lam : ℂ)) = 1 ∧
      ∃ w : poleNeutralOddSubspace L s.cutoff, ‖w‖ = 1 ∧
        poleNeutralOddCompressedCanonical L s.cutoff w = (s.lam : ℂ) • w) :=
  nativeDeepThreshold_selectedParity_simple hD s

end Zeta23.CCM

#print axioms Zeta23.CCM.exists_bottomAvoidingThreshold
#print axioms Zeta23.CCM.exists_least_deepPoleNeutralCutoff
#print axioms Zeta23.CCM.deepThreshold_predecessor_inverse_bound
#print axioms Zeta23.CCM.deepThreshold_selectedParity_simple
