import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNormalization
import Zeta23.CCM.NativeDeepThresholdGround

/-!
The phase-independent native selector for C-Schur. Both actual padded
source phases must be nonzero and literally normalized. Kd is the fixed
quartic cutoff and D is exp(beta L). No zero rho, source energy assumption,
Schur upper estimate, selected parity, or closing law enters this predicate.
-/

noncomputable section

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

structure AdmissibleDetectorSelector (β L eta : ℝ) (K : ℕ) : Prop where
  aperture_large : 4 < L
  even_nonzero : originalDetectorPaddedFinitePhaseVector 1 L fixedOriginalSincLobeCenter
    (by linarith [aperture_large]) ≠ 0
  odd_nonzero : originalDetectorPaddedFinitePhaseVector (-1) L fixedOriginalSincLobeCenter
    (by linarith [aperture_large]) ≠ 0
  even_unit : ‖originalDetectorPaddedFinitePhaseUnitVector 1 L fixedOriginalSincLobeCenter
    (by linarith [aperture_large])‖ = 1
  odd_unit : ‖originalDetectorPaddedFinitePhaseUnitVector (-1) L fixedOriginalSincLobeCenter
    (by linarith [aperture_large])‖ = 1
  cutoff_nonempty : 3 ≤ K
  cutoff_le_detector : K ≤ originalDetectorQuarticCutoff L
  eta_lower : Real.exp (β * L) / 3 < eta
  eta_upper : eta < Real.exp (β * L) / 2
  selected_bottom : poleNeutralGlobalRayleighBottom L K
    (by linarith [aperture_large]) cutoff_nonempty ≤
      -eta - nativeDeepThresholdGap (Real.exp (β * L)) (originalDetectorQuarticCutoff L)
  earlier_bottoms : ∀ J : ℕ, (hJ : 3 ≤ J) → J < K →
    -eta + nativeDeepThresholdGap (Real.exp (β * L)) (originalDetectorQuarticCutoff L) ≤
      poleNeutralGlobalRayleighBottom L J (by linarith [aperture_large]) hJ
  first_predecessor_empty : K = 3 →
    Module.finrank ℂ (poleNeutralEvenSubspace L 2) = 0 ∧
      Module.finrank ℂ (poleNeutralOddSubspace L 2) = 0

/-- All selector conditions come from the actual source normalizations
and actual least-crossing data. No detector-energy condition is added to
the predicate that the phase-uniform upper-bound cut will quantify over. -/
theorem admissibleDetectorSelector_of_actual_ground {β L : ℝ} {hL : 0 < L}
    (hlarge : 4 < L)
    (he0 : originalDetectorPaddedFinitePhaseVector 1 L fixedOriginalSincLobeCenter hL ≠ 0)
    (ho0 : originalDetectorPaddedFinitePhaseVector (-1) L fixedOriginalSincLobeCenter hL ≠ 0)
    (he1 : ‖originalDetectorPaddedFinitePhaseUnitVector 1 L fixedOriginalSincLobeCenter hL‖ = 1)
    (ho1 : ‖originalDetectorPaddedFinitePhaseUnitVector (-1) L fixedOriginalSincLobeCenter hL‖ = 1)
    (s : NativeDeepThresholdGroundData L (originalDetectorQuarticCutoff L)
      (Real.exp (β * L)) hL) :
    AdmissibleDetectorSelector β L s.eta s.cutoff := by
  refine {
    aperture_large := hlarge
    even_nonzero := he0
    odd_nonzero := ho0
    even_unit := he1
    odd_unit := ho1
    cutoff_nonempty := s.cutoff_nonempty
    cutoff_le_detector := s.cutoff_le_detector
    eta_lower := s.eta_lower
    eta_upper := s.eta_upper
    selected_bottom := ?_
    earlier_bottoms := s.earlier_bottoms
    first_predecessor_empty := s.first_predecessor_empty }
  rw [← s.lam_is_actual_global]
  exact s.lam_depth

end Zeta23.CCM

#print axioms Zeta23.CCM.admissibleDetectorSelector_of_actual_ground
