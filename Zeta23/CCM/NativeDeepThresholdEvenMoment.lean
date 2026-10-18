import Zeta23.CCM.NativeDeepThresholdSimplicity
import Zeta23.CCM.CanonicalPoleNeutralSimpleEvenTie

noncomputable section

namespace Zeta23.CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-!
The actual least-crossing geometry constructs the simplicity needed by
the native fourth-moment rigidity theorem. Thus a selected even ground
has nonzero fourth moment at either a strict-even bottom or a parity tie.
Nonvanishing of the corrected source still requires a strict odd-bottom
comparison; no corrected-source nonvanishing is asserted at a tie.
-/

/-- Every nonzero actual even ground at the selected actual global bottom
has nonzero fourth moment, without a supplied simplicity hypothesis. -/
theorem nativeDeepThreshold_even_ground_momentFour_ne_zero {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (hD : 0 < D) (s : NativeDeepThresholdGroundData L Kd D hL)
    (u : poleNeutralEvenSubspace L s.cutoff) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L s.cutoff u = (s.lam : ℂ) • u) :
    centeredMoment s.cutoff 4 (evenBoundaryFlatRawCoefficients s.cutoff u.val) ≠ 0 := by
  have hodd : s.lam ≤ poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty := by
    rw [s.lam_is_actual_global]
    exact min_le_right _ _
  exact poleNeutral_momentFour_ne_zero_of_simple_even_of_le_odd_bottom
    hL s.cutoff s.cutoff_nonempty s.lam u hu0 hu hodd
    (nativeDeepThreshold_even_ground_simple hD s u hu0 hu)

/-- The corrected source of an actual selected even ground is nonzero
when its actual spectral value is strictly below the actual odd bottom. -/
theorem nativeDeepThreshold_strictEven_ground_source_ne_zero {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL)
    (hstrict : s.lam < poleNeutralOddRayleighBottom L s.cutoff hL s.cutoff_nonempty)
    (u : poleNeutralEvenSubspace L s.cutoff) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L s.cutoff u = (s.lam : ℂ) • u) :
    poleNeutralCorrectedCubicSource L s.cutoff u ≠ 0 :=
  poleNeutral_even_eigen_source_ne_zero_of_lt_odd_bottom
    hL s.cutoff s.cutoff_nonempty s.lam hstrict u hu0 hu

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeDeepThreshold_even_ground_momentFour_ne_zero
#print axioms Zeta23.CCM.nativeDeepThreshold_strictEven_ground_source_ne_zero
