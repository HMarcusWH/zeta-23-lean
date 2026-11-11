import Zeta23.CCM.NativeDeepThresholdGround
import Zeta23.OPICARound4.ArithmeticFrontier.MomentSlices

/-!
# The least-crossing cutoff when the first native space is already deep

`NativeDeepThresholdGroundData` stores the least Fourier cutoff `K ≥ 3` at which
the global pole-neutral bottom falls below `-eta`, with `D/3 < eta < D/2`. That
record allows the cutoff to be `3`, in which case both predecessor spaces at
cutoff `2` have dimension zero.

This module records the exact finite statement behind the round-seven paper
note: if the cutoff-3 bottom is already below `-D/2` (for instance because one
unit vector of either one-dimensional cutoff-3 parity space has energy below
`-D/2`), then every such packet has cutoff exactly `3`, and its predecessor is
empty. Whether a deep cutoff-3 vector exists at a given aperture is an analytic
question that this module does not address. RH and Step 4 remain OPEN.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier

open CCM

/-- A packet forces `0 < D`, because `D/3 < eta < D/2`. -/
theorem nativeDeepThresholdGround_depth_pos {L : ℝ} {Kd : ℕ} {D : ℝ} {hL : 0 < L}
    (g : NativeDeepThresholdGroundData L Kd D hL) : 0 < D := by
  have h1 := g.eta_lower
  have h2 := g.eta_upper
  linarith

/-- **Least crossing at the first native cutoff.** If the cutoff-3 global bottom is
below `-D/2`, the stored least-crossing cutoff is `3`. -/
theorem nativeDeepThresholdGround_cutoff_eq_three_of_bottom_three_lt
    {L : ℝ} {Kd : ℕ} {D : ℝ} {hL : 0 < L} (g : NativeDeepThresholdGroundData L Kd D hL)
    (h3 : poleNeutralGlobalRayleighBottom L 3 hL le_rfl < -(D / 2)) :
    g.cutoff = 3 := by
  by_contra hne
  have hlt : 3 < g.cutoff := lt_of_le_of_ne g.cutoff_nonempty (Ne.symm hne)
  have hKd : 3 ≤ Kd := le_trans g.cutoff_nonempty g.cutoff_le_detector
  have hb := g.earlier_bottoms 3 le_rfl hlt
  have hgap := nativeDeepThresholdGap_pos D Kd (nativeDeepThresholdGround_depth_pos g) hKd
  have hη := g.eta_upper
  linarith

/-- In that case both predecessor spaces are zero-dimensional. -/
theorem nativeDeepThresholdGround_predecessor_empty_of_bottom_three_lt
    {L : ℝ} {Kd : ℕ} {D : ℝ} {hL : 0 < L} (g : NativeDeepThresholdGroundData L Kd D hL)
    (h3 : poleNeutralGlobalRayleighBottom L 3 hL le_rfl < -(D / 2)) :
    Module.finrank ℂ (poleNeutralEvenSubspace L 2) = 0 ∧
      Module.finrank ℂ (poleNeutralOddSubspace L 2) = 0 :=
  g.first_predecessor_empty (nativeDeepThresholdGround_cutoff_eq_three_of_bottom_three_lt g h3)

/-- One deep unit vector in the even cutoff-3 space puts the least crossing at `3`. -/
theorem nativeDeepThresholdGround_cutoff_eq_three_of_even_trial
    {L : ℝ} {Kd : ℕ} {D : ℝ} {hL : 0 < L} (g : NativeDeepThresholdGroundData L Kd D hL)
    (u : poleNeutralEvenSubspace L 3) (hu : ‖u‖ = 1)
    (he : evenNativeEnergy L 3 u < -(D / 2)) :
    g.cutoff = 3 := by
  refine nativeDeepThresholdGround_cutoff_eq_three_of_bottom_three_lt g ?_
  have hb := poleNeutralEvenRayleighBottom_mul_norm_sq_le hL 3 le_rfl u
  rw [hu, one_pow, mul_one] at hb
  have hmin : poleNeutralGlobalRayleighBottom L 3 hL le_rfl ≤
      poleNeutralEvenRayleighBottom L 3 hL le_rfl := min_le_left _ _
  unfold evenNativeEnergy at he
  linarith

/-- One deep unit vector in the odd cutoff-3 space puts the least crossing at `3`. -/
theorem nativeDeepThresholdGround_cutoff_eq_three_of_odd_trial
    {L : ℝ} {Kd : ℕ} {D : ℝ} {hL : 0 < L} (g : NativeDeepThresholdGroundData L Kd D hL)
    (v : poleNeutralOddSubspace L 3) (hv : ‖v‖ = 1)
    (he : oddNativeEnergy L 3 v < -(D / 2)) :
    g.cutoff = 3 := by
  refine nativeDeepThresholdGround_cutoff_eq_three_of_bottom_three_lt g ?_
  have hb := poleNeutralOddRayleighBottom_mul_norm_sq_le hL 3 le_rfl v
  rw [hv, one_pow, mul_one] at hb
  have hmin : poleNeutralGlobalRayleighBottom L 3 hL le_rfl ≤
      poleNeutralOddRayleighBottom L 3 hL le_rfl := min_le_right _ _
  unfold oddNativeEnergy at he
  linarith

end Zeta23.OPICARound4.ArithmeticFrontier
