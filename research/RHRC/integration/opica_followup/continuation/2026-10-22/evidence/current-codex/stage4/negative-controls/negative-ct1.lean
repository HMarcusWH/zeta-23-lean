import Zeta23.OPICAFollowup.NearGapLimits
theorem bad_gap_edge_mass {L : ℝ} (hL : 0 < L) (hu : L < Real.log 2) :
    (Zeta23.OPICAFollowup.nearGapCombFamily L).positive.real ({Real.exp (-L)} : Set ℝ) = Real.exp (-L) ∧
      (Zeta23.OPICAFollowup.nearGapCombFamily L).negative ({Real.exp (-L)} : Set ℝ) = 0 :=
  Zeta23.OPICAFollowup.nearGapCombFamily_gap_edge_atom hL hu
theorem bad_wider_gap (L : ℝ) (hL : 0 < L) (hu : L < Real.log 2) :
    Zeta23.OPICAFollowup.hasNearGap (Zeta23.OPICAFollowup.nearGapCombFamily L) 1 :=
  (Zeta23.OPICAFollowup.dilation_near_gap_family L hL hu).2.2.2.2.2.1
