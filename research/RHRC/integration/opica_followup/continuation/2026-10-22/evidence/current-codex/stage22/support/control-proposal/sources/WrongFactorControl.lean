import Zeta23.OPICAFollowup.NearGapLimits
open MeasureTheory
open Zeta23.OPICA Zeta23.OPICAFollowup
example {L : ℝ} (hL : 0 < L) (hlog : L < Real.log 2) :
    (nearGapCombFamily L).integral sincSquared =
      (Real.exp L - 1) / (Real.exp L) ^ (3 / 2 : ℝ) := by
  exact CT13Support.sinc_identity_original hL hlog
