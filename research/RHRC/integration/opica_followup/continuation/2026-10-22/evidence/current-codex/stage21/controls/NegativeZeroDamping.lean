import Zeta23.OPICAFollowup.Consumers
open MeasureTheory
open Zeta23 Zeta23.CCM Zeta23.OPICAFollowup
example (theta_zero : nativeZeroDisplacementSup=0) :
    MemLp (nativeOriginalDampedPrimeField 0) 2 volume := by
  exact originalPrimeField_allDampedL2_of_native_theta_zero theta_zero 0 (by norm_num)
