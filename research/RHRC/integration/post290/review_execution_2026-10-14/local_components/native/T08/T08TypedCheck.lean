import Zeta23.CCM.NativeIntegerDriveFiniteOrderBounds

set_option pp.fullNames true
set_option pp.deepTerms true
set_option pp.proofs.withType true
set_option pp.maxSteps 1000000

#check @Zeta23.CCM.nativeOriginalIntegerDrive_finiteOrder_bound
#check @Zeta23.CCM.nativeOriginalIntegerDrive_rapid_bound

example (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |Zeta23.CCM.nativeOriginalIntegerDrive t| ≤ C * Real.exp (-A * t) :=
  Zeta23.CCM.nativeOriginalIntegerDrive_rapid_bound A hA
