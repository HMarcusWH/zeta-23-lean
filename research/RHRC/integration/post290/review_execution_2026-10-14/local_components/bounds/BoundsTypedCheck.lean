import Zeta23.CCM.NativeWeilResponseBounds

set_option pp.proofs false
set_option pp.universes false

#check Zeta23.CCM.nativePaperFT_parseval_of_integrable_sq
#check Zeta23.CCM.nativePaperFT_weighted_sq_integrable
#check Zeta23.CCM.nativePaperFT_deriv_sq_integrable
#check Zeta23.CCM.nativePaperFT_H1_energy
#check Zeta23.CCM.nativePaperFT_H1_mixed_bound
#check Zeta23.CCM.nativePrimeMass_finite_bound
#check Zeta23.CCM.nativeWeilArchResponse_bilinear_bound
#check Zeta23.CCM.nativeWeilPoleResponse_bilinear_bound
#check Zeta23.CCM.nativeWeilPrimeCorrelation_bilinear_bound
#check Zeta23.CCM.nativeWeilResponse_bilinear_bound

#print axioms Zeta23.CCM.nativeWeilResponse_bilinear_bound

/- A direct consumer on the specified C2 physical test class. -/
example : ∃ C : ℝ, 0 < C ∧ ∀ (L : ℝ) (f v : ℝ → ℂ),
    0 ≤ L → ContDiff ℝ 2 f → ContDiff ℝ 2 v →
    tsupport f ⊆ Set.Icc (0 : ℝ) L → tsupport v ⊆ Set.Icc (0 : ℝ) L →
    ‖Zeta23.zetaZeroConfig.W f v‖ ≤ C * (1 + L) * Real.exp (L / 2) *
      Zeta23.CCM.nativePhysicalH1Norm f * Zeta23.CCM.nativePhysicalH1Norm v :=
  Zeta23.CCM.nativeWeilResponse_bilinear_bound
