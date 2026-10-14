import Zeta23.CCM.OriginalDetectorNativeForcing
import Zeta23.CCM.NativeWeilResponseBounds

/-!
# Source-uniform original-detector shifted-forcing error

The H1 norm controls the COMPLETE Weil term (Archimedean, poles and
two prime translations) while the eta shift is controlled separately
by the physical L2 isometry and exact zero-translate correlation.

No Schur upper law, zeta-zero, eigenvector overlap or RH premise
is introduced. The actual source error e = finite image - original
smooth detector must be instantiated by its original-source transport
theorem; this generic lemma does not create that transport itself.
-/

noncomputable section

open MeasureTheory Set Complex

namespace Zeta23.CCM

/-- Exact full-line L2 norm for any actual native pole-neutral finite
physical test, independent of its chosen parity. -/
theorem originalDetector_nativeFinitePhysicalL2_norm (σ : ReversalParity)
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : nativePoleNeutralParitySpace σ L K) :
    nativePhysicalL2Norm
      (finitePhysicalSynthesis L K
        (canonicalNativeCoefficientInclusion σ L K v)) = ‖v‖ := by
  unfold nativePhysicalL2Norm
  rw [finitePhysicalSynthesis_energy hL K
    (canonicalNativeCoefficientInclusion σ L K v)]
  rw [(canonicalNativeCoefficientInclusion σ L K).norm_map]
  exact Real.sqrt_sq (norm_nonneg v)

/-- The actual projection-error estimate, stated in mixed finite
physical tests. This gives the exact C_Q(1+L)exp(L/2)H1 finite-mode
factor plus eta, without treating the total Schur sign as positive.

An admissible original detector instantiates eta≥0 and the actual
finite-minus-smooth H1 error; no such source data is supplied in
the proof of this generic operator bound. -/
theorem originalDetector_forcing_error_bound :
    ∃ C_Q : ℝ, 0 < C_Q ∧
      ∀ (σ : ReversalParity) (L : ℝ) (hL : 0 < L) (K : ℕ)
        (eta : ℝ) (heta : 0 ≤ eta)
        (e : ℝ → ℂ) (he : ContDiff ℝ 2 e)
        (hs : tsupport e ⊆ Icc (0 : ℝ) L)
        (v : nativePoleNeutralParitySpace σ L K),
        ‖Zeta23.zetaZeroConfig.W e
          (finitePhysicalSynthesis L K
            (canonicalNativeCoefficientInclusion σ L K v)) +
           (eta : ℂ) * EF.weilTest e
             (finitePhysicalSynthesis L K
               (canonicalNativeCoefficientInclusion σ L K v)) 0‖ ≤
        (C_Q * (1 + L) * Real.exp (L / 2) *
            Real.sqrt (1 + (2 * Real.pi * K / L) ^ 2) + eta) *
          nativePhysicalH1Norm e * ‖v‖ := by
  obtain ⟨C_Q, hC, hW⟩ := originalDetector_forcingWeilError_bound
  refine ⟨C_Q, hC, ?_⟩
  intro σ L hL K eta heta e he hs v
  let f : ℝ → ℂ :=
    finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v)
  have hvlegal : canonicalNativeCoefficientInclusion σ L K v ∈
      euclideanBoundaryFlatSubspace K := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal σ L K v
  have hv : ContDiff ℝ 2 f :=
    contDiff_localizedFiniteVector_of_boundaryFlat K _ hL
      ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat K _).mp hvlegal)
  have hfc : HasCompactSupport f := localizedFiniteVector_hasCompactSupport L K _
  have hec : HasCompactSupport e :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport e) hs
  have hL2 : nativePhysicalL2Norm f = ‖v‖ :=
    originalDetector_nativeFinitePhysicalL2_norm σ hL K v
  have hPair : ‖EF.weilTest e f 0‖ ≤ nativePhysicalH1Norm e * ‖v‖ := by
    calc
      ‖EF.weilTest e f 0‖ ≤
          nativePhysicalL2Norm e * nativePhysicalL2Norm f :=
        nativeWeilTest_norm_le_L2 he.continuous hv.continuous hec hfc 0
      _ = nativePhysicalL2Norm e * ‖v‖ := by rw [hL2]
      _ ≤ nativePhysicalH1Norm e * ‖v‖ :=
        mul_le_mul_of_nonneg_right (nativePhysicalL2Norm_le_H1 e) (norm_nonneg _)
  have hEta : ‖(eta : ℂ) * EF.weilTest e f 0‖ ≤
      eta * (nativePhysicalH1Norm e * ‖v‖) := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg heta]
      using mul_le_mul_of_nonneg_left hPair heta
  have hWeil := hW σ L hL K e he hs v
  change ‖Zeta23.zetaZeroConfig.W e f + (eta : ℂ) * EF.weilTest e f 0‖ ≤ _
  calc
    ‖Zeta23.zetaZeroConfig.W e f + (eta : ℂ) * EF.weilTest e f 0‖ ≤
        ‖Zeta23.zetaZeroConfig.W e f‖ +
          ‖(eta : ℂ) * EF.weilTest e f 0‖ := norm_add_le _ _
    _ ≤ C_Q * (1 + L) * Real.exp (L / 2) * nativePhysicalH1Norm e *
        (Real.sqrt (1 + (2 * Real.pi * K / L) ^ 2) * ‖v‖) +
          eta * (nativePhysicalH1Norm e * ‖v‖) := add_le_add hWeil hEta
    _ = _ := by ring

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetector_nativeFinitePhysicalL2_norm
#print axioms Zeta23.CCM.originalDetector_forcing_error_bound
