import Zeta23.CCM.Step123OutputData
import Zeta23.CCM.NativeWeilResponseBounds
import Zeta23.CCM.CanonicalPoleNeutralTrialResidualChannels
import Zeta23.CCM.Step123PhysicalImageIdentity

/-!
# Source-uniform upper control of the actual detector shift eta

From negative ORIGINAL unit detector depth D=exp(beta L), the true
mixed Weil identity, physical H1 finite-mode bound, and the same
admissible selection, derive an explicit universal upper bound on eta.
This is a compatibility estimate, not an RH closing estimate and not
a selected-ground inverse bound. The original detector is not replaced
by its selected ground.

This module is a new candidate until compiler and axiom audit complete.
-/

noncomputable section

open MeasureTheory Set Complex
open scoped Topology

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- The full-line support of the literal physical finite image lies
in the actual [0,L] aperture, with its true normalized coefficients. -/
private theorem step123_finite_source_support
    (σ : ReversalParity) {L : ℝ} (hL : 0 < L) (Kd : ℕ)
    (p : nativePoleNeutralParitySpace σ L Kd) :
    tsupport (finitePhysicalSynthesis L Kd
      (canonicalNativeCoefficientInclusion σ L Kd p)) ⊆
      Icc (0 : ℝ) L := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  apply hx
  unfold finitePhysicalSynthesis
  rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hnot]

/-- eta is bounded by the *actual physical Weil form* and the full
finite-frequency H1 factor. The source-only constant is the already
constructed native bilinear C_Q; no off-line zero enters the proof. -/
theorem originalDetector_eta_source_upper :
    ∃ C_Q : ℝ, 0 < C_Q ∧
      ∀ (β : ℝ) (σ : ReversalParity) (a : ℝ)
        (out : Step123NativeOutput β σ a),
        out.retained.state.selection.eta ≤
          (C_Q / 2) * (1 + fixedOriginalSincTrialAperture a) *
          Real.exp (fixedOriginalSincTrialAperture a / 2) *
          (1 + (2 * Real.pi *
            (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) /
              fixedOriginalSincTrialAperture a) ^ 2) := by
  obtain ⟨C_Q, hC, hWeil⟩ := nativeWeilResponse_bilinear_bound
  refine ⟨C_Q, hC, ?_⟩
  intro β σ a out
  let L := fixedOriginalSincTrialAperture a
  let Kd := originalDetectorQuarticCutoff L
  let p := out.retained.state.detector
  let f := finitePhysicalSynthesis L Kd
    (canonicalNativeCoefficientInclusion σ L Kd p)
  let n := nativePhysicalH1Norm f
  let b := Real.sqrt (1 + (2 * Real.pi * Kd / L) ^ 2)
  have hfLegal : canonicalNativeCoefficientInclusion σ L Kd p ∈
      euclideanBoundaryFlatSubspace Kd := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal σ L Kd p
  have hfC : ContDiff ℝ 2 f :=
    contDiff_localizedFiniteVector_of_boundaryFlat Kd _ out.aperture_pos
      ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat Kd _).mp hfLegal)
  have hfSupport : tsupport f ⊆ Icc (0 : ℝ) L :=
    step123_finite_source_support σ out.aperture_pos Kd p
  have hH1 : n ≤ b := by
    have h := canonicalNativePhysicalSynthesis_H1_bound σ
      out.aperture_pos Kd p
    dsimp only [n, f, b]
    rw [out.retained.state.detector_unit, mul_one] at h
    exact h
  have hn : 0 ≤ n := nativePhysicalH1Norm_nonneg f
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hbb : n * n ≤ b * b := by
    calc
      n * n ≤ b * n := mul_le_mul_of_nonneg_right hH1 hn
      _ ≤ b * b := mul_le_mul_of_nonneg_left hH1 hb
  let A := nativePoleNeutralParityCanonical σ L Kd
  have hMix : Zeta23.zetaZeroConfig.W f f = inner ℂ p (A p) :=
    canonicalNativePhysicalSynthesis_mixed_Weil σ out.aperture_pos Kd p p
  have hSym : inner ℂ (A p) p = inner ℂ p (A p) :=
    canonicalPoleNeutralTrial_operator_isSymmetric σ L Kd p p
  have hDeep : (Zeta23.zetaZeroConfig.W f f).re ≤
      -Real.exp (β * L) := by
    rw [hMix, ← hSym]
    exact out.retained.state.detector_depth
  have hDepthNorm : Real.exp (β * L) ≤ ‖Zeta23.zetaZeroConfig.W f f‖ := by
    have hneg : Real.exp (β * L) ≤ -(Zeta23.zetaZeroConfig.W f f).re := by
      linarith
    exact hneg.trans ((neg_le_abs _).trans (Complex.abs_re_le_norm _))
  have hW := hWeil L f f out.aperture_pos.le hfC hfC hfSupport hfSupport
  have hScale : 0 ≤ C_Q * (1 + L) * Real.exp (L / 2) := by
    have hL : 0 ≤ L := out.aperture_pos.le
    positivity
  have hBound : ‖Zeta23.zetaZeroConfig.W f f‖ ≤
      (C_Q * (1 + L) * Real.exp (L / 2)) * (b * b) := by
    calc
      _ ≤ (C_Q * (1 + L) * Real.exp (L / 2)) * (n * n) := by
        simpa only [n, mul_assoc] using hW
      _ ≤ (C_Q * (1 + L) * Real.exp (L / 2)) * (b * b) :=
        mul_le_mul_of_nonneg_left hbb hScale
  have hb2 : b * b = 1 + (2 * Real.pi * Kd / L) ^ 2 := by
    dsimp [b]
    simpa only [pow_two] using
      (Real.sq_sqrt (show
        0 ≤ 1 + (2 * Real.pi * Kd / L) ^ 2 by positivity))
  have hD : Real.exp (β * L) ≤ C_Q * (1 + L) *
      Real.exp (L / 2) * (1 + (2 * Real.pi * Kd / L) ^ 2) := by
    calc
      _ ≤ ‖Zeta23.zetaZeroConfig.W f f‖ := hDepthNorm
      _ ≤ (C_Q * (1 + L) * Real.exp (L / 2)) * (b * b) := hBound
      _ = _ := by rw [hb2]
  have hEta := out.retained.state.selection.eta_upper
  calc
    out.retained.state.selection.eta ≤ Real.exp (β * L) / 2 := hEta.le
    _ ≤ (C_Q * (1 + L) * Real.exp (L / 2) *
      (1 + (2 * Real.pi * Kd / L) ^ 2)) / 2 := by
      exact div_le_div_of_nonneg_right hD (by norm_num)
    _ = (C_Q / 2) * (1 + L) * Real.exp (L / 2) *
      (1 + (2 * Real.pi * Kd / L) ^ 2) := by ring

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetector_eta_source_upper
