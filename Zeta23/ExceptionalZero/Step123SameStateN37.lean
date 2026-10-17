import Zeta23.ExceptionalZero.Step123SameStateN14
import Zeta23.CCM.OriginalDetectorEtaControl

/-!
# N37: the actual projected forcing error at the quartic H1 rate

Field N37 (`forcing.error`) asks for the quantified projection error of the
actual shifted forcing, with its finite-mode factor and the stored shift
`eta` kept visible, composed with the actual quartic H1 error of the ONE
stored detector, under the same common threshold as N14.

Notation for a stored packet `out : Step123NativeOutput β σ a`:
`L = fixedOriginalSincTrialAperture a`, `K = out.retained.state.selection.cutoff`
(the stored selected cutoff), `eta = out.retained.state.selection.eta` (the
stored shift), `Kd = originalDetectorQuarticCutoff L` (the stored detector
cutoff), `e = out.physicalSourceError` and, for a predecessor test
`v : nativePoleNeutralParitySpace σ L (K - 1)`, `Φ v` its physical finite
synthesis.  The projected forcing error is
`‖W(e, Φ v) + eta * weilTest(e, Φ v, 0)‖`.

What is proved here:

* `step123NativeOutput_imageErrors_forcingError_commonThreshold`: source-only
  constants `C_Q, C_W > 0` and ONE threshold `L0 ≥ 4`, all chosen before any
  packet. `L0` is the N14 threshold: for every stored packet with
  `L0 ≤ L` the three N14 same-state image errors hold, the stored shift obeys
  `eta ≤ (C_W/2)(1+L)e^{L/2}(1+(2π Kd/L)^2)`, and for every predecessor
  test `v` the projected forcing error is at most
  `[C_Q(1+L)e^{L/2}√(1+(2π(K-1)/L)^2) + eta] · L^{17/2} e^{-c·r(L)} · ‖v‖`
  and at most
  `[C_Q(1+L)e^{L/2}√(1+(2π(K-1)/L)^2) + (C_W/2)(1+L)e^{L/2}(1+(2π Kd/L)^2)]
     · L^{17/2} e^{-c·r(L)} · ‖v‖`,
  where `c = originalDetectorRetainedDecayRate UniversalSinc.fixedScale` and
  `r = originalDetectorQuarticRootScale`.  This is the quartic H1 rate of
  `step123_originalSource_H1_concrete_rate` with its constants made explicit
  (`C = 1`, `c` as above), exactly as proved for the stored detector by N14.
* `step123NativeOutput_forcingError_quarticRate_commonThreshold` and
  `step123NativeOutput_forcingError_etaBound_commonThreshold`: the two
  forcing-error inequalities alone, with the same witnesses.  In the second
  form the right-hand side depends only on `L`, `K`, the source constants and
  `‖v‖` (`Kd` is a function of `L`).
* `step123NativeOutput_storedDetectorForcingError_etaBound_commonThreshold`:
  the same bound with `e` written literally as the physical synthesis of the
  stored detector `out.retained.state.detector` minus `out.originalTrial`.
* `exists_generatedStep123Output_forcingError_cofinal_atLateness`: for each
  actual off-line zero, admissible `β`, phase and lateness `R`, a generated
  packet of the existing producer whose aperture exceeds `max R L0`, so both
  forcing-error bounds apply to its stored native packet.

The constant `C_Q` is uniform over all packets (it is the constant of
`originalDetector_forcing_error_bound`), which is stronger than the
per-packet existential of `Step123NativeOutput.actualProjectedForcing_error_bound`.
No bridge identity, error bound, shift bound or branch consequence is a
hypothesis; the only inputs are the stored packet, the aperture lower bound
`L0 ≤ L` and the predecessor test `v`.

What is NOT proved here: no decay of the composed right-hand side (the
finite-mode and shift factors grow like `e^{L/2}` and `L^8 e^{L/2}` and are
not absorbed), no compact-inverse local duality, no C-Schur upper estimate,
no A-X/B-Y closure, no Step 4 law, no completion of the full 44-field
producer, no D2 gate, and no Riemann hypothesis.  The two phases are not
given a common aperture.
-/

noncomputable section

open MeasureTheory Set Complex

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- N37 together with N14 under ONE threshold.  The constants `C_Q`
(forcing bilinear bound) and `C_W` (Weil bilinear bound in the shift
control) and the threshold `L0` (the N14 threshold) are chosen before any
packet.  For every stored packet with `L0 ≤ L`, the three N14 same-state
image errors, the stored shift upper bound, and both forcing-error
bounds (with the stored `eta`, and with `eta` replaced by its proved
upper bound) hold at the quartic H1 rate. -/
theorem step123NativeOutput_imageErrors_forcingError_commonThreshold :
    ∃ C_Q C_W L0 : ℝ, 0 < C_Q ∧ 0 < C_W ∧ 4 ≤ L0 ∧
      ∀ {β : ℝ} {σ : ReversalParity} {a : ℝ}
        (out : Step123NativeOutput β σ a),
        L0 ≤ fixedOriginalSincTrialAperture a →
          (originalDetectorPhysicalH1Error
              (finitePhysicalSynthesis
                (fixedOriginalSincTrialAperture a)
                (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                (canonicalNativeCoefficientInclusion σ
                  (fixedOriginalSincTrialAperture a)
                  (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                  out.retained.state.detector))
              out.originalTrial ≤
            (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
              Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) ∧
          nativePhysicalH1Norm out.physicalSourceError ≤
            (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
              Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) ∧
          |(inner ℂ (nativePoleNeutralParityCanonical σ
                (fixedOriginalSincTrialAperture a)
                (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                out.retained.state.detector) out.retained.state.detector).re -
              (zetaZeroConfig.W out.originalTrial out.originalTrial).re| ≤
            (1 + fixedOriginalSincTrialAperture a) *
              (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
              Real.exp (fixedOriginalSincTrialAperture a / 2 -
                originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                  originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a))) ∧
          out.retained.state.selection.eta ≤
            (C_W / 2) * (1 + fixedOriginalSincTrialAperture a) *
              Real.exp (fixedOriginalSincTrialAperture a / 2) *
              (1 + (2 * Real.pi *
                (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) /
                  fixedOriginalSincTrialAperture a) ^ 2) ∧
          ∀ (v : nativePoleNeutralParitySpace σ
              (fixedOriginalSincTrialAperture a)
              (out.retained.state.selection.cutoff - 1)),
            ‖zetaZeroConfig.W out.physicalSourceError
                (finitePhysicalSynthesis
                  (fixedOriginalSincTrialAperture a)
                  (out.retained.state.selection.cutoff - 1)
                  (canonicalNativeCoefficientInclusion σ
                    (fixedOriginalSincTrialAperture a)
                    (out.retained.state.selection.cutoff - 1) v)) +
                (out.retained.state.selection.eta : ℂ) *
                  EF.weilTest out.physicalSourceError
                    (finitePhysicalSynthesis
                      (fixedOriginalSincTrialAperture a)
                      (out.retained.state.selection.cutoff - 1)
                      (canonicalNativeCoefficientInclusion σ
                        (fixedOriginalSincTrialAperture a)
                        (out.retained.state.selection.cutoff - 1) v)) 0‖ ≤
              (C_Q * (1 + fixedOriginalSincTrialAperture a) *
                  Real.exp (fixedOriginalSincTrialAperture a / 2) *
                  Real.sqrt (1 +
                    (2 * Real.pi *
                      (out.retained.state.selection.cutoff - 1 : ℕ) /
                      fixedOriginalSincTrialAperture a) ^ 2) +
                out.retained.state.selection.eta) *
                ((fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
                  Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                    originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a))) *
                ‖v‖ ∧
            ‖zetaZeroConfig.W out.physicalSourceError
                (finitePhysicalSynthesis
                  (fixedOriginalSincTrialAperture a)
                  (out.retained.state.selection.cutoff - 1)
                  (canonicalNativeCoefficientInclusion σ
                    (fixedOriginalSincTrialAperture a)
                    (out.retained.state.selection.cutoff - 1) v)) +
                (out.retained.state.selection.eta : ℂ) *
                  EF.weilTest out.physicalSourceError
                    (finitePhysicalSynthesis
                      (fixedOriginalSincTrialAperture a)
                      (out.retained.state.selection.cutoff - 1)
                      (canonicalNativeCoefficientInclusion σ
                        (fixedOriginalSincTrialAperture a)
                        (out.retained.state.selection.cutoff - 1) v)) 0‖ ≤
              (C_Q * (1 + fixedOriginalSincTrialAperture a) *
                  Real.exp (fixedOriginalSincTrialAperture a / 2) *
                  Real.sqrt (1 +
                    (2 * Real.pi *
                      (out.retained.state.selection.cutoff - 1 : ℕ) /
                      fixedOriginalSincTrialAperture a) ^ 2) +
                (C_W / 2) * (1 + fixedOriginalSincTrialAperture a) *
                  Real.exp (fixedOriginalSincTrialAperture a / 2) *
                  (1 + (2 * Real.pi *
                    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) /
                      fixedOriginalSincTrialAperture a) ^ 2)) *
                ((fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
                  Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                    originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a))) *
                ‖v‖ := by
  obtain ⟨C_Q, hCQ, hForcing⟩ := originalDetector_forcing_error_bound
  obtain ⟨C_W, hCW, hEtaUpper⟩ := originalDetector_eta_source_upper
  obtain ⟨L0, hL0, hN14⟩ := step123NativeOutput_imageErrors_commonThreshold
  refine ⟨C_Q, C_W, L0, hCQ, hCW, hL0, ?_⟩
  intro β σ a out hlarge
  have hImage := hN14 out hlarge
  have hEta := hEtaUpper β σ a out
  refine ⟨hImage, hEta, ?_⟩
  intro v
  have hEtaNonneg : 0 ≤ out.retained.state.selection.eta := by
    have h1 : 0 < Real.exp (β * fixedOriginalSincTrialAperture a) / 3 := by positivity
    exact (h1.trans out.source_selector.eta_lower).le
  obtain ⟨hC2, hSupport⟩ := out.physicalSourceError_admissible
  have hQ := hForcing σ (fixedOriginalSincTrialAperture a) out.aperture_pos
    (out.retained.state.selection.cutoff - 1)
    out.retained.state.selection.eta hEtaNonneg out.physicalSourceError
    hC2 hSupport v
  have hL : 0 ≤ fixedOriginalSincTrialAperture a := out.aperture_pos.le
  have hMode : 0 ≤ C_Q * (1 + fixedOriginalSincTrialAperture a) *
      Real.exp (fixedOriginalSincTrialAperture a / 2) *
      Real.sqrt (1 +
        (2 * Real.pi * (out.retained.state.selection.cutoff - 1 : ℕ) /
          fixedOriginalSincTrialAperture a) ^ 2) := by
    have := Real.sqrt_nonneg (1 +
        (2 * Real.pi * (out.retained.state.selection.cutoff - 1 : ℕ) /
          fixedOriginalSincTrialAperture a) ^ 2)
    positivity
  have hRate : 0 ≤ (fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
      Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
        originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a)) := by
    have := Real.rpow_nonneg hL (17 / 2 : ℝ)
    positivity
  have hv : 0 ≤ ‖v‖ := norm_nonneg v
  have hFirst := hQ.trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hImage.2.1 (add_nonneg hMode hEtaNonneg)) hv)
  refine ⟨hFirst, hFirst.trans ?_⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (add_le_add le_rfl hEta) hRate) hv

/-- N37, first form. Source-only `C_Q > 0` and one threshold `L0 ≥ 4`
(obtained from the combined theorem, hence from the N14 threshold) such
that for every stored packet with `L0 ≤ L` and every actual predecessor
test `v`, the projected forcing error is bounded by the finite-mode
factor plus the stored shift `eta`, times the quartic H1 rate, times
`‖v‖`. -/
theorem step123NativeOutput_forcingError_quarticRate_commonThreshold :
    ∃ C_Q L0 : ℝ, 0 < C_Q ∧ 4 ≤ L0 ∧
      ∀ {β : ℝ} {σ : ReversalParity} {a : ℝ}
        (out : Step123NativeOutput β σ a),
        L0 ≤ fixedOriginalSincTrialAperture a →
          ∀ (v : nativePoleNeutralParitySpace σ
              (fixedOriginalSincTrialAperture a)
              (out.retained.state.selection.cutoff - 1)),
            ‖zetaZeroConfig.W out.physicalSourceError
                (finitePhysicalSynthesis
                  (fixedOriginalSincTrialAperture a)
                  (out.retained.state.selection.cutoff - 1)
                  (canonicalNativeCoefficientInclusion σ
                    (fixedOriginalSincTrialAperture a)
                    (out.retained.state.selection.cutoff - 1) v)) +
                (out.retained.state.selection.eta : ℂ) *
                  EF.weilTest out.physicalSourceError
                    (finitePhysicalSynthesis
                      (fixedOriginalSincTrialAperture a)
                      (out.retained.state.selection.cutoff - 1)
                      (canonicalNativeCoefficientInclusion σ
                        (fixedOriginalSincTrialAperture a)
                        (out.retained.state.selection.cutoff - 1) v)) 0‖ ≤
              (C_Q * (1 + fixedOriginalSincTrialAperture a) *
                  Real.exp (fixedOriginalSincTrialAperture a / 2) *
                  Real.sqrt (1 +
                    (2 * Real.pi *
                      (out.retained.state.selection.cutoff - 1 : ℕ) /
                      fixedOriginalSincTrialAperture a) ^ 2) +
                out.retained.state.selection.eta) *
                ((fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
                  Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                    originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a))) *
                ‖v‖ := by
  obtain ⟨C_Q, _C_W, L0, hCQ, _hCW, hL0, h⟩ :=
    step123NativeOutput_imageErrors_forcingError_commonThreshold
  exact ⟨C_Q, L0, hCQ, hL0, fun out hlarge v => ((h out hlarge).2.2 v).1⟩

/-- N37, second form. The stored shift is replaced by its proved explicit
upper bound `(C_W/2)(1+L)e^{L/2}(1+(2π Kd/L)^2)`, `Kd` the stored detector
cutoff, so the right-hand side depends only on `L`, the stored selected
cutoff `K`, the source constants `C_Q, C_W` and `‖v‖`. The finite-mode
factor and the shift factor stay separate summands. -/
theorem step123NativeOutput_forcingError_etaBound_commonThreshold :
    ∃ C_Q C_W L0 : ℝ, 0 < C_Q ∧ 0 < C_W ∧ 4 ≤ L0 ∧
      ∀ {β : ℝ} {σ : ReversalParity} {a : ℝ}
        (out : Step123NativeOutput β σ a),
        L0 ≤ fixedOriginalSincTrialAperture a →
          ∀ (v : nativePoleNeutralParitySpace σ
              (fixedOriginalSincTrialAperture a)
              (out.retained.state.selection.cutoff - 1)),
            ‖zetaZeroConfig.W out.physicalSourceError
                (finitePhysicalSynthesis
                  (fixedOriginalSincTrialAperture a)
                  (out.retained.state.selection.cutoff - 1)
                  (canonicalNativeCoefficientInclusion σ
                    (fixedOriginalSincTrialAperture a)
                    (out.retained.state.selection.cutoff - 1) v)) +
                (out.retained.state.selection.eta : ℂ) *
                  EF.weilTest out.physicalSourceError
                    (finitePhysicalSynthesis
                      (fixedOriginalSincTrialAperture a)
                      (out.retained.state.selection.cutoff - 1)
                      (canonicalNativeCoefficientInclusion σ
                        (fixedOriginalSincTrialAperture a)
                        (out.retained.state.selection.cutoff - 1) v)) 0‖ ≤
              (C_Q * (1 + fixedOriginalSincTrialAperture a) *
                  Real.exp (fixedOriginalSincTrialAperture a / 2) *
                  Real.sqrt (1 +
                    (2 * Real.pi *
                      (out.retained.state.selection.cutoff - 1 : ℕ) /
                      fixedOriginalSincTrialAperture a) ^ 2) +
                (C_W / 2) * (1 + fixedOriginalSincTrialAperture a) *
                  Real.exp (fixedOriginalSincTrialAperture a / 2) *
                  (1 + (2 * Real.pi *
                    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) /
                      fixedOriginalSincTrialAperture a) ^ 2)) *
                ((fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
                  Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                    originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a))) *
                ‖v‖ := by
  obtain ⟨C_Q, C_W, L0, hCQ, hCW, hL0, h⟩ :=
    step123NativeOutput_imageErrors_forcingError_commonThreshold
  exact ⟨C_Q, C_W, L0, hCQ, hCW, hL0, fun out hlarge v => ((h out hlarge).2.2 v).2⟩

/-- N37, second form, with the source error written literally as the
physical synthesis of the stored detector `out.retained.state.detector`
minus the original smooth trial of the same packet (via the N14 identity
`Step123NativeOutput.physicalSourceError_eq_storedDetector`). -/
theorem step123NativeOutput_storedDetectorForcingError_etaBound_commonThreshold :
    ∃ C_Q C_W L0 : ℝ, 0 < C_Q ∧ 0 < C_W ∧ 4 ≤ L0 ∧
      ∀ {β : ℝ} {σ : ReversalParity} {a : ℝ}
        (out : Step123NativeOutput β σ a),
        L0 ≤ fixedOriginalSincTrialAperture a →
          ∀ (v : nativePoleNeutralParitySpace σ
              (fixedOriginalSincTrialAperture a)
              (out.retained.state.selection.cutoff - 1)),
            ‖zetaZeroConfig.W
                (finitePhysicalSynthesis
                    (fixedOriginalSincTrialAperture a)
                    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                    (canonicalNativeCoefficientInclusion σ
                      (fixedOriginalSincTrialAperture a)
                      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                      out.retained.state.detector) -
                  out.originalTrial)
                (finitePhysicalSynthesis
                  (fixedOriginalSincTrialAperture a)
                  (out.retained.state.selection.cutoff - 1)
                  (canonicalNativeCoefficientInclusion σ
                    (fixedOriginalSincTrialAperture a)
                    (out.retained.state.selection.cutoff - 1) v)) +
                (out.retained.state.selection.eta : ℂ) *
                  EF.weilTest
                    (finitePhysicalSynthesis
                        (fixedOriginalSincTrialAperture a)
                        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                        (canonicalNativeCoefficientInclusion σ
                          (fixedOriginalSincTrialAperture a)
                          (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
                          out.retained.state.detector) -
                      out.originalTrial)
                    (finitePhysicalSynthesis
                      (fixedOriginalSincTrialAperture a)
                      (out.retained.state.selection.cutoff - 1)
                      (canonicalNativeCoefficientInclusion σ
                        (fixedOriginalSincTrialAperture a)
                        (out.retained.state.selection.cutoff - 1) v)) 0‖ ≤
              (C_Q * (1 + fixedOriginalSincTrialAperture a) *
                  Real.exp (fixedOriginalSincTrialAperture a / 2) *
                  Real.sqrt (1 +
                    (2 * Real.pi *
                      (out.retained.state.selection.cutoff - 1 : ℕ) /
                      fixedOriginalSincTrialAperture a) ^ 2) +
                (C_W / 2) * (1 + fixedOriginalSincTrialAperture a) *
                  Real.exp (fixedOriginalSincTrialAperture a / 2) *
                  (1 + (2 * Real.pi *
                    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) /
                      fixedOriginalSincTrialAperture a) ^ 2)) *
                ((fixedOriginalSincTrialAperture a) ^ (17 / 2 : ℝ) *
                  Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                    originalDetectorQuarticRootScale (fixedOriginalSincTrialAperture a))) *
                ‖v‖ := by
  obtain ⟨C_Q, C_W, L0, hCQ, hCW, hL0, h⟩ :=
    step123NativeOutput_forcingError_etaBound_commonThreshold
  refine ⟨C_Q, C_W, L0, hCQ, hCW, hL0, ?_⟩
  intro β σ a out hlarge v
  rw [← out.physicalSourceError_eq_storedDetector]
  exact h out hlarge v

end Zeta23.CCM

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-- For any real `L0`, the existing producer called at lateness `max R L0`
gives a generated packet at the requested lateness `R` whose aperture
exceeds `max R L0`. Only the lateness certificate `sourceData.late` is
weakened from `max R L0` to `R`; every other field is the producer's. -/
private theorem exists_generatedStep123Output_aperture_gt_max
    (ρ : zetaZeroConfig.carrier) {β : ℝ}
    (hβ : 0 < β) (hβρ : β < |(ρ : ℂ).re - 1 / 2|)
    (σ : ReversalParity) (R L0 : ℝ) :
    ∃ g : GeneratedStep123Output ρ β σ R,
      max R L0 < fixedOriginalSincTrialAperture g.sourceData.separation := by
  obtain ⟨g⟩ := exists_generatedStep123Output ρ hβ hβρ σ (max R L0)
  have hlate : max R L0 < fixedOriginalSincTrialAperture g.sourceData.separation :=
    (le_max_left _ 4).trans_lt g.native_aperture_bound
  have hR : max R 4 < fixedOriginalSincTrialAperture g.sourceData.separation :=
    (max_le_max (le_max_left R L0) le_rfl).trans_lt g.native_aperture_bound
  let d : OriginalDetectorPaddedFinitePhaseData β
      (nativeOriginalDetectorPhaseSign σ) R :=
    { separation := g.sourceData.separation
      aperture_pos := g.sourceData.aperture_pos
      separation_gt_scale := g.sourceData.separation_gt_scale
      late := hR
      unit := g.sourceData.unit
      depth := g.sourceData.depth
      original_depth := g.sourceData.original_depth }
  let g' : GeneratedStep123Output ρ β σ R :=
    { beta_pos := g.beta_pos
      beta_below := g.beta_below
      sourceData := d
      native := g.native
      native_aperture_bound := hR
      offLine := g.offLine
      true_input_nonrange := g.true_input_nonrange }
  exact ⟨g', hlate⟩

/-- N37, generated and cofinal. The constants and the threshold of
`step123NativeOutput_imageErrors_forcingError_commonThreshold` are fixed
before the zero. For each actual off-line zero, admissible `β`, phase and
lateness `R`, a generated packet at lateness `R` has aperture above
`max R L0`, so both forcing-error bounds hold for its stored native packet
and every actual predecessor test. Each phase is cofinal separately. -/
theorem exists_generatedStep123Output_forcingError_cofinal_atLateness :
    ∃ C_Q C_W L0 : ℝ, 0 < C_Q ∧ 0 < C_W ∧ 4 ≤ L0 ∧
      ∀ (ρ : zetaZeroConfig.carrier) {β : ℝ}
        (_hβ : 0 < β) (_hβρ : β < |(ρ : ℂ).re - 1 / 2|)
        (σ : ReversalParity) (R : ℝ),
        ∃ g : GeneratedStep123Output ρ β σ R,
          max R L0 < fixedOriginalSincTrialAperture g.sourceData.separation ∧
          ∀ (v : nativePoleNeutralParitySpace σ
              (fixedOriginalSincTrialAperture g.sourceData.separation)
              (g.native.retained.state.selection.cutoff - 1)),
            ‖zetaZeroConfig.W g.native.physicalSourceError
                (finitePhysicalSynthesis
                  (fixedOriginalSincTrialAperture g.sourceData.separation)
                  (g.native.retained.state.selection.cutoff - 1)
                  (canonicalNativeCoefficientInclusion σ
                    (fixedOriginalSincTrialAperture g.sourceData.separation)
                    (g.native.retained.state.selection.cutoff - 1) v)) +
                (g.native.retained.state.selection.eta : ℂ) *
                  EF.weilTest g.native.physicalSourceError
                    (finitePhysicalSynthesis
                      (fixedOriginalSincTrialAperture g.sourceData.separation)
                      (g.native.retained.state.selection.cutoff - 1)
                      (canonicalNativeCoefficientInclusion σ
                        (fixedOriginalSincTrialAperture g.sourceData.separation)
                        (g.native.retained.state.selection.cutoff - 1) v)) 0‖ ≤
              (C_Q * (1 + fixedOriginalSincTrialAperture g.sourceData.separation) *
                  Real.exp (fixedOriginalSincTrialAperture g.sourceData.separation / 2) *
                  Real.sqrt (1 +
                    (2 * Real.pi *
                      (g.native.retained.state.selection.cutoff - 1 : ℕ) /
                      fixedOriginalSincTrialAperture g.sourceData.separation) ^ 2) +
                g.native.retained.state.selection.eta) *
                ((fixedOriginalSincTrialAperture g.sourceData.separation) ^ (17 / 2 : ℝ) *
                  Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                    originalDetectorQuarticRootScale
                      (fixedOriginalSincTrialAperture g.sourceData.separation))) *
                ‖v‖ ∧
            ‖zetaZeroConfig.W g.native.physicalSourceError
                (finitePhysicalSynthesis
                  (fixedOriginalSincTrialAperture g.sourceData.separation)
                  (g.native.retained.state.selection.cutoff - 1)
                  (canonicalNativeCoefficientInclusion σ
                    (fixedOriginalSincTrialAperture g.sourceData.separation)
                    (g.native.retained.state.selection.cutoff - 1) v)) +
                (g.native.retained.state.selection.eta : ℂ) *
                  EF.weilTest g.native.physicalSourceError
                    (finitePhysicalSynthesis
                      (fixedOriginalSincTrialAperture g.sourceData.separation)
                      (g.native.retained.state.selection.cutoff - 1)
                      (canonicalNativeCoefficientInclusion σ
                        (fixedOriginalSincTrialAperture g.sourceData.separation)
                        (g.native.retained.state.selection.cutoff - 1) v)) 0‖ ≤
              (C_Q * (1 + fixedOriginalSincTrialAperture g.sourceData.separation) *
                  Real.exp (fixedOriginalSincTrialAperture g.sourceData.separation / 2) *
                  Real.sqrt (1 +
                    (2 * Real.pi *
                      (g.native.retained.state.selection.cutoff - 1 : ℕ) /
                      fixedOriginalSincTrialAperture g.sourceData.separation) ^ 2) +
                (C_W / 2) * (1 + fixedOriginalSincTrialAperture g.sourceData.separation) *
                  Real.exp (fixedOriginalSincTrialAperture g.sourceData.separation / 2) *
                  (1 + (2 * Real.pi *
                    (originalDetectorQuarticCutoff
                      (fixedOriginalSincTrialAperture g.sourceData.separation)) /
                      fixedOriginalSincTrialAperture g.sourceData.separation) ^ 2)) *
                ((fixedOriginalSincTrialAperture g.sourceData.separation) ^ (17 / 2 : ℝ) *
                  Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
                    originalDetectorQuarticRootScale
                      (fixedOriginalSincTrialAperture g.sourceData.separation))) *
                ‖v‖ := by
  obtain ⟨C_Q, C_W, L0, hCQ, hCW, hL0, h⟩ :=
    step123NativeOutput_imageErrors_forcingError_commonThreshold
  refine ⟨C_Q, C_W, L0, hCQ, hCW, hL0, ?_⟩
  intro ρ β hβ hβρ σ R
  obtain ⟨g, hlate⟩ := exists_generatedStep123Output_aperture_gt_max ρ hβ hβρ σ R L0
  have hL : L0 ≤ fixedOriginalSincTrialAperture g.sourceData.separation :=
    ((le_max_right R L0).trans_lt hlate).le
  exact ⟨g, hlate, fun v => (h g.native hL).2.2 v⟩

end Zeta23.ExceptionalZero

#print axioms Zeta23.CCM.step123NativeOutput_imageErrors_forcingError_commonThreshold
#print axioms Zeta23.CCM.step123NativeOutput_forcingError_quarticRate_commonThreshold
#print axioms Zeta23.CCM.step123NativeOutput_forcingError_etaBound_commonThreshold
#print axioms Zeta23.CCM.step123NativeOutput_storedDetectorForcingError_etaBound_commonThreshold
#print axioms Zeta23.ExceptionalZero.exists_generatedStep123Output_forcingError_cofinal_atLateness
