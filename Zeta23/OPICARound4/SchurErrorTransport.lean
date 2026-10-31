import Zeta23.OPICARound4.SmoothForcing

/-! Finite transport of the full original-detector Schur loss.
The inverse is the same actual predecessor at -eta throughout. The direct
energy and eta-weighted physical mass are retained. No arithmetic upper law
or identification of the original detector with a selected ground is used. -/

noncomputable section
open MeasureTheory Complex
open scoped ComplexConjugate

namespace Zeta23.OPICARound4
open CCM ExceptionalZero

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace nativeDetectorComplement

variable {β : ℝ} {σ : ReversalParity} {a : ℝ}

def detectorInverse (out : Step123NativeOutput β σ a) :
    nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1) →L[ℂ]
    nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1) :=
  (nativeDetectorPredecessorEquiv σ out.retained.state.inverses).symm.toLinearMap.toContinuousLinearMap

def sourceInverseBudget (_out : Step123NativeOutput β σ a) : ℝ :=
  12 * ((originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a) - 1 : ℕ) : ℝ) /
    Real.exp (β * fixedOriginalSincTrialAperture a)

def detectorSchurLoss (out : Step123NativeOutput β σ a) : ℝ :=
  nativeOriginalAdmissibleSchurLoss σ out.source_selector

def finiteSourceEnergy (out : Step123NativeOutput β σ a) : ℝ :=
  (inner ℂ (nativePoleNeutralParityCanonical σ (fixedOriginalSincTrialAperture a)
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
    out.retained.state.detector) out.retained.state.detector).re

def smoothSourceMain (out : Step123NativeOutput β σ a) : ℝ :=
  (inner ℂ (smoothSourceForcing out) (detectorInverse out (smoothSourceForcing out))).re -
    (zetaZeroConfig.W out.originalTrial out.originalTrial).re -
      out.retained.state.selection.eta * ‖smoothSourceL2 out‖ ^ 2

def sourceEnergyErrorBudget (L : ℝ) : ℝ :=
  (1 + L) * L ^ (17 / 2 : ℝ) * Real.exp (L / 2 -
    originalDetectorRetainedDecayRate UniversalSinc.fixedScale * originalDetectorQuarticRootScale L)

def sourceSchurErrorBudget (out : Step123NativeOutput β σ a) : ℝ :=
  sourceInverseBudget out * sourceForcingErrorBudget out *
      (2 * finiteForcingBudget out + sourceForcingErrorBudget out) +
    sourceEnergyErrorBudget (fixedOriginalSincTrialAperture a) +
    out.retained.state.selection.eta * sourceImageErrorBudget (fixedOriginalSincTrialAperture a) *
      (2 + sourceImageErrorBudget (fixedOriginalSincTrialAperture a))

theorem detectorInverse_norm_bound (out : Step123NativeOutput β σ a) :
    ‖detectorInverse out‖ ≤ sourceInverseBudget out := out.detector_inverse_budget

theorem sourceInverseBudget_nonneg (out : Step123NativeOutput β σ a) :
    0 ≤ sourceInverseBudget out := by unfold sourceInverseBudget; positivity

theorem detectorSchurLoss_lower (out : Step123NativeOutput β σ a) :
    Real.exp (β * fixedOriginalSincTrialAperture a) / 2 < detectorSchurLoss out :=
  nativeOriginalAdmissibleSchurLoss_gt_half_depth σ out.retained.state
    out.source_selector out.detector_source_eq

theorem detectorSchurLoss_eq_forcing_energy (out : Step123NativeOutput β σ a) :
    detectorSchurLoss out =
      (inner ℂ out.retained.predecessorForcing
        (detectorInverse out out.retained.predecessorForcing)).re -
      finiteSourceEnergy out - out.retained.state.selection.eta := by
  let s := out.retained.state.selection
  let p := out.retained.state.detector
  let J := nativeDetectorPredecessorEmbedding σ s
  let T := nativePoleNeutralParityShifted σ (fixedOriginalSincTrialAperture a)
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) (-s.eta)
  let P := nativeDetectorPredecessorEquiv σ out.retained.state.inverses
  let x := J.toLinearMap.adjoint p
  let y := isometricDetectorComplementCoordinate J p
  let z := x + isometricDetectorResponse J T P y
  have hF : P z = out.retained.predecessorForcing := by
    rw [out.retained.forcing_eq,
      originalDetectorNativeForcing_eq_predecessor_plus_coupling σ out.retained.state.inverses]
    change P (x + P.symm (isometricDetectorCoupling J T y)) =
      P x + isometricDetectorCoupling J T y
    rw [map_add, P.apply_symm_apply]
  have hz : P.symm out.retained.predecessorForcing = z := by
    rw [← hF, P.symm_apply_apply]
  have h := congrArg Complex.re (originalDetector_schur_completion out.retained.state)
  change (inner ℂ (T p) p).re =
    (inner ℂ (P z) z + inner ℂ (nativeDetectorSchurOperator σ out.retained.state.inverses y) y).re at h
  rw [Complex.add_re, hF, ← hz] at h
  have henergy : (inner ℂ (T p) p).re = finiteSourceEnergy out + s.eta := by
    change (inner ℂ (nativePoleNeutralParityShifted σ _ _ (-s.eta) p) p).re = _
    simp only [nativePoleNeutralParityShifted, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, inner_sub_left, Complex.sub_re]
    rw [re_inner_ofReal_smul_self]
    have hp : ‖p‖ = 1 := out.retained.state.detector_unit
    rw [hp]
    change finiteSourceEnergy out - -s.eta * 1 ^ 2 = _
    ring
  have hl := nativeOriginalAdmissibleSchurLoss_eq_retained σ out.retained.state
    out.source_selector out.detector_source_eq
  change detectorSchurLoss out =
    -(inner ℂ (nativeDetectorSchurOperator σ out.retained.state.inverses y) y).re at hl
  change detectorSchurLoss out =
    (inner ℂ out.retained.predecessorForcing (P.symm out.retained.predecessorForcing)).re -
      finiteSourceEnergy out - s.eta
  rw [henergy] at h
  linarith

/-- A same-operator perturbation estimate; it does not compare two inverses. -/
theorem sourceQuadratic_perturbation_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (A : E →L[ℂ] E) (F G : E) :
    |(inner ℂ F (A F)).re - (inner ℂ G (A G)).re| ≤
      ‖A‖ * ‖F - G‖ * (‖F‖ + ‖G‖) := by
  have he : inner ℂ F (A F) - inner ℂ G (A G) =
      inner ℂ (F - G) (A F) + inner ℂ G (A (F - G)) := by
    rw [map_sub, inner_sub_left, inner_sub_right]
    ring
  calc
    _ = |(inner ℂ F (A F) - inner ℂ G (A G)).re| := by rw [Complex.sub_re]
    _ ≤ ‖inner ℂ F (A F) - inner ℂ G (A G)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖F - G‖ * ‖A F‖ + ‖G‖ * ‖A (F - G)‖ := by
      rw [he]
      exact (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
    _ ≤ ‖F - G‖ * (‖A‖ * ‖F‖) + ‖G‖ * (‖A‖ * ‖F - G‖) :=
      add_le_add (mul_le_mul_of_nonneg_left (A.le_opNorm F) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (A.le_opNorm (F - G)) (norm_nonneg _))
    _ = _ := by ring

theorem smoothSourceL2_mass_error_bound (out : Step123NativeOutput β σ a) :
    |1 - ‖smoothSourceL2 out‖ ^ 2| ≤
      sourceImageErrorBudget (fixedOriginalSincTrialAperture a) *
        (2 + sourceImageErrorBudget (fixedOriginalSincTrialAperture a)) := by
  let e := sourceImageErrorBudget (fixedOriginalSincTrialAperture a)
  let n := ‖smoothSourceL2 out‖
  have he : 0 ≤ e := sourceImageErrorBudget_nonneg _ out.aperture_pos.le
  have hn : 0 ≤ n := norm_nonneg _
  have hd := (abs_norm_sub_norm_le out.physicalFiniteImage (smoothSourceL2 out)).trans
    (smoothSourceL2_error_bound out)
  rw [out.physicalFiniteImage_unit] at hd
  change |1 - n| ≤ e at hd
  have hb : 1 + n ≤ 2 + e := by
    have := (abs_le.mp hd).1
    linarith
  calc
    |1 - n ^ 2| = |1 - n| * (1 + n) := by
      rw [← abs_of_nonneg (show 0 ≤ 1 + n by positivity), ← abs_mul]
      congr 1
      ring
    _ ≤ e * (2 + e) := mul_le_mul hd hb (by positivity) he

theorem detectorSchurLoss_sub_smoothSourceMain_bound (out : Step123NativeOutput β σ a) :
    |detectorSchurLoss out - smoothSourceMain out| ≤ sourceSchurErrorBudget out := by
  let e := sourceImageErrorBudget (fixedOriginalSincTrialAperture a)
  have hq := sourceQuadratic_perturbation_bound (detectorInverse out)
    out.retained.predecessorForcing (smoothSourceForcing out)
  have hcost : ‖detectorInverse out‖ *
      ‖out.retained.predecessorForcing - smoothSourceForcing out‖ *
        (‖out.retained.predecessorForcing‖ + ‖smoothSourceForcing out‖) ≤
      sourceInverseBudget out * sourceForcingErrorBudget out *
        (2 * finiteForcingBudget out + sourceForcingErrorBudget out) := by
    apply mul_le_mul
    · exact mul_le_mul (detectorInverse_norm_bound out) (smoothSourceForcing_error_bound out)
        (norm_nonneg _) (sourceInverseBudget_nonneg out)
    · nlinarith only [finiteForcing_norm_bound out, smoothSourceForcing_norm_bound out]
    · positivity
    · exact mul_nonneg (sourceInverseBudget_nonneg out) (sourceForcingErrorBudget_nonneg out)
  have hQ : |finiteSourceEnergy out - (zetaZeroConfig.W out.originalTrial out.originalTrial).re| ≤
      sourceEnergyErrorBudget (fixedOriginalSincTrialAperture a) :=
    (step123ImageErrorRates_of_threshold out out.image_threshold_paid.le).2.2
  have hm : |out.retained.state.selection.eta * (1 - ‖smoothSourceL2 out‖ ^ 2)| ≤
      out.retained.state.selection.eta * e * (2 + e) := by
    rw [abs_mul, abs_of_nonneg (source_eta_nonneg out)]
    exact (mul_le_mul_of_nonneg_left (smoothSourceL2_mass_error_bound out)
      (source_eta_nonneg out)).trans_eq (by dsimp [e]; ring)
  rw [detectorSchurLoss_eq_forcing_energy]
  unfold smoothSourceMain
  have heq :
      ((inner ℂ out.retained.predecessorForcing (detectorInverse out out.retained.predecessorForcing)).re -
        finiteSourceEnergy out - out.retained.state.selection.eta) -
      ((inner ℂ (smoothSourceForcing out) (detectorInverse out (smoothSourceForcing out))).re -
        (zetaZeroConfig.W out.originalTrial out.originalTrial).re -
        out.retained.state.selection.eta * ‖smoothSourceL2 out‖ ^ 2) =
      ((inner ℂ out.retained.predecessorForcing (detectorInverse out out.retained.predecessorForcing)).re -
        (inner ℂ (smoothSourceForcing out) (detectorInverse out (smoothSourceForcing out))).re) -
      (finiteSourceEnergy out - (zetaZeroConfig.W out.originalTrial out.originalTrial).re) -
      out.retained.state.selection.eta * (1 - ‖smoothSourceL2 out‖ ^ 2) := by ring
  rw [heq]
  exact ((abs_sub _ _).trans (add_le_add (abs_sub _ _) le_rfl)).trans
    (show _ ≤ sourceSchurErrorBudget out from add_le_add (add_le_add (hq.trans hcost) hQ) hm)

theorem detectorForcing_zero_at_first (out : Step123NativeOutput β σ a)
    (hK : out.retained.state.selection.cutoff = 3) :
    out.retained.predecessorForcing = 0 ∧ smoothSourceForcing out = 0 := by
  have hdim : Module.finrank ℂ
      (nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
        (out.retained.state.selection.cutoff - 1)) = 0 := by
    rw [hK]
    simpa using finrank_nativePoleNeutralParitySpace σ out.aperture_pos 2 (by norm_num)
  exact ⟨(finrank_zero_iff_forall_zero (K := ℂ)).mp hdim _,
    (finrank_zero_iff_forall_zero (K := ℂ)).mp hdim _⟩

theorem detectorSchurLoss_at_first (out : Step123NativeOutput β σ a)
    (hK : out.retained.state.selection.cutoff = 3) :
    detectorSchurLoss out = -finiteSourceEnergy out - out.retained.state.selection.eta := by
  rw [detectorSchurLoss_eq_forcing_energy, (detectorForcing_zero_at_first out hK).1]
  simp

end Zeta23.OPICARound4
