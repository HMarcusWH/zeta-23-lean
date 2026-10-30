import Zeta23.ExceptionalZero.Step123CompleteOutput
import Zeta23.CCM.OriginalDetectorSchurLoss
import Zeta23.CCM.NativeWeilResponseBounds

/-! The complete smooth original source on the actual detector predecessor.
The response is restricted to the physical aperture before taking its L2 view.
No global L2 response, arithmetic smallness or replacement inverse is assumed. -/

noncomputable section
open MeasureTheory Set Complex
open scoped ComplexConjugate

namespace Zeta23.OPICARound4
open CCM ExceptionalZero

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

variable {β : ℝ} {σ : ReversalParity} {a : ℝ}

def sourceImageErrorBudget (L : ℝ) : ℝ :=
  L ^ (17 / 2 : ℝ) * Real.exp
    (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale * originalDetectorQuarticRootScale L)

def sourceFiniteModeCost (L : ℝ) (K : ℕ) : ℝ :=
  Real.sqrt (1 + (2 * Real.pi * K / L) ^ 2)

def sourceForcingErrorBudget (out : Step123NativeOutput β σ a) : ℝ :=
  let L := fixedOriginalSincTrialAperture a
  (step123SameStateForcingConstant * (1 + L) * Real.exp (L / 2) *
      sourceFiniteModeCost L (out.retained.state.selection.cutoff - 1) +
      out.retained.state.selection.eta) * sourceImageErrorBudget L

def sourceWeilBoundConstant : ℝ := Classical.choose originalDetector_forcingWeilError_bound

theorem sourceWeilBoundConstant_pos : 0 < sourceWeilBoundConstant :=
  (Classical.choose_spec originalDetector_forcingWeilError_bound).1

def finiteForcingBudget (out : Step123NativeOutput β σ a) : ℝ :=
  let L := fixedOriginalSincTrialAperture a
  sourceWeilBoundConstant * (1 + L) * Real.exp (L / 2) *
      sourceFiniteModeCost L (originalDetectorQuarticCutoff L) *
      sourceFiniteModeCost L (out.retained.state.selection.cutoff - 1) +
    out.retained.state.selection.eta

theorem sourceImageErrorBudget_nonneg (L : ℝ) (hL : 0 ≤ L) : 0 ≤ sourceImageErrorBudget L := by
  unfold sourceImageErrorBudget
  positivity

theorem source_eta_nonneg (out : Step123NativeOutput β σ a) :
    0 ≤ out.retained.state.selection.eta := by
  have h := out.retained.state.selection.eta_lower
  linarith [Real.exp_pos (β * fixedOriginalSincTrialAperture a)]

theorem sourceForcingErrorBudget_nonneg (out : Step123NativeOutput β σ a) :
    0 ≤ sourceForcingErrorBudget out := by
  have hL := out.aperture_pos
  have hc := step123SameStateForcingConstant_pos
  have he := source_eta_nonneg out
  have hr := sourceImageErrorBudget_nonneg (fixedOriginalSincTrialAperture a) out.aperture_pos.le
  unfold sourceForcingErrorBudget sourceFiniteModeCost
  positivity

theorem finiteForcingBudget_nonneg (out : Step123NativeOutput β σ a) :
    0 ≤ finiteForcingBudget out := by
  have hL := out.aperture_pos
  have hc := sourceWeilBoundConstant_pos
  have he := source_eta_nonneg out
  unfold finiteForcingBudget sourceFiniteModeCost
  positivity

def smoothSourceL2 (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  ((fixedOriginalSincPhaseTrial_contDiff (nativeOriginalDetectorPhaseSign σ) a).continuous.memLp_of_hasCompactSupport
    (fixedOriginalSincPhaseTrial_hasCompactSupport _ a)).toLp
      out.originalTrial

theorem smoothSourceL2_ae (out : Step123NativeOutput β σ a) :
    smoothSourceL2 out =ᵐ[volume] out.originalTrial := MemLp.coeFn_toLp _

def smoothSourceResponseL2 (out : Step123NativeOutput β σ a) : CanonicalPhysicalL2 :=
  (nativeWeilResponse_indicator_memLp_two
    (fixedOriginalSincPhaseTrial_contDiff (nativeOriginalDetectorPhaseSign σ) a)
    (fixedOriginalSincPhaseTrial_hasCompactSupport _ a)
    0 (fixedOriginalSincTrialAperture a)).toLp
      ((Icc (0 : ℝ) (fixedOriginalSincTrialAperture a)).indicator
        (nativeWeilResponse out.originalTrial))

theorem smoothSourceResponseL2_ae (out : Step123NativeOutput β σ a) :
    smoothSourceResponseL2 out =ᵐ[volume]
      (Icc (0 : ℝ) (fixedOriginalSincTrialAperture a)).indicator
        (nativeWeilResponse out.originalTrial) := MemLp.coeFn_toLp _

def smoothSourceForcing (out : Step123NativeOutput β σ a) :
    nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1) :=
  canonicalNativePhysicalProjection σ out.aperture_pos (out.retained.state.selection.cutoff - 1)
    (smoothSourceResponseL2 out + (out.retained.state.selection.eta : ℂ) • smoothSourceL2 out)

theorem smoothSourceForcing_pairing (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    inner ℂ v (smoothSourceForcing out) =
      zetaZeroConfig.W out.originalTrial (out.forcingTest v) +
        (out.retained.state.selection.eta : ℂ) * EF.weilTest out.originalTrial (out.forcingTest v) 0 := by
  obtain ⟨⟨hgC, hgS⟩, _, _, ⟨hvC, hvS⟩⟩ := out.n36_sources_regular v
  have hresp : inner ℂ v
      (canonicalNativePhysicalProjection σ out.aperture_pos
        (out.retained.state.selection.cutoff - 1) (smoothSourceResponseL2 out)) =
      zetaZeroConfig.W out.originalTrial (out.forcingTest v) := by
    rw [canonicalNativePhysicalProjection_inner, nativeWeilResponse_pairing hgC hgS hvC.continuous hvS]
    apply integral_congr_ae
    filter_upwards [smoothSourceResponseL2_ae out] with x hx
    rw [hx]
    by_cases hm : x ∈ Icc (0 : ℝ) (fixedOriginalSincTrialAperture a)
    · rw [Set.indicator_of_mem hm]
      exact mul_comm _ _
    · rw [Set.indicator_of_notMem hm]
      have hv : out.forcingTest v x = 0 := by
        unfold Step123NativeOutput.forcingTest finitePhysicalSynthesis
        rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hm]
      change _ = _ * conj (out.forcingTest v x)
      rw [hv]
      simp
  have hmass : inner ℂ v
      (canonicalNativePhysicalProjection σ out.aperture_pos
        (out.retained.state.selection.cutoff - 1) (smoothSourceL2 out)) =
      EF.weilTest out.originalTrial (out.forcingTest v) 0 := by
    rw [canonicalNativePhysicalProjection_inner, n36_weilTest_zero_eq_pairing]
    apply integral_congr_ae
    filter_upwards [smoothSourceL2_ae out] with x hx
    rw [hx]
    exact mul_comm _ _
  unfold smoothSourceForcing
  rw [map_add, map_smul, inner_add_right, inner_smul_right, hresp, hmass]

theorem smoothSourceForcing_error_pairing (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    inner ℂ v (out.retained.predecessorForcing - smoothSourceForcing out) =
      out.approximationChannel v := by
  rw [inner_sub_right, out.n36_forcing_coordinate, smoothSourceForcing_pairing]
  obtain ⟨⟨hgC, hgS⟩, ⟨heC, heS⟩, ⟨hfC, hfS⟩, ⟨hvC, hvS⟩⟩ := out.n36_sources_regular v
  have hW : zetaZeroConfig.W out.storedFiniteDetector (out.forcingTest v) =
      zetaZeroConfig.W out.originalTrial (out.forcingTest v) +
        zetaZeroConfig.W out.physicalSourceError (out.forcingTest v) := by
    rw [nativeWeilResponse_pairing hfC hfS hvC.continuous hvS,
      nativeWeilResponse_pairing hgC hgS hvC.continuous hvS,
      nativeWeilResponse_pairing heC heS hvC.continuous hvS]
    have hi1 : Integrable (fun x : ℝ => nativeWeilResponse out.originalTrial x *
        conj (out.forcingTest v x)) := ((nativeWeilResponse_continuous hgC hgS).mul
      (Complex.continuous_conj.comp hvC.continuous)).integrable_of_hasCompactSupport
        ((hvS.comp_left (g := fun z : ℂ => conj z) (map_zero _)).mul_left)
    have hi2 : Integrable (fun x : ℝ => nativeWeilResponse out.physicalSourceError x *
        conj (out.forcingTest v x)) := ((nativeWeilResponse_continuous heC heS).mul
      (Complex.continuous_conj.comp hvC.continuous)).integrable_of_hasCompactSupport
        ((hvS.comp_left (g := fun z : ℂ => conj z) (map_zero _)).mul_left)
    rw [← integral_add hi1 hi2]
    apply integral_congr_ae
    filter_upwards with x
    rw [out.storedFiniteDetector_eq_originalTrial_add_error,
      n36_nativeWeilResponse_add hgC hgS heC heS x, add_mul]
  have hm : EF.weilTest out.storedFiniteDetector (out.forcingTest v) 0 =
      EF.weilTest out.originalTrial (out.forcingTest v) 0 +
        EF.weilTest out.physicalSourceError (out.forcingTest v) 0 := by
    simp only [n36_weilTest_zero_eq_pairing]
    have hi1 : Integrable (fun x : ℝ => out.originalTrial x * conj (out.forcingTest v x)) :=
      (hgC.continuous.mul
      (Complex.continuous_conj.comp hvC.continuous)).integrable_of_hasCompactSupport
        ((hvS.comp_left (g := fun z : ℂ => conj z) (map_zero _)).mul_left)
    have hi2 : Integrable (fun x : ℝ => out.physicalSourceError x * conj (out.forcingTest v x)) :=
      (heC.continuous.mul
      (Complex.continuous_conj.comp hvC.continuous)).integrable_of_hasCompactSupport
        ((hvS.comp_left (g := fun z : ℂ => conj z) (map_zero _)).mul_left)
    rw [← integral_add hi1 hi2]
    apply integral_congr_ae
    filter_upwards with x
    rw [out.storedFiniteDetector_eq_originalTrial_add_error]
    simp only [Pi.add_apply, add_mul]
  rw [hW, hm]
  unfold Step123NativeOutput.approximationChannel
  ring

/-- The exact source response keeps the complete signed prime channel. -/
theorem smoothSourceForcing_channels (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    inner ℂ v (smoothSourceForcing out) =
      out.archChannel v - out.primeChannel v + out.spectralShiftChannel v := by
  have h := out.n36_channel_expansion v
  rw [← out.n36_forcing_coordinate, out.n36_poleChannel_eq_zero v] at h
  have he := smoothSourceForcing_error_pairing out v
  rw [inner_sub_right] at he
  linear_combination h - he

theorem norm_le_of_all_inner_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (x : E) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ v : E, ‖inner ℂ v x‖ ≤ C * ‖v‖) : ‖x‖ ≤ C := by
  have hx := h x
  rw [inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
    abs_of_nonneg (norm_nonneg x)] at hx
  nlinarith [norm_nonneg x]

theorem smoothSourceForcing_error_bound (out : Step123NativeOutput β σ a) :
    ‖out.retained.predecessorForcing - smoothSourceForcing out‖ ≤ sourceForcingErrorBudget out := by
  apply norm_le_of_all_inner_bound _ _ (sourceForcingErrorBudget_nonneg out)
  intro v
  rw [smoothSourceForcing_error_pairing]
  exact ((step123ForcingErrorRates_of_threshold out out.image_threshold_paid.le).2 v).1

theorem finiteForcing_norm_bound (out : Step123NativeOutput β σ a) :
    ‖out.retained.predecessorForcing‖ ≤ finiteForcingBudget out := by
  apply norm_le_of_all_inner_bound _ _ (finiteForcingBudget_nonneg out)
  intro v
  let L := fixedOriginalSincTrialAperture a
  let N := originalDetectorQuarticCutoff L
  let K := out.retained.state.selection.cutoff - 1
  obtain ⟨_, _, ⟨hfC, hfS⟩, ⟨hvC, hvS⟩⟩ := out.n36_sources_regular v
  have hs : tsupport out.storedFiniteDetector ⊆ Icc (0 : ℝ) L := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    by_contra hm
    apply hx
    unfold Step123NativeOutput.storedFiniteDetector finitePhysicalSynthesis
    rw [localizedFiniteVector_eq_indicator, Set.indicator_of_notMem hm]
  have hW := (Classical.choose_spec originalDetector_forcingWeilError_bound).2
    σ L out.aperture_pos K out.storedFiniteDetector hfC hs v
  have hH := canonicalNativePhysicalSynthesis_H1_bound σ out.aperture_pos N
    out.retained.state.detector
  rw [out.retained.state.detector_unit, mul_one] at hH
  have hc : 0 ≤ sourceWeilBoundConstant * (1 + L) * Real.exp (L / 2) *
      (sourceFiniteModeCost L K * ‖v‖) := by
    have hC := sourceWeilBoundConstant_pos
    have hL := out.aperture_pos
    unfold sourceFiniteModeCost
    positivity
  have hW' : ‖zetaZeroConfig.W out.storedFiniteDetector (out.forcingTest v)‖ ≤
      sourceWeilBoundConstant * (1 + L) * Real.exp (L / 2) *
        sourceFiniteModeCost L N * sourceFiniteModeCost L K * ‖v‖ := by
    change nativePhysicalH1Norm out.storedFiniteDetector ≤ sourceFiniteModeCost L N at hH
    have hm := mul_le_mul_of_nonneg_left hH hc
    change ‖zetaZeroConfig.W out.storedFiniteDetector (out.forcingTest v)‖ ≤
      sourceWeilBoundConstant * (1 + L) * Real.exp (L / 2) *
        nativePhysicalH1Norm out.storedFiniteDetector * (sourceFiniteModeCost L K * ‖v‖) at hW
    nlinarith only [hW, hm]
  have hfL2 : nativePhysicalL2Norm out.storedFiniteDetector = 1 := by
    rw [Step123NativeOutput.storedFiniteDetector,
      originalDetector_nativeFinitePhysicalL2_norm σ out.aperture_pos,
      out.retained.state.detector_unit]
  have hvL2 : nativePhysicalL2Norm (out.forcingTest v) = ‖v‖ :=
    originalDetector_nativeFinitePhysicalL2_norm σ out.aperture_pos K v
  have hm := nativeWeilTest_norm_le_L2 hfC.continuous hvC.continuous hfS hvS 0
  rw [hfL2, hvL2, one_mul] at hm
  have he := source_eta_nonneg out
  have hm' : ‖(out.retained.state.selection.eta : ℂ) *
      EF.weilTest out.storedFiniteDetector (out.forcingTest v) 0‖ ≤
      out.retained.state.selection.eta * ‖v‖ := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
      using mul_le_mul_of_nonneg_left hm he
  rw [out.n36_forcing_coordinate]
  exact (norm_add_le _ _).trans ((add_le_add hW' hm').trans_eq (by
    unfold finiteForcingBudget
    dsimp only [L, N, K] at *
    ring))

theorem smoothSourceForcing_norm_bound (out : Step123NativeOutput β σ a) :
    ‖smoothSourceForcing out‖ ≤ finiteForcingBudget out + sourceForcingErrorBudget out := by
  have h := norm_sub_le out.retained.predecessorForcing
    (out.retained.predecessorForcing - smoothSourceForcing out)
  rw [sub_sub_cancel] at h
  exact h.trans (add_le_add (finiteForcing_norm_bound out) (smoothSourceForcing_error_bound out))

/-- The local physical Hilbert norm equals the literal full-line norm of its
almost-everywhere representative; this introduces no global response hypothesis. -/
theorem sourcePhysicalL2_norm_eq (u : CanonicalPhysicalL2) (f : ℝ → ℂ)
    (hf : u =ᵐ[volume] f) : ‖u‖ = nativePhysicalL2Norm f := by
  have he : inner ℂ u u = ∫ x : ℝ, ((‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf] with x hx
    rw [hx, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  have hr : ‖u‖ ^ 2 = ∫ x : ℝ, ‖f x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), he, integral_complex_ofReal]
    rfl
  unfold nativePhysicalL2Norm
  rw [← hr, Real.sqrt_sq (norm_nonneg u)]

theorem smoothSourceL2_error_bound (out : Step123NativeOutput β σ a) :
    ‖out.physicalFiniteImage - smoothSourceL2 out‖ ≤
      sourceImageErrorBudget (fixedOriginalSincTrialAperture a) := by
  have hae : (out.physicalFiniteImage - smoothSourceL2 out : CanonicalPhysicalL2) =ᵐ[volume]
      out.physicalSourceError := by
    filter_upwards [Lp.coeFn_sub out.physicalFiniteImage (smoothSourceL2 out),
      canonicalNativePhysicalIsometry_ae σ out.aperture_pos
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
        out.retained.state.detector, smoothSourceL2_ae out] with x hx hf hg
    rw [hx]
    change out.physicalFiniteImage x - smoothSourceL2 out x = _
    rw [hg]
    change out.physicalFiniteImage x = _ at hf
    rw [hf]
    have he := congrFun out.storedFiniteDetector_eq_originalTrial_add_error x
    change _ = out.originalTrial x + out.physicalSourceError x at he
    change out.storedFiniteDetector x - out.originalTrial x = out.physicalSourceError x
    rw [he]
    ring
  rw [sourcePhysicalL2_norm_eq _ _ hae]
  exact (nativePhysicalL2Norm_le_H1 _).trans
    (step123ImageErrorRates_of_threshold out out.image_threshold_paid.le).2.1

theorem smoothSourceL2_norm_bound (out : Step123NativeOutput β σ a) :
    ‖smoothSourceL2 out‖ ≤ 1 + sourceImageErrorBudget (fixedOriginalSincTrialAperture a) := by
  have h := norm_sub_le out.physicalFiniteImage (out.physicalFiniteImage - smoothSourceL2 out)
  rw [sub_sub_cancel, out.physicalFiniteImage_unit] at h
  exact h.trans (add_le_add_right (smoothSourceL2_error_bound out) 1)

end Zeta23.OPICARound4
