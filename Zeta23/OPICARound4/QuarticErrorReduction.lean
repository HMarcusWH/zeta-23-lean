import Zeta23.ExceptionalZero.Step123CompleteOutput
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Zeta23.OPICARound4.SchurErrorTransport

/-!
The literal quartic Fourier cutoff pays every fixed exponential rescaling.
The rate is chosen from the source before a zero, phase, or packet.
-/

noncomputable section

open Filter
open scoped Topology

namespace Zeta23.OPICARound4

open CCM ExceptionalZero

/-- A scalar consequence of the actual quartic cutoff, valid for every
real polynomial power and every fixed linear exponential loss. -/
theorem quartic_polynomial_exp_tendsto_zero (p t c : ℝ) (hc : 0 < c) :
    Tendsto (fun L : ℝ => L ^ p *
      Real.exp (t * L - c * originalDetectorQuarticRootScale L)) atTop (𝓝 0) := by
  have hlim : Tendsto (fun L : ℝ => L ^ p * Real.exp (-L)) atTop (𝓝 0) := by
    simpa using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero p 1 (by norm_num)
  apply squeeze_zero' _ _ hlim
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact mul_nonneg (Real.rpow_nonneg hL _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (0 : ℝ),
      originalDetectorRawCutoff_sqrt_eventually_ge_mul ((t + 1) / c)] with L hL hscale
    have hscaled := mul_le_mul_of_nonneg_left hscale hc.le
    have hc0 : c ≠ 0 := ne_of_gt hc
    have he : t * L - c * originalDetectorQuarticRootScale L ≤ -L := by
      change c * (((t + 1) / c) * L) ≤ c * originalDetectorQuarticRootScale L at hscaled
      have hcancel : c * (((t + 1) / c) * L) = (t + 1) * L := by field_simp
      rw [hcancel] at hscaled
      linarith
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (Real.rpow_nonneg hL _)

/-- The concrete N14 image rate, independent of all generated-packet data. -/
def quarticImageError (L : ℝ) : ℝ :=
  L ^ (17 / 2 : ℝ) * Real.exp
    (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
      originalDetectorQuarticRootScale L)

theorem quarticImageError_nonneg {L : ℝ} (hL : 0 ≤ L) : 0 ≤ quarticImageError L := by
  unfold quarticImageError
  positivity

/-- This is convergence of the explicit source rate, not an assumed decay
condition on a packet. The exponential weight may be any real number. -/
theorem quarticImageError_mul_exp_tendsto_zero (t : ℝ) :
    Tendsto (fun L : ℝ => quarticImageError L * Real.exp (t * L)) atTop (𝓝 0) := by
  have h := quartic_polynomial_exp_tendsto_zero (17 / 2) t
    (originalDetectorRetainedDecayRate UniversalSinc.fixedScale)
    (originalDetectorRetainedDecayRate_pos _)
  convert h using 1
  ext L
  unfold quarticImageError
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- Polynomial prefactors also cost no exponential rate. -/
theorem pow_mul_exp_mul_quarticImageError_tendsto_zero (n : ℕ) (t : ℝ) :
    Tendsto (fun L : ℝ => L ^ n * Real.exp (t * L) * quarticImageError L)
      atTop (𝓝 0) := by
  have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n).mul
    (quarticImageError_mul_exp_tendsto_zero (t + 1))
  simp only [mul_zero] at h
  convert h using 1
  ext L
  have he : Real.exp (-L) * Real.exp ((t + 1) * L) = Real.exp (t * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    L ^ n * Real.exp (t * L) * quarticImageError L =
        L ^ n * (Real.exp (-L) * Real.exp ((t + 1) * L)) * quarticImageError L := by rw [he]
    _ = (L ^ n * Real.exp (-L)) * (quarticImageError L * Real.exp ((t + 1) * L)) := by ring

/-- A ceiling bound for the prescribed degree; no cutoff is selected after
the packet. -/
theorem quarticCutoff_le_two_pow_four {L : ℝ} (hL : 1 ≤ L) :
    (originalDetectorQuarticCutoff L : ℝ) ≤ 2 * L ^ 4 := by
  have hp : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL
  have hc := Nat.ceil_lt_add_one (show 0 ≤ L ^ 4 by positivity)
  unfold originalDetectorQuarticCutoff
  linarith

/-- Every predecessor mode has a source-only cubic frequency envelope. -/
theorem quartic_mode_cost_le {L : ℝ} (hL : 1 ≤ L) {K : ℕ}
    (hK : K ≤ originalDetectorQuarticCutoff L) :
    Real.sqrt (1 + (2 * Real.pi * K / L) ^ 2) ≤ (1 + 4 * Real.pi) * L ^ 3 := by
  have hL0 : 0 < L := by linarith
  have hp : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL
  have hK' : (K : ℝ) ≤ 2 * L ^ 4 :=
    (Nat.cast_le.mpr hK).trans (quarticCutoff_le_two_pow_four hL)
  have hx0 : 0 ≤ 2 * Real.pi * K / L := by positivity
  have hx : 2 * Real.pi * K / L ≤ 4 * Real.pi * L ^ 3 := by
    apply (div_le_iff₀ hL0).mpr
    have hh := mul_le_mul_of_nonneg_left hK' (show 0 ≤ 2 * Real.pi by positivity)
    nlinarith
  have hs : Real.sqrt (1 + (2 * Real.pi * K / L) ^ 2) ≤
      1 + 2 * Real.pi * K / L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  calc
    _ ≤ 1 + 2 * Real.pi * K / L := hs
    _ ≤ 1 + 4 * Real.pi * L ^ 3 := by linarith
    _ ≤ (1 + 4 * Real.pi) * L ^ 3 := by nlinarith

/-- Full propagated scalar error after the inverse, forcing, native form,
and shifted physical-mass channels have all been paid. Constants are
subsequently supplied by the genuine source bounds. -/
def quarticErrorEnvelope (CE CB CH L : ℝ) : ℝ :=
  24 * L ^ 4 * (CE * L ^ 7 * Real.exp (L / 2) * quarticImageError L) *
      (2 * (CB * L ^ 7 * Real.exp (L / 2)) +
        CE * L ^ 7 * Real.exp (L / 2) * quarticImageError L) +
    (1 + L) * Real.exp (L / 2) * quarticImageError L +
    CH * L ^ 7 * Real.exp (L / 2) * quarticImageError L * (2 + quarticImageError L)

theorem quarticErrorEnvelope_nonneg {CE CB CH L : ℝ}
    (hCE : 0 ≤ CE) (hCB : 0 ≤ CB) (hCH : 0 ≤ CH) (hL : 0 ≤ L) :
    0 ≤ quarticErrorEnvelope CE CB CH L := by
  have he := quarticImageError_nonneg hL
  unfold quarticErrorEnvelope
  positivity

/-- The complete composed error, including the inverse amplification and
both quadratic cross terms, still beats every fixed exponential. -/
theorem quarticErrorEnvelope_mul_exp_tendsto_zero (CE CB CH t : ℝ) :
    Tendsto (fun L : ℝ => quarticErrorEnvelope CE CB CH L * Real.exp (t * L))
      atTop (𝓝 0) := by
  have he : Tendsto quarticImageError atTop (𝓝 0) := by
    simpa using quarticImageError_mul_exp_tendsto_zero 0
  have h18 := pow_mul_exp_mul_quarticImageError_tendsto_zero 18 (t + 1)
  have h7 := pow_mul_exp_mul_quarticImageError_tendsto_zero 7 (t + 1 / 2)
  have h1 := pow_mul_exp_mul_quarticImageError_tendsto_zero 1 (t + 1 / 2)
  have h0 := pow_mul_exp_mul_quarticImageError_tendsto_zero 0 (t + 1 / 2)
  have h := (((((h18.const_mul (48 * CE * CB)).add
    ((h18.mul he).const_mul (24 * CE ^ 2))).add h0).add h1).add
    (h7.const_mul (2 * CH))).add ((h7.mul he).const_mul CH)
  simp only [mul_zero, add_zero] at h
  convert h using 1
  ext L
  have he1 : Real.exp ((t + 1) * L) =
      Real.exp (L / 2) * Real.exp (L / 2) * Real.exp (t * L) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have he2 : Real.exp ((t + 1 / 2) * L) = Real.exp (L / 2) * Real.exp (t * L) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold quarticErrorEnvelope
  rw [he1, he2]
  ring

/-- The lateness threshold is selected before any packet parameters. -/
theorem quarticErrorEnvelope_eventually_lt_exp (CE CB CH M δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ L : ℝ in atTop, quarticErrorEnvelope CE CB CH L < δ * Real.exp (-M * L) := by
  have hlim := quarticErrorEnvelope_mul_exp_tendsto_zero CE CB CH M
  filter_upwards [hlim.eventually (gt_mem_nhds hδ)] with L hL
  have hmul := mul_lt_mul_of_pos_right hL (Real.exp_pos (-M * L))
  have hc : Real.exp (M * L) * Real.exp (-M * L) = 1 := by
    rw [← Real.exp_add]
    simp
  simpa only [mul_assoc, hc, mul_one] using hmul

/-- The polynomial coefficient in the source-only N37 shift estimate. -/
def sourceEtaGrowthConstant : ℝ :=
  ExceptionalZero.step123SameStateWeilConstant * (1 + 4 * Real.pi) ^ 2

theorem sourceEtaGrowthConstant_pos : 0 < sourceEtaGrowthConstant := by
  have h := ExceptionalZero.step123SameStateWeilConstant_pos
  have hp := Real.pi_pos
  unfold sourceEtaGrowthConstant
  positivity

/-- The shift is bounded using the source-only N37 estimate. In particular,
this proof does not replace it by a bound depending on the unknown zero. -/
theorem source_eta_polynomial_bound {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.retained.state.selection.eta ≤ sourceEtaGrowthConstant *
      (fixedOriginalSincTrialAperture a) ^ 7 * Real.exp (fixedOriginalSincTrialAperture a / 2) := by
  let L := fixedOriginalSincTrialAperture a
  let N := originalDetectorQuarticCutoff L
  let CW := ExceptionalZero.step123SameStateWeilConstant
  have hL : 1 ≤ L := by dsimp [L]; linarith [out.aperture_gt_four]
  have hCW : 0 ≤ CW := ExceptionalZero.step123SameStateWeilConstant_pos.le
  have hrate := (ExceptionalZero.step123ForcingErrorRates_of_threshold out
    out.image_threshold_paid.le).1
  change out.retained.state.selection.eta ≤
    (CW / 2) * (1 + L) * Real.exp (L / 2) * (1 + (2 * Real.pi * N / L) ^ 2) at hrate
  have hmode := quartic_mode_cost_le hL (show N ≤ originalDetectorQuarticCutoff L from le_rfl)
  have hsq : 1 + (2 * Real.pi * N / L) ^ 2 ≤ (1 + 4 * Real.pi) ^ 2 * L ^ 6 := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + (2 * Real.pi * N / L) ^ 2 by positivity)
    have hnon : 0 ≤ Real.sqrt (1 + (2 * Real.pi * N / L) ^ 2) := Real.sqrt_nonneg _
    nlinarith [sq_nonneg ((1 + 4 * Real.pi) * L ^ 3 - Real.sqrt (1 + (2 * Real.pi * N / L) ^ 2))]
  calc
    out.retained.state.selection.eta ≤
        (CW / 2) * (1 + L) * Real.exp (L / 2) * (1 + (2 * Real.pi * N / L) ^ 2) := hrate
    _ ≤ (CW / 2) * (2 * L) * Real.exp (L / 2) * ((1 + 4 * Real.pi) ^ 2 * L ^ 6) := by
      gcongr
      linarith
    _ = sourceEtaGrowthConstant * L ^ 7 * Real.exp (L / 2) := by
      unfold sourceEtaGrowthConstant
      dsimp [CW]
      ring

/-- The actual detector-shift inverse, not the ground-shift inverse, has
a polynomial budget when beta is positive. -/
theorem detector_inverse_polynomial_bound {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) (hβ : 0 < β) :
    ‖(nativeDetectorPredecessorEquiv σ out.retained.state.inverses).symm.toLinearMap.toContinuousLinearMap‖ ≤
      24 * (fixedOriginalSincTrialAperture a) ^ 4 := by
  let L := fixedOriginalSincTrialAperture a
  let N := originalDetectorQuarticCutoff L
  have hL : 1 ≤ L := by dsimp [L]; linarith [out.aperture_gt_four]
  have he : 1 ≤ Real.exp (β * L) := Real.one_le_exp_iff.mpr (by positivity)
  have hN : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
  calc
    _ ≤ 12 * ((N - 1 : ℕ) : ℝ) / Real.exp (β * L) := out.detector_inverse_budget
    _ ≤ 12 * ((N - 1 : ℕ) : ℝ) := div_le_self (by positivity) he
    _ ≤ 12 * (N : ℝ) := by gcongr
    _ ≤ 12 * (2 * L ^ 4) := by gcongr; exact quarticCutoff_le_two_pow_four hL
    _ = 24 * L ^ 4 := by ring

def sourceForcingGrowthConstant : ℝ :=
  2 * sourceWeilBoundConstant * (1 + 4 * Real.pi) ^ 2 + sourceEtaGrowthConstant

def sourceForcingErrorGrowthConstant : ℝ :=
  2 * ExceptionalZero.step123SameStateForcingConstant * (1 + 4 * Real.pi) +
    sourceEtaGrowthConstant

theorem sourceForcingGrowthConstant_pos : 0 < sourceForcingGrowthConstant := by
  have h := sourceWeilBoundConstant_pos
  have hη := sourceEtaGrowthConstant_pos
  have hp := Real.pi_pos
  unfold sourceForcingGrowthConstant
  positivity

theorem sourceForcingErrorGrowthConstant_pos : 0 < sourceForcingErrorGrowthConstant := by
  have h := ExceptionalZero.step123SameStateForcingConstant_pos
  have hη := sourceEtaGrowthConstant_pos
  have hp := Real.pi_pos
  unfold sourceForcingErrorGrowthConstant
  positivity

/-- The finite forcing budget is controlled uniformly in the actual
predecessor cutoff by the literal quartic detector cutoff. -/
theorem finiteForcingBudget_polynomial_bound {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    finiteForcingBudget out ≤ sourceForcingGrowthConstant *
      (fixedOriginalSincTrialAperture a) ^ 7 * Real.exp (fixedOriginalSincTrialAperture a / 2) := by
  let L := fixedOriginalSincTrialAperture a
  let N := originalDetectorQuarticCutoff L
  let K := out.retained.state.selection.cutoff
  let M := 1 + 4 * Real.pi
  have hL : 1 ≤ L := by dsimp [L]; linarith [out.aperture_gt_four]
  have hCQ : 0 ≤ sourceWeilBoundConstant := sourceWeilBoundConstant_pos.le
  have hN : sourceFiniteModeCost L N ≤ M * L ^ 3 := quartic_mode_cost_le hL le_rfl
  have hK : sourceFiniteModeCost L (K - 1) ≤ M * L ^ 3 :=
    quartic_mode_cost_le hL ((Nat.sub_le K 1).trans out.retained.state.selection.cutoff_le_detector)
  have hN0 : 0 ≤ sourceFiniteModeCost L N := Real.sqrt_nonneg _
  have hK0 : 0 ≤ sourceFiniteModeCost L (K - 1) := Real.sqrt_nonneg _
  have hη := source_eta_polynomial_bound out
  change finiteForcingBudget out ≤ sourceForcingGrowthConstant * L ^ 7 * Real.exp (L / 2)
  calc
    finiteForcingBudget out ≤
        sourceWeilBoundConstant * (2 * L) * Real.exp (L / 2) * (M * L ^ 3) * (M * L ^ 3) +
          sourceEtaGrowthConstant * L ^ 7 * Real.exp (L / 2) := by
      unfold finiteForcingBudget
      dsimp only
      gcongr
      change 1 + L ≤ 2 * L
      linarith
    _ = sourceForcingGrowthConstant * L ^ 7 * Real.exp (L / 2) := by
      unfold sourceForcingGrowthConstant
      dsimp [M]
      ring

/-- The complete source forcing error includes the actual eta channel;
its coefficient is bounded before a packet is selected. -/
theorem sourceForcingErrorBudget_polynomial_bound {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    sourceForcingErrorBudget out ≤ sourceForcingErrorGrowthConstant *
      (fixedOriginalSincTrialAperture a) ^ 7 * Real.exp (fixedOriginalSincTrialAperture a / 2) *
        quarticImageError (fixedOriginalSincTrialAperture a) := by
  let L := fixedOriginalSincTrialAperture a
  let K := out.retained.state.selection.cutoff
  let CF := ExceptionalZero.step123SameStateForcingConstant
  let M := 1 + 4 * Real.pi
  have hL : 1 ≤ L := by dsimp [L]; linarith [out.aperture_gt_four]
  have hCF : 0 ≤ CF := ExceptionalZero.step123SameStateForcingConstant_pos.le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hK : sourceFiniteModeCost L (K - 1) ≤ M * L ^ 3 :=
    quartic_mode_cost_le hL ((Nat.sub_le K 1).trans out.retained.state.selection.cutoff_le_detector)
  have hK0 : 0 ≤ sourceFiniteModeCost L (K - 1) := Real.sqrt_nonneg _
  have hη := source_eta_polynomial_bound out
  have hp : L ^ 4 ≤ L ^ 7 := pow_le_pow_right₀ hL (by norm_num)
  have hbase : CF * (1 + L) * Real.exp (L / 2) * sourceFiniteModeCost L (K - 1) +
      out.retained.state.selection.eta ≤
        sourceForcingErrorGrowthConstant * L ^ 7 * Real.exp (L / 2) := by
    calc
      _ ≤ CF * (2 * L) * Real.exp (L / 2) * (M * L ^ 3) +
          sourceEtaGrowthConstant * L ^ 7 * Real.exp (L / 2) := by
        gcongr
        linarith
      _ = (2 * CF * M) * L ^ 4 * Real.exp (L / 2) +
          sourceEtaGrowthConstant * L ^ 7 * Real.exp (L / 2) := by ring
      _ ≤ (2 * CF * M) * L ^ 7 * Real.exp (L / 2) +
          sourceEtaGrowthConstant * L ^ 7 * Real.exp (L / 2) := by gcongr
      _ = sourceForcingErrorGrowthConstant * L ^ 7 * Real.exp (L / 2) := by
        unfold sourceForcingErrorGrowthConstant
        dsimp [CF, M]
        ring
  change (CF * (1 + L) * Real.exp (L / 2) * sourceFiniteModeCost L (K - 1) +
    out.retained.state.selection.eta) * quarticImageError L ≤ _
  exact mul_le_mul_of_nonneg_right hbase (quarticImageError_nonneg (by linarith))

/-- All constants in this function depend only on the source. -/
def sourceSchurUniformEnvelope (L : ℝ) : ℝ :=
  quarticErrorEnvelope sourceForcingErrorGrowthConstant sourceForcingGrowthConstant
    sourceEtaGrowthConstant L

/-- Every term of the actual finite estimate is dominated, including the
direct native-form error and the eta-weighted physical-mass error. -/
theorem sourceSchurErrorBudget_le_uniformEnvelope {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) (hβ : 0 < β) :
    sourceSchurErrorBudget out ≤ sourceSchurUniformEnvelope (fixedOriginalSincTrialAperture a) := by
  let L := fixedOriginalSincTrialAperture a
  let N := originalDetectorQuarticCutoff L
  have hL : 1 ≤ L := by dsimp [L]; linarith [out.aperture_gt_four]
  have hA : sourceInverseBudget out ≤ 24 * L ^ 4 := by
    have he : 1 ≤ Real.exp (β * L) := Real.one_le_exp_iff.mpr (by positivity)
    have hN : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr (Nat.sub_le _ _)
    calc
      _ ≤ 12 * ((N - 1 : ℕ) : ℝ) := div_le_self (by positivity) he
      _ ≤ 12 * (N : ℝ) := by gcongr
      _ ≤ 12 * (2 * L ^ 4) := by gcongr; exact quarticCutoff_le_two_pow_four hL
      _ = 24 * L ^ 4 := by ring
  have hE := sourceForcingErrorBudget_polynomial_bound out
  have hB := finiteForcingBudget_polynomial_bound out
  have hη := source_eta_polynomial_bound out
  have hE0 := sourceForcingErrorBudget_nonneg out
  have hB0 := finiteForcingBudget_nonneg out
  have hA0 := sourceInverseBudget_nonneg out
  have he0 := quarticImageError_nonneg (show 0 ≤ L by linarith)
  have hCE0 := sourceForcingErrorGrowthConstant_pos.le
  have hCB0 := sourceForcingGrowthConstant_pos.le
  have hCH0 := sourceEtaGrowthConstant_pos.le
  have hQ : sourceEnergyErrorBudget L = (1 + L) * Real.exp (L / 2) * quarticImageError L := by
    unfold sourceEnergyErrorBudget quarticImageError
    have he : Real.exp (L / 2 - originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
        originalDetectorQuarticRootScale L) = Real.exp (L / 2) *
        Real.exp (-originalDetectorRetainedDecayRate UniversalSinc.fixedScale *
          originalDetectorQuarticRootScale L) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [he]
    ring
  unfold sourceSchurErrorBudget sourceSchurUniformEnvelope quarticErrorEnvelope
  change sourceInverseBudget out * sourceForcingErrorBudget out *
      (2 * finiteForcingBudget out + sourceForcingErrorBudget out) + sourceEnergyErrorBudget L +
      out.retained.state.selection.eta * quarticImageError L * (2 + quarticImageError L) ≤ _
  rw [hQ]
  gcongr

/-- The actual source-only full envelope tends to zero after every fixed
exponential weighting. No off-line-zero or packet hypothesis enters. -/
theorem sourceSchurUniformEnvelope_mul_exp_tendsto_zero (M : ℝ) :
    Tendsto (fun L : ℝ => sourceSchurUniformEnvelope L * Real.exp (M * L)) atTop (𝓝 0) :=
  quarticErrorEnvelope_mul_exp_tendsto_zero _ _ _ M

/-- The universal threshold precedes beta, phase, separation and packet.
The bound concerns the complete genuine-source Schur expression. -/
theorem exists_uniform_source_schur_error_threshold (M δ : ℝ) (hδ : 0 < δ) :
    ∃ L₀ : ℝ, ∀ (β : ℝ) (σ : ReversalParity) (a : ℝ)
      (out : Step123NativeOutput β σ a), 0 < β → L₀ ≤ fixedOriginalSincTrialAperture a →
      |detectorSchurLoss out - smoothSourceMain out| <
        δ * Real.exp (-M * fixedOriginalSincTrialAperture a) := by
  obtain ⟨L₀, hL₀⟩ := (eventually_atTop.1
    (quarticErrorEnvelope_eventually_lt_exp sourceForcingErrorGrowthConstant
      sourceForcingGrowthConstant sourceEtaGrowthConstant M δ hδ))
  refine ⟨L₀, ?_⟩
  intro β σ a out hβ hL
  exact (detectorSchurLoss_sub_smoothSourceMain_bound out).trans_lt
    ((sourceSchurErrorBudget_le_uniformEnvelope out hβ).trans_lt (hL₀ _ hL))

/-- A generated detector cannot hide its exponential lower bound in the
finite-image error: it survives in the complete smooth-source expression.
This is a necessary lower bound, not the missing arithmetic upper bound. -/
theorem exists_uniform_smooth_source_main_lower_threshold :
    ∃ L₀ : ℝ, ∀ (β : ℝ) (σ : ReversalParity) (a : ℝ)
      (out : Step123NativeOutput β σ a), 0 < β → L₀ ≤ fixedOriginalSincTrialAperture a →
      Real.exp (β * fixedOriginalSincTrialAperture a) / 4 < smoothSourceMain out := by
  obtain ⟨L₀, hL₀⟩ := exists_uniform_source_schur_error_threshold 0 (1 / 4) (by norm_num)
  refine ⟨L₀, ?_⟩
  intro β σ a out hβ hL
  have herr := hL₀ β σ a out hβ hL
  simp only [neg_zero, zero_mul, Real.exp_zero, mul_one] at herr
  have hgap := detectorSchurLoss_lower out
  have he : 1 ≤ Real.exp (β * fixedOriginalSincTrialAperture a) :=
    Real.one_le_exp_iff.mpr (mul_nonneg hβ.le out.aperture_pos.le)
  have hd := (abs_lt.mp herr).2
  linarith

/-- The preceding lower bound applies to the actual zero-indexed complete
producer output, with its own positive beta and its paid lateness. -/
theorem exists_generated_smooth_source_main_lower_threshold :
    ∃ L₀ : ℝ, ∀ (ρ : zetaZeroConfig.carrier) (β : ℝ) (σ : ReversalParity) (R : ℝ)
      (g : ExceptionalZero.GeneratedStep123CompleteOutput ρ β σ R), L₀ ≤ R →
      Real.exp (β * fixedOriginalSincTrialAperture g.generated.sourceData.separation) / 4 <
        smoothSourceMain g.generated.native := by
  obtain ⟨L₀, hL₀⟩ := exists_uniform_smooth_source_main_lower_threshold
  refine ⟨L₀, ?_⟩
  intro ρ β σ R g hR
  apply hL₀ β σ _ g.generated.native g.generated.beta_pos
  exact hR.trans ((le_max_left R ExceptionalZero.step123SameStateThreshold).trans
    g.thresholds_paid.le)

end Zeta23.OPICARound4
