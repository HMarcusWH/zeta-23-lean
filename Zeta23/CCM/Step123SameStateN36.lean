import Zeta23.CCM.OriginalDetectorActualForcingError
import Zeta23.CCM.OriginalSincNativeConvolution
import Zeta23.CCM.OriginalDetectorFourHistoryLocalXBound

/-! Original-detector forcing channels on identical predecessor tests.
The exact Archimedean, pole, four signed histories, shift and approximation
channels retain the fixed source. The local 16κ bound is in terms of X;
no bound on X, Step 4 premise, D2 certificate or RH is proved here. -/

noncomputable section

open MeasureTheory Set Complex
open scoped ComplexConjugate

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

/-- Zero-lag mixed correlation in physical form. -/
theorem n36_weilTest_zero_eq_pairing (f v : ℝ → ℂ) :
    EF.weilTest f v 0 = ∫ x : ℝ, f x * conj (v x) := by
  unfold EF.weilTest
  simp only [convolution_def, ContinuousLinearMap.mul_apply', EF.tilde, neg_sub,
    sub_zero]

private theorem n36_pair_integrable {r v : ℝ → ℂ}
    (hr : Continuous r) (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (fun x : ℝ => r x * conj (v x)) :=
  (hr.mul (Complex.continuous_conj.comp hv)).integrable_of_hasCompactSupport
    ((hvc.comp_left (g := fun z : ℂ => conj z) (map_zero _)).mul_left)

/-- Additivity of the Archimedean response on compact C2 sources. -/
theorem n36_nativeWeilArchResponse_add {f h : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) (x : ℝ) :
    nativeWeilArchResponse (f + h) x =
      nativeWeilArchResponse f x + nativeWeilArchResponse h x := by
  have hFT (ξ : ℝ) : paperFT (f + h) (ξ : ℂ) = paperFT f (ξ : ℂ) + paperFT h (ξ : ℂ) := by
    have hphase : Continuous (fun u : ℝ => Complex.exp (Complex.I * (ξ : ℂ) * (u : ℂ))) := by
      fun_prop
    have hif : Integrable (fun u : ℝ => f u * Complex.exp (Complex.I * (ξ : ℂ) * (u : ℂ))) :=
      (hf.continuous.mul hphase).integrable_of_hasCompactSupport hfc.mul_right
    have hih : Integrable (fun u : ℝ => h u * Complex.exp (Complex.I * (ξ : ℂ) * (u : ℂ))) :=
      (hh.continuous.mul hphase).integrable_of_hasCompactSupport hhc.mul_right
    unfold paperFT
    rw [← integral_add hif hih]
    apply integral_congr_ae
    filter_upwards with u
    simp only [Pi.add_apply]
    ring
  have hint {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
      Integrable (fun ξ : ℝ => paperFT g (ξ : ℂ) * (EF.gammaBracket ξ : ℂ) *
        Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) := by
    have hk := nativeWeilArch_fourier_integrable hg hgc
    refine hk.norm.mono' (hk.aestronglyMeasurable.mul
      (by fun_prop : Continuous (fun ξ : ℝ =>
        Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)))).aestronglyMeasurable) ?_
    filter_upwards with ξ
    rw [norm_mul, Complex.norm_exp]
    simp
  unfold nativeWeilArchResponse
  rw [← mul_add, ← integral_add (hint hf hfc) (hint hh hhc)]
  congr 1
  apply integral_congr_ae
  filter_upwards with ξ
  rw [hFT ξ]
  ring

/-- Additivity of the elementary-pole response on compact continuous sources. -/
theorem n36_nativeWeilPoleResponse_add {f h : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hh : Continuous h) (hhc : HasCompactSupport h) (x : ℝ) :
    nativeWeilPoleResponse (f + h) x =
      nativeWeilPoleResponse f x + nativeWeilPoleResponse h x := by
  have hi {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) (c : ℝ) :
      Integrable (fun t : ℝ => (Real.exp (c * t) : ℂ) * g t) :=
    ((by fun_prop : Continuous (fun t : ℝ => (Real.exp (c * t) : ℂ))).mul hg
      ).integrable_of_hasCompactSupport hgc.mul_left
  have hm (g : ℝ → ℂ) : (fun t : ℝ => (Real.exp (-t / 2) : ℂ) * g t) =
      fun t : ℝ => (Real.exp ((-1 / 2) * t) : ℂ) * g t := by
    funext t; congr 3; ring
  have hp (g : ℝ → ℂ) : (fun t : ℝ => (Real.exp (t / 2) : ℂ) * g t) =
      fun t : ℝ => (Real.exp ((1 / 2) * t) : ℂ) * g t := by
    funext t; congr 3; ring
  have hsplit (c : ℝ) :
      (∫ t : ℝ, (Real.exp (c * t) : ℂ) * (f + h) t) =
        (∫ t : ℝ, (Real.exp (c * t) : ℂ) * f t) +
          ∫ t : ℝ, (Real.exp (c * t) : ℂ) * h t := by
    rw [← integral_add (hi hf hfc c) (hi hh hhc c)]
    apply integral_congr_ae
    filter_upwards with t
    simp only [Pi.add_apply]
    ring
  unfold nativeWeilPoleResponse
  rw [hm, hm f, hm h, hp, hp f, hp h, hsplit, hsplit]
  ring

/-- Additivity of the prime response, with ONE common finite history
cutoff for both sources at the given point. -/
theorem n36_nativeWeilPrimeResponse_add {f h : ℝ → ℂ}
    (hfc : HasCompactSupport f) (hhc : HasCompactSupport h) (x : ℝ) :
    nativeWeilPrimeResponse (f + h) x =
      nativeWeilPrimeResponse f x + nativeWeilPrimeResponse h x := by
  obtain ⟨Rf, hRf⟩ := EF.exists_abs_le_of_hasCompactSupport hfc
  obtain ⟨Rh, hRh⟩ := EF.exists_abs_le_of_hasCompactSupport hhc
  let R := max Rf Rh
  have hRf' : ∀ y, f y ≠ 0 → |y| ≤ R := fun y hy => (hRf y hy).trans (le_max_left _ _)
  have hRh' : ∀ y, h y ≠ 0 → |y| ≤ R := fun y hy => (hRh y hy).trans (le_max_right _ _)
  have hRfh : ∀ y, (f + h) y ≠ 0 → |y| ≤ R := by
    intro y hy
    by_cases hfy : f y = 0
    · have hhy : h y ≠ 0 := by
        intro hz
        apply hy
        simp [Pi.add_apply, hfy, hz]
      exact hRh' y hhy
    · exact hRf' y hfy
  rw [nativeWeilPrimeResponse_eq_history_sum hRfh (le_refl |x|),
    nativeWeilPrimeResponse_eq_history_sum hRf' (le_refl |x|),
    nativeWeilPrimeResponse_eq_history_sum hRh' (le_refl |x|),
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  simp only [Pi.add_apply]
  ring

/-- Additivity of the complete literal response. -/
theorem n36_nativeWeilResponse_add {f h : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hh : ContDiff ℝ 2 h) (hhc : HasCompactSupport h) (x : ℝ) :
    nativeWeilResponse (f + h) x = nativeWeilResponse f x + nativeWeilResponse h x := by
  rw [nativeWeilResponse_decomposition, nativeWeilResponse_decomposition,
    nativeWeilResponse_decomposition,
    n36_nativeWeilArchResponse_add hf hfc hh hhc,
    n36_nativeWeilPoleResponse_add hf.continuous hfc hh.continuous hhc,
    n36_nativeWeilPrimeResponse_add hfc hhc]
  ring

/-- Both original lobes are exactly pole neutral. -/
theorem n36_fixedOriginalSincPhaseTrial_paperFT_poles (σ a : ℝ) :
    paperFT (fixedOriginalSincPhaseTrial σ a) (Complex.I / 2) = 0 ∧
      paperFT (fixedOriginalSincPhaseTrial σ a) (-Complex.I / 2) = 0 := by
  have hk : ContDiff ℝ 2 fixedOriginalSincKernel :=
    (contDiff_originalSincTest UniversalSinc.fixedScale_pos).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hkc : HasCompactSupport fixedOriginalSincKernel :=
    hasCompactSupport_originalSincTest UniversalSinc.fixedScale_pos
  obtain ⟨hp, hm⟩ := paperFT_originalSincTest_elementary_pair UniversalSinc.fixedScale_pos
  have hp' : paperFT fixedOriginalSincKernel (Complex.I / 2) = 0 := hp
  have hm' : paperFT fixedOriginalSincKernel (-Complex.I / 2) = 0 := hm
  constructor
  · unfold fixedOriginalSincPhaseTrial
    rw [paperFT_translateRight, paperFT_twoTranslateCombination hk hkc,
      paperFT_translateRight, hp']
    simp
  · unfold fixedOriginalSincPhaseTrial
    rw [paperFT_translateRight, paperFT_twoTranslateCombination hk hkc,
      paperFT_translateRight, hm']
    simp

/-- Hence the literal elementary-pole response of the original trial
vanishes identically. -/
theorem n36_originalTrial_poleResponse_eq_zero (σ a x : ℝ) :
    nativeWeilPoleResponse (fixedOriginalSincPhaseTrial σ a) x = 0 := by
  obtain ⟨hp, hm⟩ := n36_fixedOriginalSincPhaseTrial_paperFT_poles σ a
  have hfp := nativePaperFT_imaginary (fixedOriginalSincPhaseTrial σ a) (1 / 2)
  have hfm := nativePaperFT_imaginary (fixedOriginalSincPhaseTrial σ a) (-1 / 2)
  have hargplus : (((1 / 2 : ℝ) : ℂ) * Complex.I) = Complex.I / 2 := by push_cast; ring
  have hargminus : (((-1 / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I / 2 := by push_cast; ring
  rw [hargplus, hp] at hfp
  rw [hargminus, hm] at hfm
  have ep (t : ℝ) : -(1 / 2 : ℝ) * t = -t / 2 := by ring
  have em (t : ℝ) : -(-1 / 2 : ℝ) * t = t / 2 := by ring
  simp only [ep, em] at hfp hfm
  unfold nativeWeilPoleResponse
  rw [← hfp, ← hfm]
  ring

/-! ### Native finite tests: regularity and predecessor realization -/

/-- Every native pole-neutral vector synthesizes a C2 compact physical
test supported in the aperture. -/
theorem n36_nativeSynthesis_regular (σ : ReversalParity) {L : ℝ} (hL : 0 < L)
    (K : ℕ) (v : nativePoleNeutralParitySpace σ L K) :
    ContDiff ℝ 2 (finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v)) ∧
      HasCompactSupport
        (finitePhysicalSynthesis L K (canonicalNativeCoefficientInclusion σ L K v)) := by
  have hLegal : canonicalNativeCoefficientInclusion σ L K v ∈ euclideanBoundaryFlatSubspace K := by
    rw [canonicalNativeCoefficientInclusion_eq_ambient]
    exact nativePoleNeutralParityAmbient_legal σ L K v
  exact ⟨contDiff_localizedFiniteVector_of_boundaryFlat K _ hL
      ((mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat K _).mp hLegal),
    localizedFiniteVector_hasCompactSupport L K _⟩

/-- The detector-level physical test of an embedded predecessor vector is
literally the predecessor-level test: centered zero extension does not
change the physical function. -/
theorem n36_predecessorEmbedding_synthesis (σ : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL)
    (v : nativePoleNeutralParitySpace σ L (s.cutoff - 1)) :
    finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd
        (nativeDetectorPredecessorEmbedding σ s v)) =
      finitePhysicalSynthesis L (s.cutoff - 1)
        (canonicalNativeCoefficientInclusion σ L (s.cutoff - 1) v) := by
  have hc : canonicalNativeCoefficientInclusion σ L Kd
      (nativeDetectorPredecessorEmbedding σ s v) =
      euclideanCenteredZeroExtend ((Nat.sub_le s.cutoff 1).trans s.cutoff_le_detector)
        (canonicalNativeCoefficientInclusion σ L (s.cutoff - 1) v) := by
    cases σ <;> rfl
  unfold finitePhysicalSynthesis
  rw [hc, euclideanCenteredZeroExtend_coordinates, localizedFiniteVector_centeredZeroExtend]

/-- The coefficient pairing of an embedded predecessor vector with a
detector vector is the zero-lag physical correlation of their syntheses. -/
theorem n36_predecessorEmbedding_inner_eq_weilTest (σ : ReversalParity) {L D : ℝ} {Kd : ℕ}
    {hL : 0 < L} (s : NativeDeepThresholdGroundData L Kd D hL)
    (p : nativePoleNeutralParitySpace σ L Kd)
    (v : nativePoleNeutralParitySpace σ L (s.cutoff - 1)) :
    inner ℂ (nativeDetectorPredecessorEmbedding σ s v) p =
      EF.weilTest
        (finitePhysicalSynthesis L Kd (canonicalNativeCoefficientInclusion σ L Kd p))
        (finitePhysicalSynthesis L (s.cutoff - 1)
          (canonicalNativeCoefficientInclusion σ L (s.cutoff - 1) v)) 0 := by
  rw [n36_weilTest_zero_eq_pairing,
    ← (canonicalNativePhysicalIsometry σ hL Kd).inner_map_map,
    canonicalNativePhysicalIsometry_predecessor σ s v, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [canonicalNativePhysicalIsometry_ae σ hL (s.cutoff - 1) v,
    canonicalNativePhysicalIsometry_ae σ hL Kd p] with x hv hp
  rw [hv, hp]
  simp only [RCLike.inner_apply]

/-! ### The stored packet's identical test and source channels -/

/-- The identical native predecessor physical test used by every channel:
the same form as in `Step123NativeOutput.actualProjectedForcing_error_bound`. -/
def Step123NativeOutput.forcingTest
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) : ℝ → ℂ :=
  finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
    (out.retained.state.selection.cutoff - 1)
    (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1) v)

/-- The physical synthesis of the stored finite detector at its own cutoff. -/
def Step123NativeOutput.storedFiniteDetector
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : ℝ → ℂ :=
  finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
    (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
      (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a))
      out.retained.state.detector)

/-- Archimedean channel of the ORIGINAL smooth trial on the identical test. -/
def Step123NativeOutput.archChannel
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) : ℂ :=
  ∫ x : ℝ, nativeWeilArchResponse out.originalTrial x * conj (out.forcingTest v x)

/-- Elementary-pole channel of the ORIGINAL smooth trial on the identical test. -/
def Step123NativeOutput.poleChannel
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) : ℂ :=
  ∫ x : ℝ, nativeWeilPoleResponse out.originalTrial x * conj (out.forcingTest v x)

/-- Prime channel: the STORED four signed original prime histories
(`out.smoothOriginal.primeHistories`) on the identical test. -/
def Step123NativeOutput.primeChannel
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) : ℂ :=
  ∫ x : ℝ, out.smoothOriginal.primeHistories x * conj (out.forcingTest v x)

/-- One literal `F_k = Π k` history channel at the argument map `φ`, on the
identical test. -/
def Step123NativeOutput.fkHistoryChannel
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) (φ : ℝ → ℝ)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) : ℂ :=
  ∫ x : ℝ, nativeOriginalKernelPrimeField (φ x) * conj (out.forcingTest v x)

/-- `+eta` spectral-shift channel of the ORIGINAL smooth trial, with the
stored detector shift `eta`, on the identical test. -/
def Step123NativeOutput.spectralShiftChannel
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) : ℂ :=
  (out.retained.state.selection.eta : ℂ) *
    EF.weilTest out.originalTrial (out.forcingTest v) 0

/-- Exact approximation channel: the complete shifted forcing of the
actual finite-minus-smooth source `out.physicalSourceError`. -/
def Step123NativeOutput.approximationChannel
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) : ℂ :=
  zetaZeroConfig.W out.physicalSourceError (out.forcingTest v) +
    (out.retained.state.selection.eta : ℂ) *
      EF.weilTest out.physicalSourceError (out.forcingTest v) 0

/-- The stored finite detector is the original trial plus the actual
physical source error (N13 realization, no approximation). -/
theorem Step123NativeOutput.storedFiniteDetector_eq_originalTrial_add_error
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    out.storedFiniteDetector = out.originalTrial + out.physicalSourceError := by
  unfold Step123NativeOutput.storedFiniteDetector
  rw [out.finitePhysicalSource_eq_originalPadded]
  funext x
  simp only [Step123NativeOutput.physicalSourceError, Step123NativeOutput.originalTrial,
    Pi.add_apply, Pi.sub_apply]
  ring

/-- The stored projected forcing coordinate equals the complete mixed
Weil pairing plus `+eta` zero-lag correlation of the stored finite
detector against the identical test. -/
theorem Step123NativeOutput.n36_forcing_coordinate
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    inner ℂ v out.retained.predecessorForcing =
      zetaZeroConfig.W out.storedFiniteDetector (out.forcingTest v) +
        (out.retained.state.selection.eta : ℂ) *
          EF.weilTest out.storedFiniteDetector (out.forcingTest v) 0 := by
  let s := out.retained.state.selection
  let p := out.retained.state.detector
  obtain ⟨hpC, hpS⟩ := n36_nativeSynthesis_regular σ out.aperture_pos
    (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture a)) p
  obtain ⟨hvC, hvS⟩ := n36_nativeSynthesis_regular σ out.aperture_pos (s.cutoff - 1) v
  rw [out.retained.forcing_eq, originalDetectorNativeForcing_physical_mixed σ s p v,
    n36_predecessorEmbedding_synthesis σ s v,
    n36_predecessorEmbedding_inner_eq_weilTest σ s p v,
    ← nativeWeilResponse_pairing hpC hpS hvC.continuous hvS]
  rfl

/-- Regularity of the three physical sources and of the identical test,
all proved from the stored packet (no caller hypothesis). -/
theorem Step123NativeOutput.n36_sources_regular
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    (ContDiff ℝ 2 out.originalTrial ∧ HasCompactSupport out.originalTrial) ∧
    (ContDiff ℝ 2 out.physicalSourceError ∧ HasCompactSupport out.physicalSourceError) ∧
    (ContDiff ℝ 2 out.storedFiniteDetector ∧ HasCompactSupport out.storedFiniteDetector) ∧
    (ContDiff ℝ 2 (out.forcingTest v) ∧ HasCompactSupport (out.forcingTest v)) := by
  obtain ⟨heC, heS⟩ := out.physicalSourceError_admissible
  exact ⟨⟨fixedOriginalSincPhaseTrial_contDiff _ a,
      fixedOriginalSincPhaseTrial_hasCompactSupport _ a⟩,
    ⟨heC, IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) heS⟩,
    n36_nativeSynthesis_regular σ out.aperture_pos _ out.retained.state.detector,
    n36_nativeSynthesis_regular σ out.aperture_pos _ v⟩

/-- **N36 channel expansion.** On the identical native predecessor test,
the complete shifted forcing of the stored finite detector splits EXACTLY
into the Archimedean, pole and (minus) four-history prime channels of the
original smooth trial, its `+eta` spectral shift, and the exact
approximation channel of `out.physicalSourceError`. -/
theorem Step123NativeOutput.n36_channel_expansion
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    zetaZeroConfig.W out.storedFiniteDetector (out.forcingTest v) +
        (out.retained.state.selection.eta : ℂ) *
          EF.weilTest out.storedFiniteDetector (out.forcingTest v) 0 =
      out.archChannel v + out.poleChannel v - out.primeChannel v +
        out.spectralShiftChannel v + out.approximationChannel v := by
  obtain ⟨⟨hgC, hgS⟩, ⟨heC, heS⟩, ⟨hFC, hFS⟩, ⟨htC, htS⟩⟩ := out.n36_sources_regular v
  set g := out.originalTrial with hg
  set e := out.physicalSourceError with he
  set t := out.forcingTest v with ht
  have hF : out.storedFiniteDetector = g + e :=
    out.storedFiniteDetector_eq_originalTrial_add_error
  have hA := n36_pair_integrable (nativeWeilArchResponse_continuous hgC hgS) htC.continuous htS
  have hP := n36_pair_integrable (nativeWeilPoleResponse_continuous g) htC.continuous htS
  have hN := n36_pair_integrable (nativeWeilPrimeResponse_continuous hgC.continuous hgS)
    htC.continuous htS
  have hE := n36_pair_integrable (nativeWeilResponse_continuous heC heS) htC.continuous htS
  have hg0 := n36_pair_integrable hgC.continuous htC.continuous htS
  have he0 := n36_pair_integrable heC.continuous htC.continuous htS
  have hW : zetaZeroConfig.W out.storedFiniteDetector t =
      ((∫ x : ℝ, nativeWeilArchResponse g x * conj (t x)) +
        (∫ x : ℝ, nativeWeilPoleResponse g x * conj (t x)) -
        ∫ x : ℝ, nativeWeilPrimeResponse g x * conj (t x)) +
      zetaZeroConfig.W e t := by
    have hpt : (fun x : ℝ => nativeWeilResponse out.storedFiniteDetector x * conj (t x)) =
        fun x : ℝ => ((nativeWeilArchResponse g x * conj (t x) +
          nativeWeilPoleResponse g x * conj (t x)) -
          nativeWeilPrimeResponse g x * conj (t x)) +
          nativeWeilResponse e x * conj (t x) := by
      funext x
      rw [hF, n36_nativeWeilResponse_add hgC hgS heC heS x,
        nativeWeilResponse_decomposition g x]
      ring
    have hAP : Integrable (fun x : ℝ => nativeWeilArchResponse g x * conj (t x) +
        nativeWeilPoleResponse g x * conj (t x)) := hA.add hP
    have hAPN : Integrable (fun x : ℝ => (nativeWeilArchResponse g x * conj (t x) +
        nativeWeilPoleResponse g x * conj (t x)) -
        nativeWeilPrimeResponse g x * conj (t x)) := hAP.sub hN
    rw [nativeWeilResponse_pairing hFC hFS htC.continuous htS,
      nativeWeilResponse_pairing heC heS htC.continuous htS, hpt,
      integral_add hAPN hE, integral_sub hAP hN, integral_add hA hP]
  have hT : EF.weilTest out.storedFiniteDetector t 0 =
      EF.weilTest g t 0 + EF.weilTest e t 0 := by
    rw [n36_weilTest_zero_eq_pairing, n36_weilTest_zero_eq_pairing,
      n36_weilTest_zero_eq_pairing, ← integral_add hg0 he0]
    apply integral_congr_ae
    filter_upwards with x
    rw [hF]
    simp only [Pi.add_apply]
    ring
  have hPrime : (∫ x : ℝ, nativeWeilPrimeResponse g x * conj (t x)) = out.primeChannel v := by
    unfold Step123NativeOutput.primeChannel
    apply integral_congr_ae
    filter_upwards with x
    rw [hg, ht, show out.originalTrial =
      fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a from rfl,
      out.smoothOriginal.prime_eq x]
  rw [hW, hT, hPrime]
  unfold Step123NativeOutput.archChannel Step123NativeOutput.poleChannel
    Step123NativeOutput.spectralShiftChannel Step123NativeOutput.approximationChannel
  rw [← hg, ← he, ← ht]
  ring

/-- The pole channel of the original trial vanishes: both original lobes
are exactly pole neutral, so its literal pole response is identically 0. -/
theorem Step123NativeOutput.n36_poleChannel_eq_zero
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    out.poleChannel v = 0 := by
  unfold Step123NativeOutput.poleChannel Step123NativeOutput.originalTrial
  simp only [n36_originalTrial_poleResponse_eq_zero, zero_mul, integral_zero]

/-- The stored prime channel is EXACTLY the signed sum of the four literal
original `F_k = Π k` histories at `x-c`, `c-x`, `L-x-c`, `x+c-L`, with the
actual normalization `κ` and actual phase sign; no reflected term is
dropped. -/
theorem Step123NativeOutput.n36_primeChannel_fourHistories
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    out.primeChannel v =
      (fixedOriginalSincTrialNormalization : ℂ) *
        ((out.fkHistoryChannel (fun x => x - fixedOriginalSincLobeCenter) v +
          out.fkHistoryChannel (fun x => fixedOriginalSincLobeCenter - x) v) +
         (nativeOriginalDetectorPhaseSign σ : ℂ) *
          (out.fkHistoryChannel (fun x =>
              fixedOriginalSincTrialAperture a - x - fixedOriginalSincLobeCenter) v +
           out.fkHistoryChannel (fun x =>
              x + fixedOriginalSincLobeCenter - fixedOriginalSincTrialAperture a) v)) := by
  obtain ⟨-, -, -, ⟨htC, htS⟩⟩ := out.n36_sources_regular v
  set t := out.forcingTest v with ht
  let L := fixedOriginalSincTrialAperture a
  let c := fixedOriginalSincLobeCenter
  let κ : ℂ := (fixedOriginalSincTrialNormalization : ℂ)
  let ς : ℂ := (nativeOriginalDetectorPhaseSign σ : ℂ)
  let F := nativeOriginalKernelPrimeField
  have hF : Continuous F := nativeOriginalKernelPrimeField_contDiff.continuous
  have h1 : Integrable (fun x : ℝ => F (x - c) * conj (t x)) :=
    n36_pair_integrable (hF.comp (by fun_prop)) htC.continuous htS
  have h2 : Integrable (fun x : ℝ => F (c - x) * conj (t x)) :=
    n36_pair_integrable (hF.comp (by fun_prop)) htC.continuous htS
  have h3 : Integrable (fun x : ℝ => F (L - x - c) * conj (t x)) :=
    n36_pair_integrable (hF.comp (by fun_prop)) htC.continuous htS
  have h4 : Integrable (fun x : ℝ => F (x + c - L) * conj (t x)) :=
    n36_pair_integrable (hF.comp (by fun_prop)) htC.continuous htS
  have h12 : Integrable (fun x : ℝ => F (x - c) * conj (t x) + F (c - x) * conj (t x)) :=
    h1.add h2
  have h34 : Integrable (fun x : ℝ =>
      F (L - x - c) * conj (t x) + F (x + c - L) * conj (t x)) := h3.add h4
  have h34s : Integrable (fun x : ℝ =>
      ς * (F (L - x - c) * conj (t x) + F (x + c - L) * conj (t x))) := h34.const_mul ς
  have hpt : (fun x : ℝ => out.smoothOriginal.primeHistories x * conj (t x)) =
      fun x : ℝ => κ * ((F (x - c) * conj (t x) + F (c - x) * conj (t x)) +
        ς * (F (L - x - c) * conj (t x) + F (x + c - L) * conj (t x))) := by
    funext x
    rw [out.smoothOriginal.primeHistories_eq]
    simp only [originalSmoothFourPrimeHistories, κ, ς, F, L, c]
    ring
  unfold Step123NativeOutput.primeChannel Step123NativeOutput.fkHistoryChannel
  rw [← ht, hpt, integral_const_mul, integral_add h12 h34s, integral_add h1 h2,
    integral_const_mul, integral_add h3 h4]

/-- The Archimedean channel is the literal gamma-weighted Fourier pairing
of the original trial with the identical test. -/
theorem Step123NativeOutput.n36_archChannel_fourier
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    out.archChannel v =
      (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ,
        paperFT out.originalTrial (ξ : ℂ) * conj (paperFT (out.forcingTest v) (ξ : ℂ)) *
          (EF.gammaBracket ξ : ℂ) := by
  obtain ⟨⟨hgC, hgS⟩, -, -, ⟨htC, htS⟩⟩ := out.n36_sources_regular v
  exact nativeWeilArchResponse_pairing hgC hgS htC.continuous htS

/-- The stored prime channel is the literal prime-power pairing of the
original trial with the identical test (both translations kept). -/
theorem Step123NativeOutput.n36_primeChannel_primePowers
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    out.primeChannel v =
      ∑' n : ℕ, (nativePrimeCoefficient n : ℂ) *
        (EF.weilTest out.originalTrial (out.forcingTest v) (Real.log n) +
          EF.weilTest out.originalTrial (out.forcingTest v) (-Real.log n)) := by
  obtain ⟨⟨hgC, hgS⟩, -, -, ⟨htC, htS⟩⟩ := out.n36_sources_regular v
  rw [← nativeWeilPrimeResponse_pairing hgC.continuous hgS htC.continuous htS]
  unfold Step123NativeOutput.primeChannel
  apply integral_congr_ae
  filter_upwards with x
  rw [show out.originalTrial =
    fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a from rfl,
    out.smoothOriginal.prime_eq x]

/-- The `+eta` spectral-shift channel is the stored `eta` times the
zero-lag physical correlation of the original trial with the identical test. -/
theorem Step123NativeOutput.n36_spectralShiftChannel_eq
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    out.spectralShiftChannel v =
      (out.retained.state.selection.eta : ℂ) *
        ∫ x : ℝ, out.originalTrial x * conj (out.forcingTest v x) := by
  unfold Step123NativeOutput.spectralShiftChannel
  rw [n36_weilTest_zero_eq_pairing]

/-- The approximation channel is quantitatively controlled by the actual
H1 norm of `out.physicalSourceError`, with the existential constant of
`Step123NativeOutput.actualProjectedForcing_error_bound`. -/
theorem Step123NativeOutput.n36_approximationChannel_bound
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    ∃ C_Q : ℝ, 0 < C_Q ∧
      ∀ (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
        (out.retained.state.selection.cutoff - 1)),
        ‖out.approximationChannel v‖ ≤
          (C_Q * (1 + fixedOriginalSincTrialAperture a) *
            Real.exp (fixedOriginalSincTrialAperture a / 2) *
            Real.sqrt (1 +
              (2 * Real.pi *
                (out.retained.state.selection.cutoff - 1 : ℕ) /
                fixedOriginalSincTrialAperture a) ^ 2) +
            out.retained.state.selection.eta) *
            nativePhysicalH1Norm out.physicalSourceError * ‖v‖ :=
  out.actualProjectedForcing_error_bound

/-- The SAME stored prime channel obeys the existing 16κ local-X bound on
the identical test: only the local `L²[0, L]` norm of the actual native
prime field `X` enters, never a global `X ∈ L²` assumption. -/
theorem Step123NativeOutput.n36_primeChannel_sixteenKappa_bound
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    ‖out.primeChannel v‖ ≤
      16 * fixedOriginalSincTrialNormalization * ‖v‖ *
        Real.sqrt (∫ t in (0 : ℝ)..fixedOriginalSincTrialAperture a,
          nativeOriginalPrimeField t ^ 2) := by
  have ha : UniversalSinc.fixedScale < a :=
    originalDetector_lateSeparation_gt_fixedScale out.aperture_gt_four
  have ha0 : 0 ≤ a := UniversalSinc.fixedScale_pos.le.trans ha.le
  have hτ : |nativeOriginalDetectorPhaseSign σ| ≤ 1 := by
    cases σ <;> simp [nativeOriginalDetectorPhaseSign]
  have hb := originalDetector_nativeTest_primeForcing_le_sixteenKappa σ hτ ha0
    (out.retained.state.selection.cutoff - 1) v
  have heq : out.primeChannel v =
      ∫ x : ℝ, nativeWeilPrimeResponse
          (fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a) x *
        conj (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
          (out.retained.state.selection.cutoff - 1)
          (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
            (out.retained.state.selection.cutoff - 1) v) x) := by
    unfold Step123NativeOutput.primeChannel Step123NativeOutput.forcingTest
    apply integral_congr_ae
    filter_upwards with x
    rw [out.smoothOriginal.prime_eq x]
  rw [heq]
  exact hb

/-- **N36, single equation.** The stored projected forcing coordinate
against every actual native predecessor test equals the Archimedean
channel of the original trial, minus the four literal signed `F_k`
histories (the pole channel having vanished), plus the `+eta` spectral
shift of the original trial, plus the exact approximation channel of
`out.physicalSourceError` -- all on the identical test. -/
theorem Step123NativeOutput.n36_forcing_source_channels_eq
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    inner ℂ v out.retained.predecessorForcing =
      out.archChannel v + out.poleChannel v -
        (fixedOriginalSincTrialNormalization : ℂ) *
          ((out.fkHistoryChannel (fun x => x - fixedOriginalSincLobeCenter) v +
            out.fkHistoryChannel (fun x => fixedOriginalSincLobeCenter - x) v) +
           (nativeOriginalDetectorPhaseSign σ : ℂ) *
            (out.fkHistoryChannel (fun x =>
                fixedOriginalSincTrialAperture a - x - fixedOriginalSincLobeCenter) v +
             out.fkHistoryChannel (fun x =>
                x + fixedOriginalSincLobeCenter - fixedOriginalSincTrialAperture a) v)) +
        out.spectralShiftChannel v + out.approximationChannel v ∧
    out.poleChannel v = 0 := by
  refine ⟨?_, out.n36_poleChannel_eq_zero v⟩
  rw [out.n36_forcing_coordinate v, out.n36_channel_expansion v,
    out.n36_primeChannel_fourHistories v]

/-- **q*X bridge for the stored source.** The kernel of the stored original
trial is the literal `k = P q`; the `F_k = Π k` used by every history
channel satisfies `P F_k = X` with `X` the stored arithmetic view; the
existing correlation bridge `Π (k ⋆ k) = q ⋆ X` holds pointwise; composed
with the convolution exchange it gives `k ⋆ F_k = q ⋆ X`; and `q` has mass
one.  This is a one-way smoothing identity, not a bounded deconvolution. -/
theorem Step123NativeOutput.n36_qX_bridge
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) :
    fixedOriginalSincKernel = universalSincKernel UniversalSinc.fixedScale ∧
    universalSincDifferential nativeOriginalKernelPrimeField =
      (fun t => (out.arithmeticView.1 t : ℂ)) ∧
    (∀ t : ℝ,
      nativeComplexPrimeField (fun u => ∫ x : ℝ,
          universalSincKernel UniversalSinc.fixedScale x *
            universalSincKernel UniversalSinc.fixedScale (u - x)) t =
        ∫ x : ℝ, (universalSincSource UniversalSinc.fixedScale x : ℂ) *
          (out.arithmeticView.1 (t - x) : ℂ)) ∧
    (∀ t : ℝ,
      (∫ x : ℝ, universalSincKernel UniversalSinc.fixedScale x *
          nativeOriginalKernelPrimeField (t - x)) =
        ∫ x : ℝ, (universalSincSource UniversalSinc.fixedScale x : ℂ) *
          (out.arithmeticView.1 (t - x) : ℂ)) ∧
    (∫ x : ℝ, universalSincSource UniversalSinc.fixedScale x) = 1 := by
  have hk : NativeComplexSourceSupported UniversalSinc.fixedScale
      (universalSincKernel UniversalSinc.fixedScale) :=
    universalSincKernel_support UniversalSinc.fixedScale_pos
  have hkc : Continuous (universalSincKernel UniversalSinc.fixedScale) :=
    (universalSincKernel_contDiff UniversalSinc.fixedScale_pos).continuous
  have hqX (t : ℝ) :
      nativeComplexPrimeField (fun u => ∫ x : ℝ,
          universalSincKernel UniversalSinc.fixedScale x *
            universalSincKernel UniversalSinc.fixedScale (u - x)) t =
        ∫ x : ℝ, (universalSincSource UniversalSinc.fixedScale x : ℂ) *
          (out.arithmeticView.1 (t - x) : ℂ) :=
    originalDetector_correlationField_eq_sourceConvolution t
  refine ⟨rfl, nativeOriginalKernelPrimeField_poleImage, hqX, fun t => ?_,
    out.originalSource_mass_one⟩
  exact (nativeComplexPrimeField_convolution hk hk hkc hkc t).symm.trans (hqX t)

/-- **N36 explicit form.** The same single equation with every channel
written out literally on the identical test
`finitePhysicalSynthesis L (cutoff - 1) (canonicalNativeCoefficientInclusion σ L (cutoff - 1) v)`. -/
theorem Step123NativeOutput.n36_forcing_source_channels_explicit
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a)
    (v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1)) :
    inner ℂ v out.retained.predecessorForcing =
      (∫ x : ℝ, nativeWeilArchResponse
          (fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a) x *
        conj (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
          (out.retained.state.selection.cutoff - 1)
          (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
            (out.retained.state.selection.cutoff - 1) v) x)) +
      (∫ x : ℝ, nativeWeilPoleResponse
          (fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a) x *
        conj (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
          (out.retained.state.selection.cutoff - 1)
          (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
            (out.retained.state.selection.cutoff - 1) v) x)) -
      (fixedOriginalSincTrialNormalization : ℂ) *
        (((∫ x : ℝ, nativeOriginalKernelPrimeField (x - fixedOriginalSincLobeCenter) *
              conj (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
                (out.retained.state.selection.cutoff - 1)
                (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
                  (out.retained.state.selection.cutoff - 1) v) x)) +
          (∫ x : ℝ, nativeOriginalKernelPrimeField (fixedOriginalSincLobeCenter - x) *
              conj (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
                (out.retained.state.selection.cutoff - 1)
                (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
                  (out.retained.state.selection.cutoff - 1) v) x))) +
         (nativeOriginalDetectorPhaseSign σ : ℂ) *
          ((∫ x : ℝ, nativeOriginalKernelPrimeField
                (fixedOriginalSincTrialAperture a - x - fixedOriginalSincLobeCenter) *
              conj (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
                (out.retained.state.selection.cutoff - 1)
                (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
                  (out.retained.state.selection.cutoff - 1) v) x)) +
           (∫ x : ℝ, nativeOriginalKernelPrimeField
                (x + fixedOriginalSincLobeCenter - fixedOriginalSincTrialAperture a) *
              conj (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
                (out.retained.state.selection.cutoff - 1)
                (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
                  (out.retained.state.selection.cutoff - 1) v) x)))) +
      (out.retained.state.selection.eta : ℂ) *
        EF.weilTest (fixedOriginalSincPhaseTrial (nativeOriginalDetectorPhaseSign σ) a)
          (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
            (out.retained.state.selection.cutoff - 1)
            (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
              (out.retained.state.selection.cutoff - 1) v)) 0 +
      (zetaZeroConfig.W out.physicalSourceError
          (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
            (out.retained.state.selection.cutoff - 1)
            (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
              (out.retained.state.selection.cutoff - 1) v)) +
        (out.retained.state.selection.eta : ℂ) *
          EF.weilTest out.physicalSourceError
            (finitePhysicalSynthesis (fixedOriginalSincTrialAperture a)
              (out.retained.state.selection.cutoff - 1)
              (canonicalNativeCoefficientInclusion σ (fixedOriginalSincTrialAperture a)
                (out.retained.state.selection.cutoff - 1) v)) 0) :=
  (out.n36_forcing_source_channels_eq v).1

/-- The N36 `forcing.source_channels` certificate: every component is a
statement about the stored packet's own forcing vector, stored detector,
stored original record and stored `eta`, on the identical tests. -/
structure Step123NativeOutput.ForcingSourceChannels
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : Prop where
  coordinate : ∀ v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1),
    inner ℂ v out.retained.predecessorForcing =
      zetaZeroConfig.W out.storedFiniteDetector (out.forcingTest v) +
        (out.retained.state.selection.eta : ℂ) *
          EF.weilTest out.storedFiniteDetector (out.forcingTest v) 0
  finiteDetector_split :
    out.storedFiniteDetector = out.originalTrial + out.physicalSourceError
  expansion : ∀ v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1),
    zetaZeroConfig.W out.storedFiniteDetector (out.forcingTest v) +
        (out.retained.state.selection.eta : ℂ) *
          EF.weilTest out.storedFiniteDetector (out.forcingTest v) 0 =
      out.archChannel v + out.poleChannel v - out.primeChannel v +
        out.spectralShiftChannel v + out.approximationChannel v
  pole_zero : ∀ v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1), out.poleChannel v = 0
  four_histories : ∀ v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1),
    out.primeChannel v =
      (fixedOriginalSincTrialNormalization : ℂ) *
        ((out.fkHistoryChannel (fun x => x - fixedOriginalSincLobeCenter) v +
          out.fkHistoryChannel (fun x => fixedOriginalSincLobeCenter - x) v) +
         (nativeOriginalDetectorPhaseSign σ : ℂ) *
          (out.fkHistoryChannel (fun x =>
              fixedOriginalSincTrialAperture a - x - fixedOriginalSincLobeCenter) v +
           out.fkHistoryChannel (fun x =>
              x + fixedOriginalSincLobeCenter - fixedOriginalSincTrialAperture a) v))
  arch_fourier : ∀ v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1),
    out.archChannel v =
      (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ,
        paperFT out.originalTrial (ξ : ℂ) * conj (paperFT (out.forcingTest v) (ξ : ℂ)) *
          (EF.gammaBracket ξ : ℂ)
  prime_powers : ∀ v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1),
    out.primeChannel v =
      ∑' n : ℕ, (nativePrimeCoefficient n : ℂ) *
        (EF.weilTest out.originalTrial (out.forcingTest v) (Real.log n) +
          EF.weilTest out.originalTrial (out.forcingTest v) (-Real.log n))
  spectral_shift : ∀ v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1),
    out.spectralShiftChannel v =
      (out.retained.state.selection.eta : ℂ) *
        ∫ x : ℝ, out.originalTrial x * conj (out.forcingTest v x)
  prime_local_X_bound : ∀ v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1),
    ‖out.primeChannel v‖ ≤
      16 * fixedOriginalSincTrialNormalization * ‖v‖ *
        Real.sqrt (∫ t in (0 : ℝ)..fixedOriginalSincTrialAperture a,
          nativeOriginalPrimeField t ^ 2)
  approximation_bound : ∃ C_Q : ℝ, 0 < C_Q ∧
    ∀ v : nativePoleNeutralParitySpace σ (fixedOriginalSincTrialAperture a)
      (out.retained.state.selection.cutoff - 1),
      ‖out.approximationChannel v‖ ≤
        (C_Q * (1 + fixedOriginalSincTrialAperture a) *
          Real.exp (fixedOriginalSincTrialAperture a / 2) *
          Real.sqrt (1 +
            (2 * Real.pi *
              (out.retained.state.selection.cutoff - 1 : ℕ) /
              fixedOriginalSincTrialAperture a) ^ 2) +
          out.retained.state.selection.eta) *
          nativePhysicalH1Norm out.physicalSourceError * ‖v‖
  qX_bridge :
    universalSincDifferential nativeOriginalKernelPrimeField =
      (fun t => (out.arithmeticView.1 t : ℂ)) ∧
    ∀ t : ℝ,
      (∫ x : ℝ, universalSincKernel UniversalSinc.fixedScale x *
          nativeOriginalKernelPrimeField (t - x)) =
        ∫ x : ℝ, (universalSincSource UniversalSinc.fixedScale x : ℂ) *
          (out.arithmeticView.1 (t - x) : ℂ)

/-- N36 `forcing.source_channels` for the actual stored packet. -/
theorem Step123NativeOutput.n36_forcingSourceChannels
    {β : ℝ} {σ : ReversalParity} {a : ℝ}
    (out : Step123NativeOutput β σ a) : out.ForcingSourceChannels where
  coordinate := out.n36_forcing_coordinate
  finiteDetector_split := out.storedFiniteDetector_eq_originalTrial_add_error
  expansion := out.n36_channel_expansion
  pole_zero := out.n36_poleChannel_eq_zero
  four_histories := out.n36_primeChannel_fourHistories
  arch_fourier := out.n36_archChannel_fourier
  prime_powers := out.n36_primeChannel_primePowers
  spectral_shift := out.n36_spectralShiftChannel_eq
  prime_local_X_bound := out.n36_primeChannel_sixteenKappa_bound
  approximation_bound := out.n36_approximationChannel_bound
  qX_bridge := ⟨out.n36_qX_bridge.2.1, out.n36_qX_bridge.2.2.2.1⟩

end Zeta23.CCM
#print axioms Zeta23.CCM.n36_weilTest_zero_eq_pairing
#print axioms Zeta23.CCM.n36_nativeWeilArchResponse_add
#print axioms Zeta23.CCM.n36_nativeWeilPoleResponse_add
#print axioms Zeta23.CCM.n36_nativeWeilPrimeResponse_add
#print axioms Zeta23.CCM.n36_nativeWeilResponse_add
#print axioms Zeta23.CCM.n36_fixedOriginalSincPhaseTrial_paperFT_poles
#print axioms Zeta23.CCM.n36_originalTrial_poleResponse_eq_zero
#print axioms Zeta23.CCM.n36_nativeSynthesis_regular
#print axioms Zeta23.CCM.n36_predecessorEmbedding_synthesis
#print axioms Zeta23.CCM.n36_predecessorEmbedding_inner_eq_weilTest
#print axioms Zeta23.CCM.Step123NativeOutput.storedFiniteDetector_eq_originalTrial_add_error
#print axioms Zeta23.CCM.Step123NativeOutput.n36_forcing_coordinate
#print axioms Zeta23.CCM.Step123NativeOutput.n36_sources_regular
#print axioms Zeta23.CCM.Step123NativeOutput.n36_channel_expansion
#print axioms Zeta23.CCM.Step123NativeOutput.n36_poleChannel_eq_zero
#print axioms Zeta23.CCM.Step123NativeOutput.n36_primeChannel_fourHistories
#print axioms Zeta23.CCM.Step123NativeOutput.n36_archChannel_fourier
#print axioms Zeta23.CCM.Step123NativeOutput.n36_primeChannel_primePowers
#print axioms Zeta23.CCM.Step123NativeOutput.n36_spectralShiftChannel_eq
#print axioms Zeta23.CCM.Step123NativeOutput.n36_approximationChannel_bound
#print axioms Zeta23.CCM.Step123NativeOutput.n36_primeChannel_sixteenKappa_bound
#print axioms Zeta23.CCM.Step123NativeOutput.n36_forcing_source_channels_eq
#print axioms Zeta23.CCM.Step123NativeOutput.n36_qX_bridge
#print axioms Zeta23.CCM.Step123NativeOutput.n36_forcing_source_channels_explicit
#print axioms Zeta23.CCM.Step123NativeOutput.n36_forcingSourceChannels
