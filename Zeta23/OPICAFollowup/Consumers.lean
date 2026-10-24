import Zeta23.OPICAFollowup.RobustLaurent
import Zeta23.OPICA.NativeJetAdapter
import Zeta23.OPICAFollowup.BoundaryAmplitude
import Zeta23.OPICAFollowup.MaskedNativeRate
import Zeta23.OPICAFollowup.NativeWindowRate
import Zeta23.OPICAFollowup.MovingSourceWindowRate
import Zeta23.ExceptionalZero.Step4OutputSufficiency

/-!
Actual-source continuation consumers. The word/jet theorem preserves the same
Step123 output. The force/sampling theorem composes F1-F3 at a hypothetical actual
off-line zero. The actual zero-measure span consumer remains OPEN.
-/

noncomputable section
open Complex Set MeasureTheory Filter Metric
open scoped Topology
namespace Zeta23.OPICAFollowup
open Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICA

/-- The selected right zero is the one already used by the native completed
input obstruction of this same Step123 output.  No independent zero is chosen. -/
def step123WordRightZero {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (_out : GeneratedStep123CompleteOutput rho beta phase late) : zetaZeroConfig.carrier :=
  nativeZeroJetRightZero rho

lemma step123WordRightZero_right {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late) :
    1/2 < (step123WordRightZero out : ℂ).re :=
  nativeZeroJetRightZero_re_gt_half rho out.generated.offLine

/-- Full native local-word observation on the SAME existing generated output.
The independent histories are unrestricted beyond NativeWordHistory.  In
particular no joint continuation-domain certificate is added to this root.
The conditional derivative clause covers all positive completion counts,
including p*m=1; the normalized Laurent limit also covers p=0.
-/
theorem step123_word_jet_consumer {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late)
    (w : NativeWord)
    (history : NativeWordHistory ((step123WordRightZero out : ℂ)-1/2)) :
    let rr := step123WordRightZero out
    let hr := step123WordRightZero_right out
    (step123OpicaView out).source = nativeOriginalIntegerDrive ∧
    (step123OpicaView out).field = nativeOriginalPrimeField ∧
    (step123OpicaView out).input = nativeCompletedInput ∧
    Step123SameStateFieldRecord out.generated.native ∧
    GeneratedStep123RangeObstruction rho out.generated.offLine ∧
    zeroMult (rr : ℂ) = zeroMult (rho : ℂ) ∧
    nativeZeroJetParameter rho + (nativeZeroJetDamping rho : ℂ) = (rr : ℂ)-1/2 ∧
    0 < nativeZeroJetDamping rho ∧
    (nativeWordPrimePole rr hr).source = nativeOriginalSource ∧
    (nativeWordPrimePole rr hr).center = (rr : ℂ)-1/2 ∧
    (nativeWordPrimePole rr hr).field = nativePrimeTransformGerm ∧
    (nativeWordPrimePole rr hr).residue =
      -(zeroMult (rho : ℂ) : ℂ)*nativeOriginalSourceLaplace ((rr : ℂ)-1/2) ∧
    (∃ S : ℝ, wordHistorySafeThreshold w history ≤ S ∧ 1/2 ≤ S ∧
      ∀ z : ℂ, S < z.re →
        (∀ term ∈ nativeWordCausalState w rr history,
          Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t)) ∧
        (nativeWordCausalState w rr history).laplace z =
          nativeWordTransformedField w rr history z) ∧
    MeromorphicAt (nativeWordTransformedField w rr history) ((rr : ℂ)-1/2) ∧
    (∀ z : ℂ, nativeWordCorrectedField w rr history z =
      wordUnitFactor w z*riemannZeta (z+1/2)^wordCompletionCount w*nativePrimeTransformGerm z) ∧
    meromorphicOrderAt (nativeWordCorrectedField w rr history) ((rr : ℂ)-1/2) =
      (((wordCompletionCount w*zeroMult (rho : ℂ) : ℕ) : ℤ)-1 : ℤ) ∧
    nativeWordLeadingCoefficient w rr =
      -(zeroMult (rho : ℂ) : ℂ)*nativeOriginalSourceLaplace ((rr : ℂ)-1/2)*
        wordUnitFactor w ((rr : ℂ)-1/2)*
        (iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (rr : ℂ)/
          ((zeroMult (rho : ℂ)).factorial : ℂ))^wordCompletionCount w ∧
    nativeWordLeadingCoefficient w rr ≠ 0 ∧
    Tendsto (fun z => (z-((rr : ℂ)-1/2))^
      (-(((wordCompletionCount w*zeroMult (rho : ℂ) : ℕ) : ℤ)-1))*
        nativeWordCorrectedField w rr history z)
      (𝓝[≠] ((rr : ℂ)-1/2)) (𝓝 (nativeWordLeadingCoefficient w rr)) ∧
    (0 < wordCompletionCount w →
      (nativeWordCorrectedField w rr history =ᶠ[𝓝[≠] ((rr : ℂ)-1/2)]
        nativeWordRegularRepresentative w rr hr) ∧
      AnalyticAt ℂ (nativeWordRegularRepresentative w rr hr) ((rr : ℂ)-1/2) ∧
      (∀ j : ℕ, j < wordCompletionCount w*zeroMult (rho : ℂ)-1 →
        iteratedDeriv j (nativeWordRegularRepresentative w rr hr) ((rr : ℂ)-1/2) = 0) ∧
      iteratedDeriv (wordCompletionCount w*zeroMult (rho : ℂ)-1)
        (nativeWordRegularRepresentative w rr hr) ((rr : ℂ)-1/2) =
        ((wordCompletionCount w*zeroMult (rho : ℂ)-1).factorial : ℂ)*
          nativeWordLeadingCoefficient w rr ∧
      iteratedDeriv (wordCompletionCount w*zeroMult (rho : ℂ)-1)
        (nativeWordRegularRepresentative w rr hr) ((rr : ℂ)-1/2) ≠ 0) ∧
    inner ℂ (nativeZeroJetAdjointWitness rho out.generated.offLine)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho out.generated.offLine).le) =
      (-1 : ℂ)^zeroMult (rho : ℂ)*nativeCompletionRationalMultiplier ((rr : ℂ)-1/2)*
        nativeOriginalSourceLaplace ((rr : ℂ)-1/2)*
          iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (rr : ℂ) ∧
    inner ℂ (nativeZeroJetAdjointWitness rho out.generated.offLine)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho out.generated.offLine).le) ≠ 0 := by
  let rr := step123WordRightZero out
  let hr := step123WordRightZero_right out
  have hm : zeroMult (rr : ℂ) = zeroMult (rho : ℂ) := nativeZeroJetRightZero_mult rho
  have hphysical := nativeWord_corrected_transform w rr hr history
  have horder := nativeWord_order_and_leading w rr hr history
  have hview := step123_output_opica_view_correct out
  dsimp only
  refine ⟨hview.1,hview.2.1,hview.2.2.1,hview.2.2.2.1,hview.2.2.2.2,
    hm,nativeZeroJetParameter_add_damping rho,
    nativeZeroJetDamping_pos rho out.generated.offLine,rfl,rfl,rfl,?_,
    hphysical.1,hphysical.2.1,hphysical.2.2.1,?_,?_,horder.2.2.2.2.2.1,?_,?_,
    native_completed_input_obstruction_jet rho out.generated.offLine,
    native_completed_input_obstruction_ne_zero rho out.generated.offLine⟩
  · change -(zeroMult (rr:ℂ):ℂ)*nativeOriginalSourceLaplace ((rr:ℂ)-1/2)=_
    rw [hm]
  · simpa only [hm] using horder.2.1
  · simp only [nativeWordLeadingCoefficient]
    have hmWord : zeroMult (step123WordRightZero out : ℂ) =
        zeroMult (rho : ℂ) := hm
    rw [hmWord]
  · simpa only [hm] using horder.2.2.2.2.2.2.1
  · intro hp
    simpa only [hm] using nativeWord_first_nonzero_derivative w rr hr history hp

/-- Optional contour companion: its actual common DISK hypotheses and error
budget are explicit. They do not become premises of the local primary above.
No common global continuation domain for the histories is required here. -/
theorem step123_word_contour_consumer {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late) (w : NativeWord)
    (history : NativeWordHistory ((step123WordRightZero out : ℂ)-1/2))
    (raw correction recovery : ℂ→ℂ) (r Eraw Ecorrection Erecovery : ℝ)
    (hr : 0<r)
    (hg : MeromorphicAt (nativeWordObservedField raw correction recovery)
      ((step123WordRightZero out : ℂ)-1/2))
    (hfd : AnalyticOnNhd ℂ (nativeWordCorrectedField w (step123WordRightZero out) history)
      (closedBall ((step123WordRightZero out : ℂ)-1/2) r \ {((step123WordRightZero out : ℂ)-1/2)}))
    (hgd : AnalyticOnNhd ℂ (nativeWordObservedField raw correction recovery)
      (closedBall ((step123WordRightZero out : ℂ)-1/2) r \ {((step123WordRightZero out : ℂ)-1/2)}))
    (hraw : ContourErrorBudget (nativeWordTransformedField w (step123WordRightZero out) history)
      raw ((step123WordRightZero out : ℂ)-1/2) r Eraw)
    (hcorrection : ContourErrorBudget (wordCorrection w history) correction
      ((step123WordRightZero out : ℂ)-1/2) r Ecorrection)
    (hrecovery : ∀ z∈sphere ((step123WordRightZero out : ℂ)-1/2) r, ‖recovery z‖≤Erecovery)
    (hstrict : Eraw+Ecorrection+Erecovery <
      ‖nativeWordLeadingCoefficient w (step123WordRightZero out)‖*
      r^(((wordCompletionCount w*zeroMult (step123WordRightZero out : ℂ):ℕ):ℤ)-1)) :
    ‖laurentObservedCoefficient (nativeWordObservedField raw correction recovery)
      ((step123WordRightZero out : ℂ)-1/2) hg
      (((wordCompletionCount w*zeroMult (step123WordRightZero out : ℂ):ℕ):ℤ)-1) -
      nativeWordLeadingCoefficient w (step123WordRightZero out)‖ ≤
      r^(-(((wordCompletionCount w*zeroMult (step123WordRightZero out : ℂ):ℕ):ℤ)-1))*
      (Eraw+Ecorrection+Erecovery) ∧
    laurentObservedCoefficient (nativeWordObservedField raw correction recovery)
      ((step123WordRightZero out : ℂ)-1/2) hg
      (((wordCompletionCount w*zeroMult (step123WordRightZero out : ℂ):ℕ):ℤ)-1) ≠ 0 := by
  exact (nativeWord_contour_consumer w (step123WordRightZero out)
    (step123WordRightZero_right out) history raw correction recovery r Eraw Ecorrection Erecovery
    hr hg hfd hgd hraw hcorrection hrecovery hstrict).2.2

open scoped Real FourierTransform SchwartzMap ContDiff

section ForceSampling

/-- F1-F3 composed on an actual zero with nonreal κ (every off-line zero): the two Fourier
conventions, the actual lattice force on compact log tests and its transform, the log-unitary
profile with its weak forced equation and arithmetic quotient (in both conventions), the spectral
density, the sample identity b = κ M(κ), and the generic boundary amplitude at the right-half-strip
representative ρ' ∈ {ρ, 1 - ρ} (which has the same κ). The profile is forced: no constant multiple
of it is the Euler image, so this is not a homogeneous eigenproblem. -/
theorem actual_force_sampling_consumer {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : (spectralKappa ρ).im ≠ 0) :
    (∀ (f : ℝ → ℂ) (ξ : ℝ), logFourier f ξ = 𝓕 f (ξ / (2 * π))) ∧
    (∀ (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      nativeLogForce (hc.toSchwartzMap hφ) =
        ∑' n : ℕ, ((((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * φ (Real.log (n + 1)) -
          ∫ t, (Real.exp (t / 2) : ℂ) * φ t) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (𝓕 nativeLogForce) φ = ∫ η : ℝ, riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) * φ η) ∧
    (∀ ξ : ℝ, -(1 / 2 + ξ * I) * logFourier sawtoothWeight ξ = riemannZeta (1 / 2 + ξ * I)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv φ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (zeroProfile ρ) t * φ t =
        spectralKappa ρ * nativeLogForce φ) ∧
    (∀ ξ : ℝ, logFourier (logUnitary (zeroProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ)) ∧
    (∀ η : ℝ, 𝓕 (logUnitary (zeroProfile ρ)) η =
      spectralKappa ρ * riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) /
        ((spectralEnergy (2 * π * η) : ℂ) - spectralKappa ρ)) ∧
    arithmeticSpectralMeasure =
      volume.withDensity (fun ξ : ℝ => ENNReal.ofReal (‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (2 * π))) ∧
    profileSampleDefect ρ = spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ) ∧
    (∃ ρ' : ℂ, (ρ' = ρ ∨ ρ' = 1 - ρ) ∧ 1 / 2 < ρ'.re ∧ ρ'.re < 1 ∧ riemannZeta ρ' = 0 ∧
      spectralKappa ρ' = spectralKappa ρ ∧ boundaryAmplitude ρ' = 0 ∧
      genericForcedProfile ρ' = zeroProfile ρ' ∧
      logUnitary (genericForcedProfile ρ') = logUnitary (zeroProfile ρ)) ∧
    (∀ c : ℂ, ¬ ∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = c * ∫ x in Ioi 0, zeroProfile ρ x * φ x) := by
  have hR : spectralKappa ρ ∈ spectralResolventSet := Or.inl hκ
  have him_k : (spectralKappa ρ).im = (1 - 2 * ρ.re) * ρ.im := by
    simp only [spectralKappa, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    ring
  have hre : ρ.re ≠ 1 / 2 := fun h => hκ (by rw [him_k, h]; ring)
  have him : ρ.im ≠ 0 := fun h => hκ (by rw [him_k, h, mul_zero])
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hz' : riemannZeta (1 - ρ) = 0 := by
    have hn : ∀ n : ℕ, ρ ≠ -n := fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [riemannZeta_one_sub hn hρ1, hz, mul_zero]
  obtain ⟨-, hW, -, hq, hEq⟩ := native_forced_resolvent_unique hz h0 h1 hR
  have hb := (native_sample_stieltjes_identity hz h0 h1 hR).2.2.2.2.2.2.2.2
  obtain ⟨-, -, -, hnot, -⟩ := zero_profile_not_homogeneous_operator_vector ρ hz h0 h1
  obtain ⟨-, -, hw, hF⟩ := sawtooth_actual_mellin_fourier
  refine ⟨logFourier_eq_fourier, (sawtooth_integrable_force_identity).2.2.2.2.2.1, hF, hw, hW, hq,
    fun η => ?_, rfl, hb, ?_, hnot⟩
  · have h := hq (2 * π * η)
    rw [logFourier_eq_fourier, show 2 * π * η / (2 * π) = η by field_simp] at h
    exact h
  · -- the right-half-strip representative
    have hpick : ∃ ρ' : ℂ, (ρ' = ρ ∨ ρ' = 1 - ρ) ∧ 1 / 2 < ρ'.re ∧ ρ'.re < 1 ∧ riemannZeta ρ' = 0 ∧
        spectralKappa ρ' = spectralKappa ρ ∧ ρ'.im ≠ 0 := by
      rcases lt_or_gt_of_ne hre with hlt | hgt
      · refine ⟨1 - ρ, Or.inr rfl, by simp; linarith, by simp; linarith, hz', by
          simp only [spectralKappa]; ring, by simpa using him⟩
      · exact ⟨ρ, Or.inl rfl, hgt, h1, hz, rfl, him⟩
    obtain ⟨ρ', hρ', h12', h1', hz'', hk', him'⟩ := hpick
    have hBA := generic_boundary_amplitude h12' h1'
    have hgen := hBA.2.2.2.2.1 hz''
    have hA : boundaryAmplitude ρ' = 0 := by rw [boundaryAmplitude, hz'', zero_div]
    have hF3 := (generic_forced_profile_unique h12' h1' him').2.2.2.2.2.2.2.1
    refine ⟨ρ', hρ', h12', h1', hz'', hk', hA, hgen, ?_⟩
    rw [hF3, hk', hEq]

end ForceSampling


end Zeta23.OPICAFollowup

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICA
namespace Zeta23.OPICAFollowup

theorem fixed_two_factor_scheduled_mask_rates (T : HorizonSchedule) :
    Tendsto (positiveRate T (fun n => nativeRawHigh 1 2 1
      (logSlackY 2 8 (T.time n)) 2 (T.time n))) atTop (𝓝 nativeZeroDisplacementSup) ∧
    Tendsto (positiveRate T (fun n => nativeAbsorbedHigh 1 2 1 (by norm_num)
      (logSlackY 2 8 (T.time n)) 2 (T.time n))) atTop (𝓝 nativeZeroDisplacementSup) := by
  have hNative : Tendsto (fun t : ℝ => Real.log (1+nativePhysicalWindowEnergy 1 2 t)/(2*t))
      atTop (𝓝 nativeZeroDisplacementSup) := by
    simpa only [nativePhysicalWindowEnergy,nativeLogWindow,sq_abs] using
      native_fixed_source_window_rate 1 2 (by norm_num)
  have h := log_slack_masked_energy_rate_difference 2 1 (by norm_num) (by norm_num)
    2 0 8 (by norm_num) (by norm_num) (by norm_num) T (fun _ => 1)
    (fun _ => by norm_num) (Eventually.of_forall fun n => by simp)
  have hNativeT := hNative.comp T.cofinal
  exact ⟨by simpa only [Function.comp_apply,sub_add_cancel,zero_add] using h.1.add hNativeT,
    by simpa only [Function.comp_apply,sub_add_cancel,zero_add] using h.2.add hNativeT⟩

/-- Original fixed r=2,d=1,C=2,Q=1,K=8 physical consumer. Both complete
high-mask realizations retain the actual theta rate at continuous horizons. -/
theorem fixed_two_factor_mask_rate_theta :
    Tendsto (fun T : ℝ => Real.log (1+max
      (nativeRawHigh 1 2 1 (logSlackY 2 8 T) 2 T) 0)/(2*T)) atTop (𝓝 nativeZeroDisplacementSup) ∧
    Tendsto (fun T : ℝ => Real.log (1+max
      (nativeAbsorbedHigh 1 2 1 (by norm_num) (logSlackY 2 8 T) 2 T) 0)/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) := by
  have along (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop) :
      Tendsto (fun n => Real.log (1+max
        (nativeRawHigh 1 2 1 (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n))
        atTop (𝓝 nativeZeroDisplacementSup) ∧
      Tendsto (fun n => Real.log (1+max
        (nativeAbsorbedHigh 1 2 1 (by norm_num) (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n))
        atTop (𝓝 nativeZeroDisplacementSup) := by
    let T := NativeWindowProof.Asymptotic.normalizedHorizonSchedule time cofinal
    have hEq : ∀ᶠ n : ℕ in atTop, T.time n=time n :=
      (cofinal.eventually_ge_atTop 1).mono fun n hn => max_eq_right hn
    have h := fixed_two_factor_scheduled_mask_rates T
    constructor
    · apply h.1.congr'
      filter_upwards [hEq] with n hn
      simp only [positiveRate,hn]
    · apply h.2.congr'
      filter_upwards [hEq] with n hn
      simp only [positiveRate,hn]
  exact ⟨tendsto_of_seq_tendsto (fun time ht => (along time ht).1),
    tendsto_of_seq_tendsto (fun time ht => (along time ht).2)⟩

theorem originalPrimeField_allDampedL2_of_native_theta_zero
    (hTheta : nativeZeroDisplacementSup=0) : NativeOriginalPrimeFieldAllDampedL2 := by
  obtain ⟨A,hA,hEnv⟩ := native_field_theta_envelope
  let K := nativeFieldOrderConstant 0
  have hK : 0 < K := (hEnv 0).1
  have hBound (t : ℝ) (ht : 0 ≤ t) : |nativeOriginalPrimeField t| ≤ K := by
    have h := (hEnv 0).2.1 t ht
    simpa only [hTheta,zero_mul,Real.exp_zero,mul_one,
      sourceFamily_zero_eq_original.2.1,K] using h
  intro epsilon hepsilon
  have hDom : Integrable ((Ici (0 : ℝ)).indicator (fun t : ℝ => K^2*Real.exp (-2*epsilon*t))) :=
    ((integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      ((integrableOn_exp_mul_Ioi (by linarith : -2*epsilon<0) 0).const_mul (K^2))).integrable_indicator measurableSet_Ici
  apply (memLp_two_iff_integrable_sq_norm
    (nativeOriginalDampedPrimeField_continuous epsilon).aestronglyMeasurable).mpr
  apply hDom.mono' ((nativeOriginalDampedPrimeField_continuous epsilon).aestronglyMeasurable.norm.pow 2)
  filter_upwards with t
  change ‖‖nativeOriginalDampedPrimeField epsilon t‖^2‖ ≤ _
  by_cases ht : 0 ≤ t
  · have htmem : t ∈ Ici (0 : ℝ) := ht
    rw [indicator_of_mem htmem,Real.norm_of_nonneg (sq_nonneg _),nativeOriginalDampedPrimeField_norm_sq]
    have hsq := pow_le_pow_left₀ (abs_nonneg _) (hBound t ht) 2
    exact (mul_le_mul_of_nonneg_left hsq (Real.exp_nonneg _)).trans_eq (by ring)
  · have htmem : t ∉ Ici (0 : ℝ) := ht
    rw [indicator_of_notMem htmem,nativeOriginalDampedPrimeField_zero_of_neg epsilon (lt_of_not_ge ht)]
    simp

/-- Explicitly conditional original consumer. The complete observation upper
law is an OPEN antecedent; this theorem does not construct or assert it. -/
theorem quiet_balanced_observation_implies_native_cut
    (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop)
    (quiet :
      (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
        Real.log (1+max (nativeRawHigh 1 2 1 (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon) ∨
      (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
        Real.log (1+max (nativeAbsorbedHigh 1 2 1 (by norm_num)
          (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon)) :
    nativeZeroDisplacementSup=0 ∧
    (∀ epsilon : ℝ, 0 < epsilon → MemLp
      (fun t : ℝ => ((Real.exp (-epsilon*t)*primeFieldFamily 0 t : ℝ) : ℂ)) 2 volume) ∧
    NativeOriginalPrimeFieldAllDampedL2 ∧ NativeOriginalPrimeFieldAllDampedIntegral ∧ RiemannHypothesis := by
  have hTheta : nativeZeroDisplacementSup=0 := by
    by_contra hne
    have hp : 0 < nativeZeroDisplacementSup := lt_of_le_of_ne native_zero_sup_bounds.1 (Ne.symm hne)
    have hhalf : 0 < nativeZeroDisplacementSup/2 := by linarith
    have hlt : nativeZeroDisplacementSup/2 < nativeZeroDisplacementSup := by linarith
    have hRates := fixed_two_factor_mask_rate_theta
    rcases quiet with hQuiet | hQuiet
    · have hLo := (tendsto_order.1 (hRates.1.comp cofinal)).1 (nativeZeroDisplacementSup/2) hlt
      obtain ⟨n,hn,hq⟩ := (hLo.and (hQuiet _ hhalf)).exists
      simp only [Function.comp_apply] at hn
      linarith
    · have hLo := (tendsto_order.1 (hRates.2.comp cofinal)).1 (nativeZeroDisplacementSup/2) hlt
      obtain ⟨n,hn,hq⟩ := (hLo.and (hQuiet _ hhalf)).exists
      simp only [Function.comp_apply] at hn
      linarith
  have hL2 := originalPrimeField_allDampedL2_of_native_theta_zero hTheta
  have hIntegral := nativeOriginalPrimeField_allDampedL2_iff_integral.mp hL2
  refine ⟨hTheta,?_,hL2,hIntegral,riemannHypothesis_of_step4_AX hIntegral⟩
  intro epsilon hepsilon
  exact hL2 epsilon hepsilon

#print axioms fixed_two_factor_mask_rate_theta
#print axioms originalPrimeField_allDampedL2_of_native_theta_zero
#print axioms quiet_balanced_observation_implies_native_cut
end Zeta23.OPICAFollowup
