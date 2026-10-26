import Zeta23.OPICARound2.CausalProbe
import Zeta23.OPICARound2.NativeCuts
import Zeta23.OPICARound2.FixedFilter
import Zeta23.OPICARound2.ProbeGram
import Zeta23.CCM.UniversalSincSourceTail
import Zeta23.CCM.NativeDampedCompletionPointwiseBridge
import Zeta23.OPICAFollowup.LogSlackBalance
import Zeta23.OPICAFollowup.MultiplicityTail
import Zeta23.CCM.NativeCompletedInputZetaLaplace
import Mathlib.Analysis.Complex.JensenFormula
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-! Literal locally finite Möbius histories and source-preserving truncation
controls. A local inverse is not assigned global L2 membership. -/

noncomputable section

open Set MeasureTheory Finset Filter Matrix
open scoped Topology BigOperators ComplexConjugate ComplexOrder

namespace Zeta23.OPICARound2

/-- The literal one-copy delayed source, with the raw Möbius coefficients and
the unchanged inverse-square-root integer weights. -/
def mobiusProbeSource : ℝ → ℝ :=
  OPICAFollowup.arithmeticHistoryAction (ArithmeticFunction.moebius : ArithmeticFunction ℝ) jPlus

theorem mobiusProbeSource_history {T t : ℝ} (ht : t ≤ T) :
    mobiusProbeSource t = ∑ n ∈ range (⌊Real.exp T⌋₊ + 1),
      (ArithmeticFunction.moebius n : ℝ) / Real.sqrt (n : ℝ) * jPlus (t - Real.log n) := by
  simpa only [mobiusProbeSource,sub_zero,ArithmeticFunction.intCoe_apply] using OPICAFollowup.arithmeticHistoryAction_history
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (g := 0)
    (fun u hu => jPlus_zero_of_neg hu) ht

theorem mobiusProbeSource_zero_of_neg {t : ℝ} (ht : t < 0) : mobiusProbeSource t = 0 :=
  OPICAFollowup.arithmeticHistoryAction_zero_before
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (fun _u hu => jPlus_zero_of_neg hu) ht

/-- Actual local Dirichlet regrouping gives N M = jPlus; no transform quotient
or summability at infinite physical time is used. -/
theorem mobiusProbeSource_integer_inverse (t : ℝ) :
    CCM.nativeIntegerTranslateAction mobiusProbeSource t = jPlus t := by
  rw [← OPICAFollowup.arithmeticHistoryAction_zeta]
  unfold mobiusProbeSource
  rw [OPICAFollowup.arithmeticHistoryAction_mul
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
    (fun u hu => jPlus_zero_of_neg hu), ArithmeticFunction.coe_zeta_mul_coe_moebius,
    OPICAFollowup.arithmeticHistoryAction_one]

theorem probeIntegerAction_probeV_re (t : ℝ) :
    CCM.nativeIntegerTranslateAction (fun s => (probeV s).re) t = (probeW t).re := by
  rw [CCM.nativeIntegerTranslateAction_eq_causal_history
    (fun s hs => by rw [probeV_zero_of_neg hs]; rfl)]
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero] using (congrArg Complex.re (native_probe_integer_action t)).symm

theorem mobiusProbe_completed_inverse (t : ℝ) :
    OPICAFollowup.arithmeticHistoryAction (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
      (fun s => (probeW s).re) t = (probeV t).re := by
  have hw : (fun s => (probeW s).re) =
      OPICAFollowup.arithmeticHistoryAction (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
        (fun s => (probeV s).re) := by
    funext s
    rw [OPICAFollowup.arithmeticHistoryAction_zeta,probeIntegerAction_probeV_re]
  rw [hw,OPICAFollowup.arithmeticHistoryAction_mul
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
    (fun s hs => by rw [probeV_zero_of_neg hs]; rfl),
    ArithmeticFunction.coe_moebius_mul_coe_zeta,OPICAFollowup.arithmeticHistoryAction_one]

private theorem truncation_causal_product_integrable {g f : ℝ → ℝ}
    (hg : Integrable g) (hg0 : ∀ s : ℝ, s < 0 → g s = 0)
    (hf : Continuous f) (hf0 : ∀ s : ℝ, s < 0 → f s = 0) (t : ℝ) :
    Integrable (fun s : ℝ => g s * f (t - s)) := by
  have hc : Continuous (fun s : ℝ => f (t - s)) := hf.comp (continuous_const.sub continuous_id)
  have hi : IntegrableOn (fun s : ℝ => g s * f (t - s)) (Icc 0 t) :=
    hg.integrableOn.mul_continuousOn hc.continuousOn isCompact_Icc
  apply (hi.integrable_indicator measurableSet_Icc).congr
  filter_upwards with s
  by_cases hs : s ∈ Icc 0 t
  · simp only [indicator_of_mem hs]
  · rw [indicator_of_notMem hs]
    have hcases : s < 0 ∨ t < s := by
      simpa only [Set.mem_Icc,not_and_or,not_le] using hs
    rcases hcases with hneg | hafter
    · rw [hg0 s hneg,zero_mul]
    · rw [hf0 _ (by linarith),mul_zero]

theorem mobiusProbeSource_convolution_history (t : ℝ) :
    (fun s : ℝ => CCM.nativePositiveCompletion s * mobiusProbeSource (t - s)) =
      fun s => ∑ n ∈ range (⌊Real.exp t⌋₊ + 1),
        ((ArithmeticFunction.moebius n : ℝ) / Real.sqrt (n : ℝ)) *
          (CCM.nativePositiveCompletion s * jPlus ((t - Real.log n) - s)) := by
  funext s
  by_cases hs : s < 0
  · simp [CCM.nativePositiveCompletion_eq_zero_of_neg hs]
  · rw [mobiusProbeSource_history (T := t) (by linarith),Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    have harg : (t - s) - Real.log n = (t - Real.log n) - s := by ring
    rw [harg]
    ring

private theorem mobiusProbe_convolution_term_integrable (t : ℝ) (n : ℕ) :
    Integrable (fun s : ℝ => ((ArithmeticFunction.moebius n : ℝ) / Real.sqrt (n : ℝ)) *
      (CCM.nativePositiveCompletion s * jPlus ((t - Real.log n) - s))) :=
  (truncation_causal_product_integrable CCM.nativePositiveCompletion_integrable
    (fun _s hs => CCM.nativePositiveCompletion_eq_zero_of_neg hs) jPlus_contDiff.continuous
    (fun _s hs => jPlus_zero_of_neg hs) (t - Real.log n)).const_mul _

theorem mobiusProbeSource_convolution_integrable (t : ℝ) :
    Integrable (fun s : ℝ => CCM.nativePositiveCompletion s * mobiusProbeSource (t - s)) := by
  rw [mobiusProbeSource_convolution_history]
  exact integrable_finsetSum _ (fun n hn => mobiusProbe_convolution_term_integrable t n)

/-- The actual literal floor kernel inverts the local Möbius source to the
new target v. The integral is proved integrable at every physical time. -/
theorem mobiusProbeSource_floor_inverse (t : ℝ) :
    ((∫ s : ℝ, CCM.nativePositiveCompletion s * mobiusProbeSource (t - s) : ℝ) : ℂ) = probeV t := by
  have hwreal (r : ℝ) : (probeW r).re =
      ∫ s : ℝ, CCM.nativePositiveCompletion s * jPlus (r - s) := by
    rw [probeW_eq_real_integral]
    rfl
  have hreal : (∫ s : ℝ, CCM.nativePositiveCompletion s * mobiusProbeSource (t - s)) = (probeV t).re := by
    rw [mobiusProbeSource_convolution_history,integral_finsetSum _ (fun n hn => mobiusProbe_convolution_term_integrable t n)]
    simp_rw [integral_const_mul,← hwreal]
    have hhistory := OPICAFollowup.arithmeticHistoryAction_history
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) (g := 0)
      (f := fun s => (probeW s).re) (T := t) (t := t)
      (fun s hs => by rw [probeW_zero_of_neg hs]; rfl) le_rfl
    simp only [sub_zero,ArithmeticFunction.intCoe_apply] at hhistory
    rw [← hhistory,mobiusProbe_completed_inverse]
  rw [hreal,probeV_eq_real_integral]
  rfl

theorem native_mobius_probe_inverse :
    (∀ T t : ℝ, t ≤ T → mobiusProbeSource t = ∑ n ∈ range (⌊Real.exp T⌋₊ + 1),
      (ArithmeticFunction.moebius n : ℝ) / Real.sqrt (n : ℝ) * jPlus (t - Real.log n)) ∧
    (∀ t : ℝ, CCM.nativeIntegerTranslateAction mobiusProbeSource t = jPlus t) ∧
    (∀ t : ℝ, Integrable (fun s : ℝ => CCM.nativePositiveCompletion s * mobiusProbeSource (t - s))) ∧
    (∀ t : ℝ, ((∫ s : ℝ, CCM.nativePositiveCompletion s * mobiusProbeSource (t - s) : ℝ) : ℂ) = probeV t) :=
  ⟨fun _ _ h => mobiusProbeSource_history h,mobiusProbeSource_integer_inverse,
    mobiusProbeSource_convolution_integrable,mobiusProbeSource_floor_inverse⟩

/-- A causal arithmetic history is already its literal prefix strictly before
the first omitted delay. The endpoint is excluded rather than rounded down. -/
theorem arithmetic_history_before_next (a : ArithmeticFunction ℝ) {f : ℝ → ℝ}
    (hf : ∀ s : ℝ, s < 0 → f s = 0) (N : ℕ) {t : ℝ}
    (ht : t < Real.log (N + 1 : ℕ)) :
    OPICAFollowup.arithmeticHistoryAction a f t =
      ∑ n ∈ range (N + 1), a n / Real.sqrt (n : ℝ) * f (t - Real.log n) := by
  have hpos : 0 < ((N + 1 : ℕ) : ℝ) := by positivity
  rw [OPICAFollowup.arithmeticHistoryAction_history a hf ht.le]
  rw [sub_zero,Real.exp_log hpos,Nat.floor_natCast,Finset.sum_range_succ]
  rw [hf _ (by linarith),mul_zero,add_zero]

/-- The raw finite Möbius input. Its finite L2 membership is supplied by the
actual dictionary; no infinite Möbius sum is assigned an L2 value. -/
def mobiusProbePartialInput (N : ℕ) : CausalProbeL2 :=
  ∑ n ∈ range (N + 1), (ArithmeticFunction.moebius n : ℂ) • probeInput n

def mobiusProbePartialOutput (N : ℕ) : CausalProbeL2 :=
  probeOperator (mobiusProbePartialInput N)

def mobiusProbePartialResidual (N : ℕ) : CausalProbeL2 :=
  probeTarget - mobiusProbePartialOutput N

theorem mobiusProbePartialOutput_sum (N : ℕ) :
    mobiusProbePartialOutput N =
      ∑ n ∈ range (N + 1), (ArithmeticFunction.moebius n : ℂ) • probeColumn n := by
  simp [mobiusProbePartialOutput,mobiusProbePartialInput,probeColumn]

theorem probeColumn_coeFn_all (n : ℕ) :
    (probeColumn n : ProbeL2) =ᵐ[volume] fun t : ℝ =>
      (CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n) := by
  by_cases hn : n = 0
  · subst n
    filter_upwards [Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with t ht
    simp [probeColumn_zero,CCM.nativeIntegerCoefficient] at ht ⊢
  · exact probeColumn_coeFn hn

theorem mobiusProbePartialOutput_coeFn (N : ℕ) :
    (mobiusProbePartialOutput N : ProbeL2) =ᵐ[volume] fun t : ℝ =>
      ∑ n ∈ range (N + 1),
        ((ArithmeticFunction.moebius n : ℝ) / Real.sqrt (n : ℝ) : ℂ) *
          probeW (t - Real.log n) := by
  rw [mobiusProbePartialOutput_sum]
  simp only [Submodule.coe_sum,Submodule.coe_smul]
  have hterms : ∀ n : ℕ,
      ((ArithmeticFunction.moebius n : ℂ) • (probeColumn n : ProbeL2)) =ᵐ[volume]
        fun t : ℝ => ((ArithmeticFunction.moebius n : ℝ) / Real.sqrt (n : ℝ) : ℂ) *
          probeW (t - Real.log n) := by
    intro n
    filter_upwards [Lp.coeFn_smul (ArithmeticFunction.moebius n : ℂ) (probeColumn n : ProbeL2),
      probeColumn_coeFn_all n] with t ht hc
    rw [ht,Pi.smul_apply,hc]
    simp only [smul_eq_mul,CCM.nativeIntegerCoefficient,Complex.ofReal_div,
      Complex.ofReal_one,Complex.ofReal_intCast]
    ring
  filter_upwards [Lp.coeFn_fun_finsetSum (range (N + 1))
      (fun n => (ArithmeticFunction.moebius n : ℂ) • (probeColumn n : ProbeL2)),
    ae_all_iff.mpr hterms] with t ht hterm
  rw [ht]
  exact sum_congr rfl (fun n _hn => hterm n)

theorem mobiusProbePartialOutput_before_next (N : ℕ) {t : ℝ}
    (ht : t < Real.log (N + 1 : ℕ)) :
    ∑ n ∈ range (N + 1),
        ((ArithmeticFunction.moebius n : ℝ) / Real.sqrt (n : ℝ) : ℂ) *
          probeW (t - Real.log n) = probeV t := by
  have hh := arithmetic_history_before_next
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
    (fun s hs => show (probeW s).re = 0 by rw [probeW_zero_of_neg hs]; rfl) N ht
  rw [mobiusProbe_completed_inverse] at hh
  have hreal := congrArg (fun r : ℝ => (r : ℂ)) hh.symm
  simp only [Complex.ofReal_sum,Complex.ofReal_mul,ArithmeticFunction.intCoe_apply] at hreal
  convert hreal using 1
  · apply sum_congr rfl
    intro n _hn
    rw [probeW_eq_real_integral]
    simp only [Complex.ofReal_re,Complex.ofReal_div]
  · rw [probeV_eq_real_integral]
    rfl

/-- The actual finite raw Möbius residual vanishes on the entire past of the
first omitted delay. This includes the full negative half-line. -/
theorem mobiusProbePartialResidual_delayed (N : ℕ) :
    ∀ᵐ t : ℝ, t < Real.log (N + 1 : ℕ) →
      (mobiusProbePartialResidual N : ProbeL2) t = 0 := by
  have hs : (mobiusProbePartialResidual N : ProbeL2) =
      (probeTarget : ProbeL2) - (mobiusProbePartialOutput N : ProbeL2) := rfl
  rw [hs]
  filter_upwards [Lp.coeFn_sub (probeTarget : ProbeL2) (mobiusProbePartialOutput N : ProbeL2),
    probeTarget_coeFn,mobiusProbePartialOutput_coeFn N] with t ht hv ho
  intro hbefore
  rw [ht,Pi.sub_apply,hv,ho,mobiusProbePartialOutput_before_next N hbefore,sub_self]

/-- Shifting a genuinely delayed residual back to zero exposes the exact
exponential gain in the bounded Laplace evaluation functional. -/
theorem probe_delayed_laplace_bound (z : ℂ) (hz : 0 < z.re)
    (r : CausalProbeL2) (h : ℝ)
    (hr : ∀ᵐ t : ℝ, t < h → (r : ProbeL2) t = 0) :
    Real.sqrt (2 * z.re) * Real.exp (z.re * h) *
      ‖CCM.nativeCausalLaplaceMoment z 0 (r : ProbeL2)‖ ≤ ‖r‖ := by
  let g : CausalProbeL2 := ⟨CCM.nativeCompletionL2Delay (-h) (r : ProbeL2), by
    have hshift := (measurePreserving_sub_right volume (-h)).quasiMeasurePreserving.ae hr
    filter_upwards [CCM.nativeCompletionL2Delay_coeFn (-h) (r : ProbeL2),hshift]
      with t ht hrt
    intro ht0
    rw [ht]
    exact hrt (by linarith)⟩
  have hb := probe_laplace_evaluation_bound z hz g
  have hmoment : CCM.nativeCausalLaplaceMoment z 0 (g : ProbeL2) =
      Complex.exp (z * (h : ℂ)) * CCM.nativeCausalLaplaceMoment z 0 (r : ProbeL2) := by
    change CCM.nativeCausalLaplaceMoment z 0
      (CCM.nativeCompletionL2Delay (-h) (r : ProbeL2)) = _
    rw [CCM.nativeCausalLaplaceMoment_delay z hz 0 r (-h)]
    simp only [Nat.zero_add,Finset.sum_range_one,Nat.choose_zero_right,Nat.sub_self,pow_zero,
      Nat.cast_one,one_mul,mul_one,Complex.ofReal_neg,neg_mul_neg]
  have hnorm : ‖g‖ = ‖r‖ := CCM.nativeCompletionL2Delay_norm (-h) (r : ProbeL2)
  rw [hmoment,norm_mul,Complex.norm_exp,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,sub_zero,hnorm] at hb
  simpa only [mul_assoc] using hb

theorem mobiusProbePartialResidual_laplace (N : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    CCM.nativeCausalLaplaceMoment ((rho : ℂ) - 1 / 2) 0
        (mobiusProbePartialResidual N : ProbeL2) =
      CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        JPlus ((rho : ℂ) - 1 / 2) := by
  have hp : 0 < ((rho : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re]; norm_num; linarith
  rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment _ hp 0]
  change inner ℂ (CCM.nativeCausalExponentialWitness _ hp 0)
    (probeTarget - probeOperator (mobiusProbePartialInput N)) = _
  rw [inner_sub_right,CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
    CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment,
    probe_laplace_annihilates_range rho hright (mobiusProbePartialInput N),sub_zero,
    probeTarget_laplace_eq_physical,probeV_laplace hp.le]

/-- P15: the actual raw Möbius truncation has an exponentially strengthened
right-zero barrier, with the exact first-omitted-delay factor. -/
theorem native_mobius_delayed_barrier (N : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    (∀ᵐ t : ℝ, t < Real.log (N + 1 : ℕ) →
      (mobiusProbePartialResidual N : ProbeL2) t = 0) ∧
    Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re) *
      Real.exp (((rho : ℂ) - 1 / 2).re * Real.log (N + 1 : ℕ)) *
      ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        JPlus ((rho : ℂ) - 1 / 2)‖ ≤ ‖mobiusProbePartialResidual N‖ := by
  have hp : 0 < ((rho : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re]; norm_num; linarith
  refine ⟨mobiusProbePartialResidual_delayed N,?_⟩
  have hb := probe_delayed_laplace_bound ((rho : ℂ) - 1 / 2) hp
    (mobiusProbePartialResidual N) (Real.log (N + 1 : ℕ)) (mobiusProbePartialResidual_delayed N)
  rwa [mobiusProbePartialResidual_laplace N rho hright] at hb

/-- The actual delayed source is entire. This uses its literal original-source
formula, rather than assuming continuation of a numerical transform. -/
theorem JPlus_analyticAt (z : ℂ) : AnalyticAt ℂ JPlus z := by
  have heq : JPlus = fun w : ℂ =>
      Complex.exp (-w * (probeSigma : ℂ)) * CCM.nativeOriginalSourceLaplace w := by
    funext w
    exact JPlus_eq_delay w
  rw [heq]
  exact ((analyticAt_id.neg.mul analyticAt_const).cexp).mul
    (CCM.nativeOriginalSourceLaplace_analyticAt z)

def probeSourceL1Mass : ℝ := ∫ t : ℝ, |jPlus t|

theorem probeSourceL1Mass_nonneg : 0 ≤ probeSourceL1Mass :=
  integral_nonneg (fun _ => abs_nonneg _)

theorem probeSourceL1Mass_pos : 0 < probeSourceL1Mass := by
  have h := norm_integral_le_integral_norm jPlus (μ := (volume : Measure ℝ))
  rw [jPlus_integral] at h
  have heq : (∫ t : ℝ, ‖jPlus t‖) = probeSourceL1Mass := rfl
  rw [heq] at h
  norm_num at h
  linarith

theorem jPlusDamping_integrable_all (z : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (jPlus t : ℂ)) := by
  have hc : Continuous (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (jPlus t : ℂ)) := by
    have he : Continuous (fun t : ℝ => Complex.exp (-z * (t : ℂ))) := by fun_prop
    exact he.mul (Complex.continuous_ofReal.comp jPlus_contDiff.continuous)
  exact hc.integrable_of_hasCompactSupport jPlus_complex_hasCompactSupport.mul_left

/-- Compact support controls the exponential type of the unchanged source.
The constant is its actual L1 mass, with no unproved numerical enclosure. -/
theorem JPlus_exponential_bound (z : ℂ) :
    ‖JPlus z‖ ≤ probeSourceL1Mass * Real.exp (2 * probeSigma * ‖z‖) := by
  have hp (t : ℝ) :
      ‖Complex.exp (-z * (t : ℂ)) * (jPlus t : ℂ)‖ ≤
        Real.exp (2 * probeSigma * ‖z‖) * |jPlus t| := by
    by_cases ht : t ∈ Icc 0 (2 * probeSigma)
    · have htN : ‖(t : ℂ)‖ ≤ 2 * probeSigma := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht.1]
        exact ht.2
      have hre : (-z * (t : ℂ)).re ≤ 2 * probeSigma * ‖z‖ := by
        calc
          _ ≤ ‖-z * (t : ℂ)‖ := Complex.re_le_norm _
          _ = ‖z‖ * ‖(t : ℂ)‖ := by rw [norm_mul,norm_neg]
          _ ≤ ‖z‖ * (2 * probeSigma) := mul_le_mul_of_nonneg_left htN (norm_nonneg _)
          _ = _ := by ring
      rw [norm_mul,Complex.norm_exp,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hre) (abs_nonneg _)
    · simp [jPlus_zero_outside ht]
  calc
    ‖JPlus z‖ ≤ ∫ t : ℝ, ‖Complex.exp (-z * (t : ℂ)) * (jPlus t : ℂ)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, Real.exp (2 * probeSigma * ‖z‖) * |jPlus t| :=
      integral_mono (jPlusDamping_integrable_all z).norm
        (jPlus_integrable.abs.const_mul _) hp
    _ = _ := by rw [integral_const_mul]; exact mul_comm _ _

/-- Multiplicities are retained by the analytic divisor; this is not a count
of distinct sinc factors or a sampled count of source zeros. -/
def probeSourceZeroCount (R : ℝ) : ℤ :=
  ∑ᶠ z : ℂ, MeromorphicOn.divisor JPlus (Metric.closedBall (0 : ℂ) R) z

theorem probe_source_zero_count_bound {R : ℝ} (hR : 0 < R) :
    (probeSourceZeroCount R : ℝ) ≤
      (Real.log (16 * max 1 probeSourceL1Mass) + 4 * probeSigma * R) / Real.log 2 := by
  let M : ℝ := max 1 probeSourceL1Mass * Real.exp (4 * probeSigma * R)
  have hmass : 0 < max 1 probeSourceL1Mass := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hexp : 1 ≤ Real.exp (4 * probeSigma * R) :=
    Real.one_le_exp (mul_nonneg (mul_nonneg (by norm_num) probeSigma_pos.le) hR.le)
  have hM : 1 ≤ M := by
    dsimp [M]
    calc
      1 = 1 * 1 := by ring
      _ ≤ max 1 probeSourceL1Mass * Real.exp (4 * probeSigma * R) :=
        mul_le_mul (le_max_left _ _) hexp (by norm_num) hmass.le
  have hJ : AnalyticOnNhd ℂ JPlus (Metric.closedBall (0 : ℂ) |2 * R|) :=
    fun z _hz => JPlus_analyticAt z
  have hJ0 : JPlus 0 ≠ 0 := by rw [JPlus_zero]; norm_num
  have hbound : ∀ z ∈ Metric.sphere (0 : ℂ) |2 * R|, ‖JPlus z‖ ≤ M := by
    intro z hz
    have hn : ‖z‖ = 2 * R := by
      simpa only [Metric.mem_sphere,dist_zero_right,abs_of_pos (by positivity : 0 < 2 * R)] using hz
    calc
      _ ≤ probeSourceL1Mass * Real.exp (2 * probeSigma * ‖z‖) := JPlus_exponential_bound z
      _ ≤ max 1 probeSourceL1Mass * Real.exp (2 * probeSigma * ‖z‖) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le
      _ = M := by rw [hn]; congr 2; ring
  have h := hJ.sum_divisor_le (r := R) (R := 2 * R) (M := M)
    (by simpa only [abs_of_pos hR] using hR)
    (by rw [abs_of_pos hR,abs_of_pos (by positivity : 0 < 2 * R)]; linarith)
    hM hJ0 hbound
  rw [abs_of_pos hR] at h
  change (probeSourceZeroCount R : ℝ) ≤ _ at h
  convert h using 1
  rw [JPlus_zero]
  norm_num
  have hdiv : 2 * R / R = 2 := by field_simp
  rw [hdiv]
  congr 1
  have heq : M / (1 / 16) = (16 * max 1 probeSourceL1Mass) *
      Real.exp (4 * probeSigma * R) := by dsimp [M]; ring
  rw [heq,Real.log_mul (by positivity) (Real.exp_ne_zero _),Real.log_exp]

/-- Physical-time truncation of the actual floor kernel. This is independent
of truncating the integer delay history. -/
def probeFloorKernelCutoff (T : ℝ) : ℝ → ℝ :=
  (Iic T).indicator CCM.nativePositiveCompletion

def probeFloorKernelTail (T : ℝ) : ℝ → ℝ :=
  (Ioi T).indicator CCM.nativePositiveCompletion

theorem probeFloorKernelCutoff_integrable (T : ℝ) : Integrable (probeFloorKernelCutoff T) :=
  CCM.nativePositiveCompletion_integrable.indicator measurableSet_Iic

theorem probeFloorKernelTail_integrable (T : ℝ) : Integrable (probeFloorKernelTail T) :=
  CCM.nativePositiveCompletion_integrable.indicator measurableSet_Ioi

theorem probeFloorKernelTail_mass_bound (T : ℝ) :
    (∫ t : ℝ, ‖probeFloorKernelTail T t‖) ≤ 2 * Real.exp (-T / 2) := by
  have heq : (fun t : ℝ => ‖probeFloorKernelTail T t‖) =
      (Ioi T).indicator (fun t => ‖CCM.nativePositiveCompletion t‖) := by
    funext t
    by_cases ht : t ∈ Ioi T <;> simp [probeFloorKernelTail,ht]
  rw [heq,integral_indicator measurableSet_Ioi]
  calc
    _ ≤ ∫ t : ℝ in Ioi T, Real.exp ((-1 / 2 : ℝ) * t) := by
      apply integral_mono_ae CCM.nativePositiveCompletion_integrable.norm.integrableOn
        (integrableOn_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) T)
      filter_upwards with t
      rw [Real.norm_of_nonneg (CCM.nativePositiveCompletion_nonneg t)]
      convert CCM.nativePositiveCompletion_le_exp t using 1
      congr 1
      ring
    _ = _ := by
      rw [integral_exp_mul_Ioi (by norm_num : (-1 / 2 : ℝ) < 0) T]
      have harg : (-1 / 2 : ℝ) * T = -T / 2 := by ring
      rw [harg]
      ring

theorem nativeFloorL2Operator_eq_kernel (f : ProbeL2) :
    CCM.nativeDampedCompletionL2Operator 0 (le_rfl) f =
      kernelL2Operator CCM.nativePositiveCompletion CCM.nativePositiveCompletion_integrable f := by
  rw [CCM.nativeDampedCompletionL2Operator_apply,kernelL2Operator_apply]
  apply integral_congr_ae
  filter_upwards with t
  simp [CCM.nativeDampedCompletionKernel]

theorem probeFloorKernelCutoff_error_eq (T : ℝ) (f : ProbeL2) :
    CCM.nativeDampedCompletionL2Operator 0 (le_rfl) f -
        kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T) f =
      kernelL2Operator (probeFloorKernelTail T) (probeFloorKernelTail_integrable T) f := by
  rw [nativeFloorL2Operator_eq_kernel,kernelL2Operator_apply,kernelL2Operator_apply,
    kernelL2Operator_apply]
  change (∫ t : ℝ, kernelL2Integrand CCM.nativePositiveCompletion f t) -
      (∫ t : ℝ, kernelL2Integrand (probeFloorKernelCutoff T) f t) =
    ∫ t : ℝ, kernelL2Integrand (probeFloorKernelTail T) f t
  rw [← integral_sub
      (kernelL2Integrand_integrable _ CCM.nativePositiveCompletion_integrable f)
      (kernelL2Integrand_integrable _ (probeFloorKernelCutoff_integrable T) f)]
  apply integral_congr_ae
  filter_upwards with t
  change CCM.nativePositiveCompletion t • CCM.nativeCompletionL2Delay t f -
    probeFloorKernelCutoff T t • CCM.nativeCompletionL2Delay t f =
    probeFloorKernelTail T t • CCM.nativeCompletionL2Delay t f
  by_cases ht : t ≤ T
  · simp [probeFloorKernelCutoff,probeFloorKernelTail,ht,not_lt_of_ge ht]
  · simp [probeFloorKernelCutoff,probeFloorKernelTail,ht,lt_of_not_ge ht]

/-- P14's safe cutoff applies to every full-line L2 source, hence in particular
to the unchanged compact jPlus. The arithmetic history cutoff is not used. -/
theorem native_floor_physical_cutoff_bound (T : ℝ) (f : ProbeL2) :
    ‖CCM.nativeDampedCompletionL2Operator 0 (le_rfl) f -
        kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T) f‖ ≤
      2 * Real.exp (-T / 2) * ‖f‖ := by
  rw [probeFloorKernelCutoff_error_eq]
  exact (kernelL2Value_norm_le _ (probeFloorKernelTail_integrable T) f).trans
    (mul_le_mul_of_nonneg_right (probeFloorKernelTail_mass_bound T) (norm_nonneg _))

theorem native_probe_source_physical_cutoff_bound (T : ℝ) :
    ‖(probeCompletedSource : ProbeL2) -
        kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T)
          (probeSource : ProbeL2)‖ ≤
      2 * Real.exp (-T / 2) * ‖probeSource‖ :=
  native_floor_physical_cutoff_bound T (probeSource : ProbeL2)

/-- The square-root evaluation bound rules out first-order pole growth,
including for bounded-input limits that have no actual inverse input. -/
theorem probe_boundary_first_order_limit_of_bound (F : ℝ → ℂ) (M : ℝ)
    (hbound : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), Real.sqrt (2 * e) * ‖F e‖ ≤ M) :
    Tendsto (fun e : ℝ => (e : ℂ) * F e) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hb : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ),
      ‖(e : ℂ) * F e‖ ≤ Real.sqrt e * M / Real.sqrt 2 := by
    filter_upwards [self_mem_nhdsWithin,hbound] with e he h
    have hepos : 0 < e := he
    have hspos : 0 < Real.sqrt e := Real.sqrt_pos.mpr hepos
    have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at h
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hepos]
    apply (le_div_iff₀ hs2pos).mpr
    have hmul := mul_le_mul_of_nonneg_left h hspos.le
    have hsq := Real.sq_sqrt hepos.le
    convert hmul using 1
    nth_rw 1 [← hsq]
    ring
  apply squeeze_zero_norm' hb
  have he : Tendsto (fun e : ℝ => e) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  simpa using (Real.continuous_sqrt.continuousAt.tendsto.comp he).mul_const M |>.div_const (Real.sqrt 2)

/-- A causal L2 Laplace transform cannot have the first-order boundary
blowup of a pole. The actual normalization is paid before taking the limit. -/
theorem probe_boundary_laplace_first_order_limit (lambda : ℂ) (hlambda : lambda.re = 0)
    (f : CausalProbeL2) :
    Tendsto (fun e : ℝ => (e : ℂ) *
      CCM.nativeCausalLaplaceMoment (lambda + (e : ℂ)) 0 (f : ProbeL2))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply probe_boundary_first_order_limit_of_bound _ ‖f‖
  filter_upwards [self_mem_nhdsWithin] with e he
  have hepos : 0 < e := he
  have hz : 0 < (lambda + (e : ℂ)).re := by simpa [hlambda] using hepos
  simpa only [Complex.add_re,Complex.ofReal_re,hlambda,zero_add] using
    probe_laplace_evaluation_bound (lambda + (e : ℂ)) hz f

theorem probe_boundary_ray_tendsto (lambda : ℂ) :
    Tendsto (fun e : ℝ => lambda + (e : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝[≠] lambda) := by
  apply tendsto_nhdsWithin_iff.mpr
  refine ⟨?_,?_⟩
  · have he : Tendsto (fun e : ℝ => (e : ℂ)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.add he
  · filter_upwards [self_mem_nhdsWithin] with e he
    have hepos : 0 < e := he
    simp only [mem_compl_iff,mem_singleton_iff]
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re,Complex.ofReal_re] at hre
    linarith

/-- A meromorphic function whose first-order pole profile tends to zero
along a genuine punctured ray has nonnegative order. -/
theorem probe_boundary_meromorphic_order_nonneg_of_limit (lambda : ℂ)
    (F : ℂ → ℂ) (hF : MeromorphicAt F lambda)
    (hlimit : Tendsto (fun e : ℝ => (e : ℂ) * F (lambda + (e : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    0 ≤ meromorphicOrderAt F lambda := by
  let G : ℂ → ℂ := fun z => (z - lambda) * F z
  have hG : MeromorphicAt G lambda :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt.mul hF
  have hpath := probe_boundary_ray_tendsto lambda
  have hzero : Tendsto (fun e : ℝ => G (lambda + (e : ℂ)))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [G,add_sub_cancel_left] using hlimit
  by_contra hneg
  have ho : meromorphicOrderAt F lambda < 0 := lt_of_not_ge hneg
  obtain ⟨n,hn⟩ := WithTop.ne_top_iff_exists.mp ho.ne_top
  have hnneg : n < 0 := by simpa only [← hn,WithTop.coe_lt_zero] using ho
  have horder : meromorphicOrderAt G lambda = ((n + 1 : ℤ) : WithTop ℤ) := by
    have hid : MeromorphicAt (fun z : ℂ => z - lambda) lambda := by fun_prop
    rw [show G = (fun z : ℂ => z - lambda) * F from rfl,
      meromorphicOrderAt_mul hid hF,
      meromorphicOrderAt_id_sub_const,← hn]
    simp only [← WithTop.coe_one,← WithTop.coe_add,add_comm]
  by_cases hn1 : n + 1 = 0
  · have hoG : meromorphicOrderAt G lambda = 0 := by rw [horder,hn1]; rfl
    obtain ⟨c,hc,hlim⟩ := tendsto_ne_zero_of_meromorphicOrderAt_eq_zero hG hoG
    exact hc (tendsto_nhds_unique (hlim.comp hpath) hzero)
  · have hoG : meromorphicOrderAt G lambda < 0 := by
      rw [horder,WithTop.coe_lt_zero]
      omega
    have hlim := (tendsto_norm_cobounded_atTop.comp
      (tendsto_cobounded_of_meromorphicOrderAt_neg hoG)).comp hpath
    exact not_tendsto_atTop_of_tendsto_nhds hzero.norm hlim

/-- The meromorphic continuation of an actual causal L2 Laplace transform
has no negative integral boundary order. Equality is required on an actual
right ray, so no unproved Hardy boundary principle is assumed. -/
theorem probe_boundary_meromorphic_order_nonneg (lambda : ℂ) (hlambda : lambda.re = 0)
    (f : CausalProbeL2) (F : ℂ → ℂ) (hF : MeromorphicAt F lambda)
    (hmatch : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), F (lambda + (e : ℂ)) =
      CCM.nativeCausalLaplaceMoment (lambda + (e : ℂ)) 0 (f : ProbeL2)) :
    0 ≤ meromorphicOrderAt F lambda := by
  apply probe_boundary_meromorphic_order_nonneg_of_limit lambda F hF
  apply (probe_boundary_laplace_first_order_limit lambda hlambda f).congr'
  filter_upwards [hmatch] with e he
  rw [he]

theorem JPlus_analyticOrderAt_ne_top (z : ℂ) : analyticOrderAt JPlus z ≠ ⊤ := by
  have h0 : analyticOrderAt JPlus 0 ≠ ⊤ := by
    rw [(JPlus_analyticAt 0).analyticOrderAt_eq_zero.mpr]
    · exact ENat.zero_ne_top
    · rw [JPlus_zero]; norm_num
  exact AnalyticOnNhd.analyticOrderAt_ne_top_of_isPreconnected
    (fun w _hw => JPlus_analyticAt w) isPreconnected_univ (mem_univ 0) (mem_univ z) h0

/-- Actual causal operator evaluation, with both the exceptional half point
and the regular half-plane hypotheses exposed. -/
theorem probeOperator_laplace (z : ℂ) (hz : 0 < z.re) (hne : z ≠ 1 / 2)
    (f : CausalProbeL2) :
    CCM.nativeCausalLaplaceMoment z 0 (probeOperator f : ProbeL2) =
      CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) *
        (CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2)) := by
  rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment z hz 0]
  change inner ℂ (CCM.nativeCausalExponentialWitness z hz 0)
    (CCM.nativeDampedCompletionCausalL2Operator 0 (le_rfl) f) = _
  rw [CCM.nativeCausalExponentialWitness_inner_operator]
  simp only [Nat.zero_add,Finset.sum_range_one,Nat.choose_zero_right,Nat.sub_self,
    Nat.cast_one,one_mul]
  congr 1
  change (∫ t : ℝ, (CCM.nativeDampedCompletionKernel 0 t : ℂ) *
    (t : ℂ) ^ 0 * Complex.exp (-z * (t : ℂ))) = _
  have heq : (fun t : ℝ => (CCM.nativeDampedCompletionKernel 0 t : ℂ) *
      (t : ℂ) ^ 0 * Complex.exp (-z * (t : ℂ))) =
      fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (CCM.nativePositiveCompletion t : ℂ) := by
    funext t
    simp [CCM.nativeDampedCompletionKernel,mul_comm]
  rw [heq,CCM.nativePositiveCompletion_complexLaplace hz hne]

def probeSourceQuotient (z : ℂ) : ℂ := JPlus z / riemannZeta (z + 1 / 2)

theorem probe_shifted_zeta_analyticAt (rho : zetaZeroConfig.carrier) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (z + 1 / 2)) ((rho : ℂ) - 1 / 2) := by
  have h : AnalyticAt ℂ riemannZeta ((rho : ℂ) - 1 / 2 + 1 / 2) := by
    simpa only [sub_add_cancel] using
      riemannZeta_analyticOnNhd_compl_one (rho : ℂ) rho.property.not_trivial.2
  exact h.comp
    (f := fun z : ℂ => z + 1 / 2) (by fun_prop : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) ((rho : ℂ) - 1 / 2))

theorem probe_shifted_zeta_order (rho : zetaZeroConfig.carrier) :
    analyticOrderAt (fun z : ℂ => riemannZeta (z + 1 / 2)) ((rho : ℂ) - 1 / 2) =
      (zeroMult (rho : ℂ) : ℕ∞) := by
  have hs : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) ((rho : ℂ) - 1 / 2) := by fun_prop
  have hd : deriv (fun z : ℂ => z + 1 / 2) ((rho : ℂ) - 1 / 2) ≠ 0 := by
    simp only [deriv_add_const,deriv_id'']; exact one_ne_zero
  simpa only [Function.comp_def,sub_add_cancel] using
    (analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) hs hd).trans
      (by simpa only [sub_add_cancel] using ExceptionalZero.nativeZeroMultiplicity_order rho)

/-- Exact range membership forces every critical zeta zero to be cancelled
by the actual compact source to at least the full zeta multiplicity. This is
a boundary-order conclusion, not an assumed visible critical zero. -/
theorem native_probe_range_boundary_order (f : CausalProbeL2)
    (hf : probeOperator f = probeTarget) (rho : zetaZeroConfig.carrier)
    (hcritical : (rho : ℂ).re = 1 / 2) :
    (zetaZeroConfig.mult (rho : ℂ) : ℤ) ≤
      (meromorphicOrderAt JPlus ((rho : ℂ) - 1 / 2)).untop₀ := by
  let lambda : ℂ := (rho : ℂ) - 1 / 2
  have hlambda : lambda.re = 0 := by dsimp [lambda]; simp [hcritical]
  have hZ := probe_shifted_zeta_analyticAt rho
  have hZo := probe_shifted_zeta_order rho
  have hZn : meromorphicOrderAt (fun z : ℂ => riemannZeta (z + 1 / 2)) lambda ≠ ⊤ := by
    rw [hZ.meromorphicOrderAt_eq,hZo,ENat.map_natCast]
    exact WithTop.coe_ne_top
  have hZnz := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hZ.meromorphicAt).mp hZn
  have hR := ExceptionalZero.nativeCompletionRationalMultiplier_at_zero_analyticAt rho
  have hRnz : ∀ᶠ z in 𝓝 lambda, CCM.nativeCompletionRationalMultiplier z ≠ 0 :=
    hR.continuousAt.eventually_ne (probe_rational_multiplier_ne_zero rho)
  have hlne : lambda ≠ 1 / 2 := by
    intro h
    have hr := congrArg Complex.re h
    rw [hlambda] at hr
    norm_num at hr
  have hhalf : ∀ᶠ z in 𝓝 lambda, z ≠ (1 / 2 : ℂ) := eventually_ne_nhds hlne
  have hmatch : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ), probeSourceQuotient (lambda + (e : ℂ)) =
      CCM.nativeCausalLaplaceMoment (lambda + (e : ℂ)) 0 (f : ProbeL2) := by
    have hp := probe_boundary_ray_tendsto lambda
    filter_upwards [hp.eventually hZnz,
      hp.eventually (hRnz.filter_mono nhdsWithin_le_nhds),
      hp.eventually (hhalf.filter_mono nhdsWithin_le_nhds),self_mem_nhdsWithin]
      with e hze hre hhe he
    have hepos : 0 < e := he
    have hz : 0 < (lambda + (e : ℂ)).re := by simpa [hlambda] using hepos
    have hL := congrArg (fun g : CausalProbeL2 =>
      CCM.nativeCausalLaplaceMoment (lambda + (e : ℂ)) 0 (g : ProbeL2)) hf
    rw [probeOperator_laplace _ hz hhe f,probeTarget_laplace_eq_physical,
      probeV_laplace hz.le] at hL
    dsimp [probeSourceQuotient]
    apply (div_eq_iff hze).mpr
    exact mul_left_cancel₀ hre (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hL.symm)
  have hF : MeromorphicAt probeSourceQuotient lambda :=
    (JPlus_analyticAt lambda).meromorphicAt.div hZ.meromorphicAt
  have ho := probe_boundary_meromorphic_order_nonneg lambda hlambda f probeSourceQuotient hF hmatch
  have hJn := JPlus_analyticOrderAt_ne_top lambda
  have hJord : analyticOrderAt JPlus lambda = (analyticOrderNatAt JPlus lambda : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt hJn).symm
  have hJo : meromorphicOrderAt JPlus lambda = ((analyticOrderNatAt JPlus lambda : ℤ) : WithTop ℤ) := by
    rw [(JPlus_analyticAt lambda).meromorphicOrderAt_eq,hJord,ENat.map_natCast]
  have hFo : meromorphicOrderAt probeSourceQuotient lambda =
      ((analyticOrderNatAt JPlus lambda : ℤ) - (zeroMult (rho : ℂ) : ℤ) : WithTop ℤ) := by
    rw [show probeSourceQuotient = JPlus / (fun z : ℂ => riemannZeta (z + 1 / 2)) from rfl,
      meromorphicOrderAt_div (JPlus_analyticAt lambda).meromorphicAt hZ.meromorphicAt,
      hJo,hZ.meromorphicOrderAt_eq,hZo,ENat.map_natCast]
  rw [hFo] at ho
  have hi : (zeroMult (rho : ℂ) : ℤ) ≤ (analyticOrderNatAt JPlus lambda : ℤ) := by
    have hsub : (0 : ℤ) ≤ (analyticOrderNatAt JPlus lambda : ℤ) - (zeroMult (rho : ℂ) : ℤ) := by
      exact_mod_cast ho
    omega
  change (zeroMult (rho : ℂ) : ℤ) ≤ (meromorphicOrderAt JPlus lambda).untop₀
  simpa only [hJo,WithTop.untop₀_coe] using hi

theorem native_mobius_delayed_barrier_rpow (N : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re) *
      ((N + 1 : ℕ) : ℝ) ^ (((rho : ℂ) - 1 / 2).re) *
      ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        JPlus ((rho : ℂ) - 1 / 2)‖ ≤ ‖mobiusProbePartialResidual N‖ := by
  have h := (native_mobius_delayed_barrier N rho hright).2
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < (N + 1 : ℕ))]
  simpa only [mul_comm (Real.log ((N + 1 : ℕ) : ℝ))] using h

/-- Raw Möbius truncations diverge in residual norm at every actual right
zero. This is a structural obstruction, not merely a bad finite sample. -/
theorem native_mobius_residual_norm_tendsto_atTop (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    Tendsto (fun N : ℕ => ‖mobiusProbePartialResidual N‖) atTop atTop := by
  let d : ℝ := ((rho : ℂ) - 1 / 2).re
  let c : ℝ := Real.sqrt (2 * d) *
    ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
      JPlus ((rho : ℂ) - 1 / 2)‖
  have hd : 0 < d := by
    change 0 < ((rho : ℂ) - 1 / 2).re
    simp only [Complex.sub_re]; norm_num; linarith
  have hc : 0 < c := (native_probe_zero_separation rho hright).1
  have hN : Tendsto (fun N : ℕ => ((N + 1 : ℕ) : ℝ)) atTop atTop := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ)))
  have hpow := (tendsto_rpow_atTop hd).comp hN
  have hlow : Tendsto (fun N : ℕ => c * ((N + 1 : ℕ) : ℝ) ^ d) atTop atTop :=
    hpow.const_mul_atTop hc
  apply tendsto_atTop_mono (fun N => ?_) hlow
  simpa only [c,d,mul_assoc,mul_left_comm,mul_comm] using
    native_mobius_delayed_barrier_rpow N rho hright

/-- The safe source cutoff also controls actual Gram entries. Both output
norms are retained, so no unstated uniform input or column bound is needed. -/
theorem native_floor_cutoff_gram_bound (T : ℝ) (f g : ProbeL2) :
    ‖inner ℂ (CCM.nativeDampedCompletionL2Operator 0 (le_rfl) f)
        (CCM.nativeDampedCompletionL2Operator 0 (le_rfl) g) -
      inner ℂ (kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T) f)
        (kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T) g)‖ ≤
      (2 * Real.exp (-T / 2) * ‖f‖) * ‖CCM.nativeDampedCompletionL2Operator 0 (le_rfl) g‖ +
        ‖kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T) f‖ *
          (2 * Real.exp (-T / 2) * ‖g‖) := by
  let A := CCM.nativeDampedCompletionL2Operator 0 (le_rfl)
  let B := kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T)
  have hid : inner ℂ (A f) (A g) - inner ℂ (B f) (B g) =
      inner ℂ (A f - B f) (A g) + inner ℂ (B f) (A g - B g) := by
    rw [inner_sub_left,inner_sub_right]
    ring
  change ‖inner ℂ (A f) (A g) - inner ℂ (B f) (B g)‖ ≤ _
  rw [hid]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_right
      (native_floor_physical_cutoff_bound T f) (norm_nonneg _))
  · exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      (native_floor_physical_cutoff_bound T g) (norm_nonneg _))

/-- Translation preserves the full multiplicity sum. Under RH every zero in
the actual height window maps into the source disk; source orders are paid
pointwise before the finite sums are compared. -/
theorem probe_zeta_count_le_source_count_of_order_domination {T : ℝ} (hT : 0 < T)
    (hRH : RiemannHypothesis)
    (hDom : ∀ rho ∈ zetaZeroConfig.window T (2 * T),
      (zetaZeroConfig.mult rho : ℤ) ≤ (meromorphicOrderAt JPlus (rho - 1 / 2)).untop₀) :
    (zetaZeroConfig.N T (2 * T) : ℤ) ≤ probeSourceZeroCount (3 * T) := by
  classical
  let S := zetaZeroConfig.window T (2 * T)
  let D := MeromorphicOn.divisor JPlus (Metric.closedBall (0 : ℂ) (3 * T))
  have hS : S.Finite := zetaZeroConfig.finite_window T (2 * T)
  have hD : Function.HasFiniteSupport D := D.finiteSupport (isCompact_closedBall ..)
  have hAnalytic : AnalyticOnNhd ℂ JPlus (Metric.closedBall (0 : ℂ) (3 * T)) :=
    fun z _hz => JPlus_analyticAt z
  have hDnonneg : ∀ z, 0 ≤ D z := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAnalytic
  have hPoint : ∀ rho ∈ S, (zetaZeroConfig.mult rho : ℤ) ≤ D (rho - 1 / 2) := by
    intro rho hrho
    have hRe : rho.re = 1 / 2 := RH_implies_on_line hRH hrho.1
    have hnorm : ‖rho - (1 / 2 : ℂ)‖ ≤ 3 * T := by
      have hre : (rho - (1 / 2 : ℂ)).re = 0 := by simp [hRe]
      have him : (rho - (1 / 2 : ℂ)).im = rho.im := by simp
      rw [Complex.norm_def,Complex.normSq_apply,hre,him,zero_mul,zero_add,← pow_two,
        Real.sqrt_sq_eq_abs]
      rw [abs_of_pos (lt_trans hT hrho.2.1)]
      linarith [hrho.2.2]
    have hmem : rho - (1 / 2 : ℂ) ∈ Metric.closedBall (0 : ℂ) (3 * T) := by
      simpa only [Metric.mem_closedBall,dist_zero_right] using hnorm
    dsimp [D]
    rw [hAnalytic.meromorphicOn.divisor_apply hmem]
    exact hDom rho hrho
  have hinj : Function.Injective (fun rho : ℂ => rho - (1 / 2 : ℂ)) :=
    fun _x _y h => sub_left_injective h
  have hTranslated : Function.HasFiniteSupport (fun rho : ℂ => D (rho - 1 / 2)) :=
    Function.HasFiniteSupport.fun_comp_of_injective hinj hD
  calc
    (zetaZeroConfig.N T (2 * T) : ℤ) = ∑ᶠ rho ∈ S, (zetaZeroConfig.mult rho : ℤ) :=
      Nat.cast_finsum_mem hS _
    _ ≤ ∑ᶠ rho : ℂ, D (rho - 1 / 2) := by
      refine finsum_le_finsum' ?_ hTranslated ?_
      · apply hS.subset
        intro rho hrho
        by_contra hno
        simp [Function.mem_support,hno] at hrho
      · intro rho
        by_cases hrho : rho ∈ S
        · simpa [hrho] using hPoint rho hrho
        · simpa [hrho] using hDnonneg (rho - 1 / 2)
    _ = probeSourceZeroCount (3 * T) :=
      finsum_comp_equiv (Equiv.subRight (1 / 2 : ℂ))

/-- Actual zeta zero growth eventually exceeds the entire compact source's
linear divisor count. Thus, under RH, at least one genuine critical zero is
not cancelled to its full multiplicity by this exact source. -/
theorem native_probe_visible_critical_zero_of_RH (hRH : RiemannHypothesis) :
    ∃ rho : zetaZeroConfig.carrier, (rho : ℂ).re = 1 / 2 ∧
      (meromorphicOrderAt JPlus ((rho : ℂ) - 1 / 2)).untop₀ <
        (zetaZeroConfig.mult (rho : ℂ) : ℤ) := by
  classical
  by_contra hnone
  push Not at hnone
  let A : ℝ := Real.log (16 * max 1 probeSourceL1Mass) / Real.log 2
  let B : ℝ := 12 * probeSigma / Real.log 2
  let C : ℝ := |A| + B + 1
  obtain ⟨T,hlarge,hT1⟩ := ((native_zeta_zero_count_superlinear C).and
    (eventually_ge_atTop (1 : ℝ))).exists
  have hT : 0 < T := by linarith
  have hDom : ∀ rho ∈ zetaZeroConfig.window T (2 * T),
      (zetaZeroConfig.mult rho : ℤ) ≤ (meromorphicOrderAt JPlus (rho - 1 / 2)).untop₀ := by
    intro rho hrho
    exact hnone ⟨rho,hrho.1⟩ (RH_implies_on_line hRH hrho.1)
  have hcount : (zetaZeroConfig.N T (2 * T) : ℝ) ≤
      (probeSourceZeroCount (3 * T) : ℝ) := by
    exact_mod_cast probe_zeta_count_le_source_count_of_order_domination hT hRH hDom
  have hsource := probe_source_zero_count_bound (mul_pos (by norm_num : (0 : ℝ) < 3) hT)
  have hsource' : (probeSourceZeroCount (3 * T) : ℝ) ≤ A + B * T := by
    convert hsource using 1
    dsimp only [A,B]
    ring
  have hA : A ≤ |A| * T := by
    calc
      A ≤ |A| := le_abs_self A
      _ ≤ |A| * T := by nlinarith [abs_nonneg A]
  have hbudget : A + B * T < C * T := by
    dsimp only [C]
    nlinarith
  exact (not_lt_of_ge (hcount.trans hsource')) (hbudget.trans hlarge)

/-- Unconditional exact nonrange for the actual new undamped source/target.
The proof uses the genuine boundary-order obstruction and the unconditional
zeta/source zero counts. It makes no claim about closure of the range. -/
theorem native_probe_target_not_mem_range : probeTarget ∉ Set.range probeOperator := by
  rintro ⟨f,hf⟩
  have hRH : RiemannHypothesis := rh_of_native_probe_range (subset_closure ⟨f,hf⟩)
  obtain ⟨rho,hcritical,hvisible⟩ := native_probe_visible_critical_zero_of_RH hRH
  exact (not_lt_of_ge (native_probe_range_boundary_order f hf rho hcritical)) hvisible

/-- S07b's actual physical evaluation inequality, before any Taylor data or
one-variable optimization is introduced. -/
theorem probe_residual_evaluation_bound (z : ℂ) (hz : 0 < z.re) (hne : z ≠ 1 / 2)
    (f : CausalProbeL2) :
    Real.sqrt (2 * z.re) * ‖CCM.nativeCompletionRationalMultiplier z * JPlus z‖ ≤
      ‖probeTarget - probeOperator f‖ +
        ‖CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2)‖ * ‖f‖ := by
  let r : CausalProbeL2 := probeTarget - probeOperator f
  have hid : CCM.nativeCausalLaplaceMoment z 0 (probeTarget : ProbeL2) =
      CCM.nativeCausalLaplaceMoment z 0 (r : ProbeL2) +
        CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) *
          (CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2)) := by
    rw [← probeOperator_laplace z hz hne f,
      ← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment z hz 0,
      ← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment z hz 0,
      ← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment z hz 0]
    change inner ℂ _ probeTarget = inner ℂ _ (probeTarget - probeOperator f) + inner ℂ _ (probeOperator f)
    rw [inner_sub_right]
    ring
  have htri := norm_add_le (CCM.nativeCausalLaplaceMoment z 0 (r : ProbeL2))
    (CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) *
      (CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2)))
  rw [← hid,probeTarget_laplace_eq_physical,probeV_laplace hz.le,
    norm_mul (CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2))
      (CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2))] at htri
  have hr := probe_laplace_evaluation_bound z hz r
  have hf := probe_laplace_evaluation_bound z hz f
  have htri' := mul_le_mul_of_nonneg_left htri (Real.sqrt_nonneg (2 * z.re))
  have hf' := mul_le_mul_of_nonneg_left hf
    (norm_nonneg (CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2)))
  change _ ≤ ‖r‖ + _
  nlinarith

theorem probeSourceQuotient_negative_order_of_visible (rho : zetaZeroConfig.carrier)
    (hvisible : (meromorphicOrderAt JPlus ((rho : ℂ) - 1 / 2)).untop₀ <
      (zetaZeroConfig.mult (rho : ℂ) : ℤ)) :
    meromorphicOrderAt probeSourceQuotient ((rho : ℂ) - 1 / 2) < 0 := by
  let lambda : ℂ := (rho : ℂ) - 1 / 2
  have hZ := probe_shifted_zeta_analyticAt rho
  have hZo := probe_shifted_zeta_order rho
  have hJord : analyticOrderAt JPlus lambda = (analyticOrderNatAt JPlus lambda : ℕ∞) :=
    (Nat.cast_analyticOrderNatAt (JPlus_analyticOrderAt_ne_top lambda)).symm
  have hJo : meromorphicOrderAt JPlus lambda = ((analyticOrderNatAt JPlus lambda : ℤ) : WithTop ℤ) := by
    rw [(JPlus_analyticAt lambda).meromorphicOrderAt_eq,hJord,ENat.map_natCast]
  have hFo : meromorphicOrderAt probeSourceQuotient lambda =
      ((analyticOrderNatAt JPlus lambda : ℤ) - (zeroMult (rho : ℂ) : ℤ) : WithTop ℤ) := by
    rw [show probeSourceQuotient = JPlus / (fun z : ℂ => riemannZeta (z + 1 / 2)) from rfl,
      meromorphicOrderAt_div (JPlus_analyticAt lambda).meromorphicAt hZ.meromorphicAt,
      hJo,hZ.meromorphicOrderAt_eq,hZo,ENat.map_natCast]
  have hi : (analyticOrderNatAt JPlus lambda : ℤ) < (zeroMult (rho : ℂ) : ℤ) := by
    change (meromorphicOrderAt JPlus lambda).untop₀ < (zeroMult (rho : ℂ) : ℤ) at hvisible
    simpa only [hJo,WithTop.untop₀_coe] using hvisible
  change meromorphicOrderAt probeSourceQuotient lambda < 0
  rw [hFo]
  exact_mod_cast (sub_neg.mpr hi)

/-- Every fixed input norm budget leaves a positive residual gap. The
constant is existential and depends on that budget and actual source data;
it is not asserted to be uniform as the input budget grows. -/
theorem native_probe_bounded_input_gap (B : ℝ) :
    ∃ eta : ℝ, 0 < eta ∧ ∀ f : CausalProbeL2, ‖f‖ ≤ B →
      eta ≤ ‖probeTarget - probeOperator f‖ := by
  classical
  by_contra hnone
  push Not at hnone
  have hclosure : probeTarget ∈ closure (Set.range probeOperator) := by
    apply Metric.mem_closure_iff.mpr
    intro eta heta
    obtain ⟨f,hf,herr⟩ := hnone eta heta
    exact ⟨probeOperator f,⟨f,rfl⟩,by simpa only [dist_eq_norm] using herr⟩
  have hRH := rh_of_native_probe_range hclosure
  obtain ⟨rho,hcritical,hvisible⟩ := native_probe_visible_critical_zero_of_RH hRH
  let lambda : ℂ := (rho : ℂ) - 1 / 2
  have hlambda : lambda.re = 0 := by dsimp only [lambda]; simp [hcritical]
  have hZ := probe_shifted_zeta_analyticAt rho
  have hZo := probe_shifted_zeta_order rho
  have hZn : meromorphicOrderAt (fun z : ℂ => riemannZeta (z + 1 / 2)) lambda ≠ ⊤ := by
    rw [hZ.meromorphicOrderAt_eq,hZo,ENat.map_natCast]
    exact WithTop.coe_ne_top
  have hZnz := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero hZ.meromorphicAt).mp hZn
  have hR := ExceptionalZero.nativeCompletionRationalMultiplier_at_zero_analyticAt rho
  have hRnz : ∀ᶠ z in 𝓝 lambda, CCM.nativeCompletionRationalMultiplier z ≠ 0 :=
    hR.continuousAt.eventually_ne (probe_rational_multiplier_ne_zero rho)
  have hlne : lambda ≠ 1 / 2 := by
    intro h
    have hr := congrArg Complex.re h
    rw [hlambda] at hr
    norm_num at hr
  have hhalf : ∀ᶠ z in 𝓝 lambda, z ≠ (1 / 2 : ℂ) := eventually_ne_nhds hlne
  have hbound : ∀ᶠ e : ℝ in 𝓝[>] (0 : ℝ),
      Real.sqrt (2 * e) * ‖probeSourceQuotient (lambda + (e : ℂ))‖ ≤ B := by
    have hp := probe_boundary_ray_tendsto lambda
    filter_upwards [hp.eventually hZnz,
      hp.eventually (hRnz.filter_mono nhdsWithin_le_nhds),
      hp.eventually (hhalf.filter_mono nhdsWithin_le_nhds),self_mem_nhdsWithin]
      with e hze hre hhe he
    have hepos : 0 < e := he
    let z : ℂ := lambda + (e : ℂ)
    have hz : 0 < z.re := by simpa only [z,Complex.add_re,Complex.ofReal_re,hlambda,zero_add] using hepos
    have hzre : z.re = e := by simp only [z,Complex.add_re,Complex.ofReal_re,hlambda,zero_add]
    let A : ℝ := ‖CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2)‖
    let V : ℝ := Real.sqrt (2 * e) * ‖CCM.nativeCompletionRationalMultiplier z * JPlus z‖
    have hbudget : V ≤ A * B := by
      by_contra hno
      have hgap : 0 < (V - A * B) / 2 := by linarith
      obtain ⟨f,hf,herr⟩ := hnone ((V - A * B) / 2) hgap
      have hev := probe_residual_evaluation_bound z hz hhe f
      rw [hzre] at hev
      change V ≤ ‖probeTarget - probeOperator f‖ + A * ‖f‖ at hev
      have hAB := mul_le_mul_of_nonneg_left hf (show 0 ≤ A from norm_nonneg _)
      linarith
    have hRpos : 0 < ‖CCM.nativeCompletionRationalMultiplier z‖ := norm_pos_iff.mpr hre
    have hZpos : 0 < ‖riemannZeta (z + 1 / 2)‖ := norm_pos_iff.mpr hze
    have hJR : Real.sqrt (2 * e) * ‖JPlus z‖ ≤ ‖riemannZeta (z + 1 / 2)‖ * B := by
      apply le_of_mul_le_mul_left (a := ‖CCM.nativeCompletionRationalMultiplier z‖) ?_ hRpos
      simpa only [V,A,norm_mul,mul_assoc,mul_left_comm,mul_comm] using hbudget
    change Real.sqrt (2 * e) * ‖probeSourceQuotient z‖ ≤ B
    rw [probeSourceQuotient,norm_div,← mul_div_assoc]
    apply (div_le_iff₀ hZpos).mpr
    simpa only [mul_comm B] using hJR
  have hfirst := probe_boundary_first_order_limit_of_bound
    (fun e : ℝ => probeSourceQuotient (lambda + (e : ℂ))) B hbound
  have hF : MeromorphicAt probeSourceQuotient lambda :=
    (JPlus_analyticAt lambda).meromorphicAt.div hZ.meromorphicAt
  have ho := probe_boundary_meromorphic_order_nonneg_of_limit lambda probeSourceQuotient hF hfirst
  exact (not_lt_of_ge ho) (probeSourceQuotient_negative_order_of_visible rho hvisible)

/-- S07d: any genuinely successful approximation sequence has input norms
tending to infinity. Exact nonrange does not preclude range closure. -/
theorem native_probe_successful_input_norms_tendsto_atTop (u : ℕ → CausalProbeL2)
    (herr : Tendsto (fun N : ℕ => ‖probeTarget - probeOperator (u N)‖) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => ‖u N‖) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  obtain ⟨eta,heta,hgap⟩ := native_probe_bounded_input_gap B
  have hevent : ∀ᶠ N : ℕ in atTop, ‖probeTarget - probeOperator (u N)‖ < eta :=
    herr.eventually (eventually_lt_nhds heta)
  filter_upwards [hevent] with N hN
  by_contra hno
  exact (not_lt_of_ge (hgap (u N) (le_of_lt (lt_of_not_ge hno)))) hN

/-- Two-sided bounds follow from the actual nonzero leading Taylor factor.
The constants and radius depend on the function, point and exact order. -/
theorem analytic_order_ray_bounds (F : ℂ → ℂ) (lambda : ℂ) (k : ℕ)
    (hF : AnalyticAt ℂ F lambda) (horder : analyticOrderAt F lambda = (k : ℕ∞)) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ e : ℝ, 0 < e → e ≤ r →
      c * e ^ k ≤ ‖F (lambda + (e : ℂ))‖ ∧
        ‖F (lambda + (e : ℂ))‖ ≤ C * e ^ k := by
  obtain ⟨g,hg,hgne,hfactor⟩ := hF.analyticOrderAt_eq_natCast.mp horder
  have hgpos : 0 < ‖g lambda‖ := norm_pos_iff.mpr hgne
  have hnear : ∀ᶠ z in 𝓝 lambda,
      ‖g lambda‖ / 2 ≤ ‖g z‖ ∧ ‖g z‖ ≤ 2 * ‖g lambda‖ := by
    have h := hg.continuousAt.norm.tendsto.eventually
      (Ioo_mem_nhds (by linarith : ‖g lambda‖ / 2 < ‖g lambda‖)
        (by linarith : ‖g lambda‖ < 2 * ‖g lambda‖))
    filter_upwards [h] with z hz
    exact ⟨hz.1.le,hz.2.le⟩
  obtain ⟨r,hr,hall⟩ := Metric.eventually_nhds_iff.mp (hfactor.and hnear)
  refine ⟨‖g lambda‖ / 2,2 * ‖g lambda‖,r / 2,by positivity,by positivity,by positivity,?_⟩
  intro e he her
  have hdist : dist (lambda + (e : ℂ)) lambda < r := by
    rw [dist_eq_norm,add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he]
    linarith
  obtain ⟨hfac,hlo,hhi⟩ := hall hdist
  have hn : ‖F (lambda + (e : ℂ))‖ = e ^ k * ‖g (lambda + (e : ℂ))‖ := by
    rw [hfac,norm_smul,norm_pow]
    simp only [add_sub_cancel_left,Complex.norm_real,Real.norm_eq_abs,abs_of_pos he]
  rw [hn]
  constructor
  · simpa only [mul_comm (‖g lambda‖ / 2)] using
      mul_le_mul_of_nonneg_left hlo (pow_nonneg he.le k)
  · simpa only [mul_comm (2 * ‖g lambda‖)] using
      mul_le_mul_of_nonneg_left hhi (pow_nonneg he.le k)

/-- Actual source and kernel Taylor data at any genuine nontrivial zero.
No sign, simplicity, RH, or source-visibility assumption is manufactured. -/
theorem native_probe_boundary_taylor_bounds (rho : zetaZeroConfig.carrier) (k : ℕ)
    (hk : analyticOrderAt JPlus ((rho : ℂ) - 1 / 2) = (k : ℕ∞)) :
    ∃ c C r : ℝ, 0 < c ∧ 0 < C ∧ 0 < r ∧ ∀ e : ℝ, 0 < e → e ≤ r →
      c * e ^ k ≤ ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2 + (e : ℂ)) *
        JPlus ((rho : ℂ) - 1 / 2 + (e : ℂ))‖ ∧
      ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2 + (e : ℂ)) *
        riemannZeta ((rho : ℂ) - 1 / 2 + (e : ℂ) + 1 / 2)‖ ≤
        C * e ^ zeroMult (rho : ℂ) := by
  let lambda : ℂ := (rho : ℂ) - 1 / 2
  have hR := ExceptionalZero.nativeCompletionRationalMultiplier_at_zero_analyticAt rho
  have hRn : analyticOrderAt CCM.nativeCompletionRationalMultiplier lambda = 0 :=
    hR.analyticOrderAt_eq_zero.mpr (probe_rational_multiplier_ne_zero rho)
  have hJ := JPlus_analyticAt lambda
  have hZ := probe_shifted_zeta_analyticAt rho
  have hZo := probe_shifted_zeta_order rho
  have hV : AnalyticAt ℂ (fun z => CCM.nativeCompletionRationalMultiplier z * JPlus z) lambda := hR.mul hJ
  have hA : AnalyticAt ℂ (fun z => CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2)) lambda :=
    hR.mul hZ
  have hVo : analyticOrderAt (fun z => CCM.nativeCompletionRationalMultiplier z * JPlus z) lambda = (k : ℕ∞) := by
    change analyticOrderAt (CCM.nativeCompletionRationalMultiplier * JPlus) lambda = (k : ℕ∞)
    rw [analyticOrderAt_mul hR hJ,hRn,zero_add]
    exact hk
  have hAo : analyticOrderAt (fun z => CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2)) lambda =
      (zeroMult (rho : ℂ) : ℕ∞) := by
    change analyticOrderAt (CCM.nativeCompletionRationalMultiplier *
      (fun z : ℂ => riemannZeta (z + 1 / 2))) lambda = (zeroMult (rho : ℂ) : ℕ∞)
    rw [analyticOrderAt_mul hR hZ,hRn,zero_add]
    exact hZo
  obtain ⟨cV,CV,rV,hcV,_hCV,hrV,hbV⟩ := analytic_order_ray_bounds _ lambda k hV hVo
  obtain ⟨cA,CA,rA,_hcA,hCA,hrA,hbA⟩ := analytic_order_ray_bounds _ lambda (zeroMult (rho : ℂ)) hA hAo
  refine ⟨cV,CA,min rV rA,hcV,hCA,lt_min hrV hrA,?_⟩
  intro e he her
  exact ⟨(hbV e he (her.trans (min_le_left _ _))).1,
    (hbA e he (her.trans (min_le_right _ _))).2⟩

theorem positive_power_tradeoff (a C p q r : ℝ)
    (ha : 0 < a) (hC : 0 < C) (hp : 0 < p) (hpq : p < q) (hr : 0 < r) :
    ∃ cstar M0 : ℝ, 0 < cstar ∧ 0 < M0 ∧ ∀ M eta : ℝ, M0 ≤ M →
      (∀ e : ℝ, 0 < e → e ≤ r → a * e ^ p - C * M * e ^ q ≤ eta) →
      cstar * M ^ (-(p / (q - p))) ≤ eta := by
  let d := q - p
  let s := p / d
  let kappa := a / (2 * C)
  have hd : 0 < d := by dsimp only [d]; linarith
  have hs : 0 < s := div_pos hp hd
  have hk : 0 < kappa := div_pos ha (mul_pos (by norm_num) hC)
  refine ⟨a / 2 * kappa ^ s,max 1 (kappa / r ^ d),by positivity,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro M eta hM0 hbudget
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hM0)
  have hMr : kappa / r ^ d ≤ M := (le_max_right _ _).trans hM0
  have hratio : kappa / M ≤ r ^ d := by
    apply (div_le_iff₀ hM).mpr
    have h := (div_le_iff₀ (Real.rpow_pos_of_pos hr d)).mp hMr
    simpa only [mul_comm] using h
  have hratioPos : 0 < kappa / M := div_pos hk hM
  let e : ℝ := (kappa / M) ^ (1 / d)
  have he : 0 < e := Real.rpow_pos_of_pos hratioPos _
  have her : e ≤ r := by
    have h := Real.rpow_le_rpow hratioPos.le hratio (one_div_nonneg.mpr hd.le)
    rw [← Real.rpow_mul hr.le,mul_one_div_cancel hd.ne',Real.rpow_one] at h
    exact h
  have hed : e ^ d = kappa / M := by
    dsimp only [e]
    rw [← Real.rpow_mul hratioPos.le,one_div_mul_cancel hd.ne',Real.rpow_one]
  have heq : e ^ q = e ^ p * e ^ d := by
    have hq : q = p + d := by dsimp only [d]; ring
    rw [hq,Real.rpow_add he]
  have hhalf : C * M * e ^ q = a / 2 * e ^ p := by
    rw [heq,hed]
    dsimp only [kappa]
    field_simp
  have hep : e ^ p = kappa ^ s * M ^ (-s) := by
    calc
      e ^ p = (kappa / M) ^ s := by
        dsimp only [e,s]
        rw [← Real.rpow_mul hratioPos.le]
        congr 1
        ring
      _ = _ := by
        rw [Real.div_rpow hk.le hM.le,Real.rpow_neg hM.le]
        rfl
  have hb := hbudget e he her
  rw [hhalf] at hb
  have hid : a * e ^ p - a / 2 * e ^ p = a / 2 * e ^ p := by ring
  rw [hid,hep] at hb
  simpa only [d,s,mul_assoc] using hb

/-- S07b: the exact critical-zero and source orders determine the input-cost
exponent. The constants depend on the actual local Taylor data. -/
theorem native_probe_boundary_power_cost (rho : zetaZeroConfig.carrier)
    (hcritical : (rho : ℂ).re = 1 / 2) (k : ℕ)
    (hk : analyticOrderAt JPlus ((rho : ℂ) - 1 / 2) = (k : ℕ∞))
    (hkm : k < zeroMult (rho : ℂ)) :
    ∃ cstar M0 : ℝ, 0 < cstar ∧ 0 < M0 ∧ ∀ f : CausalProbeL2, M0 ≤ ‖f‖ →
      cstar * ‖f‖ ^ (-((2 * (k : ℝ) + 1) /
        (2 * (zeroMult (rho : ℂ) : ℝ) - 2 * (k : ℝ) - 1))) ≤
        ‖probeTarget - probeOperator f‖ := by
  obtain ⟨c,C,r,hc,hC,hr,htaylor⟩ := native_probe_boundary_taylor_bounds rho k hk
  let p : ℝ := (k : ℝ) + 1 / 2
  let q : ℝ := zeroMult (rho : ℂ)
  let a : ℝ := Real.sqrt 2 * c
  have hp : 0 < p := by dsimp only [p]; positivity
  have hpq : p < q := by
    have h : (k : ℝ) + 1 ≤ (zeroMult (rho : ℂ) : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hkm
    dsimp only [p,q]
    linarith
  have ha : 0 < a := mul_pos (Real.sqrt_pos.mpr (by norm_num)) hc
  obtain ⟨cstar,M0,hcs,hM0,htrade⟩ :=
    positive_power_tradeoff a C p q (min r (1 / 4)) ha hC hp hpq (lt_min hr (by norm_num))
  refine ⟨cstar,M0,hcs,hM0,?_⟩
  intro f hf
  have hb := htrade ‖f‖ ‖probeTarget - probeOperator f‖ hf
  have hcost : cstar * ‖f‖ ^ (-(p / (q - p))) ≤ ‖probeTarget - probeOperator f‖ := by
    apply hb
    intro e he her
    have hbounds := htaylor e he (her.trans (min_le_left _ _))
    let z : ℂ := (rho : ℂ) - 1 / 2 + (e : ℂ)
    have hzre : z.re = e := by dsimp only [z]; simp [hcritical]
    have hz : 0 < z.re := hzre.symm ▸ he
    have hne : z ≠ 1 / 2 := by
      intro heq
      have hre := congrArg Complex.re heq
      rw [hzre] at hre
      have hequarter := her.trans (min_le_right _ _)
      norm_num at hre
      linarith
    have hev := probe_residual_evaluation_bound z hz hne f
    rw [hzre] at hev
    have hV := mul_le_mul_of_nonneg_left hbounds.1 (Real.sqrt_nonneg (2 * e))
    have hA := mul_le_mul_of_nonneg_right hbounds.2 (norm_nonneg f)
    have hepower : e ^ p = e ^ k * Real.sqrt e := by
      dsimp only [p]
      rw [Real.rpow_add he,Real.rpow_natCast,← Real.sqrt_eq_rpow]
    rw [hepower,show e ^ q = e ^ zeroMult (rho : ℂ) from Real.rpow_natCast _ _]
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)] at hV hev
    dsimp only [z] at hev
    change _ ≤ ‖probeTarget - probeOperator f‖
    dsimp only [a]
    nlinarith
  have hexp : p / (q - p) = (2 * (k : ℝ) + 1) /
      (2 * (zeroMult (rho : ℂ) : ℝ) - 2 * (k : ℝ) - 1) := by
    have hd1 : q - p ≠ 0 := (sub_pos.mpr hpq).ne'
    have hd2 : 2 * (zeroMult (rho : ℂ) : ℝ) - 2 * (k : ℝ) - 1 ≠ 0 := by
      dsimp only [p,q] at hpq
      linarith
    apply (div_eq_div_iff hd1 hd2).mpr
    dsimp only [p,q]
    ring
  simpa only [hexp] using hcost

/-- S07c: a fully visible actual critical zero gives the arbitrary-
multiplicity power-law input requirement in the sufficiently small-error
regime. Visibility is explicit and is never inferred from criticality. -/
theorem native_probe_visible_boundary_input_cost (rho : zetaZeroConfig.carrier)
    (hcritical : (rho : ℂ).re = 1 / 2)
    (hvisible : JPlus ((rho : ℂ) - 1 / 2) ≠ 0) :
    ∃ cstar eta0 : ℝ, 0 < cstar ∧ 0 < eta0 ∧
      ∀ eta : ℝ, 0 < eta → eta ≤ eta0 → ∀ f : CausalProbeL2,
        ‖probeTarget - probeOperator f‖ ≤ eta →
        (cstar / eta) ^ (2 * (zeroMult (rho : ℂ) : ℝ) - 1) ≤ ‖f‖ := by
  have hk : analyticOrderAt JPlus ((rho : ℂ) - 1 / 2) = (0 : ℕ∞) :=
    (JPlus_analyticAt _).analyticOrderAt_eq_zero.mpr hvisible
  have hm : 0 < zeroMult (rho : ℂ) :=
    lt_of_lt_of_le Nat.zero_lt_one (zetaZeroConfig.one_le_mult _ rho.property)
  obtain ⟨cstar,M0,hcs,hM0,hcost⟩ := native_probe_boundary_power_cost rho hcritical 0 hk hm
  obtain ⟨gap,hgap,hbudget⟩ := native_probe_bounded_input_gap M0
  refine ⟨cstar,min (gap / 2) 1,hcs,lt_min (by positivity) (by norm_num),?_⟩
  intro eta heta heta0 f herr
  have hMf : M0 ≤ ‖f‖ := by
    by_contra hno
    have h := hbudget f (le_of_lt (lt_of_not_ge hno))
    have hetaGap := heta0.trans (min_le_left _ _)
    linarith
  have hfpos : 0 < ‖f‖ := lt_of_lt_of_le hM0 hMf
  let d : ℝ := 2 * (zeroMult (rho : ℂ) : ℝ) - 1
  have hd : 0 < d := by
    have hm1 : (1 : ℝ) ≤ zeroMult (rho : ℂ) := by exact_mod_cast (Nat.succ_le_iff.mpr hm)
    dsimp only [d]
    linarith
  have hcost' : cstar * ‖f‖ ^ (-(1 / d)) ≤ eta := by
    have h := (hcost f hMf).trans herr
    simpa only [Nat.cast_zero,mul_zero,zero_add,sub_zero,one_div,d] using h
  have hroot : 0 < ‖f‖ ^ (1 / d) := Real.rpow_pos_of_pos hfpos _
  rw [Real.rpow_neg hfpos.le,← div_eq_mul_inv] at hcost'
  have hfirst : cstar / eta ≤ ‖f‖ ^ (1 / d) := by
    apply (div_le_iff₀ heta).mpr
    have h := (div_le_iff₀ hroot).mp hcost'
    simpa only [mul_comm] using h
  have hraise := Real.rpow_le_rpow (div_pos hcs heta).le hfirst hd.le
  rw [← Real.rpow_mul hfpos.le,one_div_mul_cancel hd.ne',Real.rpow_one] at hraise
  exact hraise

theorem mobiusProbeSource_first_cell {t : ℝ} (ht : t < Real.log 2) :
    mobiusProbeSource t = jPlus t := by
  have h := arithmetic_history_before_next
    (ArithmeticFunction.moebius : ArithmeticFunction ℝ)
    (fun _s hs => jPlus_zero_of_neg hs) 1 ht
  simpa [mobiusProbeSource,Finset.sum_range_succ] using h

theorem mobiusProbeSource_nonzero_first_cell :
    ∃ t : ℝ, t < Real.log 2 ∧ mobiusProbeSource t ≠ 0 := by
  have hj : jPlus ≠ 0 := by
    intro h
    have hi := jPlus_integral
    rw [h] at hi
    norm_num at hi
  obtain ⟨t,ht⟩ := Function.ne_iff.mp hj
  have htin : t ∈ Icc 0 (2 * probeSigma) := by
    by_contra hno
    exact ht (jPlus_zero_outside hno)
  have hlog : t < Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (2 : ℝ))
    rw [probeSigma_eq] at htin
    norm_num at h
    linarith [htin.2]
  exact ⟨t,hlog,by rwa [mobiusProbeSource_first_cell hlog]⟩

theorem probeFloorKernelCutoff_eq_Icc (T t : ℝ) :
    probeFloorKernelCutoff T t = (Icc (0 : ℝ) T).indicator CCM.nativePositiveCompletion t := by
  by_cases ht0 : 0 ≤ t
  · by_cases htT : t ≤ T <;> simp [probeFloorKernelCutoff,ht0,htT]
  · simp [probeFloorKernelCutoff,ht0,
      CCM.nativePositiveCompletion_eq_zero_of_neg (lt_of_not_ge ht0)]

/-- The public P15 contract retains the literal raw Möbius coefficients,
the exact activation delay and the positive right-zero power. -/
theorem mobius_partial_zero_barrier (N : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) :
    (∀ᵐ t : ℝ, t < Real.log (N + 1 : ℕ) →
      (mobiusProbePartialResidual N : ProbeL2) t = 0) ∧
    Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re) *
      ((N + 1 : ℕ) : ℝ) ^ (((rho : ℂ) - 1 / 2).re) *
      ‖CCM.nativeCompletionRationalMultiplier ((rho : ℂ) - 1 / 2) *
        JPlus ((rho : ℂ) - 1 / 2)‖ ≤ ‖mobiusProbePartialResidual N‖ :=
  ⟨mobiusProbePartialResidual_delayed N,native_mobius_delayed_barrier_rpow N rho hright⟩

/-- The complete S07 contract separates unconditional exact nonrange,
literal evaluation, source-order cost, explicit full visibility and input
growth. No component identifies range with range closure. -/
theorem native_undamped_nonrange_and_input_cost :
    probeTarget ∉ Set.range probeOperator ∧
    (∀ z : ℂ, 0 < z.re → z ≠ 1 / 2 → ∀ f : CausalProbeL2,
      Real.sqrt (2 * z.re) * ‖CCM.nativeCompletionRationalMultiplier z * JPlus z‖ ≤
        ‖probeTarget - probeOperator f‖ +
          ‖CCM.nativeCompletionRationalMultiplier z * riemannZeta (z + 1 / 2)‖ * ‖f‖) ∧
    (∀ rho : zetaZeroConfig.carrier, (rho : ℂ).re = 1 / 2 → ∀ k : ℕ,
      analyticOrderAt JPlus ((rho : ℂ) - 1 / 2) = (k : ℕ∞) → k < zeroMult (rho : ℂ) →
      ∃ cstar M0 : ℝ, 0 < cstar ∧ 0 < M0 ∧ ∀ f : CausalProbeL2, M0 ≤ ‖f‖ →
        cstar * ‖f‖ ^ (-((2 * (k : ℝ) + 1) /
          (2 * (zeroMult (rho : ℂ) : ℝ) - 2 * (k : ℝ) - 1))) ≤
          ‖probeTarget - probeOperator f‖) ∧
    (∀ rho : zetaZeroConfig.carrier, (rho : ℂ).re = 1 / 2 →
      JPlus ((rho : ℂ) - 1 / 2) ≠ 0 →
      ∃ cstar eta0 : ℝ, 0 < cstar ∧ 0 < eta0 ∧
        ∀ eta : ℝ, 0 < eta → eta ≤ eta0 → ∀ f : CausalProbeL2,
          ‖probeTarget - probeOperator f‖ ≤ eta →
          (cstar / eta) ^ (2 * (zeroMult (rho : ℂ) : ℝ) - 1) ≤ ‖f‖) ∧
    (∀ u : ℕ → CausalProbeL2,
      Tendsto (fun N : ℕ => ‖probeTarget - probeOperator (u N)‖) atTop (𝓝 0) →
      Tendsto (fun N : ℕ => ‖u N‖) atTop atTop) :=
  ⟨native_probe_target_not_mem_range,probe_residual_evaluation_bound,
    native_probe_boundary_power_cost,native_probe_visible_boundary_input_cost,
    native_probe_successful_input_norms_tendsto_atTop⟩

def probeIntegerTargetPrefix (K : ℕ) (t : ℝ) : ℂ :=
  ∑ n ∈ range (K + 1), (CCM.nativeIntegerCoefficient n : ℂ) * probeV (t - Real.log n)

theorem probeIntegerTargetPrefix_memLp (K : ℕ) : MemLp (probeIntegerTargetPrefix K) 2 volume := by
  apply memLp_finsetSum
  intro n _hn
  exact (probeV_memLp.comp_measurePreserving (measurePreserving_sub_right volume (Real.log n))).const_mul _

def probeIntegerTargetPrefixL2 (K : ℕ) : ProbeL2 :=
  (probeIntegerTargetPrefix_memLp K).toLp (probeIntegerTargetPrefix K)

theorem probeIntegerTargetPrefixL2_coeFn (K : ℕ) :
    (probeIntegerTargetPrefixL2 K : ProbeL2) =ᵐ[volume] probeIntegerTargetPrefix K :=
  (probeIntegerTargetPrefix_memLp K).coeFn_toLp

def probeNativeTailAmplitude : ℂ := 2 * JPlus (-3 / 2 : ℂ)

theorem probeNativeTailAmplitude_norm_lower : 8 ≤ ‖probeNativeTailAmplitude‖ := by
  have hreal : Integrable (fun t : ℝ => qPlus t * Real.exp ((3 / 2 : ℝ) * t)) := by
    exact (qPlus_contDiff.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      qPlus_hasCompactSupport.mul_right
  have hp (t : ℝ) : qPlus t ≤ qPlus t * Real.exp ((3 / 2 : ℝ) * t) := by
    by_cases ht : 0 ≤ t
    · have he : 1 ≤ Real.exp ((3 / 2 : ℝ) * t) := Real.one_le_exp (by positivity)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left he (qPlus_nonneg t)
    · rw [qPlus_zero_of_neg (lt_of_not_ge ht),zero_mul]
  have hQ : 1 ≤ (QPlus (-3 / 2 : ℂ)).re := by
    have h := integral_mono qPlus_integrable hreal hp
    rw [qPlus_integral_one] at h
    have hre : (QPlus (-3 / 2 : ℂ)).re =
        ∫ t : ℝ, qPlus t * Real.exp ((3 / 2 : ℝ) * t) := by
      rw [QPlus_re_integral]
      apply integral_congr_ae
      filter_upwards with t
      norm_num
    rwa [hre]
  have hJ : JPlus (-3 / 2 : ℂ) = 4 * QPlus (-3 / 2 : ℂ) := by
    rw [JPlus_eq_pole_polynomial_QPlus]
    norm_num
  have hD : 8 ≤ probeNativeTailAmplitude.re := by
    rw [probeNativeTailAmplitude,hJ]
    norm_num [Complex.mul_re]
    linarith
  exact hD.trans (Complex.re_le_norm _)

theorem probe_integer_weight_growing {n : ℕ} (hn : n ≠ 0) :
    CCM.nativeIntegerCoefficient n * Real.exp (3 * Real.log n / 2) = (n : ℝ) := by
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hroot : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
    rw [Real.exp_half,Real.exp_log hnreal]
  rw [CCM.nativeIntegerCoefficient,hroot,one_div,← Real.exp_neg,← Real.exp_add]
  have harg : -(Real.log (n : ℝ) / 2) + 3 * Real.log n / 2 = Real.log n := by ring
  rw [harg,Real.exp_log hnreal]

theorem probe_sum_nat_cast_range (K : ℕ) :
    (∑ n ∈ range (K + 1), (n : ℂ)) = (K : ℂ) * ((K : ℂ) + 1) / 2 := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ,ih]
    push_cast
    ring

theorem probeIntegerTargetPrefix_tail {K : ℕ} (_hK : 1 ≤ K) {t : ℝ}
    (ht : Real.log K + 2 * probeSigma ≤ t) :
    probeIntegerTargetPrefix K t = probeNativeTailAmplitude *
      Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) * ((K : ℂ) * ((K : ℂ) + 1) / 2) := by
  have hsum : probeIntegerTargetPrefix K t =
      ∑ n ∈ range (K + 1), probeNativeTailAmplitude *
        Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) * (n : ℂ) := by
    apply sum_congr rfl
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      simp [CCM.nativeIntegerCoefficient]
    have hnK : (n : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show n ≤ K by simpa using mem_range.mp hn)
    have hnpos : 0 < (n : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)
    have hlog : Real.log n ≤ Real.log K := Real.log_le_log hnpos hnK
    have hafter : 2 * probeSigma ≤ t - Real.log n := by linarith
    rw [probeV_tail hafter]
    have heq : Complex.exp (-(3 / 2 : ℂ) * ((t - Real.log n : ℝ) : ℂ)) =
        Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) *
          (Real.exp (3 * Real.log n / 2) : ℂ) := by
      rw [Complex.ofReal_exp,← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [heq]
    have hweight : (CCM.nativeIntegerCoefficient n : ℂ) *
        (Real.exp (3 * Real.log n / 2) : ℂ) = (n : ℂ) := by
      simpa only [Complex.ofReal_mul,Complex.ofReal_natCast] using
        congrArg (fun r : ℝ => (r : ℂ)) (probe_integer_weight_growing hn0)
    dsimp only [probeNativeTailAmplitude]
    calc
      _ = (2 * JPlus (-3 / 2 : ℂ)) * Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) *
          ((CCM.nativeIntegerCoefficient n : ℂ) * (Real.exp (3 * Real.log n / 2) : ℂ)) := by ring
      _ = _ := by rw [hweight]
  rw [hsum,← Finset.mul_sum,probe_sum_nat_cast_range]

theorem probeIntegerTargetPrefix_square_integrable (K : ℕ) :
    Integrable (fun t : ℝ => ‖probeIntegerTargetPrefix K t‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm (probeIntegerTargetPrefix_memLp K).aestronglyMeasurable).mp
    (probeIntegerTargetPrefix_memLp K)

theorem probeIntegerTargetPrefixL2_norm_sq (K : ℕ) :
    ‖probeIntegerTargetPrefixL2 K‖ ^ 2 = ∫ t : ℝ, ‖probeIntegerTargetPrefix K t‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),L2.inner_def,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) (probeIntegerTargetPrefixL2 K) (probeIntegerTargetPrefixL2 K))]
  apply integral_congr_ae
  filter_upwards [probeIntegerTargetPrefixL2_coeFn K] with t ht
  rw [ht,inner_self_eq_norm_sq_to_K]
  change (((‖probeIntegerTargetPrefix K t‖ : ℝ) : ℂ) ^ 2).re = ‖probeIntegerTargetPrefix K t‖ ^ 2
  rw [← Complex.ofReal_pow,Complex.ofReal_re]

theorem native_exponential_tail_square (D : ℂ) (a L : ℝ) (ha : 0 < a) :
    (∫ t : ℝ in Ioi L, ‖D * Complex.exp (-(a : ℂ) * (t : ℂ))‖ ^ 2) =
      ‖D‖ ^ 2 * Real.exp (-2 * a * L) / (2 * a) := by
  have hp (t : ℝ) : ‖D * Complex.exp (-(a : ℂ) * (t : ℂ))‖ ^ 2 =
      ‖D‖ ^ 2 * Real.exp ((-2 * a) * t) := by
    have hre : (-(a : ℂ) * (t : ℂ)).re = -a * t := by simp
    have he : Real.exp (-a * t) ^ 2 = Real.exp ((-2 * a) * t) := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    rw [norm_mul,mul_pow,Complex.norm_exp,hre,he]
  rw [integral_congr_ae (Filter.Eventually.of_forall hp),integral_const_mul,
    integral_exp_mul_Ioi (by nlinarith : -2 * a < 0) L]
  field_simp

theorem probeIntegerTargetPrefix_tail_square {K : ℕ} (hK : 1 ≤ K) :
    (∫ t : ℝ in Ioi (Real.log K + 2 * probeSigma), ‖probeIntegerTargetPrefix K t‖ ^ 2) =
      ‖probeNativeTailAmplitude‖ ^ 2 * Real.exp (-6 * probeSigma) * ((K : ℝ) + 1) ^ 2 /
        (12 * (K : ℝ)) := by
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  let A : ℂ := probeNativeTailAmplitude * ((K : ℂ) * ((K : ℂ) + 1) / 2)
  have hp : (fun t : ℝ => ‖probeIntegerTargetPrefix K t‖ ^ 2) =ᵐ[
      volume.restrict (Ioi (Real.log K + 2 * probeSigma))]
      fun t : ℝ => ‖A * Complex.exp (-(3 / 2 : ℂ) * (t : ℂ))‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hc : probeIntegerTargetPrefix K t = A * Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) := by
      rw [probeIntegerTargetPrefix_tail hK ht.le]
      dsimp only [A]
      ring
    rw [hc]
  have hrateC : (3 / 2 : ℂ) = ((3 / 2 : ℝ) : ℂ) := by norm_num
  rw [integral_congr_ae hp,hrateC,native_exponential_tail_square A (3 / 2) _ (by norm_num)]
  have htri : (K : ℂ) * ((K : ℂ) + 1) / 2 =
      (((K : ℝ) * ((K : ℝ) + 1) / 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_add,
      Complex.ofReal_natCast,Complex.ofReal_one,Complex.ofReal_ofNat]
  have htriNorm : ‖(K : ℂ) * ((K : ℂ) + 1) / 2‖ = (K : ℝ) * ((K : ℝ) + 1) / 2 := by
    rw [htri,Complex.norm_real,Real.norm_eq_abs]
    exact abs_of_nonneg (by positivity)
  have hexp : Real.exp (-3 * (Real.log K + 2 * probeSigma)) =
      Real.exp (-6 * probeSigma) / (K : ℝ) ^ 3 := by
    have harg : -3 * (Real.log (K : ℝ) + 2 * probeSigma) =
        -6 * probeSigma - 3 * Real.log K := by ring
    have hpow : Real.exp (3 * Real.log (K : ℝ)) = (K : ℝ) ^ 3 := by
      rw [show 3 * Real.log (K : ℝ) = Real.log K + Real.log K + Real.log K by ring]
      simp only [Real.exp_add,Real.exp_log hKpos]
      ring
    rw [harg,Real.exp_sub,hpow]
  dsimp only [A]
  rw [norm_mul,mul_pow,htriNorm]
  norm_num only [show (-2 : ℝ) * (3 / 2) = -3 by norm_num,
    show (2 : ℝ) * (3 / 2) = 3 by norm_num]
  rw [hexp]
  field_simp
  <;> ring

def probeIntegerTailConstant : ℝ := ‖probeNativeTailAmplitude‖ ^ 2 * Real.exp (-3 * probeSigma) / 12

theorem probeIntegerTailConstant_pos : 0 < probeIntegerTailConstant := by
  have hD : 0 < ‖probeNativeTailAmplitude‖ := lt_of_lt_of_le (by norm_num) probeNativeTailAmplitude_norm_lower
  dsimp only [probeIntegerTailConstant]
  positivity

theorem probeIntegerTargetPrefix_tail_square_paper {K : ℕ} (hK : 1 ≤ K) :
    (∫ t : ℝ in Ioi (Real.log K + 2 * probeSigma), ‖probeIntegerTargetPrefix K t‖ ^ 2) =
      probeIntegerTailConstant * Real.exp (-3 * probeSigma) * ((K : ℝ) + 1) ^ 2 / (K : ℝ) := by
  rw [probeIntegerTargetPrefix_tail_square hK]
  have he : Real.exp (-6 * probeSigma) = Real.exp (-3 * probeSigma) * Real.exp (-3 * probeSigma) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he]
  dsimp only [probeIntegerTailConstant]
  ring

theorem probeIntegerTargetPrefixL2_norm_sq_lower {K : ℕ} (hK : 1 ≤ K) :
    (probeIntegerTailConstant * Real.exp (-3 * probeSigma)) * (K : ℝ) ≤
      ‖probeIntegerTargetPrefixL2 K‖ ^ 2 := by
  have hKpos : 0 < (K : ℝ) := by exact_mod_cast (show 0 < K by omega)
  have hi := setIntegral_le_integral (s := Ioi (Real.log K + 2 * probeSigma))
    (probeIntegerTargetPrefix_square_integrable K) (Filter.Eventually.of_forall (fun t => sq_nonneg _))
  rw [probeIntegerTargetPrefix_tail_square_paper hK,← probeIntegerTargetPrefixL2_norm_sq] at hi
  have hpoly : (K : ℝ) ≤ ((K : ℝ) + 1) ^ 2 / (K : ℝ) := by
    apply (le_div_iff₀ hKpos).mpr
    nlinarith
  have hc : 0 ≤ probeIntegerTailConstant * Real.exp (-3 * probeSigma) :=
    (mul_pos probeIntegerTailConstant_pos (Real.exp_pos _)).le
  calc
    _ ≤ (probeIntegerTailConstant * Real.exp (-3 * probeSigma)) *
        (((K : ℝ) + 1) ^ 2 / (K : ℝ)) := mul_le_mul_of_nonneg_left hpoly hc
    _ = probeIntegerTailConstant * Real.exp (-3 * probeSigma) * ((K : ℝ) + 1) ^ 2 / (K : ℝ) := by ring
    _ ≤ _ := hi

theorem probeIntegerTargetPrefixL2_norm_tendsto_atTop :
    Tendsto (fun K : ℕ => ‖probeIntegerTargetPrefixL2 K‖) atTop atTop := by
  have hc : 0 < probeIntegerTailConstant * Real.exp (-3 * probeSigma) :=
    mul_pos probeIntegerTailConstant_pos (Real.exp_pos _)
  have hlinear := tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hsq : Tendsto (fun K : ℕ => ‖probeIntegerTargetPrefixL2 K‖ ^ 2) atTop atTop := by
    have hbound : ∀ᶠ K : ℕ in atTop,
        (probeIntegerTailConstant * Real.exp (-3 * probeSigma)) * (K : ℝ) ≤
          ‖probeIntegerTargetPrefixL2 K‖ ^ 2 := by
      filter_upwards [eventually_ge_atTop (1 : ℕ)] with K hK
      exact probeIntegerTargetPrefixL2_norm_sq_lower hK
    exact tendsto_atTop_mono' atTop hbound hlinear
  have h := Real.tendsto_sqrt_atTop.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq (norm_nonneg _)] using h

theorem probeIntegerTargetPrefix_causal (K : ℕ) {t : ℝ} (ht : t < 0) :
    probeIntegerTargetPrefix K t = 0 := by
  apply Finset.sum_eq_zero
  intro n _hn
  by_cases hn0 : n = 0
  · subst n
    simp [CCM.nativeIntegerCoefficient]
  · rw [probeV_zero_of_neg (by linarith [probe_log_nonneg hn0]),mul_zero]

theorem probeIntegerTargetPrefix_eq_actual_history (t : ℝ) {K : ℕ}
    (hK : ⌊Real.exp t⌋₊ ≤ K) : probeIntegerTargetPrefix K t = probeW t := by
  rw [native_probe_integer_action]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hK 1))
  intro n _hn hnsmall
  have hnlarge : ⌊Real.exp t⌋₊ + 1 ≤ n := by
    simpa only [Finset.mem_range,not_lt] using hnsmall
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hfloor : Real.exp t < ((⌊Real.exp t⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using Nat.lt_floor_add_one (Real.exp t)
  have hexp : Real.exp t < (n : ℝ) := hfloor.trans_le (by exact_mod_cast hnlarge)
  have hbefore : t < Real.log n := by
    calc
      t = Real.log (Real.exp t) := (Real.log_exp t).symm
      _ < Real.log n := Real.log_lt_log (Real.exp_pos t) hexp
  rw [probeV_zero_of_neg (by linarith),mul_zero]

/-- Pointwise eventual agreement coexists with divergent global L2 norms;
the escaping integer-history tail cannot be discarded. -/
theorem probeIntegerTargetPrefix_tendsto_pointwise (t : ℝ) :
    Tendsto (fun K : ℕ => probeIntegerTargetPrefix K t) atTop (𝓝 (probeW t)) := by
  have heq : (fun K : ℕ => probeIntegerTargetPrefix K t) =ᶠ[atTop] (fun _K : ℕ => probeW t) := by
    filter_upwards [eventually_ge_atTop (⌊Real.exp t⌋₊)] with K hK
    exact probeIntegerTargetPrefix_eq_actual_history t hK
  exact tendsto_const_nhds.congr' heq.symm

/-- The fixed tail constant agrees with the original, undelayed source
normalization. The two copies of the translation exponential cancel. -/
theorem probeIntegerTailConstant_eq_original :
    probeIntegerTailConstant = ‖2 * CCM.nativeOriginalSourceLaplace (-3 / 2 : ℂ)‖ ^ 2 / 12 := by
  have he : ‖Complex.exp (-(-3 / 2 : ℂ) * (probeSigma : ℂ))‖ ^ 2 *
      Real.exp (-3 * probeSigma) = 1 := by
    rw [Complex.norm_exp,pow_two,← Real.exp_add,← Real.exp_add]
    have harg : (-(-3 / 2 : ℂ) * (probeSigma : ℂ)).re +
        (-(-3 / 2 : ℂ) * (probeSigma : ℂ)).re + -3 * probeSigma = 0 := by
      norm_num [Complex.mul_re]
      ring
    rw [harg,Real.exp_zero]
  dsimp only [probeIntegerTailConstant,probeNativeTailAmplitude]
  rw [JPlus_eq_delay]
  calc
    _ = (‖2 * CCM.nativeOriginalSourceLaplace (-3 / 2 : ℂ)‖ ^ 2 / 12) *
        (‖Complex.exp (-(-3 / 2 : ℂ) * (probeSigma : ℂ))‖ ^ 2 * Real.exp (-3 * probeSigma)) := by
      simp only [norm_mul,mul_pow]
      ring
    _ = _ := by rw [he,mul_one]

/-- P14: integer truncation has an escaping exact tail, whereas physical
kernel truncation has a decaying operator error. Both use the actual source. -/
theorem integer_partial_divergence_and_safe_cutoff :
    0 < probeIntegerTailConstant ∧
    (∀ K : ℕ, 1 ≤ K →
      (∫ t : ℝ in Ioi (Real.log K + 2 * probeSigma), ‖probeIntegerTargetPrefix K t‖ ^ 2) =
        probeIntegerTailConstant * Real.exp (-3 * probeSigma) * ((K : ℝ) + 1) ^ 2 / (K : ℝ)) ∧
    Tendsto (fun K : ℕ => ‖probeIntegerTargetPrefixL2 K‖) atTop atTop ∧
    (∀ T : ℝ, ‖(probeCompletedSource : ProbeL2) -
      kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T)
        (probeSource : ProbeL2)‖ ≤ 2 * Real.exp (-T / 2) * ‖probeSource‖) ∧
    (∀ T : ℝ, ∀ f g : ProbeL2,
      ‖inner ℂ (CCM.nativeDampedCompletionL2Operator 0 (le_rfl) f)
          (CCM.nativeDampedCompletionL2Operator 0 (le_rfl) g) -
        inner ℂ (kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T) f)
          (kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T) g)‖ ≤
        (2 * Real.exp (-T / 2) * ‖f‖) * ‖CCM.nativeDampedCompletionL2Operator 0 (le_rfl) g‖ +
          ‖kernelL2Operator (probeFloorKernelCutoff T) (probeFloorKernelCutoff_integrable T) f‖ *
            (2 * Real.exp (-T / 2) * ‖g‖)) :=
  ⟨probeIntegerTailConstant_pos,fun _ hK => probeIntegerTargetPrefix_tail_square_paper hK,
    probeIntegerTargetPrefixL2_norm_tendsto_atTop,native_probe_source_physical_cutoff_bound,
    native_floor_cutoff_gram_bound⟩

/-! S01a/b: actual-source isolated pulses and squarefree omission bounds.
The separation constant is confined to indices 1 through 2047. -/


def probePulseLength : ℝ := 2 * probeSigma

theorem probePulseLength_pos : 0 < probePulseLength := mul_pos (by norm_num) probeSigma_pos

theorem probeV_first_half : deriv (probeLaplace probeV) (1 / 2 : ℂ) = 0 := by
  have hR : AnalyticAt ℂ CCM.nativeCompletionRationalMultiplier (1 / 2 : ℂ) := by
    unfold CCM.nativeCompletionRationalMultiplier
    exact (analyticAt_id.sub analyticAt_const).div
      ((analyticAt_id.add analyticAt_const).mul (analyticAt_id.add analyticAt_const)) (by norm_num)
  have heq : probeLaplace probeV =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun z => CCM.nativeCompletionRationalMultiplier z * JPlus z := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
      (by norm_num : 0 < (1 / 2 : ℂ).re)] with z hz
    exact probeV_laplace hz.le
  rw [heq.deriv_eq,deriv_fun_mul hR.differentiableAt (JPlus_analyticAt _).differentiableAt,JPlus_half]
  norm_num [CCM.nativeCompletionRationalMultiplier]

theorem probeTarget_half_moments :
    CCM.nativeCausalLaplaceMoment (1 / 2 : ℂ) 0 (probeTarget : ProbeL2) = 0 ∧
      CCM.nativeCausalLaplaceMoment (1 / 2 : ℂ) 1 (probeTarget : ProbeL2) = 0 := by
  have hp : 0 < (1 / 2 : ℂ).re := by norm_num
  constructor
  · rw [probeTarget_laplace_eq_physical,probeV_laplace hp.le,JPlus_half,mul_zero]
  · have hF : (fun z : ℂ => CCM.nativeCausalLaplaceMoment z 0 (probeTarget : ProbeL2)) =
        probeLaplace probeV := funext probeTarget_laplace_eq_physical
    have h := CCM.nativeCausalLaplaceMoment_iteratedDeriv (1 / 2 : ℂ) hp 1 probeTarget
    rw [hF,iteratedDeriv_one,probeV_first_half] at h
    norm_num only [pow_one,neg_one_mul] at h
    exact neg_eq_zero.mp h.symm

def probePulseWeightMass : ℝ := ∫ u : ℝ in Icc 0 probePulseLength, Real.exp (-2 * u)

def probePulseFirstWeightMoment : ℝ :=
  ∫ u : ℝ in Icc 0 probePulseLength, u * Real.exp (-2 * u)

def probePulseCenter : ℝ := probePulseFirstWeightMoment / probePulseWeightMass

theorem probePulseWeight_integrable :
    IntegrableOn (fun u : ℝ => Real.exp (-2 * u)) (Icc 0 probePulseLength) :=
  (by fun_prop : Continuous (fun u : ℝ => Real.exp (-2 * u))).integrableOn_Icc

theorem probePulseFirstWeight_integrable :
    IntegrableOn (fun u : ℝ => u * Real.exp (-2 * u)) (Icc 0 probePulseLength) :=
  (by fun_prop : Continuous (fun u : ℝ => u * Real.exp (-2 * u))).integrableOn_Icc

theorem probePulseWeightMass_pos : 0 < probePulseWeightMass := by
  letI : NeZero (volume (Icc (0 : ℝ) probePulseLength)) := ⟨by
    rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by simpa using probePulseLength_pos))⟩
  exact integral_exp_pos probePulseWeight_integrable

theorem probePulseCenter_mem : probePulseCenter ∈ Icc 0 probePulseLength := by
  have hnum0 : 0 ≤ probePulseFirstWeightMoment := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact mul_nonneg hu.1 (Real.exp_pos _).le
  have hnum : probePulseFirstWeightMoment ≤ probePulseLength * probePulseWeightMass := by
    have h := integral_mono_ae probePulseFirstWeight_integrable
      (probePulseWeight_integrable.const_mul probePulseLength) ?_
    · simpa only [probePulseFirstWeightMoment,probePulseWeightMass,integral_const_mul] using h
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      exact mul_le_mul_of_nonneg_right hu.2 (Real.exp_pos _).le
  exact ⟨div_nonneg hnum0 probePulseWeightMass_pos.le,
    (div_le_iff₀ probePulseWeightMass_pos).mpr hnum⟩

theorem probePulse_tail_orthogonal :
    (∫ u : ℝ in Icc 0 probePulseLength,
      Real.exp (-u / 2) * (u - probePulseCenter) * Real.exp (-3 * u / 2)) = 0 := by
  have hp (u : ℝ) : Real.exp (-u / 2) * (u - probePulseCenter) * Real.exp (-3 * u / 2) =
      u * Real.exp (-2 * u) - probePulseCenter * Real.exp (-2 * u) := by
    have he : Real.exp (-u / 2) * Real.exp (-3 * u / 2) = Real.exp (-2 * u) := by
      rw [← Real.exp_add]
      congr 1
      ring
    calc
      _ = (u - probePulseCenter) * (Real.exp (-u / 2) * Real.exp (-3 * u / 2)) := by ring
      _ = _ := by rw [he]; ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hp),
    integral_sub probePulseFirstWeight_integrable (probePulseWeight_integrable.const_mul probePulseCenter),
    integral_const_mul]
  change probePulseFirstWeightMoment - probePulseCenter * probePulseWeightMass = 0
  rw [probePulseCenter,div_mul_cancel₀ _ probePulseWeightMass_pos.ne',sub_self]

def probePulseProfile (t : ℝ) : ℂ := (Icc (0 : ℝ) probePulseLength).indicator
  (fun u : ℝ => ((Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) : ℂ)) t

theorem probePulseProfile_hasCompactSupport : HasCompactSupport probePulseProfile := by
  apply HasCompactSupport.intro (K := Icc (0 : ℝ) probePulseLength) isCompact_Icc
  intro t ht
  simp [probePulseProfile,ht]

theorem probePulseProfile_bound (t : ℝ) : ‖probePulseProfile t‖ ≤ probePulseLength := by
  by_cases ht : t ∈ Icc 0 probePulseLength
  · rw [probePulseProfile,indicator_of_mem ht,Complex.norm_real,Real.norm_eq_abs,abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [ht.1])
    have hd : |t - probePulseCenter| ≤ probePulseLength := by
      rw [abs_le]
      constructor <;> linarith [ht.1,ht.2,probePulseCenter_mem.1,probePulseCenter_mem.2]
    calc
      _ ≤ 1 * probePulseLength := mul_le_mul he hd (abs_nonneg _) (by norm_num)
      _ = _ := one_mul _
  · simp [probePulseProfile,ht,probePulseLength_pos.le]

theorem probePulseProfile_memLp : MemLp probePulseProfile 2 volume := by
  have hc : Continuous (fun u : ℝ => ((Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) : ℂ)) := by fun_prop
  apply probePulseProfile_hasCompactSupport.memLp_of_bound
    (hc.aestronglyMeasurable.indicator measurableSet_Icc) probePulseLength
  exact Filter.Eventually.of_forall probePulseProfile_bound

def probePulseL2 : ProbeL2 := probePulseProfile_memLp.toLp probePulseProfile

theorem probePulseL2_coeFn : probePulseL2 =ᵐ[volume] probePulseProfile := probePulseProfile_memLp.coeFn_toLp

theorem probePulseL2_norm_sq : ‖probePulseL2‖ ^ 2 =
    ∫ u : ℝ in Icc 0 probePulseLength, Real.exp (-u) * (u - probePulseCenter) ^ 2 := by
  rw [OPICAFollowup.L2_norm_sq_eq_integral]
  have hrep : (fun u : ℝ => ‖probePulseL2 u‖ ^ 2) =ᵐ[volume]
      fun u : ℝ => ‖probePulseProfile u‖ ^ 2 := by
    filter_upwards [probePulseL2_coeFn] with u hu
    rw [hu]
  rw [integral_congr_ae hrep]
  have hp : (fun u : ℝ => ‖probePulseProfile u‖ ^ 2) =
      (Icc (0 : ℝ) probePulseLength).indicator
        (fun u : ℝ => Real.exp (-u) * (u - probePulseCenter) ^ 2) := by
    funext u
    by_cases hu : u ∈ Icc 0 probePulseLength
    · have he : Real.exp (-u / 2) ^ 2 = Real.exp (-u) := by
        rw [pow_two,← Real.exp_add]
        congr 1
        ring
      simp only [probePulseProfile,indicator_of_mem hu,Complex.norm_real,Real.norm_eq_abs,
        sq_abs,mul_pow,he]
    · simp [probePulseProfile,hu]
  rw [hp,integral_indicator measurableSet_Icc]

theorem probePulse_polynomial_integral :
    (∫ u : ℝ in Icc 0 probePulseLength, (u - probePulseCenter) ^ 2) =
      probePulseLength ^ 3 / 3 - probePulseCenter * probePulseLength ^ 2 +
        probePulseCenter ^ 2 * probePulseLength := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le probePulseLength_pos.le]
  have heq : (fun u : ℝ => (u - probePulseCenter) ^ 2) =
      fun u : ℝ => u ^ 2 - (2 * probePulseCenter) * u + probePulseCenter ^ 2 := by
    funext u
    ring
  have h2 : IntervalIntegrable (fun u : ℝ => u ^ 2) volume 0 probePulseLength :=
    (by fun_prop : Continuous (fun u : ℝ => u ^ 2)).intervalIntegrable _ _
  have h1 : IntervalIntegrable (fun u : ℝ => (2 * probePulseCenter) * u) volume 0 probePulseLength :=
    (by fun_prop : Continuous (fun u : ℝ => (2 * probePulseCenter) * u)).intervalIntegrable _ _
  have h0 : IntervalIntegrable (fun _u : ℝ => probePulseCenter ^ 2) volume 0 probePulseLength :=
    continuous_const.intervalIntegrable _ _
  rw [heq,intervalIntegral.integral_add (h2.sub h1) h0,
    intervalIntegral.integral_sub h2 h1,intervalIntegral.integral_const_mul,
    integral_pow,integral_id,intervalIntegral.integral_const]
  norm_num
  ring

theorem probePulseL2_norm_sq_upper : ‖probePulseL2‖ ^ 2 ≤ probePulseLength ^ 3 / 3 := by
  rw [probePulseL2_norm_sq]
  have hi : (∫ u : ℝ in Icc 0 probePulseLength, Real.exp (-u) * (u - probePulseCenter) ^ 2) ≤
      ∫ u : ℝ in Icc 0 probePulseLength, (u - probePulseCenter) ^ 2 := by
    apply integral_mono_ae
      (by fun_prop : Continuous (fun u : ℝ => Real.exp (-u) * (u - probePulseCenter) ^ 2)).integrableOn_Icc
      (by fun_prop : Continuous (fun u : ℝ => (u - probePulseCenter) ^ 2)).integrableOn_Icc
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have he : Real.exp (-u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hu.1])
    simpa only [one_mul] using mul_le_mul_of_nonneg_right he (sq_nonneg _)
  apply hi.trans
  rw [probePulse_polynomial_integral]
  have hnonneg : 0 ≤ probePulseLength * probePulseCenter * (probePulseLength - probePulseCenter) :=
    mul_nonneg (mul_nonneg probePulseLength_pos.le probePulseCenter_mem.1)
      (sub_nonneg.mpr probePulseCenter_mem.2)
  nlinarith

theorem affine_exponential_tail_integral (L c : ℝ) :
    (∫ u : ℝ in Ioi L, (u - c) * Real.exp (-2 * u)) =
      Real.exp (-2 * L) * ((L - c) / 2 + 1 / 4) := by
  have hG2 : Real.Gamma (2 : ℝ) = 1 := by simpa using Real.Gamma_nat_eq_factorial 1
  have hbase : (∫ x : ℝ in Ioi 0, x * Real.exp (-2 * x)) = (1 / 4 : ℝ) := by
    have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1) (b := 2)
      (by norm_num) (by norm_num) (by norm_num)
    norm_num [hG2] at h
    simpa only [neg_mul] using h
  have hi1 : IntegrableOn (fun x : ℝ => x * Real.exp (-2 * x)) (Ioi 0) := by
    simpa only [Real.rpow_one,neg_mul] using integrableOn_rpow_mul_exp_neg_mul_rpow
      (p := 1) (s := 1) (b := 2) (by norm_num) (by norm_num) (by norm_num)
  have hi0 : IntegrableOn (fun x : ℝ => Real.exp (-2 * x)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0
  let H : ℝ → ℝ := (Ioi (0 : ℝ)).indicator
    (fun x => x * Real.exp (-2 * x) + (L - c) * Real.exp (-2 * x))
  have hp : (Ioi L).indicator (fun u : ℝ => (u - c) * Real.exp (-2 * u)) =
      fun u : ℝ => Real.exp (-2 * L) * H (u - L) := by
    funext u
    by_cases hu : L < u
    · have hu0 : 0 < u - L := by linarith
      change u ∈ Ioi L at hu
      change u - L ∈ Ioi (0 : ℝ) at hu0
      rw [indicator_of_mem hu]
      dsimp only [H]
      rw [indicator_of_mem hu0]
      rw [show -2 * u = -2 * L + -2 * (u - L) by ring,Real.exp_add]
      ring
    · have hu0 : ¬0 < u - L := by linarith
      simp [H,hu,hu0]
  rw [← integral_indicator measurableSet_Ioi,hp,integral_const_mul,integral_sub_right_eq_self]
  dsimp only [H]
  rw [integral_indicator measurableSet_Ioi,integral_add hi1 (hi0.const_mul (L-c)),
    integral_const_mul,hbase,integral_exp_mul_Ioi (by norm_num : (-2 : ℝ) < 0) 0]
  norm_num
  ring


theorem probePulse_pairing :
    inner ℂ probePulseL2 (probeTarget : ProbeL2) =
      -probeNativeTailAmplitude * (Real.exp (-2 * probePulseLength) *
        ((probePulseLength - probePulseCenter) / 2 + 1 / 4) : ℝ) := by
  let H : ℝ → ℂ := fun u =>
    (Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) * probeV u
  let M (k : ℕ) : ℝ → ℂ := fun u =>
    (u : ℂ) ^ k * Complex.exp (-(1 / 2 : ℂ) * (u : ℂ)) *
      (probeTarget : ProbeL2) u
  have hM (k : ℕ) : Integrable (M k) :=
    CCM.nativeCausalLaplaceMoment_integrable (1 / 2 : ℂ) (by norm_num) k probeTarget
  have he (u : ℝ) : Complex.exp (-(1 / 2 : ℂ) * (u : ℂ)) =
      (Real.exp (-u / 2) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hrep : (fun u => M 1 u - (probePulseCenter : ℂ) * M 0 u) =ᵐ[volume] H := by
    filter_upwards [probeTarget_coeFn] with u hu
    dsimp only [M,H]
    rw [hu,he]
    push_cast
    ring
  have hiH : Integrable H := ((hM 1).sub ((hM 0).const_mul _)).congr hrep
  have hz : (∫ u : ℝ, H u) = 0 := by
    rw [← integral_congr_ae hrep,integral_sub (hM 1) ((hM 0).const_mul _),integral_const_mul]
    change CCM.nativeCausalLaplaceMoment (1 / 2 : ℂ) 1 (probeTarget : ProbeL2) -
      (probePulseCenter : ℂ) * CCM.nativeCausalLaplaceMoment (1 / 2 : ℂ) 0
        (probeTarget : ProbeL2) = 0
    rw [probeTarget_half_moments.1,probeTarget_half_moments.2,mul_zero,sub_self]
  have hhead : inner ℂ probePulseL2 (probeTarget : ProbeL2) =
      ∫ u : ℝ in Icc 0 probePulseLength, H u := by
    rw [L2.inner_def,← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    filter_upwards [probePulseL2_coeFn,probeTarget_coeFn] with u hp hv
    rw [hp,hv,RCLike.inner_apply']
    by_cases hu : u ∈ Icc 0 probePulseLength
    · simp only [probePulseProfile,indicator_of_mem hu,Complex.conj_ofReal]
      rfl
    · simp [probePulseProfile,hu]
  have htailset : (∫ u : ℝ in (Icc 0 probePulseLength)ᶜ, H u) =
      ∫ u : ℝ in Ioi probePulseLength, H u := by
    rw [← integral_indicator measurableSet_Icc.compl,← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro u
    by_cases hneg : u < 0
    · have hnot : u ∉ Ioi probePulseLength := by
        simp only [Set.mem_Ioi,not_lt]
        linarith [probePulseLength_pos]
      simp [H,probeV_zero_of_neg hneg,hnot]
    · have h0 : 0 ≤ u := le_of_not_gt hneg
      by_cases hu : u ≤ probePulseLength
      · simp [h0,hu,show ¬probePulseLength < u by linarith]
      · have hgt : probePulseLength < u := lt_of_not_ge hu
        simp [h0,hu,hgt]
  have htail : (∫ u : ℝ in Ioi probePulseLength, H u) =
      probeNativeTailAmplitude * (Real.exp (-2 * probePulseLength) *
        ((probePulseLength - probePulseCenter) / 2 + 1 / 4) : ℝ) := by
    have heq : (fun u : ℝ => H u) =ᵐ[volume.restrict (Ioi probePulseLength)]
        fun u : ℝ => probeNativeTailAmplitude *
          ((u - probePulseCenter) * Real.exp (-2 * u) : ℝ) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      dsimp only [H]
      rw [probeV_tail (show 2 * probeSigma ≤ u from hu.le)]
      have h3 : Complex.exp (-(3 / 2 : ℂ) * (u : ℂ)) =
          (Real.exp (-3 * u / 2) : ℂ) := by
        rw [Complex.ofReal_exp]
        congr 1
        push_cast
        ring
      rw [h3]
      have hprod : Real.exp (-u / 2) * Real.exp (-3 * u / 2) = Real.exp (-2 * u) := by
        rw [← Real.exp_add]
        congr 1
        ring
      dsimp only [probeNativeTailAmplitude]
      push_cast
      calc
        _ = (2 * JPlus (-3 / 2)) * ((u - probePulseCenter) : ℂ) *
            ((Real.exp (-u / 2) * Real.exp (-3 * u / 2) : ℝ) : ℂ) := by push_cast; ring
        _ = _ := by rw [hprod]; push_cast; ring
    rw [integral_congr_ae heq,integral_const_mul,integral_complex_ofReal,
      affine_exponential_tail_integral]
  have hs := integral_add_compl (s := Set.Icc (0 : ℝ) probePulseLength) measurableSet_Icc hiH
  rw [hz,htailset,htail,← hhead] at hs
  calc
    _ = -(probeNativeTailAmplitude * (Real.exp (-2 * probePulseLength) *
      ((probePulseLength - probePulseCenter) / 2 + 1 / 4) : ℝ)) := eq_neg_of_add_eq_zero_left hs
    _ = _ := by ring

theorem probePulse_pairing_norm_lower :
    2 * Real.exp (-2 * probePulseLength) ≤
      ‖inner ℂ probePulseL2 (probeTarget : ProbeL2)‖ := by
  have hb : (1 / 4 : ℝ) ≤ (probePulseLength - probePulseCenter) / 2 + 1 / 4 := by
    linarith [probePulseCenter_mem.2]
  have hp : 0 < Real.exp (-2 * probePulseLength) *
      ((probePulseLength - probePulseCenter) / 2 + 1 / 4) :=
    mul_pos (Real.exp_pos _) (lt_of_lt_of_le (by norm_num) hb)
  rw [probePulse_pairing,norm_mul,norm_neg,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hp]
  nlinarith [mul_le_mul_of_nonneg_left hb (Real.exp_pos (-2 * probePulseLength)).le,
    mul_le_mul_of_nonneg_right probeNativeTailAmplitude_norm_lower hp.le]

theorem probePulseL2_ne_zero : probePulseL2 ≠ 0 := by
  intro h
  have hp := probePulse_pairing_norm_lower
  rw [h,inner_zero_left,norm_zero] at hp
  exact (mul_pos (by norm_num : (0 : ℝ) < 2) (Real.exp_pos _)).not_ge hp

def probePulseSeparation : ℝ :=
  ‖inner ℂ probePulseL2 (probeTarget : ProbeL2)‖ ^ 2 / ‖probePulseL2‖ ^ 2

theorem probePulseSeparation_lower :
    12 * Real.exp (-4 * probePulseLength) / probePulseLength ^ 3 ≤ probePulseSeparation := by
  have hn : 0 < ‖probePulseL2‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr probePulseL2_ne_zero)
  have hl : 0 < probePulseLength ^ 3 := pow_pos probePulseLength_pos _
  have he : Real.exp (-2 * probePulseLength) ^ 2 = Real.exp (-4 * probePulseLength) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hb : 4 * Real.exp (-4 * probePulseLength) ≤
      ‖inner ℂ probePulseL2 (probeTarget : ProbeL2)‖ ^ 2 := by
    have hs := sq_le_sq₀ (mul_pos (by norm_num : (0 : ℝ) < 2)
      (Real.exp_pos (-2 * probePulseLength))).le
      (norm_nonneg (inner ℂ probePulseL2 (probeTarget : ProbeL2)))
    have hsq := hs.mpr probePulse_pairing_norm_lower
    nlinarith [he]
  unfold probePulseSeparation
  rw [div_le_div_iff₀ hl hn]
  nlinarith [mul_le_mul_of_nonneg_left probePulseL2_norm_sq_upper
    (show 0 ≤ 12 * Real.exp (-4 * probePulseLength) by positivity),
    mul_le_mul_of_nonneg_right hb hl.le]

theorem probePulseLength_eq : probePulseLength = 1 / 2048 := by
  norm_num [probePulseLength,probeSigma,CCM.UniversalSinc.fixedScale]

theorem probe_early_log_gap {k n : ℕ} (hk : 0 < k) (hkmax : k ≤ 2047)
    (hkn : k < n) : probePulseLength < Real.log (n : ℝ) - Real.log (k : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hnR : (k : ℝ) < n := by exact_mod_cast hkn
  have hratio : 1 < (n : ℝ) / k := (one_lt_div hkR).mpr hnR
  have hlog : 1 - (k : ℝ) / n < Real.log ((n : ℝ) / k) := by
    have h := Real.log_lt_sub_one_of_pos (inv_pos.mpr (lt_trans zero_lt_one hratio))
      (show ((n : ℝ) / k)⁻¹ ≠ 1 from inv_ne_one.mpr hratio.ne')
    rw [Real.log_inv,inv_div] at h
    linarith
  have hfrac : (1 / 2048 : ℝ) ≤ 1 - (k : ℝ) / n := by
    have hn : (0 : ℝ) < n := lt_trans hkR hnR
    rw [le_sub_iff_add_le,add_comm,← le_sub_iff_add_le,(div_le_iff₀ hn)]
    have hnat : (k : ℝ) + 1 ≤ n := by exact_mod_cast hkn
    have hmax : (k : ℝ) ≤ 2047 := by exact_mod_cast hkmax
    nlinarith
  rw [probePulseLength_eq,← Real.log_div (ne_of_gt (lt_trans hkR hnR)) hkR.ne']
  simpa only [inv_div] using lt_of_le_of_lt hfrac hlog

def probePulseVPair (s : ℝ) : ℂ := ∫ u : ℝ in Set.Icc 0 probePulseLength,
  ((Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) : ℂ) * probeV (u + s)

theorem probePulseVPair_zero : probePulseVPair 0 =
    inner ℂ probePulseL2 (probeTarget : ProbeL2) := by
  rw [probePulseVPair,L2.inner_def,← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards [probePulseL2_coeFn,probeTarget_coeFn] with u hp hv
  rw [hp,hv,RCLike.inner_apply']
  by_cases hu : u ∈ Set.Icc 0 probePulseLength
  · simp only [probePulseProfile,indicator_of_mem hu,Complex.conj_ofReal,add_zero]
  · simp [probePulseProfile,hu]

theorem probePulseVPair_eq_zero_of_tail {s : ℝ} (hs : probePulseLength ≤ s) :
    probePulseVPair s = 0 := by
  change 2 * probeSigma ≤ s at hs
  have heq : (fun u : ℝ =>
      ((Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) : ℂ) * probeV (u + s))
      =ᵐ[volume.restrict (Set.Icc 0 probePulseLength)] fun u : ℝ =>
        (probeNativeTailAmplitude * Complex.exp (-(3 / 2 : ℂ) * (s : ℂ))) *
          ((Real.exp (-u / 2) * (u - probePulseCenter) * Real.exp (-3 * u / 2) : ℝ) : ℂ) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    rw [probeV_tail (show 2 * probeSigma ≤ u + s by linarith [hu.1])]
    have he : Complex.exp (-(3 / 2 : ℂ) * ((u + s : ℝ) : ℂ)) =
        Complex.exp (-(3 / 2 : ℂ) * (s : ℂ)) * (Real.exp (-3 * u / 2) : ℂ) := by
      rw [Complex.ofReal_exp,← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [he]
    dsimp only [probeNativeTailAmplitude]
    push_cast
    ring
  rw [probePulseVPair,integral_congr_ae heq,integral_const_mul,
    integral_complex_ofReal,probePulse_tail_orthogonal,Complex.ofReal_zero,mul_zero]

theorem probePulseVPair_eq_zero_of_before {s : ℝ} (hs : s < -probePulseLength) :
    probePulseVPair s = 0 := by
  apply setIntegral_eq_zero_of_forall_eq_zero
  intro u hu
  rw [probeV_zero_of_neg (show u + s < 0 by linarith [hu.2]),mul_zero]

theorem probePulseVPair_integer_isolation {k q : ℕ} (hk : 0 < k) (hmax : k ≤ 2047)
    (hq : 0 < q) : probePulseVPair (Real.log k - Real.log q) =
      if q = k then inner ℂ probePulseL2 (probeTarget : ProbeL2) else 0 := by
  split_ifs with heq
  · subst q
    rw [sub_self,probePulseVPair_zero]
  · rcases lt_or_gt_of_ne heq with hlt | hgt
    · exact probePulseVPair_eq_zero_of_tail
        (probe_early_log_gap hq (le_trans hlt.le hmax) hlt).le
    · exact probePulseVPair_eq_zero_of_before (by
        have h := probe_early_log_gap hk hmax hgt
        linarith)

def probePulseWPair (s : ℝ) : ℂ := ∫ u : ℝ in Set.Icc 0 probePulseLength,
  ((Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) : ℂ) * probeW (u + s)

theorem probeW_history_before_next (K : ℕ) {t : ℝ} (ht : t < Real.log (K + 1 : ℕ)) :
    probeW t = probeIntegerTargetPrefix K t := by
  symm
  apply probeIntegerTargetPrefix_eq_actual_history
  have hfloor : ⌊Real.exp t⌋₊ < K + 1 := (Nat.floor_lt (Real.exp_pos t).le).mpr (by
    calc
      Real.exp t < Real.exp (Real.log ((K + 1 : ℕ) : ℝ)) := Real.exp_lt_exp.mpr ht
      _ = _ := Real.exp_log (by positivity))
  omega

theorem probePulseWPair_integer_history {k n : ℕ} (hk : 0 < k) (hmax : k ≤ 2047)
    (hn : 0 < n) : probePulseWPair (Real.log k - Real.log n) =
      ∑ m ∈ Finset.range (k + 1), (CCM.nativeIntegerCoefficient m : ℂ) *
        probePulseVPair (Real.log k - Real.log n - Real.log m) := by
  have hcV : Continuous probeV := probeV_contDiff.continuous
  have heq : (fun u : ℝ =>
      ((Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) : ℂ) *
        probeW (u + (Real.log k - Real.log n))) =ᵐ[volume.restrict (Set.Icc 0 probePulseLength)]
        fun u : ℝ => ∑ m ∈ Finset.range (k + 1),
          ((Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) : ℂ) *
            ((CCM.nativeIntegerCoefficient m : ℂ) *
              probeV (u + (Real.log k - Real.log n - Real.log m))) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have hbefore : u + (Real.log k - Real.log n) < Real.log (k + 1 : ℕ) := by
      have hgap := probe_early_log_gap hk hmax (Nat.lt_succ_self k)
      have hlogn := probe_log_nonneg (Nat.ne_of_gt hn)
      linarith [hu.2]
    rw [probeW_history_before_next k hbefore,probeIntegerTargetPrefix,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _hm
    congr 2
    congr 1
    ring
  rw [probePulseWPair,integral_congr_ae heq,
    integral_finsetSum _ (fun m _hm => (by fun_prop : Continuous (fun u : ℝ =>
      ((Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) : ℂ) *
        ((CCM.nativeIntegerCoefficient m : ℂ) *
          probeV (u + (Real.log k - Real.log n - Real.log m))))).integrableOn_Icc)]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [probePulseVPair,← integral_const_mul]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  ring

theorem probeIntegerCoefficient_mul (n m : ℕ) :
    CCM.nativeIntegerCoefficient n * CCM.nativeIntegerCoefficient m =
      CCM.nativeIntegerCoefficient (n * m) := by
  simp only [CCM.nativeIntegerCoefficient,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg n)]
  ring

theorem probePulseWPair_integer_isolation {k n : ℕ} (hk : 0 < k) (hmax : k ≤ 2047)
    (hn : 0 < n) : (CCM.nativeIntegerCoefficient n : ℂ) *
      probePulseWPair (Real.log k - Real.log n) =
      ∑ m ∈ Finset.range (k + 1), if n * m = k then
        (CCM.nativeIntegerCoefficient k : ℂ) * inner ℂ probePulseL2 (probeTarget : ProbeL2)
      else 0 := by
  rw [probePulseWPair_integer_history hk hmax hn,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  by_cases hm : m = 0
  · subst m
    simp [CCM.nativeIntegerCoefficient,Nat.ne_of_gt hk,(Nat.ne_of_gt hk).symm]
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hlog : Real.log k - Real.log n - Real.log m = Real.log k - Real.log (n * m : ℕ) := by
      rw [Nat.cast_mul,Real.log_mul (by positivity : (n : ℝ) ≠ 0) (by positivity : (m : ℝ) ≠ 0)]
      ring
    rw [hlog,probePulseVPair_integer_isolation hk hmax (Nat.mul_pos hn hmpos)]
    by_cases hnm : n * m = k
    · rw [if_pos hnm,if_pos hnm]
      rw [← mul_assoc,← Complex.ofReal_mul,probeIntegerCoefficient_mul,hnm]
    · rw [if_neg hnm,if_neg hnm,mul_zero,mul_zero]

theorem probePulseWPair_divisor {k n : ℕ} (hk : 0 < k) (hmax : k ≤ 2047)
    (hn : 0 < n) : (CCM.nativeIntegerCoefficient n : ℂ) *
      probePulseWPair (Real.log k - Real.log n) =
      if n ∣ k then (CCM.nativeIntegerCoefficient k : ℂ) *
        inner ℂ probePulseL2 (probeTarget : ProbeL2) else 0 := by
  classical
  rw [probePulseWPair_integer_isolation hk hmax hn]
  by_cases hd : n ∣ k
  · rw [if_pos hd]
    have hmul : n * (k / n) = k := Nat.mul_div_cancel' hd
    rw [Finset.sum_eq_single_of_mem (k / n) (show k / n ∈ Finset.range (k + 1) from
      Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_self k n)))]
    · rw [if_pos hmul]
    · intro m _hm hmne
      apply if_neg
      intro heq
      exact hmne (mul_left_cancel₀ (Nat.ne_of_gt hn) (heq.trans hmul.symm))
  · rw [if_neg hd]
    apply Finset.sum_eq_zero
    intro m _hm
    exact if_neg (fun h => hd ⟨m,h.symm⟩)

def probePulseShift (s : ℝ) : ProbeL2 := CCM.nativeCompletionL2Delay s probePulseL2

theorem probePulseShift_coeFn (s : ℝ) :
    probePulseShift s =ᵐ[volume] fun t : ℝ => probePulseProfile (t - s) := by
  have hs := (measurePreserving_sub_right volume s).quasiMeasurePreserving.ae_eq probePulseL2_coeFn
  filter_upwards [CCM.nativeCompletionL2Delay_coeFn s probePulseL2,hs] with t hd hp
  exact hd.trans hp

theorem probePulseShift_norm (s : ℝ) : ‖probePulseShift s‖ = ‖probePulseL2‖ :=
  CCM.nativeCompletionL2Delay_norm s probePulseL2

theorem probePulseShift_inner (s : ℝ) (f : ProbeL2) (F : ℝ → ℂ)
    (hf : f =ᵐ[volume] F) : inner ℂ (probePulseShift s) f =
      ∫ u : ℝ in Set.Icc 0 probePulseLength,
        ((Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) : ℂ) * F (u + s) := by
  have heq : (fun t : ℝ => inner ℂ (probePulseShift s t) (f t)) =ᵐ[volume]
      fun t : ℝ => conj (probePulseProfile (t - s)) * F t := by
    filter_upwards [probePulseShift_coeFn s,hf] with t hp hft
    rw [hp,hft,RCLike.inner_apply']
  rw [L2.inner_def,integral_congr_ae heq]
  have ht := integral_add_right_eq_self (fun t : ℝ => conj (probePulseProfile (t - s)) * F t) s
    (μ := (volume : Measure ℝ))
  rw [← ht,← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro u
  simp only [add_sub_cancel_right]
  by_cases hu : u ∈ Set.Icc 0 probePulseLength
  · simp only [probePulseProfile,indicator_of_mem hu,Complex.conj_ofReal]
  · simp [probePulseProfile,hu]

theorem probePulseShift_target {k : ℕ} (hk : 0 < k) (hmax : k ≤ 2047) :
    inner ℂ (probePulseShift (Real.log k)) (probeTarget : ProbeL2) =
      if k = 1 then inner ℂ probePulseL2 (probeTarget : ProbeL2) else 0 := by
  rw [probePulseShift_inner _ _ _ probeTarget_coeFn]
  have h := probePulseVPair_integer_isolation hk hmax (by norm_num : 0 < 1)
  simpa only [probePulseVPair,Nat.cast_one,Real.log_one,sub_zero,eq_comm] using h

theorem probePulseShift_column {k n : ℕ} (hk : 0 < k) (hmax : k ≤ 2047)
    (hn : 0 < n) : inner ℂ (probePulseShift (Real.log k)) (probeColumn n : ProbeL2) =
      if n ∣ k then (CCM.nativeIntegerCoefficient k : ℂ) *
        inner ℂ probePulseL2 (probeTarget : ProbeL2) else 0 := by
  rw [probePulseShift_inner _ _ _ (probeColumn_coeFn (Nat.ne_of_gt hn))]
  have heq : (fun u : ℝ =>
      ((Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) : ℂ) *
        ((CCM.nativeIntegerCoefficient n : ℂ) * probeW (u + Real.log k - Real.log n))) =
      fun u : ℝ => (CCM.nativeIntegerCoefficient n : ℂ) *
        (((Real.exp (-u / 2) * (u - probePulseCenter) : ℝ) : ℂ) *
          probeW (u + (Real.log k - Real.log n))) := by
    funext u
    rw [show u + Real.log k - Real.log n = u + (Real.log k - Real.log n) by ring]
    ring
  rw [heq,integral_const_mul]
  exact probePulseWPair_divisor hk hmax hn

theorem probePulseShift_orthogonal {s t : ℝ} (hst : probePulseLength < t - s) :
    inner ℂ (probePulseShift s) (probePulseShift t) = 0 := by
  rw [L2.inner_def]
  apply integral_eq_zero_of_ae
  filter_upwards [probePulseShift_coeFn s,probePulseShift_coeFn t] with u hs ht
  rw [hs,ht,RCLike.inner_apply']
  by_cases hus : u - s ∈ Set.Icc 0 probePulseLength
  · have hut : u - t ∉ Set.Icc 0 probePulseLength := by
      intro hu
      linarith [hus.2,hu.1]
    simp [probePulseProfile,hut]
  · simp [probePulseProfile,hus]

def probeDivisorDefect (x : ℕ → ℂ) (k : ℕ) : ℂ :=
  (if k = 1 then 1 else 0) - ∑ n ∈ k.divisors, x n

def probeSparseOutput (x : ℕ →₀ ℂ) : ProbeL2 :=
  ∑ n ∈ x.support, x n • (probeColumn n : ProbeL2)

def probeSparseResidual (x : ℕ →₀ ℂ) : ProbeL2 := (probeTarget : ProbeL2) - probeSparseOutput x

theorem probeSparse_divisor_sum (x : ℕ →₀ ℂ) {k : ℕ} (hk : 0 < k) :
    (∑ n ∈ x.support.filter (fun n => n ∣ k), x n) = ∑ n ∈ k.divisors, x n := by
  apply Finset.sum_subset
    (show x.support.filter (fun n => n ∣ k) ⊆ k.divisors from fun n hn =>
      Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hn).2,Nat.ne_of_gt hk⟩)
  intro n hn hnnot
  apply Finsupp.notMem_support_iff.mp
  intro hns
  exact hnnot (Finset.mem_filter.mpr ⟨hns,(Nat.mem_divisors.mp hn).1⟩)

theorem probePulseShift_residual {k : ℕ} (hk : 0 < k) (hmax : k ≤ 2047)
    (x : ℕ →₀ ℂ) : inner ℂ (probePulseShift (Real.log k)) (probeSparseResidual x) =
      (CCM.nativeIntegerCoefficient k : ℂ) * inner ℂ probePulseL2 (probeTarget : ProbeL2) *
        probeDivisorDefect x k := by
  classical
  have hs : (∑ n ∈ x.support,
      x n * inner ℂ (probePulseShift (Real.log k)) (probeColumn n : ProbeL2)) =
      (∑ n ∈ k.divisors, x n) * ((CCM.nativeIntegerCoefficient k : ℂ) *
        inner ℂ probePulseL2 (probeTarget : ProbeL2)) := by
    rw [← probeSparse_divisor_sum x hk,Finset.sum_filter,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hn : n = 0
    · subst n
      simp [probeColumn_zero,Nat.ne_of_gt hk]
    · rw [probePulseShift_column hk hmax (Nat.pos_of_ne_zero hn)]
      split_ifs <;> simp
  rw [probeSparseResidual,inner_sub_right,probePulseShift_target hk hmax,
    probeSparseOutput,inner_sum]
  simp_rw [inner_smul_right]
  rw [hs]
  by_cases hk1 : k = 1
  · subst k
    norm_num only [CCM.nativeIntegerCoefficient,Nat.cast_one,Real.sqrt_one,div_one,
      Complex.ofReal_one,one_mul,if_pos rfl,probeDivisorDefect,ite_true]
    ring
  · rw [if_neg hk1,probeDivisorDefect,if_neg hk1]
    ring

def probePulseNormalized (k : ℕ) : ProbeL2 :=
  ((‖probePulseL2‖⁻¹ : ℝ) : ℂ) • probePulseShift (Real.log k)

theorem probePulseNormalized_orthonormal (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ k ≤ 2047) :
    Orthonormal ℂ (fun k : K => probePulseNormalized k) := by
  constructor
  · intro k
    change ‖probePulseNormalized (k : ℕ)‖ = 1
    dsimp only [probePulseNormalized]
    rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,
      abs_norm,probePulseShift_norm,inv_mul_cancel₀ (norm_ne_zero_iff.mpr probePulseL2_ne_zero)]
  · intro i j hij
    change inner ℂ (probePulseNormalized (i : ℕ)) (probePulseNormalized (j : ℕ)) = 0
    dsimp only [probePulseNormalized]
    rw [inner_smul_left,inner_smul_right]
    have hne : (i : ℕ) ≠ j := fun h => hij (Subtype.ext h)
    have horth : inner ℂ (probePulseShift (Real.log (i : ℕ)))
        (probePulseShift (Real.log (j : ℕ))) = 0 := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact probePulseShift_orthogonal
          (probe_early_log_gap (hK i i.property).1 (hK i i.property).2 hlt)
      · exact inner_eq_zero_symm.mp (probePulseShift_orthogonal
          (probe_early_log_gap (hK j j.property).1 (hK j j.property).2 hgt))
    rw [horth,mul_zero,mul_zero]

theorem probePulse_bessel (K : Finset ℕ) (hK : ∀ k ∈ K, 0 < k ∧ k ≤ 2047)
    (f : ProbeL2) :
    (∑ k ∈ K, ‖inner ℂ (probePulseShift (Real.log k)) f‖ ^ 2) ≤
      ‖probePulseL2‖ ^ 2 * ‖f‖ ^ 2 := by
  have hn : 0 < ‖probePulseL2‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr probePulseL2_ne_zero)
  have heach (k : K) : ‖inner ℂ (probePulseNormalized k) f‖ ^ 2 =
      ‖inner ℂ (probePulseShift (Real.log (k : ℕ))) f‖ ^ 2 / ‖probePulseL2‖ ^ 2 := by
    rw [probePulseNormalized,inner_smul_left,Complex.conj_ofReal,norm_mul,
      Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_norm,mul_pow,inv_pow]
    ring
  have hb := (probePulseNormalized_orthonormal K hK).sum_inner_products_le (s := Finset.univ) f
  simp_rw [heach] at hb
  rw [← Finset.sum_div,Finset.sum_coe_sort K
    (fun k : ℕ => ‖inner ℂ (probePulseShift (Real.log k)) f‖ ^ 2)] at hb
  have h := (div_le_iff₀ hn).mp hb
  simpa only [mul_comm] using h

theorem probeIntegerCoefficient_sq {k : ℕ} (hk : 0 < k) :
    CCM.nativeIntegerCoefficient k ^ 2 = 1 / (k : ℝ) := by
  rw [CCM.nativeIntegerCoefficient,div_pow,one_pow,Real.sq_sqrt (Nat.cast_nonneg k)]

theorem native_isolated_pulse_lower_bound (x : ℕ →₀ ℂ) (K : Finset ℕ)
    (hK : ∀ k ∈ K, 0 < k ∧ k ≤ 2047) :
    probePulseSeparation * (∑ k ∈ K, ‖probeDivisorDefect x k‖ ^ 2 / (k : ℝ)) ≤
      ‖probeSparseResidual x‖ ^ 2 := by
  have hn : 0 < ‖probePulseL2‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr probePulseL2_ne_zero)
  have hb := probePulse_bessel K hK (probeSparseResidual x)
  have heach (k : ℕ) (hkK : k ∈ K) :
      ‖inner ℂ (probePulseShift (Real.log k)) (probeSparseResidual x)‖ ^ 2 =
      ‖inner ℂ probePulseL2 (probeTarget : ProbeL2)‖ ^ 2 *
        (‖probeDivisorDefect x k‖ ^ 2 / (k : ℝ)) := by
    rw [probePulseShift_residual (hK k hkK).1 (hK k hkK).2,norm_mul,norm_mul,
      mul_pow,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
      probeIntegerCoefficient_sq (hK k hkK).1]
    ring
  rw [Finset.sum_congr rfl heach,← Finset.mul_sum] at hb
  unfold probePulseSeparation
  rw [div_mul_eq_mul_div,div_le_iff₀ hn]
  simpa only [mul_comm] using hb

theorem probeMobius_divisor_sum (k : ℕ) :
    (∑ n ∈ k.divisors, (ArithmeticFunction.moebius n : ℂ)) =
      if k = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f k)
    (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  rw [ArithmeticFunction.coe_mul_zeta_apply,ArithmeticFunction.one_apply] at h
  simpa only [ArithmeticFunction.intCoe_apply] using h

theorem probeDivisorDefect_sum (x : ℕ → ℂ) (k : ℕ) :
    (∑ n ∈ k.divisors, ((ArithmeticFunction.moebius n : ℂ) - x n)) =
      probeDivisorDefect x k := by
  rw [Finset.sum_sub_distrib,probeMobius_divisor_sum]
  rfl

theorem probeDivisorDefect_inversion (x : ℕ → ℂ) {k : ℕ} (hk : 0 < k) :
    (∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k / d) : ℂ) * probeDivisorDefect x d) =
      (ArithmeticFunction.moebius k : ℂ) - x k := by
  have h := ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq.mp
    (fun n (_hn : 0 < n) => probeDivisorDefect_sum x n) k hk
  rw [Nat.sum_divisorsAntidiagonal' (fun a b =>
    (ArithmeticFunction.moebius a : ℂ) * probeDivisorDefect x b)] at h
  exact h

theorem probe_squarefree_omission_defect {x : ℕ → ℂ} {k : ℕ}
    (hk : 0 < k) (hsq : Squarefree k) (hx : x k = 0) :
    1 / (∑ d ∈ k.divisors, (d : ℝ)) ≤
      ∑ d ∈ k.divisors, ‖probeDivisorDefect x d‖ ^ 2 / (d : ℝ) := by
  have hsum : 1 ≤ ∑ d ∈ k.divisors, ‖probeDivisorDefect x d‖ := by
    have hi := probeDivisorDefect_inversion x hk
    rw [hx,sub_zero] at hi
    have hnorm : ‖(ArithmeticFunction.moebius k : ℂ)‖ = 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_eq_one_of_squarefree hsq
    calc
      1 = ‖∑ d ∈ k.divisors, (ArithmeticFunction.moebius (k / d) : ℂ) *
          probeDivisorDefect x d‖ := by rw [hi,hnorm]
      _ ≤ ∑ d ∈ k.divisors, ‖(ArithmeticFunction.moebius (k / d) : ℂ) *
          probeDivisorDefect x d‖ := norm_sum_le _ _
      _ ≤ ∑ d ∈ k.divisors, ‖probeDivisorDefect x d‖ := by
        apply Finset.sum_le_sum
        intro d _hd
        rw [norm_mul]
        apply mul_le_of_le_one_left (norm_nonneg _)
        rw [Complex.norm_intCast]
        exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := k / d))
  have hcs := Finset.sq_sum_div_le_sum_sq_div k.divisors
    (fun d => ‖probeDivisorDefect x d‖)
    (g := fun d => (d : ℝ)) (fun d hd => by exact_mod_cast Nat.pos_of_mem_divisors hd)
  have hden : 0 < ∑ d ∈ k.divisors, (d : ℝ) := by
    apply Finset.sum_pos'
    · intro d _hd
      positivity
    · exact ⟨1,Nat.one_mem_divisors.mpr (Nat.ne_of_gt hk),by norm_num⟩
  calc
    _ ≤ (∑ d ∈ k.divisors, ‖probeDivisorDefect x d‖) ^ 2 /
        (∑ d ∈ k.divisors, (d : ℝ)) := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith [sq_nonneg ((∑ d ∈ k.divisors, ‖probeDivisorDefect x d‖) - 1)]
    _ ≤ _ := hcs

theorem probe_2047_squarefree : Squarefree (2047 : ℕ) := by
  rw [show (2047 : ℕ) = 23 * 89 by norm_num,
    Nat.squarefree_mul (show Nat.Coprime 23 89 by norm_num)]
  exact ⟨(show Nat.Prime 23 by norm_num).squarefree,(show Nat.Prime 89 by norm_num).squarefree⟩

theorem probe_2047_divisor_sum : (∑ d ∈ Nat.divisors 2047, (d : ℝ)) = 2160 := by
  have h : (∑ d ∈ Nat.divisors 2047, d) = 2160 := by
    rw [show (2047 : ℕ) = 23 * 89 by norm_num,
      (show Nat.Coprime 23 89 by norm_num).sum_divisors_mul,
      (show Nat.Prime 23 by norm_num).divisors,
      (show Nat.Prime 89 by norm_num).divisors]
    norm_num
  rw [← Nat.cast_sum,h]
  norm_num

theorem probe_pulse_numerical_bound : (6900 : ℝ) ^ 2 <
    12 * Real.exp (-1 / 512) * 2048 ^ 3 / 2160 := by
  have h := Real.add_one_le_exp (-1 / 512 : ℝ)
  nlinarith


theorem probePulseSeparation_paper_lower :
    12 * Real.exp (-1 / 512) * 2048 ^ 3 ≤ probePulseSeparation := by
  have h := probePulseSeparation_lower
  rw [probePulseLength_eq] at h
  norm_num [div_eq_mul_inv] at h ⊢
  exact h

theorem native_squarefree_omission_bound (x : ℕ →₀ ℂ) {k : ℕ}
    (hk : 0 < k) (hmax : k ≤ 2047) (hsq : Squarefree k) (hx : x k = 0) :
    probePulseSeparation / (∑ d ∈ k.divisors, (d : ℝ)) ≤ ‖probeSparseResidual x‖ ^ 2 := by
  have hS : 0 ≤ probePulseSeparation := div_nonneg (sq_nonneg _) (sq_nonneg _)
  calc
    _ = probePulseSeparation * (1 / (∑ d ∈ k.divisors, (d : ℝ))) := by ring
    _ ≤ probePulseSeparation * (∑ d ∈ k.divisors, ‖probeDivisorDefect x d‖ ^ 2 / (d : ℝ)) :=
      mul_le_mul_of_nonneg_left (probe_squarefree_omission_defect hk hsq hx) hS
    _ ≤ _ := native_isolated_pulse_lower_bound x k.divisors (fun d hd =>
      ⟨Nat.pos_of_mem_divisors hd,le_trans (Nat.le_of_dvd hk (Nat.mem_divisors.mp hd).1) hmax⟩)

theorem native_2047_omission_residual_lower (x : ℕ →₀ ℂ) (hx : x 2047 = 0) :
    6900 < ‖probeSparseResidual x‖ := by
  have hb := native_squarefree_omission_bound x (by norm_num : 0 < 2047)
    (by norm_num : 2047 ≤ 2047) probe_2047_squarefree hx
  rw [probe_2047_divisor_sum] at hb
  have hs := div_le_div_of_nonneg_right probePulseSeparation_paper_lower
    (show (0 : ℝ) ≤ 2160 by norm_num)
  have hsq := probe_pulse_numerical_bound.trans_le (hs.trans hb)
  nlinarith [norm_nonneg (probeSparseResidual x)]



/-! S01 native source endpoint: verified actual probability-law and stable-filter composition. -/
section NativeSourceEndpoint
set_option backward.isDefEq.respectTransparency.types false
open Zeta23.CCM.UniversalSinc



theorem source_unit_left_interval_positive (delta : ℝ) (hdelta : 0<delta) (hd1 : delta≤1) :
    0<centeredUnitBoxLaw (Ioo (-1:ℝ) (-1+delta)) := by
  rw [centeredUnitBoxLaw,ProbabilityTheory.cond_apply measurableSet_Icc]
  have hs : Ioo (-1:ℝ) (-1+delta)⊆Icc (-1:ℝ) 1 := by
    intro x hx
    exact ⟨hx.1.le,by linarith [hx.2]⟩
  rw [inter_eq_right.mpr hs,Real.volume_Icc,Real.volume_Ioo]
  apply ENNReal.mul_pos
  · norm_num
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))

theorem source_left_cylinder_positive (M : ℕ) (delta : ℝ) (hdelta : 0<delta) (hd1 : delta≤1) :
    0<sourceCoordinateLaw (Set.pi (↑(Finset.range M)) (fun _ : ℕ => Ioo (-1:ℝ) (-1+delta))) := by
  rw [sourceCoordinateLaw,Measure.infinitePi_pi _ (fun _ _ => measurableSet_Ioo)]
  apply pos_iff_ne_zero.mpr
  rw [Finset.prod_ne_zero_iff]
  intro n _
  exact ne_of_gt (source_unit_left_interval_positive delta hdelta hd1)

theorem source_left_cylinder_forces_sum (s epsilon delta : ℝ) (hs : 0<s) (hepsilon : 0<epsilon)
    (hdelta : 0<delta) (hd1 : delta≤1) (M : ℕ) (hM : 1≤M)
    (hprecision : delta*s+2*(s/((M:ℝ)+1))<epsilon)
    (omega : ℕ → ℝ)
    (homega : omega∈Set.pi (↑(Finset.range M)) (fun _ : ℕ => Ioo (-1:ℝ) (-1+delta))) :
    sourceSampleSum s omega∈Ioo (-s) (-s+epsilon) := by
  have hc (n : ℕ) (hn : n∈range M) : unitClamp (omega n)=omega n := by
    have h := homega n hn
    exact unitClamp_eq_self_of_mem ⟨h.1.le,by linarith [h.2]⟩
  have hlow : (∑ n∈range M,width s n*(-1))<sourceSamplePartialSum s M omega := by
    unfold sourceSamplePartialSum
    apply Finset.sum_lt_sum
    · intro n hn
      rw [hc n hn]
      exact (mul_lt_mul_of_pos_left (homega n hn).1 (width_pos hs n)).le
    · have h0 : 0∈Finset.range M := Finset.mem_range.mpr (by omega)
      refine ⟨0,h0,?_⟩
      rw [hc 0 h0]
      exact mul_lt_mul_of_pos_left (homega 0 h0).1 (width_pos hs 0)
  have hupp : sourceSamplePartialSum s M omega≤∑ n∈range M,width s n*(-1+delta) := by
    unfold sourceSamplePartialSum
    apply Finset.sum_le_sum
    intro n hn
    rw [hc n hn]
    exact (mul_lt_mul_of_pos_left (homega n hn).2 (width_pos hs n)).le
  rw [← Finset.sum_mul,sum_width_range] at hlow hupp
  have ht := abs_le.mp (sourceSampleSum_sub_partial_abs_le hs.le M omega)
  have hr : 0≤s/((M:ℝ)+1) := by positivity
  constructor
  · linarith [ht.1]
  · nlinarith [ht.2,mul_nonneg hdelta.le hr]

theorem original_source_law_left_mass (s epsilon : ℝ) (hs : 0<s) (hepsilon : 0<epsilon) :
    0<originalSourceLaw s (Ioo (-s) (-s+epsilon)) := by
  obtain ⟨M,hM⟩ := exists_nat_gt (4*s/epsilon)
  have hMpositive : (0:ℝ)<(M:ℝ) := (by positivity : (0:ℝ)<4*s/epsilon).trans hM
  have hM1 : 1≤M := by exact_mod_cast (by linarith : (0:ℝ)<(M:ℝ))
  have hrad : s/((M:ℝ)+1)<epsilon/4 := by
    apply (div_lt_iff₀ (by positivity : 0<(M:ℝ)+1)).mpr
    have h := (div_lt_iff₀ hepsilon).mp hM
    nlinarith
  let delta : ℝ := min 1 (epsilon/(4*s))
  have hdelta : 0<delta := lt_min (by norm_num) (by positivity)
  have hd1 : delta≤1 := min_le_left _ _
  have hds : delta*s≤epsilon/4 := by
    have h := mul_le_mul_of_nonneg_right (min_le_right (1:ℝ) (epsilon/(4*s))) hs.le
    have he : epsilon/(4*s)*s=epsilon/4 := by field_simp
    rwa [he] at h
  have hprecision : delta*s+2*(s/((M:ℝ)+1))<epsilon := by linarith
  have hpositive := source_left_cylinder_positive M delta hdelta hd1
  rw [originalSourceLaw,Measure.map_apply (measurable_sourceSampleSum hs.le) measurableSet_Ioo]
  apply lt_of_lt_of_le hpositive
  apply measure_mono
  intro omega homega
  exact source_left_cylinder_forces_sum s epsilon delta hs hepsilon hdelta hd1 M hM1
    hprecision omega homega

theorem original_source_left_positive_point (s epsilon : ℝ) (hs : 0<s) (hepsilon : 0<epsilon) :
    ∃ x∈Ioo (-s) (-s+epsilon), 0<CCM.universalSincSource s x := by
  by_contra hnone
  push_neg at hnone
  have hz (x : ℝ) (hx : x∈Ioo (-s) (-s+epsilon)) : originalDensityCandidate s x=0 :=
    le_antisymm (hnone x hx) (originalDensityCandidate_nonneg hs x)
  have hmass := original_source_law_left_mass s epsilon hs hepsilon
  rw [originalSourceLaw_eq_withDensity hs,withDensity_apply _ measurableSet_Ioo] at hmass
  have hi : (∫⁻ x in Ioo (-s) (-s+epsilon), ENNReal.ofReal (originalDensityCandidate s x))=0 := by
    calc
      _=(∫⁻ x in Ioo (-s) (-s+epsilon), (0:ENNReal)) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        simp [hz x hx]
      _=0 := by simp
  rw [hi] at hmass
  exact (lt_irrefl _ hmass)

theorem qPlus_positive_arbitrarily_near_zero (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ∃ t∈Ioo (0:ℝ) epsilon, 0<qPlus t := by
  obtain ⟨x,hx,hpos⟩ := original_source_left_positive_point probeSigma epsilon probeSigma_pos hepsilon
  refine ⟨x+probeSigma,⟨by linarith [hx.1],by linarith [hx.2]⟩,?_⟩
  simpa [qPlus] using hpos






theorem endpoint_half_power_memLp (n : ℕ) :
    MemLp (fun t : ℝ => (halfExponentialPower n t : ℂ)) 2 volume := by
  have hmeas : Measurable (halfExponentialPower n) := by
    unfold halfExponentialPower
    exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const
  apply (memLp_two_iff_integrable_sq_norm (Complex.measurable_ofReal.comp hmeas).aestronglyMeasurable).mpr
  have hpos : IntegrableOn (fun t : ℝ => t^(2*n)*Real.exp (-t)) (Ioi 0) := by
    have h := integrableOn_rpow_mul_exp_neg_mul_rpow
      (s := ((2*n:ℕ):ℝ)) (p := (1:ℝ)) (b := (1:ℝ))
      (by have h := Nat.cast_nonneg (α:=ℝ) (2*n); linarith) (by norm_num) (by norm_num)
    simpa only [Real.rpow_natCast,Real.rpow_one,one_mul,neg_one_mul] using h
  have hc : IntegrableOn (fun t : ℝ => t^(2*n)*Real.exp (-t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr hpos
  have heq : (fun t : ℝ => ‖(halfExponentialPower n t : ℂ)‖^2)=
      (Ici (0:ℝ)).indicator (fun t : ℝ => t^(2*n)*Real.exp (-t)) := by
    funext t
    by_cases ht : 0≤t
    · simp only [halfExponentialPower,if_pos ht,indicator_apply,Set.mem_Ici,if_pos ht,
        Complex.norm_real,Real.norm_eq_abs,sq_abs,mul_pow]
      have he : Real.exp (-(1/2:ℝ)*t)^2=Real.exp (-t) := by
        rw [pow_two,← Real.exp_add]
        congr 1
        ring
      rw [he,← pow_mul,Nat.mul_comm]
    · simp [halfExponentialPower,ht]
  change Integrable (fun t : ℝ => ‖(halfExponentialPower n t : ℂ)‖^2)
  rw [heq]
  exact hc.integrable_indicator measurableSet_Ici

def endpointU2Real (t : ℝ) : ℝ :=
  halfExponentialPower 0 t-3*halfExponentialPower 1 t+
    (3/2)*halfExponentialPower 2 t-(1/6)*halfExponentialPower 3 t

theorem endpointU2Real_formula (t : ℝ) (ht : 0≤t) :
    endpointU2Real t=Real.exp (-t/2)*(1-3*t+3*t^2/2-t^3/6) := by
  simp only [endpointU2Real,halfExponentialPower,if_pos ht,pow_zero,pow_one]
  rw [show -(1/2:ℝ)*t=-t/2 by ring]
  ring

theorem endpointU2Real_zero_of_neg {t : ℝ} (ht : t<0) : endpointU2Real t=0 := by
  simp [endpointU2Real,halfExponentialPower,not_le_of_gt ht]

theorem endpointU2Real_integrable : Integrable endpointU2Real :=
  (((halfExponentialPower_integrable 0).sub ((halfExponentialPower_integrable 1).const_mul 3)).add
    ((halfExponentialPower_integrable 2).const_mul (3/2))).sub
      ((halfExponentialPower_integrable 3).const_mul (1/6))

theorem endpointU2Real_memLp : MemLp (fun t : ℝ => (endpointU2Real t : ℂ)) 2 volume := by
  have h := (((endpoint_half_power_memLp 0).sub ((endpoint_half_power_memLp 1).const_mul (3:ℂ))).add
    ((endpoint_half_power_memLp 2).const_mul (3/2:ℂ))).sub
      ((endpoint_half_power_memLp 3).const_mul (1/6:ℂ))
  convert h using 1
  funext t
  simp [endpointU2Real]

def endpointU2 : CausalProbeL2 :=
  ⟨endpointU2Real_memLp.toLp (fun t : ℝ => (endpointU2Real t : ℂ)),by
    filter_upwards [endpointU2Real_memLp.coeFn_toLp] with t ht
    intro hneg
    rw [ht,endpointU2Real_zero_of_neg hneg]
    simp⟩

theorem endpointU2_coeFn : (endpointU2 : ProbeL2)=ᵐ[volume]
    fun t : ℝ => (endpointU2Real t : ℂ) := endpointU2Real_memLp.coeFn_toLp

theorem endpointU2_damped_integrable (z : ℂ) (hz : 0≤z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(endpointU2Real t:ℂ)) := by
  have heq : (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(endpointU2Real t:ℂ))=
      fun t : ℝ => Complex.exp (-z*(t:ℂ))*(halfExponentialPower 0 t:ℂ)-
        3*(Complex.exp (-z*(t:ℂ))*(halfExponentialPower 1 t:ℂ))+
        (3/2)*(Complex.exp (-z*(t:ℂ))*(halfExponentialPower 2 t:ℂ))-
        (1/6)*(Complex.exp (-z*(t:ℂ))*(halfExponentialPower 3 t:ℂ)) := by
    funext t
    simp only [endpointU2Real,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,
      Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one]
    ring
  rw [heq]
  exact (((halfExponentialPower_damped_integrable 0 z hz).sub
    ((halfExponentialPower_damped_integrable 1 z hz).const_mul 3)).add
      ((halfExponentialPower_damped_integrable 2 z hz).const_mul (3/2))).sub
        ((halfExponentialPower_damped_integrable 3 z hz).const_mul (1/6))

theorem endpointU2_laplace (z : ℂ) (hz : 0<z.re) :
    CCM.nativeCausalLaplaceMoment z 0 (endpointU2 : ProbeL2)=
      (z-1/2)^3/(z+1/2)^4 := by
  have hrep : CCM.nativeCausalLaplaceMoment z 0 (endpointU2 : ProbeL2)=
      probeLaplace (fun t : ℝ => (endpointU2Real t:ℂ)) z := by
    apply integral_congr_ae
    filter_upwards [endpointU2_coeFn] with t ht
    simp only [pow_zero,one_mul,ht]
  rw [hrep]
  have heq : (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(endpointU2Real t:ℂ))=
      fun t : ℝ => Complex.exp (-z*(t:ℂ))*(halfExponentialPower 0 t:ℂ)-
        3*(Complex.exp (-z*(t:ℂ))*(halfExponentialPower 1 t:ℂ))+
        (3/2)*(Complex.exp (-z*(t:ℂ))*(halfExponentialPower 2 t:ℂ))-
        (1/6)*(Complex.exp (-z*(t:ℂ))*(halfExponentialPower 3 t:ℂ)) := by
    funext t
    simp only [endpointU2Real,Complex.ofReal_sub,Complex.ofReal_add,Complex.ofReal_mul,
      Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_one]
    ring
  unfold probeLaplace
  have h01 : Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(halfExponentialPower 0 t:ℂ)-
      3*(Complex.exp (-z*(t:ℂ))*(halfExponentialPower 1 t:ℂ))) :=
    (halfExponentialPower_damped_integrable 0 z hz.le).sub
      ((halfExponentialPower_damped_integrable 1 z hz.le).const_mul 3)
  have h012 : Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(halfExponentialPower 0 t:ℂ)-
      3*(Complex.exp (-z*(t:ℂ))*(halfExponentialPower 1 t:ℂ))+
      (3/2)*(Complex.exp (-z*(t:ℂ))*(halfExponentialPower 2 t:ℂ))) :=
    h01.add ((halfExponentialPower_damped_integrable 2 z hz.le).const_mul (3/2))
  rw [heq,integral_sub h012 ((halfExponentialPower_damped_integrable 3 z hz.le).const_mul (1/6)),
    integral_add h01 ((halfExponentialPower_damped_integrable 2 z hz.le).const_mul (3/2)),
    integral_sub (halfExponentialPower_damped_integrable 0 z hz.le)
      ((halfExponentialPower_damped_integrable 1 z hz.le).const_mul 3),
    integral_const_mul,integral_const_mul,integral_const_mul]
  change probeLaplace (fun t => (halfExponentialPower 0 t:ℂ)) z-
    3*probeLaplace (fun t => (halfExponentialPower 1 t:ℂ)) z+
    (3/2)*probeLaplace (fun t => (halfExponentialPower 2 t:ℂ)) z-
    (1/6)*probeLaplace (fun t => (halfExponentialPower 3 t:ℂ)) z=_
  rw [halfExponentialPower_laplace 0 z hz.le,halfExponentialPower_laplace 1 z hz.le,
    halfExponentialPower_laplace 2 z hz.le,halfExponentialPower_laplace 3 z hz.le]
  have hh : z+1/2≠0 := by
    intro h
    have h := congrArg Complex.re h
    norm_num at h
    linarith
  norm_num
  field_simp [hh]
  <;> ring

theorem endpoint_filtered_target_identity :
    fixedFilterOperator probeTarget=qPlusOperator endpointU2 := by
  apply probeCausalLaplace_ext
  intro z hz
  have hh : z+1/2≠0 := by
    intro h
    have h := congrArg Complex.re h
    norm_num at h
    linarith
  have hc : z+3/2≠0 := by
    intro h
    have h := congrArg Complex.re h
    norm_num at h
    linarith
  rw [fixedFilterOperator_laplace z hz,probeTarget_laplace_eq_physical,probeV_laplace hz.le,
    JPlus_eq_pole_polynomial_QPlus,qPlusOperator_laplace z hz,endpointU2_laplace z hz]
  calc
    _=(fixedFilterMultiplier z*CCM.nativeCompletionRationalMultiplier z*(z^2-1/4)^2)*QPlus z := by ring
    _=(causalInnerMultiplier z^2*classicalProbeMultiplier z)*QPlus z := by
      have hp := fixedFilter_pole_polynomial_factorization z hh hc
      change fixedFilterMultiplier z*CCM.nativeCompletionRationalMultiplier z*(z^2-1/4)^2=_ at hp
      rw [hp]
    _=QPlus z*((z-1/2)^3/(z+1/2)^4) := by
      unfold causalInnerMultiplier classicalProbeMultiplier
      field_simp [hh]
      <;> ring




theorem endpoint_qPlus_prefix_integral (t : ℝ) (ht : 0<t) :
    0<∫ s in Ioo (0:ℝ) t,qPlus s := by
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (Eventually.of_forall qPlus_nonneg) qPlus_integrable.integrableOn).mpr
  obtain ⟨x,hx,hpos⟩ := qPlus_positive_arbitrarily_near_zero t ht
  exact (qPlus_contDiff.continuous.isOpen_support.inter isOpen_Ioo).measure_pos volume
    ⟨x,ne_of_gt hpos,hx⟩

theorem endpointU2_lower (r u : ℝ) (hu : 0≤u) (hur : u≤r) (hr : r≤1/8) :
    Real.exp (-r/2)/2≤endpointU2Real u := by
  have hu1 : u≤1/8 := hur.trans hr
  have hc : u^3≤(1/8:ℝ)^3 := pow_le_pow_left₀ hu hu1 3
  have hp : (1/2:ℝ)≤1-3*u+3*u^2/2-u^3/6 := by nlinarith [sq_nonneg u]
  have he : Real.exp (-r/2)≤Real.exp (-u/2) := Real.exp_le_exp.mpr (by linarith)
  rw [endpointU2Real_formula u hu]
  nlinarith [Real.exp_pos (-u/2),Real.exp_pos (-r/2)]

theorem endpoint_q_u2_positive (t : ℝ) (ht : 0<t) (hsmall : t≤1/8) :
    0<∫ s : ℝ,qPlus s*endpointU2Real (t-s) := by
  have hq : MemLp qPlus 2 volume := by simpa using qPlus_memLp.re
  have hu : MemLp endpointU2Real 2 volume := by simpa using endpointU2Real_memLp.re
  have hi : Integrable (fun s : ℝ => qPlus s*endpointU2Real (t-s)) :=
    hq.integrable_mul (hu.comp_measurePreserving (volume.measurePreserving_sub_left t))
  let c : ℝ := Real.exp (-t/2)/2
  have hc : 0<c := by dsimp [c]; positivity
  have hlo : Integrable ((Ioo (0:ℝ) t).indicator (fun s => c*qPlus s)) :=
    ((qPlus_integrable.const_mul c).integrableOn).integrable_indicator measurableSet_Ioo
  have hpoint (s : ℝ) : (Ioo (0:ℝ) t).indicator (fun s => c*qPlus s) s≤
      qPlus s*endpointU2Real (t-s) := by
    by_cases hs : s∈Ioo (0:ℝ) t
    · rw [indicator_of_mem hs]
      have hu := endpointU2_lower t (t-s) (by linarith [hs.2]) (by linarith [hs.1]) hsmall
      dsimp [c]
      nlinarith [qPlus_nonneg s]
    · rw [indicator_of_notMem hs]
      by_cases hsn : s<0
      · rw [qPlus_zero_of_neg hsn,zero_mul]
      by_cases hst : t<s
      · rw [endpointU2Real_zero_of_neg (by linarith : t-s<0),mul_zero]
      have hu := endpointU2_lower t (t-s) (by linarith) (by linarith) hsmall
      exact mul_nonneg (qPlus_nonneg s) (le_trans hc.le hu)
  have hb := integral_mono hlo hi hpoint
  rw [integral_indicator measurableSet_Ioo,integral_const_mul] at hb
  exact (mul_pos hc (endpoint_qPlus_prefix_integral t ht)).trans_le hb

theorem endpoint_fixedFilter_memLp :
    MemLp (fun t : ℝ => (fixedFilterKernel t:ℂ)) 2 volume := by
  have h := ((endpoint_half_power_memLp 3).const_mul (1/6:ℂ)).add
    ((endpoint_half_power_memLp 4).const_mul (1/24:ℂ))
  convert h using 1
  funext t
  simp [fixedFilterKernel_eq_exponential_powers]
  ring

theorem endpoint_fixedFilter_measurable : Measurable fixedFilterKernel := by
  unfold fixedFilterKernel
  exact Measurable.ite measurableSet_Ici (by fun_prop) measurable_const

theorem endpoint_filtered_target_representative :
    (fixedFilterOperator probeTarget : ProbeL2)=ᵐ[volume]
      fun t => ∫ s : ℝ,(fixedFilterKernel s:ℂ)*probeV (t-s) :=
  kernelL2Operator_coeFn_of_representative fixedFilterKernel fixedFilterKernel_integrable
    endpoint_fixedFilter_measurable endpoint_fixedFilter_memLp (probeTarget:ProbeL2) probeV probeTarget_coeFn

theorem endpoint_smoothed_u2_representative :
    (qPlusOperator endpointU2 : ProbeL2)=ᵐ[volume]
      fun t => ∫ s : ℝ,(qPlus s:ℂ)*(endpointU2Real (t-s):ℂ) :=
  kernelL2Operator_coeFn_of_representative qPlus qPlus_integrable qPlus_contDiff.continuous.measurable
    qPlus_memLp (endpointU2:ProbeL2) _ endpointU2_coeFn

theorem endpoint_probeV_essential_left (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ¬ (probeV=ᵐ[volume.restrict (Ioo (0:ℝ) epsilon)] fun _ => (0:ℂ)) := by
  intro hzero
  have hp := Measure.eqOn_Ioo_of_ae_eq volume hzero probeV_contDiff.continuous.continuousOn continuousOn_const
  have hconv (t : ℝ) (ht : t∈Ioo (0:ℝ) epsilon) :
      (∫ s : ℝ,(fixedFilterKernel s:ℂ)*probeV (t-s))=0 := by
    apply integral_eq_zero_of_ae
    have hne : ∀ᵐ s : ℝ ∂volume,s≠t := by
      rw [ae_iff]
      simpa only [not_not,setOf_eq_eq_singleton] using (measure_singleton t : volume {t}=0)
    filter_upwards [hne] with s hs
    change (fixedFilterKernel s:ℂ)*probeV (t-s)=0
    by_cases hsn : s<0
    · rw [fixedFilterKernel_zero_of_neg s hsn,Complex.ofReal_zero,zero_mul]
    by_cases hst : s<t
    · rw [hp ⟨by linarith,by linarith [ht.2]⟩,mul_zero]
    · rw [probeV_zero_of_neg (by have hst' : t<s := lt_of_le_of_ne (le_of_not_gt hst) (Ne.symm hs); linarith),mul_zero]
  have hrepr := endpoint_filtered_target_representative
  rw [endpoint_filtered_target_identity] at hrepr
  have heq := hrepr.symm.trans endpoint_smoothed_u2_representative
  let r : ℝ := min epsilon (1/8)
  have hr : 0<r := lt_min hepsilon (by norm_num)
  have hnull : ∀ᵐ t : ℝ ∂volume,t∉Ioo (0:ℝ) r := by
    filter_upwards [heq] with t ht
    intro hmem
    have h0 := hconv t ⟨hmem.1,hmem.2.trans_le (min_le_left _ _)⟩
    have hpos := endpoint_q_u2_positive t hmem.1 (hmem.2.le.trans (min_le_right _ _))
    rw [h0,realKernelConvolution_coe] at ht
    have hz : (∫ s : ℝ,qPlus s*endpointU2Real (t-s))=0 := Complex.ofReal_eq_zero.mp ht.symm
    linarith
  have hmeasure : volume (Ioo (0:ℝ) r)=0 := by
    have h := ae_iff.mp hnull
    have hset : {a : ℝ | ¬(a∉Ioo (0:ℝ) r)}=Ioo (0:ℝ) r := by
      ext a
      simp only [mem_setOf_eq,not_not]
    rw [hset] at h
    exact h
  have hpositive : 0<volume (Ioo (0:ℝ) r) := (Measure.measure_Ioo_pos volume).mpr hr
  rw [hmeasure] at hpositive
  exact lt_irrefl _ hpositive

theorem endpoint_probeW_essential_left (epsilon : ℝ) (hepsilon : 0<epsilon) :
    ¬ (probeW=ᵐ[volume.restrict (Ioo (0:ℝ) epsilon)] fun _ => (0:ℂ)) := by
  intro hzero
  have hp := Measure.eqOn_Ioo_of_ae_eq volume hzero probeW_contDiff.continuous.continuousOn continuousOn_const
  let r : ℝ := min epsilon (Real.log 2)
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hr : 0<r := lt_min hepsilon hlog
  apply endpoint_probeV_essential_left r hr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have heq := probeW_eq_probeV_first_cell (ht.2.trans_le (min_le_right _ _))
  rw [← heq]
  exact hp ⟨ht.1,ht.2.trans_le (min_le_left _ _)⟩


end NativeSourceEndpoint

/-! S01d/e: fixed-prefix geometry at the exact source support endpoint. -/


def sourcePrefixProfile (w : ℝ → ℂ) (α : ℝ) (M n : ℕ) : ℝ → ℂ :=
  (Set.Ioo (0 : ℝ) (α + Real.log (M + 1 : ℕ))).indicator
    (fun t => (CCM.nativeIntegerCoefficient n : ℂ) * w (t - Real.log n))

theorem sourcePrefixProfile_memLp {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) (M n : ℕ) : MemLp (sourcePrefixProfile w α M n) 2 volume :=
  ((hw.comp_measurePreserving (measurePreserving_sub_right volume (Real.log n))).const_mul
    (CCM.nativeIntegerCoefficient n : ℂ)).indicator measurableSet_Ioo

def sourcePrefixColumn {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) (M n : ℕ) : ProbeL2 :=
  (sourcePrefixProfile_memLp hw α M n).toLp (sourcePrefixProfile w α M n)

theorem sourcePrefixColumn_coeFn {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) (M n : ℕ) : sourcePrefixColumn hw α M n =ᵐ[volume] sourcePrefixProfile w α M n :=
  (sourcePrefixProfile_memLp hw α M n).coeFn_toLp

theorem sourcePrefixColumns_linearIndependent {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (hc : Continuous w) {α : ℝ} (hα : 0 ≤ α)
    (hbefore : ∀ t : ℝ, t < α → w t = 0)
    (hendpoint : ∀ ε : ℝ, 0 < ε → ∃ u ∈ Set.Ioo α (α + ε), w u ≠ 0)
    (M : ℕ) : LinearIndependent ℂ (fun i : Fin M => sourcePrefixColumn hw α M (i.val + 1)) := by
  classical
  apply Fintype.linearIndependent_iff.2
  intro x hx i
  by_contra hxi
  let S : Finset (Fin M) := Finset.univ.filter (fun j => x j ≠ 0)
  have hS : S.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxi⟩⟩
  let j : Fin M := S.min' hS
  have hjS : j ∈ S := Finset.min'_mem S hS
  have hxj : x j ≠ 0 := (Finset.mem_filter.mp hjS).2
  have hsmall (m : Fin M) (hm : m < j) : x m = 0 := by
    by_contra hxm
    have hmS : m ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxm⟩
    have hmin : j ≤ m := Finset.min'_le S m hmS
    exact (not_lt_of_ge hmin) hm
  let T : ℝ := α + Real.log (M + 1 : ℕ)
  let H : ℝ → ℂ := fun t => ∑ m : Fin M,
    x m * ((CCM.nativeIntegerCoefficient (m.val + 1) : ℂ) * w (t - Real.log (m.val + 1 : ℕ)))
  have hterms (m : Fin M) :
      (x m • sourcePrefixColumn hw α M (m.val + 1)) =ᵐ[volume] fun t : ℝ =>
        x m * sourcePrefixProfile w α M (m.val + 1) t := by
    filter_upwards [Lp.coeFn_smul (x m) (sourcePrefixColumn hw α M (m.val + 1)),
      sourcePrefixColumn_coeFn hw α M (m.val + 1)] with t hsm hcfn
    rw [hsm,Pi.smul_apply,hcfn,smul_eq_mul]
  have hrep : ((∑ m : Fin M, x m • sourcePrefixColumn hw α M (m.val + 1)) : ProbeL2) =ᵐ[volume]
      fun t : ℝ => ∑ m : Fin M, x m * sourcePrefixProfile w α M (m.val + 1) t := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun m : Fin M => x m • sourcePrefixColumn hw α M (m.val + 1)),
      ae_all_iff.mpr hterms] with t hsum hterm
    rw [hsum]
    exact Finset.sum_congr rfl (fun m _hm => hterm m)
  have hz : ((∑ m : Fin M, x m • sourcePrefixColumn hw α M (m.val + 1)) : ProbeL2) =ᵐ[volume]
      fun _t : ℝ => (0 : ℂ) := by
    rw [hx]
    exact Lp.coeFn_zero ℂ 2 volume
  have hHz : H =ᵐ[volume.restrict (Set.Ioo 0 T)] fun _t : ℝ => (0 : ℂ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,ae_restrict_of_ae hrep,
      ae_restrict_of_ae hz] with t ht hrt hzt
    have hp : H t = ∑ m : Fin M, x m * sourcePrefixProfile w α M (m.val + 1) t := by
      apply Finset.sum_congr rfl
      intro m _hm
      rw [sourcePrefixProfile,indicator_of_mem ht]
    exact hp.trans (hrt.symm.trans hzt)
  have hHC : Continuous H := by
    unfold H
    fun_prop
  have hpoint := Measure.eqOn_open_of_ae_eq hHz isOpen_Ioo hHC.continuousOn continuous_const.continuousOn
  let δ : ℝ := Real.log (j.val + 2 : ℕ) - Real.log (j.val + 1 : ℕ)
  have hδ : 0 < δ := sub_pos.mpr (Real.log_lt_log (by positivity) (by exact_mod_cast Nat.lt_succ_self (j.val + 1)))
  obtain ⟨u,hu,huw⟩ := hendpoint δ hδ
  let t : ℝ := u + Real.log (j.val + 1 : ℕ)
  have ht : t ∈ Set.Ioo 0 T := by
    have hlogj : 0 ≤ Real.log (j.val + 1 : ℕ) := probe_log_nonneg (Nat.succ_ne_zero _)
    have hlogM : Real.log (j.val + 2 : ℕ) ≤ Real.log (M + 1 : ℕ) :=
      Real.log_le_log (by positivity) (by exact_mod_cast (show j.val + 2 ≤ M + 1 by omega))
    dsimp only [t,T]
    dsimp only [δ] at hu
    constructor <;> linarith [hu.1,hu.2]
  have hzero := hpoint ht
  have hsum : H t = x j * (CCM.nativeIntegerCoefficient (j.val + 1) : ℂ) * w u := by
    dsimp only [H]
    rw [Finset.sum_eq_single j]
    · dsimp only [t]
      rw [add_sub_cancel_right]
      ring
    · intro m _hm hmj
      rcases lt_or_gt_of_ne hmj with hlt | hgt
      · rw [hsmall m hlt,zero_mul]
      · have hlogm : Real.log (j.val + 2 : ℕ) ≤ Real.log (m.val + 1 : ℕ) :=
          Real.log_le_log (by positivity) (by exact_mod_cast (show j.val + 2 ≤ m.val + 1 by exact Nat.succ_le_succ hgt))
        have htb : t - Real.log (m.val + 1 : ℕ) < α := by
          dsimp only [t]
          dsimp only [δ] at hu
          linarith [hu.2]
        rw [hbefore _ htb,mul_zero,mul_zero]
    · intro hjnot
      exact (hjnot (Finset.mem_univ _)).elim
  rw [hsum] at hzero
  have hcoef : (CCM.nativeIntegerCoefficient (j.val + 1) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    unfold CCM.nativeIntegerCoefficient
    exact one_div_ne_zero (ne_of_gt (Real.sqrt_pos.mpr (by positivity)))
  exact (mul_ne_zero (mul_ne_zero hxj hcoef) huw) hzero

def sourcePrefixGram {w : ℝ → ℂ} (hw : MemLp w 2 volume) (α : ℝ) (M : ℕ) :
    Matrix (Fin M) (Fin M) ℂ := Matrix.gram ℂ (fun i : Fin M => sourcePrefixColumn hw α M (i.val + 1))

theorem sourcePrefixGram_posDef {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (hc : Continuous w) {α : ℝ} (hα : 0 ≤ α)
    (hbefore : ∀ t : ℝ, t < α → w t = 0)
    (hendpoint : ∀ ε : ℝ, 0 < ε → ∃ u ∈ Set.Ioo α (α + ε), w u ≠ 0)
    (M : ℕ) : (sourcePrefixGram hw α M).PosDef :=
  Matrix.posDef_gram_of_linearIndependent (sourcePrefixColumns_linearIndependent hw hc hα hbefore hendpoint M)

def sourcePrefixEnergy {w : ℝ → ℂ} (hw : MemLp w 2 volume) (α : ℝ) (M : ℕ)
    (x : EuclideanSpace ℂ (Fin M)) : ℝ :=
  ‖∑ i : Fin M, x i • sourcePrefixColumn hw α M (i.val + 1)‖ ^ 2

theorem sourcePrefixEnergy_continuous {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) (M : ℕ) : Continuous (sourcePrefixEnergy hw α M) := by
  unfold sourcePrefixEnergy
  fun_prop

theorem sourcePrefixEnergy_smul {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) (M : ℕ) (c : ℂ) (x : EuclideanSpace ℂ (Fin M)) :
    sourcePrefixEnergy hw α M (c • x) = ‖c‖ ^ 2 * sourcePrefixEnergy hw α M x := by
  have hs : (∑ i : Fin M, (c • x) i • sourcePrefixColumn hw α M (i.val + 1)) =
      c • (∑ i : Fin M, x i • sourcePrefixColumn hw α M (i.val + 1)) := by
    change (∑ i : Fin M, (c * x i) • sourcePrefixColumn hw α M (i.val + 1)) = _
    simp only [mul_smul,Finset.smul_sum]
  rw [sourcePrefixEnergy,hs,norm_smul,mul_pow,sourcePrefixEnergy]

/-- The variational least eigenvalue of the actual fixed-prefix Gram matrix. -/
def sourcePrefixLeastEigenvalue {w : ℝ → ℂ} (hw : MemLp w 2 volume) (α : ℝ) (M : ℕ) : ℝ :=
  sInf (sourcePrefixEnergy hw α M '' Metric.sphere (0 : EuclideanSpace ℂ (Fin M)) 1)

theorem sourcePrefixEnergy_unit_compact {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) (M : ℕ) : IsCompact
      (sourcePrefixEnergy hw α M '' Metric.sphere (0 : EuclideanSpace ℂ (Fin M)) 1) :=
  (isCompact_sphere _ _).image (sourcePrefixEnergy_continuous hw α M)

theorem sourcePrefixEnergy_unit_nonempty {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) {M : ℕ} (hM : 0 < M) :
    (sourcePrefixEnergy hw α M '' Metric.sphere (0 : EuclideanSpace ℂ (Fin M)) 1).Nonempty := by
  have hx : PiLp.single 2 (⟨0,hM⟩ : Fin M) (1 : ℂ) ∈
      Metric.sphere (0 : EuclideanSpace ℂ (Fin M)) 1 := by
    simp only [Metric.mem_sphere,dist_zero_right,PiLp.norm_single,norm_one]
  exact ⟨_,⟨_,hx,rfl⟩⟩

theorem sourcePrefixLeastEigenvalue_mem {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) {M : ℕ} (hM : 0 < M) :
    sourcePrefixLeastEigenvalue hw α M ∈
      sourcePrefixEnergy hw α M '' Metric.sphere (0 : EuclideanSpace ℂ (Fin M)) 1 :=
  (sourcePrefixEnergy_unit_compact hw α M).sInf_mem (sourcePrefixEnergy_unit_nonempty hw α hM)

theorem sourcePrefixLeastEigenvalue_lower {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) {M : ℕ} (hM : 0 < M) (x : EuclideanSpace ℂ (Fin M)) :
    sourcePrefixLeastEigenvalue hw α M * ‖x‖ ^ 2 ≤ sourcePrefixEnergy hw α M x := by
  by_cases hx : x = 0
  · subst x
    simp [sourcePrefixEnergy]
  · have hn : 0 < ‖x‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hx)
    let y : EuclideanSpace ℂ (Fin M) := ((‖x‖⁻¹ : ℝ) : ℂ) • x
    have hy : y ∈ Metric.sphere (0 : EuclideanSpace ℂ (Fin M)) 1 := by
      rw [Metric.mem_sphere,dist_zero_right]
      dsimp only [y]
      rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
    have hb : sourcePrefixLeastEigenvalue hw α M ≤ sourcePrefixEnergy hw α M y :=
      csInf_le (sourcePrefixEnergy_unit_compact hw α M).bddBelow ⟨y,hy,rfl⟩
    dsimp only [y] at hb
    rw [sourcePrefixEnergy_smul,Complex.norm_real,Real.norm_eq_abs,abs_inv,abs_norm,inv_pow,
      ← div_eq_inv_mul] at hb
    exact (le_div_iff₀ hn).mp hb

theorem sourcePrefixLeastEigenvalue_pos {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (hc : Continuous w) {α : ℝ} (hα : 0 ≤ α)
    (hbefore : ∀ t : ℝ, t < α → w t = 0)
    (hendpoint : ∀ ε : ℝ, 0 < ε → ∃ u ∈ Set.Ioo α (α + ε), w u ≠ 0)
    {M : ℕ} (hM : 0 < M) : 0 < sourcePrefixLeastEigenvalue hw α M := by
  obtain ⟨x,hx,hE⟩ := sourcePrefixLeastEigenvalue_mem hw α hM
  have hxn : x ≠ 0 := by
    intro hz
    simpa [hz] using hx
  have hS : (∑ i : Fin M, x i • sourcePrefixColumn hw α M (i.val + 1)) ≠ 0 := by
    intro hz
    have hcoeff := Fintype.linearIndependent_iff.mp
      (sourcePrefixColumns_linearIndependent hw hc hα hbefore hendpoint M) (fun i => x i) hz
    apply hxn
    ext i
    exact hcoeff i
  rw [← hE,sourcePrefixEnergy]
  exact sq_pos_of_pos (norm_pos_iff.mpr hS)

theorem sourcePrefixEnergy_eq_quadratic {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) (M : ℕ) (x : EuclideanSpace ℂ (Fin M)) :
    sourcePrefixEnergy hw α M x =
      (star (fun i : Fin M => x i) ⬝ᵥ (sourcePrefixGram hw α M) *ᵥ (fun i : Fin M => x i)).re := by
  rw [sourcePrefixGram,Matrix.star_dotProduct_gram_mulVec,inner_self_eq_norm_sq_to_K]
  simp only [← RCLike.ofReal_pow,RCLike.ofReal_re]
  rfl

theorem sourcePrefixEnergy_eq_integral {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) (M : ℕ) (x : EuclideanSpace ℂ (Fin M)) :
    sourcePrefixEnergy hw α M x = ∫ t : ℝ in Set.Ioo 0 (α + Real.log (M + 1 : ℕ)),
      ‖∑ i : Fin M, x i * ((CCM.nativeIntegerCoefficient (i.val + 1) : ℂ) *
        w (t - Real.log (i.val + 1 : ℕ)))‖ ^ 2 := by
  let U : Set ℝ := Set.Ioo 0 (α + Real.log (M + 1 : ℕ))
  let F : ℝ → ℂ := fun t => ∑ i : Fin M, x i *
    ((CCM.nativeIntegerCoefficient (i.val + 1) : ℂ) * w (t - Real.log (i.val + 1 : ℕ)))
  have hterm (i : Fin M) :
      (x i • sourcePrefixColumn hw α M (i.val + 1)) =ᵐ[volume] fun t : ℝ =>
        x i * sourcePrefixProfile w α M (i.val + 1) t := by
    filter_upwards [Lp.coeFn_smul (x i) (sourcePrefixColumn hw α M (i.val + 1)),
      sourcePrefixColumn_coeFn hw α M (i.val + 1)] with t hsm hp
    rw [hsm,Pi.smul_apply,hp,smul_eq_mul]
  have hrep : ((∑ i : Fin M, x i • sourcePrefixColumn hw α M (i.val + 1)) : ProbeL2)
      =ᵐ[volume] U.indicator F := by
    filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun i : Fin M => x i • sourcePrefixColumn hw α M (i.val + 1)),
      ae_all_iff.mpr hterm] with t hsum hterms
    rw [hsum]
    by_cases ht : t ∈ U
    · rw [indicator_of_mem ht]
      apply Finset.sum_congr rfl
      intro i _hi
      rw [hterms i,sourcePrefixProfile,indicator_of_mem ht]
    · rw [indicator_of_notMem ht]
      apply Finset.sum_eq_zero
      intro i _hi
      rw [hterms i,sourcePrefixProfile,indicator_of_notMem ht,mul_zero]
  rw [sourcePrefixEnergy,OPICAFollowup.L2_norm_sq_eq_integral]
  have hnorm : (fun t : ℝ => ‖((∑ i : Fin M, x i •
      sourcePrefixColumn hw α M (i.val + 1)) : ProbeL2) t‖ ^ 2) =ᵐ[volume]
      U.indicator (fun t : ℝ => ‖F t‖ ^ 2) := by
    filter_upwards [hrep] with t ht
    rw [ht]
    by_cases hu : t ∈ U <;> simp [hu]
  rw [integral_congr_ae hnorm,integral_indicator measurableSet_Ioo]

theorem finsupp_weighted_sum_before (x : ℕ →₀ ℂ) (f : ℕ → ℂ) (M : ℕ)
    (hf : ∀ n : ℕ, M < n → f n = 0) :
    (∑ n ∈ x.support, x n * f n) = ∑ n ∈ Finset.range (M + 1), x n * f n := by
  let S := x.support ∩ Finset.range (M + 1)
  have hleft : (∑ n ∈ S, x n * f n) = ∑ n ∈ x.support, x n * f n := by
    apply Finset.sum_subset (Finset.inter_subset_left)
    intro n hn hnot
    have hnM : M < n := by
      have hnr : n ∉ Finset.range (M + 1) := fun h => hnot (Finset.mem_inter.mpr ⟨hn,h⟩)
      simpa only [Finset.mem_range,not_lt,Nat.add_one_le_iff] using hnr
    rw [hf n hnM,mul_zero]
  have hright : (∑ n ∈ S, x n * f n) = ∑ n ∈ Finset.range (M + 1), x n * f n := by
    apply Finset.sum_subset (Finset.inter_subset_right)
    intro n hn hnot
    have hnS : n ∉ x.support := fun h => hnot (Finset.mem_inter.mpr ⟨h,hn⟩)
    rw [Finsupp.notMem_support_iff.mp hnS,zero_mul]
  exact hleft.symm.trans hright

theorem native_sparse_residual_prefix_point (x : ℕ →₀ ℂ) (M : ℕ) {t : ℝ}
    (ht : t < Real.log (M + 1 : ℕ)) :
    probeV t - (∑ n ∈ x.support, x n *
      ((CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n))) =
      ∑ i : Fin M, ((ArithmeticFunction.moebius (i.val + 1) : ℂ) - x (i.val + 1)) *
        ((CCM.nativeIntegerCoefficient (i.val + 1) : ℂ) *
          probeW (t - Real.log (i.val + 1 : ℕ))) := by
  have htail (n : ℕ) (hn : M < n) :
      (CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n) = 0 := by
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlog : Real.log (M + 1 : ℕ) ≤ Real.log n :=
      Real.log_le_log (by positivity) (by exact_mod_cast hn)
    rw [probeW_zero_of_neg (show t - Real.log n < 0 by linarith),mul_zero]
  have hmu : (∑ n ∈ Finset.range (M + 1), (ArithmeticFunction.moebius n : ℂ) *
      ((CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n))) = probeV t := by
    convert mobiusProbePartialOutput_before_next M ht using 1
    apply Finset.sum_congr rfl
    intro n _hn
    simp only [CCM.nativeIntegerCoefficient,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_intCast]
    ring
  rw [finsupp_weighted_sum_before x _ M htail,← hmu,
    ← Finset.sum_sub_distrib]
  have heq : (fun n : ℕ => (ArithmeticFunction.moebius n : ℂ) *
      ((CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n)) -
        x n * ((CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n))) =
      fun n : ℕ => ((ArithmeticFunction.moebius n : ℂ) - x n) *
        ((CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n)) := by
    funext n
    ring
  rw [heq,Finset.sum_range_succ']
  simp only [CCM.nativeIntegerCoefficient,Nat.cast_zero,Real.sqrt_zero,div_zero,
    Complex.ofReal_zero,zero_mul,mul_zero,add_zero]
  exact (Fin.sum_univ_eq_sum_range _ _).symm

theorem probeSparseOutput_coeFn (x : ℕ →₀ ℂ) : probeSparseOutput x =ᵐ[volume]
    fun t : ℝ => ∑ n ∈ x.support, x n *
      ((CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n)) := by
  have hterm (n : ℕ) : (x n • (probeColumn n : ProbeL2)) =ᵐ[volume] fun t : ℝ =>
      x n * ((CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n)) := by
    filter_upwards [Lp.coeFn_smul (x n) (probeColumn n : ProbeL2),probeColumn_coeFn_all n]
      with t hsm hc
    rw [hsm,Pi.smul_apply,hc,smul_eq_mul]
  rw [probeSparseOutput]
  filter_upwards [Lp.coeFn_fun_finsetSum x.support
    (fun n => x n • (probeColumn n : ProbeL2)),ae_all_iff.mpr hterm] with t hsum hterms
  rw [hsum]
  exact Finset.sum_congr rfl (fun n _hn => hterms n)

theorem probeSparseResidual_coeFn (x : ℕ →₀ ℂ) : probeSparseResidual x =ᵐ[volume]
    fun t : ℝ => probeV t - (∑ n ∈ x.support, x n *
      ((CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n))) := by
  rw [probeSparseResidual]
  filter_upwards [Lp.coeFn_sub (probeTarget : ProbeL2) (probeSparseOutput x),
    probeTarget_coeFn,probeSparseOutput_coeFn x] with t hsub hv ho
  rw [hsub,Pi.sub_apply,hv,ho]

def nativePrefixDifference (x : ℕ →₀ ℂ) (M : ℕ) : EuclideanSpace ℂ (Fin M) :=
  WithLp.toLp 2 (fun i : Fin M => (ArithmeticFunction.moebius (i.val + 1) : ℂ) - x (i.val + 1))

def nativePrefixGram (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  sourcePrefixGram probeW_memLp 0 M

def nativePrefixLeastEigenvalue (M : ℕ) : ℝ := sourcePrefixLeastEigenvalue probeW_memLp 0 M

theorem native_prefix_energy_residual_bound (x : ℕ →₀ ℂ) (M : ℕ) :
    sourcePrefixEnergy probeW_memLp 0 M (nativePrefixDifference x M) ≤
      ‖probeSparseResidual x‖ ^ 2 := by
  rw [sourcePrefixEnergy_eq_integral,zero_add]
  have heq : (fun t : ℝ =>
      ‖∑ i : Fin M, (nativePrefixDifference x M) i *
        ((CCM.nativeIntegerCoefficient (i.val + 1) : ℂ) *
          probeW (t - Real.log (i.val + 1 : ℕ)))‖ ^ 2) =ᵐ[
          volume.restrict (Set.Ioo 0 (Real.log (M + 1 : ℕ)))]
      fun t : ℝ => ‖probeSparseResidual x t‖ ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo,
      ae_restrict_of_ae (probeSparseResidual_coeFn x)] with t ht hr
    rw [hr,native_sparse_residual_prefix_point x M ht.2]
    rfl
  rw [integral_congr_ae heq,OPICAFollowup.L2_norm_sq_eq_integral]
  apply setIntegral_le_integral
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (probeSparseResidual x))).mp
      (Lp.memLp (probeSparseResidual x)))
  exact Filter.Eventually.of_forall (fun t => sq_nonneg ‖probeSparseResidual x t‖)

theorem native_prefix_gram_residual_bound (x : ℕ →₀ ℂ) (M : ℕ) :
    (star (fun i : Fin M => (nativePrefixDifference x M) i) ⬝ᵥ
      nativePrefixGram M *ᵥ (fun i : Fin M => (nativePrefixDifference x M) i)).re ≤
        ‖probeSparseResidual x‖ ^ 2 := by
  rw [nativePrefixGram,← sourcePrefixEnergy_eq_quadratic]
  exact native_prefix_energy_residual_bound x M

theorem native_prefix_coefficient_bound (x : ℕ →₀ ℂ) {M : ℕ} (hM : 0 < M) :
    nativePrefixLeastEigenvalue M *
      (∑ i : Fin M, ‖(ArithmeticFunction.moebius (i.val + 1) : ℂ) - x (i.val + 1)‖ ^ 2) ≤
        ‖probeSparseResidual x‖ ^ 2 := by
  have h := (sourcePrefixLeastEigenvalue_lower probeW_memLp 0 hM
    (nativePrefixDifference x M)).trans (native_prefix_energy_residual_bound x M)
  rw [EuclideanSpace.norm_sq_eq] at h
  exact h

theorem sourcePrefixGram_apply_integral {w : ℝ → ℂ} (hw : MemLp w 2 volume)
    (α : ℝ) (M : ℕ) (i j : Fin M) : sourcePrefixGram hw α M i j =
      ∫ t : ℝ in Set.Ico 0 (α + Real.log (M + 1 : ℕ)),
        conj ((CCM.nativeIntegerCoefficient (i.val + 1) : ℂ) * w (t - Real.log (i.val + 1 : ℕ))) *
          ((CCM.nativeIntegerCoefficient (j.val + 1) : ℂ) * w (t - Real.log (j.val + 1 : ℕ))) := by
  rw [sourcePrefixGram,Matrix.gram_apply,L2.inner_def,integral_Ico_eq_integral_Ioo,
    ← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards [sourcePrefixColumn_coeFn hw α M (i.val + 1),
    sourcePrefixColumn_coeFn hw α M (j.val + 1)] with t hi hj
  rw [hi,hj,RCLike.inner_apply']
  dsimp only [sourcePrefixProfile]
  by_cases ht : t ∈ Set.Ioo 0 (α + Real.log (M + 1 : ℕ))
  · simp only [indicator_of_mem ht]
  · simp only [indicator_of_notMem ht,map_zero,zero_mul]

theorem native_prefix_coordinate_error_bound (x : ℕ →₀ ℂ) {M : ℕ} (hM : 0 < M)
    (hEigen : 0 < nativePrefixLeastEigenvalue M) (i : Fin M) :
    ‖(ArithmeticFunction.moebius (i.val + 1) : ℂ) - x (i.val + 1)‖ ≤
      ‖probeSparseResidual x‖ / Real.sqrt (nativePrefixLeastEigenvalue M) := by
  have hi : ‖(ArithmeticFunction.moebius (i.val + 1) : ℂ) - x (i.val + 1)‖ ^ 2 ≤
      ∑ j : Fin M, ‖(ArithmeticFunction.moebius (j.val + 1) : ℂ) - x (j.val + 1)‖ ^ 2 :=
    Finset.single_le_sum (fun j _hj => sq_nonneg
      ‖(ArithmeticFunction.moebius (j.val + 1) : ℂ) - x (j.val + 1)‖) (Finset.mem_univ i)
  have hb := (mul_le_mul_of_nonneg_left hi hEigen.le).trans (native_prefix_coefficient_bound x hM)
  have hs : 0 < Real.sqrt (nativePrefixLeastEigenvalue M) := Real.sqrt_pos.mpr hEigen
  apply (le_div_iff₀ hs).mpr
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hs.le) (norm_nonneg _)).mp
  rw [mul_pow,Real.sq_sqrt hEigen.le]
  nlinarith

theorem native_prefix_coordinate_tendsto {M : ℕ} (hM : 0 < M)
    (hEigen : 0 < nativePrefixLeastEigenvalue M) (x : ℕ → (ℕ →₀ ℂ))
    (hr : Tendsto (fun n => ‖probeSparseResidual (x n)‖) atTop (𝓝 0)) (i : Fin M) :
    Tendsto (fun n => x n (i.val + 1)) atTop
      (𝓝 (ArithmeticFunction.moebius (i.val + 1) : ℂ)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  apply squeeze_zero (fun _n => norm_nonneg _)
    (fun n => ?_) (by simpa using hr.div_const (Real.sqrt (nativePrefixLeastEigenvalue M)))
  simpa only [norm_sub_rev] using native_prefix_coordinate_error_bound (x n) hM hEigen i


theorem native_probeW_left_endpoint (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ u ∈ Ioo (0 : ℝ) epsilon, probeW u ≠ 0 := by
  by_contra h
  push_neg at h
  apply endpoint_probeW_essential_left epsilon hepsilon
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  exact h u hu

theorem native_prefix_gram_posDef (M : ℕ) : (nativePrefixGram M).PosDef := by
  apply sourcePrefixGram_posDef probeW_memLp probeW_contDiff.continuous (le_rfl)
    (fun t ht => probeW_zero_of_neg ht)
  intro epsilon hepsilon
  simpa only [zero_add] using native_probeW_left_endpoint epsilon hepsilon

theorem native_prefix_eigenvalue_pos {M : ℕ} (hM : 0 < M) :
    0 < nativePrefixLeastEigenvalue M := by
  apply sourcePrefixLeastEigenvalue_pos probeW_memLp probeW_contDiff.continuous (le_rfl)
    (fun t ht => probeW_zero_of_neg ht) ?_ hM
  intro epsilon hepsilon
  simpa only [zero_add] using native_probeW_left_endpoint epsilon hepsilon

theorem native_prefix_coordinate_error (x : ℕ →₀ ℂ) {M : ℕ} (hM : 0 < M) (i : Fin M) :
    ‖(ArithmeticFunction.moebius (i.val + 1) : ℂ) - x (i.val + 1)‖ ≤
      ‖probeSparseResidual x‖ / Real.sqrt (nativePrefixLeastEigenvalue M) :=
  native_prefix_coordinate_error_bound x hM (native_prefix_eigenvalue_pos hM) i

theorem native_prefix_coordinate_convergence {M : ℕ} (hM : 0 < M)
    (x : ℕ → (ℕ →₀ ℂ))
    (hr : Tendsto (fun n => ‖probeSparseResidual (x n)‖) atTop (𝓝 0)) (i : Fin M) :
    Tendsto (fun n => x n (i.val + 1)) atTop
      (𝓝 (ArithmeticFunction.moebius (i.val + 1) : ℂ)) :=
  native_prefix_coordinate_tendsto hM (native_prefix_eigenvalue_pos hM) x hr i

/-! P16: the actual full-line operator pays for negative-time input. -/


def probeNegativePart (f : ProbeL2) : ProbeL2 :=
  ((Lp.memLp f).indicator measurableSet_Iio).toLp ((Iio (0 : ℝ)).indicator f)

theorem probeNegativePart_coeFn (f : ProbeL2) :
    probeNegativePart f =ᵐ[volume] (Iio (0 : ℝ)).indicator f :=
  ((Lp.memLp f).indicator measurableSet_Iio).coeFn_toLp

def probePositivePart (f : ProbeL2) : CausalProbeL2 :=
  ⟨f - probeNegativePart f,by
    filter_upwards [Lp.coeFn_sub f (probeNegativePart f),probeNegativePart_coeFn f] with t hs hn
    intro ht
    change t ∈ Iio (0 : ℝ) at ht
    rw [hs,Pi.sub_apply,hn,indicator_of_mem ht,sub_self]⟩

theorem probe_signed_time_decomposition (f : ProbeL2) :
    f = (probePositivePart f : ProbeL2) + probeNegativePart f := by
  change f = (f - probeNegativePart f) + probeNegativePart f
  abel

def probeNegativeExponential (u : ℝ) : ℂ :=
  (Iic (0 : ℝ)).indicator (fun u : ℝ => (Real.exp (u / 2) : ℂ)) u

theorem probeNegativeExponential_norm_sq (u : ℝ) :
    ‖probeNegativeExponential u‖ ^ 2 = (Iic (0 : ℝ)).indicator Real.exp u := by
  by_cases hu : u ∈ Iic (0 : ℝ)
  · rw [probeNegativeExponential,indicator_of_mem hu,indicator_of_mem hu,
      Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _),pow_two,← Real.exp_add]
    congr 1
    ring
  · simp [probeNegativeExponential,hu]

theorem probeNegativeExponential_norm_sq_integrable :
    Integrable (fun u : ℝ => ‖probeNegativeExponential u‖ ^ 2) := by
  have hi : IntegrableOn Real.exp (Iic (0 : ℝ)) := by
    simpa only [one_mul] using integrableOn_exp_mul_Iic (a := 1) (by norm_num) 0
  exact (hi.integrable_indicator measurableSet_Iic).congr
    (Filter.Eventually.of_forall fun u => (probeNegativeExponential_norm_sq u).symm)

theorem probeNegativeExponential_memLp : MemLp probeNegativeExponential 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm ?_).mpr probeNegativeExponential_norm_sq_integrable
  exact (by fun_prop : Continuous (fun u : ℝ => (Real.exp (u / 2) : ℂ))).aestronglyMeasurable.indicator measurableSet_Iic

theorem probeNegativeExponential_integral_norm_sq :
    (∫ u : ℝ, ‖probeNegativeExponential u‖ ^ 2) = 1 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall probeNegativeExponential_norm_sq),
    integral_indicator measurableSet_Iic]
  simpa only [one_mul,mul_zero,Real.exp_zero,div_one] using integral_exp_mul_Iic (a := 1) (by norm_num) 0

def probeNegativeWeightedMass (f : ProbeL2) : ℝ :=
  ∫ u : ℝ, ‖probeNegativeExponential u‖ * ‖probeNegativePart f u‖

theorem probeNegativeWeightedMass_integrable (f : ProbeL2) :
    Integrable (fun u : ℝ => ‖probeNegativeExponential u‖ * ‖probeNegativePart f u‖) := by
  have hf : Integrable (fun u : ℝ => ‖probeNegativePart f u‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  apply (((probeNegativeExponential_norm_sq_integrable.add hf).div_const 2)).mono'
    (probeNegativeExponential_memLp.aestronglyMeasurable.norm.mul
      (Lp.aestronglyMeasurable (probeNegativePart f)).norm)
  filter_upwards with u
  change ‖‖probeNegativeExponential u‖ * ‖probeNegativePart f u‖‖ ≤
    (‖probeNegativeExponential u‖ ^ 2 + ‖probeNegativePart f u‖ ^ 2) / 2
  rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  nlinarith [sq_nonneg (‖probeNegativeExponential u‖ - ‖probeNegativePart f u‖)]

theorem probeNegativeWeightedMass_bound (f : ProbeL2) :
    probeNegativeWeightedMass f ≤ ‖probeNegativePart f‖ := by
  have h := integral_mul_norm_le_Lp_mul_Lq (p := 2) (q := 2)
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    (by simpa using probeNegativeExponential_memLp)
    (by simpa using Lp.memLp (probeNegativePart f))
  simp only [Real.rpow_two] at h
  rw [probeNegativeExponential_integral_norm_sq,← OPICAFollowup.L2_norm_sq_eq_integral] at h
  norm_num only [Real.one_rpow,one_mul] at h
  rw [← Real.sqrt_eq_rpow,Real.sqrt_sq_eq_abs,abs_norm] at h
  exact h

theorem native_negative_output_envelope (f : ProbeL2) (t : ℝ) :
    ‖CCM.nativeDampedCompletionPointwise 0 (probeNegativePart f) t‖ ≤
      Real.exp (-t / 2) * ‖probeNegativePart f‖ := by
  have hi0 : Integrable (fun s : ℝ => (CCM.nativePositiveCompletion s : ℂ) *
      probeNegativePart f (t - s)) := by
    simpa only [CCM.nativeDampedCompletionKernel,zero_mul,neg_zero,Real.exp_zero,one_mul] using
      CCM.nativeDampedCompletionPointwise_integrable 0 (le_rfl) (probeNegativePart f) t
  have hi : Integrable (fun u : ℝ => (CCM.nativePositiveCompletion (t - u) : ℂ) *
      probeNegativePart f u) := by
    have h := (integrable_comp_sub_left
      (fun s : ℝ => (CCM.nativePositiveCompletion s : ℂ) * probeNegativePart f (t - s)) t).mpr hi0
    simpa only [sub_sub_cancel] using h
  have htrans : (∫ s : ℝ, (CCM.nativePositiveCompletion s : ℂ) * probeNegativePart f (t - s)) =
      ∫ u : ℝ, (CCM.nativePositiveCompletion (t - u) : ℂ) * probeNegativePart f u := by
    have h := integral_sub_left_eq_self
      (fun s : ℝ => (CCM.nativePositiveCompletion s : ℂ) * probeNegativePart f (t - s)) t
      (μ := (volume : Measure ℝ))
    simpa only [sub_sub_cancel] using h.symm
  have hb : (fun u : ℝ => ‖(CCM.nativePositiveCompletion (t - u) : ℂ) *
      probeNegativePart f u‖) ≤ᵐ[volume] fun u : ℝ => Real.exp (-t / 2) *
        (‖probeNegativeExponential u‖ * ‖probeNegativePart f u‖) := by
    filter_upwards [probeNegativePart_coeFn f] with u hu
    by_cases hu0 : u < 0
    · have huSet : u ∈ Iic (0 : ℝ) := hu0.le
      have henv := CCM.nativePositiveCompletion_le_exp (t - u)
      have he : Real.exp (-((t - u) / 2)) = Real.exp (-t / 2) * Real.exp (u / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (CCM.nativePositiveCompletion_nonneg _),probeNegativeExponential,
        indicator_of_mem huSet,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      rw [he] at henv
      nlinarith [mul_le_mul_of_nonneg_right henv (norm_nonneg (probeNegativePart f u))]
    · have huSet : u ∉ Iio (0 : ℝ) := hu0
      simp only [hu,indicator_of_notMem huSet,mul_zero,norm_zero]
      exact le_rfl
  change ‖∫ s : ℝ, (CCM.nativeDampedCompletionKernel 0 s : ℂ) * probeNegativePart f (t - s)‖ ≤ _
  simp only [CCM.nativeDampedCompletionKernel,zero_mul,neg_zero,Real.exp_zero,one_mul]
  rw [htrans]
  calc
    _ ≤ ∫ u : ℝ, ‖(CCM.nativePositiveCompletion (t - u) : ℂ) * probeNegativePart f u‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ u : ℝ, Real.exp (-t / 2) *
        (‖probeNegativeExponential u‖ * ‖probeNegativePart f u‖) :=
      integral_mono_ae hi.norm ((probeNegativeWeightedMass_integrable f).const_mul _) hb
    _ = Real.exp (-t / 2) * probeNegativeWeightedMass f := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (probeNegativeWeightedMass_bound f) (Real.exp_pos _).le

def probeFullEvaluation (z : ℂ) (hz : 0 < z.re) (f : ProbeL2) : ℂ :=
  inner ℂ (CCM.nativeCausalExponentialPolynomialL2 z hz 0) f

theorem probeFullEvaluation_bound (z : ℂ) (hz : 0 < z.re) (f : ProbeL2) :
    ‖probeFullEvaluation z hz f‖ ≤ ‖f‖ / Real.sqrt (2 * z.re) := by
  have hs : 0 < Real.sqrt (2 * z.re) := Real.sqrt_pos.mpr (by positivity)
  have h := norm_inner_le_norm (𝕜 := ℂ) (CCM.nativeCausalExponentialPolynomialL2 z hz 0) f
  have hn := probeLaplaceWitness_normalization z hz
  change Real.sqrt (2 * z.re) * ‖CCM.nativeCausalExponentialPolynomialL2 z hz 0‖ = 1 at hn
  apply (le_div_iff₀ hs).mpr
  change ‖inner ℂ (CCM.nativeCausalExponentialPolynomialL2 z hz 0) f‖ * Real.sqrt (2 * z.re) ≤ ‖f‖
  have hm := mul_le_mul_of_nonneg_right h hs.le
  nlinarith [mul_nonneg (norm_nonneg f) hs.le]

theorem probeFullEvaluation_bound_of_exponential (z : ℂ) (hz : 0 < z.re) (f : ProbeL2)
    (C : ℝ) (hC : 0 ≤ C)
    (hf : ∀ᵐ t : ℝ, 0 ≤ t → ‖f t‖ ≤ C * Real.exp (-t / 2)) :
    ‖probeFullEvaluation z hz f‖ ≤ C / (z.re + 1 / 2) := by
  let H : ℝ → ℝ := (Ici (0 : ℝ)).indicator
    (fun t : ℝ => C * Real.exp (-(z.re + 1 / 2) * t))
  have ha : -(z.re + 1 / 2) < 0 := by linarith
  have hH : Integrable H := by
    have hi : IntegrableOn (fun t : ℝ => Real.exp (-(z.re + 1 / 2) * t)) (Ici 0) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]
      exact integrableOn_exp_mul_Ioi ha 0
    exact (integrable_indicator_iff measurableSet_Ici).mpr (hi.const_mul C)
  have hb : (fun t : ℝ => ‖inner ℂ
      (CCM.nativeCausalExponentialPolynomialL2 z hz 0 t) (f t)‖) ≤ᵐ[volume] H := by
    filter_upwards [CCM.nativeCausalExponentialPolynomialL2_coeFn z hz 0,hf] with t hp ht
    rw [hp,RCLike.inner_apply',norm_mul,Complex.norm_conj]
    by_cases ht0 : 0 ≤ t
    · rw [CCM.nativeCausalExponentialPolynomial_norm z 0 ht0,pow_zero,one_mul]
      dsimp only [H]
      rw [indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht0)]
      have he : Real.exp (-z.re * t) * Real.exp (-t / 2) =
          Real.exp (-(z.re + 1 / 2) * t) := by
        rw [← Real.exp_add]
        congr 1
        ring
      calc
        _ ≤ Real.exp (-z.re * t) * (C * Real.exp (-t / 2)) :=
          mul_le_mul_of_nonneg_left (ht ht0) (Real.exp_pos _).le
        _ = _ := by rw [← he]; ring
    · rw [CCM.nativeCausalExponentialPolynomial_zero_of_neg z 0 (lt_of_not_ge ht0),norm_zero,zero_mul]
      dsimp only [H]
      rw [indicator_of_notMem (show t ∉ Ici (0 : ℝ) from ht0)]
  have hI : (∫ t : ℝ, H t) = C / (z.re + 1 / 2) := by
    rw [integral_indicator measurableSet_Ici,integral_Ici_eq_integral_Ioi,
      integral_const_mul,integral_exp_mul_Ioi ha 0]
    simp only [mul_zero,Real.exp_zero,neg_div_neg_eq]
    ring
  calc
    _ ≤ ∫ t : ℝ, ‖inner ℂ (CCM.nativeCausalExponentialPolynomialL2 z hz 0 t) (f t)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, H t := integral_mono_ae (L2.integrable_inner _ _).norm hH hb
    _ = _ := hI

theorem native_negative_output_evaluation_bound (z : ℂ) (hz : 0 < z.re) (f : ProbeL2) :
    ‖probeFullEvaluation z hz (CCM.nativeDampedCompletionL2Operator 0 (le_rfl)
      (probeNegativePart f))‖ ≤ ‖probeNegativePart f‖ / (z.re + 1 / 2) := by
  apply probeFullEvaluation_bound_of_exponential z hz _ _ (norm_nonneg _)
  filter_upwards [CCM.nativeDampedCompletionL2Operator_coeFn_pointwise 0 (le_rfl)
    (probeNegativePart f)] with t ht
  intro _ht0
  rw [ht]
  simpa only [mul_comm] using native_negative_output_envelope f t

theorem probeFullEvaluation_causal (z : ℂ) (hz : 0 < z.re) (f : CausalProbeL2) :
    probeFullEvaluation z hz (f : ProbeL2) = CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) := by
  change inner ℂ (CCM.nativeCausalExponentialWitness z hz 0) f = _
  exact CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment z hz 0 f

theorem native_full_operator_causal_evaluation_zero (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) (f : CausalProbeL2) :
    probeFullEvaluation ((rho : ℂ) - 1 / 2)
      (by simp only [Complex.sub_re,Complex.ofReal_re]; norm_num; linarith)
      (CCM.nativeDampedCompletionL2Operator 0 (le_rfl) (f : ProbeL2)) = 0 := by
  change probeFullEvaluation ((rho : ℂ) - 1 / 2) _ (probeOperator f : ProbeL2) = 0
  rw [probeFullEvaluation_causal]
  exact probe_laplace_annihilates_rangeClosure rho hright (subset_closure ⟨f,rfl⟩)

theorem noncausal_probe_leakage (rho : zetaZeroConfig.carrier)
    (hright : 1 / 2 < (rho : ℂ).re) (f : ProbeL2) :
    (((rho : ℂ) - 1 / 2).re + 1 / 2) *
      max (‖probeLaplace probeV ((rho : ℂ) - 1 / 2)‖ -
        ‖(probeTarget : ProbeL2) - CCM.nativeDampedCompletionL2Operator 0 (le_rfl) f‖ /
          Real.sqrt (2 * ((rho : ℂ) - 1 / 2).re)) 0 ≤ ‖probeNegativePart f‖ := by
  let z : ℂ := (rho : ℂ) - 1 / 2
  have hz : 0 < z.re := by
    dsimp only [z]
    simp only [Complex.sub_re,Complex.ofReal_re]
    norm_num
    linarith
  let T := CCM.nativeDampedCompletionL2Operator 0 (le_rfl)
  have hcausal : probeFullEvaluation z hz (T (probePositivePart f : ProbeL2)) = 0 :=
    native_full_operator_causal_evaluation_zero rho hright (probePositivePart f)
  have hmap : T f = T (probePositivePart f : ProbeL2) + T (probeNegativePart f) := by
    have h := congrArg T (probe_signed_time_decomposition f)
    simpa only [map_add] using h
  have heval : probeFullEvaluation z hz (T f) = probeFullEvaluation z hz (T (probeNegativePart f)) := by
    rw [hmap]
    unfold probeFullEvaluation at hcausal ⊢
    rw [inner_add_right,hcausal,zero_add]
  have hv : probeFullEvaluation z hz (probeTarget : ProbeL2) = probeLaplace probeV z := by
    rw [probeFullEvaluation_causal,probeTarget_laplace_eq_physical]
  have hlin : probeFullEvaluation z hz (probeTarget : ProbeL2) =
      probeFullEvaluation z hz ((probeTarget : ProbeL2) - T f) + probeFullEvaluation z hz (T f) := by
    unfold probeFullEvaluation
    rw [inner_sub_right]
    ring
  have hb : ‖probeLaplace probeV z‖ ≤
      ‖(probeTarget : ProbeL2) - T f‖ / Real.sqrt (2 * z.re) +
        ‖probeNegativePart f‖ / (z.re + 1 / 2) := by
    calc
      _ = ‖probeFullEvaluation z hz ((probeTarget : ProbeL2) - T f) +
          probeFullEvaluation z hz (T f)‖ := congrArg norm (hv.symm.trans hlin)
      _ ≤ _ := norm_add_le _ _
      _ ≤ _ := add_le_add (probeFullEvaluation_bound z hz _)
        (by rw [heval]; exact native_negative_output_evaluation_bound z hz f)
  have ha : 0 < z.re + 1 / 2 := by linarith
  have htrade : (z.re + 1 / 2) *
      (‖probeLaplace probeV z‖ - ‖(probeTarget : ProbeL2) - T f‖ /
        Real.sqrt (2 * z.re)) ≤ ‖probeNegativePart f‖ := by
    have h := (le_div_iff₀ ha).mp (show ‖probeLaplace probeV z‖ -
      ‖(probeTarget : ProbeL2) - T f‖ / Real.sqrt (2 * z.re) ≤
        ‖probeNegativePart f‖ / (z.re + 1 / 2) from by linarith)
    nlinarith
  change (z.re + 1 / 2) * max (‖probeLaplace probeV z‖ -
    ‖(probeTarget : ProbeL2) - T f‖ / Real.sqrt (2 * z.re)) 0 ≤ ‖probeNegativePart f‖
  by_cases hA : ‖probeLaplace probeV z‖ -
      ‖(probeTarget : ProbeL2) - T f‖ / Real.sqrt (2 * z.re) ≤ 0
  · rw [max_eq_right hA,mul_zero]
    exact norm_nonneg _
  · rw [max_eq_left (le_of_not_ge hA)]
    exact htrade


end Zeta23.OPICARound2
