import Zeta23.OPICAFollowup.NativeSourceFamily
import Zeta23.OPICA.LocalData
import Zeta23.CCM.NativeIntegerDriveComplexLaplace
import Zeta23.CCM.NativeIntegerPrimeConvolution
import Zeta23.ExceptionalZero.NativeOriginalSourceLaplaceVisibility
import Zeta23.ExceptionalZero.NativeZeroJetAnalyticFactors
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic

/-! Actual integral transforms of the literal differential source family.
The native pole and forward-field assertions require their physical transform
identifications; a meromorphic formula alone does not establish that bridge. -/

noncomputable section

open Set MeasureTheory Filter Complex
open ENNReal
open scoped Topology
namespace Zeta23.OPICAFollowup
open Zeta23.CCM Zeta23.ExceptionalZero

def sourceFamilyLaplace (d : ℕ) (w : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-w*(t:ℂ))*(sourceOrderFamily d t:ℂ)

def forwardKernelLaplace (d ell : ℕ) (w : ℂ) : ℂ :=
  ∫ t : ℝ, Complex.exp (-w*(t:ℂ))*(forwardKernel d ell t:ℂ)

/-- The canonical continued expression for the repeated integer action.
Its identification with the actual integral on the initial half-plane, and
its removable value at the exceptional point, are separate obligations. -/
def forwardKernelTransformGerm (d ell : ℕ) (z : ℂ) : ℂ :=
  -sourceFamilyLaplace d z * riemannZeta (z+1/2)^ell * deriv riemannZeta (z+1/2)

theorem forwardKernelTransformGerm_formula (d ell : ℕ) (z : ℂ) :
    forwardKernelTransformGerm d ell z =
      -sourceFamilyLaplace d z * riemannZeta (z+1/2)^ell * deriv riemannZeta (z+1/2) := rfl

/-- The source-specific meromorphic expression. Its physical transform
identification is a separate theorem rather than a field in a data packet. -/
def nativePrimeTransformGerm (w : ℂ) : ℂ :=
  -nativeOriginalSourceLaplace w*deriv riemannZeta (w+1/2)/riemannZeta (w+1/2)

theorem sourceFamily_complex_contDiff (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (sourceOrderFamily d t:ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (sourceFamily_contDiff d)

theorem sourceFamily_complex_hasCompactSupport (d : ℕ) :
    HasCompactSupport (fun t : ℝ => (sourceOrderFamily d t:ℂ)) := by
  apply HasCompactSupport.intro
    (K := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale) isCompact_Icc
  intro t ht
  rw [sourceFamily_supported d t ht, Complex.ofReal_zero]

theorem complexify_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) :
    deriv (fun t : ℝ => (f t:ℂ)) = fun t : ℝ => Complex.ofReal (deriv f t) := by
  funext t
  exact ((hf t).hasDerivAt.ofReal_comp).deriv

theorem sourceDifferential_complexify {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) :
    (fun t : ℝ => (sourceDifferential f t:ℂ)) =
      universalSincDifferential (fun t : ℝ => (f t:ℂ)) := by
  have hd := complexify_deriv (hf.differentiable (by norm_num))
  have hDf : ContDiff ℝ 1 (deriv f) := hf.deriv'
  have hdd := complexify_deriv (hDf.differentiable (by norm_num))
  funext t
  simp only [sourceDifferential,universalSincDifferential,hd,hdd,Complex.ofReal_sub,
    Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat]

theorem sourceFamilyLaplace_eq_paperFT (d : ℕ) (w : ℂ) :
    sourceFamilyLaplace d w =
      Zeta23.paperFT (fun t : ℝ => (sourceOrderFamily d t:ℂ)) (I*w) := by
  unfold sourceFamilyLaplace Zeta23.paperFT
  apply integral_congr_ae
  filter_upwards with t
  have he : I*(I*w)*(t:ℂ) = -w*(t:ℂ) := by
    calc
      _ = (I*I)*w*(t:ℂ) := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [he,mul_comm]

theorem sourceFamilyLaplace_succ (d : ℕ) (w : ℂ) :
    sourceFamilyLaplace (d+1) w = (w^2-1/4)*sourceFamilyLaplace d w := by
  rw [sourceFamilyLaplace_eq_paperFT,sourceFamily_succ,
    sourceDifferential_complexify ((sourceFamily_contDiff d).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))]
  change Zeta23.paperFT (poleKilled (fun t : ℝ => (sourceOrderFamily d t:ℂ))) (I*w) = _
  rw [paperFT_poleKilled ((sourceFamily_complex_contDiff d).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
      (sourceFamily_complex_hasCompactSupport d),←sourceFamilyLaplace_eq_paperFT]
  have he : -((I*w)^2+1/4) = w^2-1/4 := by
    calc
      _ = -(I^2*w^2+1/4) := by ring
      _ = _ := by rw [I_sq]; ring
  rw [he]

theorem sourceFamilyLaplace_factor (d : ℕ) (w : ℂ) :
    sourceFamilyLaplace d w = (w^2-1/4)^d*nativeOriginalSourceLaplace w := by
  induction d with
  | zero => simp [sourceFamilyLaplace,sourceOrderFamily,nativeOriginalSourceLaplace]
  | succ d ih => rw [sourceFamilyLaplace_succ,ih,pow_succ]; ring

theorem sourceFamily_complex_eq_iterated_original (d : ℕ) :
    (fun t : ℝ => (sourceOrderFamily d t:ℂ)) =
      universalSincDifferential^[d+2] (UniversalSinc.originalDensityComplex UniversalSinc.fixedScale) := by
  induction d with
  | zero =>
    funext t
    exact nativeOriginalSource_cast_eq_physical t
  | succ d ih =>
    change (fun t : ℝ => (sourceDifferential (sourceOrderFamily d) t:ℂ)) = _
    rw [sourceDifferential_complexify ((sourceFamily_contDiff d).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)),ih]
    simpa only [show d+1+2=(d+2)+1 by omega] using
      (Function.iterate_succ_apply' (f := universalSincDifferential) (d+2)
        (UniversalSinc.originalDensityComplex UniversalSinc.fixedScale)).symm

theorem sourceFamilyLaplace_elementary_zeros (d : ℕ) :
    sourceFamilyLaplace d (1/2)=0 ∧ sourceFamilyLaplace d (-1/2)=0 := by
  constructor
  all_goals
    rw [sourceFamilyLaplace_factor,nativeOriginalSourceLaplace_formula]
    norm_num [mul_pow,I_sq]

theorem right_zero_source_factor_ne_zero (rho : zetaZeroConfig.carrier)
    (hright : 1/2 < (rho:ℂ).re) : ((rho:ℂ)-1/2)^2-1/4 ≠ 0 := by
  intro hz
  have he : ((rho:ℂ)-1/2)^2-1/4 = (rho:ℂ)*((rho:ℂ)-1) := by ring
  rw [he] at hz
  rcases mul_eq_zero.mp hz with h0 | h1
  · have h := congrArg Complex.re h0
    norm_num at h
    linarith
  · have h := congrArg Complex.re h1
    have hrho := rho.property.2.2
    simp at h
    linarith

theorem sourceFamilyLaplace_ne_zero_at_right_zero (d : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2 < (rho:ℂ).re) : sourceFamilyLaplace d ((rho:ℂ)-1/2) ≠ 0 := by
  rw [sourceFamilyLaplace_factor]
  exact mul_ne_zero (pow_ne_zero d (right_zero_source_factor_ne_zero rho hright))
    (nativeOriginalSourceLaplace_ne_zero_at_off_line_zero rho (ne_of_gt hright))

/-- The transform is the genuine compact-source integral and retains one Q;
its nonvanishing is instantiated at every actual right zero. -/
theorem sourceFamily_laplace_identity (d : ℕ) :
    (∀ w : ℂ, sourceFamilyLaplace d w = (w^2-1/4)^d*nativeOriginalSourceLaplace w) ∧
    (∀ rho : zetaZeroConfig.carrier, 1/2<(rho:ℂ).re →
      sourceFamilyLaplace d ((rho:ℂ)-1/2) ≠ 0) :=
  ⟨sourceFamilyLaplace_factor d,sourceFamilyLaplace_ne_zero_at_right_zero d⟩

theorem sourceFamily_complexDamping_integrable (d : ℕ) (w : ℂ) :
    Integrable (nativeCausalComplexDamping w (sourceOrderFamily d)) := by
  exact ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-w*(t:ℂ)))).mul
    (sourceFamily_complex_contDiff d).continuous).integrable_of_hasCompactSupport
      (sourceFamily_complex_hasCompactSupport d).mul_left

/-- Absolute norm summability precedes the exchange of the physical lattice
history and the integral. The source need not be positive. -/
theorem complex_tsum_integrable_of_summable_integral_norm
    (F : ℕ → ℝ → ℂ) (hI : ∀ n, Integrable (F n))
    (hS : Summable (fun n => ∫ t : ℝ, ‖F n t‖)) :
    Integrable (fun t => ∑' n, F n t) := by
  refine ⟨(AEMeasurable.tsum fun n => (hI n).aestronglyMeasurable.aemeasurable).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  apply lt_of_le_of_lt (lintegral_mono (fun t => enorm_tsum_le_tsum_enorm))
  rw [lintegral_tsum (fun n => (hI n).aestronglyMeasurable.enorm)]
  apply lt_top_iff_ne_top.mpr
  have heq (n : ℕ) : (∫⁻ t : ℝ, ‖F n t‖ₑ) = ‖∫ t : ℝ, ‖F n t‖‖ₑ := by
    dsimp [enorm]
    rw [lintegral_coe_eq_integral _ (hI n).norm, coe_nnreal_eq,
      coe_nnnorm, Real.norm_of_nonneg (integral_nonneg (fun t => norm_nonneg (F n t)))]
    simp only [coe_nnnorm]
  rw [funext heq]
  exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hS.abs)

theorem complexWeightedTranslate_integrable_laplace
    (c : ℕ → ℂ) (f : ℝ → ℂ) (w : ℂ)
    (hf : Integrable (fun t : ℝ => Complex.exp (-w*(t:ℂ))*f t))
    (hc : Summable (fun n : ℕ => ‖c n*Complex.exp (-w*(Real.log n:ℂ))‖)) :
    Integrable (fun t : ℝ => Complex.exp (-w*(t:ℂ))*
      (∑' n : ℕ, c n*f (t-Real.log n))) ∧
    (∫ t : ℝ, Complex.exp (-w*(t:ℂ))*(∑' n : ℕ, c n*f (t-Real.log n))) =
      (∑' n : ℕ, c n*Complex.exp (-w*(Real.log n:ℂ)))*
        ∫ t : ℝ, Complex.exp (-w*(t:ℂ))*f t := by
  let b : ℝ → ℂ := fun t => Complex.exp (-w*(t:ℂ))*f t
  let a : ℕ → ℂ := fun n => c n*Complex.exp (-w*(Real.log n:ℂ))
  let term : ℕ → ℝ → ℂ := fun n t =>
    Complex.exp (-w*(t:ℂ))*(c n*f (t-Real.log n))
  have hfactor (n : ℕ) (t : ℝ) : term n t = a n*b (t-Real.log n) := by
    have hexp : Complex.exp (-w*(t:ℂ)) =
        Complex.exp (-w*(Real.log n:ℂ))*Complex.exp (-w*((t-Real.log n:ℝ):ℂ)) := by
      rw [←Complex.exp_add]
      congr 1
      push_cast
      ring
    dsimp [term,a,b]
    rw [hexp]
    ring
  have hterm (n : ℕ) : Integrable (term n) :=
    ((hf.comp_sub_right (Real.log n)).const_mul (a n)).congr
      (Eventually.of_forall fun t => (hfactor n t).symm)
  have hnorm (n : ℕ) : (∫ t : ℝ, ‖term n t‖) = ‖a n‖*∫ t : ℝ, ‖b t‖ := by
    simp_rw [hfactor,norm_mul]
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun t : ℝ => ‖b t‖) (Real.log n)
  have hnormsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖term n t‖) := by
    simp_rw [hnorm]
    exact hc.mul_right _
  have hint (n : ℕ) : (∫ t : ℝ, term n t) = a n*∫ t : ℝ, b t := by
    simp_rw [hfactor]
    rw [integral_const_mul,integral_sub_right_eq_self]
  have hpoint (t : ℝ) : Complex.exp (-w*(t:ℂ))*(∑' n : ℕ, c n*f (t-Real.log n)) =
      ∑' n : ℕ, term n t := by
    rw [←tsum_mul_left]
  constructor
  · exact (complex_tsum_integrable_of_summable_integral_norm term hterm hnormsum).congr
      (Eventually.of_forall fun t => (hpoint t).symm)
  · calc
      _ = ∫ t : ℝ, ∑' n : ℕ, term n t := integral_congr_ae (Eventually.of_forall hpoint)
      _ = ∑' n : ℕ, ∫ t : ℝ, term n t :=
        (hasSum_integral_of_summable_integral_norm hterm hnormsum).tsum_eq.symm
      _ = (∑' n : ℕ, a n)*∫ t : ℝ, b t := by simp_rw [hint]; rw [tsum_mul_right]

theorem weightedTranslate_physical_laplace (c : ℕ → ℝ) (f : ℝ → ℝ) (w : ℂ)
    (hf : Integrable (nativeCausalComplexDamping w f))
    (hc : Summable (fun n : ℕ => ‖(c n:ℂ)*Complex.exp (-w*(Real.log n:ℂ))‖)) :
    (∫ t : ℝ, Complex.exp (-w*(t:ℂ))*(∑' n : ℕ, c n*f (t-Real.log n):ℝ)) =
      (∑' n : ℕ, (c n:ℂ)*Complex.exp (-w*(Real.log n:ℂ)))*
        ∫ t : ℝ, nativeCausalComplexDamping w f t := by
  let b := nativeCausalComplexDamping w f
  let a : ℕ → ℂ := fun n => (c n:ℂ)*Complex.exp (-w*(Real.log n:ℂ))
  let term : ℕ → ℝ → ℂ := fun n t =>
    Complex.exp (-w*(t:ℂ))*(c n*f (t-Real.log n):ℝ)
  have hfactor (n : ℕ) (t : ℝ) : term n t = a n*b (t-Real.log n) := by
    have hexp : Complex.exp (-w*(t:ℂ)) =
        Complex.exp (-w*(Real.log n:ℂ))*Complex.exp (-w*((t-Real.log n:ℝ):ℂ)) := by
      rw [←Complex.exp_add]
      congr 1
      push_cast
      ring
    dsimp [term,a,b,nativeCausalComplexDamping]
    rw [Complex.ofReal_mul,hexp]
    ring
  have hterm (n : ℕ) : Integrable (term n) :=
    ((hf.comp_sub_right (Real.log n)).const_mul (a n)).congr
      (Eventually.of_forall fun t => (hfactor n t).symm)
  have hnorm (n : ℕ) : (∫ t : ℝ, ‖term n t‖) = ‖a n‖*∫ t : ℝ, ‖b t‖ := by
    simp_rw [hfactor,norm_mul]
    rw [integral_const_mul]
    congr 1
    exact integral_sub_right_eq_self (fun t : ℝ => ‖b t‖) (Real.log n)
  have hnormsum : Summable (fun n : ℕ => ∫ t : ℝ, ‖term n t‖) := by
    simp_rw [hnorm]
    exact hc.mul_right _
  have hint (n : ℕ) : (∫ t : ℝ, term n t) = a n*∫ t : ℝ, b t := by
    simp_rw [hfactor]
    rw [integral_const_mul,integral_sub_right_eq_self]
  have hpoint (t : ℝ) : Complex.exp (-w*(t:ℂ))*(∑' n : ℕ, c n*f (t-Real.log n):ℝ) =
      ∑' n : ℕ, term n t := by
    rw [Complex.ofReal_tsum,←tsum_mul_left]
  calc
    _ = ∫ t : ℝ, ∑' n : ℕ, term n t := integral_congr_ae (Eventually.of_forall hpoint)
    _ = ∑' n : ℕ, ∫ t : ℝ, term n t :=
      (hasSum_integral_of_summable_integral_norm hterm hnormsum).tsum_eq.symm
    _ = (∑' n : ℕ, a n)*∫ t : ℝ, b t := by simp_rw [hint]; rw [tsum_mul_right]

def primeLaplaceCoefficient (w : ℂ) (n : ℕ) : ℂ :=
  (nativePrimeCoefficient n:ℂ)*Complex.exp (-w*(Real.log n:ℂ))

theorem primeLaplaceCoefficient_eq_term {w : ℂ} (hw : 1/2<w.re) (n : ℕ) :
    primeLaplaceCoefficient w n =
      LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n:ℂ)) (w+1/2) n := by
  have hfactor : primeLaplaceCoefficient w n =
      (ArithmeticFunction.vonMangoldt n:ℂ)*nativeIntegerLaplaceCoefficient w n := by
    simp only [primeLaplaceCoefficient,nativePrimeCoefficient,nativeIntegerLaplaceCoefficient,
      nativeIntegerCoefficient,Complex.ofReal_div,Complex.ofReal_one]
    ring
  rw [hfactor]
  by_cases hn : n=0
  · subst n; simp [LSeries.term_zero]
  · rw [nativeIntegerLaplaceCoefficient_eq_cpow hw,LSeries.term_of_ne_zero hn]
    ring

theorem primeLaplaceCoefficient_summable_norm {w : ℂ} (hw : 1/2<w.re) :
    Summable (fun n : ℕ => ‖primeLaplaceCoefficient w n‖) := by
  simp_rw [primeLaplaceCoefficient_eq_term hw]
  exact summable_norm_iff.mpr (ArithmeticFunction.LSeriesSummable_vonMangoldt
    (s := w+1/2) (by norm_num; linarith))

theorem primeLaplaceCoefficient_tsum {w : ℂ} (hw : 1/2<w.re) :
    (∑' n : ℕ, primeLaplaceCoefficient w n) = -deriv riemannZeta (w+1/2)/riemannZeta (w+1/2) := by
  simp_rw [primeLaplaceCoefficient_eq_term hw]
  exact ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div
    (s := w+1/2) (by norm_num; linarith)

theorem primeFieldFamily_physical_laplace (d : ℕ) {w : ℂ} (hw : 1/2<w.re) :
    (∫ t : ℝ, Complex.exp (-w*(t:ℂ))*(primeFieldFamily d t:ℂ)) =
      -sourceFamilyLaplace d w*deriv riemannZeta (w+1/2)/riemannZeta (w+1/2) := by
  unfold primeFieldFamily nativePrimeField
  rw [weightedTranslate_physical_laplace _ _ _ (sourceFamily_complexDamping_integrable d w)
    (primeLaplaceCoefficient_summable_norm hw)]
  change (∑' n : ℕ, primeLaplaceCoefficient w n)*sourceFamilyLaplace d w = _
  rw [primeLaplaceCoefficient_tsum hw]
  ring

theorem sourceFamilyLaplace_analyticAt (d : ℕ) (w : ℂ) :
    AnalyticAt ℂ (sourceFamilyLaplace d) w := by
  have heq : sourceFamilyLaplace d = fun z : ℂ =>
      (z^2-1/4)^d*nativeOriginalSourceLaplace z := funext (sourceFamilyLaplace_factor d)
  rw [heq]
  exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => (z^2-1/4)^d) w).mul
    (nativeOriginalSourceLaplace_analyticAt w)

/-- Local factorization proves the entire analytic remainder, including
multiple zeros. No residue or pole datum is supplied as a premise. -/
theorem weighted_logDeriv_visible_pole {f g : ℂ → ℂ} {p : ℂ}
    (hf : AnalyticAt ℂ f p) (hord : analyticOrderAt f p ≠ ⊤)
    (hg : AnalyticAt ℂ g p) :
    ∃ rem : ℂ → ℂ, AnalyticAt ℂ rem p ∧
      (fun z => -g z*logDeriv f z) =ᶠ[𝓝[≠] p]
        fun z => -(analyticOrderNatAt f p:ℂ)*g p/(z-p)+rem z := by
  obtain ⟨h,hh,hh0,hfh⟩ := hf.analyticOrderAt_ne_top.mp hord
  have hhn : ∀ᶠ z in 𝓝 p, h z ≠ 0 := hh.continuousAt.eventually_ne hh0
  have hlocal : ∀ᶠ z in 𝓝 p,
      f =ᶠ[𝓝 z] fun u => (u-p)^analyticOrderNatAt f p*h u := by
    filter_upwards [hfh.eventually_nhds] with z hz
    filter_upwards [hz] with u hu
    simpa only [smul_eq_mul] using hu
  have hha : ∀ᶠ z in 𝓝 p, AnalyticAt ℂ h z := hh.eventually_analyticAt
  have hds : AnalyticAt ℂ (dslope g p) p := by
    rcases hg with ⟨series,hseries⟩
    exact ⟨series.fslope,hseries.has_fpower_series_dslope_fslope⟩
  let rem : ℂ → ℂ := fun z =>
    -(analyticOrderNatAt f p:ℂ)*dslope g p z-g z*logDeriv h z
  refine ⟨rem,?_,?_⟩
  · exact (analyticAt_const.mul hds).sub (hg.mul (hh.deriv.div hh hh0))
  · filter_upwards [self_mem_nhdsWithin,mem_nhdsWithin_of_mem_nhds hhn,
      mem_nhdsWithin_of_mem_nhds hlocal,mem_nhdsWithin_of_mem_nhds hha]
      with z hz hhz hfz hhaz
    have hzp : z-p ≠ 0 := sub_ne_zero.mpr (by simpa using hz)
    have hld : logDeriv f z = (analyticOrderNatAt f p:ℂ)/(z-p)+logDeriv h z := by
      have he : logDeriv f z =
          logDeriv (fun u : ℂ => (u-p)^analyticOrderNatAt f p*h u) z := by
        simp only [logDeriv_apply,hfz.deriv_eq,hfz.self_of_nhds]
      rw [he,logDeriv_mul (f := fun u : ℂ => (u-p)^analyticOrderNatAt f p)
        (g := h) z (pow_ne_zero _ hzp) hhz (by fun_prop) hhaz.differentiableAt]
      have he' : logDeriv (fun u : ℂ => (u-p)^analyticOrderNatAt f p) z =
          (analyticOrderNatAt f p:ℂ)/(z-p) := by
        rw [show (fun u : ℂ => (u-p)^analyticOrderNatAt f p) =
            (fun x : ℂ => x^analyticOrderNatAt f p) ∘ (fun u => u-p) from rfl,
          logDeriv_comp (by fun_prop) (by fun_prop),logDeriv_pow]
        simp
      rw [he']
    dsimp [rem]
    rw [hld,dslope_of_ne _ (by simpa using hz),slope_def_field]
    ring

theorem shiftedZeta_actual_analyticAt (rho : zetaZeroConfig.carrier) :
    AnalyticAt ℂ (fun z : ℂ => riemannZeta (z+1/2)) ((rho:ℂ)-1/2) := by
  have hz : AnalyticAt ℂ riemannZeta ((rho:ℂ)-1/2+1/2) := by
    simpa only [sub_add_cancel] using
      riemannZeta_analyticOnNhd_compl_one _ rho.property.not_trivial.2
  exact hz.comp (f := fun z : ℂ => z+1/2) (x := (rho:ℂ)-1/2) (by fun_prop)

theorem shiftedZeta_actual_order (rho : zetaZeroConfig.carrier) :
    analyticOrderAt (fun z : ℂ => riemannZeta (z+1/2)) ((rho:ℂ)-1/2) =
      (zeroMult (rho:ℂ):ℕ∞) := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => z+1/2) ((rho:ℂ)-1/2) := by fun_prop
  have hd : deriv (fun z : ℂ => z+1/2) ((rho:ℂ)-1/2) ≠ 0 := by
    simp only [deriv_add_const,deriv_id'']
    exact one_ne_zero
  simpa only [Function.comp_def,sub_add_cancel] using
    (analyticOrderAt_comp_of_deriv_ne_zero (f := riemannZeta) hshift hd).trans
      (by simpa only [sub_add_cancel] using nativeZeroMultiplicity_order rho)

theorem actualZeta_meromorphic : Meromorphic riemannZeta := by
  intro s
  by_cases hs : s=1
  · subst s
    let Z : ℂ → ℂ := Function.update (fun z => (z-1)*riemannZeta z) 1 1
    have hc : ContinuousAt Z 1 := by
      simpa only [Z,continuousAt_update_same] using riemannZeta_residue_one
    have hd : ∀ᶠ z in 𝓝[≠] (1:ℂ), DifferentiableAt ℂ Z z := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z ≠ 1 := by simpa using hz
      have heq : Z =ᶠ[𝓝 z] fun u => (u-1)*riemannZeta u := by
        filter_upwards [eventually_ne_nhds hz'] with u hu
        exact Function.update_of_ne hu _ _
      exact ((differentiableAt_id.sub_const 1).mul
        (differentiableAt_riemannZeta hz')).congr_of_eventuallyEq heq
    have ha := analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hc
    have hm : MeromorphicAt (fun z : ℂ => Z z/(z-1)) 1 :=
      ha.meromorphicAt.div (analyticAt_id.sub analyticAt_const).meromorphicAt
    apply hm.congr
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz' : z ≠ 1 := by simpa using hz
    dsimp [Z]
    rw [Function.update_of_ne hz']
    field_simp
  · exact (riemannZeta_analyticOnNhd_compl_one s hs).meromorphicAt

theorem nativePrimeTransformGerm_meromorphic : Meromorphic nativePrimeTransformGerm := by
  intro z
  have hshift : AnalyticAt ℂ (fun w : ℂ => w+1/2) z := by fun_prop
  exact (((nativeOriginalSourceLaplace_analyticAt z).meromorphicAt.neg.mul
    ((actualZeta_meromorphic (z+1/2)).deriv.comp_analyticAt
      (g := fun w : ℂ => w+1/2) (x := z) hshift)).div
      ((actualZeta_meromorphic (z+1/2)).comp_analyticAt
        (g := fun w : ℂ => w+1/2) (x := z) hshift))

theorem forwardKernelTransformGerm_meromorphic (d ell : ℕ) :
    Meromorphic (forwardKernelTransformGerm d ell) := by
  intro z
  have hshift : AnalyticAt ℂ (fun w : ℂ => w+1/2) z := by fun_prop
  exact ((sourceFamilyLaplace_analyticAt d z).meromorphicAt.neg.mul
    (((actualZeta_meromorphic (z+1/2)).comp_analyticAt
      (g := fun w : ℂ => w+1/2) (x := z) hshift).pow ell)).mul
      ((actualZeta_meromorphic (z+1/2)).deriv.comp_analyticAt
        (g := fun w : ℂ => w+1/2) (x := z) hshift)

theorem forwardKernelTransformGerm_analyticAt {d ell : ℕ} {z : ℂ}
    (hz : z ≠ 1/2) : AnalyticAt ℂ (forwardKernelTransformGerm d ell) z := by
  have hs : z+1/2 ≠ 1 := by
    intro h
    apply hz
    linear_combination h
  have hshift : AnalyticAt ℂ (fun w : ℂ => w+1/2) z := by fun_prop
  have hZ := riemannZeta_analyticOnNhd_compl_one (z+1/2) hs
  exact ((sourceFamilyLaplace_analyticAt d z).neg.mul
    ((hZ.comp (f := fun w : ℂ => w+1/2) (x := z) hshift).pow ell)).mul
      (hZ.deriv.comp (f := fun w : ℂ => w+1/2) (x := z) hshift)

theorem nativePrimeField_visiblePole (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    ∃ pole : Zeta23.OPICA.SimplePoleData (ℝ → ℝ),
      pole.source=nativeOriginalSource ∧ pole.center=(rho:ℂ)-1/2 ∧
      pole.field=nativePrimeTransformGerm ∧
      pole.residue=-(zeroMult (rho:ℂ):ℂ)*nativeOriginalSourceLaplace ((rho:ℂ)-1/2) ∧
      Meromorphic pole.field ∧
      (∀ w : ℂ, 1/2<w.re →
        (∫ t : ℝ, Complex.exp (-w*(t:ℂ))*(nativeOriginalPrimeField t:ℂ))=pole.field w) := by
  let p : ℂ := (rho:ℂ)-1/2
  let f : ℂ → ℂ := fun z => riemannZeta (z+1/2)
  have horder : analyticOrderAt f p=(zeroMult (rho:ℂ):ℕ∞) := shiftedZeta_actual_order rho
  have hn : analyticOrderNatAt f p=zeroMult (rho:ℂ) := by
    change (analyticOrderAt f p).toNat=zeroMult (rho:ℂ)
    rw [horder]
    rfl
  obtain ⟨rem,hrema,hrem⟩ := weighted_logDeriv_visible_pole
    (shiftedZeta_actual_analyticAt rho) (by rw [horder]; exact ENat.natCast_ne_top _)
    (nativeOriginalSourceLaplace_analyticAt p)
  have heq : nativePrimeTransformGerm = fun z => -nativeOriginalSourceLaplace z*logDeriv f z := by
    funext z
    dsimp [nativePrimeTransformGerm,f]
    rw [logDeriv_apply,deriv_comp_add_const]
    ring
  let pole : Zeta23.OPICA.SimplePoleData (ℝ → ℝ) :=
    { source := nativeOriginalSource
      center := p
      field := nativePrimeTransformGerm
      residue := -(zeroMult (rho:ℂ):ℂ)*nativeOriginalSourceLaplace p
      residue_ne_zero := by
        apply mul_ne_zero (neg_ne_zero.mpr ?_)
          (nativeOriginalSourceLaplace_ne_zero_at_off_line_zero rho (ne_of_gt hright))
        exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one
          (zetaZeroConfig.one_le_mult _ rho.property))
      remainder := rem
      remainder_analytic := hrema
      field_eq := by
        rw [heq]
        change (fun z => -nativeOriginalSourceLaplace z*logDeriv f z) =ᶠ[𝓝[≠] p]
          (fun z => -(analyticOrderNatAt f p:ℂ)*nativeOriginalSourceLaplace p/(z-p)+rem z) at hrem
        rw [hn] at hrem
        exact hrem }
  refine ⟨pole,rfl,rfl,rfl,rfl,nativePrimeTransformGerm_meromorphic,?_⟩
  intro w hw
  have hphysical := primeFieldFamily_physical_laplace 0 hw
  change (∫ t : ℝ, Complex.exp (-w*(t:ℂ))*(nativeOriginalPrimeField t:ℂ))=nativePrimeTransformGerm w
  simpa only [sourceFamilyLaplace_factor,pow_zero,one_mul,primeFieldFamily,sourceOrderFamily,
    nativeOriginalPrimeField,nativePrimeTransformGerm] using hphysical

def nativePrimePoleData (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    Zeta23.OPICA.SimplePoleData (ℝ → ℝ) := Classical.choose (nativePrimeField_visiblePole rho hright)

theorem nativePrimePoleData_source (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    (nativePrimePoleData rho hright).source=nativeOriginalSource :=
  (Classical.choose_spec (nativePrimeField_visiblePole rho hright)).1

theorem nativePrimePoleData_center (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    (nativePrimePoleData rho hright).center=(rho:ℂ)-1/2 :=
  (Classical.choose_spec (nativePrimeField_visiblePole rho hright)).2.1

theorem nativePrimePoleData_field (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    (nativePrimePoleData rho hright).field=nativePrimeTransformGerm :=
  (Classical.choose_spec (nativePrimeField_visiblePole rho hright)).2.2.1

theorem nativePrimePoleData_residue (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    (nativePrimePoleData rho hright).residue=
      -(zeroMult (rho:ℂ):ℂ)*nativeOriginalSourceLaplace ((rho:ℂ)-1/2) :=
  (Classical.choose_spec (nativePrimeField_visiblePole rho hright)).2.2.2.1

theorem nativePrimePoleData_meromorphic (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    Meromorphic (nativePrimePoleData rho hright).field :=
  (Classical.choose_spec (nativePrimeField_visiblePole rho hright)).2.2.2.2.1

theorem nativePrimePoleData_physical_laplace (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) {w : ℂ} (hw : 1/2<w.re) :
    (∫ t : ℝ, Complex.exp (-w*(t:ℂ))*(nativeOriginalPrimeField t:ℂ))=
      (nativePrimePoleData rho hright).field w :=
  (Classical.choose_spec (nativePrimeField_visiblePole rho hright)).2.2.2.2.2 w hw


open Zeta23.CCM Zeta23.ExceptionalZero

theorem integerDriveFamily_integrable_laplace (d : ℕ) {z : ℂ} (hz : 1/2<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(integerDriveFamily d t:ℂ)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(integerDriveFamily d t:ℂ))=
      -sourceFamilyLaplace d z*deriv riemannZeta (z+1/2) := by
  have h := complexWeightedTranslate_integrable_laplace
    (fun n => (nativeIntegerDriveCoefficient n:ℂ))
    (fun t => (sourceOrderFamily d t:ℂ)) z (sourceFamily_complexDamping_integrable d z)
    (nativeIntegerDriveLaplaceCoefficient_summable_norm hz)
  have hcast (t : ℝ) : (integerDriveFamily d t:ℂ)=
      ∑' n : ℕ, (nativeIntegerDriveCoefficient n:ℂ)*(sourceOrderFamily d (t-Real.log n):ℂ) := by
    simp only [integerDriveFamily,nativeIntegerDriveField,Complex.ofReal_tsum,Complex.ofReal_mul]
  simp_rw [←hcast] at h
  constructor
  · exact h.1
  · have he := h.2
    rw [show (∑' n : ℕ, (nativeIntegerDriveCoefficient n:ℂ)*Complex.exp (-z*(Real.log n:ℂ)))=
      -deriv riemannZeta (z+1/2) from nativeIntegerDriveLaplaceCoefficient_tsum hz] at he
    exact he.trans (by unfold sourceFamilyLaplace; ring)

theorem forwardKernel_integrable_laplace (d ell : ℕ) {z : ℂ} (hz : 1/2<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(forwardKernel d ell t:ℂ)) ∧
    forwardKernelLaplace d ell z=forwardKernelTransformGerm d ell z := by
  induction ell with
  | zero => simpa only [forwardKernel,forwardKernelLaplace,forwardKernelTransformGerm,pow_zero,mul_one]
      using integerDriveFamily_integrable_laplace d hz
  | succ ell ih =>
    have h := complexWeightedTranslate_integrable_laplace
      (fun n => (nativeIntegerCoefficient n:ℂ)) (fun t => (forwardKernel d ell t:ℂ)) z ih.1
      (nativeIntegerLaplaceCoefficient_summable_norm hz)
    have hcast (t : ℝ) : (forwardKernel d (ell+1) t:ℂ)=
        ∑' n : ℕ, (nativeIntegerCoefficient n:ℂ)*(forwardKernel d ell (t-Real.log n):ℂ) := by
      simp only [forwardKernel,nativeIntegerTranslateAction,Complex.ofReal_tsum,Complex.ofReal_mul]
    simp_rw [←hcast] at h
    constructor
    · exact h.1
    · have he := h.2
      rw [show (∑' n : ℕ, (nativeIntegerCoefficient n:ℂ)*Complex.exp (-z*(Real.log n:ℂ)))=
        riemannZeta (z+1/2) from nativeIntegerLaplaceCoefficient_tsum hz] at he
      change forwardKernelLaplace d (ell+1) z=
        riemannZeta (z+1/2)*forwardKernelLaplace d ell z at he
      rw [he,ih.2,forwardKernelTransformGerm,forwardKernelTransformGerm,pow_succ]
      ring

def zetaPoleCleared (s : ℂ) : ℂ :=
  Function.update (fun u : ℂ => (u-1)*riemannZeta u) 1 1 s

theorem zetaPoleCleared_eq {s : ℂ} (hs : s≠1) :
    zetaPoleCleared s=(s-1)*riemannZeta s := Function.update_of_ne hs _ _

theorem zetaPoleCleared_one : zetaPoleCleared 1=1 := by simp [zetaPoleCleared]

theorem zetaPoleCleared_eventuallyEq {s : ℂ} (hs : s≠1) :
    zetaPoleCleared =ᶠ[𝓝 s] fun u : ℂ => (u-1)*riemannZeta u := by
  filter_upwards [eventually_ne_nhds hs] with u hu
  exact zetaPoleCleared_eq hu

theorem zetaPoleCleared_analyticAt (s : ℂ) : AnalyticAt ℂ zetaPoleCleared s := by
  by_cases hs : s=1
  · subst s
    have hc : ContinuousAt zetaPoleCleared 1 := by
      change ContinuousAt (Function.update (fun u : ℂ => (u-1)*riemannZeta u) 1 1) 1
      simpa only [continuousAt_update_same] using riemannZeta_residue_one
    have hd : ∀ᶠ u in 𝓝[≠] (1:ℂ), DifferentiableAt ℂ zetaPoleCleared u := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu' : u≠1 := by simpa using hu
      exact ((differentiableAt_id.sub_const 1).mul (differentiableAt_riemannZeta hu')).congr_of_eventuallyEq
        (zetaPoleCleared_eventuallyEq hu')
    exact analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hd hc
  · exact ((analyticAt_id.sub analyticAt_const).mul
      (riemannZeta_analyticOnNhd_compl_one s hs)).congr (zetaPoleCleared_eventuallyEq hs).symm

theorem zetaPoleCleared_deriv {s : ℂ} (hs : s≠1) :
    deriv zetaPoleCleared s=riemannZeta s+(s-1)*deriv riemannZeta s := by
  rw [(zetaPoleCleared_eventuallyEq hs).deriv_eq]
  change deriv ((fun u : ℂ => u-1)*riemannZeta) s=_
  simpa using (((hasDerivAt_id s).sub_const 1).mul (differentiableAt_riemannZeta hs).hasDerivAt).deriv

theorem sourceFamilyLaplace_cleared_factor (d : ℕ) (z : ℂ) :
    sourceFamilyLaplace d z=(z^2-1/4)^(d+2)*UniversalSinc.product UniversalSinc.fixedScale (I*z) := by
  rw [sourceFamilyLaplace_factor,nativeOriginalSourceLaplace_formula]
  have he : ((I*z)^2+1/4)^2=(z^2-1/4)^2 := by
    calc
      _ = (-(z^2-1/4))^2 := by congr 1; rw [mul_pow,I_sq]; ring
      _ = _ := by ring
  rw [he,pow_add]
  ring

def forwardKernelEntireContinuation (d ell : ℕ) (z : ℂ) : ℂ :=
  -(z+1/2)^(d+2)*(z-1/2)^(d-ell)*UniversalSinc.product UniversalSinc.fixedScale (I*z)*
    zetaPoleCleared (z+1/2)^ell*
      ((z-1/2)*deriv zetaPoleCleared (z+1/2)-zetaPoleCleared (z+1/2))

theorem forwardKernelEntireContinuation_analyticAt (d ell : ℕ) (z : ℂ) :
    AnalyticAt ℂ (forwardKernelEntireContinuation d ell) z := by
  have hshift : AnalyticAt ℂ (fun w : ℂ => w+1/2) z := by fun_prop
  have hbox : AnalyticAt ℂ (fun w : ℂ => UniversalSinc.product UniversalSinc.fixedScale (I*w)) z :=
    (UniversalSinc.analyticAt_product UniversalSinc.fixedScale_pos.le (I*z)).comp (by fun_prop)
  have hH := (zetaPoleCleared_analyticAt (z+1/2)).comp
    (f := fun w : ℂ => w+1/2) (x := z) hshift
  have hD := (zetaPoleCleared_analyticAt (z+1/2)).deriv.comp
    (f := fun w : ℂ => w+1/2) (x := z) hshift
  exact (((((by fun_prop : AnalyticAt ℂ (fun w : ℂ => -(w+1/2)^(d+2)*(w-1/2)^(d-ell)) z).mul
    hbox).mul (hH.pow ell)).mul
      (((by fun_prop : AnalyticAt ℂ (fun w : ℂ => w-1/2) z).mul hD).sub hH)))

theorem forwardKernelEntireContinuation_agrees (d ell : ℕ) (hd : ell≤d) {z : ℂ}
    (hz : z≠1/2) : forwardKernelEntireContinuation d ell z=forwardKernelTransformGerm d ell z := by
  have hs : z+1/2≠1 := by intro he; apply hz; linear_combination he
  have hH : zetaPoleCleared (z+1/2)=(z-1/2)*riemannZeta (z+1/2) := by
    rw [zetaPoleCleared_eq hs]
    congr 1
    ring
  have hD : (z-1/2)*deriv zetaPoleCleared (z+1/2)-zetaPoleCleared (z+1/2)=
      (z-1/2)^2*deriv riemannZeta (z+1/2) := by
    rw [zetaPoleCleared_deriv hs,hH]
    ring
  have hp : (z-1/2)^(d+2)=(z-1/2)^(d-ell)*(z-1/2)^ell*(z-1/2)^2 := by
    rw [←pow_add,←pow_add]
    congr 1
    omega
  rw [forwardKernelEntireContinuation,forwardKernelTransformGerm,sourceFamilyLaplace_cleared_factor,
    show z^2-1/4=(z-1/2)*(z+1/2) by ring,mul_pow,hp,hD,hH,mul_pow]
  ring

theorem forwardKernelEntireContinuation_diagonal_half (d : ℕ) :
    forwardKernelEntireContinuation d d (1/2)=UniversalSinc.product UniversalSinc.fixedScale (I*(1/2)) := by
  norm_num [forwardKernelEntireContinuation,zetaPoleCleared]

theorem forwardKernelEntireContinuation_diagonal_half_ne_zero (d : ℕ) :
    forwardKernelEntireContinuation d d (1/2) ≠ 0 := by
  rw [forwardKernelEntireContinuation_diagonal_half]
  exact UniversalSinc.product_ne_zero_of_im_ne_zero UniversalSinc.fixedScale_pos (by norm_num)

theorem forwardKernelTransformGerm_half (d ell : ℕ) :
    forwardKernelTransformGerm d ell (1/2)=0 := by
  rw [forwardKernelTransformGerm,(sourceFamilyLaplace_elementary_zeros d).1]
  ring

theorem forwardKernelEntireContinuation_diagonal_half_ne_raw (d : ℕ) :
    forwardKernelEntireContinuation d d (1/2) ≠ forwardKernelTransformGerm d d (1/2) := by
  rw [forwardKernelTransformGerm_half]
  exact forwardKernelEntireContinuation_diagonal_half_ne_zero d

theorem forwardKernel_physical_laplace (d ell : ℕ) (hd : ell≤d) :
    (∀ z : ℂ, 1/2<z.re →
      Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(forwardKernel d ell t:ℂ)) ∧
      forwardKernelLaplace d ell z=
        -sourceFamilyLaplace d z*riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2)) ∧
    (∀ z : ℂ, AnalyticAt ℂ (forwardKernelEntireContinuation d ell) z) ∧
    (∀ z : ℂ, z≠1/2 →
      forwardKernelEntireContinuation d ell z=
        -sourceFamilyLaplace d z*riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2)) :=
  ⟨fun _z hz => forwardKernel_integrable_laplace d ell hz,
    forwardKernelEntireContinuation_analyticAt d ell,
    fun _z hz => forwardKernelEntireContinuation_agrees d ell hd hz⟩



open Zeta23.CCM

def realWeightedLogTranslate (c : ℕ → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑' n : ℕ, c n*f (t-Real.log n)

theorem lowerSupport_deriv {f : ℝ → ℝ} {a : ℝ} (hf : ∀ t<a, f t=0) :
    ∀ t<a, deriv f t=0 := by
  intro t ht
  have heq : f =ᶠ[𝓝 t] fun _ : ℝ => 0 := by
    filter_upwards [eventually_lt_nhds ht] with u hu
    exact hf u hu
  rw [heq.deriv_eq,deriv_const]

theorem lowerSupport_iteratedDeriv {f : ℝ → ℝ} {a : ℝ} (hf : ∀ t<a, f t=0) (k : ℕ) :
    ∀ t<a, iteratedDeriv k f t=0 := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [iteratedDeriv_succ]; exact lowerSupport_deriv ih

theorem contDiff_infty_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv k f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

theorem hasCompactSupport_iteratedDeriv {f : ℝ → ℝ} (hf : HasCompactSupport f) (k : ℕ) :
    HasCompactSupport (iteratedDeriv k f) := by
  induction k with
  | zero => exact hf
  | succ k ih => rw [iteratedDeriv_succ]; exact ih.deriv

theorem realWeightedLogTranslate_history (c : ℕ → ℝ) {f : ℝ → ℝ} {a T t : ℝ}
    (hf : ∀ u<a, f u=0) (ht : t≤T) :
    realWeightedLogTranslate c f t=
      ∑ n ∈ Finset.range (Nat.floor (Real.exp (T-a))+1), c n*f (t-Real.log n) := by
  apply tsum_eq_sum
  intro n hn
  have hn' : Nat.floor (Real.exp (T-a))<n := by
    have : ¬n<Nat.floor (Real.exp (T-a))+1 := by simpa only [Finset.mem_range] using hn
    omega
  have he : Real.exp (T-a)<(n:ℝ) := Nat.lt_of_floor_lt hn'
  have hnpos : 0<(n:ℝ) := (Real.exp_pos _).trans he
  have hlog : T-a<Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr he
  rw [hf _ (by linarith),mul_zero]

theorem realWeightedLogTranslate_contDiff (c : ℕ → ℝ) {f : ℝ → ℝ} {a : ℝ}
    (hf : ∀ u<a, f u=0) (hfd : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (realWeightedLogTranslate c f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ =>
      ∑ n ∈ Finset.range (Nat.floor (Real.exp (t+1-a))+1), c n*f (u-Real.log n)) := by fun_prop
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [eventually_le_nhds (show t<t+1 by linarith)] with u hu
  exact realWeightedLogTranslate_history c hf hu

theorem realWeightedLogTranslate_hasDerivAt (c : ℕ → ℝ) {f : ℝ → ℝ} {a : ℝ}
    (hf : ∀ u<a, f u=0) (hfd : Differentiable ℝ f) (t : ℝ) :
    HasDerivAt (realWeightedLogTranslate c f) (realWeightedLogTranslate c (deriv f) t) t := by
  have hsum : HasDerivAt (fun u : ℝ =>
      ∑ n ∈ Finset.range (Nat.floor (Real.exp (t+1-a))+1), c n*f (u-Real.log n))
      (∑ n ∈ Finset.range (Nat.floor (Real.exp (t+1-a))+1), c n*deriv f (t-Real.log n)) t := by
    apply HasDerivAt.fun_sum
    intro n hn
    have hshift : HasDerivAt (fun u : ℝ => f (u-Real.log n)) (deriv f (t-Real.log n)) t := by
      simpa only [one_smul,Function.comp_def,id_eq] using
        ((hfd (t-Real.log n)).hasDerivAt.scomp t ((hasDerivAt_id t).sub_const (Real.log n)))
    exact hshift.const_mul (c n)
  rw [←realWeightedLogTranslate_history c (lowerSupport_deriv hf) (show t≤t+1 by linarith)] at hsum
  apply hsum.congr_of_eventuallyEq
  filter_upwards [eventually_le_nhds (show t<t+1 by linarith)] with u hu
  exact realWeightedLogTranslate_history c hf hu

theorem realWeightedLogTranslate_deriv (c : ℕ → ℝ) {f : ℝ → ℝ} {a : ℝ}
    (hf : ∀ u<a, f u=0) (hfd : Differentiable ℝ f) :
    deriv (realWeightedLogTranslate c f)=realWeightedLogTranslate c (deriv f) := by
  funext t
  exact (realWeightedLogTranslate_hasDerivAt c hf hfd t).deriv

theorem realWeightedLogTranslate_iteratedDeriv (c : ℕ → ℝ) {f : ℝ → ℝ} {a : ℝ}
    (hf : ∀ u<a, f u=0) (hfd : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) :
    iteratedDeriv k (realWeightedLogTranslate c f)=realWeightedLogTranslate c (iteratedDeriv k f) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDeriv_succ,ih,realWeightedLogTranslate_deriv c (lowerSupport_iteratedDeriv hf k)
      ((contDiff_infty_iteratedDeriv hfd k).differentiable (by norm_num)),←iteratedDeriv_succ]

theorem forwardKernel_contDiff (d ell : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (forwardKernel d ell) := by
  induction ell with
  | zero => exact integerDriveFamily_contDiff d
  | succ ell ih =>
    exact realWeightedLogTranslate_contDiff nativeIntegerCoefficient
      (fun t ht => forwardKernel_zero_before d ell ht) ih

theorem sourceFamily_iteratedDeriv_complexDamping_integrable (d k : ℕ) (z : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (iteratedDeriv k (sourceOrderFamily d) t)) := by
  have hc : Continuous (fun t : ℝ => Complex.ofReal (iteratedDeriv k (sourceOrderFamily d) t)) :=
    Complex.continuous_ofReal.comp (contDiff_infty_iteratedDeriv (sourceFamily_contDiff d) k).continuous
  have hs : HasCompactSupport (fun t : ℝ => Complex.ofReal (iteratedDeriv k (sourceOrderFamily d) t)) :=
    (hasCompactSupport_iteratedDeriv (sourceFamily_hasCompactSupport d) k).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  exact ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-z*(t:ℂ)))).mul hc).integrable_of_hasCompactSupport hs.mul_left

theorem forwardKernel_iteratedDeriv_integrable (d ell k : ℕ) {z : ℂ} (hz : 1/2<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t)) := by
  induction ell with
  | zero =>
    have hsupport : ∀ t < -UniversalSinc.fixedScale, sourceOrderFamily d t=0 := by
      intro t ht
      exact sourceFamily_supported d t (fun h => (not_le.mpr ht) h.1)
    have heq := realWeightedLogTranslate_iteratedDeriv nativeIntegerDriveCoefficient hsupport (sourceFamily_contDiff d) k
    change iteratedDeriv k (integerDriveFamily d)=_ at heq
    change Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (iteratedDeriv k (integerDriveFamily d) t))
    rw [heq]
    have h := (complexWeightedTranslate_integrable_laplace
      (fun n => (nativeIntegerDriveCoefficient n:ℂ))
      (fun t => Complex.ofReal (iteratedDeriv k (sourceOrderFamily d) t)) z
      (sourceFamily_iteratedDeriv_complexDamping_integrable d k z)
      (nativeIntegerDriveLaplaceCoefficient_summable_norm hz)).1
    simpa only [realWeightedLogTranslate,Complex.ofReal_tsum,Complex.ofReal_mul] using h
  | succ ell ih =>
    have heq := realWeightedLogTranslate_iteratedDeriv nativeIntegerCoefficient
      (fun t ht => forwardKernel_zero_before d ell ht) (forwardKernel_contDiff d ell) k
    change iteratedDeriv k (forwardKernel d (ell+1))=_ at heq
    rw [heq]
    have h := (complexWeightedTranslate_integrable_laplace
      (fun n => (nativeIntegerCoefficient n:ℂ))
      (fun t => Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t)) z ih
      (nativeIntegerLaplaceCoefficient_summable_norm hz)).1
    simpa only [realWeightedLogTranslate,Complex.ofReal_tsum,Complex.ofReal_mul] using h



/-- Actual integration by parts. Weighted integrability of both functions
discharges the boundary terms through the full-line integral theorem. -/
theorem bilateralLaplace_real_deriv (f : ℝ → ℝ) (hfd : Differentiable ℝ f) (z : ℂ)
    (hf : Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (f t)))
    (hdf : Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (deriv f t))) :
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (deriv f t))=
      z*(∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (f t)) := by
  have hu (t : ℝ) : HasDerivAt (fun t : ℝ => Complex.exp (-z*(t:ℂ)))
      ((-z)*Complex.exp (-z*(t:ℂ))) t := by
    convert (((hasDerivAt_id (t:ℂ)).const_mul (-z)).cexp).comp_ofReal using 1 <;>
      simp only [id_eq,mul_one,mul_comm]
  have hv (t : ℝ) : HasDerivAt (fun t : ℝ => Complex.ofReal (f t))
      (Complex.ofReal (deriv f t)) t := (hfd t).hasDerivAt.ofReal_comp
  have hscaled : Integrable (fun t : ℝ => ((-z)*Complex.exp (-z*(t:ℂ)))*Complex.ofReal (f t)) := by
    simpa only [mul_assoc] using hf.const_mul (-z)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun t : ℝ => Complex.exp (-z*(t:ℂ)))
    (u' := fun t : ℝ => (-z)*Complex.exp (-z*(t:ℂ)))
    (v := fun t : ℝ => Complex.ofReal (f t)) (v' := fun t : ℝ => Complex.ofReal (deriv f t))
    (fun t _ => hu t) (fun t _ => hv t) hdf hscaled hf
  rw [h]
  have he : (fun t : ℝ => ((-z)*Complex.exp (-z*(t:ℂ)))*Complex.ofReal (f t))=
      fun t : ℝ => (-z)*(Complex.exp (-z*(t:ℂ))*Complex.ofReal (f t)) := by funext t; ring
  rw [he,integral_const_mul]
  ring


theorem forwardKernel_iteratedDeriv_zero_before (d ell k : ℕ) {t : ℝ}
    (ht : t<nativeCausalGap) : iteratedDeriv k (forwardKernel d ell) t=0 :=
  lowerSupport_iteratedDeriv (fun _u hu => forwardKernel_zero_before d ell hu) k t ht

theorem forwardKernel_iteratedDeriv_physical_laplace (d ell k : ℕ) {z : ℂ} (hz : 1/2<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t))=
      z^k*forwardKernelTransformGerm d ell z := by
  refine ⟨forwardKernel_iteratedDeriv_integrable d ell k hz,?_⟩
  induction k with
  | zero =>
    simpa only [iteratedDeriv_zero,pow_zero,one_mul,forwardKernelLaplace] using
      (forwardKernel_integrable_laplace d ell hz).2
  | succ k ih =>
    have hdf : Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*
        Complex.ofReal (deriv (iteratedDeriv k (forwardKernel d ell)) t)) := by
      simpa only [iteratedDeriv_succ] using forwardKernel_iteratedDeriv_integrable d ell (k+1) hz
    have he := bilateralLaplace_real_deriv (iteratedDeriv k (forwardKernel d ell))
      ((contDiff_infty_iteratedDeriv (forwardKernel_contDiff d ell) k).differentiable (by norm_num))
      z (forwardKernel_iteratedDeriv_integrable d ell k hz) hdf
    rw [iteratedDeriv_succ,he,ih,pow_succ]
    ring

theorem forwardKernel_iteratedDeriv_laplace_entire (d ell k : ℕ) (hd : ell≤d)
    {z : ℂ} (hz : 1/2<z.re) :
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t))=
      z^k*forwardKernelEntireContinuation d ell z := by
  have hz' : z≠1/2 := by intro he; rw [he] at hz; norm_num at hz
  rw [(forwardKernel_iteratedDeriv_physical_laplace d ell k hz).2,
    forwardKernelEntireContinuation_agrees d ell hd hz']


end Zeta23.OPICAFollowup
