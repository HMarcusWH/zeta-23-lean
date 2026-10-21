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

end Zeta23.OPICAFollowup
