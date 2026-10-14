import Zeta23.CCM.OriginalSincCompactPotential
import Zeta23.CCM.OriginalSincNativeSource

/-!
# Actual zeroth and first elementary moments of the original source

Integration by parts keeps the first weighted moment as well as the ordinary
pole moment. Two applications of P cancel both at r = ±1/2. These are actual
integrals of the fixed source, needed for the continuum integer-drive
cancellation; no decay, stable-input membership or inverse is assumed.
-/

noncomputable section

open MeasureTheory

namespace Zeta23.CCM

def nativePoleMoment (r : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, nativePoleExponential r x * f x

def nativePoleFirstMoment (r : ℝ) (f : ℝ → ℂ) : ℂ :=
  ∫ x : ℝ, (x : ℂ) * nativePoleExponential r x * f x

private theorem continuous_poleExp (r : ℝ) : Continuous (nativePoleExponential r) :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_nativePoleExponential r x).continuousAt)

private theorem poleMoment_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (r : ℝ) :
    Integrable (fun x : ℝ => nativePoleExponential r x * f x) :=
  ((continuous_poleExp r).mul hf).integrable_of_hasCompactSupport hc.mul_left

private theorem poleFirstMoment_integrable {f : ℝ → ℂ} (hf : Continuous f)
    (hc : HasCompactSupport f) (r : ℝ) :
    Integrable (fun x : ℝ => (x : ℂ) * nativePoleExponential r x * f x) :=
  ((Complex.continuous_ofReal.mul (continuous_poleExp r)).mul hf).integrable_of_hasCompactSupport
    hc.mul_left

theorem nativePoleMoment_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (r : ℝ) :
    nativePoleMoment r (deriv f) = -(r : ℂ) * nativePoleMoment r f := by
  have hd : ∀ x, HasDerivAt f (deriv f x) x :=
    fun x => (hf.differentiable (by norm_num) x).hasDerivAt
  have hE := continuous_poleExp r
  have hD := hf.continuous_deriv le_rfl
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := deriv f) (v := nativePoleExponential r)
    (v' := fun x => (r : ℂ) * nativePoleExponential r x)
    (fun x _ => hd x) (fun x _ => hasDerivAt_nativePoleExponential r x)
    ((hf.continuous.mul (continuous_const.mul hE)).integrable_of_hasCompactSupport hc.mul_right)
    ((hD.mul hE).integrable_of_hasCompactSupport hc.deriv.mul_right)
    ((hf.continuous.mul hE).integrable_of_hasCompactSupport hc.mul_right)
  have hleft : (fun x : ℝ => f x * ((r : ℂ) * nativePoleExponential r x)) =
      fun x => (r : ℂ) * (nativePoleExponential r x * f x) := by funext x; ring
  have hright : (fun x : ℝ => deriv f x * nativePoleExponential r x) =
      fun x => nativePoleExponential r x * deriv f x := by funext x; ring
  rw [hleft, hright, Zeta23.integral_const_mul_C] at key
  change (r : ℂ) * nativePoleMoment r f = -nativePoleMoment r (deriv f) at key
  simpa only [neg_neg] using (congrArg (fun z : ℂ => -z) key).symm

theorem nativePoleFirstMoment_deriv {f : ℝ → ℂ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (r : ℝ) :
    nativePoleFirstMoment r (deriv f) =
      -nativePoleMoment r f - (r : ℂ) * nativePoleFirstMoment r f := by
  have hd : ∀ x, HasDerivAt f (deriv f x) x :=
    fun x => (hf.differentiable (by norm_num) x).hasDerivAt
  have hE := continuous_poleExp r
  have hXE := Complex.continuous_ofReal.mul hE
  have hD := hf.continuous_deriv le_rfl
  have hweight (x : ℝ) :
      HasDerivAt (fun y : ℝ => (y : ℂ) * nativePoleExponential r y)
        (nativePoleExponential r x + (r : ℂ) * ((x : ℂ) * nativePoleExponential r x)) x := by
    have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 x := by
      simpa only [id_eq, Complex.ofReal_one] using (hasDerivAt_id x).ofReal_comp
    simpa only [one_mul, mul_assoc, mul_comm, mul_left_comm] using
      hid.mul (hasDerivAt_nativePoleExponential r x)
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := deriv f)
    (v := fun x : ℝ => (x : ℂ) * nativePoleExponential r x)
    (v' := fun x => nativePoleExponential r x +
      (r : ℂ) * ((x : ℂ) * nativePoleExponential r x))
    (fun x _ => hd x) (fun x _ => hweight x)
    ((hf.continuous.mul (hE.add (continuous_const.mul hXE))).integrable_of_hasCompactSupport hc.mul_right)
    ((hD.mul hXE).integrable_of_hasCompactSupport hc.deriv.mul_right)
    ((hf.continuous.mul hXE).integrable_of_hasCompactSupport hc.mul_right)
  have hleft : (fun x : ℝ => f x * (nativePoleExponential r x +
      (r : ℂ) * ((x : ℂ) * nativePoleExponential r x))) = fun x =>
      nativePoleExponential r x * f x +
        (r : ℂ) * ((x : ℂ) * nativePoleExponential r x * f x) := by funext x; ring
  have hright : (fun x : ℝ => deriv f x * ((x : ℂ) * nativePoleExponential r x)) =
      fun x => (x : ℂ) * nativePoleExponential r x * deriv f x := by funext x; ring
  rw [hleft, hright, integral_add (poleMoment_integrable hf.continuous hc r)
    ((poleFirstMoment_integrable hf.continuous hc r).const_mul _),
    Zeta23.integral_const_mul_C] at key
  change nativePoleMoment r f + (r : ℂ) * nativePoleFirstMoment r f =
    -nativePoleFirstMoment r (deriv f) at key
  calc
    nativePoleFirstMoment r (deriv f) =
        -(nativePoleMoment r f + (r : ℂ) * nativePoleFirstMoment r f) := by
      simpa only [neg_neg] using (congrArg (fun z : ℂ => -z) key).symm
    _ = -nativePoleMoment r f - (r : ℂ) * nativePoleFirstMoment r f := by ring

theorem nativePoleMoment_differential {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (r : ℝ) :
    nativePoleMoment r (universalSincDifferential f) =
      ((r : ℂ) ^ 2 - 1 / 4) * nativePoleMoment r f := by
  have hD2 := hf.deriv'.continuous_deriv le_rfl
  have heq : (fun x : ℝ => nativePoleExponential r x * universalSincDifferential f x) =
      fun x => nativePoleExponential r x * deriv (deriv f) x -
        (1 / 4 : ℂ) * (nativePoleExponential r x * f x) := by
    funext x
    unfold universalSincDifferential
    ring
  unfold nativePoleMoment
  rw [heq, integral_sub (poleMoment_integrable hD2 hc.deriv.deriv r)
    ((poleMoment_integrable hf.continuous hc r).const_mul _),
    Zeta23.integral_const_mul_C]
  change nativePoleMoment r (deriv (deriv f)) - (1 / 4 : ℂ) * nativePoleMoment r f = _
  rw [nativePoleMoment_deriv hf.deriv' hc.deriv,
    nativePoleMoment_deriv (hf.of_le (by norm_num)) hc]
  change -(r : ℂ) * (-(r : ℂ) * nativePoleMoment r f) -
    (1 / 4 : ℂ) * nativePoleMoment r f =
      ((r : ℂ) ^ 2 - 1 / 4) * nativePoleMoment r f
  ring

theorem nativePoleFirstMoment_differential {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (r : ℝ) :
    nativePoleFirstMoment r (universalSincDifferential f) =
      2 * (r : ℂ) * nativePoleMoment r f +
        ((r : ℂ) ^ 2 - 1 / 4) * nativePoleFirstMoment r f := by
  have hD2 := hf.deriv'.continuous_deriv le_rfl
  have heq : (fun x : ℝ => (x : ℂ) * nativePoleExponential r x *
      universalSincDifferential f x) = fun x : ℝ =>
      (x : ℂ) * nativePoleExponential r x * deriv (deriv f) x -
        (1 / 4 : ℂ) * ((x : ℂ) * nativePoleExponential r x * f x) := by
    funext x
    unfold universalSincDifferential
    ring
  unfold nativePoleFirstMoment
  rw [heq, integral_sub (poleFirstMoment_integrable hD2 hc.deriv.deriv r)
    ((poleFirstMoment_integrable hf.continuous hc r).const_mul _),
    Zeta23.integral_const_mul_C]
  change nativePoleFirstMoment r (deriv (deriv f)) -
    (1 / 4 : ℂ) * nativePoleFirstMoment r f = _
  rw [nativePoleFirstMoment_deriv hf.deriv' hc.deriv,
    nativePoleMoment_deriv (hf.of_le (by norm_num)) hc,
    nativePoleFirstMoment_deriv (hf.of_le (by norm_num)) hc]
  change -(-(r : ℂ) * nativePoleMoment r f) -
    (r : ℂ) * (-nativePoleMoment r f - (r : ℂ) * nativePoleFirstMoment r f) -
      (1 / 4 : ℂ) * nativePoleFirstMoment r f =
        2 * (r : ℂ) * nativePoleMoment r f +
          ((r : ℂ) ^ 2 - 1 / 4) * nativePoleFirstMoment r f
  ring

theorem universalSincSecondKernel_first_elementary_moments {s : ℝ} (hs : 0 < s) :
    nativePoleFirstMoment (1 / 2) (universalSincSecondKernel s) = 0 ∧
      nativePoleFirstMoment (-1 / 2) (universalSincSecondKernel s) = 0 := by
  have hq : ContDiff ℝ 2 (UniversalSinc.originalDensityComplex s) := by
    rw [← UniversalSinc.inverseCandidate_eq_originalDensityComplex hs]
    exact (UniversalSinc.contDiff_inverseCandidate hs).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hqc := UniversalSinc.originalDensityComplex_hasCompactSupport hs
  have hk : ContDiff ℝ 2 (universalSincKernel s) :=
    (universalSincKernel_contDiff hs).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hkc := universalSincKernel_hasCompactSupport hs
  have hmoment (r : ℝ) :
      nativePoleMoment r (universalSincKernel s) =
        ((r : ℂ) ^ 2 - 1 / 4) * nativePoleMoment r (UniversalSinc.originalDensityComplex s) :=
    nativePoleMoment_differential hq hqc r
  constructor
  all_goals
    unfold universalSincSecondKernel
    rw [nativePoleFirstMoment_differential hk hkc, hmoment]
    norm_num

/-- The actual real source has both elementary pole moments and both first
weighted elementary moments zero. -/
theorem nativeOriginalSource_weighted_elementary_moments :
    (∫ x : ℝ, Real.exp (x / 2) * nativeOriginalSource x) = 0 ∧
    (∫ x : ℝ, Real.exp (-x / 2) * nativeOriginalSource x) = 0 ∧
    (∫ x : ℝ, x * Real.exp (x / 2) * nativeOriginalSource x) = 0 ∧
    (∫ x : ℝ, x * Real.exp (-x / 2) * nativeOriginalSource x) = 0 := by
  have hs := UniversalSinc.fixedScale_pos
  have hm := universalSincSecondKernel_elementary_moments hs
  have hfirst := universalSincSecondKernel_first_elementary_moments hs
  have hcont := (universalSincSecondKernel_contDiff hs).continuous
  have hc := universalSincSecondKernel_hasCompactSupport hs
  have h0 (r : ℝ) : (∫ x : ℝ, Real.exp (r * x) * nativeOriginalSource x) =
      (nativePoleMoment r (universalSincSecondKernel UniversalSinc.fixedScale)).re := by
    change _ = RCLike.re (∫ x : ℝ, nativePoleExponential r x *
      universalSincSecondKernel UniversalSinc.fixedScale x)
    rw [← integral_re (poleMoment_integrable hcont hc r)]
    apply integral_congr_ae
    filter_upwards with x
    simp only [RCLike.re_eq_complex_re, nativePoleMoment, nativeOriginalSource, universalSincSecondSource,
      nativePoleExponential, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  have h1 (r : ℝ) : (∫ x : ℝ, x * Real.exp (r * x) * nativeOriginalSource x) =
      (nativePoleFirstMoment r (universalSincSecondKernel UniversalSinc.fixedScale)).re := by
    change _ = RCLike.re (∫ x : ℝ, (x : ℂ) * nativePoleExponential r x *
      universalSincSecondKernel UniversalSinc.fixedScale x)
    rw [← integral_re (poleFirstMoment_integrable hcont hc r)]
    apply integral_congr_ae
    filter_upwards with x
    simp [RCLike.re_eq_complex_re, nativeOriginalSource, universalSincSecondSource,
      nativePoleExponential, Complex.mul_re, Complex.mul_im]
  have hmplus : nativePoleMoment (1 / 2)
      (universalSincSecondKernel UniversalSinc.fixedScale) = 0 := hm.1
  have hmminus : nativePoleMoment (-1 / 2)
      (universalSincSecondKernel UniversalSinc.fixedScale) = 0 := hm.2
  simpa only [Complex.zero_re, div_eq_mul_inv, one_mul, neg_mul, mul_neg,
    mul_comm, mul_left_comm, mul_assoc]
    using And.intro ((h0 (1 / 2)).trans (congrArg Complex.re hmplus))
      (And.intro ((h0 (-1 / 2)).trans (congrArg Complex.re hmminus))
        (And.intro ((h1 (1 / 2)).trans (congrArg Complex.re hfirst.1))
          ((h1 (-1 / 2)).trans (congrArg Complex.re hfirst.2))))

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePoleMoment_deriv
#print axioms Zeta23.CCM.nativePoleFirstMoment_deriv
#print axioms Zeta23.CCM.nativePoleMoment_differential
#print axioms Zeta23.CCM.nativePoleFirstMoment_differential
#print axioms Zeta23.CCM.universalSincSecondKernel_first_elementary_moments
#print axioms Zeta23.CCM.nativeOriginalSource_weighted_elementary_moments
