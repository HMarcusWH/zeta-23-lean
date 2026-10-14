import Zeta23.CCM.OriginalSincCompactPotential
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The actual compact pole inverse has L2 bound four

The inverse is the existing finite-primitive construction. Its differential
equation and compact support prove the energy identity by integration by
parts; neither that identity nor an inverse bound is an input. The factor
four then follows from Cauchy--Schwarz in the actual L2 space.

The source here is continuous with compact support and both elementary
moments zero, so the constructed inverse is C2. The final specialization
uses the actual smooth original twice pole-killed source. Extension to an
arbitrary compact L2 source and its Sobolev/traces interface remains OPEN.
-/

noncomputable section

open Set MeasureTheory
open scoped ComplexConjugate

namespace Zeta23.CCM

private theorem interval_supported_hasCompactSupport {s : ℝ} {f : ℝ → ℂ}
    (hsupport : ∀ x : ℝ, x ∉ Icc (-s) s → f x = 0) : HasCompactSupport f := by
  apply HasCompactSupport.intro (K := Icc (-s) s) isCompact_Icc
  exact hsupport

theorem nativePoleCompactInverse_memLp_two {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : Continuous f) (hsupport : ∀ x : ℝ, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    MemLp (nativePoleCompactInverse s f) 2 volume :=
  (nativePoleCompactInverse_continuous s hf).memLp_of_hasCompactSupport
    (nativePoleCompactInverse_hasCompactSupport hs hsupport hplus hminus)

theorem nativePoleCompactInverseDerivative_memLp_two {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : Continuous f)
    (hsupport : ∀ x : ℝ, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    MemLp (nativePoleCompactInverseDerivative s f) 2 volume :=
  (nativePoleCompactInverseDerivative_continuous s hf).memLp_of_hasCompactSupport
    (nativePoleCompactInverseDerivative_hasCompactSupport hs hsupport hplus hminus)

/-- The exact complex energy identity for the constructed compact inverse.
The first derivative is its existing explicit derivative expression. -/
theorem nativePoleCompactInverse_energy_identity {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : Continuous f)
    (hsupport : ∀ x : ℝ, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    (∫ x : ℝ, star (nativePoleCompactInverse s f x) * f x) =
      -(∫ x : ℝ, star (nativePoleCompactInverseDerivative s f x) *
        nativePoleCompactInverseDerivative s f x) -
      (1 / 4 : ℂ) * (∫ x : ℝ, star (nativePoleCompactInverse s f x) *
        nativePoleCompactInverse s f x) := by
  let g := nativePoleCompactInverse s f
  let d := nativePoleCompactInverseDerivative s f
  have hgc : Continuous g := nativePoleCompactInverse_continuous s hf
  have hdc : Continuous d := nativePoleCompactInverseDerivative_continuous s hf
  have hgs : HasCompactSupport g :=
    nativePoleCompactInverse_hasCompactSupport hs hsupport hplus hminus
  have hds : HasCompactSupport d :=
    nativePoleCompactInverseDerivative_hasCompactSupport hs hsupport hplus hminus
  have hfs : HasCompactSupport f := interval_supported_hasCompactSupport hsupport
  have hforce : HasCompactSupport (fun x : ℝ => (1 / 4 : ℂ) * g x + f x) :=
    (hgs.mul_left (f := fun _ => (1 / 4 : ℂ))).add hfs
  have hgg : Integrable (fun x : ℝ => star (g x) * g x) :=
    (hgc.star.mul hgc).integrable_of_hasCompactSupport hgs.mul_left
  have hgf : Integrable (fun x : ℝ => star (g x) * f x) :=
    (hgc.star.mul hf).integrable_of_hasCompactSupport hfs.mul_left
  have hdd : Integrable (fun x : ℝ => star (d x) * d x) :=
    (hdc.star.mul hdc).integrable_of_hasCompactSupport hds.mul_left
  have hgd : Integrable (fun x : ℝ => star (g x) * d x) :=
    (hgc.star.mul hdc).integrable_of_hasCompactSupport hds.mul_left
  have hgforce : Integrable (fun x : ℝ => star (g x) * ((1 / 4 : ℂ) * g x + f x)) :=
    (hgc.star.mul ((continuous_const.mul hgc).add hf)).integrable_of_hasCompactSupport
      hforce.mul_left
  have hibp := MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun x : ℝ => star (g x)) (v := d)
    (u' := fun x : ℝ => star (d x))
    (v' := fun x : ℝ => (1 / 4 : ℂ) * g x + f x)
    (fun x _ => (nativePoleCompactInverse_hasDerivAt s hf x).star)
    (fun x _ => nativePoleCompactInverseDerivative_hasDerivAt s hf x)
    hgforce hdd hgd
  have hexpand : (fun x : ℝ => star (g x) * ((1 / 4 : ℂ) * g x + f x)) =
      fun x : ℝ => (1 / 4 : ℂ) * (star (g x) * g x) + star (g x) * f x := by
    funext x
    ring
  rw [hexpand, integral_add (hgg.const_mul (1 / 4 : ℂ)) hgf,
    integral_const_mul] at hibp
  change (∫ x : ℝ, star (g x) * f x) =
    -(∫ x : ℝ, star (d x) * d x) - (1 / 4 : ℂ) * (∫ x : ℝ, star (g x) * g x)
  linear_combination hibp

private theorem integral_star_mul_eq_inner_toLp {u v : ℝ → ℂ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    (∫ x : ℝ, star (u x) * v x) = inner ℂ (hu.toLp u) (hv.toLp v) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hux hvx
  rw [hux, hvx]
  simp [RCLike.inner_apply, mul_comm]

/-- Actual L2 norm bound, with finite L2 membership proved in this theorem.
No energy, inverse norm, or differential equation is a caller premise. -/
theorem nativePoleCompactInverse_l2_norm_le_four {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : Continuous f)
    (hsupport : ∀ x : ℝ, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    (eLpNorm (nativePoleCompactInverse s f) 2 volume).toReal ≤
      4 * (eLpNorm f 2 volume).toReal := by
  have hg := nativePoleCompactInverse_memLp_two hs hf hsupport hplus hminus
  have hd := nativePoleCompactInverseDerivative_memLp_two hs hf hsupport hplus hminus
  have hfl : MemLp f 2 volume :=
    hf.memLp_of_hasCompactSupport (interval_supported_hasCompactSupport hsupport)
  let G := hg.toLp (nativePoleCompactInverse s f)
  let F := hfl.toLp f
  let V := hd.toLp (nativePoleCompactInverseDerivative s f)
  have he := nativePoleCompactInverse_energy_identity hs hf hsupport hplus hminus
  rw [integral_star_mul_eq_inner_toLp hg hfl,
    integral_star_mul_eq_inner_toLp hd hd,
    integral_star_mul_eq_inner_toLp hg hg] at he
  change inner ℂ G F = -inner ℂ V V - (1 / 4 : ℂ) * inner ℂ G G at he
  have hgg : (inner ℂ G G).re = ‖G‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) G).symm
  have hvv : (inner ℂ V V).re = ‖V‖ ^ 2 := by
    simpa only [RCLike.re_eq_complex_re] using (norm_sq_eq_re_inner (𝕜 := ℂ) V).symm
  have hquarter : (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) := by norm_num
  rw [hquarter] at he
  have henergy : (inner ℂ G F).re = -‖V‖ ^ 2 - (1 / 4 : ℝ) * ‖G‖ ^ 2 := by
    simpa only [Complex.neg_re, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, hgg, hvv] using congrArg Complex.re he
  have hcs : -(inner ℂ G F).re ≤ ‖G‖ * ‖F‖ := by
    simpa only [inner_neg_right, Complex.neg_re, norm_neg, RCLike.re_eq_complex_re] using
      (re_inner_le_norm (𝕜 := ℂ) G (-F))
  have hbound : ‖G‖ ≤ 4 * ‖F‖ := by
    by_cases hz : ‖G‖ = 0
    · rw [hz]
      positivity
    · have hpos : 0 < ‖G‖ := lt_of_le_of_ne (norm_nonneg G) (Ne.symm hz)
      apply (mul_le_mul_left hpos).mp
      nlinarith [sq_nonneg ‖V‖]
  simpa only [G, F, Lp.norm_toLp] using hbound

/-- The same bound for the actual smooth twice pole-killed original source. -/
theorem originalSincCompactPotential_l2_norm_le_four {s : ℝ} (hs : 0 < s) :
    (eLpNorm (originalSincCompactPotential s) 2 volume).toReal ≤
      4 * (eLpNorm (universalSincSecondKernel s) 2 volume).toReal := by
  have hm := universalSincSecondKernel_elementary_moments hs
  exact nativePoleCompactInverse_l2_norm_le_four hs.le
    (universalSincSecondKernel_contDiff hs).continuous
    (fun x hx => universalSincSecondKernel_zero_outside hs hx) hm.1 hm.2

/-- The prescribed original scale is used literally. -/
theorem fixedOriginalSincCompactPotential_l2_norm_le_four :
    (eLpNorm (originalSincCompactPotential UniversalSinc.fixedScale) 2 volume).toReal ≤
      4 * (eLpNorm (universalSincSecondKernel UniversalSinc.fixedScale) 2 volume).toReal :=
  originalSincCompactPotential_l2_norm_le_four UniversalSinc.fixedScale_pos

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePoleCompactInverse_memLp_two
#print axioms Zeta23.CCM.nativePoleCompactInverseDerivative_memLp_two
#print axioms Zeta23.CCM.nativePoleCompactInverse_energy_identity
#print axioms Zeta23.CCM.nativePoleCompactInverse_l2_norm_le_four
#print axioms Zeta23.CCM.originalSincCompactPotential_l2_norm_le_four
#print axioms Zeta23.CCM.fixedOriginalSincCompactPotential_l2_norm_le_four
