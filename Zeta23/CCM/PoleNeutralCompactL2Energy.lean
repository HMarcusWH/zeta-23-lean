import Zeta23.CCM.PoleNeutralCompactL2Regularity
import Zeta23.CCM.CompactComplexIntegralFTC
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Sharp compact pole-inverse energy and norm bounds for general L2 input

Absolute continuity of the literal finite primitives justifies complex
integration by parts for an L2 source. No smoothness, weak equation or energy
identity is an input. The true L2 norm bound is four.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Zeta23.CCM

private theorem polePrimitive_ac (s r : ℝ) {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    AbsolutelyContinuousOnInterval (nativePolePrimitive s r f) (-s) s :=
  complex_intervalPrimitive_absolutelyContinuous
    ((nativePoleWeightedSource_locallyIntegrable hf r).integrableOn_isCompact
      isCompact_uIcc).intervalIntegrable (by simp)

private theorem poleExponential_ac (r a b : ℝ) :
    AbsolutelyContinuousOnInterval (nativePoleExponential r) a b := by
  have h : ContDiff ℝ 1 (nativePoleExponential r) :=
    Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp (contDiff_const.mul contDiff_id))
  exact h.contDiffOn.absolutelyContinuousOnInterval

/-- Absolute continuity of the actual first two jet representatives. -/
theorem nativePoleCompactInverse_jet_absolutelyContinuous (s : ℝ) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) :
    AbsolutelyContinuousOnInterval (nativePoleCompactInverse s f) (-s) s ∧
      AbsolutelyContinuousOnInterval (nativePoleCompactInverseDerivative s f) (-s) s := by
  have hp : AbsolutelyContinuousOnInterval
      (fun x => nativePoleExponential (1 / 2) x * nativePolePrimitive s (-1 / 2) f x) (-s) s := by
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      (poleExponential_ac (1 / 2) (-s) s).smul (polePrimitive_ac s (-1 / 2) hf)
  have hm : AbsolutelyContinuousOnInterval
      (fun x => nativePoleExponential (-1 / 2) x * nativePolePrimitive s (1 / 2) f x) (-s) s := by
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      (poleExponential_ac (-1 / 2) (-s) s).smul (polePrimitive_ac s (1 / 2) hf)
  exact ⟨hp.sub hm, (hp.add hm).const_smul (1 / 2 : ℂ)⟩

private theorem compact_intervalIntegral_eq_integral {s : ℝ} (hs : 0 ≤ s)
    {v : ℝ → ℂ} (hv : ∀ x, x ∉ Icc (-s) s → v x = 0) :
    (∫ x in (-s)..s, v x) = ∫ x : ℝ, v x := by
  rw [intervalIntegral.integral_of_le (by linarith : -s ≤ s), ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hv

/-- Exact complex energy identity for the actual compact inverse of a
general compact pole-neutral L2 source. -/
theorem nativePoleCompactInverse_memLp_energy_identity {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
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
  obtain ⟨hg, hd, hforce⟩ := nativePoleCompactInverse_memLp_jet_representatives hs hf
    hsupport hplus hminus
  have hgg : Integrable (fun x : ℝ => star (g x) * g x) := hg.star.integrable_mul hg
  have hgf : Integrable (fun x : ℝ => star (g x) * f x) := hg.star.integrable_mul hf
  have hdd : Integrable (fun x : ℝ => star (d x) * d x) := hd.star.integrable_mul hd
  have hgdforce : Integrable (fun x : ℝ => star (g x) * ((1 / 4 : ℂ) * g x + f x)) :=
    hg.star.integrable_mul hforce
  obtain ⟨hgAC, hdAC⟩ := nativePoleCompactInverse_jet_absolutelyContinuous s hf
  have hstarAC : AbsolutelyContinuousOnInterval (fun x : ℝ => star (g x)) (-s) s := by
    simpa only [AbsolutelyContinuousOnInterval, dist_star_star] using hgAC
  have hprodAC : AbsolutelyContinuousOnInterval (fun x : ℝ => star (g x) * d x) (-s) s := by
    simpa only [Pi.smul_apply, smul_eq_mul] using! hstarAC.smul hdAC
  have hderiv : ∀ᵐ x : ℝ, x ∈ uIcc (-s) s →
      HasDerivAt (fun x : ℝ => star (g x) * d x)
        (star (d x) * d x + star (g x) * ((1 / 4 : ℂ) * g x + f x)) x := by
    filter_upwards [nativePoleCompactInverse_ae_hasDerivAt s hf,
      nativePoleCompactInverseDerivative_ae_hasDerivAt s hf] with x hx hdx _
    exact hx.star.mul hdx
  have hFTC := complex_integral_eq_sub_of_ac_ae hprodAC
    (hdd.add hgdforce).intervalIntegrable hderiv
  have htraces := nativePoleCompactInverse_memLp_clamped_values hs hf hsupport hplus hminus
  change g (-s) = 0 ∧ g s = 0 ∧ d (-s) = 0 ∧ d s = 0 at htraces
  simp only [htraces.1, htraces.2.1, star_zero, zero_mul, sub_self] at hFTC
  change (∫ x in (-s)..s, star (d x) * d x +
    star (g x) * ((1 / 4 : ℂ) * g x + f x)) = 0 at hFTC
  have hexpand : (fun x : ℝ => star (d x) * d x +
      star (g x) * ((1 / 4 : ℂ) * g x + f x)) = fun x : ℝ =>
      star (d x) * d x + (1 / 4 : ℂ) * (star (g x) * g x) + star (g x) * f x := by
    funext x
    ring
  have hsum : IntervalIntegrable (fun x : ℝ => star (d x) * d x +
      (1 / 4 : ℂ) * (star (g x) * g x)) volume (-s) s :=
    (hdd.add (hgg.const_mul (1 / 4 : ℂ))).intervalIntegrable
  rw [hexpand, intervalIntegral.integral_add
      hsum hgf.intervalIntegrable,
    intervalIntegral.integral_add hdd.intervalIntegrable
      (hgg.const_mul (1 / 4 : ℂ)).intervalIntegrable,
    intervalIntegral.integral_const_mul] at hFTC
  have hgzero (x : ℝ) (hx : x ∉ Icc (-s) s) : g x = 0 :=
    nativePoleCompactInverse_zero_outside hs hsupport hplus hminus hx
  have hdzero (x : ℝ) (hx : x ∉ Icc (-s) s) : d x = 0 :=
    nativePoleCompactInverseDerivative_zero_outside hs hsupport hplus hminus hx
  rw [compact_intervalIntegral_eq_integral hs (v := fun x => star (d x) * d x)
      (fun x hx => by rw [hdzero x hx, star_zero, zero_mul]),
    compact_intervalIntegral_eq_integral hs (v := fun x => star (g x) * g x)
      (fun x hx => by rw [hgzero x hx, star_zero, zero_mul]),
    compact_intervalIntegral_eq_integral hs (v := fun x => star (g x) * f x)
      (fun x hx => by rw [hgzero x hx, star_zero, zero_mul])] at hFTC
  change (∫ x : ℝ, star (g x) * f x) =
    -(∫ x : ℝ, star (d x) * d x) - (1 / 4 : ℂ) * (∫ x : ℝ, star (g x) * g x)
  linear_combination hFTC

private theorem integral_star_mul_eq_inner {u v : ℝ → ℂ}
    (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    (∫ x : ℝ, star (u x) * v x) = inner ℂ (hu.toLp u) (hv.toLp v) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hu.coeFn_toLp, hv.coeFn_toLp] with x hux hvx
  rw [hux, hvx]
  simp [RCLike.inner_apply, mul_comm]

/-- The sharp inverse norm estimate for actual general compact L2 data. -/
theorem nativePoleCompactInverse_l2_norm_le_four_of_memLp {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ x : ℝ, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    (eLpNorm (nativePoleCompactInverse s f) 2 volume).toReal ≤
      4 * (eLpNorm f 2 volume).toReal := by
  obtain ⟨hg, hd, _⟩ := nativePoleCompactInverse_memLp_jet_representatives hs hf
    hsupport hplus hminus
  let G := hg.toLp (nativePoleCompactInverse s f)
  let F := hf.toLp f
  let V := hd.toLp (nativePoleCompactInverseDerivative s f)
  have he := nativePoleCompactInverse_memLp_energy_identity hs hf hsupport hplus hminus
  rw [integral_star_mul_eq_inner hg hf, integral_star_mul_eq_inner hd hd,
    integral_star_mul_eq_inner hg hg] at he
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
      apply (mul_le_mul_iff_right₀ hpos).mp
      nlinarith [sq_nonneg ‖V‖]
  simpa only [G, F, Lp.norm_toLp] using hbound

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePoleCompactInverse_jet_absolutelyContinuous
#print axioms Zeta23.CCM.nativePoleCompactInverse_memLp_energy_identity
#print axioms Zeta23.CCM.nativePoleCompactInverse_l2_norm_le_four_of_memLp
