import Zeta23.CCM.CanonicalApertureAnalyticPrimitives
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Complex.CauchyIntegral

noncomputable section

namespace Zeta23.CCM

open Complex Set Filter
open scoped Topology Interval

/-! # FIRST-BAD-RIGIDITY-E4-A4R1b: common archimedean aperture domain

The fixed-unit aperture integrals sample the regularized archimedean scale at
`z * t` with `t ∈ [0,1]`.  The open strip `|Im z| < π` is a canonical common
domain for this archimedean layer: it contains the full real axis, is convex,
and is stable under multiplication by `t ∈ [0,1]`.

Inside this strip the divided hyperbolic sine denominator never vanishes.  This
upgrades the previously local-at-zero analyticity of
`complexRegularizedArchScale` to analyticity throughout one explicit connected
domain.  This file concerns only the archimedean continuation layer; it makes
no claim that the full frozen source is analytic on the same strip.
-/

/-- Canonical zero-free strip for the archimedean divided-sinh denominator. -/
def complexArchSafeStrip : Set ℂ :=
  {z : ℂ | |z.im| < Real.pi}

/-- The archimedean safe strip is open. -/
theorem isOpen_complexArchSafeStrip : IsOpen complexArchSafeStrip := by
  rw [complexArchSafeStrip]
  exact isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

/-- The archimedean safe strip is convex as a real subset of `ℂ`. -/
theorem convex_complexArchSafeStrip : Convex ℝ complexArchSafeStrip := by
  rw [complexArchSafeStrip]
  simpa only [abs_lt] using
    (convex_halfSpace_im_gt (-Real.pi)).inter (convex_halfSpace_im_lt Real.pi)

/-- Hence the archimedean safe strip is preconnected. -/
theorem isPreconnected_complexArchSafeStrip :
    IsPreconnected complexArchSafeStrip :=
  convex_complexArchSafeStrip.isPreconnected

@[simp] theorem zero_mem_complexArchSafeStrip :
    (0 : ℂ) ∈ complexArchSafeStrip := by
  simp [complexArchSafeStrip, Real.pi_pos]

/-- The strip is connected; this is recorded now because later determinant
arguments need one connected analytic domain rather than unrelated local
neighborhoods. -/
theorem isConnected_complexArchSafeStrip :
    IsConnected complexArchSafeStrip :=
  convex_complexArchSafeStrip.isConnected ⟨0, zero_mem_complexArchSafeStrip⟩

/-- Every real aperture lies in the archimedean safe strip. -/
@[simp] theorem ofReal_mem_complexArchSafeStrip (L : ℝ) :
    (L : ℂ) ∈ complexArchSafeStrip := by
  simp [complexArchSafeStrip, Real.pi_pos]

/-- The strip is stable under the fixed-unit sampling map `z ↦ z*t` for
`t ∈ [0,1]`. -/
theorem mul_Icc_mem_complexArchSafeStrip
    {z : ℂ} (hz : z ∈ complexArchSafeStrip)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    z * (t : ℂ) ∈ complexArchSafeStrip := by
  rw [complexArchSafeStrip] at hz ⊢
  have ht0 : 0 ≤ t := ht.1
  have ht1 : t ≤ 1 := ht.2
  have him : (z * (t : ℂ)).im = z.im * t := by
    simp [Complex.mul_im]
  rw [him, abs_mul, abs_of_nonneg ht0]
  calc
    |z.im| * t ≤ |z.im| * 1 :=
      mul_le_mul_of_nonneg_left ht1 (abs_nonneg z.im)
    _ = |z.im| := by ring
    _ < Real.pi := hz

/-- The complex divided hyperbolic slope has no zero in the safe strip.
At the origin the divided slope equals one; away from the origin, a hypothetical
zero would force `exp z = exp (-z)`, and exponential injectivity on the
fundamental strip then forces `z = 0`. -/
theorem complexArchSinhSlope_ne_zero_of_mem_strip
    {z : ℂ} (hz : z ∈ complexArchSafeStrip) :
    complexArchSinhSlope z ≠ 0 := by
  by_cases hz0 : z = 0
  · subst z
    simp
  · intro hslope
    have hsinh : Complex.sinh z = 0 := by
      rw [complexArchSinhSlope, dslope_of_ne _ hz0] at hslope
      simpa [slope, hz0] using hslope
    have hexp : Complex.exp z = Complex.exp (-z) := by
      have htwo := Complex.two_sinh z
      rw [hsinh, mul_zero] at htwo
      exact sub_eq_zero.mp htwo.symm
    have hb : -Real.pi < z.im ∧ z.im < Real.pi := abs_lt.mp hz
    have hnegLower : -Real.pi < (-z).im := by
      simpa using (neg_lt_neg hb.2)
    have hnegUpper : (-z).im ≤ Real.pi := by
      simpa using (neg_le_neg hb.1.le)
    have hEq : z = -z :=
      Complex.exp_inj_of_neg_pi_lt_of_le_pi
        hb.1 hb.2.le hnegLower hnegUpper hexp
    have hsum : z + z = 0 := by
      have h := congrArg (fun w : ℂ => z + w) hEq
      simpa using h
    have hmul : (2 : ℂ) * z = 0 := by
      simpa [two_mul] using hsum
    exact hz0 ((mul_eq_zero.mp hmul).resolve_left (by norm_num))

/-- The denominator sampled by every fixed-unit aperture integral is nonzero on
the common strip. -/
theorem complexArchSinhSlope_mul_Icc_ne_zero
    {z : ℂ} (hz : z ∈ complexArchSafeStrip)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    complexArchSinhSlope (z * (t : ℂ)) ≠ 0 :=
  complexArchSinhSlope_ne_zero_of_mem_strip
    (mul_Icc_mem_complexArchSafeStrip hz ht)

/-- The regularized complex archimedean scale is complex differentiable at
every point of the safe strip. -/
theorem differentiableAt_complexRegularizedArchScale_of_mem_strip
    {z : ℂ} (hz : z ∈ complexArchSafeStrip) :
    DifferentiableAt ℂ complexRegularizedArchScale z := by
  unfold complexRegularizedArchScale
  have hnum : Differentiable ℂ (fun w : ℂ => Complex.exp (w / 2)) :=
    Complex.differentiable_exp.comp (differentiable_id.div_const _)
  have hden : Differentiable ℂ (fun w : ℂ => (2 : ℂ) * complexArchSinhSlope w) :=
    differentiable_complexArchSinhSlope.const_mul 2
  exact (hnum z).div (hden z)
    (mul_ne_zero (by norm_num) (complexArchSinhSlope_ne_zero_of_mem_strip hz))

/-- Strip-wide differentiability packaging. -/
theorem differentiableOn_complexRegularizedArchScale_strip :
    DifferentiableOn ℂ complexRegularizedArchScale complexArchSafeStrip := by
  intro z hz
  exact (differentiableAt_complexRegularizedArchScale_of_mem_strip hz).differentiableWithinAt

/-- The regularized complex archimedean scale is genuinely analytic throughout
the common open strip. -/
theorem analyticOnNhd_complexRegularizedArchScale_strip :
    AnalyticOnNhd ℂ complexRegularizedArchScale complexArchSafeStrip :=
  differentiableOn_complexRegularizedArchScale_strip.analyticOnNhd
    isOpen_complexArchSafeStrip

/-- Pointwise analytic form used by the parametric-integral layer. -/
theorem analyticAt_complexRegularizedArchScale_of_mem_strip
    {z : ℂ} (hz : z ∈ complexArchSafeStrip) :
    AnalyticAt ℂ complexRegularizedArchScale z :=
  analyticOnNhd_complexRegularizedArchScale_strip z hz

/-- Every point of the safe strip has a positive closed ball still contained in
the strip.  This is the compact parameter neighborhood used for local uniform
bounds under the fixed-unit integral. -/
theorem exists_closedBall_subset_complexArchSafeStrip
    {z : ℂ} (hz : z ∈ complexArchSafeStrip) :
    ∃ r > 0, Metric.closedBall z r ⊆ complexArchSafeStrip := by
  rcases Metric.isOpen_iff.mp isOpen_complexArchSafeStrip z hz with
    ⟨ε, hε, hball⟩
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro w hw
  apply hball
  exact Metric.mem_ball.mpr
    (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (half_lt_self hε))

end Zeta23.CCM

#print axioms Zeta23.CCM.complexArchSinhSlope_ne_zero_of_mem_strip
#print axioms Zeta23.CCM.analyticOnNhd_complexRegularizedArchScale_strip
