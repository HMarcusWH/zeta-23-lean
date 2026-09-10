import Zeta23.CCM.CanonicalApertureContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.RemovableSingularity

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped Interval

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1b: analytic aperture primitives

PR #142 regularized the origin of the three production archimedean aperture
integrands and proved real continuity.  This module performs the exact
`x = L*t` change of variables so the integration interval is fixed at `[0,1]`,
and introduces the corresponding complex divided-slope primitives.

The fixed-unit identities are production identities, not numerical ansatzes.
The complex definitions are auxiliary continuation objects; later files must
prove exact real-axis agreement before using them on the canonical source.

No determinant nonidentity, dense regularity, sign, or RH claim is made here.
-/

private theorem intervalIntegral_zero_L_eq_mul_zero_one
    {L : ℝ} (hL : 0 < L) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ x in (0 : ℝ)..L, g x) =
      L * ∫ t in (0 : ℝ)..1, g (L * t) := by
  have hsub := intervalIntegral.integral_deriv_smul_comp
    (f := fun t : ℝ => L * t)
    (f' := fun _ : ℝ => L)
    (g := g)
    (a := (0 : ℝ)) (b := (1 : ℝ))
    (fun t _ => by simpa using (hasDerivAt_id t).const_mul L)
    continuousOn_const hg
  have hsub' :
      (∫ t in (0 : ℝ)..1, L * g (L * t)) =
        ∫ x in (0 : ℝ)..L, g x := by
    simpa [Function.comp_def, smul_eq_mul] using hsub
  rw [← hsub']
  rw [intervalIntegral.integral_const_mul]

/-- Exact fixed-unit-interval representation of the production `alphaL`.
The apparent `n/L` frequency disappears after `x = L*t`. -/
theorem alphaL_eq_unitInterval_integral
    (n : ℤ) {L : ℝ} (hL : 0 < L) :
    alphaL n L =
      2 * (n : ℝ) *
        ∫ t in (0 : ℝ)..1,
          Real.sinc (2 * Real.pi * (n : ℝ) * t) *
            regularizedArchScale (L * t) := by
  rw [alphaL_eq_regularized_integral n hL]
  have hg : Continuous (fun x : ℝ => regularizedAlphaIntegrand n L x) := by
    unfold regularizedAlphaIntegrand
    fun_prop (disch := exact hL.ne')
  rw [intervalIntegral_zero_L_eq_mul_zero_one hL hg]
  congr 1
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  unfold regularizedAlphaIntegrand
  have hLn : L ≠ 0 := hL.ne'
  field_simp [hLn, Real.pi_ne_zero]
  ring

/-- Exact fixed-unit-interval representation of the production `betaL`. -/
theorem betaL_eq_unitInterval_integral
    (n : ℤ) {L : ℝ} (hL : 0 < L) :
    betaL n L =
      ∫ t in (0 : ℝ)..1,
        Real.cos (2 * Real.pi * (n : ℝ) * t) *
          regularizedArchScale (L * t) := by
  rw [betaL_eq_regularized_integral n hL]
  have hg : Continuous (fun x : ℝ => regularizedBetaIntegrand n L x) := by
    unfold regularizedBetaIntegrand
    fun_prop (disch := exact hL.ne')
  rw [intervalIntegral_zero_L_eq_mul_zero_one hL hg]
  rw [one_div, inv_mul_eq_iff₀ hL.ne']
  apply intervalIntegral.integral_congr
  intro t _
  unfold regularizedBetaIntegrand
  congr 2
  field_simp [hL.ne']

/-- Exact fixed-unit representation of the direct equation-(4.4) diagonal
primitive after removing only `wCorrection`. -/
theorem sourceEq44GammaL_sub_wCorrection_eq_unitInterval_integral
    (n : ℤ) {L : ℝ} (hL : 0 < L) :
    sourceEq44GammaL n L - wCorrection L =
      ∫ t in (0 : ℝ)..1,
        ((2 * Real.pi * (n : ℝ)) *
            archCosSlope (2 * Real.pi * (n : ℝ) * t) +
          (L / 2) * archExpSlope (-(L * t) / 2)) *
            regularizedArchScale (L * t) := by
  have hgamma :
      sourceEq44GammaL n L - wCorrection L =
        ∫ x in (0 : ℝ)..L, regularizedSourceEq411LhsIntegrand n L x := by
    unfold sourceEq44GammaL
    rw [sub_eq_iff_eq_add]
    congr 1
    apply intervalIntegral.integral_congr
    intro x _
    exact (regularizedSourceEq411LhsIntegrand_eq n L x).symm
  rw [hgamma]
  have hg : Continuous
      (fun x : ℝ => regularizedSourceEq411LhsIntegrand n L x) := by
    unfold regularizedSourceEq411LhsIntegrand
    fun_prop (disch := exact hL.ne')
  rw [intervalIntegral_zero_L_eq_mul_zero_one hL hg]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  unfold regularizedSourceEq411LhsIntegrand
  have hLn : L ≠ 0 := hL.ne'
  field_simp [hLn]
  ring

/-- Complex divided slope `sinh(z)/z`, with the derivative value at zero. -/
def complexArchSinhSlope (z : ℂ) : ℂ :=
  dslope Complex.sinh 0 z

/-- Complex divided slope `(cos z - 1)/z`, with its removable value at zero. -/
def complexArchCosSlope (z : ℂ) : ℂ :=
  dslope Complex.cos 0 z

/-- Complex divided slope `(exp z - 1)/z`, with value one at zero. -/
def complexArchExpSlope (z : ℂ) : ℂ :=
  dslope Complex.exp 0 z

/-- Complex version of the regularized archimedean scale. -/
def complexRegularizedArchScale (z : ℂ) : ℂ :=
  Complex.exp (z / 2) / (2 * complexArchSinhSlope z)

@[simp] theorem complexArchSinhSlope_zero : complexArchSinhSlope 0 = 1 := by
  rw [complexArchSinhSlope, dslope_same, (Complex.hasDerivAt_sinh 0).deriv]
  simp

@[simp] theorem complexArchCosSlope_zero : complexArchCosSlope 0 = 0 := by
  rw [complexArchCosSlope, dslope_same, (Complex.hasDerivAt_cos 0).deriv]
  simp

@[simp] theorem complexArchExpSlope_zero : complexArchExpSlope 0 = 1 := by
  rw [complexArchExpSlope, dslope_same, (Complex.hasDerivAt_exp 0).deriv]
  simp

@[simp] theorem complexRegularizedArchScale_zero :
    complexRegularizedArchScale 0 = 1 / 2 := by
  simp [complexRegularizedArchScale]

/-- The complex hyperbolic divided slope is analytic everywhere. -/
theorem differentiable_complexArchSinhSlope :
    Differentiable ℂ complexArchSinhSlope := by
  unfold complexArchSinhSlope
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope univ_mem).2
    Complex.differentiable_sinh.differentiableOn

/-- The complex cosine divided slope is analytic everywhere. -/
theorem differentiable_complexArchCosSlope :
    Differentiable ℂ complexArchCosSlope := by
  unfold complexArchCosSlope
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope univ_mem).2
    Complex.differentiable_cos.differentiableOn

/-- The complex exponential divided slope is analytic everywhere. -/
theorem differentiable_complexArchExpSlope :
    Differentiable ℂ complexArchExpSlope := by
  unfold complexArchExpSlope
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope univ_mem).2
    Complex.differentiable_exp.differentiableOn

/-- There is a genuine complex neighborhood of zero on which the regularized
archimedean scale denominator is nonzero.  We deliberately keep the radius
existential instead of hard-coding the first complex sinh zero. -/
theorem eventually_complexArchSinhSlope_ne_zero :
    ∀ᶠ z in 𝓝 (0 : ℂ), complexArchSinhSlope z ≠ 0 := by
  have hcont : ContinuousAt complexArchSinhSlope 0 :=
    (differentiable_complexArchSinhSlope 0).continuousAt
  have hne : complexArchSinhSlope 0 ≠ 0 := by simp
  exact hcont.eventually_ne hne

end Zeta23.CCM

#print axioms Zeta23.CCM.alphaL_eq_unitInterval_integral
#print axioms Zeta23.CCM.betaL_eq_unitInterval_integral
#print axioms Zeta23.CCM.sourceEq44GammaL_sub_wCorrection_eq_unitInterval_integral
#print axioms Zeta23.CCM.differentiable_complexArchSinhSlope
#print axioms Zeta23.CCM.eventually_complexArchSinhSlope_ne_zero
