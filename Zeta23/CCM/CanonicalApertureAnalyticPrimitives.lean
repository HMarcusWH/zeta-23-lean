import Zeta23.CCM.CanonicalApertureContinuity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter
open scoped Topology Interval

/-! # FIRST-BAD-RIGIDITY-E4-A4R1b: analytic aperture primitives

PR #142 regularized the origin of the three production archimedean aperture
integrands and proved real continuity.  This module performs the exact
`x = L*t` change of variables so the integration interval is fixed at `[0,1]`,
and introduces the corresponding genuine complex divided-slope primitives.

The fixed-unit identities are production identities, not numerical ansatzes.
The complex definitions are auxiliary continuation objects; exact real-axis
bridges are theorem-locked below before they are used by the frozen source.

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
  have hLn : L ≠ 0 := hL.ne'
  have hInt :
      (∫ t in (0 : ℝ)..1, regularizedAlphaIntegrand n L (L * t)) =
        ∫ t in (0 : ℝ)..1,
          (2 * Real.pi * (n : ℝ) / L) *
            (Real.sinc (2 * Real.pi * (n : ℝ) * t) *
              regularizedArchScale (L * t)) := by
    apply intervalIntegral.integral_congr
    intro t _
    unfold regularizedAlphaIntegrand
    dsimp
    have harg :
        2 * Real.pi * (n : ℝ) * (L * t) / L =
          2 * Real.pi * (n : ℝ) * t := by
      field_simp [hLn]
    rw [harg]
    ring
  rw [hInt, intervalIntegral.integral_const_mul]
  field_simp [hLn, Real.pi_ne_zero]

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
  have hLn : L ≠ 0 := hL.ne'
  rw [one_div, inv_mul_cancel_left₀ hLn]
  apply intervalIntegral.integral_congr
  intro t _
  unfold regularizedBetaIntegrand
  dsimp
  have harg :
      2 * Real.pi * (n : ℝ) * (L * t) / L =
        2 * Real.pi * (n : ℝ) * t := by
    field_simp [hLn]
  rw [harg]

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
    have hreg :
        (∫ x in (0 : ℝ)..L, sourceEq411LhsIntegrand n L x) =
          ∫ x in (0 : ℝ)..L, regularizedSourceEq411LhsIntegrand n L x := by
      apply intervalIntegral.integral_congr
      intro x _
      exact (regularizedSourceEq411LhsIntegrand_eq n L x).symm
    rw [hreg]
    ring
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
  dsimp
  have hLn : L ≠ 0 := hL.ne'
  have harg :
      2 * Real.pi * (n : ℝ) * (L * t) / L =
        2 * Real.pi * (n : ℝ) * t := by
    field_simp [hLn]
  rw [harg]
  field_simp [hLn] <;> ring

/-- Complex divided slope `sin(z)/z`, with value one at zero. -/
def complexArchSinc (z : ℂ) : ℂ :=
  dslope Complex.sin 0 z

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

@[simp] theorem complexArchSinc_zero : complexArchSinc 0 = 1 := by
  rw [complexArchSinc, dslope_same, (Complex.hasDerivAt_sin 0).deriv]
  simp

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

/-- The complex sine divided slope is analytic everywhere. -/
theorem differentiable_complexArchSinc :
    Differentiable ℂ complexArchSinc := by
  unfold complexArchSinc
  rw [← differentiableOn_univ]
  have hU : (Set.univ : Set ℂ) ∈ 𝓝 (0 : ℂ) := by simp
  exact (Complex.differentiableOn_dslope hU).2
    Complex.differentiable_sin.differentiableOn

/-- The complex hyperbolic divided slope is analytic everywhere. -/
theorem differentiable_complexArchSinhSlope :
    Differentiable ℂ complexArchSinhSlope := by
  unfold complexArchSinhSlope
  rw [← differentiableOn_univ]
  have hU : (Set.univ : Set ℂ) ∈ 𝓝 (0 : ℂ) := by simp
  exact (Complex.differentiableOn_dslope hU).2
    Complex.differentiable_sinh.differentiableOn

/-- The complex cosine divided slope is analytic everywhere. -/
theorem differentiable_complexArchCosSlope :
    Differentiable ℂ complexArchCosSlope := by
  unfold complexArchCosSlope
  rw [← differentiableOn_univ]
  have hU : (Set.univ : Set ℂ) ∈ 𝓝 (0 : ℂ) := by simp
  exact (Complex.differentiableOn_dslope hU).2
    Complex.differentiable_cos.differentiableOn

/-- The complex exponential divided slope is analytic everywhere. -/
theorem differentiable_complexArchExpSlope :
    Differentiable ℂ complexArchExpSlope := by
  unfold complexArchExpSlope
  rw [← differentiableOn_univ]
  have hU : (Set.univ : Set ℂ) ∈ 𝓝 (0 : ℂ) := by simp
  exact (Complex.differentiableOn_dslope hU).2
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

/-- Consequently the complex regularized archimedean scale is analytic at the
origin. -/
theorem analyticAt_complexRegularizedArchScale_zero :
    AnalyticAt ℂ complexRegularizedArchScale 0 := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_complexArchSinhSlope_ne_zero] with z hz
  unfold complexRegularizedArchScale
  have hnum : Differentiable ℂ (fun w : ℂ => Complex.exp (w / 2)) :=
    Complex.differentiable_exp.comp (differentiable_id.div_const _)
  have hden : Differentiable ℂ (fun w : ℂ => (2 : ℂ) * complexArchSinhSlope w) :=
    differentiable_complexArchSinhSlope.const_mul 2
  exact (hnum z).div (hden z) (mul_ne_zero (by norm_num) hz)

/-- Genuine complex fixed-unit continuation of `alphaL`. -/
def complexAlphaCore (n : ℤ) (z : ℂ) : ℂ :=
  2 * (n : ℂ) *
    ∫ t in (0 : ℝ)..1,
      complexArchSinc ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ) *
        complexRegularizedArchScale (z * (t : ℂ))

/-- Genuine complex fixed-unit continuation of `betaL`. -/
def complexBetaCore (n : ℤ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    Complex.cos ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ) *
      complexRegularizedArchScale (z * (t : ℂ))

/-- Genuine complex fixed-unit continuation of `sourceEq44GammaL-wCorrection`. -/
def complexGammaCore (n : ℤ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1,
    (((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) *
        complexArchCosSlope ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ) +
      (z / 2) * complexArchExpSlope (-(z * (t : ℂ)) / 2)) *
        complexRegularizedArchScale (z * (t : ℂ))

end Zeta23.CCM

#print axioms Zeta23.CCM.alphaL_eq_unitInterval_integral
#print axioms Zeta23.CCM.betaL_eq_unitInterval_integral
#print axioms Zeta23.CCM.sourceEq44GammaL_sub_wCorrection_eq_unitInterval_integral
#print axioms Zeta23.CCM.differentiable_complexArchSinhSlope
#print axioms Zeta23.CCM.analyticAt_complexRegularizedArchScale_zero
