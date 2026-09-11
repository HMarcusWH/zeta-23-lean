import Zeta23.CCM.CanonicalApertureArchDomain
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Order.Compact

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set Filter Metric
open scoped Topology Interval

/-! # FIRST-BAD-RIGIDITY-E4-A4R1b: aperture-parameter holomorphy

This module differentiates the already theorem-locked fixed-unit aperture
integrals with respect to the genuine complex aperture parameter.  The
measure-theoretic engine is deliberately local: a compact closed parameter ball
inside `complexArchSafeStrip`, crossed with `[0,1]`, provides the uniform
integrable derivative bound required by Mathlib's parametric interval-integral
theorem.

The common engine is first instantiated by `complexBetaCore`, then reused for
`complexAlphaCore`; `complexGammaCore` uses the same dominated-integral engine
with one additional aperture-dependent entire coefficient.

No frozen-source determinant, determinant nonidentity, dense regularity,
positivity, negative-root exclusion, or RH claim is made here.
-/

/-- Compiler-facing fixed-unit differentiation engine.  Joint continuity of an
integrand and its parameter derivative on a compact closed parameter ball times
`[0,1]` supplies a constant dominated bound automatically. -/
private theorem hasDerivAt_fixedUnitIntegral_of_continuousOn
    {F F' : ℂ → ℝ → ℂ} {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r)
    (hF : ContinuousOn (Function.uncurry F)
      (closedBall z₀ r ×ˢ Set.Icc (0 : ℝ) 1))
    (hF' : ContinuousOn (Function.uncurry F')
      (closedBall z₀ r ×ˢ Set.Icc (0 : ℝ) 1))
    (hderiv : ∀ z ∈ closedBall z₀ r, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt (fun w : ℂ => F w t) (F' z t) z) :
    HasDerivAt
      (fun z : ℂ => ∫ t in (0 : ℝ)..1, F z t)
      (∫ t in (0 : ℝ)..1, F' z₀ t) z₀ := by
  let K : Set (ℂ × ℝ) := closedBall z₀ r ×ˢ Set.Icc (0 : ℝ) 1
  have hK : IsCompact K := by
    dsimp [K]
    exact (isCompact_closedBall z₀ r).prod isCompact_Icc
  have hnorm : ContinuousOn (fun p : ℂ × ℝ => ‖F' p.1 p.2‖) K := by
    simpa [K, Function.uncurry] using hF'.norm
  rcases hK.bddAbove_image hnorm with ⟨C, hC⟩
  have hz₀closed : z₀ ∈ closedBall z₀ r := mem_closedBall_self hr.le
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := F) (F' := F') (bound := fun _ : ℝ => C)
    (ball_mem_nhds z₀ hr) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_).2
  · filter_upwards [ball_mem_nhds z₀ hr] with z hz
    have hzclosed : z ∈ closedBall z₀ r := ball_subset_closedBall hz
    have hpair : ContinuousOn (fun t : ℝ => (z, t)) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hmap : MapsTo (fun t : ℝ => (z, t)) (Set.Icc (0 : ℝ) 1) K := by
      intro t ht
      exact ⟨hzclosed, ht⟩
    have hslice : ContinuousOn (F z) (Set.Icc (0 : ℝ) 1) := by
      change ContinuousOn
        ((Function.uncurry F) ∘ fun t : ℝ => (z, t)) (Set.Icc (0 : ℝ) 1)
      exact hF.comp hpair hmap
    have hsliceIoc := hslice.mono Set.Ioc_subset_Icc_self
    rw [Set.uIoc_of_le zero_le_one]
    exact hsliceIoc.aestronglyMeasurable measurableSet_Ioc
  · have hpair : ContinuousOn (fun t : ℝ => (z₀, t)) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hmap : MapsTo (fun t : ℝ => (z₀, t)) (Set.Icc (0 : ℝ) 1) K := by
      intro t ht
      exact ⟨hz₀closed, ht⟩
    have hslice : ContinuousOn (F z₀) (Set.Icc (0 : ℝ) 1) := by
      change ContinuousOn
        ((Function.uncurry F) ∘ fun t : ℝ => (z₀, t)) (Set.Icc (0 : ℝ) 1)
      exact hF.comp hpair hmap
    have hsliceU : ContinuousOn (F z₀) (Set.uIcc (0 : ℝ) 1) := by
      simpa [uIcc_of_le zero_le_one] using hslice
    exact hsliceU.intervalIntegrable
  · have hpair : ContinuousOn (fun t : ℝ => (z₀, t)) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hmap : MapsTo (fun t : ℝ => (z₀, t)) (Set.Icc (0 : ℝ) 1) K := by
      intro t ht
      exact ⟨hz₀closed, ht⟩
    have hslice : ContinuousOn (F' z₀) (Set.Icc (0 : ℝ) 1) := by
      change ContinuousOn
        ((Function.uncurry F') ∘ fun t : ℝ => (z₀, t)) (Set.Icc (0 : ℝ) 1)
      exact hF'.comp hpair hmap
    have hsliceIoc := hslice.mono Set.Ioc_subset_Icc_self
    rw [Set.uIoc_of_le zero_le_one]
    exact hsliceIoc.aestronglyMeasurable measurableSet_Ioc
  · filter_upwards with t
    intro ht z hz
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact Set.Ioc_subset_Icc_self ht
    have hp : (z, t) ∈ K :=
      ⟨ball_subset_closedBall hz, htIcc⟩
    exact hC ⟨(z, t), hp, rfl⟩
  · filter_upwards with t
    intro ht z hz
    have htIcc : t ∈ Set.Icc (0 : ℝ) 1 := by
      rw [Set.uIoc_of_le zero_le_one] at ht
      exact Set.Ioc_subset_Icc_self ht
    exact hderiv z (ball_subset_closedBall hz) t htIcc

/-- A fixed continuous weight multiplied by the regularized archimedean scale. -/
private def weightedArchIntegrand (w : ℝ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  w t * complexRegularizedArchScale (z * (t : ℂ))

/-- Its complex-aperture derivative. -/
private def weightedArchIntegrandDeriv (w : ℝ → ℂ) (z : ℂ) (t : ℝ) : ℂ :=
  w t * ((t : ℂ) * deriv complexRegularizedArchScale (z * (t : ℂ)))

/-- Fixed-unit weighted archimedean integral. -/
private def weightedArchIntegral (w : ℝ → ℂ) (z : ℂ) : ℂ :=
  ∫ t in (0 : ℝ)..1, weightedArchIntegrand w z t

/-- Any continuous fixed weight gives a complex-differentiable aperture
integral at every point of the common archimedean strip. -/
private theorem differentiableAt_weightedArchIntegral
    {w : ℝ → ℂ}
    (hw : ContinuousOn w (Set.Icc (0 : ℝ) 1))
    {z₀ : ℂ} (hz₀ : z₀ ∈ complexArchSafeStrip) :
    DifferentiableAt ℂ (weightedArchIntegral w) z₀ := by
  rcases exists_closedBall_subset_complexArchSafeStrip hz₀ with ⟨r, hr, hclosed⟩
  let K : Set (ℂ × ℝ) := closedBall z₀ r ×ˢ Set.Icc (0 : ℝ) 1
  have hmap : MapsTo
      (fun p : ℂ × ℝ => p.1 * (p.2 : ℂ)) K complexArchSafeStrip := by
    intro p hp
    exact mul_Icc_mem_complexArchSafeStrip (hclosed hp.1) hp.2
  have hmapcont : ContinuousOn
      (fun p : ℂ × ℝ => p.1 * (p.2 : ℂ)) K := by
    fun_prop
  have hwprod : ContinuousOn (fun p : ℂ × ℝ => w p.2) K := by
    exact hw.comp (by fun_prop) (by intro p hp; exact hp.2)
  have hscale : ContinuousOn
      (fun p : ℂ × ℝ => complexRegularizedArchScale (p.1 * (p.2 : ℂ))) K := by
    exact analyticOnNhd_complexRegularizedArchScale_strip.continuousOn.comp hmapcont hmap
  have hF : ContinuousOn
      (Function.uncurry (weightedArchIntegrand w)) K := by
    change ContinuousOn
      (fun p : ℂ × ℝ =>
        w p.2 * complexRegularizedArchScale (p.1 * (p.2 : ℂ))) K
    exact hwprod.mul hscale
  have hderivScale : AnalyticOnNhd ℂ
      (deriv complexRegularizedArchScale) complexArchSafeStrip :=
    analyticOnNhd_complexRegularizedArchScale_strip.deriv
  have hderivScaleComp : ContinuousOn
      (fun p : ℂ × ℝ =>
        deriv complexRegularizedArchScale (p.1 * (p.2 : ℂ))) K := by
    exact hderivScale.continuousOn.comp hmapcont hmap
  have htcast : ContinuousOn (fun p : ℂ × ℝ => (p.2 : ℂ)) K := by
    fun_prop
  have hF' : ContinuousOn
      (Function.uncurry (weightedArchIntegrandDeriv w)) K := by
    change ContinuousOn
      (fun p : ℂ × ℝ =>
        w p.2 * ((p.2 : ℂ) *
          deriv complexRegularizedArchScale (p.1 * (p.2 : ℂ)))) K
    exact hwprod.mul (htcast.mul hderivScaleComp)
  have hpoint : ∀ z ∈ closedBall z₀ r, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt
        (fun u : ℂ => weightedArchIntegrand w u t)
        (weightedArchIntegrandDeriv w z t) z := by
    intro z hz t ht
    have hzt : z * (t : ℂ) ∈ complexArchSafeStrip :=
      mul_Icc_mem_complexArchSafeStrip (hclosed hz) ht
    have hscaleDeriv : HasDerivAt complexRegularizedArchScale
        (deriv complexRegularizedArchScale (z * (t : ℂ)))
        (z * (t : ℂ)) :=
      (differentiableAt_complexRegularizedArchScale_of_mem_strip hzt).hasDerivAt
    have hmul : HasDerivAt (fun u : ℂ => u * (t : ℂ)) (t : ℂ) z := by
      simpa using (hasDerivAt_id z).mul_const (t : ℂ)
    have hcomp := hscaleDeriv.comp z hmul
    have hweighted := hcomp.const_mul (w t)
    simpa [weightedArchIntegrand, weightedArchIntegrandDeriv,
      mul_assoc, mul_comm, mul_left_comm] using hweighted
  have hmain := hasDerivAt_fixedUnitIntegral_of_continuousOn
    hr hF hF' hpoint
  change DifferentiableAt ℂ
    (fun z : ℂ => ∫ t in (0 : ℝ)..1, weightedArchIntegrand w z t) z₀
  exact hmain.differentiableAt

/-- `complexBetaCore` is complex differentiable at every aperture in the
common archimedean safe strip. -/
theorem differentiableAt_complexBetaCore_of_mem_strip
    (n : ℤ) {z : ℂ} (hz : z ∈ complexArchSafeStrip) :
    DifferentiableAt ℂ (complexBetaCore n) z := by
  let w : ℝ → ℂ := fun t =>
    Complex.cos ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)
  have hw : ContinuousOn w (Set.Icc (0 : ℝ) 1) := by
    dsimp [w]
    fun_prop
  have h := differentiableAt_weightedArchIntegral hw hz
  change DifferentiableAt ℂ (complexBetaCore n) z at h
  exact h

/-- Strip-wide differentiability of the beta core. -/
theorem differentiableOn_complexBetaCore_strip (n : ℤ) :
    DifferentiableOn ℂ (complexBetaCore n) complexArchSafeStrip := by
  intro z hz
  exact (differentiableAt_complexBetaCore_of_mem_strip n hz).differentiableWithinAt

/-- Genuine holomorphy of the beta core on the common open strip. -/
theorem analyticOnNhd_complexBetaCore_strip (n : ℤ) :
    AnalyticOnNhd ℂ (complexBetaCore n) complexArchSafeStrip :=
  (differentiableOn_complexBetaCore_strip n).analyticOnNhd
    isOpen_complexArchSafeStrip

/-- Every real aperture is an analytic point of the beta continuation. -/
theorem analyticAt_complexBetaCore_ofReal (n : ℤ) (L : ℝ) :
    AnalyticAt ℂ (complexBetaCore n) (L : ℂ) :=
  analyticOnNhd_complexBetaCore_strip n _ (ofReal_mem_complexArchSafeStrip L)

/-- `complexAlphaCore` is complex differentiable throughout the same strip. -/
theorem differentiableAt_complexAlphaCore_of_mem_strip
    (n : ℤ) {z : ℂ} (hz : z ∈ complexArchSafeStrip) :
    DifferentiableAt ℂ (complexAlphaCore n) z := by
  let w : ℝ → ℂ := fun t =>
    complexArchSinc ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)
  have hsinc : Continuous complexArchSinc := differentiable_complexArchSinc.continuous
  have hw : ContinuousOn w (Set.Icc (0 : ℝ) 1) := by
    dsimp [w]
    fun_prop (disch := assumption)
  have h := differentiableAt_weightedArchIntegral hw hz
  have hscaled := h.const_mul (2 * (n : ℂ))
  change DifferentiableAt ℂ (complexAlphaCore n) z at hscaled
  exact hscaled

/-- Strip-wide differentiability of the alpha core. -/
theorem differentiableOn_complexAlphaCore_strip (n : ℤ) :
    DifferentiableOn ℂ (complexAlphaCore n) complexArchSafeStrip := by
  intro z hz
  exact (differentiableAt_complexAlphaCore_of_mem_strip n hz).differentiableWithinAt

/-- Genuine holomorphy of the alpha core on the common open strip. -/
theorem analyticOnNhd_complexAlphaCore_strip (n : ℤ) :
    AnalyticOnNhd ℂ (complexAlphaCore n) complexArchSafeStrip :=
  (differentiableOn_complexAlphaCore_strip n).analyticOnNhd
    isOpen_complexArchSafeStrip

/-- Every real aperture is an analytic point of the alpha continuation. -/
theorem analyticAt_complexAlphaCore_ofReal (n : ℤ) (L : ℝ) :
    AnalyticAt ℂ (complexAlphaCore n) (L : ℂ) :=
  analyticOnNhd_complexAlphaCore_strip n _ (ofReal_mem_complexArchSafeStrip L)

/-- Aperture-dependent coefficient multiplying the common regularized scale in
the fixed-unit gamma core. -/
private def gammaApertureCoeff (n : ℤ) (z : ℂ) (t : ℝ) : ℂ :=
  ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) *
      complexArchCosSlope ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ) +
    (z / 2) * complexArchExpSlope (-(z * (t : ℂ)) / 2)

/-- Exact parameter derivative of `gammaApertureCoeff`. -/
private def gammaApertureCoeffDeriv (_n : ℤ) (z : ℂ) (t : ℝ) : ℂ :=
  (1 / 2 : ℂ) * complexArchExpSlope (-(z * (t : ℂ)) / 2) +
    (z / 2) *
      (deriv complexArchExpSlope (-(z * (t : ℂ)) / 2) * (-(t : ℂ) / 2))

private def gammaParamIntegrand (n : ℤ) (z : ℂ) (t : ℝ) : ℂ :=
  gammaApertureCoeff n z t *
    complexRegularizedArchScale (z * (t : ℂ))

private def gammaParamIntegrandDeriv (n : ℤ) (z : ℂ) (t : ℝ) : ℂ :=
  gammaApertureCoeffDeriv n z t *
      complexRegularizedArchScale (z * (t : ℂ)) +
    gammaApertureCoeff n z t *
      (deriv complexRegularizedArchScale (z * (t : ℂ)) * (t : ℂ))

private theorem continuous_deriv_complexArchExpSlope :
    Continuous (deriv complexArchExpSlope) := by
  rw [continuous_iff_continuousAt]
  intro z
  exact (differentiable_complexArchExpSlope.analyticAt z).deriv.continuousAt

private theorem continuous_gammaApertureCoeff (n : ℤ) :
    Continuous (Function.uncurry (gammaApertureCoeff n)) := by
  have hcos : Continuous complexArchCosSlope :=
    differentiable_complexArchCosSlope.continuous
  have hexp : Continuous complexArchExpSlope :=
    differentiable_complexArchExpSlope.continuous
  unfold gammaApertureCoeff Function.uncurry
  fun_prop (disch := assumption)

private theorem continuous_gammaApertureCoeffDeriv (n : ℤ) :
    Continuous (Function.uncurry (gammaApertureCoeffDeriv n)) := by
  have hexp : Continuous complexArchExpSlope :=
    differentiable_complexArchExpSlope.continuous
  have hderivExp : Continuous (deriv complexArchExpSlope) :=
    continuous_deriv_complexArchExpSlope
  unfold gammaApertureCoeffDeriv Function.uncurry
  fun_prop (disch := assumption)

private theorem hasDerivAt_gammaApertureCoeff
    (n : ℤ) (z : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℂ => gammaApertureCoeff n u t)
      (gammaApertureCoeffDeriv n z t) z := by
  let A : ℂ :=
    ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) *
      complexArchCosSlope ((2 * Real.pi * (n : ℝ) * t : ℝ) : ℂ)
  have hzhalf : HasDerivAt (fun u : ℂ => u / 2) (1 / 2 : ℂ) z := by
    simpa using (hasDerivAt_id z).div_const 2
  have hinner : HasDerivAt
      (fun u : ℂ => -(u * (t : ℂ)) / 2) (-(t : ℂ) / 2) z := by
    simpa using (((hasDerivAt_id z).mul_const (t : ℂ)).neg.div_const 2)
  have hexpBase : HasDerivAt complexArchExpSlope
      (deriv complexArchExpSlope (-(z * (t : ℂ)) / 2))
      (-(z * (t : ℂ)) / 2) :=
    (differentiable_complexArchExpSlope (-(z * (t : ℂ)) / 2)).hasDerivAt
  have hexpComp := hexpBase.comp z hinner
  have hprod := hzhalf.mul hexpComp
  have hsum := hprod.const_add A
  change HasDerivAt
    (fun u : ℂ => A +
      ((fun v : ℂ => v / 2) *
        (complexArchExpSlope ∘ fun v : ℂ => -(v * (t : ℂ)) / 2)) u)
    (gammaApertureCoeffDeriv n z t) z
  exact hsum

private theorem hasDerivAt_gammaParamIntegrand
    (n : ℤ) {z : ℂ} (hz : z ∈ complexArchSafeStrip)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivAt (fun u : ℂ => gammaParamIntegrand n u t)
      (gammaParamIntegrandDeriv n z t) z := by
  have hzt : z * (t : ℂ) ∈ complexArchSafeStrip :=
    mul_Icc_mem_complexArchSafeStrip hz ht
  have hscaleBase : HasDerivAt complexRegularizedArchScale
      (deriv complexRegularizedArchScale (z * (t : ℂ)))
      (z * (t : ℂ)) :=
    (differentiableAt_complexRegularizedArchScale_of_mem_strip hzt).hasDerivAt
  have hmul : HasDerivAt (fun u : ℂ => u * (t : ℂ)) (t : ℂ) z := by
    simpa using (hasDerivAt_id z).mul_const (t : ℂ)
  have hscale := hscaleBase.comp z hmul
  have hcoeff := hasDerivAt_gammaApertureCoeff n z t
  change HasDerivAt
    ((fun u : ℂ => gammaApertureCoeff n u t) *
      (complexRegularizedArchScale ∘ fun u : ℂ => u * (t : ℂ)))
    (gammaParamIntegrandDeriv n z t) z
  exact hcoeff.mul hscale

/-- `complexGammaCore` is complex differentiable throughout the common strip. -/
theorem differentiableAt_complexGammaCore_of_mem_strip
    (n : ℤ) {z₀ : ℂ} (hz₀ : z₀ ∈ complexArchSafeStrip) :
    DifferentiableAt ℂ (complexGammaCore n) z₀ := by
  rcases exists_closedBall_subset_complexArchSafeStrip hz₀ with ⟨r, hr, hclosed⟩
  let K : Set (ℂ × ℝ) := closedBall z₀ r ×ˢ Set.Icc (0 : ℝ) 1
  have hmap : MapsTo
      (fun p : ℂ × ℝ => p.1 * (p.2 : ℂ)) K complexArchSafeStrip := by
    intro p hp
    exact mul_Icc_mem_complexArchSafeStrip (hclosed hp.1) hp.2
  have hmapcont : ContinuousOn
      (fun p : ℂ × ℝ => p.1 * (p.2 : ℂ)) K := by
    fun_prop
  have hscale : ContinuousOn
      (fun p : ℂ × ℝ => complexRegularizedArchScale (p.1 * (p.2 : ℂ))) K :=
    analyticOnNhd_complexRegularizedArchScale_strip.continuousOn.comp hmapcont hmap
  have hderivScale : AnalyticOnNhd ℂ
      (deriv complexRegularizedArchScale) complexArchSafeStrip :=
    analyticOnNhd_complexRegularizedArchScale_strip.deriv
  have hderivScaleComp : ContinuousOn
      (fun p : ℂ × ℝ =>
        deriv complexRegularizedArchScale (p.1 * (p.2 : ℂ))) K :=
    hderivScale.continuousOn.comp hmapcont hmap
  have htcast : ContinuousOn (fun p : ℂ × ℝ => (p.2 : ℂ)) K := by
    fun_prop
  have hcoeff : ContinuousOn
      (Function.uncurry (gammaApertureCoeff n)) K :=
    (continuous_gammaApertureCoeff n).continuousOn
  have hcoeff' : ContinuousOn
      (Function.uncurry (gammaApertureCoeffDeriv n)) K :=
    (continuous_gammaApertureCoeffDeriv n).continuousOn
  have hF : ContinuousOn
      (Function.uncurry (gammaParamIntegrand n)) K := by
    change ContinuousOn
      (fun p : ℂ × ℝ => gammaApertureCoeff n p.1 p.2 *
        complexRegularizedArchScale (p.1 * (p.2 : ℂ))) K
    exact hcoeff.mul hscale
  have hscaleParamDeriv : ContinuousOn
      (fun p : ℂ × ℝ =>
        deriv complexRegularizedArchScale (p.1 * (p.2 : ℂ)) * (p.2 : ℂ)) K :=
    hderivScaleComp.mul htcast
  have hF' : ContinuousOn
      (Function.uncurry (gammaParamIntegrandDeriv n)) K := by
    change ContinuousOn
      (fun p : ℂ × ℝ =>
        gammaApertureCoeffDeriv n p.1 p.2 *
            complexRegularizedArchScale (p.1 * (p.2 : ℂ)) +
          gammaApertureCoeff n p.1 p.2 *
            (deriv complexRegularizedArchScale (p.1 * (p.2 : ℂ)) * (p.2 : ℂ))) K
    exact (hcoeff'.mul hscale).add (hcoeff.mul hscaleParamDeriv)
  have hpoint : ∀ z ∈ closedBall z₀ r, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt
        (fun u : ℂ => gammaParamIntegrand n u t)
        (gammaParamIntegrandDeriv n z t) z := by
    intro z hz t ht
    exact hasDerivAt_gammaParamIntegrand n (hclosed hz) ht
  have hmain := hasDerivAt_fixedUnitIntegral_of_continuousOn
    hr hF hF' hpoint
  have hd := hmain.differentiableAt
  change DifferentiableAt ℂ (complexGammaCore n) z₀ at hd
  exact hd

/-- Strip-wide differentiability of the gamma core. -/
theorem differentiableOn_complexGammaCore_strip (n : ℤ) :
    DifferentiableOn ℂ (complexGammaCore n) complexArchSafeStrip := by
  intro z hz
  exact (differentiableAt_complexGammaCore_of_mem_strip n hz).differentiableWithinAt

/-- Genuine holomorphy of the gamma core on the common open strip. -/
theorem analyticOnNhd_complexGammaCore_strip (n : ℤ) :
    AnalyticOnNhd ℂ (complexGammaCore n) complexArchSafeStrip :=
  (differentiableOn_complexGammaCore_strip n).analyticOnNhd
    isOpen_complexArchSafeStrip

/-- Every real aperture is an analytic point of the gamma continuation. -/
theorem analyticAt_complexGammaCore_ofReal (n : ℤ) (L : ℝ) :
    AnalyticAt ℂ (complexGammaCore n) (L : ℂ) :=
  analyticOnNhd_complexGammaCore_strip n _ (ofReal_mem_complexArchSafeStrip L)

end Zeta23.CCM

#print axioms Zeta23.CCM.analyticOnNhd_complexAlphaCore_strip
#print axioms Zeta23.CCM.analyticOnNhd_complexBetaCore_strip
#print axioms Zeta23.CCM.analyticOnNhd_complexGammaCore_strip