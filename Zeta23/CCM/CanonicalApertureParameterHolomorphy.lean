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

The first production core proved here is `complexBetaCore`; alpha and gamma are
added using the same engine once the compiler has validated the common
infrastructure.

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
    exact isCompact_closedBall.prod isCompact_Icc
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
      have hc := hF.comp hpair hmap
      simpa [K, Function.uncurry] using hc
    exact (hslice.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · have hpair : ContinuousOn (fun t : ℝ => (z₀, t)) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hmap : MapsTo (fun t : ℝ => (z₀, t)) (Set.Icc (0 : ℝ) 1) K := by
      intro t ht
      exact ⟨hz₀closed, ht⟩
    have hslice : ContinuousOn (F z₀) (Set.Icc (0 : ℝ) 1) := by
      have hc := hF.comp hpair hmap
      simpa [K, Function.uncurry] using hc
    exact hslice.intervalIntegrable
  · have hpair : ContinuousOn (fun t : ℝ => (z₀, t)) (Set.Icc (0 : ℝ) 1) := by
      fun_prop
    have hmap : MapsTo (fun t : ℝ => (z₀, t)) (Set.Icc (0 : ℝ) 1) K := by
      intro t ht
      exact ⟨hz₀closed, ht⟩
    have hslice : ContinuousOn (F' z₀) (Set.Icc (0 : ℝ) 1) := by
      have hc := hF'.comp hpair hmap
      simpa [K, Function.uncurry] using hc
    exact (hslice.mono uIoc_subset_uIcc).aestronglyMeasurable measurableSet_uIoc
  · filter_upwards with t
    intro ht z hz
    have hp : (z, t) ∈ K :=
      ⟨ball_subset_closedBall hz, uIoc_subset_uIcc ht⟩
    exact hC ⟨(z, t), hp, rfl⟩
  · filter_upwards with t
    intro ht z hz
    exact hderiv z (ball_subset_closedBall hz) t (uIoc_subset_uIcc ht)

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
    simpa [weightedArchIntegrand, Function.uncurry] using hwprod.mul hscale
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
    simpa [weightedArchIntegrandDeriv, Function.uncurry] using
      hwprod.mul (htcast.mul hderivScaleComp)
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
  exact (by
    simpa [weightedArchIntegral] using hmain.differentiableAt)

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
  simpa [w, weightedArchIntegral, weightedArchIntegrand, complexBetaCore] using h

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

/-- Every real aperture, not only every positive real aperture, is an analytic
point of the beta continuation.  Production provenance still separately uses
`L > 0`. -/
theorem analyticAt_complexBetaCore_ofReal (n : ℤ) (L : ℝ) :
    AnalyticAt ℂ (complexBetaCore n) (L : ℂ) :=
  analyticOnNhd_complexBetaCore_strip n _ (ofReal_mem_complexArchSafeStrip L)

end Zeta23.CCM

#print axioms Zeta23.CCM.analyticOnNhd_complexBetaCore_strip
