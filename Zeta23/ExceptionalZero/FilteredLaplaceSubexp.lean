import Zeta23.ExceptionalZero.FilteredLaplace
import Zeta23.ExceptionalZero.FilteredZeroRegularity
import Zeta23.ExceptionalZero.FilteredGrowthEnvelope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Set MeasureTheory Filter Topology

/-- The Laplace transform of the complete filtered zero family.  The integral is totalized by
Mathlib outside its convergence domain; the theorems below prove genuine integrability wherever
the transform is used. -/
def filteredLaplaceTransform (φ : ZeroFilter) (c z : ℂ) : ℂ :=
  ∫ a : ℝ in Set.Ioi 0,
    Complex.exp (-z * (a : ℂ)) * filteredZeroFamily φ c a

/-- In the already-proved safe half-plane, the named Laplace transform is exactly the filtered
resolvent. -/
theorem filteredLaplaceTransform_eq_resolvent_safe
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c z : ℂ} (hc : c.re = 1 / 2) (hz : 1 < z.re) :
    filteredLaplaceTransform φ c z = filteredResolvent φ c z := by
  simpa [filteredLaplaceTransform] using
    (integral_laplace_filteredZeroFamily hφ hc hz)

/-- The Laplace kernel of the filtered zero family is continuous on positive apertures. -/
theorem continuousOn_laplace_filteredZeroFamily_kernel
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2) (z : ℂ) :
    ContinuousOn
      (fun a : ℝ => Complex.exp (-z * (a : ℂ)) * filteredZeroFamily φ c a)
      (Set.Ioi 0) := by
  intro a ha
  have hexp : ContinuousAt (fun x : ℝ => Complex.exp (-z * (x : ℂ))) a := by fun_prop
  exact hexp.continuousWithinAt.mul ((continuousOn_filteredZeroFamily_Ioi hφ hc) a ha)

/-- The z-derivative kernel of the filtered Laplace transform is continuous on positive
apertures. -/
theorem continuousOn_laplace_filteredZeroFamily_derivKernel
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2) (z : ℂ) :
    ContinuousOn
      (fun a : ℝ =>
        Complex.exp (-z * (a : ℂ)) * -(a : ℂ) * filteredZeroFamily φ c a)
      (Set.Ioi 0) := by
  intro a ha
  have hfac : ContinuousAt
      (fun x : ℝ => Complex.exp (-z * (x : ℂ)) * -(x : ℂ)) a := by fun_prop
  exact hfac.continuousWithinAt.mul ((continuousOn_filteredZeroFamily_Ioi hφ hc) a ha)

/-- If the filtered zero family is subexponential, its Laplace kernel is genuinely integrable at
every point of the open right half-plane.  The proof uses the global epsilon-envelope with
`epsilon = Re z / 2`, leaving exponential decay `exp(-(Re z / 2) a)`. -/
theorem integrableOn_laplace_filteredZeroFamily_of_subexponential
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2)
    (hsub : Subexponential (fun a => ‖filteredZeroFamily φ c a‖))
    {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn
      (fun a : ℝ => Complex.exp (-z * (a : ℂ)) * filteredZeroFamily φ c a)
      (Set.Ioi 0) := by
  obtain ⟨C, _hC, hglobal⟩ :=
    exists_global_exp_bound_of_subexponential_filteredZeroFamily hφ hc hsub
      (ε := z.re / 2) (by linarith)
  have hmeas : AEStronglyMeasurable
      (fun a : ℝ => Complex.exp (-z * (a : ℂ)) * filteredZeroFamily φ c a)
      (volume.restrict (Set.Ioi 0)) :=
    (continuousOn_laplace_filteredZeroFamily_kernel hφ hc z).aestronglyMeasurable
      measurableSet_Ioi
  have hdecay : -(z.re / 2) < 0 := by linarith
  have hbase : IntegrableOn (fun a : ℝ => Real.exp (-(z.re / 2) * a)) (Set.Ioi 0) := by
    simpa using (integrableOn_exp_mul_Ioi (a := -(z.re / 2)) hdecay 0)
  have hmajor : IntegrableOn (fun a : ℝ => C * Real.exp (-(z.re / 2) * a)) (Set.Ioi 0) :=
    hbase.const_mul C
  refine Integrable.mono' hmajor hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a hmem
  have ha0 : (0 : ℝ) < a := hmem
  have hfa := hglobal a ha0.le
  rw [norm_mul, Complex.norm_exp]
  have hre : (-z * (a : ℂ)).re = -z.re * a := by simp [Complex.mul_re]
  rw [hre]
  calc
    Real.exp (-z.re * a) * ‖filteredZeroFamily φ c a‖
        ≤ Real.exp (-z.re * a) * (C * Real.exp (z.re / 2 * a)) :=
      mul_le_mul_of_nonneg_left hfa (Real.exp_pos _).le
    _ = C * (Real.exp (-z.re * a) * Real.exp (z.re / 2 * a)) := by ring
    _ = C * Real.exp (-z.re * a + z.re / 2 * a) := by rw [Real.exp_add]
    _ = C * Real.exp (-(z.re / 2) * a) := by
      rw [show -z.re * a + z.re / 2 * a = -(z.re / 2) * a by ring]

/-- Elementary envelope trade: for positive rate `r`, `a · exp(-(r/4)·a) ≤ 4/r`. -/
theorem aperture_mul_exp_quarter_le {r a : ℝ} (hr : 0 < r) :
    a * Real.exp (-(r / 4) * a) ≤ 4 / r := by
  have h1 : r / 4 * a ≤ Real.exp (r / 4 * a) := by
    have := Real.add_one_le_exp (r / 4 * a)
    linarith
  have hEpos : 0 < Real.exp (-(r / 4) * a) := Real.exp_pos _
  have hcancel : Real.exp (r / 4 * a) * Real.exp (-(r / 4) * a) = 1 := by
    rw [← Real.exp_add]
    rw [show r / 4 * a + -(r / 4) * a = 0 by ring]
    exact Real.exp_zero
  have h2 : r / 4 * a * Real.exp (-(r / 4) * a) ≤ 1 := by
    calc
      r / 4 * a * Real.exp (-(r / 4) * a)
          ≤ Real.exp (r / 4 * a) * Real.exp (-(r / 4) * a) :=
        mul_le_mul_of_nonneg_right h1 hEpos.le
      _ = 1 := hcancel
  rw [le_div_iff₀ hr]
  nlinarith

/-- Subexponential growth makes the filtered Laplace transform complex-differentiable at every
point of the open right half-plane.  Differentiation under the integral sign is justified by a
locally uniform integrable exponential majorant obtained from the global growth envelope. -/
theorem differentiableAt_filteredLaplaceTransform
    {φ : ZeroFilter} (hφ : AbsolutelySummableZeroFilter φ)
    {c : ℂ} (hc : c.re = 1 / 2)
    (hsub : Subexponential (fun a => ‖filteredZeroFamily φ c a‖))
    {z₀ : ℂ} (hz₀ : 0 < z₀.re) :
    DifferentiableAt ℂ (filteredLaplaceTransform φ c) z₀ := by
  have hε4 : 0 < z₀.re / 4 := by linarith
  obtain ⟨C, hC, hglobal⟩ :=
    exists_global_exp_bound_of_subexponential_filteredZeroFamily hφ hc hsub hε4
  have hkey := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume.restrict (Set.Ioi 0)) (s := Metric.ball z₀ (z₀.re / 4)) (x₀ := z₀)
    (F := fun z a => Complex.exp (-z * (a : ℂ)) * filteredZeroFamily φ c a)
    (F' := fun z a =>
      Complex.exp (-z * (a : ℂ)) * -(a : ℂ) * filteredZeroFamily φ c a)
    (bound := fun a => C * (4 / z₀.re) * Real.exp (-(z₀.re / 4) * a))
    (Metric.ball_mem_nhds z₀ hε4)
    (Eventually.of_forall fun z =>
      (continuousOn_laplace_filteredZeroFamily_kernel hφ hc z).aestronglyMeasurable
        measurableSet_Ioi)
    (integrableOn_laplace_filteredZeroFamily_of_subexponential hφ hc hsub hz₀)
    ((continuousOn_laplace_filteredZeroFamily_derivKernel hφ hc z₀).aestronglyMeasurable
      measurableSet_Ioi)
    ?_ ?_ ?_
  · exact hkey.2.differentiableAt
  · -- locally uniform bound for the derivative kernel
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha z hz
    have ha0 : (0 : ℝ) < a := ha
    have hzre : 3 * z₀.re / 4 < z.re := by
      have h1 : ‖z - z₀‖ < z₀.re / 4 := by
        simpa [Metric.mem_ball, Complex.dist_eq] using hz
      have h2 : |(z - z₀).re| ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
      have h3 : |z.re - z₀.re| < z₀.re / 4 := by
        simpa [Complex.sub_re] using lt_of_le_of_lt h2 h1
      have h4 := (abs_lt.mp h3).1
      linarith
    have hfa := hglobal a ha0.le
    rw [norm_mul, norm_mul, Complex.norm_exp]
    have hre : (-z * (a : ℂ)).re = -z.re * a := by simp [Complex.mul_re]
    rw [hre, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
    have hEnonneg : 0 ≤ Real.exp (-z.re * a) * a := by positivity
    calc
      Real.exp (-z.re * a) * a * ‖filteredZeroFamily φ c a‖
          ≤ Real.exp (-z.re * a) * a * (C * Real.exp (z₀.re / 4 * a)) :=
        mul_le_mul_of_nonneg_left hfa hEnonneg
      _ = C * a * (Real.exp (-z.re * a) * Real.exp (z₀.re / 4 * a)) := by ring
      _ = C * a * Real.exp (-z.re * a + z₀.re / 4 * a) := by rw [Real.exp_add]
      _ ≤ C * a * Real.exp (-(z₀.re / 2) * a) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Real.exp_le_exp.mpr
        nlinarith
      _ = C * (a * Real.exp (-(z₀.re / 4) * a)) * Real.exp (-(z₀.re / 4) * a) := by
        have hsplitexp : Real.exp (-(z₀.re / 2) * a) =
            Real.exp (-(z₀.re / 4) * a) * Real.exp (-(z₀.re / 4) * a) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hsplitexp]
        ring
      _ ≤ C * (4 / z₀.re) * Real.exp (-(z₀.re / 4) * a) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        exact mul_le_mul_of_nonneg_left
          (aperture_mul_exp_quarter_le hz₀) hC.le
  · -- the majorant is integrable
    have hdecay : -(z₀.re / 4) < 0 := by linarith
    have hbase : IntegrableOn
        (fun a : ℝ => Real.exp (-(z₀.re / 4) * a)) (Set.Ioi 0) := by
      simpa using (integrableOn_exp_mul_Ioi (a := -(z₀.re / 4)) hdecay 0)
    exact hbase.const_mul (C * (4 / z₀.re))
  · -- pointwise complex differentiability of the kernel in z
    refine Eventually.of_forall fun a z _hz => ?_
    have h1 : HasDerivAt (fun w : ℂ => -w * (a : ℂ)) (-(a : ℂ)) z := by
      simpa using (hasDerivAt_id z).neg.mul_const (a : ℂ)
    exact h1.cexp.mul_const (filteredZeroFamily φ c a)

end Zeta23.ExceptionalZero
