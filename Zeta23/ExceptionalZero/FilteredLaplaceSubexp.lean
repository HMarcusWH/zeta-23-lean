import Zeta23.ExceptionalZero.FilteredLaplace
import Zeta23.ExceptionalZero.FilteredZeroRegularity
import Zeta23.ExceptionalZero.FilteredGrowthEnvelope
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Set MeasureTheory Filter Topology

/-- The Laplace transform of the complete filtered zero family.  The integral is totalized by
Mathlib outside its convergence domain; later theorems prove genuine integrability wherever used. -/
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
  let ε : ℝ := z.re / 2
  have hε : 0 < ε := by
    dsimp [ε]
    linarith
  obtain ⟨C, _hC, hglobal⟩ :=
    exists_global_exp_bound_of_subexponential_filteredZeroFamily hφ hc hsub hε
  have hfam_cont := continuousOn_filteredZeroFamily_Ioi hφ hc
  have hkernel_cont : ContinuousOn
      (fun a : ℝ => Complex.exp (-z * (a : ℂ)) * filteredZeroFamily φ c a)
      (Set.Ioi 0) := by
    intro a ha
    have hexp : ContinuousAt (fun x : ℝ => Complex.exp (-z * (x : ℂ))) a := by
      fun_prop
    exact hexp.continuousWithinAt.mul (hfam_cont a ha)
  have hkernel_meas : AEStronglyMeasurable
      (fun a : ℝ => Complex.exp (-z * (a : ℂ)) * filteredZeroFamily φ c a)
      (volume.restrict (Set.Ioi 0)) :=
    hkernel_cont.aestronglyMeasurable measurableSet_Ioi
  have hdecay : -ε < 0 := by linarith
  have hbase : IntegrableOn (fun a : ℝ => Real.exp (-ε * a)) (Set.Ioi 0) := by
    simpa using (integrableOn_exp_mul_Ioi (a := -ε) hdecay 0)
  have hmajor : IntegrableOn (fun a : ℝ => C * Real.exp (-ε * a)) (Set.Ioi 0) :=
    hbase.const_mul C
  refine Integrable.mono hmajor hkernel_meas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have hfa := hglobal a ha.le
  rw [norm_mul, Complex.norm_exp]
  calc
    Real.exp (-z * (a : ℂ)).re * ‖filteredZeroFamily φ c a‖ ≤
        Real.exp (-z * (a : ℂ)).re * (C * Real.exp (ε * a)) :=
      mul_le_mul_of_nonneg_left hfa (Real.exp_pos _).le
    _ = C * (Real.exp (-z * (a : ℂ)).re * Real.exp (ε * a)) := by
      ring
    _ = C * Real.exp ((-z * (a : ℂ)).re + ε * a) := by
      rw [Real.exp_add]
    _ = C * Real.exp (-ε * a) := by
      have hzε : z.re = 2 * ε := by
        dsimp [ε]
        ring
      have hre : (-z * (a : ℂ)).re = -z.re * a := by
        simp [Complex.mul_re]
      rw [hre, hzε]
      congr 2
      ring

end Zeta23.ExceptionalZero
