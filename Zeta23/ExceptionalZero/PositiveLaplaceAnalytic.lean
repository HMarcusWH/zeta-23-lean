import Zeta23.ExceptionalZero.PositiveLaplaceBoundary
import Mathlib.Analysis.Meromorphic.Basic

/-!
# Analyticity on the actual positive Laplace domain

The literal tilt and the existing complex-MGF theorem prove analyticity
where real Laplace integrability holds in a genuine neighborhood. For a
nonnegative source, this includes every complex point strictly to the
right of its actual abscissa. No analytic continuation premise is used.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Zeta23.ExceptionalZero

theorem analyticAt_positiveLaplaceTransform_of_integrable_nhds
    {u : ℝ → ℝ} {z : ℂ} (hu : Measurable u)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (hLaplace : ∀ᶠ p in 𝓝 z.re,
      Integrable (positiveLaplaceWeight u p) positiveLaplaceHalfLine) :
    AnalyticAt ℂ (positiveLaplaceTransform u) z := by
  let p0 : ℝ := z.re
  have h0 : 0 ∈ interior (integrableExpSet id (positiveLaplaceTilt u p0)) :=
    zero_mem_interior_integrableExpSet_positiveLaplaceTilt hu hnonneg hLaplace
  have hre : ((p0 : ℂ) - z).re = 0 := by
    simp only [Complex.sub_re, Complex.ofReal_re, p0, sub_self]
  have hMGF : AnalyticAt ℂ (complexMGF id (positiveLaplaceTilt u p0)) ((p0 : ℂ) - z) :=
    analyticAt_complexMGF (by rw [hre]; exact h0)
  have hshift : AnalyticAt ℂ (fun w : ℂ => (p0 : ℂ) - w) z :=
    analyticAt_const.sub analyticAt_id
  have heq : positiveLaplaceTransform u =
      fun w : ℂ => complexMGF id (positiveLaplaceTilt u p0) ((p0 : ℂ) - w) := by
    funext w
    rw [complexMGF_positiveLaplaceTilt hu hnonneg p0]
    rw [show (p0 : ℂ) - ((p0 : ℂ) - w) = w by ring]
  rw [heq]
  exact hMGF.comp hshift

theorem analyticAt_positiveLaplaceTransform_of_abscissa_lt
    {u : ℝ → ℝ} {z : ℂ} (hu : Measurable u)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (hne : (positiveLaplaceDomain u).Nonempty)
    (hz : positiveLaplaceAbscissa u < z.re) :
    AnalyticAt ℂ (positiveLaplaceTransform u) z := by
  apply analyticAt_positiveLaplaceTransform_of_integrable_nhds hu hnonneg
  filter_upwards [isOpen_Ioi.eventually_mem hz] with p hp
  exact integrable_positiveLaplaceWeight_of_abscissa_lt hu hnonneg hne hp

theorem meromorphicOn_positiveLaplaceTransform_abscissa_halfPlane
    {u : ℝ → ℝ} (hu : Measurable u)
    (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (hne : (positiveLaplaceDomain u).Nonempty) :
    MeromorphicOn (positiveLaplaceTransform u) {z : ℂ | positiveLaplaceAbscissa u < z.re} :=
  fun z hz => (analyticAt_positiveLaplaceTransform_of_abscissa_lt hu hnonneg hne hz).meromorphicAt

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.analyticAt_positiveLaplaceTransform_of_integrable_nhds
#print axioms Zeta23.ExceptionalZero.analyticAt_positiveLaplaceTransform_of_abscissa_lt
#print axioms Zeta23.ExceptionalZero.meromorphicOn_positiveLaplaceTransform_abscissa_halfPlane
