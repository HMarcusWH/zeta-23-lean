import Zeta23.CCM.FrozenCanonicalSourceComplex
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

noncomputable section

namespace Zeta23.CCM

open Complex Set Filter

/-!
# FIRST-BAD-RIGIDITY-E4-A4R1c: genuine aperture holomorphy

This module begins the post-#144 analytic layer.  In particular it repairs the
removable singularity in the scalar factor used by the canonical aperture
remainder without changing the already theorem-locked #144 production
definitions.

The existing `complexApertureScalarFactor` is intentionally totalized by Lean
and therefore has the wrong point value at zero.  The auxiliary removable
extension below has the correct value `2`, is analytic at zero, and will be
proved equal to the existing factor on the punctured domain where the latter
is mathematically used.

No determinant nonidentity, dense regularity, sign, negative-root exclusion,
or RH claim is made here.
-/

/-- Removable extension of
`z * (exp z + 1) / (exp z - 1)`, expressed using the already-entire divided
exponential slope.  At zero this has the mathematically correct value `2`. -/
def complexApertureScalarFactorRemovable (z : ℂ) : ℂ :=
  (Complex.exp z + 1) / complexArchExpSlope z

@[simp] theorem complexApertureScalarFactorRemovable_zero :
    complexApertureScalarFactorRemovable 0 = 2 := by
  simp [complexApertureScalarFactorRemovable]
  norm_num

/-- The divided exponential slope stays nonzero in a genuine neighborhood of
zero. -/
theorem eventually_complexArchExpSlope_ne_zero :
    ∀ᶠ z in nhds (0 : ℂ), complexArchExpSlope z ≠ 0 := by
  have hcont : ContinuousAt complexArchExpSlope 0 :=
    (differentiable_complexArchExpSlope 0).continuousAt
  have hne : complexArchExpSlope 0 ≠ 0 := by simp
  exact hcont.eventually_ne hne

/-- The removable scalar factor is genuinely analytic at zero. -/
theorem analyticAt_complexApertureScalarFactorRemovable_zero :
    AnalyticAt ℂ complexApertureScalarFactorRemovable 0 := by
  rw [analyticAt_iff_eventually_differentiableAt]
  filter_upwards [eventually_complexArchExpSlope_ne_zero] with z hz
  unfold complexApertureScalarFactorRemovable
  have hnum : Differentiable ℂ (fun w : ℂ => Complex.exp w + 1) := by
    fun_prop
  exact (hnum z).div (differentiable_complexArchExpSlope z) hz

/-- At the removable point the corrected scalar factor lies in the principal
logarithm's slit plane. -/
theorem complexApertureScalarFactorRemovable_zero_mem_slitPlane :
    complexApertureScalarFactorRemovable 0 ∈ Complex.slitPlane := by
  rw [complexApertureScalarFactorRemovable_zero, Complex.mem_slitPlane_iff]
  norm_num

/-- Hence the principal logarithm of the corrected scalar factor is analytic
at zero. -/
theorem analyticAt_log_complexApertureScalarFactorRemovable_zero :
    AnalyticAt ℂ (fun z : ℂ => Complex.log (complexApertureScalarFactorRemovable z)) 0 :=
  analyticAt_complexApertureScalarFactorRemovable_zero.clog
    complexApertureScalarFactorRemovable_zero_mem_slitPlane

/-- Corrected scalar remainder used only as an analytic auxiliary object near
zero.  The production remainder remains `complexApertureScalarRemainder`. -/
def complexApertureScalarRemainderRemovable (z : ℂ) : ℂ :=
  Complex.log (complexApertureScalarFactorRemovable z) -
    ((Real.eulerMascheroniConstant + Real.log (4 * Real.pi) : ℝ) : ℂ)

/-- The corrected scalar remainder is analytic at zero. -/
theorem analyticAt_complexApertureScalarRemainderRemovable_zero :
    AnalyticAt ℂ complexApertureScalarRemainderRemovable 0 := by
  unfold complexApertureScalarRemainderRemovable
  exact analyticAt_log_complexApertureScalarFactorRemovable_zero.sub analyticAt_const

end Zeta23.CCM

#print axioms Zeta23.CCM.analyticAt_complexApertureScalarFactorRemovable_zero
#print axioms Zeta23.CCM.analyticAt_complexApertureScalarRemainderRemovable_zero
