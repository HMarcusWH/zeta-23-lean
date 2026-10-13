import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic.Ring

/-!
# The literal positive Laplace tilt and its transport identities

The measure is the density u(t) exp(-p0*t) against Lebesgue measure on
the nonnegative half-line. It is unnormalized. Genuine Laplace
integrability at p0 proves its finiteness. Exponential integrability
transports to the parameter p0-h, and its complex MGF is the Laplace
transform at exactly p0-z.

Nonnegativity of u on the half-line and measurability are explicit.
No boundary singularity or input about the actual zeta tail is assumed.
-/

noncomputable section

open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace Zeta23.ExceptionalZero

/-- Lebesgue measure on the nonnegative half-line, including its zero endpoint. -/
def positiveLaplaceHalfLine : Measure ℝ := volume.restrict (Ici 0)

def positiveLaplaceWeight (u : ℝ → ℝ) (p t : ℝ) : ℝ :=
  u t * Real.exp (-p * t)

/-- The actual unnormalized positive measure used for the Laplace tilt. -/
def positiveLaplaceTilt (u : ℝ → ℝ) (p0 : ℝ) : Measure ℝ :=
  positiveLaplaceHalfLine.withDensity
    (fun t => ENNReal.ofReal (positiveLaplaceWeight u p0 t))

def positiveLaplaceTransform (u : ℝ → ℝ) (p : ℂ) : ℂ :=
  ∫ t : ℝ, (u t : ℂ) * Complex.exp (-p * (t : ℂ)) ∂positiveLaplaceHalfLine

private theorem measurable_positiveLaplaceWeight {u : ℝ → ℝ}
    (hu : Measurable u) (p : ℝ) : Measurable (positiveLaplaceWeight u p) :=
  hu.mul ((measurable_const.mul measurable_id).exp)

private theorem positiveLaplaceWeight_ae_nonneg {u : ℝ → ℝ}
    (hu : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t) (p : ℝ) :
    ∀ᵐ t ∂positiveLaplaceHalfLine, 0 ≤ positiveLaplaceWeight u p t := by
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact mul_nonneg (hu t ht) (Real.exp_pos _).le

/-- Actual Laplace integrability proves finiteness of the literal measure. -/
theorem positiveLaplaceTilt_isFiniteMeasure {u : ℝ → ℝ} {p0 : ℝ}
    (hLaplace : Integrable (positiveLaplaceWeight u p0) positiveLaplaceHalfLine) :
    IsFiniteMeasure (positiveLaplaceTilt u p0) :=
  isFiniteMeasure_withDensity_ofReal hLaplace.hasFiniteIntegral

/-- The measure's mass is the actual Laplace integral, without normalization. -/
theorem positiveLaplaceTilt_apply_univ {u : ℝ → ℝ} {p0 : ℝ}
    (hu : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (hLaplace : Integrable (positiveLaplaceWeight u p0) positiveLaplaceHalfLine) :
    positiveLaplaceTilt u p0 univ =
      ENNReal.ofReal (∫ t, positiveLaplaceWeight u p0 t ∂positiveLaplaceHalfLine) := by
  rw [positiveLaplaceTilt, withDensity_apply _ measurableSet_univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal hLaplace
    (positiveLaplaceWeight_ae_nonneg hu p0)).symm

/-- The identity random variable is nonnegative almost everywhere under the tilt. -/
theorem positiveLaplaceTilt_ae_nonneg (u : ℝ → ℝ) (p0 : ℝ) :
    ∀ᵐ t ∂positiveLaplaceTilt u p0, 0 ≤ t := by
  have hbase : ∀ᵐ t ∂positiveLaplaceHalfLine, 0 ≤ t :=
    ae_restrict_mem measurableSet_Ici
  exact (withDensity_absolutelyContinuous positiveLaplaceHalfLine
    (fun t => ENNReal.ofReal (positiveLaplaceWeight u p0 t))).ae_le hbase

/-- Exponential integrability under the literal tilt is exactly Laplace
integrability at the real parameter p0-h. -/
theorem integrable_exp_positiveLaplaceTilt_iff {u : ℝ → ℝ}
    (hu : Measurable u) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (p0 h : ℝ) :
    Integrable (fun t : ℝ => Real.exp (h * t)) (positiveLaplaceTilt u p0) ↔
      Integrable (positiveLaplaceWeight u (p0 - h)) positiveLaplaceHalfLine := by
  rw [positiveLaplaceTilt, integrable_withDensity_iff_integrable_smul'
    (measurable_positiveLaplaceWeight hu p0).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  rw [ENNReal.toReal_ofReal
    (mul_nonneg (hnonneg t ht) (Real.exp_pos _).le)]
  change positiveLaplaceWeight u p0 t * Real.exp (h * t) =
    positiveLaplaceWeight u (p0 - h) t
  unfold positiveLaplaceWeight
  rw [mul_assoc, ← Real.exp_add]
  have heq : -p0 * t + h * t = -(p0 - h) * t := by ring
  rw [heq]

private theorem positiveLaplaceTilt_complex_weight {u : ℝ → ℝ}
    {p0 t : ℝ} (ht : 0 ≤ u t) (z : ℂ) :
    (ENNReal.ofReal (positiveLaplaceWeight u p0 t)).toReal •
        Complex.exp (z * (t : ℂ)) =
      (u t : ℂ) * Complex.exp (-((p0 : ℂ) - z) * (t : ℂ)) := by
  rw [ENNReal.toReal_ofReal (mul_nonneg ht (Real.exp_pos _).le)]
  unfold positiveLaplaceWeight
  rw [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_exp,
    mul_assoc, ← Complex.exp_add]
  have heq : ((-p0 * t : ℝ) : ℂ) + z * (t : ℂ) =
      -((p0 : ℂ) - z) * (t : ℂ) := by
    push_cast
    ring
  rw [heq]

/-- Complex exponential integrability also transports with the exact shift p0-z. -/
theorem integrable_cexp_positiveLaplaceTilt_iff {u : ℝ → ℝ}
    (hu : Measurable u) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (p0 : ℝ) (z : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (z * (t : ℂ))) (positiveLaplaceTilt u p0) ↔
      Integrable (fun t : ℝ =>
        (u t : ℂ) * Complex.exp (-((p0 : ℂ) - z) * (t : ℂ)))
        positiveLaplaceHalfLine := by
  rw [positiveLaplaceTilt, integrable_withDensity_iff_integrable_smul'
    (measurable_positiveLaplaceWeight hu p0).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact positiveLaplaceTilt_complex_weight (hnonneg t ht) z

/-- The actual complex MGF of the tilt equals the actual Laplace transform
at p0-z. This is a change-of-measure identity, without a convergence claim. -/
theorem complexMGF_positiveLaplaceTilt {u : ℝ → ℝ}
    (hu : Measurable u) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t)
    (p0 : ℝ) (z : ℂ) :
    complexMGF id (positiveLaplaceTilt u p0) z =
      positiveLaplaceTransform u ((p0 : ℂ) - z) := by
  rw [complexMGF, positiveLaplaceTilt, integral_withDensity_eq_integral_toReal_smul
    (measurable_positiveLaplaceWeight hu p0).ennreal_ofReal
    (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold positiveLaplaceTransform
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact positiveLaplaceTilt_complex_weight (hnonneg t ht) z

/-- A genuine neighborhood of Laplace integrability supplies the interior
MGF base point needed by the positive continuation theorem. -/
theorem zero_mem_interior_integrableExpSet_positiveLaplaceTilt {u : ℝ → ℝ}
    (hu : Measurable u) (hnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ u t) {p0 : ℝ}
    (hLaplace : ∀ᶠ p in 𝓝 p0,
      Integrable (positiveLaplaceWeight u p) positiveLaplaceHalfLine) :
    0 ∈ interior (integrableExpSet id (positiveLaplaceTilt u p0)) := by
  apply mem_interior_iff_mem_nhds.mpr
  have hshift : Tendsto (fun h : ℝ => p0 - h) (𝓝 0) (𝓝 p0) := by
    simpa only [sub_zero] using (continuous_const.sub continuous_id).tendsto (0 : ℝ)
  filter_upwards [hshift.eventually hLaplace] with h hh
  exact (integrable_exp_positiveLaplaceTilt_iff hu hnonneg p0 h).mpr hh

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.positiveLaplaceTilt_isFiniteMeasure
#print axioms Zeta23.ExceptionalZero.positiveLaplaceTilt_apply_univ
#print axioms Zeta23.ExceptionalZero.positiveLaplaceTilt_ae_nonneg
#print axioms Zeta23.ExceptionalZero.integrable_exp_positiveLaplaceTilt_iff
#print axioms Zeta23.ExceptionalZero.integrable_cexp_positiveLaplaceTilt_iff
#print axioms Zeta23.ExceptionalZero.complexMGF_positiveLaplaceTilt
#print axioms Zeta23.ExceptionalZero.zero_mem_interior_integrableExpSet_positiveLaplaceTilt
