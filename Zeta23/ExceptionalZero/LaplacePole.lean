import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Zeta23.ExceptionalZero.Defs

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex Set MeasureTheory

/-- One exponential zero-mode after fixing the spectral parameter `s`; in the intended
application `w = ρ - s`.  This definition is generic and makes no zeta claim. -/
def zeroMode (w : ℂ) (a : ℝ) : ℂ :=
  w⁻¹ * Complex.exp ((2 * w) * a)

/-- The rational kernel obtained by Laplace transforming one zero mode. -/
def laplaceZeroKernel (w z : ℂ) : ℂ :=
  1 / (w * (z - 2 * w))

/-- Elementary partial-fraction identity behind the log-derivative route. -/
theorem laplaceZeroKernel_partialFraction (w z : ℂ)
    (hw : w ≠ 0) (hz : z ≠ 0) (hwz : w - z / 2 ≠ 0) :
    laplaceZeroKernel w z = (1 / z) * (1 / w - 1 / (w - z / 2)) := by
  unfold laplaceZeroKernel
  field_simp [hw, hz, hwz]
  ring

/-- A single mode has the expected Laplace transform whenever the Laplace variable lies
strictly to the right of that mode.  This is the analytic seed of the pole detector. -/
theorem integral_laplace_zeroMode {w z : ℂ} (hw : w ≠ 0)
    (hdecay : (2 * w - z).re < 0) :
    ∫ a : ℝ in Set.Ioi 0, Complex.exp (-z * a) * zeroMode w a =
      laplaceZeroKernel w z := by
  have hmode : ∀ a : ℝ,
      Complex.exp (-z * a) * zeroMode w a =
        w⁻¹ * Complex.exp ((2 * w - z) * a) := by
    intro a
    unfold zeroMode
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hmode]
  rw [integral_const_mul]
  rw [integral_exp_mul_complex_Ioi hdecay 0]
  have hcoef : 2 * w - z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    linarith
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  unfold laplaceZeroKernel
  field_simp [hw, hcoef]
  ring

end Zeta23.ExceptionalZero
