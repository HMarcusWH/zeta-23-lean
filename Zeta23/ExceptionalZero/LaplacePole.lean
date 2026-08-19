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
  have hden : z - 2 * w ≠ 0 := by
    intro h
    apply hwz
    calc
      w - z / 2 = -(z - 2 * w) / 2 := by ring
      _ = 0 := by rw [h]; norm_num
  unfold laplaceZeroKernel
  field_simp [hw, hz, hwz, hden]
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
    calc
      Complex.exp (-z * a) * (w⁻¹ * Complex.exp ((2 * w) * a))
          = w⁻¹ * (Complex.exp (-z * a) * Complex.exp ((2 * w) * a)) := by ring
      _ = w⁻¹ * Complex.exp ((-z * a) + ((2 * w) * a)) := by
        rw [Complex.exp_add]
      _ = w⁻¹ * Complex.exp ((2 * w - z) * a) := by
        congr 2
        ring
  have heq : Set.EqOn
      (fun a : ℝ => Complex.exp (-z * a) * zeroMode w a)
      (fun a : ℝ => w⁻¹ * Complex.exp ((2 * w - z) * a))
      (Set.Ioi 0) := by
    intro a ha
    exact hmode a
  rw [setIntegral_congr_fun measurableSet_Ioi heq]
  rw [integral_const_mul]
  rw [integral_exp_mul_complex_Ioi hdecay 0]
  have hcoef : 2 * w - z ≠ 0 := by
    intro h
    rw [h] at hdecay
    norm_num at hdecay
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  unfold laplaceZeroKernel
  field_simp [hw, hcoef]
  ring

end Zeta23.ExceptionalZero
