import Zeta23.Poisson.PaperFT
import Mathlib.Analysis.Fourier.Convolution

noncomputable section

namespace Zeta23

open Complex MeasureTheory Real ContinuousLinearMap
open scoped Convolution FourierTransform

/-!
# Complex-frequency convolution law for the paper Fourier transform

Mathlib's convolution theorem is stated for its real-frequency Fourier
transform.  The project's `paperFT` accepts a complex spectral argument.  For
compactly supported continuous functions the missing bridge is obtained by
tilting each input by the real exponential coming from the imaginary part of
the spectral parameter, applying Mathlib's real-frequency convolution theorem,
and untilting.

This is a neutral Fourier helper; it does not change any explicit-formula
hypothesis or interface.
-/

/-- Exponential tilt converting a complex `paperFT` frequency to its real
part. -/
def paperFTTilt (f : ℝ → ℂ) (b : ℝ) : ℝ → ℂ :=
  fun x => f x * Complex.exp (-(b : ℂ) * (x : ℂ))

/-- A complex-frequency `paperFT` is a real-frequency `paperFT` of the
exponentially tilted function. -/
theorem paperFT_eq_tilt_re (f : ℝ → ℂ) (z : ℂ) :
    paperFT f z = paperFT (paperFTTilt f z.im) z.re := by
  rw [paperFT_def, paperFT_def]
  apply integral_congr_ae
  filter_upwards with x
  unfold paperFTTilt
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

/-- Exponential tilting commutes exactly with convolution. -/
theorem paperFTTilt_convolution
    (f g : ℝ → ℂ) (b : ℝ) :
    paperFTTilt (f ⋆[mul ℂ ℂ, volume] g) b =
      paperFTTilt f b ⋆[mul ℂ ℂ, volume] paperFTTilt g b := by
  funext x
  unfold paperFTTilt MeasureTheory.convolution
  rw [← integral_mul_const_C]
  apply integral_congr_ae
  filter_upwards with t
  have hexp :
      Complex.exp (-(b : ℂ) * (x : ℂ)) =
        Complex.exp (-(b : ℂ) * (t : ℂ)) *
          Complex.exp (-(b : ℂ) * ((x - t : ℝ) : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [hexp]
  ring

/-- Tilting preserves continuity. -/
theorem continuous_paperFTTilt
    {f : ℝ → ℂ} (hf : Continuous f) (b : ℝ) :
    Continuous (paperFTTilt f b) := by
  unfold paperFTTilt
  fun_prop

/-- Tilting preserves compact support because the exponential factor never
enlarges the support of the left factor. -/
theorem hasCompactSupport_paperFTTilt
    {f : ℝ → ℂ} (hf : HasCompactSupport f) (b : ℝ) :
    HasCompactSupport (paperFTTilt f b) := by
  unfold paperFTTilt
  exact hf.mul_right

/-- Continuous compactly supported inputs remain integrable after tilting. -/
theorem integrable_paperFTTilt
    {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (b : ℝ) :
    Integrable (paperFTTilt f b) := by
  exact (continuous_paperFTTilt hf b).integrable_of_hasCompactSupport
    (hasCompactSupport_paperFTTilt hfc b)

/-- Complex-frequency convolution product law in the project's native
`paperFT` convention. -/
theorem paperFT_mul_convolution_eq_of_continuous_compactSupport
    {f g : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hg : Continuous g) (hgc : HasCompactSupport g)
    (z : ℂ) :
    paperFT (f ⋆[mul ℂ ℂ, volume] g) z =
      paperFT f z * paperFT g z := by
  have hft : Integrable (paperFTTilt f z.im) :=
    integrable_paperFTTilt hf hfc z.im
  have hgt : Integrable (paperFTTilt g z.im) :=
    integrable_paperFTTilt hg hgc z.im
  calc
    paperFT (f ⋆[mul ℂ ℂ, volume] g) z =
        paperFT (paperFTTilt (f ⋆[mul ℂ ℂ, volume] g) z.im) z.re :=
      paperFT_eq_tilt_re _ z
    _ = paperFT
        (paperFTTilt f z.im ⋆[mul ℂ ℂ, volume] paperFTTilt g z.im) z.re := by
      rw [paperFTTilt_convolution]
    _ = paperFT (paperFTTilt f z.im) z.re *
        paperFT (paperFTTilt g z.im) z.re := by
      rw [paperFT_ofReal_eq_fourier,
        Real.fourier_mul_convolution_eq hft hgt,
        ← paperFT_ofReal_eq_fourier,
        ← paperFT_ofReal_eq_fourier]
    _ = paperFT f z * paperFT g z := by
      rw [← paperFT_eq_tilt_re f z, ← paperFT_eq_tilt_re g z]

end Zeta23

#print axioms Zeta23.paperFT_mul_convolution_eq_of_continuous_compactSupport
