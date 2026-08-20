import Zeta23.Poisson.PaperFT

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex MeasureTheory

/-- Physical-space translation by `t`: `translateRight f t (x) = f (x - t)`. -/
def translateRight (f : ℝ → ℂ) (t : ℝ) : ℝ → ℂ :=
  fun x => f (x - t)

/-- Under the paper convention `paperFT f z = ∫ f(x) exp(i z x) dx`, translating physical space
by `t` multiplies the transform by `exp(i z t)`.  This sign is claim-bearing for the R001
exceptional-zero amplification and is therefore proved explicitly. -/
theorem paperFT_translateRight (f : ℝ → ℂ) (t : ℝ) (z : ℂ) :
    paperFT (translateRight f t) z = cexp (I * z * t) * paperFT f z := by
  unfold paperFT translateRight
  rw [← integral_add_right_eq_self
    (μ := volume) (fun x : ℝ => f (x - t) * cexp (I * z * x)) t]
  simp only [add_sub_cancel_right]
  rw [← integral_const_mul_C]
  congr 1 with x
  have harg :
      I * z * ((x + t : ℝ) : ℂ) = I * z * (t : ℂ) + I * z * (x : ℂ) := by
    push_cast
    ring
  rw [harg, Complex.exp_add]
  ring

end Zeta23.ExceptionalZero
