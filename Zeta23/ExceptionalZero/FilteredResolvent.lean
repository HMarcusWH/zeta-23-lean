import Zeta23.ExceptionalZero.FilteredZeroFamily

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex

/-- One resolvent term associated to a filtered zeta zero. -/
def filteredResolventTerm (φ : ZeroFilter) (c : ℂ) (ρ : zetaZeroConfig.carrier)
    (z : ℂ) : ℂ :=
  zeroFilterCoeff φ ρ / (z - 2 * ((ρ : ℂ) - c))

/-- The filtered zero resolvent.  Its poles, when the corresponding coefficient is nonzero, are at
`z = 2 * (ρ - c)`. -/
def filteredResolvent (φ : ZeroFilter) (c z : ℂ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier, filteredResolventTerm φ c ρ z

/-- For a critical-line center, every zero-resolvent denominator is uniformly separated from zero
in the safe half-plane `Re z > 1`. -/
theorem safeHalfPlane_le_norm_resolventDenom {c z : ℂ} (hc : c.re = 1 / 2)
    (hz : 1 < z.re) (ρ : zetaZeroConfig.carrier) :
    z.re - 1 ≤ ‖z - 2 * ((ρ : ℂ) - c)‖ := by
  have hρ : (ρ : ℂ).re < 1 := ρ.2.2.2
  have hre : (z - 2 * ((ρ : ℂ) - c)).re =
      z.re - 2 * ((ρ : ℂ).re - c.re) := by
    simp [Complex.mul_re]
  have hleft : z.re - 1 < (z - 2 * ((ρ : ℂ) - c)).re := by
    rw [hre, hc]
    linarith
  calc
    z.re - 1 ≤ |(z - 2 * ((ρ : ℂ) - c)).re| := by
      have hpos : 0 < (z - 2 * ((ρ : ℂ) - c)).re := by linarith
      rw [abs_of_pos hpos]
      exact hleft.le
    _ ≤ ‖z - 2 * ((ρ : ℂ) - c)‖ := Complex.abs_re_le_norm _

/-- Absolute coefficient summability gives absolute resolvent summability throughout `Re z > 1`.
This is the safe region in which the future termwise Laplace transform can be justified directly. -/
theorem summable_filteredResolventTerm {φ : ZeroFilter} {c z : ℂ}
    (hφ : AbsolutelySummableZeroFilter φ) (hc : c.re = 1 / 2) (hz : 1 < z.re) :
    Summable (fun ρ : zetaZeroConfig.carrier => filteredResolventTerm φ c ρ z) := by
  unfold AbsolutelySummableZeroFilter at hφ
  have hδ : 0 < z.re - 1 := by linarith
  refine Summable.of_norm_bounded (hφ.mul_left (1 / (z.re - 1))) (fun ρ => ?_)
  unfold filteredResolventTerm
  rw [norm_div]
  have hden := safeHalfPlane_le_norm_resolventDenom hc hz ρ
  calc
    ‖zeroFilterCoeff φ ρ‖ / ‖z - 2 * ((ρ : ℂ) - c)‖
        ≤ ‖zeroFilterCoeff φ ρ‖ / (z.re - 1) :=
      div_le_div_of_nonneg_left (norm_nonneg _) hδ hden
    _ = (1 / (z.re - 1)) * ‖zeroFilterCoeff φ ρ‖ := by ring

end Zeta23.ExceptionalZero
