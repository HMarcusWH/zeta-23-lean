import Zeta23.ExceptionalZero.Defs
import Zeta23.XiPrime.ExplicitFormula.ZeroFree

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex

/-- A spectral filter on the distinct nontrivial zeta zeros.  Multiplicity is kept separate in
`zeroFilterCoeff`, matching the rest of the Zeta23 zero-side API. -/
abbrev ZeroFilter := zetaZeroConfig.carrier → ℂ

/-- Multiplicity-weighted coefficient of a zero filter. -/
def zeroFilterCoeff (φ : ZeroFilter) (ρ : zetaZeroConfig.carrier) : ℂ :=
  (zeroMult ρ : ℂ) * φ ρ

/-- The convergence hypothesis used by the generic exceptional-zero detector. -/
def AbsolutelySummableZeroFilter (φ : ZeroFilter) : Prop :=
  Summable (fun ρ : zetaZeroConfig.carrier => ‖zeroFilterCoeff φ ρ‖)

/-- One filtered exponential zero mode at aperture/scale `a`.  The intended center has
`Re c = 1/2`, but keeping `c` explicit makes the analytic layer reusable. -/
def filteredZeroTerm (φ : ZeroFilter) (c : ℂ) (ρ : zetaZeroConfig.carrier) (a : ℝ) : ℂ :=
  zeroFilterCoeff φ ρ * Complex.exp ((2 * ((ρ : ℂ) - c)) * (a : ℂ))

/-- The full filtered zero family. -/
def filteredZeroFamily (φ : ZeroFilter) (c : ℂ) (a : ℝ) : ℂ :=
  ∑' ρ : zetaZeroConfig.carrier, filteredZeroTerm φ c ρ a

/-- On the critical-line center and for nonnegative scale, every exponential mode has norm at most
`exp a`.  This is deliberately coarse: it uses only the strip bound `Re ρ < 1`. -/
theorem norm_filteredZeroExp_le {c : ℂ} (hc : c.re = 1 / 2) (ρ : zetaZeroConfig.carrier)
    {a : ℝ} (ha : 0 ≤ a) :
    ‖Complex.exp ((2 * ((ρ : ℂ) - c)) * (a : ℂ))‖ ≤ Real.exp a := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hρ : (ρ : ℂ).re < 1 := ρ.2.2.2
  have hre : (((2 : ℂ) * ((ρ : ℂ) - c)) * (a : ℂ)).re =
      2 * ((ρ : ℂ).re - c.re) * a := by
    simp [Complex.mul_re]
  rw [hre, hc]
  nlinarith

/-- Absolute coefficient summability is preserved by every fixed nonnegative aperture.  This is the
basic legality seam for the generic filtered-zero route. -/
theorem summable_filteredZeroTerm {φ : ZeroFilter} {c : ℂ}
    (hφ : AbsolutelySummableZeroFilter φ) (hc : c.re = 1 / 2) {a : ℝ} (ha : 0 ≤ a) :
    Summable (fun ρ : zetaZeroConfig.carrier => filteredZeroTerm φ c ρ a) := by
  unfold AbsolutelySummableZeroFilter at hφ
  refine Summable.of_norm_bounded (hφ.mul_left (Real.exp a)) (fun ρ => ?_)
  unfold filteredZeroTerm
  rw [norm_mul]
  calc
    ‖zeroFilterCoeff φ ρ‖ * ‖Complex.exp ((2 * ((ρ : ℂ) - c)) * (a : ℂ))‖
        ≤ ‖zeroFilterCoeff φ ρ‖ * Real.exp a :=
      mul_le_mul_of_nonneg_left (norm_filteredZeroExp_le hc ρ ha) (norm_nonneg _)
    _ = Real.exp a * ‖zeroFilterCoeff φ ρ‖ := by ring

end Zeta23.ExceptionalZero
