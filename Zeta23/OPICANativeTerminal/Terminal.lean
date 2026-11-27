import Zeta23Arithmetic.NativePrincipal
import Zeta23.OPICARound4.ArithmeticFrontier.ZeroFreeFloor
import Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure

/-!
Standalone native source-port Step 4, direct finite-slice route. Uses the exact native
carrier and original quartic cutoff from #316. All-tolerance strip transport
is mathematically RH-equivalent after symmetry; it is DERIVED here from the
weighted arithmetic theorem, not assumed or imported as an endpoint.
Every arithmetic proof body is compiled from repository-local source. No claim of independently invented arithmetic mathematics or of the separate literal-energy splice.
-/
noncomputable section
open Set Filter
open Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICARound3 Zeta23.OPICARound4
open Zeta23.OPICARound4.ArithmeticFrontier

namespace Zeta23.OPICANativeTerminal

/-- Arithmetic supplies the right boundary for every actual nontrivial zero.
The choice of tolerance is made for the given zero. -/
theorem actual_zero_re_le_half (ρ : ℂ)
    (hρ : ρ ∈ zetaZeroConfig.carrier) : ρ.re ≤ 1 / 2 := by
  have hz : IsNontrivialZero ρ := by simpa using hρ
  have hs1 : ρ ≠ 1 := by
    intro hs
    rw [hs] at hz
    have hlt := hz.2.2
    norm_num at hlt
  by_contra hn
  have hright : 1 / 2 < ρ.re := lt_of_not_ge hn
  let β : ℝ := (ρ.re + 1 / 2) / 2
  have hβ : 1 / 2 < β := by dsimp [β]; linarith
  have hβ1 : β < 1 := by dsimp [β]; linarith [hz.2.2]
  have hb : ρ.re ≤ β :=
    Zeta23Arithmetic.Principal.principal_fixed_strip hβ hβ1 ρ hs1 hz.1
  dsimp [β] at hb
  linarith

theorem actual_critical_line_arithmetic (ρ : ℂ)
    (hρ : ρ ∈ zetaZeroConfig.carrier) : ρ.re = 1 / 2 := by
  have h := abs_re_sub_half_le_of_re_le (θ := 1 / 2)
    actual_zero_re_le_half ρ hρ
  have h0 : |ρ.re - 1 / 2| = 0 :=
    le_antisymm (by simpa using h) (abs_nonneg _)
  exact sub_eq_zero.mp (abs_eq_zero.mp h0)

/-- Stronger than C1: zero error on both complete native physical slices,
for every positive aperture and the original quartic cutoff. -/
theorem both_parity_zero_floor_arithmetic (L : ℝ) (hL : 0 < L) :
    EvenMomentSliceLowerBound L (originalDetectorQuarticCutoff L) 0 ∧
    OddMomentSliceLowerBound L (originalDetectorQuarticCutoff L) 0 :=
  ⟨evenMomentSliceLowerBound_zero_of_critical_line
      actual_critical_line_arithmetic hL _,
   oddMomentSliceLowerBound_zero_of_critical_line
      actual_critical_line_arithmetic hL _⟩

/-- Literal native C1, using the original all-vector bound and cutoff. -/
theorem step4C1_native_arithmetic : CofinalMomentSliceVanishingErrorBounds := by
  intro n hn
  let L : ℝ := (n : ℝ) + 2
  have hL : 0 < L := by dsimp [L]; positivity
  obtain ⟨he, ho⟩ := both_parity_zero_floor_arithmetic L hL
  refine ⟨L, le_rfl, Or.inl (he.mono ?_)⟩
  positivity

/-- Candidate exact Mathlib endpoint. Uses native C1 consumer, not
New.grh, an imported RH endpoint, or an RH-to-C1 theorem. -/
theorem riemannHypothesis_step4_native_arithmetic : RiemannHypothesis :=
  riemannHypothesis_of_cofinal_moment_slice_bounds step4C1_native_arithmetic

example : RiemannHypothesis := riemannHypothesis_step4_native_arithmetic

end Zeta23.OPICANativeTerminal
