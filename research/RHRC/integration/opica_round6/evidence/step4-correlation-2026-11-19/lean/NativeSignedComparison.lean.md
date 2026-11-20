# Historical source for NativeSignedComparison

Recorded source SHA-256 is `7ad4464957b6f51f0a888c8d1a7f6ee5709bc8a2643769940f25ac7fa69d4742`.

```lean
import Zeta23.OPICAFollowup.NativeWindowRate

/-! A conditional use of the actual fixed-source rate. The comparison energy and
the cofinal signed inequality must be supplied independently for the same times. -/

noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Zeta23 Zeta23.OPICAFollowup

namespace Step4.NativeSignedComparison

/-- The full literal one-copy prime-power field on the original terminal window. -/
def terminalEnergy (C T : ℝ) : ℝ :=
  ∫ t : ℝ in Icc (T - C * Real.log T) T, |primeFieldFamily 0 t| ^ 2

/-- An independently subexponential nonnegative comparison and nonpositive
signed excess at arbitrarily late real horizons force zero displacement. -/
theorem displacement_eq_zero_of_cofinal_nonpositive
    {C : ℝ} (hC : 1 < C) (E : ℝ → NNReal)
    (hRate : Tendsto (fun T : ℝ => Real.log (1 + (E T : ℝ)) / (2*T)) atTop (𝓝 0))
    (hSigned : ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧ terminalEnergy C T - (E T : ℝ) ≤ 0) :
    nativeZeroDisplacementSup = 0 := by
  have hNative : Tendsto (fun T : ℝ => Real.log (1 + terminalEnergy C T) / (2*T))
      atTop (𝓝 nativeZeroDisplacementSup) := native_fixed_source_window_rate 0 C hC
  have hFreq : ∃ᶠ T : ℝ in atTop,
      Real.log (1 + terminalEnergy C T) / (2*T) ≤ Real.log (1 + (E T : ℝ)) / (2*T) := by
    apply frequently_atTop.2
    intro R
    obtain ⟨T, hT, hSignedT⟩ := hSigned (max R 1)
    have hpos : 0 < 2*T := by linarith [le_trans (le_max_right R 1) hT]
    have henergy : 0 ≤ terminalEnergy C T := integral_nonneg fun t => sq_nonneg _
    exact ⟨T, (le_max_left R 1).trans hT,
      div_le_div_of_nonneg_right (Real.log_le_log (by linarith) (by linarith)) hpos.le⟩
  exact le_antisymm (le_of_tendsto_of_tendsto_of_frequently hNative hRate hFreq)
    native_zero_sup_bounds.1

/-- This implication concerns every member of the genuine nontrivial zero carrier. -/
theorem no_right_zero_of_cofinal_nonpositive
    {C : ℝ} (hC : 1 < C) (E : ℝ → NNReal)
    (hRate : Tendsto (fun T : ℝ => Real.log (1 + (E T : ℝ)) / (2*T)) atTop (𝓝 0))
    (hSigned : ∀ R : ℝ, ∃ T : ℝ, R ≤ T ∧ terminalEnergy C T - (E T : ℝ) ≤ 0) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re ≤ 1/2 := by
  have heq := displacement_eq_zero_of_cofinal_nonpositive hC E hRate hSigned
  intro ρ
  have h := native_zero_sup_bounds.2.2.1 ρ
  rw [heq] at h
  linarith [le_trans (le_max_left ((ρ : ℂ).re - 1/2) 0) h]

#print axioms displacement_eq_zero_of_cofinal_nonpositive
#print axioms no_right_zero_of_cofinal_nonpositive

end Step4.NativeSignedComparison
```
