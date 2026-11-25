import Zeta23.OPICATerminal.Energy
import Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure

/-! Conditional power-margin transfer. The same-source comparison is OPEN.
No conclusion about a particular arithmetic source is introduced here. -/
noncomputable section
open Filter
open Zeta23.OPICARound4.ArithmeticFrontier
open Zeta23.OPICARound6.PrimeDeficit
open Zeta23.OPICARound3
open Zeta23.CCM Zeta23.ExceptionalZero
namespace OPICAR2

/-- One quantitative candidate for the remaining detector bridge. The
    native norm, quartic cutoff and entire slice bound are unchanged. -/
def PowerDetectorComparison (δ C : ℝ) : Prop :=
  ∃ Y₀ : ℝ, ∀ Y : ℝ, max Y₀ 2 ≤ Y →
    MomentSliceLowerBound (Real.log Y) (originalDetectorQuarticCutoff (Real.log Y))
      (C * literalGEnergy Y / Y^δ)

def PowerDetectorSupply : Prop :=
  ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ PowerDetectorComparison δ C

theorem directEnergyToC1_of_power_comparison {δ C : ℝ}
    (hδ : 0 < δ) (hC : 0 ≤ C) (hcomp : PowerDetectorComparison δ C) :
    OPICAExtractionR1.DirectEnergyToC1 := by
  intro hE n hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hη : 0 < δ / 2 := by linarith
  obtain ⟨Y₀,h₀⟩ := hcomp
  obtain ⟨Y₁,h₁⟩ := eventually_atTop.1
    ((tendsto_rpow_atTop hη).eventually_ge_atTop (C * (n : ℝ)))
  obtain ⟨Y,hY,henergy⟩ := hE (δ / 2) hη (max (Real.exp ((n : ℝ)+2)) (max Y₀ Y₁))
  have hbound : max (Real.exp ((n : ℝ)+2)) (max Y₀ Y₁) ≤ Y :=
    (le_max_left _ _).trans hY
  have hY2 : 2 ≤ Y := (le_max_right _ _).trans hY
  have hYpos : 0 < Y := by linarith
  have hY0 : Y₀ ≤ Y := (le_max_left _ _).trans ((le_max_right _ _).trans hbound)
  have hY1 : Y₁ ≤ Y := (le_max_right _ _).trans ((le_max_right _ _).trans hbound)
  have hcoef : C * (n : ℝ) ≤ Y^(δ/2) := h₁ Y hY1
  have hlog : (n : ℝ)+2 ≤ Real.log Y := by
    rw [← Real.log_exp ((n : ℝ)+2)]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_left _ _).trans hbound)
  have hprod : (C * literalGEnergy Y) * (n : ℝ) ≤ Y^δ := by
    calc
      _ = (C * (n : ℝ)) * literalGEnergy Y := by ring
      _ ≤ (C * (n : ℝ)) * Y^(δ/2) :=
        mul_le_mul_of_nonneg_left henergy (mul_nonneg hC hnpos.le)
      _ ≤ Y^(δ/2) * Y^(δ/2) :=
        mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg hYpos.le _)
      _ = Y^δ := by rw [← Real.rpow_add hYpos, show δ/2+δ/2=δ by ring]
  have hsmall : C * literalGEnergy Y / Y^δ ≤ 1/(n : ℝ) := by
    apply (div_le_div_iff₀ (Real.rpow_pos_of_pos hYpos _) hnpos).2
    simpa only [one_mul] using hprod
  exact ⟨Real.log Y,hlog,(h₀ Y (max_le hY0 hY2)).mono hsmall⟩

theorem directEnergyToC1_of_power_supply (h : PowerDetectorSupply) :
    OPICAExtractionR1.DirectEnergyToC1 := by
  obtain ⟨δ,C,hδ,hC,hcomp⟩ := h
  exact directEnergyToC1_of_power_comparison hδ hC hcomp

end OPICAR2
