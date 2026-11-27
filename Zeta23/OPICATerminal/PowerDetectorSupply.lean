import Zeta23.OPICATerminal.DisplacementGrowth
import Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure

/-! Supplier-free comparison of the literal energy with both native moment
slices at the original quartic cutoff. The strip supremum need not be attained.
The arithmetic upper is not an input to any theorem in this file. -/
noncomputable section
open Set Filter
open Zeta23.OPICARound4.ArithmeticFrontier
open Zeta23.OPICARound6.PrimeDeficit
open Zeta23.OPICARound3 Zeta23.CCM Zeta23.ExceptionalZero
namespace Zeta23.OPICATerminal

/-- Stronger than R2's disjunction: both original slices, same error and cutoff. -/
def BothParityPowerComparison (δ : ℝ) : Prop :=
  ∃ Y₀ : ℝ, ∀ Y : ℝ, max Y₀ 2 ≤ Y →
    EvenMomentSliceLowerBound (Real.log Y) (originalDetectorQuarticCutoff (Real.log Y))
      (literalGEnergy Y / Y^δ) ∧
    OddMomentSliceLowerBound (Real.log Y) (originalDetectorQuarticCutoff (Real.log Y))
      (literalGEnergy Y / Y^δ)

theorem bothParityPowerComparison_proved :
    ∃ δ : ℝ, 0 < δ ∧ BothParityPowerComparison δ := by
  by_cases hz : displacement = 0
  · have hline : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1/2 := by
      intro ρ hρ
      have h := displacement_bound ρ hρ
      rw [hz] at h
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm h (abs_nonneg _)))
    refine ⟨1,one_pos,Real.exp 1,fun Y hY => ?_⟩
    have hY2 : 2 ≤ Y := (le_max_right _ _).trans hY
    have hYpos : 0 < Y := by linarith
    have hlog : 1 ≤ Real.log Y := by
      rw [← Real.log_exp (1:ℝ)]
      exact Real.log_le_log (Real.exp_pos _) ((le_max_left _ _).trans hY)
    have hL : 0 < Real.log Y := by linarith
    have herr : 0 ≤ literalGEnergy Y / Y^(1:ℝ) :=
      div_nonneg (literalGEnergy_nonneg hY2) (Real.rpow_nonneg hYpos.le _)
    exact ⟨(evenMomentSliceLowerBound_zero_of_critical_line hline hL _).mono herr,
      (oddMomentSliceLowerBound_zero_of_critical_line hline hL _).mono herr⟩
  · let a := displacement
    have ha : 0 < a := lt_of_le_of_ne displacement_nonneg (Ne.symm hz)
    have hs : ∀ ρ ∈ zetaZeroConfig.carrier, |ρ.re-1/2| ≤ a := displacement_bound
    obtain ⟨Ce,hCe,he⟩ := evenMomentSliceLowerBound_explicit_of_zeroStrip
      (a := a) (α := 5*a/4) (by linarith) hs
    obtain ⟨Co,hCo,ho⟩ := oddMomentSliceLowerBound_explicit_of_zeroStrip
      (a := a) (α := 5*a/4) (by linarith) hs
    have hga : 2*a < 3*displacement := by dsimp [a] at *; linarith
    obtain ⟨B,hB⟩ := eventually_atTop.1
      (eventual_literalGEnergy_ge_rpow (show 0 < 2*a by positivity) hga)
    obtain ⟨D,hD⟩ := eventually_atTop.1
      ((tendsto_rpow_atTop (show 0 < a/4 by positivity)).eventually_ge_atTop (max Ce Co))
    refine ⟨a/2,by positivity,max (Real.exp 1) (max B D),fun Y hY => ?_⟩
    have hY2 : 2 ≤ Y := (le_max_right _ _).trans hY
    have hYpos : 0 < Y := by linarith
    have hY0 : max (Real.exp 1) (max B D) ≤ Y := (le_max_left _ _).trans hY
    have hBD : max B D ≤ Y := (le_max_right _ _).trans hY0
    have hE := hB Y ((le_max_left _ _).trans hBD)
    have hC := hD Y ((le_max_right _ _).trans hBD)
    have hlog : 1 ≤ Real.log Y := by
      rw [← Real.log_exp (1:ℝ)]
      exact Real.log_le_log (Real.exp_pos _) ((le_max_left _ _).trans hY0)
    have hpow : Real.exp (5*a/4*Real.log Y) = Y^(5*a/4:ℝ) := by
      rw [Real.rpow_def_of_pos hYpos, mul_comm]
    have hfinal : Y^(3*a/2:ℝ) ≤ literalGEnergy Y / Y^(a/2:ℝ) := by
      apply (le_div_iff₀ (Real.rpow_pos_of_pos hYpos _)).2
      rw [← Real.rpow_add hYpos, show 3*a/2+a/2=2*a by ring]
      exact hE
    have herr (C : ℝ) (hC' : C ≤ max Ce Co) :
        C * Real.exp (5*a/4*Real.log Y) ≤ literalGEnergy Y / Y^(a/2:ℝ) := by
      rw [hpow]
      calc
        _ ≤ Y^(a/4:ℝ)*Y^(5*a/4:ℝ) :=
          mul_le_mul_of_nonneg_right (hC'.trans hC) (Real.rpow_nonneg hYpos.le _)
        _ = Y^(3*a/2:ℝ) := by rw [← Real.rpow_add hYpos, show a/4+5*a/4=3*a/2 by ring]
        _ ≤ _ := hfinal
    exact ⟨(he _ hlog).mono (herr Ce (le_max_left _ _)),
      (ho _ hlog).mono (herr Co (le_max_right _ _))⟩

end Zeta23.OPICATerminal
