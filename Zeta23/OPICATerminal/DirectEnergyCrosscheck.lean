import Zeta23.OPICATerminal.DisplacementGrowth
import Zeta23.ExceptionalZero.RHTerminalConfigAttempt

/-! Independent terminal consumer: no moment-slice or detector comparison
is used in this proof. Only the literal source, eventual energy growth and
the cofinal subpower premise are needed. -/
noncomputable section
open Filter Set
open Zeta23.OPICARound6.PrimeDeficit
open Zeta23.ExceptionalZero
namespace Zeta23.OPICATerminal

theorem displacement_eq_zero_of_nativeEnergySubpower
    (hE : OPICAExtractionR1.NativeEnergySubpower) : displacement = 0 := by
  by_contra hn
  have ha : 0 < displacement := lt_of_le_of_ne displacement_nonneg (Ne.symm hn)
  have hmargin : displacement < 3 * displacement := by linarith
  obtain ⟨B,hB⟩ := eventually_atTop.1
    (eventual_literalGEnergy_ge_rpow ha hmargin)
  obtain ⟨Y,hY,hupper⟩ := hE (displacement/2) (by linarith) B
  have hY1 : 1 < Y := by linarith [(le_max_right B (2:ℝ)).trans hY]
  have hlower := hB Y ((le_max_left B (2:ℝ)).trans hY)
  have hstrict : Y^(displacement/2:ℝ) < Y^displacement :=
    Real.rpow_lt_rpow_of_exponent_lt hY1 (by linarith)
  exact (not_lt_of_ge (hlower.trans hupper)) hstrict

theorem riemannHypothesis_of_nativeEnergySubpower_direct
    (hE : OPICAExtractionR1.NativeEnergySubpower) : RiemannHypothesis := by
  intro s hz htriv hs1
  have hm : s ∈ zetaZeroConfig.carrier :=
    isNontrivialZero_of_mathlib_nontrivialZero hz htriv hs1
  have hb := displacement_bound s hm
  rw [displacement_eq_zero_of_nativeEnergySubpower hE] at hb
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hb (abs_nonneg _)))

end Zeta23.OPICATerminal
