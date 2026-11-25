import Zeta23.OPICATerminal.PowerDetectorSupply

open Zeta23.OPICATerminal
open Zeta23.OPICARound4.ArithmeticFrontier
open Zeta23.OPICARound6.PrimeDeficit
open Zeta23.OPICARound3 Zeta23.CCM Zeta23.ExceptionalZero

example : ∃ δ : ℝ, 0 < δ ∧ ∃ Y₀ : ℝ, ∀ Y : ℝ, max Y₀ 2 ≤ Y →
    EvenMomentSliceLowerBound (Real.log Y) (originalDetectorQuarticCutoff (Real.log Y))
      (literalGEnergy Y / Y^δ) ∧
    OddMomentSliceLowerBound (Real.log Y) (originalDetectorQuarticCutoff (Real.log Y))
      (literalGEnergy Y / Y^δ) :=
  bothParityPowerComparison_proved

example : ∃ δ C : ℝ, 0 < δ ∧ 0 ≤ C ∧ ∃ Y₀ : ℝ, ∀ Y : ℝ, max Y₀ 2 ≤ Y →
    MomentSliceLowerBound (Real.log Y) (originalDetectorQuarticCutoff (Real.log Y))
      (C * literalGEnergy Y / Y^δ) :=
  powerDetectorSupply_proved

example : (∀ η : ℝ, 0 < η → ∀ Y₀ : ℝ,
    ∃ Y : ℝ, max Y₀ 2 ≤ Y ∧ literalGEnergy Y ≤ Y^η) →
    (∀ n : ℕ, 1 ≤ n → ∃ L : ℝ, (n : ℝ)+2 ≤ L ∧
      MomentSliceLowerBound L (originalDetectorQuarticCutoff L) (1/(n:ℝ))) :=
  directEnergyToC1_proved

#print axioms Zeta23.OPICATerminal.principalG_eq_literal
#print axioms Zeta23.OPICATerminal.literalGEnergy_nonneg
#print axioms Deduction.poleData
#print axioms Deduction.landau_window
#print axioms Zeta23.OPICATerminal.eventual_literalGEnergy_ge_rpow
#print axioms Zeta23.OPICATerminal.bothParityPowerComparison_proved
#print axioms Zeta23.OPICATerminal.powerDetectorSupply_proved
#print axioms Zeta23.OPICATerminal.directEnergyToC1_proved
#print axioms Zeta23.OPICATerminal.riemannHypothesis_of_nativeEnergySubpower
