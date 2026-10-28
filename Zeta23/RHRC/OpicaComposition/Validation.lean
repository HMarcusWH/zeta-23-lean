import Zeta23.OPICAComposition.Calibration

/-! AUDIT_ONLY independent literal expected statements. No scientific closure
claim is created by compiling this facade. The answer wrappers are never
proposer constants. RH, Step4 and the independent source leaves remain OPEN. -/
noncomputable section
namespace Zeta23.RHRC.OpicaComposition.Validation
open Zeta23 Zeta23.CCM Zeta23.OPICARound3

theorem calibration_consumer
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ ∃ hL : 0 < L,
      ∃ Ke Ko : ℕ, 3 ≤ Ke ∧ 3 ≤ Ko ∧
        EvenNeutralNegative L Ke ∧ OddNeutralNegative L Ko ∧
        (∀ M, 3 ≤ M → EvenNeutralNegative L M → Ke ≤ M) ∧
        (∀ M, 3 ≤ M → OddNeutralNegative L M → Ko ≤ M) ∧
        BothNeutralNegative L (max Ke Ko) ∧
        (∀ M, 3 ≤ M → BothNeutralNegative L M → max Ke Ko ≤ M) ∧
        Nonempty (NativeNewbornSourceWitness .even L Ke hL) ∧
        Nonempty (NativeNewbornSourceWitness .odd L Ko hL) ∧
        (Ko ≤ Ke → Nonempty (NativeNewbornSourceWitness .even L (max Ke Ko) hL)) ∧
        (Ke ≤ Ko → Nonempty (NativeNewbornSourceWitness .odd L (max Ke Ko) hL)) :=
  Zeta23.OPICAComposition.cofinal_newborn_packet_calibration ρ hoff R

theorem schur_calibration_consumer :
  ∀ (ρ : zetaZeroConfig.carrier), (ρ : ℂ).re ≠ 1 / 2 → ∀ (R : ℝ),
    ∃ L : ℝ, R < L ∧ ∃ hL : 0 < L,
    ∃ Ke Ko : ℕ, 3 ≤ Ke ∧ 3 ≤ Ko ∧
      EvenNeutralNegative L Ke ∧ OddNeutralNegative L Ko ∧
      (∀ M, 3 ≤ M → EvenNeutralNegative L M → Ke ≤ M) ∧
      (∀ M, 3 ≤ M → OddNeutralNegative L M → Ko ≤ M) ∧
      BothNeutralNegative L (max Ke Ko) ∧
      (∀ M, 3 ≤ M → BothNeutralNegative L M → max Ke Ko ≤ M) ∧
      PoleNeutralParityPSD .even L (Ke - 1) ∧
      PoleNeutralParityPSD .odd L (Ko - 1) ∧
      NeutralNewbornSchur .even L Ke ∧ NeutralNewbornSchur .odd L Ko ∧
      (Ke < Ko → EvenNeutralNegative L (Ko - 1)) ∧
      (Ko < Ke → OddNeutralNegative L (Ke - 1)) :=
  Zeta23.OPICAComposition.cofinal_schur_packet_calibration

theorem context_consumers
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ 0 < L ∧ ∃ K : ℕ, 3 ≤ K ∧ BothNeutralNegative L K :=
  cofinally_both_neutral_negative_of_off_line_zero ρ hoff R

end Zeta23.RHRC.OpicaComposition.Validation

#print axioms Zeta23.RHRC.OpicaComposition.Validation.calibration_consumer
#print axioms Zeta23.RHRC.OpicaComposition.Validation.schur_calibration_consumer
#print axioms Zeta23.RHRC.OpicaComposition.Validation.context_consumers
