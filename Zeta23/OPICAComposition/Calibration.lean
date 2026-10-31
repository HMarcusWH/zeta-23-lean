import Zeta23.OPICARound3.CofinalSimultaneousNegative
import Zeta23.OPICARound3.NewbornSource

/-! Proposed calibration source. NOT COMPILED IN THIS BUILD-KIT REVIEW.
The target preserves all D05 clauses under D02's actual off-line-zero premise.
This is an integration calibration, not a new independent source restriction.
D05 provides unit shell e and nonzero w; no unit-w premise is added.
External reported timed-out checking does not qualify this template.
Do not expose this answer declaration as an allowed proposer constant. -/

noncomputable section
namespace Zeta23.OPICAComposition
open CCM OPICARound3

def CofinalNewbornPacket
    : Prop := ∀ (ρ : zetaZeroConfig.carrier), (ρ : ℂ).re ≠ 1 / 2 → ∀ (R : ℝ),
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
        (Ke ≤ Ko → Nonempty (NativeNewbornSourceWitness .odd L (max Ke Ko) hL))

def CofinalSchurPacket : Prop :=
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
      (Ko < Ke → OddNeutralNegative L (Ke - 1))

theorem cofinal_newborn_packet_calibration
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
        (Ke ≤ Ko → Nonempty (NativeNewbornSourceWitness .odd L (max Ke Ko) hL)) := by
  obtain ⟨L, hRL, hL, K, hK, hboth⟩ :=
    Zeta23.OPICARound3.cofinally_both_neutral_negative_of_off_line_zero ρ hoff R
  obtain ⟨Ke, Ko, hpacket⟩ :=
    Zeta23.OPICARound3.first_simultaneous_newborn_source_witnesses hL hK hboth
  exact ⟨L, hRL, hL, Ke, Ko, hpacket⟩



theorem cofinal_schur_packet_calibration : CofinalSchurPacket := by
  intro ρ hoff R
  obtain ⟨L, hRL, hL, K, hK, hboth⟩ :=
    cofinally_both_neutral_negative_of_off_line_zero ρ hoff R
  obtain ⟨Ke, Ko, hpacket⟩ := first_simultaneous_neutral_negative_cutoff hL hK hboth
  exact ⟨L, hRL, hL, Ke, Ko, hpacket⟩

end Zeta23.OPICAComposition
