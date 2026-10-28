import Zeta23.OPICARound3.FirstNeutralCutoff
import Zeta23.OPICARound3.KernelSafeSchur

noncomputable section

namespace Zeta23.OPICARound3

open CCM

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace
  nativePoleNeutralParitySpace_normedAddCommGroup
  nativePoleNeutralParitySpace_innerProductSpace

def NeutralNewbornSchur (p : ReversalParity) (L : ℝ) (K : ℕ) : Prop :=
  let J := nativePoleNeutralParityCenteredZeroExtend p L
    (show K - 1 ≤ K by omega)
  let T := nativePoleNeutralParityCanonical p L K
  Module.finrank ℂ (isometricDetectorComplement J) = 1 ∧
    ∃ e : isometricDetectorComplement J, ‖e‖ = 1 ∧
      ((predecessorBlock J T).ker.starProjection (J.toLinearMap.adjoint (T (e : _))) ≠ 0 ∨
        ∃ hb : J.toLinearMap.adjoint (T (e : _)) ∈ (predecessorBlock J T).range,
          oneShellSchurScalar J T e hb < 0)

theorem firstNeutralCutoff_schur {L : ℝ} (hL : 0 < L)
    (p : ReversalParity) (h : ∃ K, 3 ≤ K ∧ PoleNeutralParityNegative p L K) :
    NeutralNewbornSchur p L (firstNeutralCutoff p L h) := by
  let K := firstNeutralCutoff p L h
  let J := nativePoleNeutralParityCenteredZeroExtend p L (show K - 1 ≤ K by omega)
  let T := nativePoleNeutralParityCanonical p L K
  have hshell : Module.finrank ℂ (isometricDetectorComplement J) = 1 := by
    cases p
    · exact firstNeutralCutoff_even_shell hL h
    · exact firstNeutralCutoff_odd_shell hL h
  have hT : T.IsSymmetric := by
    cases p
    · exact poleNeutralEvenCompressedCanonical_isSymmetric L K
    · exact poleNeutralOddCompressedCanonical_isSymmetric L K
  have hPSD : ∀ x, 0 ≤ (inner ℂ (predecessorBlock J T x) x).re := by
    have hprev := firstNeutralCutoff_predecessor_psd hL p h
    have hcomp := nativePoleNeutralParity_predecessor_compression_eq p hL
      (show K - 1 ≤ K by omega)
    change predecessorBlock J T = nativePoleNeutralParityCanonical p L (K - 1) at hcomp
    rw [hcomp]
    cases p <;> exact hprev
  have hneg : ∃ v, (inner ℂ (T v) v).re < 0 := by
    have hn := (firstNeutralCutoff_spec p L h).2
    cases p <;> exact hn
  obtain ⟨e, he⟩ := exists_unit_shell J hshell
  have he0 : e ≠ 0 := by intro hz; simpa [hz] using he
  exact ⟨hshell, e, he, oneShell_negative_classification J T hT hPSD hshell e he0 hneg⟩

/-- D04. The common first cutoff is the maximum of two genuine least
parity cutoffs. Every newborn parity has its own PSD predecessor and a
kernel-safe regular/resonant one-shell classification, including K=3.
No equality of eigenvalues or PSD of the earlier parity is inferred. -/
theorem first_simultaneous_neutral_negative_cutoff {L : ℝ} (hL : 0 < L)
    {K : ℕ} (hK : 3 ≤ K) (hboth : BothNeutralNegative L K) :
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
      (Ko < Ke → OddNeutralNegative L (Ke - 1)) := by
  let he : ∃ M, 3 ≤ M ∧ EvenNeutralNegative L M := ⟨K, hK, hboth.1⟩
  let ho : ∃ M, 3 ≤ M ∧ OddNeutralNegative L M := ⟨K, hK, hboth.2⟩
  let Ke := firstNeutralCutoff .even L he
  let Ko := firstNeutralCutoff .odd L ho
  have hcommon := firstBothNeutralCutoff_least hL he ho
  refine ⟨Ke, Ko, (firstNeutralCutoff_spec .even L he).1,
    (firstNeutralCutoff_spec .odd L ho).1,
    (firstNeutralCutoff_spec .even L he).2, (firstNeutralCutoff_spec .odd L ho).2,
    (fun M hM hn => firstNeutralCutoff_le .even L he hM hn),
    (fun M hM hn => firstNeutralCutoff_le .odd L ho hM hn), hcommon.2.1, hcommon.2.2,
    firstNeutralCutoff_predecessor_psd hL .even he,
    firstNeutralCutoff_predecessor_psd hL .odd ho,
    firstNeutralCutoff_schur hL .even he, firstNeutralCutoff_schur hL .odd ho,
    ?_, ?_⟩
  · exact earlier_parity_negative_at_other_predecessor hL .even .odd he ho
  · exact earlier_parity_negative_at_other_predecessor hL .odd .even ho he

end Zeta23.OPICARound3

#print axioms Zeta23.OPICARound3.firstNeutralCutoff_schur
#print axioms Zeta23.OPICARound3.first_simultaneous_neutral_negative_cutoff
