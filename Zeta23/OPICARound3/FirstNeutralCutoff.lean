import Zeta23.OPICARound3.NeutralParityCover
import Zeta23.CCM.CanonicalPoleNeutralBottomNFlow

noncomputable section

namespace Zeta23.OPICARound3

open CCM
open scoped Classical

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-! Least cutoffs concern the actual physical neutral spaces. In particular,
the PSD conclusion below is for a newborn parity's own predecessor. -/

def PoleNeutralParityPSD (p : ReversalParity) (L : ℝ) (K : ℕ) : Prop :=
  match p with
  | .even => ∀ u : poleNeutralEvenSubspace L K,
      0 ≤ (inner ℂ (poleNeutralEvenCompressedCanonical L K u) u).re
  | .odd => ∀ u : poleNeutralOddSubspace L K,
      0 ≤ (inner ℂ (poleNeutralOddCompressedCanonical L K u) u).re

theorem poleNeutralParityPSD_iff_not_negative (p : ReversalParity) (L : ℝ) (K : ℕ) :
    PoleNeutralParityPSD p L K ↔ ¬ PoleNeutralParityNegative p L K := by
  cases p <;> simp [PoleNeutralParityPSD, PoleNeutralParityNegative,
    EvenNeutralNegative, OddNeutralNegative, not_lt]

theorem poleNeutralParityNegative_mono {L : ℝ} (hL : 0 < L)
    (p : ReversalParity) {N M : ℕ} (hNM : N ≤ M)
    (h : PoleNeutralParityNegative p L N) : PoleNeutralParityNegative p L M := by
  cases p
  · obtain ⟨u, hu⟩ := h
    refine ⟨poleNeutralEvenCenteredZeroExtend L hNM u, ?_⟩
    simpa only [inner_poleNeutralEvenCompressedCanonical_centeredZeroExtend hL hNM] using hu
  · obtain ⟨u, hu⟩ := h
    refine ⟨poleNeutralOddCenteredZeroExtend L hNM u, ?_⟩
    simpa only [inner_poleNeutralOddCompressedCanonical_centeredZeroExtend hL hNM] using hu

theorem poleNeutralParityPSD_two {L : ℝ} (hL : 0 < L) (p : ReversalParity) :
    PoleNeutralParityPSD p L 2 := by
  cases p
  · intro u
    have hdim : Module.finrank ℂ (poleNeutralEvenSubspace L 2) = 0 :=
      finrank_poleNeutralEvenSubspace hL 2 (by omega)
    letI : Subsingleton (poleNeutralEvenSubspace L 2) := Module.finrank_zero_iff.mp hdim
    have hz : u = 0 := Subsingleton.elim _ _
    simp [hz]
  · intro u
    have hdim : Module.finrank ℂ (poleNeutralOddSubspace L 2) = 0 :=
      finrank_poleNeutralOddSubspace hL 2 (by omega)
    letI : Subsingleton (poleNeutralOddSubspace L 2) := Module.finrank_zero_iff.mp hdim
    have hz : u = 0 := Subsingleton.elim _ _
    simp [hz]

def firstNeutralCutoff (p : ReversalParity) (L : ℝ)
    (h : ∃ K, 3 ≤ K ∧ PoleNeutralParityNegative p L K) : ℕ := Nat.find h

theorem firstNeutralCutoff_spec (p : ReversalParity) (L : ℝ)
    (h : ∃ K, 3 ≤ K ∧ PoleNeutralParityNegative p L K) :
    3 ≤ firstNeutralCutoff p L h ∧
      PoleNeutralParityNegative p L (firstNeutralCutoff p L h) := Nat.find_spec h

theorem firstNeutralCutoff_le (p : ReversalParity) (L : ℝ)
    (h : ∃ K, 3 ≤ K ∧ PoleNeutralParityNegative p L K) {K : ℕ}
    (hK : 3 ≤ K) (hneg : PoleNeutralParityNegative p L K) :
    firstNeutralCutoff p L h ≤ K := Nat.find_min' h ⟨hK, hneg⟩

theorem firstNeutralCutoff_predecessor_psd {L : ℝ} (hL : 0 < L)
    (p : ReversalParity) (h : ∃ K, 3 ≤ K ∧ PoleNeutralParityNegative p L K) :
    PoleNeutralParityPSD p L (firstNeutralCutoff p L h - 1) := by
  have hmin := (firstNeutralCutoff_spec p L h).1
  by_cases hthree : firstNeutralCutoff p L h = 3
  · simpa [hthree] using poleNeutralParityPSD_two hL p
  · rw [poleNeutralParityPSD_iff_not_negative]
    intro hneg
    have hle := firstNeutralCutoff_le p L h (by omega) hneg
    omega

def firstBothNeutralCutoff (L : ℝ)
    (he : ∃ K, 3 ≤ K ∧ EvenNeutralNegative L K)
    (ho : ∃ K, 3 ≤ K ∧ OddNeutralNegative L K) : ℕ :=
  max (firstNeutralCutoff .even L he) (firstNeutralCutoff .odd L ho)

theorem firstBothNeutralCutoff_least {L : ℝ} (hL : 0 < L)
    (he : ∃ K, 3 ≤ K ∧ EvenNeutralNegative L K)
    (ho : ∃ K, 3 ≤ K ∧ OddNeutralNegative L K) :
    3 ≤ firstBothNeutralCutoff L he ho ∧
    BothNeutralNegative L (firstBothNeutralCutoff L he ho) ∧
    ∀ K, 3 ≤ K → BothNeutralNegative L K → firstBothNeutralCutoff L he ho ≤ K := by
  obtain ⟨hKe, hne⟩ := firstNeutralCutoff_spec .even L he
  obtain ⟨hKo, hno⟩ := firstNeutralCutoff_spec .odd L ho
  refine ⟨le_trans hKe (le_max_left _ _), ⟨?_, ?_⟩, ?_⟩
  · exact poleNeutralParityNegative_mono hL .even (le_max_left _ _) hne
  · exact poleNeutralParityNegative_mono hL .odd (le_max_right _ _) hno
  · intro K hK hboth
    exact max_le (firstNeutralCutoff_le .even L he hK hboth.1)
      (firstNeutralCutoff_le .odd L ho hK hboth.2)

/-- Earlier arrival stays negative at the other parity's predecessor.
Thus the newborn predecessor conclusion cannot be imposed on both parities. -/
theorem earlier_parity_negative_at_other_predecessor {L : ℝ} (hL : 0 < L)
    (p q : ReversalParity)
    (hp : ∃ K, 3 ≤ K ∧ PoleNeutralParityNegative p L K)
    (hq : ∃ K, 3 ≤ K ∧ PoleNeutralParityNegative q L K)
    (hlt : firstNeutralCutoff p L hp < firstNeutralCutoff q L hq) :
    PoleNeutralParityNegative p L (firstNeutralCutoff q L hq - 1) :=
  poleNeutralParityNegative_mono hL p (by omega) (firstNeutralCutoff_spec p L hp).2

theorem even_predecessor_shell {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) :
    Module.finrank ℂ (@Submodule.orthogonal ℂ (poleNeutralEvenSubspace L K)
      inferInstance inferInstance (poleNeutralEven_innerProductSpace L K)
      (LinearMap.range (poleNeutralEvenCenteredZeroExtend L
        (show K - 1 ≤ K by omega)).toLinearMap)) = 1 := by
  cases K with
  | zero => omega
  | succ N =>
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
      (finrank_poleNeutralEven_successor_shell_eq_one hL N (by omega))

theorem odd_predecessor_shell {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) :
    Module.finrank ℂ (@Submodule.orthogonal ℂ (poleNeutralOddSubspace L K)
      inferInstance inferInstance (poleNeutralOdd_innerProductSpace L K)
      (LinearMap.range (poleNeutralOddCenteredZeroExtend L
        (show K - 1 ≤ K by omega)).toLinearMap)) = 1 := by
  cases K with
  | zero => omega
  | succ N =>
    simpa only [Nat.succ_eq_add_one, Nat.add_sub_cancel] using
      (finrank_poleNeutralOdd_successor_shell_eq_one hL N (by omega))

theorem firstNeutralCutoff_even_shell {L : ℝ} (hL : 0 < L)
    (h : ∃ K, 3 ≤ K ∧ EvenNeutralNegative L K) :
    Module.finrank ℂ (@Submodule.orthogonal ℂ
      (poleNeutralEvenSubspace L (firstNeutralCutoff .even L h))
      inferInstance inferInstance (poleNeutralEven_innerProductSpace L _)
      (LinearMap.range (poleNeutralEvenCenteredZeroExtend L
        (show firstNeutralCutoff .even L h - 1 ≤ firstNeutralCutoff .even L h by omega)).toLinearMap)) = 1 :=
  even_predecessor_shell hL _ (firstNeutralCutoff_spec .even L h).1

theorem firstNeutralCutoff_odd_shell {L : ℝ} (hL : 0 < L)
    (h : ∃ K, 3 ≤ K ∧ OddNeutralNegative L K) :
    Module.finrank ℂ (@Submodule.orthogonal ℂ
      (poleNeutralOddSubspace L (firstNeutralCutoff .odd L h))
      inferInstance inferInstance (poleNeutralOdd_innerProductSpace L _)
      (LinearMap.range (poleNeutralOddCenteredZeroExtend L
        (show firstNeutralCutoff .odd L h - 1 ≤ firstNeutralCutoff .odd L h by omega)).toLinearMap)) = 1 :=
  odd_predecessor_shell hL _ (firstNeutralCutoff_spec .odd L h).1

end Zeta23.OPICARound3

#print axioms Zeta23.OPICARound3.firstBothNeutralCutoff_least
#print axioms Zeta23.OPICARound3.firstNeutralCutoff_predecessor_psd
#print axioms Zeta23.OPICARound3.firstNeutralCutoff_even_shell
#print axioms Zeta23.OPICARound3.firstNeutralCutoff_odd_shell
