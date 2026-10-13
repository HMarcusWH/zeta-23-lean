import Zeta23.CCM.FiniteBottomGapSelector
import Zeta23.CCM.CanonicalPoleNeutralBottomNFlow

noncomputable section

namespace Zeta23.CCM

/-!
The exact bottom-only avoidance part of the native deep threshold selector.

Only the actual native global bottoms at cutoffs 3 through Kd are avoided.
There are Kd-2 such values, so the midpoint grid supplies the original gap
D/[12(Kd-1)]. No all-eigenvalue separator or fabricated ground at -eta is
used. The actual detector-depth bridge, least crossing, selected ground,
predecessor coercivity and the two distinct Schur inverse budgets remain
separate producer obligations beyond this finite avoidance theorem.
-/

def nativeDeepThresholdGap (D : ℝ) (Kd : ℕ) : ℝ :=
  D / (12 * ((Kd - 1 : ℕ) : ℝ))

theorem nativeDeepThresholdGap_pos (D : ℝ) (Kd : ℕ) (hD : 0 < D) (hKd : 3 ≤ Kd) :
    0 < nativeDeepThresholdGap D Kd := by
  have hcutoff : (0 : ℝ) < ((Kd - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < Kd - 1 by omega)
  unfold nativeDeepThresholdGap
  positivity

/-- Actual native bottom avoidance with the original D/3, D/2 and gap12. -/
theorem exists_nativeDeepThreshold_bottom_separator {L : ℝ} (hL : 0 < L)
    (Kd : ℕ) (hKd : 3 ≤ Kd) (D : ℝ) (hD : 0 < D) :
    ∃ eta : ℝ, D / 3 < eta ∧ eta < D / 2 ∧
      ∀ K : ℕ, (hK : 3 ≤ K) → K ≤ Kd →
        nativeDeepThresholdGap D Kd ≤ |poleNeutralGlobalRayleighBottom L K hL hK + eta| := by
  let x : Fin (Kd - 2) → ℝ := fun i =>
    -poleNeutralGlobalRayleighBottom L (i.val + 3) hL (by omega)
  have hab : D / 3 < D / 2 := by linarith
  obtain ⟨eta, hlo, hhi, hsep⟩ := exists_finite_real_gap_selector (Kd - 2) (D / 3) (D / 2) hab x
  have hcount : (((Kd - 2 : ℕ) : ℝ) + 1) = ((Kd - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show Kd - 2 + 1 = Kd - 1 by omega)
  have hden : (((Kd - 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show Kd - 1 ≠ 0 by omega)
  have hgap : (D / 2 - D / 3) / (2 * (((Kd - 2 : ℕ) : ℝ) + 1)) =
      nativeDeepThresholdGap D Kd := by
    rw [hcount]
    unfold nativeDeepThresholdGap
    field_simp [hden] <;> ring
  refine ⟨eta, hlo, hhi, ?_⟩
  intro K hK hKKd
  let i : Fin (Kd - 2) := ⟨K - 3, by omega⟩
  have hi : i.val + 3 = K := by dsimp [i]; omega
  have hs := hsep i
  rw [hgap] at hs
  dsimp only [x] at hs
  rw [hi] at hs
  simpa only [sub_neg_eq_add, add_comm] using hs

/-- A genuine crossing and the constructed gap retain depth at the actual
bottom; they do not identify the actual eigenvalue with -eta. -/
theorem nativeDeepThreshold_crossing_retains_gap {L : ℝ} (hL : 0 < L)
    (K Kd : ℕ) (hK : 3 ≤ K) (D eta : ℝ)
    (hcross : poleNeutralGlobalRayleighBottom L K hL hK < -eta)
    (hgap : nativeDeepThresholdGap D Kd ≤ |poleNeutralGlobalRayleighBottom L K hL hK + eta|) :
    poleNeutralGlobalRayleighBottom L K hL hK ≤ -eta - nativeDeepThresholdGap D Kd := by
  have hn : poleNeutralGlobalRayleighBottom L K hL hK + eta < 0 := by linarith
  rw [abs_of_neg hn] at hgap
  linarith

/-- An actual noncrossing cutoff separated from -eta lies on the positive
side of the full gap. This is a conditional interface for the least selector. -/
theorem nativeDeepThreshold_noncrossing_has_lower_gap {L : ℝ} (hL : 0 < L)
    (K Kd : ℕ) (hK : 3 ≤ K) (D eta : ℝ)
    (hnocross : -eta ≤ poleNeutralGlobalRayleighBottom L K hL hK)
    (hgap : nativeDeepThresholdGap D Kd ≤ |poleNeutralGlobalRayleighBottom L K hL hK + eta|) :
    -eta + nativeDeepThresholdGap D Kd ≤ poleNeutralGlobalRayleighBottom L K hL hK := by
  have hn : 0 ≤ poleNeutralGlobalRayleighBottom L K hL hK + eta := by linarith
  rw [abs_of_nonneg hn] at hgap
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeDeepThresholdGap_pos
#print axioms Zeta23.CCM.exists_nativeDeepThreshold_bottom_separator
#print axioms Zeta23.CCM.nativeDeepThreshold_crossing_retains_gap
#print axioms Zeta23.CCM.nativeDeepThreshold_noncrossing_has_lower_gap
