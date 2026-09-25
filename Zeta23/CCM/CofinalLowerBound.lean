import Zeta23.CCM.GlobalParityBottomNFlow

noncomputable section

namespace Zeta23.CCM

/-!
# Jointly cofinal vanishing lower certificates

These are conditional order lemmas. The joint quantifier is essential:
a large size and a small error must be available in the SAME certificate.
No finite list, graph edge, or decreasing quadrature error supplies this premise.
-/

/-- An antitone family cannot retain a negative value if arbitrarily large
indices have arbitrarily small negative error bounds, jointly. -/
theorem nonneg_of_antitone_jointCofinal_lowerBound
    (f : ℕ → ℝ)
    (hanti : ∀ {n m : ℕ}, 1 ≤ n → n ≤ m → f m ≤ f n)
    (hcert : ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε →
      ∃ m : ℕ, n ≤ m ∧ -ε ≤ f m) :
    ∀ n : ℕ, 1 ≤ n → 0 ≤ f n := by
  intro n hn
  by_contra h
  have hneg : f n < 0 := lt_of_not_ge h
  obtain ⟨m, hnm, hm⟩ := hcert n hn (-f n / 2) (by linarith)
  have ha := hanti hn hnm
  linarith

/-- A named exact certificate condition at one positive aperture. This is a
proposition, not a supplied certificate and not a positivity assertion. -/
def JointCofinalBottomLowerBounds (L : ℝ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ε : ℝ, 0 < ε →
    ∃ m : ℕ, n ≤ m ∧ -ε ≤ globalParitySuccessorBottom L m

/-- A single joint cofinal family would rule out every finite negative bottom
at this aperture. -/
theorem globalParitySuccessorBottom_nonneg_of_jointCofinal_lowerBounds
    {L : ℝ} (hL : 0 < L) (hcert : JointCofinalBottomLowerBounds L) :
    ∀ n : ℕ, 1 ≤ n → 0 ≤ globalParitySuccessorBottom L n := by
  apply nonneg_of_antitone_jointCofinal_lowerBound
    (globalParitySuccessorBottom L)
  · intro n m hn hnm
    exact globalParitySuccessorBottom_antitone_of_le hL hn hnm
  · exact hcert

end Zeta23.CCM

#print axioms Zeta23.CCM.nonneg_of_antitone_jointCofinal_lowerBound
#print axioms Zeta23.CCM.globalParitySuccessorBottom_nonneg_of_jointCofinal_lowerBounds
