import Zeta23.Spectral.CharacteristicNormalization

namespace Zeta23.Spectral

def CharacteristicCompactBound
    (F : ℂ → ℂ) (R M : ℝ) : Prop :=
  ∀ z : ℂ, ‖z‖ ≤ R → ‖F z‖ ≤ M

theorem CharacteristicCompactBound.mono
    {F : ℂ → ℂ} {R M M' : ℝ}
    (h : CharacteristicCompactBound F R M)
    (hMM' : M ≤ M') :
    CharacteristicCompactBound F R M' := by
  intro z hz
  exact le_trans (h z hz) hMM'

end Zeta23.Spectral

#print axioms Zeta23.Spectral.CharacteristicCompactBound.mono
