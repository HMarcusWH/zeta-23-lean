import Zeta23.Spectral.CharacteristicCompactBounds

namespace Zeta23.Spectral

/-!
# Closure campaign C2: complex limit identification contract

The hard step is identification of the complex compact limit with the intended
Xi normalization. No equality with Xi is asserted here.
-/

def ComplexFunctionIdentification (F G : ℂ → ℂ) : Prop :=
  ∀ z : ℂ, F z = G z

theorem ComplexFunctionIdentification.trans
    {F G H : ℂ → ℂ}
    (hFG : ComplexFunctionIdentification F G)
    (hGH : ComplexFunctionIdentification G H) :
    ComplexFunctionIdentification F H := by
  intro z
  exact (hFG z).trans (hGH z)

def CanonicalCharacteristicXiIdentification : Prop := False

end Zeta23.Spectral

#print axioms Zeta23.Spectral.ComplexFunctionIdentification.trans
