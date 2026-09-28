import Zeta23.Spectral.CharacteristicCompactBounds

namespace Zeta23.Spectral

/-!
# Closure campaign C2: complex limit identification interface

The hard theorem identifying a compact complex limit with Xi is still OPEN and
therefore has no placeholder declaration here.
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

end Zeta23.Spectral

#print axioms Zeta23.Spectral.ComplexFunctionIdentification.trans
