import Zeta23.Spectral.CharacteristicXiIdentification

namespace Zeta23.Spectral

theorem zero_transfer_of_identification
    {F G : ℂ → ℂ}
    (hFG : ComplexFunctionIdentification F G)
    {z : ℂ} (hz : F z = 0) :
    G z = 0 := by
  rw [← hFG z]
  exact hz

end Zeta23.Spectral

#print axioms Zeta23.Spectral.zero_transfer_of_identification
