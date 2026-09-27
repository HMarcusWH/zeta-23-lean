import Zeta23.Spectral.CanonicalCharacteristic

noncomputable section

namespace Zeta23.Spectral

def canonicalCharacteristicNormalizer (L : ℝ) (K : ℕ) : ℂ :=
  canonicalCharacteristic L K 0

def normalizedCanonicalCharacteristic (L : ℝ) (K : ℕ) (z : ℂ) : ℂ :=
  canonicalCharacteristic L K z / canonicalCharacteristicNormalizer L K

@[simp] theorem normalizedCanonicalCharacteristic_zero
    (L : ℝ) (K : ℕ)
    (h : canonicalCharacteristicNormalizer L K ≠ 0) :
    normalizedCanonicalCharacteristic L K 0 = 1 := by
  have h' : canonicalCharacteristic L K 0 ≠ 0 := by
    simpa [canonicalCharacteristicNormalizer] using h
  simpa [normalizedCanonicalCharacteristic, canonicalCharacteristicNormalizer]
    using (div_self (canonicalCharacteristic L K 0) h')

end Zeta23.Spectral

#print axioms Zeta23.Spectral.normalizedCanonicalCharacteristic_zero
