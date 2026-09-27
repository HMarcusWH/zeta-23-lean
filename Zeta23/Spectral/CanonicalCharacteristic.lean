import Zeta23.Spectral.CanonicalOperator

noncomputable section

namespace Zeta23.Spectral

open Matrix
open Zeta23.CCM

def canonicalCharacteristic (L : ℝ) (K : ℕ) (z : ℂ) : ℂ :=
  Matrix.det
    (canonicalSourceMatrix L K -
      z • (1 : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ))

@[simp] theorem canonicalCharacteristic_zero (L : ℝ) (K : ℕ) :
    canonicalCharacteristic L K 0 =
      Matrix.det (canonicalSourceMatrix L K) := by
  simp [canonicalCharacteristic]

end Zeta23.Spectral

#print axioms Zeta23.Spectral.canonicalCharacteristic_zero
