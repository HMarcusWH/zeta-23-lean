import Zeta23.CCM.CanonicalFullSpaceSourceBridge

noncomputable section

namespace Zeta23.Spectral

open Zeta23.CCM

def canonicalFiniteOperator (L : ℝ) (K : ℕ) :=
  canonicalFullSpaceOperator L K

theorem canonicalFiniteOperator_energy
    (L : ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalSourceMatrix L K) x =
      Complex.re (inner ℂ (canonicalFiniteOperator L K x) x) := by
  simpa [canonicalFiniteOperator] using
    canonicalFullSpaceOperator_energy L K x

end Zeta23.Spectral

#print axioms Zeta23.Spectral.canonicalFiniteOperator_energy
