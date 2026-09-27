import Zeta23.CCM.CanonicalSourceEnergy

noncomputable section

namespace Zeta23.CCM

/-! # Closure campaign C1: exact full-space operator/energy bridge -/

def canonicalFullSpaceOperator (L : ℝ) (K : ℕ) :=
  (canonicalSourceMatrix L K).toEuclideanLin

theorem canonicalFullSpaceOperator_energy
    (L : ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalSourceMatrix L K) x =
      Complex.re (inner ℂ (canonicalFullSpaceOperator L K x) x) := by
  simpa [canonicalFullSpaceOperator] using
    matrixRealEnergy_eq_re_inner_apply_self
      (canonicalSourceMatrix L K) x

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalFullSpaceOperator_energy
