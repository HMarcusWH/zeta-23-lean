import Zeta23.CCM.SourceContraction
import Zeta23.CCM.LocalizedFiniteSpace

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A1: source contraction through the localized autocorrelation

This module pushes the remaining source-contraction analysis onto the actual
zero-extended finite Fourier function already constructed in the repository.
The remaining open inequality is now a standard L2 autocorrelation bound rather
than a matrix-entry estimate.
-/

/-- The elementary source contraction is exactly the unit-aperture localized
finite autocorrelation at complementary shift. -/
theorem sourceContract_eq_localizedWeilCorrelation_unit
    (K : ℕ) (u : Fin (2 * K + 1) → ℂ)
    (ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) :
    sourceContract K u ω =
      localizedWeilCorrelation
        (localizedFiniteVector 1 K u)
        (localizedFiniteVector 1 K u) (1 - ω) := by
  have hy0 : 0 ≤ 1 - ω := sub_nonneg.mpr hω1
  have hy1 : 1 - ω ≤ (1 : ℝ) := by linarith
  have hcorr :=
    localizedWeilCorrelation_finiteVector_eq_two_mul_dictionaryTest_of_nonneg
      K u (L := (1 : ℝ)) (y := 1 - ω) (by norm_num) hy0 hy1
  have habs : |1 - ω| ≤ (1 : ℝ) := by
    rw [abs_of_nonneg hy0]
    exact hy1
  have hdict :
      dictionaryTest K u 1 (1 - ω) =
        (1 / 2 : ℂ) * sourceContract K u ω := by
    unfold dictionaryTest dictionaryKernel
    rw [if_pos habs, abs_of_nonneg hy0]
    congr 2
    ring
  rw [hdict] at hcorr
  have htwo : (2 : ℂ) * ((1 / 2 : ℂ) * sourceContract K u ω) =
      sourceContract K u ω := by ring
  rw [htwo] at hcorr
  exact hcorr.symm

/-- Exact matrix-energy form of the same bridge. -/
theorem matrixRealEnergy_sourceMatrix_eq_localizedWeilCorrelation_re
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) (hω0 : 0 ≤ ω) (hω1 : ω ≤ 1) :
    matrixRealEnergy (sourceMatrix ω K) x =
      Complex.re
        (localizedWeilCorrelation
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          (1 - ω)) := by
  change
    Complex.re
      (sourceContract K
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ω) =
      Complex.re
        (localizedWeilCorrelation
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          (1 - ω))
  rw [sourceContract_eq_localizedWeilCorrelation_unit
    K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ω hω0 hω1]

/-- Standard L2 statement still required analytically: the symmetrized
autocorrelation of the normalized finite Fourier vector is bounded by twice
its Euclidean coefficient mass. -/
def LocalizedFiniteAutocorrelationBound : Prop :=
  ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
    ∀ y : ℝ, 0 ≤ y → y ≤ 1 →
      |Complex.re
        (localizedWeilCorrelation
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          (localizedFiniteVector 1 K
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
          y)| ≤ 2 * ‖x‖ ^ 2

/-- The localized autocorrelation inequality immediately supplies the complete
source-contraction theorem, including both endpoints. -/
theorem sourceContractionBound_of_localizedAutocorrelation
    (h : LocalizedFiniteAutocorrelationBound) :
    SourceContractionBound := by
  intro K ω hω0 hω1 x
  rw [matrixRealEnergy_sourceMatrix_eq_localizedWeilCorrelation_re
    K x ω hω0 hω1]
  exact h K x (1 - ω) (sub_nonneg.mpr hω1) (by linarith)

end Zeta23.CCM

#print axioms Zeta23.CCM.sourceContract_eq_localizedWeilCorrelation_unit
#print axioms Zeta23.CCM.matrixRealEnergy_sourceMatrix_eq_localizedWeilCorrelation_re
#print axioms Zeta23.CCM.sourceContractionBound_of_localizedAutocorrelation
