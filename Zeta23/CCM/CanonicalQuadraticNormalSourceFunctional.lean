import Zeta23.CCM.DictionaryMixedPairing
import Zeta23.CCM.QuadraticNormalSourceJets
import Zeta23.CCM.SourceNormalizationRepair

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: complete quadratic-normal source functional

PR #209 constrains the pairing between the exact production source moment and
the seventh jet of `quadraticNormalSourceAtom`.  This module identifies the
production source moment with one complete explicit-formula functional of that
same source observable.

The functional is deliberately defined through the theorem-authoritative
`Zeta23.EF.literatureRHS`; no pole/archimedean/prime normalization is retyped.
The physical lift uses the already theorem-locked clamped dictionary source
coordinate.
-/

/-- The quadratic-normal observable annihilates the identity matrix. -/
@[simp] theorem quadraticNormalMatrixMoment_one_eq_zero
    (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixMoment K
        (1 : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ) v = 0 := by
  unfold quadraticNormalMatrixMoment
  rw [quadraticNormalMatrixNumerator_one_eq_zero]
  simp

/-- The active source observable vanishes at source coordinate zero. -/
@[simp] theorem quadraticNormalSourceAtom_zero
    (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalSourceAtom K v 0 = 0 := by
  unfold quadraticNormalSourceAtom
  rw [sourceMatrix_zero]
  exact quadraticNormalMatrixMoment_zero K v

/-- The active source observable also vanishes at source coordinate one:
`sourceMatrix 1 = 2I`, and the quadratic normal kills scalar identity action. -/
@[simp] theorem quadraticNormalSourceAtom_one
    (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalSourceAtom K v 1 = 0 := by
  unfold quadraticNormalSourceAtom
  rw [sourceMatrix_one, quadraticNormalMatrixMoment_smul,
    quadraticNormalMatrixMoment_one_eq_zero]
  ring

/-- Physical-space lift of a source-coordinate observable through the exact
clamped dictionary aperture coordinate. -/
def canonicalSourcePhysicalLift
    (L : ℝ) (h : ℝ → ℂ) : ℝ → ℂ :=
  fun t => h (dictionaryApertureCoord L t)

/-- Complete canonical functional.  The factor `1/2` compensates for the
production basis normalization `dictionaryBasisTest = (1/2) * sourceEntry`. -/
def canonicalQuadraticNormalSourceFunctional
    (L : ℝ) (h : ℝ → ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    Zeta23.EF.literatureRHS (canonicalSourcePhysicalLift L h)

/-- Half of the mixed coefficient pairing with the quadratic normal and the
`2/<n2,n2>`-scaled carrier is exactly the normalized quadratic-normal matrix
moment. -/
theorem half_matrixCoefficientPairing_quadraticNormal_scaled_eq_moment
    (K : ℕ) (hK : 1 ≤ K)
    (M : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    (1 / 2 : ℂ) *
        matrixCoefficientPairing M
          (fun i => centeredQuadraticNormal K i)
          (fun j =>
            (2 / inner ℂ (centeredQuadraticNormal K)
                    (centeredQuadraticNormal K)) *
              evenBoundaryFlatRawCoefficients K v j) =
      quadraticNormalMatrixMoment K M v := by
  have hden :
      inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) ≠ 0 :=
    inner_centeredQuadraticNormal_self_ne_zero K hK
  unfold matrixCoefficientPairing quadraticNormalMatrixMoment
    quadraticNormalMatrixNumerator
  unfold Matrix.mulVec dotProduct
  field_simp [hden]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The physical lift of the active source observable is exactly the mixed
finite dictionary built from the quadratic normal and the scaled carrier. -/
theorem canonicalSourcePhysicalLift_quadraticNormalSourceAtom_eq_mixedTest
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    canonicalSourcePhysicalLift L (quadraticNormalSourceAtom K v) =
      dictionaryMixedTest K
        (fun i => centeredQuadraticNormal K i)
        (fun j =>
          (2 / inner ℂ (centeredQuadraticNormal K)
                  (centeredQuadraticNormal K)) *
            evenBoundaryFlatRawCoefficients K v j)
        L := by
  have hden :
      inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) ≠ 0 :=
    inner_centeredQuadraticNormal_self_ne_zero K hK
  funext t
  unfold canonicalSourcePhysicalLift quadraticNormalSourceAtom
    quadraticNormalMatrixMoment quadraticNormalMatrixNumerator
    dictionaryMixedTest
  simp_rw [dictionaryBasisTest_eq_sourceEntry_clamped hL]
  unfold Matrix.mulVec dotProduct
  simp_rw [sourceMatrix_apply]
  field_simp [hden]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The complete functional evaluated on the active source atom is exactly the
quadratic-normal moment of the deterministic dictionary matrix. -/
theorem canonicalQuadraticNormalSourceFunctional_eq_dictionaryMoment
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    canonicalQuadraticNormalSourceFunctional L
        (quadraticNormalSourceAtom K v) =
      quadraticNormalMatrixMoment K (dictionaryMatrix L K) v := by
  unfold canonicalQuadraticNormalSourceFunctional
  rw [canonicalSourcePhysicalLift_quadraticNormalSourceAtom_eq_mixedTest
    hL K hK v]
  rw [literatureRHS_dictionaryMixedTest_eq_matrixCoefficientPairing
    K
    (fun i => centeredQuadraticNormal K i)
    (fun j =>
      (2 / inner ℂ (centeredQuadraticNormal K)
              (centeredQuadraticNormal K)) *
        evenBoundaryFlatRawCoefficients K v j)
    hL]
  exact half_matrixCoefficientPairing_quadraticNormal_scaled_eq_moment
    K hK (dictionaryMatrix L K) v

/-- Headline complete-functional representation: the exact production source
moment is one literature explicit-formula functional of the same elementary
source observable whose seventh jet is used by Pair D. -/
theorem explicitCanonicalSourceMoment_eq_completeSourceFunctional
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    explicitCanonicalSourceMoment L K v =
      canonicalQuadraticNormalSourceFunctional L
        (quadraticNormalSourceAtom K v) := by
  calc
    explicitCanonicalSourceMoment L K v =
        evenQuadraticSourceMoment L K v :=
      (evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment hL K v).symm
    _ = quadraticNormalMatrixMoment K (canonicalSourceMatrix L K) v :=
      evenQuadraticSourceMoment_eq_quadraticNormalMatrixMoment L K v
    _ = quadraticNormalMatrixMoment K (dictionaryMatrix L K) v := by
      rw [canonicalSourceMatrix_eq_dictionaryMatrix]
    _ = canonicalQuadraticNormalSourceFunctional L
          (quadraticNormalSourceAtom K v) :=
      (canonicalQuadraticNormalSourceFunctional_eq_dictionaryMoment
        hL K hK v).symm

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalSourcePhysicalLift_quadraticNormalSourceAtom_eq_mixedTest
#print axioms Zeta23.CCM.canonicalQuadraticNormalSourceFunctional_eq_dictionaryMoment
#print axioms Zeta23.CCM.explicitCanonicalSourceMoment_eq_completeSourceFunctional
