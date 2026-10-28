import Zeta23.CCM.CanonicalPoleNeutralShiftedSecular

noncomputable section

namespace Zeta23.OPICARound4

open CCM Matrix
open scoped BigOperators ComplexConjugate

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- The corrected row includes the normal removed by the second projection.
Conjugated coefficients respect the convention that the first inner slot is antilinear. -/
def correctedSourceRow (L : ℝ) (K : ℕ) : EuclideanSpace ℂ (Fin (2 * K + 1)) :=
  star (1 / inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K)) •
      centeredQuadraticNormal K -
    star (canonicalPoleQuadraticNormalCoefficient L K /
      inner ℂ (canonicalPoleEvenLegalNormal L K) (canonicalPoleEvenLegalNormal L K)) •
      (canonicalPoleEvenLegalNormal L K : EuclideanSpace ℂ (Fin (2 * K + 1)))

theorem correctedSourceRow_pairing (L : ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    inner ℂ (correctedSourceRow L K) x =
      inner ℂ (centeredQuadraticNormal K) x /
          inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) -
      canonicalPoleQuadraticNormalCoefficient L K *
        (inner ℂ (canonicalPoleEvenLegalNormal L K : EuclideanSpace ℂ (Fin (2 * K + 1))) x /
          inner ℂ (canonicalPoleEvenLegalNormal L K) (canonicalPoleEvenLegalNormal L K)) := by
  simp only [correctedSourceRow, inner_sub_left, inner_smul_left, starRingEnd_apply, star_star]
  ring

theorem correctedSourceRow_orthogonal (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    inner ℂ (correctedSourceRow L K)
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
  rw [correctedSourceRow_pairing]
  have hq : inner ℂ (centeredQuadraticNormal K)
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 :=
    (Submodule.mem_orthogonal' _ _).mp
      (centeredQuadraticNormal_mem_evenBoundaryFlat_orthogonal K) _ u.val.property
  have hg : inner ℂ (canonicalPoleEvenLegalNormal L K) u.val = 0 := by
    rw [inner_canonicalPoleEvenLegalNormal]
    exact (mem_poleNeutralEvenSubspace L K u.val).mp u.property
  change _ - _ * (inner ℂ (canonicalPoleEvenLegalNormal L K) u.val / _) = 0
  rw [hq, hg]
  simp

/-- The complete corrected functional is paired with the *uncompressed* native
source action. It includes the removed output, not only the neutral compression. -/
theorem correctedSourceRow_native {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : poleNeutralEvenSubspace L K) :
    poleNeutralCorrectedCubicSource L K u =
      inner ℂ (correctedSourceRow L K)
        ((canonicalSourceMatrix L K).toEuclideanLin
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) := by
  rw [correctedSourceRow_pairing, poleNeutralCorrectedCubicSource]
  rw [cubicDefectFunctional_eq_evenQuadraticSourceMoment hL K hK]
  unfold evenQuadraticSourceMoment poleNeutralEvenOutputCoefficient
  congr 1
  congr 1
  congr 1
  change inner ℂ (canonicalPoleEvenLegalNormal L K)
    ((euclideanEvenBoundaryFlatSubspace K).orthogonalProjectionOnto
      ((canonicalSourceMatrix L K).toEuclideanLin
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))))) = _
  exact Submodule.inner_orthogonalProjectionOnto_eq_of_mem_left
    (𝕜 := ℂ) (E := EuclideanSpace ℂ (Fin (2 * K + 1)))
    (K := euclideanEvenBoundaryFlatSubspace K)
    (canonicalPoleEvenLegalNormal L K) _

/-- Exact pole cancellation precedes any source estimate. The full prime matrix
is retained; its existing definition includes every von-Mangoldt prime power. -/
theorem correctedSourceRow_pole_cancelled {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : poleNeutralEvenSubspace L K) :
    poleNeutralCorrectedCubicSource L K u =
      -inner ℂ (correctedSourceRow L K)
        ((canonicalArchMatrix L K).toEuclideanLin
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) -
      inner ℂ (correctedSourceRow L K)
        ((canonicalPrimeMatrix L K).toEuclideanLin
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) := by
  rw [correctedSourceRow_native hL K hK]
  have haction := canonicalSourceMatrix_mulVec_poleNeutralEven_eq_negative_arch_prime hL K u
  have hlin : (canonicalSourceMatrix L K).toEuclideanLin
      (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) =
      -((canonicalArchMatrix L K).toEuclideanLin
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) -
      (canonicalPrimeMatrix L K).toEuclideanLin
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
    apply (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).injective
    exact haction
  rw [hlin, inner_sub_right, inner_neg_right]

/-- The row's orthogonality explains precisely why common scalar shifts are
invisible to this functional. The source itself is still the canonical one. -/
theorem correctedSourceRow_scalar_shift {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : poleNeutralEvenSubspace L K) (c : ℂ) :
    inner ℂ (correctedSourceRow L K)
      (((canonicalSourceMatrix L K).toEuclideanLin - c •
        (LinearMap.id : EuclideanSpace ℂ (Fin (2 * K + 1)) →ₗ[ℂ]
          EuclideanSpace ℂ (Fin (2 * K + 1))))
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) =
      poleNeutralCorrectedCubicSource L K u := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    inner_sub_right, inner_smul_right, correctedSourceRow_orthogonal, mul_zero, sub_zero]
  exact (correctedSourceRow_native hL K hK u).symm

end Zeta23.OPICARound4
