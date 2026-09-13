import Zeta23.CCM.MixedSourceDerivativeTransport
import Zeta23.CCM.QuadraticNormalMatrixMoment
import Zeta23.CCM.SourceMomentDecomposition
import Zeta23.CCM.CanonicalRieszBoundary

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB04C: quadratic-normal mixed source jets

This module specializes the mixed source transport to the exact quadratic
normal `centeredQuadraticNormal`.  The observable is not a new normalization:
it is definitionally the existing `quadraticNormalMatrixMoment` evaluated on
one elementary `sourceMatrix`.

The main result identifies its seventh source-coordinate jet with the fourth
centered moment of an even boundary-flat carrier.  The same observable is then
exposed in the exact prime-source sum and in the order-eight Riesz boundary.
No implication between the global explicit source moment and `M4`, no endpoint
scalar sign, no branch exclusion, and no RH claim is asserted.
-/

/-- Exact elementary quadratic-normal source observable. -/
def quadraticNormalSourceAtom
    (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (ω : ℝ) : ℂ :=
  quadraticNormalMatrixMoment K (sourceMatrix ω K) v

/-- The elementary quadratic-normal observable is the normalized mixed pairing
with the canonical quadratic normal. -/
theorem quadraticNormalSourceAtom_eq_sourceAtomPairing_div
    (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (ω : ℝ) :
    quadraticNormalSourceAtom K v ω =
      sourceAtomPairing K (centeredQuadraticNormal K)
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) ω /
        inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) := by
  unfold quadraticNormalSourceAtom quadraticNormalMatrixMoment
  congr 1
  unfold quadraticNormalMatrixNumerator sourceAtomPairing
    evenBoundaryFlatRawCoefficients
  unfold Matrix.mulVec dotProduct
  simp_rw [sourceMatrix_apply, sourceEntry_eq_ofReal]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Complex.real_smul]
  ring

/-- Raw coordinates of an even boundary-flat vector satisfy the exact three
boundary-flat moment constraints. -/
theorem evenBoundaryFlatRawCoefficients_boundaryFlat
    (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    BoundaryFlatCoefficients K (evenBoundaryFlatRawCoefficients K v) := by
  have hv :=
    ((mem_euclideanEvenBoundaryFlatSubspace_iff K
      (v : EuclideanSpace ℂ (Fin (2 * K + 1)))).mp v.property).1
  exact (mem_boundaryFlatSubspace_iff K _).mp hv

/-- Raw coordinates of an even boundary-flat vector lie in the even reversal
sector. -/
theorem evenBoundaryFlatRawCoefficients_mem_even
    (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    evenBoundaryFlatRawCoefficients K v ∈ evenCoefficientSubspace K := by
  have hv :=
    ((mem_euclideanEvenBoundaryFlatSubspace_iff K
      (v : EuclideanSpace ℂ (Fin (2 * K + 1)))).mp v.property).2
  simpa [evenBoundaryFlatRawCoefficients] using hv

/-- The quadratic normal has zero constant centered moment. -/
theorem centeredQuadraticNormal_moment_zero_eq_zero
    (K : ℕ) :
    centeredMoment K 0
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (centeredQuadraticNormal K)) = 0 := by
  calc
    centeredMoment K 0
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (centeredQuadraticNormal K)) =
      inner ℂ (centeredPowerVector K 0) (centeredQuadraticNormal K) :=
        (inner_centeredPowerVector K 0 (centeredQuadraticNormal K)).symm
    _ = 0 :=
      inner_centeredPowerVector_zero_centeredQuadraticNormal_eq_zero K

/-- The quadratic normal is itself even. -/
theorem centeredQuadraticNormal_coordinates_mem_even
    (K : ℕ) :
    ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
      (centeredQuadraticNormal K)) ∈ evenCoefficientSubspace K := by
  have hmem : centeredQuadraticNormal K ∈ euclideanEvenCoefficientSubspace K :=
    evenNormalSubspace_le_evenCoefficient K
      (centeredQuadraticNormal_mem_evenNormalSubspace K)
  exact (mem_euclideanEvenCoefficientSubspace_iff K
    (centeredQuadraticNormal K)).mp hmem

/-- Hence the first centered moment of the quadratic normal vanishes. -/
theorem centeredQuadraticNormal_moment_one_eq_zero
    (K : ℕ) :
    centeredMoment K 1
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (centeredQuadraticNormal K)) = 0 := by
  exact centeredMoment_odd_eq_zero_of_even
    (centeredQuadraticNormal_coordinates_mem_even K) (by decide)

/-- The third centered moment of the quadratic normal also vanishes. -/
theorem centeredQuadraticNormal_moment_three_eq_zero
    (K : ℕ) :
    centeredMoment K 3
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (centeredQuadraticNormal K)) = 0 := by
  exact centeredMoment_odd_eq_zero_of_even
    (centeredQuadraticNormal_coordinates_mem_even K) (by decide)

/-- The conjugated second moment of the quadratic normal is exactly its
self-inner-product normalization. -/
theorem star_centeredQuadraticNormal_moment_two_eq_inner_self
    (K : ℕ) :
    star
        (centeredMoment K 2
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
            (centeredQuadraticNormal K))) =
      inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) := by
  calc
    star
        (centeredMoment K 2
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
            (centeredQuadraticNormal K))) =
      star (inner ℂ (centeredPowerVector K 2) (centeredQuadraticNormal K)) := by
        rw [inner_centeredPowerVector]
    _ = inner ℂ (centeredQuadraticNormal K) (centeredPowerVector K 2) := by
        exact inner_conj_symm (centeredQuadraticNormal K) (centeredPowerVector K 2)
    _ = inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) :=
      inner_centeredQuadraticNormal_centeredPowerVector_two_eq_self K

private theorem sourcePairingCoefficientSum_eq_moment_zero
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourcePairingCoefficientSum K x =
      centeredMoment K 0
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) := by
  unfold sourcePairingCoefficientSum
  rw [centeredMoment_zero_eq_sum]

private theorem sourcePairingCoefficientSum_indexAction_eq_moment_one
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourcePairingCoefficientSum K (sourceIndexAction K x) =
      centeredMoment K 1
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) := by
  rw [sourcePairingCoefficientSum_eq_moment_zero,
    centeredMoment_sourceIndexAction]

private theorem sourcePairingCoefficientSum_indexAction_sq_eq_moment_two
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    sourcePairingCoefficientSum K
        (sourceIndexAction K (sourceIndexAction K x)) =
      centeredMoment K 2
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) := by
  rw [sourcePairingCoefficientSum_eq_moment_zero,
    centeredMoment_sourceIndexAction,
    centeredMoment_sourceIndexAction]

private theorem centeredMoment_one_indexAction_sq_eq_moment_three
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    centeredMoment K 1
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (sourceIndexAction K (sourceIndexAction K x))) =
      centeredMoment K 3
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) := by
  rw [centeredMoment_sourceIndexAction, centeredMoment_sourceIndexAction]

private theorem centeredMoment_two_indexAction_sq_eq_moment_four
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    centeredMoment K 2
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (sourceIndexAction K (sourceIndexAction K x))) =
      centeredMoment K 4
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) := by
  rw [centeredMoment_sourceIndexAction, centeredMoment_sourceIndexAction]

/-- Unnormalized headline calculation: the seventh mixed source jet against
`n2` is its normalization times the fourth centered moment of the carrier. -/
theorem iteratedDeriv_seven_sourceAtomPairing_quadraticNormal_eq_moment_four
    (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    iteratedDeriv 7
        (sourceAtomPairing K (centeredQuadraticNormal K)
          (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) 0 =
      ((-2 * (2 * Real.pi) ^ 6 : ℝ) : ℂ) *
        inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) *
        centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) := by
  let n2 := centeredQuadraticNormal K
  let y : EuclideanSpace ℂ (Fin (2 * K + 1)) := v
  let Dn2 := sourceIndexAction K n2
  let Dy := sourceIndexAction K y
  let D2n2 := sourceIndexAction K Dn2
  let D2y := sourceIndexAction K Dy
  have hflat := evenBoundaryFlatRawCoefficients_boundaryFlat K v
  have hn20 : sourcePairingCoefficientSum K n2 = 0 := by
    rw [sourcePairingCoefficientSum_eq_moment_zero]
    simpa [n2] using centeredQuadraticNormal_moment_zero_eq_zero K
  have hy0 : sourcePairingCoefficientSum K y = 0 := by
    rw [sourcePairingCoefficientSum_eq_moment_zero]
    simpa [y, evenBoundaryFlatRawCoefficients] using hflat.1
  have hDn20 : sourcePairingCoefficientSum K Dn2 = 0 := by
    rw [sourcePairingCoefficientSum_indexAction_eq_moment_one]
    simpa [Dn2, n2] using centeredQuadraticNormal_moment_one_eq_zero K
  have hDy0 : sourcePairingCoefficientSum K Dy = 0 := by
    rw [sourcePairingCoefficientSum_indexAction_eq_moment_one]
    simpa [Dy, y, evenBoundaryFlatRawCoefficients] using hflat.2.1
  have hD2y0 : sourcePairingCoefficientSum K D2y = 0 := by
    rw [sourcePairingCoefficientSum_indexAction_sq_eq_moment_two]
    simpa [D2y, Dy, y, evenBoundaryFlatRawCoefficients] using hflat.2.2
  have hstep1 :=
    iteratedDeriv_add_two_sourceAtomPairing_eq_indexActions
      K n2 y 5 0 hn20 hy0
  have hstep2 :=
    iteratedDeriv_add_two_sourceAtomPairing_eq_indexActions
      K Dn2 Dy 3 0 hDn20 hDy0
  have hthird :=
    iteratedDeriv_three_sourceAtomPairing_eq_moments_of_right_sum_zero
      K D2n2 D2y hD2y0
  have hD2n2m1 :
      centeredMoment K 1
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) D2n2) = 0 := by
    rw [centeredMoment_one_indexAction_sq_eq_moment_three]
    simpa [D2n2, Dn2, n2] using centeredQuadraticNormal_moment_three_eq_zero K
  have hD2n2m0 :
      star
          (centeredMoment K 0
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) D2n2)) =
        inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) := by
    rw [centeredMoment_sourceIndexAction, centeredMoment_sourceIndexAction]
    simpa [D2n2, Dn2, n2] using
      star_centeredQuadraticNormal_moment_two_eq_inner_self K
  have hD2ym2 :
      centeredMoment K 2
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) D2y) =
        centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) := by
    rw [centeredMoment_two_indexAction_sq_eq_moment_four]
    rfl
  calc
    iteratedDeriv 7
        (sourceAtomPairing K (centeredQuadraticNormal K)
          (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) 0 =
      (-(2 * Real.pi) ^ 2 : ℝ) •
        iteratedDeriv 5 (sourceAtomPairing K Dn2 Dy) 0 := by
          simpa [n2, y, Dn2, Dy] using hstep1
    _ = (-(2 * Real.pi) ^ 2 : ℝ) •
        ((-(2 * Real.pi) ^ 2 : ℝ) •
          iteratedDeriv 3 (sourceAtomPairing K D2n2 D2y) 0) := by
          rw [hstep2]
    _ = _ := by
          rw [hthird, hD2n2m1, hD2n2m0, hD2ym2]
          simp only [star_zero, zero_mul, zero_add, Complex.real_smul]
          push_cast
          ring

/-- Headline FB-04C mixed-jet theorem. -/
theorem iteratedDeriv_seven_quadraticNormalSourceAtom_eq_moment_four
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    iteratedDeriv 7 (quadraticNormalSourceAtom K v) 0 =
      ((-2 * (2 * Real.pi) ^ 6 : ℝ) : ℂ) *
        centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) := by
  let den := inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K)
  have hden : den ≠ 0 := by
    simpa [den] using inner_centeredQuadraticNormal_self_ne_zero K hK
  have hfun : quadraticNormalSourceAtom K v =
      fun ω => den⁻¹ *
        sourceAtomPairing K (centeredQuadraticNormal K)
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) ω := by
    funext ω
    rw [quadraticNormalSourceAtom_eq_sourceAtomPairing_div]
    simp only [div_eq_inv_mul, den]
  rw [hfun, iteratedDeriv_const_mul_field]
  rw [iteratedDeriv_seven_sourceAtomPairing_quadraticNormal_eq_moment_four]
  field_simp [hden]
  ring

/-- The exact production source moment samples the same mixed source function at
the finite prime-source coordinates.  Pole and archimedean terms are unchanged. -/
theorem explicitCanonicalSourceMoment_eq_quadraticNormalSourceAtom_sum
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    explicitCanonicalSourceMoment L K v =
      (poleProfileScale L *
          (poleEvenProfile L K ⬝ᵥ evenBoundaryFlatRawCoefficients K v) *
          (poleEvenProfile L K ⬝ᵥ
            fun i => star (centeredQuadraticNormal K i))) /
          inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K)
        - quadraticNormalMatrixMoment K
            (reducedCanonicalArchDiagonalMatrix L K) v
        - quadraticNormalMatrixMoment K
            (reducedCanonicalArchOffDiagonalMatrix L K) v
        - ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
            primeSourceWeight q *
              quadraticNormalSourceAtom K v (primeSourceCoordinate q L) := by
  rfl

/-- Norm-square form of the seventh mixed jet. -/
theorem normSq_iteratedDeriv_seven_quadraticNormalSourceAtom
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    Complex.normSq (iteratedDeriv 7 (quadraticNormalSourceAtom K v) 0) =
      4 * (2 * Real.pi) ^ 12 *
        Complex.normSq
          (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)) := by
  rw [iteratedDeriv_seven_quadraticNormalSourceAtom_eq_moment_four K hK v]
  rw [Complex.normSq_mul, Complex.normSq_ofReal]
  ring

/-- Denominator-free Riesz boundary identity in terms of the squared seventh
mixed source jet. -/
theorem two_pi_four_mul_rieszBoundaryEight_eq_endpointScalar_mul_mixedJetNormSq
    (L : ℝ)
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    2 * (2 * Real.pi) ^ 4 *
        canonicalPolePrimeRieszBoundaryTerm L 8 K
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) =
      canonicalPolePrimeRieszEndpointScalar L 8 *
        Complex.normSq
          (iteratedDeriv 7 (quadraticNormalSourceAtom K v) 0) := by
  have hflat := evenBoundaryFlatRawCoefficients_boundaryFlat K v
  have heven := evenBoundaryFlatRawCoefficients_mem_even K v
  rw [canonicalPolePrimeRieszBoundaryTerm_eight_eq_moment_four_of_even
    L K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))]
  · rw [normSq_iteratedDeriv_seven_quadraticNormalSourceAtom K hK v]
    simp only [evenBoundaryFlatRawCoefficients]
    ring
  · simpa [evenBoundaryFlatRawCoefficients] using hflat
  · simpa [evenBoundaryFlatRawCoefficients] using heven

/-- Complete-channel order-eight/order-nine recurrence rewritten through the
same seventh mixed source jet. -/
theorem two_pi_four_mul_rieszEight_sub_nine_eq_endpointScalar_mul_mixedJetNormSq
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    2 * (2 * Real.pi) ^ 4 *
        (canonicalRieszSourceChannelEnergy L 8 K
            (v : EuclideanSpace ℂ (Fin (2 * K + 1))) -
          canonicalRieszSourceChannelEnergy L 9 K
            (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) =
      canonicalPolePrimeRieszEndpointScalar L 8 *
        Complex.normSq
          (iteratedDeriv 7 (quadraticNormalSourceAtom K v) 0) := by
  have hrec :=
    canonicalRieszSourceChannelEnergy_eq_succ_add_boundary
      hL 8 K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))
  norm_num at hrec
  rw [show
    canonicalRieszSourceChannelEnergy L 8 K
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) -
        canonicalRieszSourceChannelEnergy L 9 K
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) =
      canonicalPolePrimeRieszBoundaryTerm L 8 K
        (v : EuclideanSpace ℂ (Fin (2 * K + 1))) by linarith]
  exact
    two_pi_four_mul_rieszBoundaryEight_eq_endpointScalar_mul_mixedJetNormSq
      L K hK v

end Zeta23.CCM

#print axioms Zeta23.CCM.iteratedDeriv_seven_quadraticNormalSourceAtom_eq_moment_four
#print axioms Zeta23.CCM.explicitCanonicalSourceMoment_eq_quadraticNormalSourceAtom_sum
#print axioms Zeta23.CCM.normSq_iteratedDeriv_seven_quadraticNormalSourceAtom
#print axioms Zeta23.CCM.two_pi_four_mul_rieszBoundaryEight_eq_endpointScalar_mul_mixedJetNormSq
#print axioms Zeta23.CCM.two_pi_four_mul_rieszEight_sub_nine_eq_endpointScalar_mul_mixedJetNormSq
