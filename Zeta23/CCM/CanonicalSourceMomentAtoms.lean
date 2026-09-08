import Zeta23.CCM.QuadraticNormalMatrixMoment
import Zeta23.CCM.SourceMatrix
import Zeta23.CCM.ConstrainedParity

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ArithmeticFunction ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4a: source-moment atoms

This module rewrites two exact production channels in forms adapted to the
quadratic-normal observable.

* The prime channel is a finite von-Mangoldt weighted sum of the already
  theorem-locked elementary `sourceMatrix` atoms.
* The pole channel is a difference of two rank-one bilinear profiles on the
  full centered grid.  The odd profile pairs to zero against every even
  boundary-flat input, leaving one exact pole channel in the active moment.

No sign or nonzeroness of any resulting factor is asserted.
-/

/-- Complex von-Mangoldt weight of one finite prime-power source atom. -/
def primeSourceWeight (q : ℕ) : ℂ :=
  ((Λ q / Real.sqrt q : ℝ) : ℂ)

/-- Source coordinate corresponding to the finite prime-power logarithm. -/
def primeSourceCoordinate (q : ℕ) (L : ℝ) : ℝ :=
  1 - Real.log q / L

/-- Exact source-atom expansion of the finite prime-power matrix. -/
theorem canonicalPrimeMatrix_eq_sum_sourceMatrix
    (L : ℝ) (K : ℕ) :
    canonicalPrimeMatrix L K =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q • sourceMatrix (primeSourceCoordinate q L) K := by
  classical
  ext i j
  change
    ((∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
      (Λ q / Real.sqrt q : ℝ) *
        qBasis (centeredIndex K i) (centeredIndex K j) (Real.log q) L : ℝ) : ℂ) =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q *
          sourceEntry (primeSourceCoordinate q L)
            (centeredIndex K i) (centeredIndex K j)
  push_cast
  apply Finset.sum_congr rfl
  intro q hq
  simp [primeSourceWeight, primeSourceCoordinate,
    sourceEntry_one_sub_eq_qBasis]

/-- Exact prime-channel numerator as a finite weighted sum of elementary source
numerators. -/
theorem quadraticNormalPrimeNumerator_eq_sum_sourceMatrix
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixNumerator K (canonicalPrimeMatrix L K) v =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q *
          quadraticNormalMatrixNumerator K
            (sourceMatrix (primeSourceCoordinate q L) K) v := by
  rw [canonicalPrimeMatrix_eq_sum_sourceMatrix]
  rw [quadraticNormalMatrixNumerator_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [quadraticNormalMatrixNumerator_smul]

/-- Exact prime-channel normalized moment as a finite weighted source-atom sum. -/
theorem quadraticNormalPrimeMoment_eq_sum_sourceMatrix
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixMoment K (canonicalPrimeMatrix L K) v =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q *
          quadraticNormalMatrixMoment K
            (sourceMatrix (primeSourceCoordinate q L) K) v := by
  rw [canonicalPrimeMatrix_eq_sum_sourceMatrix]
  rw [quadraticNormalMatrixMoment_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [quadraticNormalMatrixMoment_smul]

/-- Common positive denominator of the pole profiles at positive aperture. -/
def poleProfileDenominator (n : ℤ) (L : ℝ) : ℝ :=
  L ^ 2 + 16 * Real.pi ^ 2 * (n : ℝ) ^ 2

/-- Real even pole profile. -/
def poleEvenProfileReal (n : ℤ) (L : ℝ) : ℝ :=
  L / poleProfileDenominator n L

/-- Real odd pole profile. -/
def poleOddProfileReal (n : ℤ) (L : ℝ) : ℝ :=
  (4 * Real.pi * (n : ℝ)) / poleProfileDenominator n L

/-- Common pole scale. -/
def poleProfileScaleReal (L : ℝ) : ℝ :=
  32 * L * Real.sinh (L / 4) ^ 2

/-- Complex centered even pole profile. -/
def poleEvenProfile (L : ℝ) (K : ℕ) : Fin (2 * K + 1) → ℂ :=
  fun i => (poleEvenProfileReal (centeredIndex K i) L : ℂ)

/-- Complex centered odd pole profile. -/
def poleOddProfile (L : ℝ) (K : ℕ) : Fin (2 * K + 1) → ℂ :=
  fun i => (poleOddProfileReal (centeredIndex K i) L : ℂ)

/-- Complex pole scale. -/
def poleProfileScale (L : ℝ) : ℂ :=
  (poleProfileScaleReal L : ℂ)

/-- Pole profile denominators are strictly positive at positive aperture. -/
theorem poleProfileDenominator_pos
    {L : ℝ} (hL : 0 < L) (n : ℤ) :
    0 < poleProfileDenominator n L := by
  unfold poleProfileDenominator
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
  positivity

/-- Exact real scalar factorization of one pole entry. -/
theorem poleComponent_eq_profile_factorization
    {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    poleComponent n m L =
      poleProfileScaleReal L *
        (poleEvenProfileReal n L * poleEvenProfileReal m L -
          poleOddProfileReal n L * poleOddProfileReal m L) := by
  have hn := poleProfileDenominator_pos hL n
  have hm := poleProfileDenominator_pos hL m
  unfold poleComponent poleProfileScaleReal poleEvenProfileReal
    poleOddProfileReal poleProfileDenominator
  dsimp
  field_simp [ne_of_gt hn, ne_of_gt hm]
  push_cast
  ring

/-- Exact rank-two bilinear factorization of the full finite pole matrix. -/
theorem canonicalPoleMatrix_eq_rankTwoProfiles
    {L : ℝ} (hL : 0 < L) (K : ℕ) :
    canonicalPoleMatrix L K =
      poleProfileScale L •
        (vecMulVec (poleEvenProfile L K) (poleEvenProfile L K) -
          vecMulVec (poleOddProfile L K) (poleOddProfile L K)) := by
  ext i j
  change
    (poleComponent (centeredIndex K i) (centeredIndex K j) L : ℂ) =
      poleProfileScale L *
        (poleEvenProfile L K i * poleEvenProfile L K j -
          poleOddProfile L K i * poleOddProfile L K j)
  have hreal :=
    poleComponent_eq_profile_factorization hL
      (centeredIndex K i) (centeredIndex K j)
  simpa [poleProfileScale, poleEvenProfile, poleOddProfile] using
    congrArg (fun x : ℝ => (x : ℂ)) hreal

/-- Local complex specialization of rank-one matrix action, avoiding any
opposite-ring coercion in the project theorem surface. -/
theorem complex_vecMulVec_mulVec
    {K : ℕ}
    (u w x : Fin (2 * K + 1) → ℂ) :
    vecMulVec u w *ᵥ x = (w ⬝ᵥ x) • u := by
  ext i
  simp [Matrix.mulVec, dotProduct, Matrix.vecMulVec,
    Finset.mul_sum, mul_assoc]

/-- Quadratic-normal numerator of a rank-one bilinear matrix. -/
theorem quadraticNormalMatrixNumerator_vecMulVec
    (K : ℕ)
    (u w : Fin (2 * K + 1) → ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixNumerator K (vecMulVec u w) v =
      (w ⬝ᵥ evenBoundaryFlatRawCoefficients K v) *
        (u ⬝ᵥ fun i => star (centeredQuadraticNormal K i)) := by
  unfold quadraticNormalMatrixNumerator
  rw [complex_vecMulVec_mulVec]
  simp [dotProduct, Finset.mul_sum, mul_assoc]

/-- Generic bilinear cancellation for an odd profile against an even vector
under the centered reversal. -/
theorem dotProduct_eq_zero_of_reverse_odd_even
    (K : ℕ)
    (r u : Fin (2 * K + 1) → ℂ)
    (hr : reverseCoefficients K r = -r)
    (hu : reverseCoefficients K u = u) :
    r ⬝ᵥ u = 0 := by
  unfold dotProduct
  have hrev :
      (∑ i, r i * u i) = -(∑ i, r i * u i) := by
    calc
      (∑ i, r i * u i) =
          ∑ i : Fin (2 * K + 1), r i.rev * u i.rev := by
            rw [← Equiv.sum_comp Fin.revPerm]
            simp
      _ = -(∑ i, r i * u i) := by
            rw [← Finset.sum_neg_distrib]
            apply Finset.sum_congr rfl
            intro i hi
            have hri := congrFun hr i
            have hui := congrFun hu i
            simp only [reverseCoefficients, Pi.neg_apply] at hri hui
            rw [hri, hui]
            ring
  have hsum :
      (∑ i, r i * u i) + (∑ i, r i * u i) = 0 :=
    (eq_neg_iff_add_eq_zero).mp hrev
  linear_combination (1 / 2 : ℂ) * hsum

/-- The centered pole-even profile is reversal even. -/
theorem reverseCoefficients_poleEvenProfile
    (L : ℝ) (K : ℕ) :
    reverseCoefficients K (poleEvenProfile L K) = poleEvenProfile L K := by
  ext i
  simp [reverseCoefficients, poleEvenProfile, poleEvenProfileReal,
    poleProfileDenominator]

/-- The centered pole-odd profile is reversal odd. -/
theorem reverseCoefficients_poleOddProfile
    (L : ℝ) (K : ℕ) :
    reverseCoefficients K (poleOddProfile L K) = -poleOddProfile L K := by
  ext i
  simp [reverseCoefficients, poleOddProfile, poleOddProfileReal,
    poleProfileDenominator]
  ring

/-- The odd pole profile pairs to zero with every even boundary-flat input. -/
theorem poleOddProfile_dot_evenBoundaryFlat_eq_zero
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    poleOddProfile L K ⬝ᵥ evenBoundaryFlatRawCoefficients K v = 0 := by
  have hvbf :
      evenBoundaryFlatRawCoefficients K v ∈ evenBoundaryFlatSubspace K := by
    change
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) ∈
        evenBoundaryFlatSubspace K
    exact
      (mem_euclideanEvenBoundaryFlatSubspace_iff K
        (v : EuclideanSpace ℂ (Fin (2 * K + 1)))).mp v.property
  have heven :
      reverseCoefficients K (evenBoundaryFlatRawCoefficients K v) =
        evenBoundaryFlatRawCoefficients K v :=
    (mem_evenCoefficientSubspace_iff K _).mp hvbf.2
  exact dotProduct_eq_zero_of_reverse_odd_even K
    (poleOddProfile L K) (evenBoundaryFlatRawCoefficients K v)
    (reverseCoefficients_poleOddProfile L K) heven

/-- On the even boundary-flat sector, the pole numerator has only one surviving
profile channel. -/
theorem quadraticNormalPoleNumerator_eq_evenProfile
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixNumerator K (canonicalPoleMatrix L K) v =
      poleProfileScale L *
        (poleEvenProfile L K ⬝ᵥ evenBoundaryFlatRawCoefficients K v) *
        (poleEvenProfile L K ⬝ᵥ
          fun i => star (centeredQuadraticNormal K i)) := by
  rw [canonicalPoleMatrix_eq_rankTwoProfiles hL K]
  rw [quadraticNormalMatrixNumerator_smul,
    quadraticNormalMatrixNumerator_sub,
    quadraticNormalMatrixNumerator_vecMulVec,
    quadraticNormalMatrixNumerator_vecMulVec,
    poleOddProfile_dot_evenBoundaryFlat_eq_zero]
  ring

/-- Normalized one-channel pole formula on the even boundary-flat sector. -/
theorem quadraticNormalPoleMoment_eq_evenProfile
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixMoment K (canonicalPoleMatrix L K) v =
      (poleProfileScale L *
        (poleEvenProfile L K ⬝ᵥ evenBoundaryFlatRawCoefficients K v) *
        (poleEvenProfile L K ⬝ᵥ
          fun i => star (centeredQuadraticNormal K i))) /
        inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K) := by
  unfold quadraticNormalMatrixMoment
  rw [quadraticNormalPoleNumerator_eq_evenProfile hL K v]

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalPrimeMatrix_eq_sum_sourceMatrix
#print axioms Zeta23.CCM.quadraticNormalPrimeMoment_eq_sum_sourceMatrix
#print axioms Zeta23.CCM.poleComponent_eq_profile_factorization
#print axioms Zeta23.CCM.canonicalPoleMatrix_eq_rankTwoProfiles
#print axioms Zeta23.CCM.poleOddProfile_dot_evenBoundaryFlat_eq_zero
#print axioms Zeta23.CCM.quadraticNormalPoleMoment_eq_evenProfile
