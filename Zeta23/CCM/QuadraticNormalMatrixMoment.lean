import Zeta23.CCM.CanonicalSourceChannels
import Zeta23.CCM.SourceExplicitCubicDefect

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4a: quadratic-normal matrix moment

The source-explicit cubic defect from PR #129 is an inner-product observable of
`canonicalSourceMatrix`.  This module factors out the matrix-linear part of
that observable in raw finite coordinates, then proves once that it is the same
Euclidean inner product used by `evenQuadraticSourceMoment`.

This keeps source-channel algebra away from repeated `toEuclideanLin` coercion
work.  It also theoremizes that the quadratic-normal observable annihilates
scalar identity shifts.  That statement is only about this observable and does
not transport spectral sign, inertia, absolute eigenvalues, or lower bounds.
-/

/-- Raw coefficient function underlying an even Euclidean boundary-flat vector. -/
def evenBoundaryFlatRawCoefficients
    (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K) :
    Fin (2 * K + 1) → ℂ :=
  (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1)))

/-- Unnormalized quadratic-normal observable of an arbitrary finite matrix. -/
def quadraticNormalMatrixNumerator
    (K : ℕ)
    (M : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) : ℂ :=
  (M *ᵥ evenBoundaryFlatRawCoefficients K v) ⬝ᵥ
    (fun i => star (centeredQuadraticNormal K i))

/-- Normalized quadratic-normal matrix moment. -/
def quadraticNormalMatrixMoment
    (K : ℕ)
    (M : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) : ℂ :=
  quadraticNormalMatrixNumerator K M v /
    inner ℂ (centeredQuadraticNormal K) (centeredQuadraticNormal K)

/-- The raw-coordinate numerator is exactly the Euclidean inner product used by
PR #129.  The orientation follows Mathlib's convention: the second vector is
linear and the first is conjugate-linear. -/
theorem quadraticNormalMatrixNumerator_eq_inner
    (K : ℕ)
    (M : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixNumerator K M v =
      inner ℂ (centeredQuadraticNormal K)
        (M.toEuclideanLin
          (v : EuclideanSpace ℂ (Fin (2 * K + 1)))) := by
  unfold quadraticNormalMatrixNumerator evenBoundaryFlatRawCoefficients
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  rw [Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  rfl

/-- PR #129's source moment is the generic matrix moment specialized to the
production canonical source matrix. -/
theorem evenQuadraticSourceMoment_eq_quadraticNormalMatrixMoment
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    evenQuadraticSourceMoment L K v =
      quadraticNormalMatrixMoment K (canonicalSourceMatrix L K) v := by
  unfold evenQuadraticSourceMoment quadraticNormalMatrixMoment
  rw [quadraticNormalMatrixNumerator_eq_inner]

@[simp] theorem quadraticNormalMatrixNumerator_zero
    (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixNumerator K 0 v = 0 := by
  simp [quadraticNormalMatrixNumerator]

/-- Additivity in the matrix argument. -/
theorem quadraticNormalMatrixNumerator_add
    (K : ℕ)
    (A B : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixNumerator K (A + B) v =
      quadraticNormalMatrixNumerator K A v +
        quadraticNormalMatrixNumerator K B v := by
  simp [quadraticNormalMatrixNumerator, Matrix.add_mulVec]

/-- Subtractivity in the matrix argument. -/
theorem quadraticNormalMatrixNumerator_sub
    (K : ℕ)
    (A B : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixNumerator K (A - B) v =
      quadraticNormalMatrixNumerator K A v -
        quadraticNormalMatrixNumerator K B v := by
  simp [quadraticNormalMatrixNumerator, Matrix.sub_mulVec]

/-- Complex scalar-linearity in the matrix argument. -/
theorem quadraticNormalMatrixNumerator_smul
    (K : ℕ) (a : ℂ)
    (A : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixNumerator K (a • A) v =
      a * quadraticNormalMatrixNumerator K A v := by
  simp [quadraticNormalMatrixNumerator, Matrix.smul_mulVec]

/-- Finite-sum linearity in the matrix argument. -/
theorem quadraticNormalMatrixNumerator_sum
    {ι : Type*} [DecidableEq ι]
    (K : ℕ) (s : Finset ι)
    (A : ι → Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixNumerator K (∑ i ∈ s, A i) v =
      ∑ i ∈ s, quadraticNormalMatrixNumerator K (A i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, quadraticNormalMatrixNumerator_add, ih]

@[simp] theorem quadraticNormalMatrixMoment_zero
    (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixMoment K 0 v = 0 := by
  simp [quadraticNormalMatrixMoment]

/-- Additivity of the normalized moment. -/
theorem quadraticNormalMatrixMoment_add
    (K : ℕ)
    (A B : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixMoment K (A + B) v =
      quadraticNormalMatrixMoment K A v +
        quadraticNormalMatrixMoment K B v := by
  unfold quadraticNormalMatrixMoment
  rw [quadraticNormalMatrixNumerator_add]
  ring

/-- Subtractivity of the normalized moment. -/
theorem quadraticNormalMatrixMoment_sub
    (K : ℕ)
    (A B : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixMoment K (A - B) v =
      quadraticNormalMatrixMoment K A v -
        quadraticNormalMatrixMoment K B v := by
  unfold quadraticNormalMatrixMoment
  rw [quadraticNormalMatrixNumerator_sub]
  ring

/-- Scalar-linearity of the normalized moment. -/
theorem quadraticNormalMatrixMoment_smul
    (K : ℕ) (a : ℂ)
    (A : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixMoment K (a • A) v =
      a * quadraticNormalMatrixMoment K A v := by
  unfold quadraticNormalMatrixMoment
  rw [quadraticNormalMatrixNumerator_smul]
  ring

/-- Finite-sum linearity of the normalized moment. -/
theorem quadraticNormalMatrixMoment_sum
    {ι : Type*} [DecidableEq ι]
    (K : ℕ) (s : Finset ι)
    (A : ι → Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixMoment K (∑ i ∈ s, A i) v =
      ∑ i ∈ s, quadraticNormalMatrixMoment K (A i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp [ha, quadraticNormalMatrixMoment_add, ih]

/-- The quadratic normal annihilates the identity action on every even
boundary-flat vector. -/
theorem quadraticNormalMatrixNumerator_one_eq_zero
    (K : ℕ) (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixNumerator K
      (1 : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ) v = 0 := by
  have hnorth := centeredQuadraticNormal_mem_evenBoundaryFlat_orthogonal K
  have hinner :
      inner ℂ (centeredQuadraticNormal K)
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 := by
    rw [inner_eq_zero_symm]
    exact
      ((euclideanEvenBoundaryFlatSubspace K).mem_orthogonal
        (centeredQuadraticNormal K)).mp hnorth
        (v : EuclideanSpace ℂ (Fin (2 * K + 1))) v.property
  rw [EuclideanSpace.inner_eq_star_dotProduct] at hinner
  simpa [quadraticNormalMatrixNumerator,
    evenBoundaryFlatRawCoefficients] using hinner

/-- Adding an arbitrary scalar identity does not change the numerator. -/
theorem quadraticNormalMatrixNumerator_add_scalar_identity
    (K : ℕ) (a : ℂ)
    (M : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixNumerator K
        (M + a • (1 : Matrix
          (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)) v =
      quadraticNormalMatrixNumerator K M v := by
  rw [quadraticNormalMatrixNumerator_add,
    quadraticNormalMatrixNumerator_smul,
    quadraticNormalMatrixNumerator_one_eq_zero]
  simp

/-- Adding an arbitrary scalar identity does not change the normalized moment. -/
theorem quadraticNormalMatrixMoment_add_scalar_identity
    (K : ℕ) (a : ℂ)
    (M : Matrix (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixMoment K
        (M + a • (1 : Matrix
          (Fin (2 * K + 1)) (Fin (2 * K + 1)) ℂ)) v =
      quadraticNormalMatrixMoment K M v := by
  unfold quadraticNormalMatrixMoment
  rw [quadraticNormalMatrixNumerator_add_scalar_identity]

/-- The active quadratic-normal source observable is insensitive to the exact
legacy-to-canonical scalar identity shift.  This theorem is not a spectral
transport theorem. -/
theorem evenQuadraticSourceMoment_eq_legacyPrintedMatrixMoment
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    evenQuadraticSourceMoment L K v =
      quadraticNormalMatrixMoment K (legacyPrintedMatrix L K) v := by
  rw [evenQuadraticSourceMoment_eq_quadraticNormalMatrixMoment]
  rw [canonicalSourceMatrix_eq_legacyPrintedMatrix_add_correction]
  exact quadraticNormalMatrixMoment_add_scalar_identity
    K (((2 * legacyPrintedCorrection L : ℝ) : ℂ))
      (legacyPrintedMatrix L K) v

/-- The index-independent corrected archimedean scalar disappears from the
quadratic-normal observable. -/
theorem quadraticNormalMatrixMoment_canonicalArch_eq_reduced
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    quadraticNormalMatrixMoment K (canonicalArchMatrix L K) v =
      quadraticNormalMatrixMoment K (reducedCanonicalArchMatrix L K) v := by
  rw [canonicalArchMatrix_eq_reducedCanonicalArchMatrix_add_scalar hL K]
  exact quadraticNormalMatrixMoment_add_scalar_identity
    K ((canonicalArchScalarCorrection L : ℝ) : ℂ)
      (reducedCanonicalArchMatrix L K) v

end Zeta23.CCM

#print axioms Zeta23.CCM.quadraticNormalMatrixNumerator_eq_inner
#print axioms Zeta23.CCM.evenQuadraticSourceMoment_eq_quadraticNormalMatrixMoment
#print axioms Zeta23.CCM.quadraticNormalMatrixNumerator_one_eq_zero
#print axioms Zeta23.CCM.quadraticNormalMatrixMoment_add_scalar_identity
#print axioms Zeta23.CCM.evenQuadraticSourceMoment_eq_legacyPrintedMatrixMoment
#print axioms Zeta23.CCM.quadraticNormalMatrixMoment_canonicalArch_eq_reduced
