import Zeta23.CCM.CanonicalSourceMomentAtoms
import Zeta23.CCM.ZeroShiftShellResponse

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ArithmeticFunction ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4b1: absolute canonical source energy

PR #134 closes the denominator-free kernel/source and direct zero-shift
transport layer.  This module restores the scalar-sensitive quadratic
observable needed to locate the absolute spectral origin.

The production canonical source is decomposed exactly into pole, reduced
archimedean diagonal/off-diagonal, the canonical archimedean scalar identity
correction, and the finite von-Mangoldt source-atom sum.  The same absolute
energy is then attached to the already-formalized regular zero-shift trial and
Schur endpoint.

Firewalls:
* the archimedean scalar correction is retained explicitly;
* no source-channel sign or positivity theorem is asserted;
* no one-step domination/coercivity theorem is asserted;
* no zero-shift inverse, pseudoinverse, or Laurent limit is introduced;
* no factor nonzeroness is assumed or inferred;
* no branch exclusion, finite negative-root exclusion, or RH theorem is
  claimed.
-/

/-- Real quadratic energy of a finite complex matrix on a Euclidean vector. -/
def matrixRealEnergy
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) : ℝ :=
  Complex.re
    (quadraticForm M ((EuclideanSpace.equiv ι ℂ) x))

private theorem quadraticForm_matrix_add
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ)
    (u : ι → ℂ) :
    quadraticForm (A + B) u = quadraticForm A u + quadraticForm B u := by
  unfold quadraticForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.add_apply]
  ring

private theorem quadraticForm_matrix_sub
    {ι : Type*} [Fintype ι]
    (A B : Matrix ι ι ℂ)
    (u : ι → ℂ) :
    quadraticForm (A - B) u = quadraticForm A u - quadraticForm B u := by
  unfold quadraticForm
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Matrix.sub_apply]
  ring

private theorem quadraticForm_matrix_smul_real
    {ι : Type*} [Fintype ι]
    (a : ℝ)
    (A : Matrix ι ι ℂ)
    (u : ι → ℂ) :
    quadraticForm (((a : ℂ)) • A) u =
      (a : ℂ) * quadraticForm A u := by
  unfold quadraticForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

@[simp] theorem matrixRealEnergy_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℂ ι) :
    matrixRealEnergy (0 : Matrix ι ι ℂ) x = 0 := by
  unfold matrixRealEnergy
  have h := congrArg Complex.re
    (quadraticForm_matrix_smul_real
      (a := 0) (A := (1 : Matrix ι ι ℂ))
      ((EuclideanSpace.equiv ι ℂ) x))
  simpa using h

/-- Additivity in the matrix argument. -/
theorem matrixRealEnergy_add
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    matrixRealEnergy (A + B) x =
      matrixRealEnergy A x + matrixRealEnergy B x := by
  unfold matrixRealEnergy
  rw [quadraticForm_matrix_add, Complex.add_re]

/-- Subtractivity in the matrix argument. -/
theorem matrixRealEnergy_sub
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    matrixRealEnergy (A - B) x =
      matrixRealEnergy A x - matrixRealEnergy B x := by
  unfold matrixRealEnergy
  rw [quadraticForm_matrix_sub, Complex.sub_re]

/-- Real scalar-linearity in the matrix argument. -/
theorem matrixRealEnergy_smul_real
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ)
    (A : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    matrixRealEnergy (((a : ℂ)) • A) x =
      a * matrixRealEnergy A x := by
  unfold matrixRealEnergy
  rw [quadraticForm_matrix_smul_real, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Finite-sum linearity in the matrix argument. -/
theorem matrixRealEnergy_sum
    {ι α : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (s : Finset α)
    (A : α → Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    matrixRealEnergy (∑ a ∈ s, A a) x =
      ∑ a ∈ s, matrixRealEnergy (A a) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [matrixRealEnergy_add, ih]

/-- Existing exact bridge to the Euclidean self-energy orientation used by the
spectral and Schur layers. -/
theorem matrixRealEnergy_eq_re_inner_apply_self
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    matrixRealEnergy M x =
      Complex.re (inner ℂ (M.toEuclideanLin x) x) := by
  exact quadraticForm_re_eq_re_inner_apply_self M x

/-- Absolute energy of the identity matrix is the Euclidean norm square. -/
theorem matrixRealEnergy_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : EuclideanSpace ℂ ι) :
    matrixRealEnergy (1 : Matrix ι ι ℂ) x = ‖x‖ ^ 2 := by
  rw [matrixRealEnergy_eq_re_inner_apply_self]
  have hone :
      (1 : Matrix ι ι ℂ).toEuclideanLin x = x := by
    change (Matrix.toLpLin 2 2 (1 : Matrix ι ι ℂ)) x = x
    rw [Matrix.toLpLin_one]
    rfl
  rw [hone]
  simpa only [RCLike.re_to_complex] using
    (norm_sq_eq_re_inner (𝕜 := ℂ) x).symm

/-- Absolute energy remembers a real scalar identity shift.  This is the
scalar-origin sensitivity deliberately absent from the #131 source moment. -/
theorem matrixRealEnergy_add_real_scalar_identity
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ℝ)
    (M : Matrix ι ι ℂ)
    (x : EuclideanSpace ℂ ι) :
    matrixRealEnergy
        (M + ((a : ℂ) • (1 : Matrix ι ι ℂ))) x =
      matrixRealEnergy M x + a * ‖x‖ ^ 2 := by
  rw [matrixRealEnergy_add, matrixRealEnergy_smul_real,
    matrixRealEnergy_one]

/-- Endpoint acceptance test: the elementary source atom at `ω = 1` contributes
exactly twice the Euclidean norm square. -/
theorem matrixRealEnergy_sourceMatrix_one
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (sourceMatrix 1 K) x = 2 * ‖x‖ ^ 2 := by
  have htwo : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [sourceMatrix_one, htwo, matrixRealEnergy_smul_real, matrixRealEnergy_one]

/-- Absolute canonical energy on one legal reversal-parity carrier. -/
def parityCanonicalSourceEnergy
    (p : ReversalParity)
    (L : ℝ) (K : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p K) : ℝ :=
  Complex.re
    (inner ℂ (parityCompressedCanonical p L K v) v)

/-- Compression preserves the self-energy, so the parity energy is exactly the
ambient production-matrix energy on the same Euclidean vector. -/
theorem parityCanonicalSourceEnergy_eq_matrixRealEnergy
    (p : ReversalParity)
    (L : ℝ) (K : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p K) :
    parityCanonicalSourceEnergy p L K v =
      matrixRealEnergy (canonicalSourceMatrix L K)
        (v : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
  unfold parityCanonicalSourceEnergy
  rw [re_inner_parityCompressedCanonical_self]
  exact (matrixRealEnergy_eq_re_inner_apply_self
    (canonicalSourceMatrix L K)
    (v : EuclideanSpace ℂ (Fin (2 * K + 1)))).symm

/-- Exact absolute-energy expansion of the finite prime-power channel into the
already theorem-locked elementary source matrices. -/
theorem matrixRealEnergy_canonicalPrimeMatrix_eq_sum_sourceMatrix
    (L : ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalPrimeMatrix L K) x =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        (Λ q / Real.sqrt q : ℝ) *
          matrixRealEnergy
            (sourceMatrix (primeSourceCoordinate q L) K) x := by
  rw [canonicalPrimeMatrix_eq_sum_sourceMatrix]
  rw [matrixRealEnergy_sum]
  apply Finset.sum_congr rfl
  intro q hq
  change
    matrixRealEnergy
        ((((Λ q / Real.sqrt q : ℝ) : ℂ)) •
          sourceMatrix (primeSourceCoordinate q L) K) x =
      (Λ q / Real.sqrt q : ℝ) *
        matrixRealEnergy
          (sourceMatrix (primeSourceCoordinate q L) K) x
  exact matrixRealEnergy_smul_real
    (Λ q / Real.sqrt q : ℝ)
    (sourceMatrix (primeSourceCoordinate q L) K) x

/-- Exact absolute-energy split of the canonical archimedean channel.  The
index-independent scalar correction is retained as a norm-square term. -/
theorem matrixRealEnergy_canonicalArchMatrix_eq_channels
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalArchMatrix L K) x =
      matrixRealEnergy (reducedCanonicalArchDiagonalMatrix L K) x +
        matrixRealEnergy (reducedCanonicalArchOffDiagonalMatrix L K) x +
          canonicalArchScalarCorrection L * ‖x‖ ^ 2 := by
  rw [canonicalArchMatrix_eq_reducedCanonicalArchMatrix_add_scalar hL K]
  rw [reducedCanonicalArchMatrix_eq_diagonal_add_offDiagonal]
  rw [matrixRealEnergy_add, matrixRealEnergy_add,
    matrixRealEnergy_smul_real, matrixRealEnergy_one]

/-- Exact arithmetic channel expression for one Euclidean vector. -/
def canonicalSourceChannelEnergy
    (L : ℝ) (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  matrixRealEnergy (canonicalPoleMatrix L K) x -
    matrixRealEnergy (reducedCanonicalArchDiagonalMatrix L K) x -
    matrixRealEnergy (reducedCanonicalArchOffDiagonalMatrix L K) x -
    canonicalArchScalarCorrection L * ‖x‖ ^ 2 -
    ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
      (Λ q / Real.sqrt q : ℝ) *
        matrixRealEnergy
          (sourceMatrix (primeSourceCoordinate q L) K) x

/-- Headline A4b1 production identity: absolute canonical energy is exactly
pole minus reduced arch diagonal/off-diagonal minus the scalar normalization
and the finite von-Mangoldt source-atom sum. -/
theorem matrixRealEnergy_canonicalSourceMatrix_eq_channels
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    matrixRealEnergy (canonicalSourceMatrix L K) x =
      canonicalSourceChannelEnergy L K x := by
  rw [canonicalSourceMatrix_eq_pole_sub_arch_sub_prime]
  rw [matrixRealEnergy_sub, matrixRealEnergy_sub]
  rw [matrixRealEnergy_canonicalArchMatrix_eq_channels hL K x]
  rw [matrixRealEnergy_canonicalPrimeMatrix_eq_sum_sourceMatrix L K x]
  unfold canonicalSourceChannelEnergy
  ring

/-- Parity-compressed form of the exact production channel decomposition. -/
theorem parityCanonicalSourceEnergy_eq_channels
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (v : euclideanParityBoundaryFlatSubspace p K) :
    parityCanonicalSourceEnergy p L K v =
      canonicalSourceChannelEnergy L K
        (v : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
  rw [parityCanonicalSourceEnergy_eq_matrixRealEnergy]
  exact matrixRealEnergy_canonicalSourceMatrix_eq_channels
    hL K (v : EuclideanSpace ℂ (Fin (2 * K + 1)))

/-- Absolute energy of the canonical one-dimensional cubic successor shell. -/
def cubicShellRealEnergy
    (p : ReversalParity)
    (L : ℝ) (N : ℕ) : ℝ :=
  parityCanonicalSourceEnergy p L (N + 1)
    (intrinsicCubicShellPart p N :
      euclideanParityBoundaryFlatSubspace p (N + 1))

/-- Exact channel expansion of the cubic shell energy.  No sign is asserted. -/
theorem cubicShellRealEnergy_eq_channels
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) :
    cubicShellRealEnergy p L N =
      canonicalSourceChannelEnergy L (N + 1)
        ((intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
  unfold cubicShellRealEnergy
  exact parityCanonicalSourceEnergy_eq_channels
    p hL (N + 1)
      (intrinsicCubicShellPart p N :
        euclideanParityBoundaryFlatSubspace p (N + 1))

/-- In the regular zero-shift branch, the absolute trial energy is exactly the
real part of the already-canonical Schur endpoint. -/
theorem parityCanonicalSourceEnergy_cubicZeroShiftTrialVector_eq_re_endpoint
    (p : ReversalParity)
    (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    parityCanonicalSourceEnergy p L (N + 1)
        (cubicZeroShiftTrialVector p L N x₀) =
      Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) := by
  unfold parityCanonicalSourceEnergy
  exact congrArg Complex.re
    (inner_parityCompressedCanonical_cubicZeroShiftTrialVector_self
      p L N x₀ hx₀)

/-- Arithmetic form of the regular zero-shift endpoint: its real part is the
exact production pole/arch/scalar/prime channel expression on the canonical
zero-shift trial. -/
theorem cubicZeroShiftSchurEndpoint_re_eq_canonicalSourceChannels
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) =
      canonicalSourceChannelEnergy L (N + 1)
        (cubicZeroShiftTrialVector p L N x₀ :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
  calc
    Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) =
        parityCanonicalSourceEnergy p L (N + 1)
          (cubicZeroShiftTrialVector p L N x₀) := by
      exact
        (parityCanonicalSourceEnergy_cubicZeroShiftTrialVector_eq_re_endpoint
          p L N x₀ hx₀).symm
    _ = canonicalSourceChannelEnergy L (N + 1)
        (cubicZeroShiftTrialVector p L N x₀ :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
      exact parityCanonicalSourceEnergy_eq_channels
        p hL (N + 1) (cubicZeroShiftTrialVector p L N x₀)

/-- The already-formalized safe negative explicit Schur root forces the new
absolute canonical trial energy to be strictly negative. -/
theorem parityCanonicalSourceEnergy_cubicZeroShiftTrialVector_neg_of_explicit_root
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicExplicitSchurScalar p hL N hprev lam hlam = 0) :
    parityCanonicalSourceEnergy p L (N + 1)
        (cubicZeroShiftTrialVector p L N x₀) < 0 := by
  rw [parityCanonicalSourceEnergy_cubicZeroShiftTrialVector_eq_re_endpoint
    p L N x₀ hx₀]
  exact cubicZeroShiftSchurEndpoint_re_neg_of_explicit_root
    p hL N hN hprev x₀ hx₀ lam hlam hroot

end Zeta23.CCM

#print axioms Zeta23.CCM.matrixRealEnergy_add_real_scalar_identity
#print axioms Zeta23.CCM.matrixRealEnergy_sourceMatrix_one
#print axioms Zeta23.CCM.matrixRealEnergy_canonicalPrimeMatrix_eq_sum_sourceMatrix
#print axioms Zeta23.CCM.matrixRealEnergy_canonicalArchMatrix_eq_channels
#print axioms Zeta23.CCM.matrixRealEnergy_canonicalSourceMatrix_eq_channels
#print axioms Zeta23.CCM.parityCanonicalSourceEnergy_eq_channels
#print axioms Zeta23.CCM.parityCanonicalSourceEnergy_cubicZeroShiftTrialVector_eq_re_endpoint
#print axioms Zeta23.CCM.cubicZeroShiftSchurEndpoint_re_eq_canonicalSourceChannels
#print axioms Zeta23.CCM.parityCanonicalSourceEnergy_cubicZeroShiftTrialVector_neg_of_explicit_root