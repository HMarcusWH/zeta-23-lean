import Zeta23.CCM.CanonicalSourcePairing
import Zeta23.CCM.ZeroShiftSchurEndpoint

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4b2a: canonical one-step determinant reduction

This module does not prove the missing canonical positivity theorem.  It makes
that theorem exact and proves that it is sufficient.

For the intrinsic predecessor block `A`, canonical cubic shell `c`, and shell
coupling `b = P_W T c`, define

  q_c = Re <T c,c>,
  q_A(w) = Re <A w,w>,
  Delta(w) = q_c q_A(w) - |<w,b>|^2.

The one-step domination certificate is `q_c >= 0` together with
`Delta(w) >= 0` for every predecessor vector.  The determinant inequality
annihilates the coupling on `ker A`, so the zero-shift preimage exists.  On that
regular branch it forces the zero-shift endpoint nonnegative, contradicting the
already-proved strict negativity forced by any safe negative explicit Schur
root.

Firewalls:
* no one-step domination certificate is asserted to hold;
* no predecessor positive-definiteness or zero-shift inverse is used;
* no division by shell or predecessor energy is used;
* no source-atom sign is asserted;
* no unconditional negative-root exclusion, finite-to-infinite closure, or RH
  theorem is claimed.
-/

/-- Real quadratic energy of the projected predecessor block. -/
def intrinsicPredecessorRealEnergy
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) : ℝ :=
  Complex.re
    (inner ℂ
      ((intrinsicPredecessorBlock p L N w :
          intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1))
      (w : euclideanParityBoundaryFlatSubspace p (N + 1)))

/-- The predecessor energy is the full successor canonical energy restricted to
`W`. -/
theorem intrinsicPredecessorRealEnergy_eq_parityCanonicalSourceEnergy
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorRealEnergy p L N w =
      parityCanonicalSourceEnergy p L (N + 1)
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  unfold intrinsicPredecessorRealEnergy parityCanonicalSourceEnergy
  exact congrArg Complex.re
    (inner_intrinsicPredecessorBlock_self p L N w)

/-- Exact production-channel expression for predecessor energy. -/
theorem intrinsicPredecessorRealEnergy_eq_channels
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) :
    intrinsicPredecessorRealEnergy p L N w =
      canonicalSourceChannelEnergy L (N + 1)
        ((w : euclideanParityBoundaryFlatSubspace p (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
  rw [intrinsicPredecessorRealEnergy_eq_parityCanonicalSourceEnergy]
  exact parityCanonicalSourceEnergy_eq_channels
    p hL (N + 1)
      (w : euclideanParityBoundaryFlatSubspace p (N + 1))

/-- Canonical shell/predecessor coupling in the orientation used by the
zero-shift range theorem. -/
def cubicShellCoupling
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) : ℂ :=
  inner ℂ
    (w : euclideanParityBoundaryFlatSubspace p (N + 1))
    ((intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N) :
        intrinsicParityPredecessorSubspace p N) :
      euclideanParityBoundaryFlatSubspace p (N + 1))

/-- The shell coupling is exactly the parity-compressed canonical off-diagonal
pairing against the cubic shell. -/
theorem cubicShellCoupling_eq_parityCanonicalSourcePairing
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) :
    cubicShellCoupling p L N w =
      parityCanonicalSourcePairing p L (N + 1)
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  unfold cubicShellCoupling parityCanonicalSourcePairing
  exact
    (inner_intrinsicPredecessor_parityCompressedCanonical_shell_eq
      p L N w (intrinsicCubicShellPart p N)).symm

/-- Exact production-channel expression for the shell coupling. -/
theorem cubicShellCoupling_eq_channels
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) :
    cubicShellCoupling p L N w =
      canonicalSourceChannelPairing L (N + 1)
        ((w : euclideanParityBoundaryFlatSubspace p (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
        ((intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) := by
  rw [cubicShellCoupling_eq_parityCanonicalSourcePairing]
  exact parityCanonicalSourcePairing_eq_channels
    p hL (N + 1)
      (w : euclideanParityBoundaryFlatSubspace p (N + 1))
      (intrinsicCubicShellPart p N :
        euclideanParityBoundaryFlatSubspace p (N + 1))

/-- Denominator-free one-step Gram/Schur determinant. -/
def cubicOneStepDeterminant
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) : ℝ :=
  cubicShellRealEnergy p L N * intrinsicPredecessorRealEnergy p L N w -
    ‖cubicShellCoupling p L N w‖ ^ 2

/-- Exact channel form of the one-step determinant. -/
theorem cubicOneStepDeterminant_eq_channels
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L) (N : ℕ)
    (w : intrinsicParityPredecessorSubspace p N) :
    cubicOneStepDeterminant p L N w =
      canonicalSourceChannelEnergy L (N + 1)
          (((intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) *
        canonicalSourceChannelEnergy L (N + 1)
          ((w : euclideanParityBoundaryFlatSubspace p (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) -
        ‖canonicalSourceChannelPairing L (N + 1)
          ((w : euclideanParityBoundaryFlatSubspace p (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))
          ((intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1)) :
            EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))‖ ^ 2 := by
  unfold cubicOneStepDeterminant
  rw [cubicShellRealEnergy_eq_channels p hL N]
  rw [intrinsicPredecessorRealEnergy_eq_channels p hL N w]
  rw [cubicShellCoupling_eq_channels p hL N w]

/-- Exact A4b2 certificate: nonnegative shell energy and nonnegative one-step
determinant on every predecessor vector.  This is a proposition, not a theorem
that the certificate holds. -/
def canonicalOneStepDomination
    (p : ReversalParity) (L : ℝ) (N : ℕ) : Prop :=
  0 ≤ cubicShellRealEnergy p L N ∧
    ∀ w : intrinsicParityPredecessorSubspace p N,
      0 ≤ cubicOneStepDeterminant p L N w

/-- Kernel vectors have zero predecessor energy. -/
theorem intrinsicPredecessorRealEnergy_eq_zero_of_kernel
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (z : intrinsicParityPredecessorSubspace p N)
    (hz : intrinsicPredecessorBlock p L N z = 0) :
    intrinsicPredecessorRealEnergy p L N z = 0 := by
  unfold intrinsicPredecessorRealEnergy
  rw [hz]
  simp

/-- Nonnegative one-step determinant on a predecessor-kernel vector forces the
full complex shell coupling to vanish. -/
theorem cubicShellCoupling_eq_zero_of_kernel_of_determinant_nonnegative
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (z : intrinsicParityPredecessorSubspace p N)
    (hz : intrinsicPredecessorBlock p L N z = 0)
    (hdet : 0 ≤ cubicOneStepDeterminant p L N z) :
    cubicShellCoupling p L N z = 0 := by
  have henergy := intrinsicPredecessorRealEnergy_eq_zero_of_kernel p L N z hz
  unfold cubicOneStepDeterminant at hdet
  rw [henergy, mul_zero, zero_sub] at hdet
  have hnormsq : ‖cubicShellCoupling p L N z‖ ^ 2 ≤ 0 := by
    nlinarith
  have hnorm0 : ‖cubicShellCoupling p L N z‖ = 0 := by
    nlinarith [norm_nonneg (cubicShellCoupling p L N z)]
  exact norm_eq_zero.mp hnorm0

/-- Full domination annihilates the canonical cubic coupling on `ker A`. -/
theorem cubicShellCoupling_eq_zero_on_kernel_of_canonicalOneStepDomination
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hdom : canonicalOneStepDomination p L N)
    (z : intrinsicParityPredecessorSubspace p N)
    (hz : intrinsicPredecessorBlock p L N z = 0) :
    cubicShellCoupling p L N z = 0 :=
  cubicShellCoupling_eq_zero_of_kernel_of_determinant_nonnegative
    p L N z hz (hdom.2 z)

/-- Domination removes the resonant zero-shift branch by placing the shell
coupling in `range A`. -/
theorem exists_cubicZeroShift_preimage_of_canonicalOneStepDomination
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hdom : canonicalOneStepDomination p L N) :
    ∃ x₀ : intrinsicParityPredecessorSubspace p N,
      intrinsicPredecessorBlock p L N x₀ =
        intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N) := by
  let b := intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)
  have horth :
      ∀ z : intrinsicParityPredecessorSubspace p N,
        intrinsicPredecessorBlock p L N z = 0 →
          inner ℂ
            (z : euclideanParityBoundaryFlatSubspace p (N + 1))
            (b : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
    intro z hz
    have hzCoupling :=
      cubicShellCoupling_eq_zero_on_kernel_of_canonicalOneStepDomination
        p L N hdom z hz
    simpa [cubicShellCoupling, b] using hzCoupling
  have hbRange :=
    mem_intrinsicPredecessorBlock_range_of_inner_kernel_eq_zero
      p L N b horth
  rcases hbRange with ⟨x₀, hx₀⟩
  exact ⟨x₀, by simpa [b] using hx₀⟩

/-- Predecessor nonnegativity descends to the real predecessor-energy wrapper. -/
theorem intrinsicPredecessorRealEnergy_nonnegative
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L) (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (w : intrinsicParityPredecessorSubspace p N) :
    0 ≤ intrinsicPredecessorRealEnergy p L N w := by
  exact re_inner_intrinsicPredecessorBlock_nonnegative p hL N hprev w

/-- On a zero-shift preimage, the real part of the shell coupling equals the
predecessor quadratic energy. -/
theorem cubicShellCoupling_re_eq_predecessorRealEnergy_of_preimage
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    Complex.re (cubicShellCoupling p L N x₀) =
      intrinsicPredecessorRealEnergy p L N x₀ := by
  unfold cubicShellCoupling intrinsicPredecessorRealEnergy
  rw [← hx₀]
  exact congrArg Complex.re
    (intrinsicPredecessorBlock_isSymmetric p L N x₀ x₀).symm

/-- The regular zero-shift endpoint is shell energy minus predecessor energy. -/
theorem cubicZeroShiftSchurEndpoint_re_eq_shell_sub_predecessorRealEnergy
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) =
      cubicShellRealEnergy p L N -
        intrinsicPredecessorRealEnergy p L N x₀ := by
  unfold cubicZeroShiftSchurEndpoint cubicShellRealEnergy
  unfold parityCanonicalSourceEnergy
  rw [Complex.sub_re]
  congr 1
  unfold intrinsicPredecessorRealEnergy
  rw [← hx₀]
  exact congrArg Complex.re
    (intrinsicPredecessorBlock_isSymmetric p L N x₀ x₀).symm

/-- Full domination forces every regular zero-shift endpoint nonnegative.  The
proof does not divide by predecessor energy; the zero-energy case is split
off explicitly. -/
theorem cubicZeroShiftSchurEndpoint_re_nonnegative_of_canonicalOneStepDomination
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L) (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hdom : canonicalOneStepDomination p L N)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ : intrinsicPredecessorBlock p L N x₀ =
      intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) :
    0 ≤ Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) := by
  let q := cubicShellRealEnergy p L N
  let r := intrinsicPredecessorRealEnergy p L N x₀
  let z := cubicShellCoupling p L N x₀
  have hq : 0 ≤ q := by simpa [q] using hdom.1
  have hr : 0 ≤ r := by
    simpa [r] using intrinsicPredecessorRealEnergy_nonnegative
      p hL N hprev x₀
  have hdet := hdom.2 x₀
  have hzre : Complex.re z = r := by
    simpa [z, r] using
      cubicShellCoupling_re_eq_predecessorRealEnergy_of_preimage
        p L N x₀ hx₀
  have habs : |r| ≤ ‖z‖ := by
    rw [← hzre]
    exact Complex.abs_re_le_norm z
  have habssq : |r| ^ 2 ≤ ‖z‖ ^ 2 := by
    nlinarith [abs_nonneg r, norm_nonneg z]
  have hrsq : r ^ 2 ≤ ‖z‖ ^ 2 := by
    simpa [sq_abs] using habssq
  have hnormle : ‖z‖ ^ 2 ≤ q * r := by
    change 0 ≤ q * r - ‖z‖ ^ 2 at hdet
    nlinarith
  have hrr : r ^ 2 ≤ q * r := le_trans hrsq hnormle
  have hrq : r ≤ q := by
    by_cases hr0 : r = 0
    · simpa [hr0] using hq
    · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
      nlinarith
  rw [cubicZeroShiftSchurEndpoint_re_eq_shell_sub_predecessorRealEnergy
    p L N x₀ hx₀]
  simpa [q, r] using sub_nonneg.mpr hrq

/-- Headline A4b2a sufficiency theorem: predecessor nonnegativity plus the
canonical one-step domination certificate excludes every safe negative
explicit Schur root. -/
theorem cubicExplicitSchurScalar_ne_zero_of_canonicalOneStepDomination
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hdom : canonicalOneStepDomination p L N)
    (lam : ℝ) (hlam : lam < 0) :
    cubicExplicitSchurScalar p hL N hprev lam hlam ≠ 0 := by
  intro hroot
  obtain ⟨x₀, hx₀⟩ :=
    exists_cubicZeroShift_preimage_of_canonicalOneStepDomination
      p L N hdom
  have hnonneg :=
    cubicZeroShiftSchurEndpoint_re_nonnegative_of_canonicalOneStepDomination
      p hL N hprev hdom x₀ hx₀
  have hneg :=
    cubicZeroShiftSchurEndpoint_re_neg_of_explicit_root
      p hL N hN hprev x₀ hx₀ lam hlam hroot
  linarith

/-- Failure of domination is exactly a negative shell-energy certificate or a
negative one-step determinant witness. -/
theorem not_canonicalOneStepDomination_iff
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    ¬ canonicalOneStepDomination p L N ↔
      cubicShellRealEnergy p L N < 0 ∨
        ∃ w : intrinsicParityPredecessorSubspace p N,
          cubicOneStepDeterminant p L N w < 0 := by
  simp only [canonicalOneStepDomination, not_and_or, not_le, not_forall]

end Zeta23.CCM

#print axioms Zeta23.CCM.cubicOneStepDeterminant_eq_channels
#print axioms Zeta23.CCM.cubicShellCoupling_eq_zero_of_kernel_of_determinant_nonnegative
#print axioms Zeta23.CCM.exists_cubicZeroShift_preimage_of_canonicalOneStepDomination
#print axioms Zeta23.CCM.cubicZeroShiftSchurEndpoint_re_nonnegative_of_canonicalOneStepDomination
#print axioms Zeta23.CCM.cubicExplicitSchurScalar_ne_zero_of_canonicalOneStepDomination
#print axioms Zeta23.CCM.not_canonicalOneStepDomination_iff
