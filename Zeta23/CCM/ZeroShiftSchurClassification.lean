import Zeta23.CCM.GoodSectorKernelAnnihilation
import Zeta23.CCM.CubicExplicitSecular
import Zeta23.CCM.ZeroShiftSchurEndpoint

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: exact zero-shift Schur classification

PR #220 proves that successor-sector goodness annihilates the kernel component
of the actual cubic shell coupling and therefore supplies a zero-shift
preimage.  The older spectral and Schur machinery already gives the converse
bad-sector information: a bad successor has a negative compressed eigenmode,
hence a safe negative explicit Schur root, and every zero-shift preimage then
has strictly negative Schur endpoint.

This module packages those facts into an exact one-step classification.

Under predecessor nonnegativity, a bad successor sector occurs exactly in one
of two zero-shift geometries:

* resonant: the actual cubic shell coupling has nonzero predecessor-kernel
  coordinate;
* regular-negative: the coupling lies in the predecessor range and its
  zero-shift Schur endpoint has negative real part.

Equivalently, a good successor sector is exactly a regular zero-shift sector
with nonnegative endpoint.

Firewalls:
* the kernel coordinate here is the actual shell-coupling coordinate
  `cubicCouplingKernelPart`; it is not the #219 source-correction kernel
  coordinate nor the #220 transported-index correction;
* no determinant domination hypothesis is used;
* no branch is excluded;
* no negative-root exclusion, finite-to-infinite closure, or RH theorem is
  claimed.
-/

/-- The zero-shift trial is nonzero because its shell coordinate is the
nonzero canonical cubic shell. -/
theorem cubicZeroShiftTrialVector_ne_zero
    (p : ReversalParity) (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (x₀ : intrinsicParityPredecessorSubspace p N) :
    cubicZeroShiftTrialVector p L N x₀ ≠ 0 := by
  intro hu
  have hshell :=
    intrinsicShellPart_cubicZeroShiftTrialVector p L N x₀
  rw [hu, map_zero] at hshell
  exact (intrinsicCubicShellPart_ne_zero p N hN) hshell.symm

/-- The actual cubic shell coupling is regular at zero exactly when it has a
zero-shift predecessor preimage. -/
theorem cubicCouplingKernelPart_eq_zero_iff_exists_zeroShiftPreimage
    (p : ReversalParity) (L : ℝ) (N : ℕ) :
    cubicCouplingKernelPart p L N = 0 ↔
      ∃ x₀ : intrinsicParityPredecessorSubspace p N,
        intrinsicPredecessorBlock p L N x₀ =
          intrinsicShellToPredecessor p L N
            (intrinsicCubicShellPart p N) := by
  constructor
  · intro hk
    have hrange :
        intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N) ∈
          LinearMap.range (intrinsicPredecessorBlock p L N) := by
      exact
        (intrinsicPredecessorKernelPart_eq_zero_iff_mem_range
          p L N).1 (by simpa [cubicCouplingKernelPart] using hk)
    exact hrange
  · rintro ⟨x₀, hx₀⟩
    exact cubicCouplingKernelPart_eq_zero_of_preimage p L N x₀ hx₀

/-- Any bad successor sector produces a safe negative explicit cubic Schur
root, provided the predecessor sector is nonnegative. -/
theorem exists_negative_cubicExplicitSchurRoot_of_parityBad
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hbad : ParityBad p L (N + 1)) :
    ∃ lam : ℝ, ∃ hlam : lam < 0,
      cubicExplicitSchurScalar p hL N hprev lam hlam = 0 := by
  obtain ⟨lam, hlam, v, hvne, hveig⟩ :=
    exists_negative_eigenmode_of_parityBad hbad
  refine ⟨lam, hlam, ?_⟩
  exact
    (cubicExplicitSchurScalar_eq_zero_iff_exists_eigenmode
      p hL N hN hprev lam hlam).2
      ⟨v, hvne, hveig⟩

/-- In the regular zero-shift branch, successor badness forces the canonical
zero-shift Schur endpoint strictly negative. -/
theorem cubicZeroShiftSchurEndpoint_re_neg_of_parityBad_of_preimage
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (hbad : ParityBad p L (N + 1))
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ :
      intrinsicPredecessorBlock p L N x₀ =
        intrinsicShellToPredecessor p L N
          (intrinsicCubicShellPart p N)) :
    Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) < 0 := by
  obtain ⟨lam, hlam, hroot⟩ :=
    exists_negative_cubicExplicitSchurRoot_of_parityBad
      p hL N hN hprev hbad
  exact
    cubicZeroShiftSchurEndpoint_re_neg_of_explicit_root
      p hL N hN hprev x₀ hx₀ lam hlam hroot

/-- A nonzero kernel coordinate of the actual shell coupling forces successor
badness.  This is the contrapositive of the #220 good-sector annihilation
theorem. -/
theorem parityBad_of_cubicCouplingKernelPart_ne_zero
    (p : ReversalParity) (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (hk : cubicCouplingKernelPart p L N ≠ 0) :
    ParityBad p L (N + 1) := by
  by_contra hgood
  exact hk
    (cubicCouplingKernelPart_eq_zero_of_not_parityBad
      p L N hN hgood)

/-- A regular zero-shift preimage with negative endpoint is itself a negative
successor direction and therefore forces `ParityBad`. -/
theorem parityBad_of_cubicZeroShiftSchurEndpoint_re_neg
    (p : ReversalParity) (L : ℝ) (N : ℕ) (hN : 1 ≤ N)
    (x₀ : intrinsicParityPredecessorSubspace p N)
    (hx₀ :
      intrinsicPredecessorBlock p L N x₀ =
        intrinsicShellToPredecessor p L N
          (intrinsicCubicShellPart p N))
    (hneg :
      Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) < 0) :
    ParityBad p L (N + 1) := by
  let u := cubicZeroShiftTrialVector p L N x₀
  have hune : u ≠ 0 := by
    simpa [u] using cubicZeroShiftTrialVector_ne_zero p L N hN x₀
  have henergy :
      inner ℂ
          (parityCompressedCanonical p L (N + 1) u) u =
        cubicZeroShiftSchurEndpoint p L N x₀ := by
    simpa [u] using
      inner_parityCompressedCanonical_cubicZeroShiftTrialVector_self
        p L N x₀ hx₀
  have henergyNeg :
      Complex.re
        (inner ℂ
          (parityCompressedCanonical p L (N + 1) u) u) < 0 := by
    rw [henergy]
    exact hneg
  exact parityBad_of_negative_compressed_direction hune henergyNeg

/-- Exact good-sector zero-shift classification: goodness is equivalent to the
existence of a regular zero-shift preimage with nonnegative Schur endpoint. -/
theorem not_parityBad_iff_exists_cubicZeroShiftPreimage_endpoint_nonnegative
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x)) :
    (¬ ParityBad p L (N + 1)) ↔
      ∃ x₀ : intrinsicParityPredecessorSubspace p N,
        intrinsicPredecessorBlock p L N x₀ =
            intrinsicShellToPredecessor p L N
              (intrinsicCubicShellPart p N) ∧
        0 ≤ Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) := by
  constructor
  · intro hgood
    obtain ⟨x₀, hx₀⟩ :=
      exists_cubicZeroShift_preimage_of_not_parityBad
        p L N hN hgood
    have hnonneg :=
      re_inner_parityCompressedCanonical_nonnegative_of_not_parityBad
        hgood (cubicZeroShiftTrialVector p L N x₀)
    have henergy :=
      inner_parityCompressedCanonical_cubicZeroShiftTrialVector_self
        p L N x₀ hx₀
    refine ⟨x₀, hx₀, ?_⟩
    rw [henergy] at hnonneg
    exact hnonneg
  · rintro ⟨x₀, hx₀, hnonneg⟩ hbad
    have hneg :=
      cubicZeroShiftSchurEndpoint_re_neg_of_parityBad_of_preimage
        p hL N hN hprev hbad x₀ hx₀
    linarith

/-- Exact bad-sector zero-shift classification.  Every bad successor is either
resonant in the actual shell coupling or regular with a strictly negative
zero-shift Schur endpoint. -/
theorem parityBad_iff_cubicCouplingKernelPart_ne_zero_or_exists_zeroShiftEndpoint_neg
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x)) :
    ParityBad p L (N + 1) ↔
      cubicCouplingKernelPart p L N ≠ 0 ∨
        ∃ x₀ : intrinsicParityPredecessorSubspace p N,
          intrinsicPredecessorBlock p L N x₀ =
              intrinsicShellToPredecessor p L N
                (intrinsicCubicShellPart p N) ∧
          Complex.re (cubicZeroShiftSchurEndpoint p L N x₀) < 0 := by
  constructor
  · intro hbad
    by_cases hk : cubicCouplingKernelPart p L N = 0
    · right
      obtain ⟨x₀, hx₀⟩ :=
        (cubicCouplingKernelPart_eq_zero_iff_exists_zeroShiftPreimage
          p L N).1 hk
      exact
        ⟨x₀, hx₀,
          cubicZeroShiftSchurEndpoint_re_neg_of_parityBad_of_preimage
            p hL N hN hprev hbad x₀ hx₀⟩
    · exact Or.inl hk
  · rintro (hk | ⟨x₀, hx₀, hneg⟩)
    · exact parityBad_of_cubicCouplingKernelPart_ne_zero p L N hN hk
    · exact
        parityBad_of_cubicZeroShiftSchurEndpoint_re_neg
          p L N hN x₀ hx₀ hneg

end Zeta23.CCM

#print axioms Zeta23.CCM.cubicCouplingKernelPart_eq_zero_iff_exists_zeroShiftPreimage
#print axioms Zeta23.CCM.not_parityBad_iff_exists_cubicZeroShiftPreimage_endpoint_nonnegative
#print axioms Zeta23.CCM.parityBad_iff_cubicCouplingKernelPart_ne_zero_or_exists_zeroShiftEndpoint_neg
