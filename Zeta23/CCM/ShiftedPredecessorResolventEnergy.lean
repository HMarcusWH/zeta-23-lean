import Zeta23.CCM.CanonicalOneStepDomination
import Zeta23.CCM.CubicSecularMetric

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: shifted predecessor resolvent energy

This module connects the existing safe negative-shift resolvent to the existing
real predecessor-energy wrapper.

For `R = (A - lam I)⁻¹` and any predecessor source `b`, the inverse equation

  (A - lam I) (R b) = b

gives the exact real-energy identity

  E_A(R b) = Re <R b,b> + lam * ||R b||^2.

Since `lam < 0`, this immediately yields

  E_A(R b) <= Re <R b,b>.

No sign of a mixed pairing is asserted and no zero-shift inverse is used.
-/

/-- Exact predecessor energy of a safe shifted-resolvent vector. -/
theorem intrinsicPredecessorRealEnergy_shiftedIntrinsicPredecessorResolvent_eq
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (b : intrinsicParityPredecessorSubspace p N) :
    let R :=
      shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
    intrinsicPredecessorRealEnergy p L N (R b) =
      Complex.re
          (inner ℂ
            ((R b : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (b : euclideanParityBoundaryFlatSubspace p (N + 1))) +
        lam * ‖R b‖ ^ 2 := by
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  let w : intrinsicParityPredecessorSubspace p N := R b
  change
    intrinsicPredecessorRealEnergy p L N w =
      Complex.re
          (inner ℂ
            (w : euclideanParityBoundaryFlatSubspace p (N + 1))
            (b : euclideanParityBoundaryFlatSubspace p (N + 1))) +
        lam * ‖w‖ ^ 2
  have hshift :
      shiftedIntrinsicPredecessorBlock p L N lam w = b := by
    simpa [w, R] using
      shiftedIntrinsicPredecessorBlock_resolvent_apply
        p hL N hprev lam hlam b
  have hAw :
      intrinsicPredecessorBlock p L N w =
        b + (lam : ℂ) • w := by
    change
      intrinsicPredecessorBlock p L N w - (lam : ℂ) • w = b at hshift
    exact (sub_eq_iff_eq_add).mp hshift
  have hAwAmbient :
      ((intrinsicPredecessorBlock p L N w :
          intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) =
      (b : euclideanParityBoundaryFlatSubspace p (N + 1)) +
        (lam : ℂ) •
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simpa using congrArg
      (fun z : intrinsicParityPredecessorSubspace p N =>
        (z : euclideanParityBoundaryFlatSubspace p (N + 1))) hAw
  have hrealSymm :
      Complex.re
          (inner ℂ
            (b : euclideanParityBoundaryFlatSubspace p (N + 1))
            (w : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        Complex.re
          (inner ℂ
            (w : euclideanParityBoundaryFlatSubspace p (N + 1))
            (b : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
    exact inner_re_symm (𝕜 := ℂ)
      (b : euclideanParityBoundaryFlatSubspace p (N + 1))
      (w : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hlamInner :
      inner ℂ
          ((lam : ℂ) •
            (w : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        lam •
          inner ℂ
            (w : euclideanParityBoundaryFlatSubspace p (N + 1))
            (w : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    exact inner_smul_real_left (𝕜 := ℂ)
      (w : euclideanParityBoundaryFlatSubspace p (N + 1))
      (w : euclideanParityBoundaryFlatSubspace p (N + 1)) lam
  have hnorm :
      Complex.re
          (inner ℂ
            (w : euclideanParityBoundaryFlatSubspace p (N + 1))
            (w : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        ‖w‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      (norm_sq_eq_re_inner (𝕜 := ℂ)
        (w : euclideanParityBoundaryFlatSubspace p (N + 1))).symm
  unfold intrinsicPredecessorRealEnergy
  rw [hAwAmbient, inner_add_left, Complex.add_re, hlamInner]
  simp only [Complex.smul_re, smul_eq_mul]
  rw [hrealSymm, hnorm]

/-- At a negative shift, predecessor energy of a resolvent vector is at most
the real part of its resolvent quadratic pairing. -/
theorem intrinsicPredecessorRealEnergy_shiftedIntrinsicPredecessorResolvent_le_re_inner
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (b : intrinsicParityPredecessorSubspace p N) :
    let R :=
      shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
    intrinsicPredecessorRealEnergy p L N (R b) ≤
      Complex.re
        (inner ℂ
          ((R b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have hEq :=
    intrinsicPredecessorRealEnergy_shiftedIntrinsicPredecessorResolvent_eq
      p hL N hprev lam hlam b
  change
    intrinsicPredecessorRealEnergy p L N (R b) =
      Complex.re
          (inner ℂ
            ((R b : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (b : euclideanParityBoundaryFlatSubspace p (N + 1))) +
        lam * ‖R b‖ ^ 2 at hEq
  rw [hEq]
  have hshiftTerm : lam * ‖R b‖ ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (le_of_lt hlam) (sq_nonneg _)
  linarith

end Zeta23.CCM

#print axioms Zeta23.CCM.intrinsicPredecessorRealEnergy_shiftedIntrinsicPredecessorResolvent_eq
#print axioms Zeta23.CCM.intrinsicPredecessorRealEnergy_shiftedIntrinsicPredecessorResolvent_le_re_inner
