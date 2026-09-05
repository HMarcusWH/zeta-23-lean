import Zeta23.CCM.CubicNormalizedSchur

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E3-A: exact canonical cubic secular equation

PR #113 proves that at a negative first-bad spectral parameter `lam < 0`, the
predecessor block `A - lam I` is invertible. PR #118 canonically fixes the
one-dimensional successor shell by the nonzero cubic shell vector and provides
a faithful scalar coordinate on the successor modulo the predecessor.

This module combines those two facts in the converse direction. For each safe
negative shift, we reconstruct the unique successor vector whose shell part is
the canonical cubic shell vector and whose predecessor part solves the shifted
predecessor equation. Its eigenvalue residual automatically has zero
predecessor coordinate. Consequently the #118 quotient coordinate of that
residual is an exact secular scalar: it vanishes if and only if the whole
residual vanishes, equivalently if and only if the canonical reconstructed
vector is a genuine eigenmode. Finally, any genuine eigenmode at the same
negative shift canonically normalizes to this reconstructed vector.

Firewalls:
* the secular scalar is the #118 quotient coordinate of the full residual, not
  merely an inner product whose vanishing would not imply residual vanishing;
* only `A - lam I` for `lam < 0` is inverted;
* no predecessor or shell invariance is assumed;
* no unitary/isometric parity transport is asserted;
* no sign, monotonicity, deformation budget, positivity closure, or RH theorem
  is claimed.
-/

/-- The shifted predecessor resolvent is also a right inverse. This is the
compiler-facing form of `E (E.symm w) = w` for the canonical negative-shift
linear equivalence. -/
theorem shiftedIntrinsicPredecessorBlock_resolvent_apply
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (w : intrinsicParityPredecessorSubspace p N) :
    shiftedIntrinsicPredecessorBlock p L N lam
        (shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam w) = w := by
  let E := shiftedIntrinsicPredecessorEquiv p hL N hprev lam hlam
  change E (E.symm w) = w
  exact E.apply_symm_apply w

/-- The canonical E3-A trial vector at a safe negative shift. Its shell part is
the #118 cubic shell vector, while its predecessor part is the unique solution
of `(A - lam I) w = -B c`. -/
def cubicSecularTrialVector
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    euclideanParityBoundaryFlatSubspace p (N + 1) :=
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  ((- R b : intrinsicParityPredecessorSubspace p N) :
      euclideanParityBoundaryFlatSubspace p (N + 1)) +
    (c : euclideanParityBoundaryFlatSubspace p (N + 1))

/-- The predecessor coordinate of the canonical trial vector is exactly the
shifted-resolvent reconstruction. -/
theorem intrinsicPredecessorPart_cubicSecularTrialVector
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    intrinsicPredecessorPart p N
        (cubicSecularTrialVector p hL N hprev lam hlam) =
      - shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
          (intrinsicShellToPredecessor p L N (intrinsicCubicShellPart p N)) := by
  simp [cubicSecularTrialVector, intrinsicPredecessorPart]

/-- The shell coordinate of the canonical trial vector is exactly the canonical
cubic shell vector. -/
theorem intrinsicShellPart_cubicSecularTrialVector
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    intrinsicShellPart p N
        (cubicSecularTrialVector p hL N hprev lam hlam) =
      intrinsicCubicShellPart p N := by
  simp [cubicSecularTrialVector, intrinsicShellPart]

/-- The canonical trial vector has quotient coordinate one. -/
theorem intrinsicCubicQuotientCoordinate_cubicSecularTrialVector
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    intrinsicCubicQuotientCoordinate p N
        (cubicSecularTrialVector p hL N hprev lam hlam) = 1 := by
  change
    intrinsicCubicShellCoordinate p N
      (intrinsicShellPart p N
        (cubicSecularTrialVector p hL N hprev lam hlam)) = 1
  rw [intrinsicShellPart_cubicSecularTrialVector]
  exact intrinsicCubicShellCoordinate_cubic p N hN

/-- In particular, the canonical trial vector is never zero once the cubic
shell coordinate is faithful. -/
theorem cubicSecularTrialVector_ne_zero
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicSecularTrialVector p hL N hprev lam hlam ≠ 0 := by
  intro hzero
  have hcoord :=
    intrinsicCubicQuotientCoordinate_cubicSecularTrialVector
      p hL N hN hprev lam hlam
  rw [hzero, map_zero] at hcoord
  exact zero_ne_one hcoord

/-- Full successor eigenvalue residual of the canonical E3-A trial vector. -/
def cubicSecularResidual
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    euclideanParityBoundaryFlatSubspace p (N + 1) :=
  parityCompressedCanonical p L (N + 1)
      (cubicSecularTrialVector p hL N hprev lam hlam) -
    (lam : ℂ) • cubicSecularTrialVector p hL N hprev lam hlam

/-- The canonical residual has no predecessor component. This is the exact
block-algebra fact that makes a one-dimensional scalar test sufficient. -/
theorem intrinsicPredecessorPart_cubicSecularResidual_eq_zero
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    intrinsicPredecessorPart p N
        (cubicSecularResidual p hL N hprev lam hlam) = 0 := by
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  let w : intrinsicParityPredecessorSubspace p N := - R b
  let u := cubicSecularTrialVector p hL N hprev lam hlam
  have huPred : intrinsicPredecessorPart p N u = w := by
    simpa [u, w, R, b, c] using
      intrinsicPredecessorPart_cubicSecularTrialVector
        p hL N hprev lam hlam
  have huShell : intrinsicShellPart p N u = c := by
    simpa [u, c] using
      intrinsicShellPart_cubicSecularTrialVector
        p hL N hprev lam hlam
  have hTuPred :
      intrinsicPredecessorPart p N
          (parityCompressedCanonical p L (N + 1) u) =
        intrinsicPredecessorBlock p L N w + b := by
    have hrec := intrinsicPredecessorPart_add_shellPart p N u
    calc
      intrinsicPredecessorPart p N
          (parityCompressedCanonical p L (N + 1) u) =
        intrinsicPredecessorPart p N
          (parityCompressedCanonical p L (N + 1)
            (((w : intrinsicParityPredecessorSubspace p N) :
                euclideanParityBoundaryFlatSubspace p (N + 1)) +
              (c : euclideanParityBoundaryFlatSubspace p (N + 1)))) := by
                rw [← huPred, ← huShell]
                rw [hrec]
      _ = intrinsicPredecessorBlock p L N w + b := by
        simp [intrinsicPredecessorBlock, intrinsicShellToPredecessor, b,
          map_add]
  have hRright :
      shiftedIntrinsicPredecessorBlock p L N lam (R b) = b := by
    simpa [R] using
      shiftedIntrinsicPredecessorBlock_resolvent_apply
        p hL N hprev lam hlam b
  have hshiftw :
      shiftedIntrinsicPredecessorBlock p L N lam w = -b := by
    rw [show w = - R b by rfl, map_neg, hRright]
  have hshiftw' :
      intrinsicPredecessorBlock p L N w - (lam : ℂ) • w = -b := by
    simpa [shiftedIntrinsicPredecessorBlock] using hshiftw
  change
    intrinsicPredecessorPart p N
      (parityCompressedCanonical p L (N + 1) u - (lam : ℂ) • u) = 0
  rw [map_sub, hTuPred, map_smul, huPred]
  rw [← hshiftw']
  abel

/-- E3-A secular scalar: the canonical #118 quotient coordinate of the full
canonical residual. This is deliberately not defined as only a scalar inner
product. -/
def cubicSecularScalar
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) : ℂ :=
  intrinsicCubicQuotientCoordinate p N
    (cubicSecularResidual p hL N hprev lam hlam)

/-- Exact scalarization: because the canonical residual already has zero
predecessor coordinate, its cubic quotient coordinate vanishes exactly when the
whole residual vanishes. -/
theorem cubicSecularScalar_eq_zero_iff_residual_eq_zero
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicSecularScalar p hL N hprev lam hlam = 0 ↔
      cubicSecularResidual p hL N hprev lam hlam = 0 := by
  let r := cubicSecularResidual p hL N hprev lam hlam
  have hrPred : intrinsicPredecessorPart p N r = 0 := by
    simpa [r] using
      intrinsicPredecessorPart_cubicSecularResidual_eq_zero
        p hL N hprev lam hlam
  constructor
  · intro hscalar
    have hscoord :
        intrinsicCubicShellCoordinate p N (intrinsicShellPart p N r) = 0 := by
      simpa [cubicSecularScalar, intrinsicCubicQuotientCoordinate, r] using
        hscalar
    have hrShell : intrinsicShellPart p N r = 0 :=
      (intrinsicCubicShellCoordinate_eq_zero_iff p N hN).mp hscoord
    have hrec := intrinsicPredecessorPart_add_shellPart p N r
    rw [hrPred, hrShell] at hrec
    simpa using hrec.symm
  · intro hr
    simpa [cubicSecularScalar, r, hr]

/-- The secular root is exactly the eigenvalue equation for the canonical trial
vector. -/
theorem cubicSecularScalar_eq_zero_iff_trial_eigenmode
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicSecularScalar p hL N hprev lam hlam = 0 ↔
      parityCompressedCanonical p L (N + 1)
          (cubicSecularTrialVector p hL N hprev lam hlam) =
        (lam : ℂ) • cubicSecularTrialVector p hL N hprev lam hlam := by
  rw [cubicSecularScalar_eq_zero_iff_residual_eq_zero
    p hL N hN hprev lam hlam]
  simp only [cubicSecularResidual, sub_eq_zero]

/-- Any genuine negative eigenmode canonically normalizes to the E3-A trial
vector. This is the converse half missing from the one-way Schur identity. -/
theorem cubicNormalizedSuccessorVector_eq_cubicSecularTrialVector
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    {lam : ℝ} (hlam : lam < 0)
    {v : euclideanParityBoundaryFlatSubspace p (N + 1)}
    (hvne : v ≠ 0)
    (hveig :
      parityCompressedCanonical p L (N + 1) v = (lam : ℂ) • v) :
    cubicNormalizedSuccessorVector p N v =
      cubicSecularTrialVector p hL N hprev lam hlam := by
  let vhat := cubicNormalizedSuccessorVector p N v
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  have hκ :=
    negative_eigenmode_intrinsicCubicQuotientCoordinate_ne_zero
      p hL N hN hprev hlam hvne hveig
  have hveigHat :
      parityCompressedCanonical p L (N + 1) vhat = (lam : ℂ) • vhat := by
    simpa [vhat] using
      cubicNormalizedSuccessorVector_eigenmode p L N hveig
  have hshellHat : intrinsicShellPart p N vhat = c := by
    simpa [vhat, c] using
      intrinsicShellPart_cubicNormalizedSuccessorVector p N hN hκ
  have hpredHat : intrinsicPredecessorPart p N vhat = - R b := by
    have hpred :=
      eigenmode_predecessorPart_eq_neg_resolvent_shell
        p hL N hprev hlam hveigHat
    simpa [R, b, hshellHat] using hpred
  have hrec := intrinsicPredecessorPart_add_shellPart p N vhat
  rw [hpredHat, hshellHat] at hrec
  symm
  simpa [cubicSecularTrialVector, R, b, c, vhat] using hrec

/-- Exact E3-A spectral criterion at every safe negative shift: the canonical
secular scalar has a root exactly when the successor parity compression has a
nonzero eigenmode at that shift. -/
theorem cubicSecularScalar_eq_zero_iff_exists_eigenmode
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicSecularScalar p hL N hprev lam hlam = 0 ↔
      ∃ v : euclideanParityBoundaryFlatSubspace p (N + 1),
        v ≠ 0 ∧
          parityCompressedCanonical p L (N + 1) v = (lam : ℂ) • v := by
  constructor
  · intro hroot
    refine ⟨cubicSecularTrialVector p hL N hprev lam hlam,
      cubicSecularTrialVector_ne_zero p hL N hN hprev lam hlam, ?_⟩
    exact (cubicSecularScalar_eq_zero_iff_trial_eigenmode
      p hL N hN hprev lam hlam).mp hroot
  · rintro ⟨v, hvne, hveig⟩
    have hnorm :
        cubicNormalizedSuccessorVector p N v =
          cubicSecularTrialVector p hL N hprev lam hlam :=
      cubicNormalizedSuccessorVector_eq_cubicSecularTrialVector
        p hL N hN hprev hlam hvne hveig
    have hveigNorm := cubicNormalizedSuccessorVector_eigenmode p L N hveig
    have htrialEig :
        parityCompressedCanonical p L (N + 1)
            (cubicSecularTrialVector p hL N hprev lam hlam) =
          (lam : ℂ) • cubicSecularTrialVector p hL N hprev lam hlam := by
      simpa [hnorm] using hveigNorm
    exact (cubicSecularScalar_eq_zero_iff_trial_eigenmode
      p hL N hN hprev lam hlam).mpr htrialEig

end Zeta23.CCM

#print axioms Zeta23.CCM.shiftedIntrinsicPredecessorBlock_resolvent_apply
#print axioms Zeta23.CCM.cubicSecularScalar_eq_zero_iff_residual_eq_zero
#print axioms Zeta23.CCM.cubicSecularScalar_eq_zero_iff_trial_eigenmode
#print axioms Zeta23.CCM.cubicSecularScalar_eq_zero_iff_exists_eigenmode
