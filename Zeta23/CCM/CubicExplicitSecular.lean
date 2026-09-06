import Zeta23.CCM.CubicSecularEquation

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E3-B2: explicit cubic secular bridge

PR #119 defines the exact secular scalar as the canonical cubic quotient
coordinate of the full residual of the shifted-resolvent trial vector. PR #113
already supplies the corresponding basis-free Schur expression for genuine
negative eigenmodes.

This module identifies those two scalarizations pointwise at every safe
negative shift. The repository uses Mathlib's complex inner-product convention,
linear in the second argument, so the quotient-coordinate scalar matches the
complex conjugate of the #113-oriented Schur expression, normalized by the
nonzero cubic shell self-inner value. Conjugation does not change the zero set,
so the explicit Schur scalar is an exact secular equation.

Firewalls:
* the #113 Schur orientation is preserved rather than redefined for cosmetics;
* no resolvent symmetry or realness is assumed;
* no sign, monotonicity, root-count, root-exclusion, positivity, or RH theorem
  is claimed;
* only `A - lam I` for `lam < 0` is used; there is no inverse at zero.
-/

/-- The explicit #113-oriented Schur scalar evaluated on the canonical cubic
shell direction. This is a pointwise function of every safe negative shift. -/
def cubicExplicitSchurScalar
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) : ℂ :=
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  inner ℂ
      (parityCompressedCanonical p L (N + 1)
        (c : euclideanParityBoundaryFlatSubspace p (N + 1)))
      (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
    (lam : ℂ) *
      inner ℂ
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
        (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
    inner ℂ
      ((R b : intrinsicParityPredecessorSubspace p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1))
      (b : euclideanParityBoundaryFlatSubspace p (N + 1))

/-- The cubic shell self-inner value is nonzero once the canonical cubic shell
coordinate is faithful. -/
theorem inner_intrinsicCubicShellPart_self_ne_zero
    (p : ReversalParity) (N : ℕ) (hN : 1 ≤ N) :
    inner ℂ
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1))
        (intrinsicCubicShellPart p N :
          euclideanParityBoundaryFlatSubspace p (N + 1)) ≠ 0 := by
  have hc : intrinsicCubicShellPart p N ≠ 0 :=
    intrinsicCubicShellPart_ne_zero p N hN
  have hcCarrier :
      (intrinsicCubicShellPart p N :
        euclideanParityBoundaryFlatSubspace p (N + 1)) ≠ 0 := by
    intro hzero
    apply hc
    apply Subtype.ext
    exact hzero
  intro hinner
  apply hcCarrier
  exact inner_self_eq_zero.mp hinner

/-- Exact E3-B2 pointwise bridge. Because Mathlib's complex inner product is
linear in the second argument, the canonical quotient-coordinate numerator is
the conjugate of the #113-oriented explicit Schur scalar. -/
theorem cubicSecularScalar_eq_star_cubicExplicitSchurScalar_div
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicSecularScalar p hL N hprev lam hlam =
      star (cubicExplicitSchurScalar p hL N hprev lam hlam) /
        inner ℂ
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1))
          (intrinsicCubicShellPart p N :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
  let c := intrinsicCubicShellPart p N
  let b := intrinsicShellToPredecessor p L N c
  let R := shiftedIntrinsicPredecessorResolvent p hL N hprev lam hlam
  let w : intrinsicParityPredecessorSubspace p N := - R b
  let u := cubicSecularTrialVector p hL N hprev lam hlam
  let r := cubicSecularResidual p hL N hprev lam hlam
  have hu :
      u =
        (w : euclideanParityBoundaryFlatSubspace p (N + 1)) +
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    rfl
  have hr :
      r =
        parityCompressedCanonical p L (N + 1)
            ((w : euclideanParityBoundaryFlatSubspace p (N + 1)) +
              (c : euclideanParityBoundaryFlatSubspace p (N + 1))) -
          (lam : ℂ) •
            ((w : euclideanParityBoundaryFlatSubspace p (N + 1)) +
              (c : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
    simp only [r, cubicSecularResidual, hu]
  have hcw :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
    exact inner_intrinsicShell_predecessor_eq_zero p N c w
  have hsym :
      inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (w : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) := by
    exact parityCompressedCanonical_isSymmetric p L (N + 1)
      (w : euclideanParityBoundaryFlatSubspace p (N + 1))
      (c : euclideanParityBoundaryFlatSubspace p (N + 1))
  have hBT :
      inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))
          (parityCompressedCanonical p L (N + 1)
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    let y := parityCompressedCanonical p L (N + 1)
      (c : euclideanParityBoundaryFlatSubspace p (N + 1))
    have hyrec := intrinsicPredecessorPart_add_shellPart p N y
    have hort := inner_intrinsicPredecessor_shell_eq_zero
      p N w (intrinsicShellPart p N y)
    change
      inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1)) y =
        inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1))
    rw [← hyrec, inner_add_right, hort, add_zero]
    rfl
  have hTwc :
      inner ℂ
          (parityCompressedCanonical p L (N + 1)
            (w : euclideanParityBoundaryFlatSubspace p (N + 1)))
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
        inner ℂ
          (w : euclideanParityBoundaryFlatSubspace p (N + 1))
          (b : euclideanParityBoundaryFlatSubspace p (N + 1)) :=
    hsym.trans hBT
  have hcrossStar := congrArg star hTwc
  have hcross :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1))
          (parityCompressedCanonical p L (N + 1)
            (w : euclideanParityBoundaryFlatSubspace p (N + 1))) =
        - inner ℂ
          (b : euclideanParityBoundaryFlatSubspace p (N + 1))
          ((R b : intrinsicParityPredecessorSubspace p N) :
            euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simpa [w] using hcrossStar
  have hinnerResidual :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) r =
        inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            (parityCompressedCanonical p L (N + 1)
              (c : euclideanParityBoundaryFlatSubspace p (N + 1))) -
          (lam : ℂ) *
            inner ℂ
              (c : euclideanParityBoundaryFlatSubspace p (N + 1))
              (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
          inner ℂ
            (b : euclideanParityBoundaryFlatSubspace p (N + 1))
            ((R b : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    rw [hr, inner_sub_right, map_add, inner_add_right, inner_smul_right,
      inner_add_right, hcross, hcw]
    ring
  have hstarExplicit :
      star (cubicExplicitSchurScalar p hL N hprev lam hlam) =
        inner ℂ
            (c : euclideanParityBoundaryFlatSubspace p (N + 1))
            (parityCompressedCanonical p L (N + 1)
              (c : euclideanParityBoundaryFlatSubspace p (N + 1))) -
          (lam : ℂ) *
            inner ℂ
              (c : euclideanParityBoundaryFlatSubspace p (N + 1))
              (c : euclideanParityBoundaryFlatSubspace p (N + 1)) -
          inner ℂ
            (b : euclideanParityBoundaryFlatSubspace p (N + 1))
            ((R b : intrinsicParityPredecessorSubspace p N) :
              euclideanParityBoundaryFlatSubspace p (N + 1)) := by
    simp [cubicExplicitSchurScalar, c, b, R]
  have hnum :
      inner ℂ
          (c : euclideanParityBoundaryFlatSubspace p (N + 1)) r =
        star (cubicExplicitSchurScalar p hL N hprev lam hlam) :=
    hinnerResidual.trans hstarExplicit.symm
  have hrPred : intrinsicPredecessorPart p N r = 0 := by
    simpa [r] using
      intrinsicPredecessorPart_cubicSecularResidual_eq_zero
        p hL N hprev lam hlam
  have hrRec := intrinsicPredecessorPart_add_shellPart p N r
  have hrShell :
      ((intrinsicShellPart p N r : intrinsicParitySuccShell p N) :
        euclideanParityBoundaryFlatSubspace p (N + 1)) = r := by
    rw [hrPred] at hrRec
    simpa using hrRec
  change
    inner ℂ
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
        ((intrinsicShellPart p N r : intrinsicParitySuccShell p N) :
          euclideanParityBoundaryFlatSubspace p (N + 1)) /
      inner ℂ
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
        (c : euclideanParityBoundaryFlatSubspace p (N + 1)) =
    star (cubicExplicitSchurScalar p hL N hprev lam hlam) /
      inner ℂ
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
        (c : euclideanParityBoundaryFlatSubspace p (N + 1))
  rw [hrShell, hnum]

/-- The explicit #113-oriented Schur scalar and the exact #119 quotient secular
scalar have exactly the same zero set at every safe negative shift. -/
theorem cubicExplicitSchurScalar_eq_zero_iff_cubicSecularScalar_eq_zero
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicExplicitSchurScalar p hL N hprev lam hlam = 0 ↔
      cubicSecularScalar p hL N hprev lam hlam = 0 := by
  have hbridge :=
    cubicSecularScalar_eq_star_cubicExplicitSchurScalar_div
      p hL N hN hprev lam hlam
  have hcc := inner_intrinsicCubicShellPart_self_ne_zero p N hN
  constructor
  · intro hS
    rw [hS] at hbridge
    simpa using hbridge
  · intro hF
    rw [hF] at hbridge
    have hstar : star (cubicExplicitSchurScalar p hL N hprev lam hlam) = 0 := by
      rcases div_eq_zero_iff.mp hbridge.symm with hstar | hden
      · exact hstar
      · exact (hcc hden).elim
    have hback := congrArg star hstar
    simpa using hback

/-- The explicit Schur scalar vanishes exactly when the canonical #119 trial
vector is a genuine eigenmode. -/
theorem cubicExplicitSchurScalar_eq_zero_iff_trial_eigenmode
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicExplicitSchurScalar p hL N hprev lam hlam = 0 ↔
      parityCompressedCanonical p L (N + 1)
          (cubicSecularTrialVector p hL N hprev lam hlam) =
        (lam : ℂ) • cubicSecularTrialVector p hL N hprev lam hlam := by
  rw [cubicExplicitSchurScalar_eq_zero_iff_cubicSecularScalar_eq_zero
    p hL N hN hprev lam hlam]
  exact cubicSecularScalar_eq_zero_iff_trial_eigenmode
    p hL N hN hprev lam hlam

/-- Exact E3-B2 spectral criterion: the old #113-oriented explicit Schur scalar
is now a two-way secular equation, not only a necessary identity. -/
theorem cubicExplicitSchurScalar_eq_zero_iff_exists_eigenmode
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    cubicExplicitSchurScalar p hL N hprev lam hlam = 0 ↔
      ∃ v : euclideanParityBoundaryFlatSubspace p (N + 1),
        v ≠ 0 ∧
          parityCompressedCanonical p L (N + 1) v = (lam : ℂ) • v := by
  rw [cubicExplicitSchurScalar_eq_zero_iff_cubicSecularScalar_eq_zero
    p hL N hN hprev lam hlam]
  exact cubicSecularScalar_eq_zero_iff_exists_eigenmode
    p hL N hN hprev lam hlam

end Zeta23.CCM

#print axioms Zeta23.CCM.cubicSecularScalar_eq_star_cubicExplicitSchurScalar_div
#print axioms Zeta23.CCM.cubicExplicitSchurScalar_eq_zero_iff_cubicSecularScalar_eq_zero
#print axioms Zeta23.CCM.cubicExplicitSchurScalar_eq_zero_iff_exists_eigenmode