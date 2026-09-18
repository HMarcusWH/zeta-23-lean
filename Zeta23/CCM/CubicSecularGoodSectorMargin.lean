import Zeta23.CCM.ParitySourceMomentFourRigidity
import Zeta23.CCM.CrossParityQuotientTransport

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: good-sector secular margin

At every safe negative shift the canonical secular residual is exactly the
secular scalar times the canonical shell vector. Pairing that identity with
the canonical trial converts successor-sector nonnegativity into a quantitative
lower bound on the shell-scaled real part of the secular scalar.

This module is generic in parity. It does not assume a secular root, does not
use cross-parity transport, and does not exclude any bad branch. No RH theorem
is claimed.
-/

/-- Exact self-energy identity for the canonical secular trial. -/
theorem re_inner_cubicSecularTrialVector_eq
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0) :
    let u := cubicSecularTrialVector p hL N hprev lam hlam
    let c : euclideanParityBoundaryFlatSubspace p (N + 1) :=
      intrinsicCubicShellPart p N
    let F := cubicSecularScalar p hL N hprev lam hlam
    Complex.re
        (inner ℂ (parityCompressedCanonical p L (N + 1) u) u) =
      lam * ‖u‖ ^ 2 +
        Complex.re (star F * inner ℂ c c) := by
  dsimp
  let u := cubicSecularTrialVector p hL N hprev lam hlam
  let c : euclideanParityBoundaryFlatSubspace p (N + 1) :=
    intrinsicCubicShellPart p N
  let F := cubicSecularScalar p hL N hprev lam hlam
  have hres :=
    cubicSecularResidual_eq_scalar_smul_intrinsicCubicShellPart
      p hL N hN hprev lam hlam
  change
    parityCompressedCanonical p L (N + 1) u - (lam : ℂ) • u =
      F • c at hres
  have hTu :
      parityCompressedCanonical p L (N + 1) u =
        F • c + (lam : ℂ) • u :=
    (sub_eq_iff_eq_add).mp hres
  have hcu : inner ℂ c u = inner ℂ c c := by
    let w := intrinsicPredecessorPart p N u
    have hrec := intrinsicPredecessorPart_add_shellPart p N u
    have hs : intrinsicShellPart p N u = intrinsicCubicShellPart p N := by
      simpa [u] using
        intrinsicShellPart_cubicSecularTrialVector
          p hL N hprev lam hlam
    have hort :
        inner ℂ c
            (w : euclideanParityBoundaryFlatSubspace p (N + 1)) = 0 := by
      exact inner_intrinsicShell_predecessor_eq_zero p N
        (intrinsicCubicShellPart p N) w
    calc
      inner ℂ c u =
          inner ℂ c
            ((w : euclideanParityBoundaryFlatSubspace p (N + 1)) +
              (intrinsicShellPart p N u :
                euclideanParityBoundaryFlatSubspace p (N + 1))) := by
            rw [hrec]
      _ =
          inner ℂ c
              (w : euclideanParityBoundaryFlatSubspace p (N + 1)) +
            inner ℂ c
              (intrinsicShellPart p N u :
                euclideanParityBoundaryFlatSubspace p (N + 1)) := by
            rw [inner_add_right]
      _ = inner ℂ c c := by
            rw [hort, hs]
            simp [c]
  have huu :
      Complex.re (inner ℂ u u) = ‖u‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) u).symm
  rw [hTu, inner_add_left]
  have hF :
      inner ℂ (F • c) u = star F * inner ℂ c c := by
    rw [inner_smul_left, hcu]
  have hlamInnerComplex :
      inner ℂ ((lam : ℂ) • u) u =
        lam • inner ℂ u u := by
    exact inner_smul_real_left (𝕜 := ℂ) u u lam
  have hlamInner :
      Complex.re (inner ℂ ((lam : ℂ) • u) u) =
        lam * ‖u‖ ^ 2 := by
    rw [hlamInnerComplex]
    change Complex.re ((lam : ℂ) * inner ℂ u u) = lam * ‖u‖ ^ 2
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, huu]
  rw [hF, Complex.add_re, hlamInner]
  ring

/-- Successor goodness forces the shell-scaled secular real part to pay the
complete negative shift of the canonical trial. -/
theorem neg_lam_mul_cubicSecularTrialVector_norm_sq_le_shellPairing
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hgood : ¬ ParityBad p L (N + 1)) :
    (-lam) *
        ‖cubicSecularTrialVector p hL N hprev lam hlam‖ ^ 2 ≤
      Complex.re
        (star (cubicSecularScalar p hL N hprev lam hlam) *
          inner ℂ
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))) := by
  let u := cubicSecularTrialVector p hL N hprev lam hlam
  have hnonneg :=
    re_inner_parityCompressedCanonical_nonnegative_of_not_parityBad
      hgood u
  have henergy :=
    re_inner_cubicSecularTrialVector_eq
      p hL N hN hprev lam hlam
  dsimp at henergy
  change
    0 ≤ Complex.re
      (inner ℂ (parityCompressedCanonical p L (N + 1) u) u) at hnonneg
  change
    Complex.re
        (inner ℂ (parityCompressedCanonical p L (N + 1) u) u) =
      lam * ‖u‖ ^ 2 +
        Complex.re
          (star (cubicSecularScalar p hL N hprev lam hlam) *
            inner ℂ
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1))
              (intrinsicCubicShellPart p N :
                euclideanParityBoundaryFlatSubspace p (N + 1))) at henergy
  rw [henergy] at hnonneg
  simpa [u] using (show
    (-lam) * ‖u‖ ^ 2 ≤
      Complex.re
        (star (cubicSecularScalar p hL N hprev lam hlam) *
          inner ℂ
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))) by
    linarith)

/-- At a negative shift, a good successor sector forces a strictly positive
shell-scaled secular orientation. -/
theorem cubicSecularScalar_shellPairing_pos_of_not_parityBad
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hgood : ¬ ParityBad p L (N + 1)) :
    0 <
      Complex.re
        (star (cubicSecularScalar p hL N hprev lam hlam) *
          inner ℂ
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))
            (intrinsicCubicShellPart p N :
              euclideanParityBoundaryFlatSubspace p (N + 1))) := by
  have hmargin :=
    neg_lam_mul_cubicSecularTrialVector_norm_sq_le_shellPairing
      p hL N hN hprev lam hlam hgood
  have hune :
      cubicSecularTrialVector p hL N hprev lam hlam ≠ 0 :=
    cubicSecularTrialVector_ne_zero p hL N hN hprev lam hlam
  have hnorm0 :
      0 < ‖cubicSecularTrialVector p hL N hprev lam hlam‖ :=
    norm_pos_iff.mpr hune
  have hnorm : 0 < ‖cubicSecularTrialVector p hL N hprev lam hlam‖ ^ 2 := by
    positivity
  have hshift :
      0 <
        (-lam) *
          ‖cubicSecularTrialVector p hL N hprev lam hlam‖ ^ 2 := by
    exact mul_pos (neg_pos.mpr hlam) hnorm
  exact lt_of_lt_of_le hshift hmargin

end Zeta23.CCM

#print axioms Zeta23.CCM.re_inner_cubicSecularTrialVector_eq
#print axioms Zeta23.CCM.neg_lam_mul_cubicSecularTrialVector_norm_sq_le_shellPairing
#print axioms Zeta23.CCM.cubicSecularScalar_shellPairing_pos_of_not_parityBad
