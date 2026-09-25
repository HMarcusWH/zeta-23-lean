import Zeta23.CCM.GlobalParityBottomSpectrum
import Zeta23.CCM.NestedFinite

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#266 — unconditional global parity-bottom N-flow

Exact centered zero extension embeds each parity carrier into every larger
carrier, preserves the Euclidean norm, and preserves the canonical quadratic
energy at fixed positive aperture. Hence the parity Rayleigh bottom cannot
increase with truncation size. Taking the minimum over even and odd sectors
gives the same antitonicity for the global successor bottom.

Firewalls:
* larger N -> the bottom can only move down;
* small-N positivity does not propagate upward from this theorem;
* negativity does propagate upward in N;
* no aperture monotonicity is asserted;
* no prime-remainder dominance or residual-state exclusion is asserted;
* RH remains OPEN.
-/

/-- At fixed positive aperture, the parity Rayleigh bottom is antitone along
successor truncation sizes. -/
theorem parityRayleighBottom_succ_antitone_of_le
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    {N M : ℕ}
    (hN : 1 ≤ N)
    (hNM : N ≤ M) :
    parityRayleighBottom p L (M + 1) ≤
      parityRayleighBottom p L (N + 1) := by
  obtain ⟨v, hvne, hveig⟩ :=
    exists_eigenmode_at_parityRayleighBottom_succ p L N hN
  have hNM' : N + 1 ≤ M + 1 := Nat.succ_le_succ hNM
  let w : euclideanParityBoundaryFlatSubspace p (M + 1) :=
    ⟨euclideanCenteredZeroExtend hNM'
        (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))),
      euclideanCenteredZeroExtend_mem_euclideanParityBoundaryFlatSubspace
        p hNM' v.property⟩

  have hnorm : ‖w‖ = ‖v‖ := by
    change
      ‖euclideanCenteredZeroExtend hNM'
          (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))‖ =
        ‖(v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))‖
    exact (euclideanCenteredZeroExtend hNM').norm_map _

  have htransport :
      Complex.re
          (inner ℂ
            (parityCompressedCanonical p L (M + 1) w)
            w) =
        Complex.re
          (inner ℂ
            (parityCompressedCanonical p L (N + 1) v)
            v) := by
    calc
      Complex.re
          (inner ℂ
            (parityCompressedCanonical p L (M + 1) w)
            w)
          =
        Complex.re
          (inner ℂ
            ((canonicalSourceMatrix L (M + 1)).toEuclideanLin
              (w : EuclideanSpace ℂ (Fin (2 * (M + 1) + 1))))
            (w : EuclideanSpace ℂ (Fin (2 * (M + 1) + 1)))) := by
              exact re_inner_parityCompressedCanonical_self p L (M + 1) w
      _ =
        Complex.re
          (inner ℂ
            ((canonicalSourceMatrix L (N + 1)).toEuclideanLin
              (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))))
            (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) := by
              simpa [w] using
                (re_inner_canonicalSourceMatrix_euclideanCenteredZeroExtend
                  hL hNM'
                  (v : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))))
      _ =
        Complex.re
          (inner ℂ
            (parityCompressedCanonical p L (N + 1) v)
            v) := by
              symm
              exact re_inner_parityCompressedCanonical_self p L (N + 1) v

  have hold :
      Complex.re
          (inner ℂ
            (parityCompressedCanonical p L (N + 1) v)
            v) =
        parityRayleighBottom p L (N + 1) * ‖v‖ ^ 2 := by
    rw [hveig]
    have hsmul :
        inner ℂ
            ((parityRayleighBottom p L (N + 1) : ℂ) • v)
            v =
          parityRayleighBottom p L (N + 1) • inner ℂ v v := by
      exact inner_smul_real_left
        (𝕜 := ℂ) v v (parityRayleighBottom p L (N + 1))
    rw [hsmul, Complex.smul_re]
    have hvnorm :
        Complex.re (inner ℂ v v) = ‖v‖ ^ 2 := by
      simpa only [RCLike.re_to_complex] using
        (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
    rw [hvnorm, smul_eq_mul]

  have hlarge :=
    parityRayleighBottom_mul_norm_sq_le p L (M + 1) w
  have hlarge' :
      parityRayleighBottom p L (M + 1) * ‖v‖ ^ 2 ≤
        parityRayleighBottom p L (N + 1) * ‖v‖ ^ 2 := by
    simpa only [RCLike.re_to_complex, hnorm, htransport, hold] using hlarge
  have hvnormpos : 0 < ‖v‖ ^ 2 := by
    positivity
  exact (mul_le_mul_right hvnormpos).mp hlarge'

/-- The global successor bottom, the minimum of the even and odd successor
parity bottoms, is antitone in the predecessor-size index. -/
theorem globalParitySuccessorBottom_antitone_of_le
    {L : ℝ} (hL : 0 < L)
    {N M : ℕ}
    (hN : 1 ≤ N)
    (hNM : N ≤ M) :
    globalParitySuccessorBottom L M ≤
      globalParitySuccessorBottom L N := by
  unfold globalParitySuccessorBottom
  exact min_le_min
    (parityRayleighBottom_succ_antitone_of_le .even hL hN hNM)
    (parityRayleighBottom_succ_antitone_of_le .odd hL hN hNM)

end Zeta23.CCM

#print axioms Zeta23.CCM.parityRayleighBottom_succ_antitone_of_le
#print axioms Zeta23.CCM.globalParitySuccessorBottom_antitone_of_le
