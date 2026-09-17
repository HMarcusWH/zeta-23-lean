import Zeta23.CCM.ParitySourceMomentFourRigidity
import Zeta23.CCM.QuadraticNormalSourceJets

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: quantitative Pair-D coercivity

PR #207 proves the exact odd compressed self-energy identity carried by the
centered-index image of an even compressed eigenmode,

  re <T_- Dv, Dv>
    =
  lam * ||Dv||^2
    + re (star(sourceMoment(v)) * M4(v)).

This module retains the full quantitative information instead of immediately
collapsing it to strict positivity.

On an odd-good successor sector,

  -lam * ||Dv||^2
    <= re (star(sourceMoment(v)) * M4(v)).

The existing #163 mixed-source identity

  h_v^(7)(0) = -2*(2*pi)^6*M4(v)

then turns the same estimate into a global-source/local-jet orientation law.
For lam < 0 and v != 0 that orientation is strictly negative.

Firewalls:
* `D` remains algebraic/injective only; no isometry claim;
* `Dv` is not asserted to be an odd eigenvector;
* no unconditional sourceMoment-to-M4 implication is asserted;
* no endpoint-scalar sign is used;
* no simultaneous-parity exclusion is asserted;
* no negative-root exclusion or RH theorem is asserted.
-/

/-- Quantitative form of the #207 Pair-D energy inequality.

Odd-sector goodness forces the canonical sourceMoment/M4 coupling to compensate
for at least the complete transported negative eigenenergy. Negativity of
`lam` and nonzeroness of `v` are deliberately not hypotheses here. -/
theorem
    neg_lam_mul_evenToOdd_norm_sq_le_re_star_explicitCanonicalSourceMoment_mul_momentFour_of_even_eigenmode_of_not_oddBad
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    {lam : ℝ}
    {v : euclideanEvenBoundaryFlatSubspace K}
    (hveig :
      evenCompressedCanonical L K v = (lam : ℂ) • v)
    (hodd : ¬ ParityBad .odd L K) :
    -lam * ‖euclideanEvenToOddIndexLinearMap K v‖ ^ 2 ≤
      Complex.re
        (star (explicitCanonicalSourceMoment L K v) *
          centeredMoment K 4
            (evenBoundaryFlatRawCoefficients K v)) := by
  have hnonneg :=
    re_inner_parityCompressedCanonical_nonnegative_of_not_parityBad
      hodd (euclideanEvenToOddIndexLinearMap K v)
  change
    0 ≤
      Complex.re
        (inner ℂ
          (oddCompressedCanonical L K
            (euclideanEvenToOddIndexLinearMap K v))
          (euclideanEvenToOddIndexLinearMap K v)) at hnonneg
  have henergy :=
    re_inner_oddCompressedCanonical_evenIndex_eigenmode_eq
      hL K hK hveig
  rw [henergy] at hnonneg
  linarith

/-- Rewriting the #163 seventh mixed source jet converts the sourceMoment/M4
pairing exactly into a sourceMoment/seventh-jet pairing. -/
theorem
    re_star_explicitCanonicalSourceMoment_mul_seventhJet_eq_neg_two_pi_six_mul_momentFourPairing
    (L : ℝ)
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    Complex.re
        (star (explicitCanonicalSourceMoment L K v) *
          iteratedDeriv 7 (quadraticNormalSourceAtom K v) 0) =
      (-2 * (2 * Real.pi) ^ 6) *
        Complex.re
          (star (explicitCanonicalSourceMoment L K v) *
            centeredMoment K 4
              (evenBoundaryFlatRawCoefficients K v)) := by
  rw [iteratedDeriv_seven_quadraticNormalSourceAtom_eq_moment_four K hK v]
  have hmul :
      star (explicitCanonicalSourceMoment L K v) *
          (((-2 * (2 * Real.pi) ^ 6 : ℝ) : ℂ) *
            centeredMoment K 4
              (evenBoundaryFlatRawCoefficients K v)) =
        (((-2 * (2 * Real.pi) ^ 6 : ℝ) : ℂ)) *
          (star (explicitCanonicalSourceMoment L K v) *
            centeredMoment K 4
              (evenBoundaryFlatRawCoefficients K v)) := by
    ring
  rw [hmul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Quantitative global-source/local-jet upper bound.

This is exactly the #207 coercivity estimate rewritten through the #163 local
seventh mixed source jet. -/
theorem
    re_star_explicitCanonicalSourceMoment_mul_seventhJet_le_two_pi_six_mul_lam_norm_sq_of_even_eigenmode_of_not_oddBad
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    {lam : ℝ}
    {v : euclideanEvenBoundaryFlatSubspace K}
    (hveig :
      evenCompressedCanonical L K v = (lam : ℂ) • v)
    (hodd : ¬ ParityBad .odd L K) :
    Complex.re
        (star (explicitCanonicalSourceMoment L K v) *
          iteratedDeriv 7 (quadraticNormalSourceAtom K v) 0) ≤
      2 * (2 * Real.pi) ^ 6 * lam *
        ‖euclideanEvenToOddIndexLinearMap K v‖ ^ 2 := by
  have hcoerc :=
    neg_lam_mul_evenToOdd_norm_sq_le_re_star_explicitCanonicalSourceMoment_mul_momentFour_of_even_eigenmode_of_not_oddBad
      hL K hK hveig hodd
  rw [
    re_star_explicitCanonicalSourceMoment_mul_seventhJet_eq_neg_two_pi_six_mul_momentFourPairing
      L K (by omega) v
  ]
  calc
    (-2 * (2 * Real.pi) ^ 6) *
        Complex.re
          (star (explicitCanonicalSourceMoment L K v) *
            centeredMoment K 4
              (evenBoundaryFlatRawCoefficients K v))
        ≤
      (-2 * (2 * Real.pi) ^ 6) *
        (-lam * ‖euclideanEvenToOddIndexLinearMap K v‖ ^ 2) := by
          apply mul_le_mul_of_nonpos_left hcoerc
          positivity
    _ =
      2 * (2 * Real.pi) ^ 6 * lam *
        ‖euclideanEvenToOddIndexLinearMap K v‖ ^ 2 := by
          ring

/-- Strict global-source/local-jet anti-alignment for a genuine even negative
compressed eigenmode on an odd-good successor sector. -/
theorem
    re_star_explicitCanonicalSourceMoment_mul_seventhJet_neg_of_even_negative_eigenmode_of_not_oddBad
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    {lam : ℝ} (hlam : lam < 0)
    {v : euclideanEvenBoundaryFlatSubspace K}
    (hvne : v ≠ 0)
    (hveig :
      evenCompressedCanonical L K v = (lam : ℂ) • v)
    (hodd : ¬ ParityBad .odd L K) :
    Complex.re
        (star (explicitCanonicalSourceMoment L K v) *
          iteratedDeriv 7 (quadraticNormalSourceAtom K v) 0) < 0 := by
  have hle :=
    re_star_explicitCanonicalSourceMoment_mul_seventhJet_le_two_pi_six_mul_lam_norm_sq_of_even_eigenmode_of_not_oddBad
      hL K hK hveig hodd
  have hwne :
      euclideanEvenToOddIndexLinearMap K v ≠ 0 := by
    intro hw
    apply hvne
    apply euclideanEvenToOddIndexLinearMap_injective K
    simpa using hw
  have hnorm :
      0 < ‖euclideanEvenToOddIndexLinearMap K v‖ ^ 2 := by
    positivity
  have hc :
      0 < 2 * (2 * Real.pi) ^ 6 := by
    positivity
  have hlamnorm :
      lam * ‖euclideanEvenToOddIndexLinearMap K v‖ ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hlam hnorm
  have hrhs :
      2 * (2 * Real.pi) ^ 6 * lam *
          ‖euclideanEvenToOddIndexLinearMap K v‖ ^ 2 < 0 := by
    rw [mul_assoc]
    exact mul_neg_of_pos_of_neg hc hlamnorm
  exact lt_of_le_of_lt hle hrhs

end Zeta23.CCM

#print axioms Zeta23.CCM.neg_lam_mul_evenToOdd_norm_sq_le_re_star_explicitCanonicalSourceMoment_mul_momentFour_of_even_eigenmode_of_not_oddBad
#print axioms Zeta23.CCM.re_star_explicitCanonicalSourceMoment_mul_seventhJet_eq_neg_two_pi_six_mul_momentFourPairing
#print axioms Zeta23.CCM.re_star_explicitCanonicalSourceMoment_mul_seventhJet_le_two_pi_six_mul_lam_norm_sq_of_even_eigenmode_of_not_oddBad
#print axioms Zeta23.CCM.re_star_explicitCanonicalSourceMoment_mul_seventhJet_neg_of_even_negative_eigenmode_of_not_oddBad
