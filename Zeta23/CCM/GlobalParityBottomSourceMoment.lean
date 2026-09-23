import Zeta23.CCM.GlobalParityBottomSpectrum
import Zeta23.CCM.ParitySourceMomentFourRigidity

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# PR #247 — parity-gap source/fourth-moment coercivity

The historical source/M4 positivity theorem assumed the opposite successor
parity was nonnegative at zero.  At the true global ground shift that premise
can be weakened sharply.

If an even ground eigenvalue lies strictly below the odd ground eigenvalue,
then applying the odd Rayleigh lower bound to the centered-index image of the
even ground state gives

  (lambda_odd - lambda_even) ||D v||^2
    <= Re(star S(v) * M4(v)).

This remains valid when the odd successor is itself bad at zero.  It is the
quantitative source rigidity supplied specifically by global-bottom selection.
-/

/-- Exact parity-gap coercivity for any even eigenvector sitting at the true
even ground value. -/
theorem parityGap_mul_evenIndex_norm_sq_le_re_star_source_mul_momentFour
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig :
      parityCompressedCanonical .even L K v =
        (parityRayleighBottom .even L K : ℂ) • v) :
    (parityRayleighBottom .odd L K -
        parityRayleighBottom .even L K) *
        ‖euclideanEvenToOddIndexLinearMap K v‖ ^ 2 ≤
      Complex.re
        (star (explicitCanonicalSourceMoment L K v) *
          centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)) := by
  let w := euclideanEvenToOddIndexLinearMap K v
  have hbottom :=
    parityRayleighBottom_mul_norm_sq_le .odd L K w
  change
    evenCompressedCanonical L K v =
      (parityRayleighBottom .even L K : ℂ) • v at hveig
  have henergy :=
    re_inner_oddCompressedCanonical_evenIndex_eigenmode_eq
      hL K hK hveig
  change
    parityRayleighBottom .odd L K * ‖w‖ ^ 2 ≤
      Complex.re
        (inner ℂ (oddCompressedCanonical L K w) w) at hbottom
  rw [henergy] at hbottom
  simpa [w] using (show
    (parityRayleighBottom .odd L K -
        parityRayleighBottom .even L K) *
        ‖w‖ ^ 2 ≤
      Complex.re
        (star (explicitCanonicalSourceMoment L K v) *
          centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)) by
    linarith)

/-- Strict spectral separation makes the source/M4 pairing strictly positive
on every nonzero even ground eigenvector. -/
theorem re_star_source_mul_momentFour_pos_of_evenGround_strict
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hvne : v ≠ 0)
    (hveig :
      parityCompressedCanonical .even L K v =
        (parityRayleighBottom .even L K : ℂ) • v)
    (hstrict :
      parityRayleighBottom .even L K <
        parityRayleighBottom .odd L K) :
    0 <
      Complex.re
        (star (explicitCanonicalSourceMoment L K v) *
          centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)) := by
  have hbound :=
    parityGap_mul_evenIndex_norm_sq_le_re_star_source_mul_momentFour
      hL K hK v hveig
  have hwne :
      euclideanEvenToOddIndexLinearMap K v ≠ 0 := by
    intro hw
    apply hvne
    apply euclideanEvenToOddIndexLinearMap_injective K
    simpa using hw
  have hnorm :
      0 < ‖euclideanEvenToOddIndexLinearMap K v‖ ^ 2 := by
    positivity
  have hleft :
      0 <
        (parityRayleighBottom .odd L K -
            parityRayleighBottom .even L K) *
          ‖euclideanEvenToOddIndexLinearMap K v‖ ^ 2 :=
    mul_pos (sub_pos.mpr hstrict) hnorm
  exact lt_of_lt_of_le hleft hbound

theorem explicitCanonicalSourceMoment_ne_zero_of_evenGround_strict
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hvne : v ≠ 0)
    (hveig :
      parityCompressedCanonical .even L K v =
        (parityRayleighBottom .even L K : ℂ) • v)
    (hstrict :
      parityRayleighBottom .even L K <
        parityRayleighBottom .odd L K) :
    explicitCanonicalSourceMoment L K v ≠ 0 := by
  have hpos :=
    re_star_source_mul_momentFour_pos_of_evenGround_strict
      hL K hK v hvne hveig hstrict
  intro hzero
  rw [hzero] at hpos
  norm_num at hpos

theorem momentFour_ne_zero_of_evenGround_strict
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hvne : v ≠ 0)
    (hveig :
      parityCompressedCanonical .even L K v =
        (parityRayleighBottom .even L K : ℂ) • v)
    (hstrict :
      parityRayleighBottom .even L K <
        parityRayleighBottom .odd L K) :
    centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) ≠ 0 := by
  have hpos :=
    re_star_source_mul_momentFour_pos_of_evenGround_strict
      hL K hK v hvne hveig hstrict
  intro hzero
  rw [hzero] at hpos
  norm_num at hpos

end Zeta23.CCM

#print axioms Zeta23.CCM.parityGap_mul_evenIndex_norm_sq_le_re_star_source_mul_momentFour
#print axioms Zeta23.CCM.re_star_source_mul_momentFour_pos_of_evenGround_strict
#print axioms Zeta23.CCM.explicitCanonicalSourceMoment_ne_zero_of_evenGround_strict
#print axioms Zeta23.CCM.momentFour_ne_zero_of_evenGround_strict
