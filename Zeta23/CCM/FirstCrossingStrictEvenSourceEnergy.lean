import Zeta23.CCM.GlobalParityBottomSourceMoment
import Zeta23.CCM.ParitySourceMomentFourRigidity

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#279 strict-even zero-contact source energy

This module theoremizes the exact source/M4-to-odd-energy identity used in the
equality-rigidity derivation. It is branch-gated: it assumes an actual even
zero eigenmode at the selected cutoff and does not assert that every canonical
first-crossing shell lies in this strict-even global-ground regime.
-/

/-- Real source/M4 pairing at one even state. -/
def strictEvenSourceMomentPairing
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) : ℝ :=
  Complex.re
    (star (explicitCanonicalSourceMoment L K v) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v))

/-- At an exact even zero eigenmode, the source/M4 pairing is exactly the
odd compressed energy of the centered-index image. -/
theorem strictEvenSourceMomentPairing_eq_oddEnergy_of_even_zero_eigenmode
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hveig : evenCompressedCanonical L K v = 0) :
    strictEvenSourceMomentPairing L K v =
      Complex.re
        (inner ℂ
          (oddCompressedCanonical L K
            (euclideanEvenToOddIndexLinearMap K v))
          (euclideanEvenToOddIndexLinearMap K v)) := by
  have hveig' :
      evenCompressedCanonical L K v = ((0 : ℝ) : ℂ) • v := by
    simpa using hveig
  have h :=
    re_inner_oddCompressedCanonical_evenIndex_eigenmode_eq
      hL K hK (lam := 0) (v := v) hveig'
  simpa [strictEvenSourceMomentPairing] using h.symm

/-- If the even ground is exactly zero and the odd ground is strictly above it,
the exact source/M4 pairing is strictly positive. -/
theorem strictEvenSourceMomentPairing_pos_of_even_zero_ground_strict
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hvne : v ≠ 0)
    (hground : parityRayleighBottom .even L K = 0)
    (hveig : evenCompressedCanonical L K v = 0)
    (hodd : 0 < parityRayleighBottom .odd L K) :
    0 < strictEvenSourceMomentPairing L K v := by
  have hveig' :
      parityCompressedCanonical .even L K v =
        (parityRayleighBottom .even L K : ℂ) • v := by
    change
      evenCompressedCanonical L K v =
        (parityRayleighBottom .even L K : ℂ) • v
    rw [hground]
    simpa using hveig
  have hstrict :
      parityRayleighBottom .even L K <
        parityRayleighBottom .odd L K := by
    linarith
  simpa [strictEvenSourceMomentPairing] using
    re_star_source_mul_momentFour_pos_of_evenGround_strict
      hL K hK v hvne hveig' hstrict

/-- The odd energy itself is therefore strictly positive in the same branch. -/
theorem oddEnergy_evenIndex_pos_of_even_zero_ground_strict
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hvne : v ≠ 0)
    (hground : parityRayleighBottom .even L K = 0)
    (hveig : evenCompressedCanonical L K v = 0)
    (hodd : 0 < parityRayleighBottom .odd L K) :
    0 <
      Complex.re
        (inner ℂ
          (oddCompressedCanonical L K
            (euclideanEvenToOddIndexLinearMap K v))
          (euclideanEvenToOddIndexLinearMap K v)) := by
  rw [← strictEvenSourceMomentPairing_eq_oddEnergy_of_even_zero_eigenmode
    hL K hK v hveig]
  exact
    strictEvenSourceMomentPairing_pos_of_even_zero_ground_strict
      hL K hK v hvne hground hveig hodd

end Zeta23.CCM

#print axioms Zeta23.CCM.strictEvenSourceMomentPairing_eq_oddEnergy_of_even_zero_eigenmode
#print axioms Zeta23.CCM.strictEvenSourceMomentPairing_pos_of_even_zero_ground_strict
#print axioms Zeta23.CCM.oddEnergy_evenIndex_pos_of_even_zero_ground_strict
