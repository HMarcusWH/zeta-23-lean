import Zeta23.CCM.FirstBadSpectralInterfaces
import Zeta23.CCM.CubicSecularEquation
import Zeta23.CCM.CanonicalSourceEnergy
import Zeta23.CCM.CanonicalRieszBoundary

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB04B: shifted secular-root Riesz boundary

This module moves the complete production Riesz identities from a generic
boundary-flat carrier onto the canonical shifted trial at an actual negative
secular root.  In the even sector the same shifted eigenvector therefore
carries both strict order-eight negativity and the exact order-eight/order-nine
`M_4` boundary decomposition from #159.

No sign of the endpoint scalar, source moment, overlap coefficient, complete
channel beyond the stated root consequence, negative-root exclusion, or RH
theorem is asserted here.
-/

/-- At a secular root, the parity-compressed canonical self-energy of the
canonical shifted trial is exactly `lam * ‖u‖²`. -/
theorem parityCanonicalSourceEnergy_cubicSecularTrialVector_eq_lam_normSq_of_root
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicSecularScalar p hL N hprev lam hlam = 0) :
    parityCanonicalSourceEnergy p L (N + 1)
        (cubicSecularTrialVector p hL N hprev lam hlam) =
      lam * ‖cubicSecularTrialVector p hL N hprev lam hlam‖ ^ 2 := by
  have hEig :
      parityCompressedCanonical p L (N + 1)
          (cubicSecularTrialVector p hL N hprev lam hlam) =
        (lam : ℂ) • cubicSecularTrialVector p hL N hprev lam hlam :=
    (cubicSecularScalar_eq_zero_iff_trial_eigenmode
      p hL N hN hprev lam hlam).mp hroot
  unfold parityCanonicalSourceEnergy
  rw [hEig]
  have hinner :
      inner ℂ
          ((lam : ℂ) • cubicSecularTrialVector p hL N hprev lam hlam)
          (cubicSecularTrialVector p hL N hprev lam hlam) =
        (lam : ℂ) *
          inner ℂ
            (cubicSecularTrialVector p hL N hprev lam hlam)
            (cubicSecularTrialVector p hL N hprev lam hlam) := by
    simpa using
      (inner_smul_left (𝕜 := ℂ)
        (cubicSecularTrialVector p hL N hprev lam hlam)
        (cubicSecularTrialVector p hL N hprev lam hlam)
        (r := (lam : ℂ)))
  rw [hinner, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]
  have hnorm :
      Complex.re
          (inner ℂ
            (cubicSecularTrialVector p hL N hprev lam hlam)
            (cubicSecularTrialVector p hL N hprev lam hlam)) =
        ‖cubicSecularTrialVector p hL N hprev lam hlam‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      (norm_sq_eq_re_inner
        (𝕜 := ℂ) (cubicSecularTrialVector p hL N hprev lam hlam)).symm
  rw [hnorm]

/-- A negative secular root gives strict negativity of the exact parity
canonical energy on the canonical shifted trial. -/
theorem parityCanonicalSourceEnergy_cubicSecularTrialVector_neg_of_root
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicSecularScalar p hL N hprev lam hlam = 0) :
    parityCanonicalSourceEnergy p L (N + 1)
        (cubicSecularTrialVector p hL N hprev lam hlam) < 0 := by
  have hEq :=
    parityCanonicalSourceEnergy_cubicSecularTrialVector_eq_lam_normSq_of_root
      p hL N hN hprev lam hlam hroot
  have hne :=
    cubicSecularTrialVector_ne_zero p hL N hN hprev lam hlam
  have hnorm :
      0 < ‖cubicSecularTrialVector p hL N hprev lam hlam‖ ^ 2 := by
    positivity
  rw [hEq]
  exact mul_neg_of_neg_of_pos hlam hnorm

/-- The exact complete production source-channel energy is strictly negative on
that same canonical shifted root trial. -/
theorem canonicalSourceChannelEnergy_cubicSecularTrialVector_neg_of_root
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace p N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicSecularScalar p hL N hprev lam hlam = 0) :
    canonicalSourceChannelEnergy L (N + 1)
        (cubicSecularTrialVector p hL N hprev lam hlam :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) < 0 := by
  have hparity :=
    parityCanonicalSourceEnergy_cubicSecularTrialVector_neg_of_root
      p hL N hN hprev lam hlam hroot
  have hEq :=
    parityCanonicalSourceEnergy_eq_channels
      p hL (N + 1) (cubicSecularTrialVector p hL N hprev lam hlam)
  rw [← hEq]
  exact hparity

/-- An even negative secular root has a strictly negative complete order-eight
Riesz source channel on the same canonical shifted trial. -/
theorem canonicalRieszSourceChannelEnergy_eight_neg_of_even_secular_root
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicSecularScalar .even hL N hprev lam hlam = 0) :
    canonicalRieszSourceChannelEnergy L 8 (N + 1)
        (cubicSecularTrialVector .even hL N hprev lam hlam :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) < 0 := by
  let u := cubicSecularTrialVector .even hL N hprev lam hlam
  have huEven :
      (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanEvenBoundaryFlatSubspace (N + 1) := by
    exact u.property
  have huRaw :=
    (mem_euclideanEvenBoundaryFlatSubspace_iff
      (N + 1) (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))).mp huEven
  have hflat :
      BoundaryFlatCoefficients (N + 1)
        ((EuclideanSpace.equiv (Fin (2 * (N + 1) + 1)) ℂ)
          (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) :=
    (mem_boundaryFlatSubspace_iff (N + 1) _).mp huRaw.1
  have heven :
      ((EuclideanSpace.equiv (Fin (2 * (N + 1) + 1)) ℂ)
        (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) ∈
        evenCoefficientSubspace (N + 1) :=
    huRaw.2
  have hchannel :
      canonicalSourceChannelEnergy L (N + 1)
          (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) < 0 := by
    simpa [u] using
      canonicalSourceChannelEnergy_cubicSecularTrialVector_neg_of_root
        .even hL N hN hprev lam hlam hroot
  have hEq :=
    canonicalSourceChannelEnergy_eq_rieszEight_of_even_boundaryFlat
      hL (N + 1)
      (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) hflat heven
  rw [← hEq]
  exact hchannel

/-- On the same even negative secular-root trial, strict order-eight negativity
pushes order nine below the negative of the exact #159 `M_4` boundary term.
No sign of the endpoint scalar is assumed. -/
theorem canonicalRieszSourceChannelEnergy_nine_lt_neg_momentFourBoundary_of_even_secular_root
    {L : ℝ} (hL : 0 < L)
    (N : ℕ) (hN : 1 ≤ N)
    (hprev :
      ∀ x : EuclideanSpace ℂ (Fin (2 * N + 1)),
        x ∈ euclideanParityBoundaryFlatSubspace .even N →
          0 ≤ Complex.re
            (inner ℂ ((canonicalSourceMatrix L N).toEuclideanLin x) x))
    (lam : ℝ) (hlam : lam < 0)
    (hroot : cubicSecularScalar .even hL N hprev lam hlam = 0) :
    canonicalRieszSourceChannelEnergy L 9 (N + 1)
        (cubicSecularTrialVector .even hL N hprev lam hlam :
          EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) <
      -(2 * (2 * Real.pi) ^ 8 *
        canonicalPolePrimeRieszEndpointScalar L 8 *
        Complex.normSq
          (centeredMoment (N + 1) 4
            ((EuclideanSpace.equiv (Fin (2 * (N + 1) + 1)) ℂ)
              (cubicSecularTrialVector .even hL N hprev lam hlam :
                EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))))) := by
  let u := cubicSecularTrialVector .even hL N hprev lam hlam
  have huEven :
      (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) ∈
        euclideanEvenBoundaryFlatSubspace (N + 1) := by
    exact u.property
  have huRaw :=
    (mem_euclideanEvenBoundaryFlatSubspace_iff
      (N + 1) (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))).mp huEven
  have hflat :
      BoundaryFlatCoefficients (N + 1)
        ((EuclideanSpace.equiv (Fin (2 * (N + 1) + 1)) ℂ)
          (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) :=
    (mem_boundaryFlatSubspace_iff (N + 1) _).mp huRaw.1
  have heven :
      ((EuclideanSpace.equiv (Fin (2 * (N + 1) + 1)) ℂ)
        (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))) ∈
        evenCoefficientSubspace (N + 1) :=
    huRaw.2
  have hEq :=
    canonicalRieszSourceChannelEnergy_eight_eq_nine_add_moment_four
      hL (N + 1)
      (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) hflat heven
  have hNeg :
      canonicalRieszSourceChannelEnergy L 8 (N + 1)
          (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) < 0 := by
    simpa [u] using
      canonicalRieszSourceChannelEnergy_eight_neg_of_even_secular_root
        hL N hN hprev lam hlam hroot
  simpa [u] using (show
    canonicalRieszSourceChannelEnergy L 9 (N + 1)
        (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1))) <
      -(2 * (2 * Real.pi) ^ 8 *
        canonicalPolePrimeRieszEndpointScalar L 8 *
        Complex.normSq
          (centeredMoment (N + 1) 4
            ((EuclideanSpace.equiv (Fin (2 * (N + 1) + 1)) ℂ)
              (u : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)))))) by
      linarith)

/-- If the successor parity sector is not bad, its secular scalar cannot vanish
at a negative shift. -/
theorem cubicSecularScalar_ne_zero_of_not_parityBad
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
    cubicSecularScalar p hL N hprev lam hlam ≠ 0 := by
  intro hroot
  obtain ⟨v, hvne, hveig⟩ :=
    (cubicSecularScalar_eq_zero_iff_exists_eigenmode
      p hL N hN hprev lam hlam).mp hroot
  exact hgood (parityBad_of_negative_eigenmode hlam hvne hveig)

end Zeta23.CCM

#print axioms Zeta23.CCM.parityCanonicalSourceEnergy_cubicSecularTrialVector_eq_lam_normSq_of_root
#print axioms Zeta23.CCM.canonicalSourceChannelEnergy_cubicSecularTrialVector_neg_of_root
#print axioms Zeta23.CCM.canonicalRieszSourceChannelEnergy_eight_neg_of_even_secular_root
#print axioms Zeta23.CCM.canonicalRieszSourceChannelEnergy_nine_lt_neg_momentFourBoundary_of_even_secular_root
#print axioms Zeta23.CCM.cubicSecularScalar_ne_zero_of_not_parityBad
