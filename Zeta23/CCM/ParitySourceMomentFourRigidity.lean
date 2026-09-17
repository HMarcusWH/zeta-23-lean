import Zeta23.CCM.FirstBadSpectralInterfaces
import Zeta23.CCM.SourceMomentDecomposition

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB05: parity/source/M4 energy rigidity

This module composes the exact rank-one even-to-odd compressed parity defect
with the source-explicit identification of its coefficient.  For an even
negative compressed eigenmode `v`, the centered-index image `Dv` therefore has
odd compressed energy

  lam * ||Dv||^2 + re (star(sourceMoment(v)) * M4(v)).

Consequently, if the odd successor sector is not bad, the source-moment/M4
pairing is strictly positive.  This is stronger than either factor being
nonzero separately and does not assert a generic implication
`sourceMoment != 0 -> M4 != 0`.

Firewalls:
* `D` is used only algebraically and injectively, never as an isometry;
* `Dv` is not asserted to be an eigenvector; the cubic defect is retained;
* the defect coefficient is the actual canonical production source moment;
* no simultaneous-parity exclusion, endpoint-scalar sign, negative-root
  exclusion, finite-to-infinite closure, or RH theorem is asserted.
-/

/-- Any nonzero compressed direction with strictly negative self-energy is
already an exact `ParityBad` witness. -/
theorem parityBad_of_negative_compressed_direction
    {p : ReversalParity} {L : ℝ} {N : ℕ}
    {v : euclideanParityBoundaryFlatSubspace p N}
    (hvne : v ≠ 0)
    (hneg :
      Complex.re
        (inner ℂ (parityCompressedCanonical p L N v) v) < 0) :
    ParityBad p L N := by
  let x : EuclideanSpace ℂ (Fin (2 * N + 1)) :=
    (v : EuclideanSpace ℂ (Fin (2 * N + 1)))
  let u : Fin (2 * N + 1) → ℂ :=
    (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x
  have hxmem : x ∈ euclideanParityBoundaryFlatSubspace p N := by
    simpa [x] using v.property
  have humem : u ∈ parityBoundaryFlatSubspace p N := by
    exact (mem_euclideanParityBoundaryFlatSubspace_iff p N x).mp hxmem
  have hune : u ≠ 0 := by
    intro hu
    apply hvne
    apply Subtype.ext
    change x = 0
    apply (EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ).injective
    simpa [u] using hu
  have hxneg :
      Complex.re
        (inner ℂ
          ((canonicalSourceMatrix L N).toEuclideanLin x)
          x) < 0 := by
    rw [← re_inner_parityCompressedCanonical_self p L N v]
    simpa [x] using hneg
  have hbridge :
      (quadraticForm (canonicalSourceMatrix L N)
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x)).re =
      Complex.re
        (inner ℂ
          ((canonicalSourceMatrix L N).toEuclideanLin x)
          x) :=
    quadraticForm_re_eq_re_inner_apply_self
      (canonicalSourceMatrix L N) x
  have hquad :
      (quadraticForm (canonicalSourceMatrix L N) u).re < 0 := by
    change
      (quadraticForm (canonicalSourceMatrix L N)
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x)).re < 0
    rw [hbridge]
    exact hxneg
  exact ⟨u, hune, humem, hquad⟩

/-- The negation of `ParityBad` is exactly enough to make every compressed
self-energy nonnegative. -/
theorem re_inner_parityCompressedCanonical_nonnegative_of_not_parityBad
    {p : ReversalParity} {L : ℝ} {N : ℕ}
    (hgood : ¬ ParityBad p L N)
    (v : euclideanParityBoundaryFlatSubspace p N) :
    0 ≤ Complex.re
      (inner ℂ (parityCompressedCanonical p L N v) v) := by
  by_contra hnonneg
  have hneg :
      Complex.re
        (inner ℂ (parityCompressedCanonical p L N v) v) < 0 :=
    lt_of_not_ge hnonneg
  have hvne : v ≠ 0 := by
    intro hv
    subst v
    simpa using hneg
  exact hgood (parityBad_of_negative_compressed_direction hvne hneg)

/-- Pairing the surviving odd cubic channel with the centered-index image of
an even constrained vector is exactly the fourth centered moment of the
original vector. -/
theorem inner_oddCubicCompressionVector_evenToOddIndex_eq_momentFour
    (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    inner ℂ
        (oddCubicCompressionVector K)
        (euclideanEvenToOddIndexLinearMap K v) =
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) := by
  let w := euclideanEvenToOddIndexLinearMap K v
  have hproj :
      inner ℂ
          ((euclideanOddBoundaryFlatSubspace K).orthogonalProjectionOnto
            (centeredPowerVector K 3))
          (w : EuclideanSpace ℂ (Fin (2 * K + 1))) =
        inner ℂ (centeredPowerVector K 3)
          (w : EuclideanSpace ℂ (Fin (2 * K + 1))) := by
    exact
      Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
        (K := euclideanOddBoundaryFlatSubspace K) w w.property
  change
    inner ℂ
        ((euclideanOddBoundaryFlatSubspace K).orthogonalProjectionOnto
          (centeredPowerVector K 3))
        (w : EuclideanSpace ℂ (Fin (2 * K + 1))) = _
  rw [hproj, inner_centeredPowerVector]
  change
    centeredMoment K 3
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (w : EuclideanSpace ℂ (Fin (2 * K + 1)))) = _
  rw [show
      (w : EuclideanSpace ℂ (Fin (2 * K + 1))) =
        euclideanIndexLinearMap K
          (v : EuclideanSpace ℂ (Fin (2 * K + 1))) by rfl]
  rw [euclideanIndexLinearMap_coordinates]
  change
    centeredMoment K 3
        (indexMatrix K *ᵥ evenBoundaryFlatRawCoefficients K v) = _
  simpa using
    centeredMoment_indexMatrix_mulVec K 3 (evenBoundaryFlatRawCoefficients K v)

/-- Exact operator identity on an even compressed eigenmode.  The centered-index
image need not be an odd eigenvector; its failure is precisely the canonical
source-moment multiple of the cubic odd channel. -/
theorem oddCompressedCanonical_evenToOddIndex_of_even_eigenmode
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    {lam : ℝ}
    {v : euclideanEvenBoundaryFlatSubspace K}
    (hveig : evenCompressedCanonical L K v = (lam : ℂ) • v) :
    oddCompressedCanonical L K (euclideanEvenToOddIndexLinearMap K v) =
      (lam : ℂ) • euclideanEvenToOddIndexLinearMap K v +
        explicitCanonicalSourceMoment L K v • oddCubicCompressionVector K := by
  have hdef :=
    evenOddCompressedIntertwiningDefect_eq_cubicFunctional_smul
      hL K hK v
  rw [cubicDefectFunctional_eq_explicitCanonicalSourceMoment hL K hK v] at hdef
  change
    oddCompressedCanonical L K (euclideanEvenToOddIndexLinearMap K v) -
        euclideanEvenToOddIndexLinearMap K (evenCompressedCanonical L K v) =
      explicitCanonicalSourceMoment L K v • oddCubicCompressionVector K at hdef
  rw [hveig, map_smul] at hdef
  have hsum := (sub_eq_iff_eq_add).mp hdef
  simpa [add_comm] using hsum

/-- Exact odd compressed self-energy identity carried by the centered-index
image of an even compressed eigenmode. -/
theorem re_inner_oddCompressedCanonical_evenIndex_eigenmode_eq
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    {lam : ℝ}
    {v : euclideanEvenBoundaryFlatSubspace K}
    (hveig : evenCompressedCanonical L K v = (lam : ℂ) • v) :
    Complex.re
        (inner ℂ
          (oddCompressedCanonical L K (euclideanEvenToOddIndexLinearMap K v))
          (euclideanEvenToOddIndexLinearMap K v)) =
      lam * ‖euclideanEvenToOddIndexLinearMap K v‖ ^ 2 +
        Complex.re
          (star (explicitCanonicalSourceMoment L K v) *
            centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)) := by
  let w := euclideanEvenToOddIndexLinearMap K v
  let g := oddCubicCompressionVector K
  let S := explicitCanonicalSourceMoment L K v
  have hop :=
    oddCompressedCanonical_evenToOddIndex_of_even_eigenmode
      hL K hK hveig
  have hpair :=
    inner_oddCubicCompressionVector_evenToOddIndex_eq_momentFour K v
  have hlaminner :
      inner ℂ ((lam : ℂ) • w) w =
        (lam : ℂ) * inner ℂ w w := by
    simpa [w] using
      (inner_smul_left (𝕜 := ℂ) w w (r := (lam : ℂ)))
  have hsourceinner :
      inner ℂ (S • g) w =
        star S * centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) := by
    have hs := inner_smul_left (𝕜 := ℂ) g w (r := S)
    simpa [S, g, w, hpair] using hs
  have hinner :
      inner ℂ
          (oddCompressedCanonical L K w) w =
        (lam : ℂ) * inner ℂ w w +
          star S * centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) := by
    rw [show
      oddCompressedCanonical L K w =
        (lam : ℂ) • w + S • g by simpa [w, S, g] using hop]
    rw [inner_add_left, hlaminner, hsourceinner]
  have hwnorm :
      Complex.re (inner ℂ w w) = ‖w‖ ^ 2 := by
    simpa only [RCLike.re_to_complex] using
      (norm_sq_eq_re_inner (𝕜 := ℂ) w).symm
  have hfirst :
      Complex.re ((lam : ℂ) * inner ℂ w w) =
        lam * ‖w‖ ^ 2 := by
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, hwnorm]
  change
    Complex.re (inner ℂ (oddCompressedCanonical L K w) w) = _
  rw [hinner, Complex.add_re, hfirst]
  rfl

/-- Headline generic rigidity: if the odd successor sector is good, then an
even negative compressed eigenmode forces a strictly positive canonical
source-moment/M4 pairing on that same vector. -/
theorem re_star_explicitCanonicalSourceMoment_mul_momentFour_pos_of_even_negative_eigenmode_of_not_oddBad
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    {lam : ℝ} (hlam : lam < 0)
    {v : euclideanEvenBoundaryFlatSubspace K}
    (hvne : v ≠ 0)
    (hveig : evenCompressedCanonical L K v = (lam : ℂ) • v)
    (hodd : ¬ ParityBad .odd L K) :
    0 < Complex.re
      (star (explicitCanonicalSourceMoment L K v) *
        centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)) := by
  let w := euclideanEvenToOddIndexLinearMap K v
  have hwne : w ≠ 0 := by
    intro hw
    apply hvne
    apply euclideanEvenToOddIndexLinearMap_injective K
    simpa [w] using hw
  have hnonneg :
      0 ≤ Complex.re
        (inner ℂ (oddCompressedCanonical L K w) w) := by
    simpa [oddCompressedCanonical, w] using
      re_inner_parityCompressedCanonical_nonnegative_of_not_parityBad
        hodd w
  have henergy :=
    re_inner_oddCompressedCanonical_evenIndex_eigenmode_eq
      hL K hK hveig
  have hnorm : 0 < ‖w‖ ^ 2 := by positivity
  have hneg : lam * ‖w‖ ^ 2 < 0 :=
    mul_neg_of_neg_of_pos hlam hnorm
  change
    Complex.re
        (inner ℂ (oddCompressedCanonical L K w) w) =
      lam * ‖w‖ ^ 2 +
        Complex.re
          (star (explicitCanonicalSourceMoment L K v) *
            centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v)) at henergy
  nlinarith

/-- The strict pairing immediately forces the canonical source moment itself to
be nonzero on the odd-good branch. -/
theorem explicitCanonicalSourceMoment_ne_zero_of_even_negative_eigenmode_of_not_oddBad
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    {lam : ℝ} (hlam : lam < 0)
    {v : euclideanEvenBoundaryFlatSubspace K}
    (hvne : v ≠ 0)
    (hveig : evenCompressedCanonical L K v = (lam : ℂ) • v)
    (hodd : ¬ ParityBad .odd L K) :
    explicitCanonicalSourceMoment L K v ≠ 0 := by
  have hpos :=
    re_star_explicitCanonicalSourceMoment_mul_momentFour_pos_of_even_negative_eigenmode_of_not_oddBad
      hL K hK hlam hvne hveig hodd
  intro hzero
  rw [hzero] at hpos
  norm_num at hpos

/-- The same strict pairing also forces the fourth centered moment to be
nonzero; no implication from source-moment nonvanishing alone is used. -/
theorem momentFour_ne_zero_of_even_negative_eigenmode_of_not_oddBad
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K)
    {lam : ℝ} (hlam : lam < 0)
    {v : euclideanEvenBoundaryFlatSubspace K}
    (hvne : v ≠ 0)
    (hveig : evenCompressedCanonical L K v = (lam : ℂ) • v)
    (hodd : ¬ ParityBad .odd L K) :
    centeredMoment K 4 (evenBoundaryFlatRawCoefficients K v) ≠ 0 := by
  have hpos :=
    re_star_explicitCanonicalSourceMoment_mul_momentFour_pos_of_even_negative_eigenmode_of_not_oddBad
      hL K hK hlam hvne hveig hodd
  intro hzero
  rw [hzero] at hpos
  norm_num at hpos

end Zeta23.CCM

#print axioms Zeta23.CCM.parityBad_of_negative_compressed_direction
#print axioms Zeta23.CCM.inner_oddCubicCompressionVector_evenToOddIndex_eq_momentFour
#print axioms Zeta23.CCM.oddCompressedCanonical_evenToOddIndex_of_even_eigenmode
#print axioms Zeta23.CCM.re_inner_oddCompressedCanonical_evenIndex_eigenmode_eq
#print axioms Zeta23.CCM.re_star_explicitCanonicalSourceMoment_mul_momentFour_pos_of_even_negative_eigenmode_of_not_oddBad
#print axioms Zeta23.CCM.momentFour_ne_zero_of_even_negative_eigenmode_of_not_oddBad
