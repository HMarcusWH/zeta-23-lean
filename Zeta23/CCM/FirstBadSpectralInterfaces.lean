import Zeta23.CCM.ConstrainedParitySpectrum
import Zeta23.CCM.CellMinimalRegularFirstBad

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB04B: spectral interfaces

This module exposes two small interfaces already implicit in the validated
first-bad stack:

* a genuine negative compressed eigenmode is exactly enough to construct a
  `ParityBad` witness;
* whole-cell first-bad minimality gives predecessor nonnegativity for either
  reversal parity, not only the parity selected by the bad successor.

No parity comparison, root exclusion, positivity closure, finite-to-infinite
closure, or RH theorem is asserted here.
-/

/-- A nonzero negative eigenmode of one parity compression gives an exact
`ParityBad` witness in that parity sector. -/
theorem parityBad_of_negative_eigenmode
    {p : ReversalParity} {L : ℝ} {N : ℕ}
    {lam : ℝ} (hlam : lam < 0)
    {v : euclideanParityBoundaryFlatSubspace p N}
    (hvne : v ≠ 0)
    (hveig :
      parityCompressedCanonical p L N v = (lam : ℂ) • v) :
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
  have hcomp :
      Complex.re
        (inner ℂ (parityCompressedCanonical p L N v) v) < 0 := by
    rw [hveig]
    have hinner :
        inner ℂ ((lam : ℂ) • v) v =
          (lam : ℂ) * inner ℂ v v := by
      simpa using
        (inner_smul_left (𝕜 := ℂ) v v (r := (lam : ℂ)))
    rw [hinner, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    have hvnorm :
        Complex.re (inner ℂ v v) = ‖v‖ ^ 2 := by
      simpa only [RCLike.re_to_complex] using
        (norm_sq_eq_re_inner (𝕜 := ℂ) v).symm
    rw [hvnorm]
    have hnorm : 0 < ‖v‖ ^ 2 := by
      positivity
    exact mul_neg_of_neg_of_pos hlam hnorm
  have hamb :
      Complex.re
        (inner ℂ
          ((canonicalSourceMatrix L N).toEuclideanLin
            (v : EuclideanSpace ℂ (Fin (2 * N + 1))))
          (v : EuclideanSpace ℂ (Fin (2 * N + 1)))) < 0 := by
    rw [← re_inner_parityCompressedCanonical_self p L N v]
    exact hcomp
  have hquad :
      (quadraticForm (canonicalSourceMatrix L N) u).re < 0 := by
    change
      (quadraticForm (canonicalSourceMatrix L N)
        ((EuclideanSpace.equiv (Fin (2 * N + 1)) ℂ) x)).re < 0
    rw [quadraticForm_re_eq_re_inner_apply_self]
    simpa [x] using hamb
  exact ⟨u, hune, humem, hquad⟩

/-- Whole-cell first-bad ancestry gives predecessor nonnegativity in either
reversal parity at the retained predecessor size. -/
theorem RegularCellMinimalFirstBadCertificate.predecessorNonnegative_anyParity
    {Q : ℕ}
    (c : RegularCellMinimalFirstBadCertificate Q)
    (p : ReversalParity) :
    ∀ x : EuclideanSpace ℂ (Fin (2 * c.Nstar + 1)),
      x ∈ euclideanParityBoundaryFlatSubspace p c.Nstar →
        0 ≤ Complex.re
          (inner ℂ
            ((canonicalSourceMatrix c.L c.Nstar).toEuclideanLin x)
            x) := by
  intro x hx
  have hNlt : c.Nstar < c.Kstar := by
    rw [← c.succ_eq]
    exact Nat.lt_succ_self c.Nstar
  exact euclideanParity_nonnegative_of_lt_least_anyParityBad
    c.L c.smaller_good p hNlt x hx

end Zeta23.CCM

#print axioms Zeta23.CCM.parityBad_of_negative_eigenmode
#print axioms Zeta23.CCM.RegularCellMinimalFirstBadCertificate.predecessorNonnegative_anyParity
