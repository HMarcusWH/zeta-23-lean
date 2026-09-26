import Zeta23.ExceptionalZero.CanonicalArithmeticCriterion
import Zeta23.ExceptionalZero.CofinalArithmeticConditionalRH

noncomputable section

namespace Zeta23.ExceptionalZero

open Zeta23.CCM

/-!
# Audit-only: cofinal canonical arithmetic certificates are RH-equivalent

PR #271 proved the sufficient implication
`CofinalCanonicalArithmeticCertificates -> RiemannHypothesis`.
This file performs the anti-circularity audit in the reverse direction.

The reverse implication uses only the already-proved #246 theorem that RH gives
nonnegativity of the complete canonical finite Weil energy on every legal
boundary-flat carrier.  For each requested aperture threshold, choose any
positive larger aperture; for every starting size and every positive error,
reuse that starting size.  Exact nonnegativity is stronger than the requested
`-epsilon * ||x||^2` lower bound.

This classifies the #271 cofinal certificate proposition as another exact
RH-equivalent terminal formulation.  It does not prove RH and must not be
treated as independent arithmetic progress toward RH.
-/

/-- Under RH the #271 cofinal arithmetic certificate family exists.  The
construction is deliberately trivial once canonical finite Weil positivity is
available: choose a positive aperture above the requested threshold and reuse
the requested finite size for every positive error. -/
theorem cofinalCanonicalArithmeticCertificates_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    CofinalCanonicalArithmeticCertificates := by
  intro B
  let L : ℝ := max 1 (B + 1)
  have hL : 0 < L := by
    exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _)
  have hBL : B < L := by
    exact lt_of_lt_of_le (by linarith : B < B + 1) (le_max_right _ _)
  refine ⟨L, hL, hBL, ?_⟩
  intro n hn ε hε
  refine ⟨n, le_rfl, ?_⟩
  rw [canonicalArithmeticLowerBound_iff_energy hL (n + 1) ε]
  intro x hx
  have hx' : EuclideanBoundaryFlat (n + 1) x := by
    exact
      (mem_euclideanBoundaryFlatSubspace_iff_boundaryFlat (n + 1) x).mp hx
  have hnonneg : 0 ≤ canonicalSourceChannelEnergy L (n + 1) x :=
    canonicalFiniteWeilPositivity_of_riemannHypothesis hRH
      L hL (n + 1) x hx'
  have hcoeff : -ε ≤ 0 := by
    linarith
  exact
    le_trans
      (mul_nonpos_of_nonpos_of_nonneg hcoeff (sq_nonneg ‖x‖))
      hnonneg

/-- Exact anti-circularity classification of the #271 terminal certificate:
it is logically equivalent to Mathlib's RH.  This theorem does not establish
either side unconditionally. -/
theorem cofinalCanonicalArithmeticCertificates_iff_riemannHypothesis :
    CofinalCanonicalArithmeticCertificates ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_cofinalCanonicalArithmeticCertificates,
    cofinalCanonicalArithmeticCertificates_of_riemannHypothesis⟩

end Zeta23.ExceptionalZero

#print axioms Zeta23.ExceptionalZero.cofinalCanonicalArithmeticCertificates_of_riemannHypothesis
#print axioms Zeta23.ExceptionalZero.cofinalCanonicalArithmeticCertificates_iff_riemannHypothesis
