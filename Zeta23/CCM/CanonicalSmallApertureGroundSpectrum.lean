import Zeta23.CCM.CanonicalArchDensityClosure
import Zeta23.CCM.GlobalParityBottomSpectrum

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#275 small-aperture legal ground spectrum

PR #275 proves full-space canonical coercivity on the frozen tiny-aperture
range.  This module pushes that theorem into the exact legal spectral
coordinates introduced by the #247/#268 ground-spectrum stack.

The result is deliberately restricted to the nontrivial successor regime
`N + 1` with `1 <= N`, where the complete boundary-flat carrier and both
parity carriers are nontrivial.

No RH premise, bad-state premise, ground simplicity assumption, aperture
propagation statement, or prime-power seam statement is used.
-/

/-- The #275 full-space coercive base raises the complete legal boundary-flat
Rayleigh bottom to at least one at every nontrivial successor size. -/
theorem one_le_boundaryFlatRayleighBottom_succ_of_smallAperture
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512)
    (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ boundaryFlatRayleighBottom L (N + 1) := by
  have hfin :
      0 < Module.finrank ℂ (euclideanBoundaryFlatSubspace (N + 1)) := by
    rw [finrank_euclideanBoundaryFlatSubspace (N + 1) (by omega)]
    omega
  letI : Nontrivial (euclideanBoundaryFlatSubspace (N + 1)) :=
    Module.nontrivial_of_finrank_pos hfin
  letI : Nonempty
      {z : euclideanBoundaryFlatSubspace (N + 1) // z ≠ 0} := by
    obtain ⟨z, hz⟩ :
        ∃ z : euclideanBoundaryFlatSubspace (N + 1), z ≠ 0 :=
      exists_ne 0
    exact ⟨⟨z, hz⟩⟩
  unfold boundaryFlatRayleighBottom
  refine le_ciInf fun z => ?_
  let x : EuclideanSpace ℂ (Fin (2 * (N + 1) + 1)) :=
    (z : euclideanBoundaryFlatSubspace (N + 1))
  have hcoerc :=
    canonicalSmallApertureCoercivity_proved
      L hL hsmall (N + 1) x
  have hmatrix :
      ‖x‖ ^ 2 ≤
        Complex.re
          (inner ℂ
            ((canonicalSourceMatrix L (N + 1)).toEuclideanLin x)
            x) := by
    rw [← matrixRealEnergy_eq_re_inner_apply_self]
    exact hcoerc
  have hden :
      0 < ‖(z : euclideanBoundaryFlatSubspace (N + 1))‖ ^ 2 := by
    simpa only [sq_pos_iff, norm_ne_zero_iff] using z.property
  rw [le_div_iff₀ hden]
  simpa [x] using hmatrix

/-- The actual complete legal successor ground used by the first-contact
programme inherits the same unit lower bound. -/
theorem one_le_globalParitySuccessorBottom_of_smallAperture
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512)
    (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ globalParitySuccessorBottom L N := by
  have hbf :=
    one_le_boundaryFlatRayleighBottom_succ_of_smallAperture
      hL hsmall N hN
  rw [(canonicalCarrierBottom_hierarchy L N hN).2.2] at hbf
  exact hbf

/-- Each individual successor parity ground is at least one on the same
small-aperture range.  No parity selection or simplicity assumption is needed. -/
theorem one_le_parityRayleighBottom_succ_of_smallAperture
    (p : ReversalParity)
    {L : ℝ} (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512)
    (N : ℕ) (hN : 1 ≤ N) :
    1 ≤ parityRayleighBottom p L (N + 1) := by
  have hglobal :=
    one_le_globalParitySuccessorBottom_of_smallAperture
      hL hsmall N hN
  cases p with
  | even =>
      exact le_trans hglobal (globalParitySuccessorBottom_le_even L N)
  | odd =>
      exact le_trans hglobal (globalParitySuccessorBottom_le_odd L N)

end Zeta23.CCM

#print axioms Zeta23.CCM.one_le_boundaryFlatRayleighBottom_succ_of_smallAperture
#print axioms Zeta23.CCM.one_le_globalParitySuccessorBottom_of_smallAperture
#print axioms Zeta23.CCM.one_le_parityRayleighBottom_succ_of_smallAperture
