import Zeta23.CCM.RegularFirstBadCanonicalEnergy
import Zeta23.CCM.SecularRootRieszBoundary
import Zeta23.CCM.CrossParitySecularTransfer
import Zeta23.CCM.SourceMomentDecomposition
import Zeta23.CCM.CubicExplicitSecular

noncomputable section

namespace Zeta23.CCM

open Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB04B: retained shifted-root cross-parity Riesz obstruction

This module composes the retained cell-minimal first-bad certificate with the
shifted secular-root Riesz layer and the already-proved cross-parity source
transfer.  In the even selected branch, one and the same canonical negative
shifted trial therefore carries:

* strict complete Riesz-8 negativity;
* the exact #159 Riesz-9 / `M_4` boundary inequality;
* either opposite-parity badness at the same successor size or a nonzero exact
  production source moment.

The zero-shift trial retained by the certificate is not identified with the
shifted secular trial.  No sign/nonzeroness of the Riesz endpoint scalar is
assumed, no overlap factor is divided out, no source-moment-to-`M_4` implication
is asserted, and no negative-root exclusion or RH theorem is claimed.
-/

/-- Canonical even shifted trial at the negative root retained by the complete
first-bad certificate, using the whole-cell any-parity predecessor bound. -/
def RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) :
    euclideanEvenBoundaryFlatSubspace (c.firstBad.Nstar + 1) :=
  cubicSecularTrialVector
    .even c.firstBad.L_pos c.firstBad.Nstar
    (c.firstBad.predecessorNonnegative_anyParity .even)
    c.lam c.lam_neg

/-- If the retained selected first-bad parity is even, the retained explicit
Schur root is also the quotient secular root built from the canonical
whole-cell even predecessor bound.  The bridge passes through a genuine
`lam`-eigenmode, avoiding any equality requirement between proof-valued
predecessor-nonnegativity arguments. -/
theorem RegularCellMinimalNegativeEnergyCertificate.evenSecularRoot_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    cubicSecularScalar
      .even c.firstBad.L_pos c.firstBad.Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      c.lam c.lam_neg = 0 := by
  have hexSelected :
      ∃ v : euclideanParityBoundaryFlatSubspace c.firstBad.p
          (c.firstBad.Nstar + 1),
        v ≠ 0 ∧
          parityCompressedCanonical c.firstBad.p c.firstBad.L
              (c.firstBad.Nstar + 1) v =
            (c.lam : ℂ) • v :=
    (cubicExplicitSchurScalar_eq_zero_iff_exists_eigenmode
      c.firstBad.p c.firstBad.L_pos c.firstBad.Nstar
      c.firstBad.one_le_Nstar c.predecessorNonnegative
      c.lam c.lam_neg).mp c.explicit_root
  have hexEven :
      ∃ v : euclideanParityBoundaryFlatSubspace .even
          (c.firstBad.Nstar + 1),
        v ≠ 0 ∧
          parityCompressedCanonical .even c.firstBad.L
              (c.firstBad.Nstar + 1) v =
            (c.lam : ℂ) • v := by
    rw [← hp]
    exact hexSelected
  exact
    (cubicSecularScalar_eq_zero_iff_exists_eigenmode
      .even c.firstBad.L_pos c.firstBad.Nstar
      c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      c.lam c.lam_neg).mpr hexEven

/-- The canonical even shifted trial at a retained even first-bad root has
strictly negative complete order-eight Riesz energy. -/
theorem RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNeg
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    canonicalRieszSourceChannelEnergy
        c.firstBad.L 8 (c.firstBad.Nstar + 1)
        (c.evenShiftedTrial :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) < 0 := by
  have hroot := c.evenSecularRoot_of_even hp
  simpa [RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial] using
    canonicalRieszSourceChannelEnergy_eight_neg_of_even_secular_root
      c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      c.lam c.lam_neg hroot

/-- The same retained even shifted trial satisfies the exact #159 order-nine
upper bound by the negative `M_4` boundary quantity, without any endpoint-scalar
sign assumption. -/
theorem RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_momentFourBoundary
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    canonicalRieszSourceChannelEnergy
        c.firstBad.L 9 (c.firstBad.Nstar + 1)
        (c.evenShiftedTrial :
          EuclideanSpace ℂ (Fin (2 * (c.firstBad.Nstar + 1) + 1))) <
      -(2 * (2 * Real.pi) ^ 8 *
        canonicalPolePrimeRieszEndpointScalar c.firstBad.L 8 *
        Complex.normSq
          (centeredMoment (c.firstBad.Nstar + 1) 4
            ((EuclideanSpace.equiv
              (Fin (2 * (c.firstBad.Nstar + 1) + 1)) ℂ)
              (c.evenShiftedTrial :
                EuclideanSpace ℂ
                  (Fin (2 * (c.firstBad.Nstar + 1) + 1)))))) := by
  have hroot := c.evenSecularRoot_of_even hp
  simpa [RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial] using
    canonicalRieszSourceChannelEnergy_nine_lt_neg_momentFourBoundary_of_even_secular_root
      c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      c.lam c.lam_neg hroot

/-- At a retained even first-bad root, the opposite-parity secular scalar is
exactly the cross-parity Gamma coefficient times the exact production source
moment of the same even shifted trial. -/
theorem RegularCellMinimalNegativeEnergyCertificate.oddSecularScalar_eq_gamma_mul_explicitSource_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    cubicSecularScalar
        .odd c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg =
      crossParitySecularGamma
          c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .odd)
          c.lam c.lam_neg *
        explicitCanonicalSourceMoment
          c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial := by
  have hroot := c.evenSecularRoot_of_even hp
  have htransfer :=
    cubicSecularScalar_crossParity_source_transfer
      c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg
  rw [hroot] at htransfer
  simp only [mul_zero, zero_add] at htransfer
  have hsource :=
    evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment
      c.firstBad.L_pos (c.firstBad.Nstar + 1)
      (cubicSecularTrialVector
        .even c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .even)
        c.lam c.lam_neg)
  rw [hsource] at htransfer
  simpa [RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial] using htransfer

/-- If the opposite odd successor sector is good, the exact production source
moment on the retained even shifted root cannot vanish.  No division by the
Gamma/overlap factor is used. -/
theorem RegularCellMinimalNegativeEnergyCertificate.explicitSourceMoment_ne_zero_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial ≠ 0 := by
  have hFodd :
      cubicSecularScalar
          .odd c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .odd)
          c.lam c.lam_neg ≠ 0 :=
    cubicSecularScalar_ne_zero_of_not_parityBad
      .odd c.firstBad.L_pos c.firstBad.Nstar c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .odd)
      c.lam c.lam_neg hodd
  have htransfer := c.oddSecularScalar_eq_gamma_mul_explicitSource_of_even hp
  intro hsource
  apply hFodd
  calc
    cubicSecularScalar
        .odd c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .odd)
        c.lam c.lam_neg =
      crossParitySecularGamma
          c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .odd)
          c.lam c.lam_neg *
        explicitCanonicalSourceMoment
          c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial := htransfer
    _ = 0 := by rw [hsource, mul_zero]

/-- Headline retained obstruction: an even selected first-bad state forces
either simultaneous odd badness at the same successor size or a nonzero exact
production source defect on the same canonical even negative-root trial that
carries the Riesz obstruction. -/
theorem RegularCellMinimalNegativeEnergyCertificate.oddBad_or_explicitSourceMoment_ne_zero_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1) ∨
      explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial ≠ 0 := by
  by_cases hodd : ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)
  · exact Or.inl hodd
  · exact Or.inr
      (c.explicitSourceMoment_ne_zero_of_even_of_not_oddBad hp hodd)

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenSecularRoot_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszEightNeg
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedRieszNine_lt_neg_momentFourBoundary
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddSecularScalar_eq_gamma_mul_explicitSource_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.explicitSourceMoment_ne_zero_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddBad_or_explicitSourceMoment_ne_zero_of_even
