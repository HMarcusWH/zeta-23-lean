import Zeta23.CCM.CubicSecularRealPhase
import Zeta23.CCM.RegularFirstBadSourceKernelCompatibility
import Zeta23.CCM.RegularFirstBadParitySourceMomentRigidity
import Zeta23.CCM.SourceExplicitCubicDefect

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Retained source-kernel real phase

The selected-even retained negative-root trial is the canonical E3-A cubic
trial.  Once the secular root is known, canonical conjugation normalization
forces that trial to be coordinatewise real.  The exact quadratic-normal source
moment is then real because both the canonical source matrix and the quadratic
normal are real.

Consequently the post-#235 compatibility law depends on one real source scalar
rather than an unconstrained complex phase.

No sign of that real scalar, no strict deficit/excess sign, no simultaneous-bad
exclusion, and no RH theorem is proved here.
-/

/-- The quadratic normal itself has real coordinates. -/
theorem centeredQuadraticNormal_conj_fixed
    (K : ℕ) :
    euclideanConj (centeredQuadraticNormal K) =
      centeredQuadraticNormal K := by
  let p0 := centeredPowerVector K 0
  let p2 := centeredPowerVector K 2
  let mu : ℂ := inner ℂ p0 p2 / inner ℂ p0 p0
  have hp0 : euclideanConj p0 = p0 := by
    simpa [p0] using centeredPowerVector_conj_fixed K 0
  have hp2 : euclideanConj p2 = p2 := by
    simpa [p2] using centeredPowerVector_conj_fixed K 2
  have h02 := inner_euclideanConj p0 p2
  rw [hp0, hp2] at h02
  have h00 := inner_euclideanConj p0 p0
  rw [hp0] at h00
  have hmu : star mu = mu := by
    dsimp [mu]
    rw [star_div₀, ← h02, ← h00]
  change euclideanConj (p2 - mu • p0) = p2 - mu • p0
  rw [euclideanConj_sub, euclideanConj_smul, hp0, hp2, hmu]

/-- If an even boundary-flat vector is conjugation-fixed, its exact production
source moment is real. -/
theorem evenQuadraticSourceMoment_star_eq_of_conj_fixed
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (hv : parityConj .even K v = v) :
    star (evenQuadraticSourceMoment L K v) =
      evenQuadraticSourceMoment L K v := by
  let n2 := centeredQuadraticNormal K
  let x : EuclideanSpace ℂ (Fin (2 * K + 1)) :=
    (v : EuclideanSpace ℂ (Fin (2 * K + 1)))
  let Mx : EuclideanSpace ℂ (Fin (2 * K + 1)) :=
    (canonicalSourceMatrix L K).toEuclideanLin x
  have hn2 : euclideanConj n2 = n2 := by
    simpa [n2] using centeredQuadraticNormal_conj_fixed K
  have hx : euclideanConj x = x := by
    have h := congrArg Subtype.val hv
    simpa [x, parityConj] using h
  have hMx : euclideanConj Mx = Mx := by
    have h := canonicalSourceMatrix_toEuclideanLin_conj L K x
    rw [hx] at h
    exact h.symm
  have hnum := inner_euclideanConj n2 Mx
  rw [hn2, hMx] at hnum
  have hden := inner_euclideanConj n2 n2
  rw [hn2] at hden
  unfold evenQuadraticSourceMoment
  change
    star (inner ℂ n2 Mx / inner ℂ n2 n2) =
      inner ℂ n2 Mx / inner ℂ n2 n2
  rw [star_div₀, ← hnum, ← hden]

/-- The retained selected-even cubic trial has canonical real phase. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial_conj_fixed_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    parityConj .even (c.firstBad.Nstar + 1) c.evenShiftedTrial =
      c.evenShiftedTrial := by
  have hroot := c.evenSecularRoot_of_even hp
  change
    parityConj .even (c.firstBad.Nstar + 1)
        (cubicSecularTrialVector
          .even c.firstBad.L_pos c.firstBad.Nstar
          (c.firstBad.predecessorNonnegative_anyParity .even)
          c.lam c.lam_neg) =
      cubicSecularTrialVector
        .even c.firstBad.L_pos c.firstBad.Nstar
        (c.firstBad.predecessorNonnegative_anyParity .even)
        c.lam c.lam_neg
  exact
    cubicSecularTrialVector_conj_fixed_of_secularRoot
      .even c.firstBad.L_pos c.firstBad.Nstar
      c.firstBad.one_le_Nstar
      (c.firstBad.predecessorNonnegative_anyParity .even)
      c.lam c.lam_neg hroot

/-- The retained exact production source moment is real on the selected-even
branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.star_evenShiftedSourceMoment_eq_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    star
        (explicitCanonicalSourceMoment
          c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial) =
      explicitCanonicalSourceMoment
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial := by
  have hreal :=
    evenQuadraticSourceMoment_star_eq_of_conj_fixed
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
      (c.evenShiftedTrial_conj_fixed_of_even hp)
  have hbridge :=
    evenQuadraticSourceMoment_eq_explicitCanonicalSourceMoment
      c.firstBad.L_pos (c.firstBad.Nstar + 1) c.evenShiftedTrial
  rw [hbridge] at hreal
  exact hreal

/-- The exact retained source-coordinate kernel is real on the selected-even
branch. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.star_evenShiftedSourceKernel_eq_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    star
        (quadraticNormalSourceKernelRHS
          c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial) =
      quadraticNormalSourceKernelRHS
        c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial := by
  have h := c.star_evenShiftedSourceMoment_eq_of_even hp
  rw [c.evenShiftedExplicitCanonicalSourceMoment_eq_sourceKernelRHS] at h
  exact h

/-- Human-facing imaginary-part form of the retained source-kernel reality
theorem. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceKernel_im_eq_zero_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    Complex.im
        (quadraticNormalSourceKernelRHS
          c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial) = 0 := by
  let S :=
    quadraticNormalSourceKernelRHS
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial
  have hstar : star S = S := by
    simpa [S] using c.star_evenShiftedSourceKernel_eq_of_even hp
  have him := congrArg Complex.im hstar
  simpa [S] using him

/-- The single real source scalar left after canonical phase collapse. -/
def
    RegularCellMinimalNegativeEnergyCertificate.retainedRealSourceScalar
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q) : ℝ :=
  Complex.re
    (quadraticNormalSourceKernelRHS
      c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial)

/-- On the selected-even branch the complex source norm is exactly the square
of the one surviving real source scalar. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernel_normSq_eq_realScalar_sq_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    Complex.normSq
        (quadraticNormalSourceKernelRHS
          c.firstBad.L (c.firstBad.Nstar + 1) c.evenShiftedTrial) =
      c.retainedRealSourceScalar ^ 2 := by
  have him := c.evenShiftedSourceKernel_im_eq_zero_of_even hp
  simp [Complex.normSq, retainedRealSourceScalar, him]

/-- The post-#235 sharp excess rewritten with one real source scalar. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernelSharpExcess_eq_realScalar_of_even
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even) :
    c.retainedSourceKernelSharpExcess =
      c.retainedSourceKernelCenterDeficit ^ 2 -
        c.retainedRealSourceScalar ^ 2 *
          c.retainedSourceKernelSharpRadiusSq := by
  unfold RegularCellMinimalNegativeEnergyCertificate.retainedSourceKernelSharpExcess
  rw [c.retainedSourceKernel_normSq_eq_realScalar_sq_of_even hp]
  rfl

/-- One-real-scalar form of the #235 selected-even / odd-good compatibility
law. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.retainedRealSourceDeficit_or_radius_of_even_of_not_oddBad
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hodd :
      ¬ ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1)) :
    c.retainedSourceKernelCenterDeficit ≤ 0 ∨
      c.retainedSourceKernelCenterDeficit ^ 2 ≤
        c.retainedRealSourceScalar ^ 2 *
          c.retainedSourceKernelSharpRadiusSq := by
  have h :=
    c.retainedSourceKernelDeficit_or_excess_nonpos_of_even_of_not_oddBad
      hp hodd
  rcases h with hD | hE
  · exact Or.inl hD
  · right
    rw [c.retainedSourceKernelSharpExcess_eq_realScalar_of_even hp] at hE
    exact sub_nonpos.mp hE

/-- Flagship contradiction interface after phase collapse.

Future arithmetic need only force a positive center deficit and place its
square strictly outside the one-real-source sharp radius. -/
theorem
    RegularCellMinimalNegativeEnergyCertificate.oddBad_of_even_of_realSourceDeficit_pos_of_radius_gap
    {Q : ℕ}
    (c : RegularCellMinimalNegativeEnergyCertificate Q)
    (hp : c.firstBad.p = ReversalParity.even)
    (hD : 0 < c.retainedSourceKernelCenterDeficit)
    (hgap :
      c.retainedRealSourceScalar ^ 2 *
          c.retainedSourceKernelSharpRadiusSq <
        c.retainedSourceKernelCenterDeficit ^ 2) :
    ParityBad .odd c.firstBad.L (c.firstBad.Nstar + 1) := by
  by_contra hodd
  have h :=
    c.retainedRealSourceDeficit_or_radius_of_even_of_not_oddBad hp hodd
  rcases h with hD' | hrad
  · exact (not_lt_of_ge hD') hD
  · exact (not_lt_of_ge hrad) hgap

end Zeta23.CCM

#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedTrial_conj_fixed_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.star_evenShiftedSourceKernel_eq_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.evenShiftedSourceKernel_im_eq_zero_of_even
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.retainedRealSourceDeficit_or_radius_of_even_of_not_oddBad
#print axioms Zeta23.CCM.RegularCellMinimalNegativeEnergyCertificate.oddBad_of_even_of_realSourceDeficit_pos_of_radius_gap
