import Zeta23.CCM.FirstCrossingSourceDynamics
import Zeta23.CCM.CanonicalSourceMomentJets

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#279 lifted first-crossing features

This module exposes a small theorem-backed feature surface for the new
contact-quotient research lane. It does not assert that the feature surface is
globally complete; it is only the exact surface required by the currently
registered first-crossing and source-jet identities.
-/

structure RegularEndpointLiftedFeatures where
  endpointRe : ℝ
  shellEnergy : ℝ
  predecessorEnergy : ℝ

noncomputable def regularEndpointLiftedFeatures
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) :
    RegularEndpointLiftedFeatures where
  endpointRe :=
    Complex.re (regularZeroShiftSchurEndpoint p L N hreg)
  shellEnergy :=
    cubicShellRealEnergy p L N
  predecessorEnergy :=
    intrinsicPredecessorRealEnergy p L N
      (regularCubicZeroShiftPreimage p L N hreg)

theorem regularEndpointLiftedFeatures_relation
    (p : ReversalParity) (L : ℝ) (N : ℕ)
    (hreg : IntrinsicPredecessorRegular p L N) :
    (regularEndpointLiftedFeatures p L N hreg).endpointRe =
      (regularEndpointLiftedFeatures p L N hreg).shellEnergy -
        (regularEndpointLiftedFeatures p L N hreg).predecessorEnergy := by
  simpa [regularEndpointLiftedFeatures] using
    regularZeroShiftSchurEndpoint_re_eq_shell_sub_predecessor
      p L N hreg

structure EvenBoundaryFlatMomentFourFeatures where
  ninthJet : ℝ
  momentFourNormSq : ℝ

noncomputable def evenBoundaryFlatMomentFourFeatures
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    EvenBoundaryFlatMomentFourFeatures where
  ninthJet := iteratedDeriv 9 (sourceAtomRealEnergy K x) 0
  momentFourNormSq :=
    Complex.normSq
      (centeredMoment K 4
        ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))

theorem evenBoundaryFlatMomentFourFeatures_relation
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
    (heven :
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
        evenCoefficientSubspace K) :
    (evenBoundaryFlatMomentFourFeatures K x).ninthJet =
      2 * (2 * Real.pi) ^ 8 *
        (evenBoundaryFlatMomentFourFeatures K x).momentFourNormSq := by
  simpa [evenBoundaryFlatMomentFourFeatures] using
    iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
      K x hflat heven

end Zeta23.CCM

#print axioms Zeta23.CCM.regularEndpointLiftedFeatures_relation
#print axioms Zeta23.CCM.evenBoundaryFlatMomentFourFeatures_relation
