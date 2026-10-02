import Zeta23.CCM.FirstCrossingLiftedFeatures
import Zeta23.CCM.SourceDerivativeTransport
import Zeta23.CCM.MixedSourceDerivativeTransport

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

def SourceSecondDerivativeCompatibility
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) : Prop :=
  (∑ i, ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i = 0) →
    sourceAtomRealEnergySecondDerivative K x ω =
      -(2 * Real.pi) ^ 2 *
        sourceAtomRealEnergy K (sourceIndexAction K x) ω

theorem canonicalSourceSecondDerivativeCompatibility
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) :
    SourceSecondDerivativeCompatibility K x ω := by
  intro hsum
  exact sourceAtomRealEnergySecondDerivative_eq_indexAction
    K x ω hsum

def MixedSourceSecondDerivativeCompatibility
    (K : ℕ)
    (x y : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) : Prop :=
  sourcePairingCoefficientSum K x = 0 →
  sourcePairingCoefficientSum K y = 0 →
    sourceAtomPairingSecondDerivative K x y ω =
      (-(2 * Real.pi) ^ 2 : ℝ) •
        sourceAtomPairing K
          (sourceIndexAction K x) (sourceIndexAction K y) ω

theorem canonicalMixedSourceSecondDerivativeCompatibility
    (K : ℕ)
    (x y : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (ω : ℝ) :
    MixedSourceSecondDerivativeCompatibility K x y ω := by
  intro hx hy
  exact sourceAtomPairingSecondDerivative_eq_indexActions
    K x y ω hx hy

def EvenBoundaryFlatMomentFourCompatibility
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) : Prop :=
  ∀
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
    (heven :
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
        evenCoefficientSubspace K),
    (evenBoundaryFlatMomentFourFeatures K x).ninthJet =
      2 * (2 * Real.pi) ^ 8 *
        (evenBoundaryFlatMomentFourFeatures K x).momentFourNormSq

theorem canonicalEvenBoundaryFlatMomentFourCompatibility
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    EvenBoundaryFlatMomentFourCompatibility K x := by
  intro hflat heven
  exact evenBoundaryFlatMomentFourFeatures_relation
    K x hflat heven

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalSourceSecondDerivativeCompatibility
#print axioms Zeta23.CCM.canonicalMixedSourceSecondDerivativeCompatibility
#print axioms Zeta23.CCM.canonicalEvenBoundaryFlatMomentFourCompatibility
