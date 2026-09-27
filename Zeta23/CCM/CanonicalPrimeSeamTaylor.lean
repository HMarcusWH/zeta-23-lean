import Zeta23.CCM.CanonicalSourceMomentJets
import Zeta23.CCM.CanonicalSourceEnergyJets

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A2: exact parity source germs

These are fixed-vector source-coordinate statements; they are not
moving-ground aperture derivative theorems.
-/

theorem boundaryFlat_sourceAtom_seventh_jet_package
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    (∀ j : ℕ, 1 ≤ j → j ≤ 6 →
      iteratedDeriv j (sourceAtomRealEnergy K x) 0 = 0) ∧
    iteratedDeriv 7 (sourceAtomRealEnergy K x) 0 =
      -2 * (2 * Real.pi) ^ 6 *
        Complex.normSq
          (centeredMoment K 3
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) := by
  constructor
  · exact sourceAtomRealEnergy_boundaryFlat_jets_through_six K x hflat
  · exact iteratedDeriv_seven_sourceAtomRealEnergy_eq_moment_three K x hflat

theorem evenBoundaryFlat_sourceAtom_ninth_jet_package
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
    (heven :
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
        evenCoefficientSubspace K) :
    (∀ j : ℕ, 1 ≤ j → j ≤ 8 →
      iteratedDeriv j (sourceAtomRealEnergy K x) 0 = 0) ∧
    iteratedDeriv 9 (sourceAtomRealEnergy K x) 0 =
      2 * (2 * Real.pi) ^ 8 *
        Complex.normSq
          (centeredMoment K 4
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) := by
  constructor
  · exact sourceAtomRealEnergy_even_boundaryFlat_jets_through_eight
      K x hflat heven
  · exact
      iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
        K x hflat heven

/-- Generic remainder predicate used by the research/obligation layer.  No
instance for the canonical source is asserted here. -/
def HasNinthOrderRemainder (f : ℝ → ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧
    ∀ ω : ℝ, |ω| ≤ 1 →
      |f ω - (iteratedDeriv 9 f 0 / ((Nat.factorial 9 : ℕ) : ℝ)) * ω ^ 9| ≤
        C * |ω| ^ 10

end Zeta23.CCM

#print axioms Zeta23.CCM.boundaryFlat_sourceAtom_seventh_jet_package
#print axioms Zeta23.CCM.evenBoundaryFlat_sourceAtom_ninth_jet_package
