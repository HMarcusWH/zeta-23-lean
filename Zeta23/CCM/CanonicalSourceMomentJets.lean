import Zeta23.CCM.CanonicalSourceEnergyJets

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB04A: production moment jets

This module exposes the first surviving odd endpoint jet of the exact production
`sourceAtomRealEnergy` in terms of the first centered moment not killed by the
coefficient vector.  It is a strict downstream extension of the #157 complex
production D-transport and endpoint-jet layer.

No sign of a Riesz primitive, smoothed integrand, complete transformed channel,
or RH-directed quantity is asserted here.
-/

/-- Exact first endpoint jet of the genuine complex production source energy.
The real and imaginary coordinate contractions combine into the squared complex
coefficient sum. -/
theorem iteratedDeriv_one_sourceAtomRealEnergy_eq_two_normSq_sum
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    iteratedDeriv 1 (sourceAtomRealEnergy K x) 0 =
      2 * Complex.normSq
        (∑ i, ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i) := by
  let u := (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x
  rw [iteratedDeriv_one]
  rw [(hasDerivAt_sourceAtomRealEnergy_transport K x 0).deriv]
  unfold sourceAtomRealEnergyDerivative
  rw [sourceContractRealDerivative_zero_eq_two_coefficientSum_sq,
    sourceContractRealDerivative_zero_eq_two_coefficientSum_sq]
  unfold coefficientSumReal
  have hre :
      (∑ i, (u i).re) = (∑ i, u i).re := by
    change (∑ i, Complex.reCLM (u i)) = Complex.reCLM (∑ i, u i)
    rw [map_sum]
  have him :
      (∑ i, (u i).im) = (∑ i, u i).im := by
    change (∑ i, Complex.imCLM (u i)) = Complex.imCLM (∑ i, u i)
    rw [map_sum]
  change
    2 * (∑ i, (u i).re) ^ 2 + 2 * (∑ i, (u i).im) ^ 2 =
      2 * Complex.normSq (∑ i, u i)
  rw [hre, him, Complex.normSq_apply]
  ring

/-- If the first `r` centered moments vanish, the first odd jet left after `r`
applications of production D-transport is exactly the norm square of `M_r`.
The coefficient is deliberately kept in the recurrence-native form
`(-(2*pi)^2)^r`. -/
theorem iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix
    (K r : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hprefix :
      ∀ k : ℕ, k < r →
        centeredMoment K k
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) = 0) :
    iteratedDeriv (2 * r + 1) (sourceAtomRealEnergy K x) 0 =
      2 * (-(2 * Real.pi) ^ 2) ^ r *
        Complex.normSq
          (centeredMoment K r
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) := by
  induction r generalizing x with
  | zero =>
      simpa using
        iteratedDeriv_one_sourceAtomRealEnergy_eq_two_normSq_sum K x
  | succ r ih =>
      have hsum :
          ∑ i, ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) i = 0 := by
        rw [← centeredMoment_zero_eq_sum]
        exact hprefix 0 (by omega)
      have hprefixD :
          ∀ k : ℕ, k < r →
            centeredMoment K k
              ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
                (sourceIndexAction K x)) = 0 := by
        intro k hk
        rw [centeredMoment_sourceIndexAction]
        exact hprefix (k + 1) (by omega)
      have htransport :=
        iteratedDeriv_add_two_sourceAtomRealEnergy_eq_indexAction
          K x (2 * r + 1) 0 hsum
      have hind := ih (sourceIndexAction K x) hprefixD
      rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega]
      rw [htransport, hind, centeredMoment_sourceIndexAction]
      rw [pow_succ]
      ring

/-- Boundary-flat production carriers have exact seventh endpoint jet governed
by the first unconstrained centered moment `M_3`. -/
theorem iteratedDeriv_seven_sourceAtomRealEnergy_eq_moment_three
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    iteratedDeriv 7 (sourceAtomRealEnergy K x) 0 =
      -2 * (2 * Real.pi) ^ 6 *
        Complex.normSq
          (centeredMoment K 3
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) := by
  have hprefix :
      ∀ k : ℕ, k < 3 →
        centeredMoment K k
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) = 0 := by
    intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hk' with rfl | rfl | rfl
    · exact hflat.1
    · exact hflat.2.1
    · exact hflat.2.2
  have h :=
    iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix
      K 3 x hprefix
  convert h using 1 <;> ring

/-- On the even boundary-flat sector, parity kills `M_3`, so the exact ninth
endpoint jet is governed by the first remaining moment `M_4`. -/
theorem iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
    (heven :
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
        evenCoefficientSubspace K) :
    iteratedDeriv 9 (sourceAtomRealEnergy K x) 0 =
      2 * (2 * Real.pi) ^ 8 *
        Complex.normSq
          (centeredMoment K 4
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) := by
  have hprefix :
      ∀ k : ℕ, k < 4 →
        centeredMoment K k
          ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) = 0 := by
    intro k hk
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl
    · exact hflat.1
    · exact hflat.2.1
    · exact hflat.2.2
    · exact centeredMoment_three_eq_zero_of_even heven
  have h :=
    iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix
      K 4 x hprefix
  convert h using 1 <;> ring

end Zeta23.CCM

#print axioms Zeta23.CCM.iteratedDeriv_one_sourceAtomRealEnergy_eq_two_normSq_sum
#print axioms Zeta23.CCM.iteratedDeriv_odd_sourceAtomRealEnergy_eq_moment_normSq_of_prefix
#print axioms Zeta23.CCM.iteratedDeriv_seven_sourceAtomRealEnergy_eq_moment_three
#print axioms Zeta23.CCM.iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
