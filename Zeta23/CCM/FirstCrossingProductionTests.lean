import Zeta23.CCM.FirstCrossingProductionArithmetic
import Zeta23.CCM.DictionarySmoothCoreBridge
import Zeta23.CCM.CanonicalQuadraticNormalSourceFunctional
import Zeta23.CCM.ProductionWeightedTestCalculus
import Zeta23.CCM.ProductionWeightedGlobalTests

noncomputable section

namespace Zeta23.CCM

open Complex MeasureTheory Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#281 production test authority

PR #281 deliberately exposes a value-level physical RHS rather than pretending
that it is an unrestricted linear functional.  This module records the exact
admissibility/authority contract required by the generated-contact bridge.

The global explicit-formula test and the positive-half physical test are kept
separate because the physical RHS only samples the latter on [0,L] and at
positive prime logarithms.
-/

/-- Exact physical-RHS authority for one global test / positive-half physical
test pair.  This is stronger than merely declaring an integral to exist. -/
def ProductionPhysicalTestAuthority
    (L : ℝ) (globalTest physicalTest : ℝ → ℂ) : Prop :=
  (1 / 2 : ℂ) * Zeta23.EF.literatureRHS globalTest =
    productionArithmeticComplexValue L physicalTest

/-- Full contact-test admissibility: theorem-authoritative explicit-formula
input plus its exact physical RHS realization. -/
structure ProductionContactTestAdmissible
    (L : ℝ) (globalTest physicalTest : ℝ → ℂ) : Prop where
  contDiff_two : ContDiff ℝ 2 globalTest
  compact_support : HasCompactSupport globalTest
  physical_authority : ProductionPhysicalTestAuthority L globalTest physicalTest

/-- The already-merged quadratic-normal source has exact literature-RHS to
physical-RHS authority without retyping any channel normalization. -/
theorem quadraticNormalSource_has_physical_authority
    {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 1 ≤ K)
    (v : euclideanEvenBoundaryFlatSubspace K) :
    ProductionPhysicalTestAuthority L
      (canonicalSourcePhysicalLift L (quadraticNormalSourceAtom K v))
      (productionQuadraticNormalPhysicalSource L K v) := by
  unfold ProductionPhysicalTestAuthority
  have hfunctional :=
    canonicalQuadraticNormalSourceFunctional_eq_sourceKernelRHS
      hL K hK v
  unfold canonicalQuadraticNormalSourceFunctional at hfunctional
  have hproduction :=
    productionArithmeticComplexValue_quadraticNormal_eq_sourceKernelRHS
      L K v
  exact hfunctional.trans hproduction.symm

/-- Authority is stable under equality of either test representation. -/
theorem ProductionPhysicalTestAuthority.congr
    {L : ℝ} {g₁ g₂ p₁ p₂ : ℝ → ℂ}
    (h : ProductionPhysicalTestAuthority L g₁ p₁)
    (hg : g₁ = g₂) (hp : p₁ = p₂) :
    ProductionPhysicalTestAuthority L g₂ p₂ := by
  simpa [hg, hp] using h

/-- Current production derivative tests are admitted by the versioned weighted
calculus.  This theorem is a compatibility export for downstream callers; it
does not turn the production functional into an unrestricted linear map. -/
theorem productionContactDerivativeTests_admissible
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    ProductionWeightedPhysicalAdmissible L
        (productionFirstDerivativePhysicalTest L K z) ∧
      ProductionWeightedPhysicalAdmissible L
        (productionSecondDerivativePhysicalTest L K z) ∧
      ProductionWeightedPhysicalAdmissible L
        (productionMixedDerivativePhysicalTest L K z w) :=
  production_derivative_tests_admissible hL K z w


/-- The complete F02 production derivative-test package.  Unlike the historical
authority record, no caller supplies an explicit-formula equality: all three
authorities are consequences of the compact even global lifts. -/
theorem productionContactDerivativeTests_full_admissible
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    ProductionWeightedTestAdmissible L
        (productionFirstDerivativeGlobalTest L K z)
        (productionFirstDerivativePhysicalTest L K z) ∧
      ProductionWeightedTestAdmissible L
        (productionSecondDerivativeGlobalTest L K z)
        (productionSecondDerivativePhysicalTest L K z) ∧
      ProductionWeightedTestAdmissible L
        (productionMixedDerivativeGlobalTest L K z w)
        (productionMixedDerivativePhysicalTest L K z w) :=
  productionDerivativeWeightedTests_admissible hL K z w

/-- Compatibility with the pre-#283 authority proposition. -/
theorem productionFirstDerivative_has_physical_authority
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    ProductionPhysicalTestAuthority L
      (productionFirstDerivativeGlobalTest L K z)
      (fun t => (productionFirstDerivativePhysicalTest L K z t : ℂ)) :=
  productionFirstDerivativeTest_authority hL K z

theorem productionSecondDerivative_has_physical_authority
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    ProductionPhysicalTestAuthority L
      (productionSecondDerivativeGlobalTest L K z)
      (fun t => (productionSecondDerivativePhysicalTest L K z t : ℂ)) :=
  productionSecondDerivativeTest_authority hL K z

theorem productionMixedDerivative_has_physical_authority
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    ProductionPhysicalTestAuthority L
      (productionMixedDerivativeGlobalTest L K z w)
      (fun t => (productionMixedDerivativePhysicalTest L K z w t : ℂ)) :=
  productionMixedDerivativeTest_authority hL K z w

end Zeta23.CCM

#print axioms Zeta23.CCM.quadraticNormalSource_has_physical_authority
#print axioms Zeta23.CCM.productionContactDerivativeTests_admissible
#print axioms Zeta23.CCM.productionContactDerivativeTests_full_admissible
#print axioms Zeta23.CCM.productionFirstDerivative_has_physical_authority
#print axioms Zeta23.CCM.productionSecondDerivative_has_physical_authority
#print axioms Zeta23.CCM.productionMixedDerivative_has_physical_authority
