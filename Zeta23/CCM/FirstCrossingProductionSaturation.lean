import Zeta23.CCM.FirstCrossingProductionArithmetic
import Zeta23.CCM.FirstCrossingOptimizedCurvatureAlgebra

noncomputable section

namespace Zeta23.CCM

open Complex Matrix Set
open scoped BigOperators ComplexConjugate

/-!
# Post-#280 production saturation frontier

This file names the exact arithmetic quantity that the handoff and PR #280
leave unresolved.

The proved PR #280 algebra gives an `OptimizedCurvatureRemainderBalance`.
Here its scalar remainder is specialized to the exact complete physical
pole/archimedean/von-Mangoldt evaluation from
`FirstCrossingProductionArithmetic`.

The proposition `ProductionOptimizedCurvatureBridge` is deliberately an
interface, not a theorem: deriving it from the actual aperture derivatives,
response vector, and admissibility hypotheses remains OPEN. This file therefore
moves the formal surface to the frontier without claiming equality rigidity or
RH closure.
-/

/-- Exact production saturation gap for one real handoff remainder source. -/
def productionSaturationGap
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (remainderSource : ℝ → ℝ) : ℝ :=
  productionArithmeticRealValue L remainderSource -
    (2 * Real.pi) ^ 2 / L ^ 2 *
      productionStrictEvenSourceValue L K v

/-- The remaining derivative/admissibility bridge required to identify the
actual optimized curvature with the exact production arithmetic gap. -/
def ProductionOptimizedCurvatureBridge
    (L : ℝ) (K : ℕ)
    (v : euclideanEvenBoundaryFlatSubspace K)
    (kappa : ℝ)
    (remainderSource : ℝ → ℝ) : Prop :=
  OptimizedCurvatureRemainderBalance
    L K v kappa (productionArithmeticRealValue L remainderSource)

/-- Once the production bridge is available, the named saturation gap is
exactly the optimized curvature. -/
theorem productionSaturationGap_eq_kappa_of_bridge
    {L : ℝ} (hL : 0 < L)
    {K : ℕ} (hK : 1 ≤ K)
    {v : euclideanEvenBoundaryFlatSubspace K}
    {kappa : ℝ} {remainderSource : ℝ → ℝ}
    (hbridge :
      ProductionOptimizedCurvatureBridge
        L K v kappa remainderSource) :
    productionSaturationGap L K v remainderSource = kappa := by
  unfold ProductionOptimizedCurvatureBridge at hbridge
  unfold productionSaturationGap
  rw [productionStrictEvenSourceValue_eq_pairing hL K hK v]
  unfold OptimizedCurvatureRemainderBalance at hbridge
  linarith

/-- Production saturation is exactly equality between the physical arithmetic
remainder and the scaled strict-even source/M4 pairing, conditional only on the
still-open production derivative bridge. -/
theorem productionOptimizedCurvatureBridge_zero_iff
    {L : ℝ} {K : ℕ}
    {v : euclideanEvenBoundaryFlatSubspace K}
    {kappa : ℝ} {remainderSource : ℝ → ℝ}
    (hbridge :
      ProductionOptimizedCurvatureBridge
        L K v kappa remainderSource) :
    kappa = 0 ↔
      productionArithmeticRealValue L remainderSource =
        (2 * Real.pi) ^ 2 / L ^ 2 *
          strictEvenSourceMomentPairing L K v := by
  unfold ProductionOptimizedCurvatureBridge at hbridge
  exact optimizedCurvatureRemainderBalance_zero_iff hbridge

/-- In the strict-even zero-ground branch, a saturated production bridge forces
the exact physical arithmetic remainder value to be strictly positive. This is
not an exclusion theorem: the missing task is to show the production arithmetic
cannot attain that positive equality. -/
theorem productionArithmeticRemainder_pos_of_saturation_strictEven
    {L : ℝ} (hL : 0 < L)
    {K : ℕ} (hK : 2 ≤ K)
    {v : euclideanEvenBoundaryFlatSubspace K}
    (hvne : v ≠ 0)
    (hground : parityRayleighBottom .even L K = 0)
    (hveig : evenCompressedCanonical L K v = 0)
    (hodd : 0 < parityRayleighBottom .odd L K)
    {kappa : ℝ} {remainderSource : ℝ → ℝ}
    (hbridge :
      ProductionOptimizedCurvatureBridge
        L K v kappa remainderSource)
    (hkappa : kappa = 0) :
    0 < productionArithmeticRealValue L remainderSource := by
  unfold ProductionOptimizedCurvatureBridge at hbridge
  exact
    optimizedCurvatureRemainder_pos_of_saturation_even_zero_ground_strict
      hL hK hvne hground hveig hodd hbridge hkappa

end Zeta23.CCM

#print axioms Zeta23.CCM.productionSaturationGap_eq_kappa_of_bridge
#print axioms Zeta23.CCM.productionOptimizedCurvatureBridge_zero_iff
#print axioms Zeta23.CCM.productionArithmeticRemainder_pos_of_saturation_strictEven
