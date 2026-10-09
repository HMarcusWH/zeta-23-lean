import Zeta23.CCM.FirstCrossingProductionRemainderAuthority
import Zeta23.CCM.ProductionPhysicalFunctionalCongruence

noncomputable section
namespace Zeta23.CCM

open Set

/-! # Final F03 value authority for the concrete remainder -/

theorem productionContactRemainderValue_eq_physicalTest
    {L : ℝ} (hL : 0 < L) (K : ℕ)
    (v w : euclideanEvenBoundaryFlatSubspace K) :
    productionContactRemainderValue L K v w =
      productionArithmeticRealValue L
        (productionContactRemainderPhysicalTest L K v w) := by
  unfold productionContactRemainderValue
  exact productionArithmeticRealValue_congr_on_Icc hL
    (fun t ht =>
      (productionContactRemainderPhysicalTest_eq_source_on_Icc
        K v w ht).symm)

theorem productionContactRemainder_authority
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 1 ≤ K)
    (v w : euclideanEvenBoundaryFlatSubspace K) :
    ProductionWeightedPhysicalAdmissible L
        (productionContactRemainderPhysicalTest L K v w) ∧
      productionContactRemainderValue L K v w =
        productionArithmeticRealValue L
          (productionContactRemainderPhysicalTest L K v w) := by
  exact ⟨productionContactRemainderPhysical_admissible hL K hK v w,
    productionContactRemainderValue_eq_physicalTest hL K v w⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.productionContactRemainder_authority
