import Zeta23.CCM.CanonicalGlobalF04
import Zeta23.CCM.CanonicalPrimeFreeSecondTest
import Zeta23.CCM.FirstCrossingGeneratedStrictEvenFrontier

noncomputable section

/-!
# M66: prime-free Euler curvature, local stationary exclusion, unconditional F04 frontier

With F04 now proved at every aperture (`CanonicalGlobalF04`):

* **Q-F04 and Q-NEG-EULER.**  Below `log 2`,
  `E''_z + (2/L) E'_z = -(2π)²/L⁴ · Q_K(L, z) ≤ -(M/L²)(1 - 2π² L (2K+1) K²)`,
  strictly negative for nonzero `z` on `0 < L < ε_K = 1/(2π²(2K+1)K²)`.
* **Step 103.**  At a stationary generated strict-even contact the complete second
  physical value equals `2⟪A w, w⟫ ≥ 0` (all primes up to `e^{L*}` included).
* **M66.**  Hence no generated strict-even contact below `ε_K` is stationary, and
  every such contact is fresh-born.  This may be vacuous: numerically the even
  ground is positive on the whole prime-free window for `K = 2..16`.
* The F04-conditional frontier theorems of
  `FirstCrossingGeneratedStrictEvenFrontier` hold unconditionally.

Nothing here excludes a stationary contact above `ε_K`, the fresh-born,
odd-first, tied or interior branches, or bears on RH.
-/

namespace Zeta23.CCM

open MeasureTheory Set Filter Topology
open scoped Interval

/-! ## M66: prime-free Euler curvature and the local stationary exclusion -/

section M66

variable (K : ℕ)

theorem sourceAtomRealEnergy_sourceIndexAction_eq_re
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) (ω : ℝ) :
    sourceAtomRealEnergy K (sourceIndexAction K x) ω =
      (quadraticForm (sourceMatrix ω K)
        ((indexMatrix K).mulVec ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))).re := by
  unfold sourceAtomRealEnergy matrixRealEnergy sourceIndexAction
  rfl

theorem evenBoundaryFlat_sum_eq_zero (z : euclideanEvenBoundaryFlatSubspace K) :
    ∑ i, ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
      (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) i = 0 :=
  sourceAtom_sum_eq_zero_of_boundaryFlat K _ (evenBoundaryFlatRawCoefficients_boundaryFlat K z)

/-- **Q-F04.**  Below `log 2` the second physical value is `-(2π)²/L⁴` times the
M42 prime-free second test of the same raw coefficients. -/
theorem productionSecondDerivativePhysicalValue_eq_neg_primeFreeSecondTest {L : ℝ}
    (hL : 0 < L) (hL2 : L < Real.log 2) (z : euclideanEvenBoundaryFlatSubspace K) :
    productionArithmeticRealValue L (productionSecondDerivativePhysicalTest L K z) =
      -(2 * Real.pi) ^ 2 / L ^ 4 *
        primeFreeSecondTest K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) L := by
  rw [productionSecondDerivativePhysicalValue_eq_channels K hL hL2]
  unfold primeFreeSecondChannel primeFreeSecondTest
  rw [← intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun t => sourceAtomRealEnergySecondDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - t / L) * (t / L ^ 4) *
          poleScale t).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t => sourceAtomRealEnergySecondDerivative K
        (z : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - t / L) * (t / L ^ 4) *
          regularizedArchScale t).intervalIntegrable _ _),
    ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht => ?_)
  rw [uIoc_of_le hL.le] at ht
  rw [regularizedArchScale_eq_mul_archDensity ht.1.ne',
    sourceAtomRealEnergySecondDerivative_eq_indexAction K _ _ (evenBoundaryFlat_sum_eq_zero K z),
    sourceAtomRealEnergy_sourceIndexAction_eq_re]
  unfold poleScale primeFreeKernel
  ring

/-- The M42 radius `ε_K = 1/(2π²(2K+1)K²)`. -/
def primeFreeRadius (K : ℕ) : ℝ := 1 / (2 * Real.pi ^ 2 * (2 * K + 1) * K ^ 2)

theorem primeFreeRadius_lt_log_two (hK : 1 ≤ K) : primeFreeRadius K < Real.log 2 := by
  have hpi := Real.pi_gt_three
  have hN1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h9 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  have h3 : (3 : ℝ) ≤ 2 * K + 1 := by linarith
  have h1 : (1 : ℝ) ≤ (K : ℝ) ^ 2 := by nlinarith
  have hden : 54 ≤ 2 * Real.pi ^ 2 * (2 * K + 1) * K ^ 2 := by
    calc (54 : ℝ) = 2 * 9 * 3 * 1 := by norm_num
      _ ≤ 2 * Real.pi ^ 2 * (2 * K + 1) * K ^ 2 := by gcongr
  have hlog := Real.log_two_gt_d9
  have : primeFreeRadius K ≤ 1 / 54 :=
    one_div_le_one_div_of_le (by norm_num) hden
  linarith

/-- **Q-NEG-EULER, quantitative.**  For `0 < L < log 2` and every even
boundary-flat `z`, with `M = ∑ |z_i|²` in raw coordinates,
`E''_z + (2/L) E'_z ≤ -(M/L²)(1 - 2π² L (2K+1) K²)`. -/
theorem productionContactEulerCurvature_le {L : ℝ} (hL : 0 < L) (hL2 : L < Real.log 2)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFixedSecondVariation .even L K z +
        2 * productionContactFirstVariation .even L K z / L ≤
      -(∑ i, Complex.normSq (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) i)) / L ^ 2 *
        (1 - 2 * Real.pi ^ 2 * L * (2 * K + 1) * K ^ 2) := by
  rw [(productionContactF04DerivativeAuthority_of_lt_log_two K hL hL2).fixedSecondEuler z,
    productionSecondDerivativePhysicalValue_eq_neg_primeFreeSecondTest K hL hL2 z]
  have hge := primeFreeSecondTest_ge K _ (evenBoundaryFlat_sum_eq_zero K z) hL hL2.le
  have hc : 0 ≤ (2 * Real.pi) ^ 2 / L ^ 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hge hc
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  calc -(2 * Real.pi) ^ 2 / L ^ 4 *
        primeFreeSecondTest K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) L =
      -((2 * Real.pi) ^ 2 / L ^ 4 *
        primeFreeSecondTest K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) L) := by ring
    _ ≤ -((2 * Real.pi) ^ 2 / L ^ 4 *
        (L ^ 2 * (∑ i, Complex.normSq (((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) i)) *
          (1 / (4 * Real.pi ^ 2) - L * (2 * K + 1) * K ^ 2 / 2))) := neg_le_neg hmul
    _ = _ := by field_simp; ring

/-- **Q-NEG-EULER, strict.**  On `0 < L < ε_K` the Euler-corrected fixed
curvature is strictly negative on every nonzero even boundary-flat vector. -/
theorem productionContactEulerCurvature_neg (hK : 1 ≤ K) {L : ℝ} (hL : 0 < L)
    (hLr : L < primeFreeRadius K) (z : euclideanEvenBoundaryFlatSubspace K) (hz : z ≠ 0) :
    productionContactFixedSecondVariation .even L K z +
        2 * productionContactFirstVariation .even L K z / L < 0 := by
  have hL2 := hLr.trans (primeFreeRadius_lt_log_two K hK)
  rw [(productionContactF04DerivativeAuthority_of_lt_log_two K hL hL2).fixedSecondEuler z,
    productionSecondDerivativePhysicalValue_eq_neg_primeFreeSecondTest K hL hL2 z]
  have hz' : (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
      (z : EuclideanSpace ℂ (Fin (2 * K + 1))) ≠ 0 := by
    intro h
    apply hz
    have h0 : (z : EuclideanSpace ℂ (Fin (2 * K + 1))) = 0 :=
      (EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ).injective (by rw [h, map_zero])
    exact (Submodule.coe_eq_zero).mp h0
  have hQ := primeFreeSecondTest_pos K hK _ (evenBoundaryFlat_sum_eq_zero K z) hz' hL hLr
  have hc : 0 < (2 * Real.pi) ^ 2 / L ^ 4 := by positivity
  have : 0 < (2 * Real.pi) ^ 2 / L ^ 4 *
      primeFreeSecondTest K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
        (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) L := mul_pos hc hQ
  calc -(2 * Real.pi) ^ 2 / L ^ 4 *
        primeFreeSecondTest K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) L =
      -((2 * Real.pi) ^ 2 / L ^ 4 *
        primeFreeSecondTest K ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ)
          (z : EuclideanSpace ℂ (Fin (2 * K + 1)))) L) := by ring
    _ < 0 := neg_neg_of_pos this

end M66

/-! ## Generated strict-even contacts -/

/-- At a stationary generated strict-even contact the fixed second variation is
twice the response cost `⟪A w, w⟫` of the stationary response (zero optimized
curvature; no F04 input). -/
theorem GeneratedStrictEvenContact.fixedSecondVariation_eq_two_mul_responseCost
    (c : GeneratedStrictEvenContact)
    (hstationary : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0) :
    productionContactFixedSecondVariation .even c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z =
      2 * productionContactResponseCost c.generated.shell.Lstar (c.generated.shell.k + 1)
        (canonicalStationaryEvenResponse c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) := by
  have hκ := c.actual_stationary_curvature_eq_zero hstationary
  have hspec := canonicalStationaryEvenResponse_spec c.Lstar_pos (c.generated.shell.k + 1)
    c.two_le_K c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary
  have hsym := canonicalEvenApertureFirst_isSymmetric c.Lstar_pos (c.generated.shell.k + 1)
  unfold canonicalOptimizedContactCurvature canonicalContactSecondPairing at hκ
  rw [← hsym, show canonicalEvenApertureFirst c.generated.shell.Lstar (c.generated.shell.k + 1) c.z =
      -(evenCompressedCanonical c.generated.shell.Lstar (c.generated.shell.k + 1)
        (canonicalStationaryEvenResponse c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary)) by
      rw [hspec.2, neg_neg], inner_neg_left, Complex.neg_re] at hκ
  unfold productionContactResponseCost
  linarith

/-- **Step 103, unconditional.**  At a stationary generated strict-even contact the
complete second physical value (pole, archimedean and all primes up to `e^{L*}`)
equals twice the response cost, so it is nonnegative. -/
theorem GeneratedStrictEvenContact.secondPhysicalValue_eq_two_mul_responseCost
    (c : GeneratedStrictEvenContact)
    (hstationary : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0) :
    productionArithmeticRealValue c.generated.shell.Lstar
        (productionSecondDerivativePhysicalTest c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z) =
      2 * productionContactResponseCost c.generated.shell.Lstar (c.generated.shell.k + 1)
        (canonicalStationaryEvenResponse c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) := by
  rw [← (productionContactF04DerivativeAuthority_of_pos _ c.Lstar_pos).fixedSecondEuler c.z,
    hstationary, c.fixedSecondVariation_eq_two_mul_responseCost hstationary]
  ring

theorem GeneratedStrictEvenContact.secondPhysicalValue_nonneg
    (c : GeneratedStrictEvenContact)
    (hstationary : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0) :
    0 ≤ productionArithmeticRealValue c.generated.shell.Lstar
        (productionSecondDerivativePhysicalTest c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z) := by
  rw [c.secondPhysicalValue_eq_two_mul_responseCost hstationary]
  have := productionContactResponseCost_nonnegative c.evenGround_zero
    (canonicalStationaryEvenResponse c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary)
  linarith

/-- **M66: no stationary generated strict-even first contact below `ε_K`.**
A stationary contact would have `E''_z(L*) = 2⟪A w, w⟫ ≥ 0`, while prime-free F04
and M42 force `E''_z(L*) < 0` on `L* < ε_K`.  This may be vacuous if no generated
contact lies in this window; it is not an exclusion of other branches. -/
theorem GeneratedStrictEvenContact.firstVariation_ne_zero_of_lt_primeFreeRadius
    (c : GeneratedStrictEvenContact)
    (hLr : c.generated.shell.Lstar < primeFreeRadius (c.generated.shell.k + 1)) :
    productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z ≠ 0 := by
  intro hstationary
  have h2 := c.fixedSecondVariation_eq_two_mul_responseCost hstationary
  have hcost := productionContactResponseCost_nonnegative c.evenGround_zero
    (canonicalStationaryEvenResponse c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
      c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary)
  have hneg := productionContactEulerCurvature_neg (c.generated.shell.k + 1) (by omega)
    c.Lstar_pos hLr c.z c.z_ne
  rw [hstationary, mul_zero, zero_div, add_zero] at hneg
  linarith

/-- Corollary: below `ε_K` every generated strict-even contact is fresh-born. -/
theorem GeneratedStrictEvenContact.fresh_of_lt_primeFreeRadius
    (c : GeneratedStrictEvenContact)
    (hLr : c.generated.shell.Lstar < primeFreeRadius (c.generated.shell.k + 1)) :
    ¬ c.generated.shell.n < c.generated.shell.k := fun hinh =>
  c.firstVariation_ne_zero_of_lt_primeFreeRadius hLr (c.firstVariation_eq_zero_of_inherited hinh)

/-! ## F04-conditional frontier theorems, now unconditional -/

theorem GeneratedStrictEvenContact.production_stationary_saturation_unconditional
    (c : GeneratedStrictEvenContact)
    (hstationary : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0) :
    productionContactRemainderValue c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z
        (canonicalStationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) =
      (2 * Real.pi)^2 / c.generated.shell.Lstar^2 *
        productionStrictEvenSourceValue c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z :=
  c.production_stationary_saturation
    (productionContactF04DerivativeAuthority_of_pos _ c.Lstar_pos) hstationary

theorem GeneratedStrictEvenContact.production_stationary_remainder_pos_unconditional
    (c : GeneratedStrictEvenContact)
    (hstationary : productionContactFirstVariation .even c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z = 0) :
    0 < productionContactRemainderValue c.generated.shell.Lstar
      (c.generated.shell.k + 1) c.z
      (canonicalStationaryEvenResponse
        c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
        c.z c.z_ne c.z_norm c.z_kernel c.odd_positive hstationary) :=
  c.production_stationary_remainder_pos
    (productionContactF04DerivativeAuthority_of_pos _ c.Lstar_pos) hstationary

theorem GeneratedStrictEvenContact.completed_production_frontier_unconditional
    (c : GeneratedStrictEvenContact) :
    Nonempty (GeneratedStrictEvenCompletedProductionBranch c) :=
  c.completed_production_frontier (productionContactF04DerivativeAuthority_of_pos _ c.Lstar_pos)

theorem GeneratedStrictEvenContact.inherited_completed_production_frontier_unconditional
    (c : GeneratedStrictEvenContact)
    (hinh : c.generated.shell.n < c.generated.shell.k) :
    ∃ b : GeneratedStrictEvenCompletedProductionBranch c,
      match b with
      | .firstOrder _ _ => False
      | .stationary hzero _ _ _ _ _ _ _ =>
          hzero = c.firstVariation_eq_zero_of_inherited hinh :=
  c.inherited_completed_production_frontier
    (productionContactF04DerivativeAuthority_of_pos _ c.Lstar_pos) hinh

theorem GeneratedStrictEvenContact.inherited_production_saturation_unconditional
    (c : GeneratedStrictEvenContact)
    (hinh : c.generated.shell.n < c.generated.shell.k) :
    productionContactRemainderValue c.generated.shell.Lstar
        (c.generated.shell.k + 1) c.z
        (canonicalStationaryEvenResponse
          c.Lstar_pos (c.generated.shell.k + 1) c.two_le_K
          c.z c.z_ne c.z_norm c.z_kernel c.odd_positive
          (c.firstVariation_eq_zero_of_inherited hinh)) =
      (2 * Real.pi)^2 / c.generated.shell.Lstar^2 *
        productionStrictEvenSourceValue c.generated.shell.Lstar
          (c.generated.shell.k + 1) c.z :=
  c.inherited_production_saturation
    (productionContactF04DerivativeAuthority_of_pos _ c.Lstar_pos) hinh

/-! ## The F04 bridge identities, now unconditional -/

theorem canonicalFirstVariation_eq_physical_of_pos {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFirstVariation .even L K z =
      productionArithmeticRealValue L (productionFirstDerivativePhysicalTest L K z) :=
  (productionContactF04DerivativeAuthority_of_pos K hL).first z

theorem canonicalFixedSecondEuler_eq_physical_of_pos {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z : euclideanEvenBoundaryFlatSubspace K) :
    productionContactFixedSecondVariation .even L K z +
        2 * productionContactFirstVariation .even L K z / L =
      productionArithmeticRealValue L (productionSecondDerivativePhysicalTest L K z) :=
  (productionContactF04DerivativeAuthority_of_pos K hL).fixedSecondEuler z

theorem canonicalMixedFirstVariation_eq_physical_of_pos {L : ℝ} (hL : 0 < L) (K : ℕ)
    (z w : euclideanEvenBoundaryFlatSubspace K) :
    Complex.re (inner ℂ z (canonicalEvenApertureFirst L K w)) =
      productionArithmeticRealValue L (productionMixedDerivativePhysicalTest L K z w) :=
  (productionContactF04DerivativeAuthority_of_pos K hL).mixed z w

theorem canonicalStationaryCurvature_eq_productionSaturationGap_of_pos
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 2 ≤ K)
    (z : euclideanEvenBoundaryFlatSubspace K)
    (hzne : z ≠ 0) (hznorm : ‖z‖ = 1)
    (hzero : evenCompressedCanonical L K z = 0)
    (hodd : 0 < parityRayleighBottom .odd L K)
    (hstationary : productionContactFirstVariation .even L K z = 0) :
    canonicalOptimizedContactCurvature hL K hK z hzne hznorm hzero hodd hstationary =
      productionContactSaturationGap L K z
        (canonicalStationaryEvenResponse hL K hK z hzne hznorm hzero hodd hstationary) :=
  canonicalStationaryCurvature_eq_productionSaturationGap hL K hK z hzne hznorm hzero hodd
    hstationary (productionContactF04DerivativeAuthority_of_pos K hL)

end Zeta23.CCM

#print axioms Zeta23.CCM.productionSecondDerivativePhysicalValue_eq_neg_primeFreeSecondTest
#print axioms Zeta23.CCM.productionContactEulerCurvature_le
#print axioms Zeta23.CCM.productionContactEulerCurvature_neg
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.fixedSecondVariation_eq_two_mul_responseCost
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.secondPhysicalValue_eq_two_mul_responseCost
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.secondPhysicalValue_nonneg
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.firstVariation_ne_zero_of_lt_primeFreeRadius
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.fresh_of_lt_primeFreeRadius
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.production_stationary_saturation_unconditional
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.production_stationary_remainder_pos_unconditional
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.completed_production_frontier_unconditional
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.inherited_completed_production_frontier_unconditional
#print axioms Zeta23.CCM.GeneratedStrictEvenContact.inherited_production_saturation_unconditional
#print axioms Zeta23.CCM.canonicalFirstVariation_eq_physical_of_pos
#print axioms Zeta23.CCM.canonicalFixedSecondEuler_eq_physical_of_pos
#print axioms Zeta23.CCM.canonicalMixedFirstVariation_eq_physical_of_pos
#print axioms Zeta23.CCM.canonicalStationaryCurvature_eq_productionSaturationGap_of_pos
