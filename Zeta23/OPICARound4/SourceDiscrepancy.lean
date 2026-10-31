import Zeta23.OPICARound4.SourceRow
import Zeta23.CCM.MixedSourceDerivativeTransport

noncomputable section

namespace Zeta23.OPICARound4
open CCM Matrix
open scoped BigOperators ComplexConjugate

/-- The mixed source pairing is the physical coefficient inner product.
Both left and right vectors are retained, so signed cross terms survive. -/
theorem sourceAtomPairing_eq_physical_inner (K : ℕ)
    (h u : EuclideanSpace ℂ (Fin (2 * K + 1))) (omega : ℝ) :
    sourceAtomPairing K h u omega =
      inner ℂ h ((sourceMatrix omega K).toEuclideanLin u) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [sourceAtomPairing, dotProduct, Matrix.toEuclideanLin_apply,
    WithLp.ofLp_toLp, Matrix.mulVec, sourceMatrix_apply, sourceEntry_eq_ofReal,
    Finset.sum_mul, Complex.real_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (sourceEntryReal omega (centeredIndex K i) (centeredIndex K j) : ℂ) *
    (star (h i) * u j) =
    (sourceEntryReal omega (centeredIndex K i) (centeredIndex K j) : ℂ) * u j * star (h i)
  ring

/-- The test depends on the same complete source through its input. In the
resolvent consumer below, that input is the actual native source-selected ray. -/
def correctedSourceTest (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) (y : ℝ) : ℂ :=
  sourceAtomPairing K (correctedSourceRow L K)
    (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - y / L)

theorem correctedSourceTest_eq_inner (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) (y : ℝ) :
    correctedSourceTest L K u y =
      inner ℂ (correctedSourceRow L K) ((sourceMatrix (1 - y / L) K).toEuclideanLin
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) :=
  sourceAtomPairing_eq_physical_inner K _ _ _

theorem correctedSourceTest_lower_endpoint (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) : correctedSourceTest L K u 0 = 0 := by
  rw [correctedSourceTest_eq_inner]
  simp only [zero_div, sub_zero, sourceMatrix_one, map_smul, LinearMap.smul_apply,
    Matrix.toEuclideanLin_apply, Matrix.one_mulVec, WithLp.toLp_ofLp]
  change inner ℂ (correctedSourceRow L K)
    ((2 : ℂ) • (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) = 0
  rw [inner_smul_right, correctedSourceRow_orthogonal, mul_zero]

theorem correctedSourceTest_upper_endpoint {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) : correctedSourceTest L K u L = 0 := by
  rw [correctedSourceTest_eq_inner]
  simp [div_self hL.ne', sourceMatrix_zero]

/-- Exact source differentiation cost. The aperture factor is present and no
uniform bound over resolvent-selected states is asserted. -/
theorem correctedSourceTest_hasDerivAt (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) (y : ℝ) :
    HasDerivAt (correctedSourceTest L K u)
      ((-(1 / L) : ℝ) • sourceAtomPairingDerivative K (correctedSourceRow L K)
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - y / L)) y := by
  have hcoord : HasDerivAt (fun x : ℝ => 1 - x / L) (-(1 / L)) y := by
    simpa using! (hasDerivAt_const y (1 : ℝ)).sub ((hasDerivAt_id y).div_const L)
  exact (hasDerivAt_sourceAtomPairing K (correctedSourceRow L K)
    (u.val : EuclideanSpace ℂ (Fin (2 * K + 1))) (1 - y / L)).scomp y hcoord

/-- Exact all-prime-power pairing of the same row and the same input state. -/
theorem correctedSourceTest_prime_pairing (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) :
    inner ℂ (correctedSourceRow L K) ((canonicalPrimeMatrix L K).toEuclideanLin
        (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) =
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q * correctedSourceTest L K u (Real.log q) := by
  simp_rw [correctedSourceTest_eq_inner]
  rw [canonicalPrimeMatrix_eq_sum_sourceMatrix]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    inner_sum, inner_smul_right, primeSourceCoordinate]

/-- The signed arithmetic row identity includes full Archimedean output,
every prime power, and the projection correction already in the row. -/
theorem correctedSourceTest_complete_arithmetic {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : poleNeutralEvenSubspace L K) :
    poleNeutralCorrectedCubicSource L K u =
      -inner ℂ (correctedSourceRow L K)
        ((canonicalArchMatrix L K).toEuclideanLin
          (u.val : EuclideanSpace ℂ (Fin (2 * K + 1)))) -
      ∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
        primeSourceWeight q * correctedSourceTest L K u (Real.log q) := by
  rw [correctedSourceRow_pole_cancelled hL K hK, correctedSourceTest_prime_pairing]

/-- The source-dependent resolvent test is not replaced by an arbitrary fixed
test when proving its endpoint and differentiability prerequisites. -/
theorem actual_even_ray_test_prerequisites {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralOddRayleighBottom L K hL hK) :
    let u := poleNeutralEvenShiftedRay hL K hK lam hlam
    correctedSourceTest L K u 0 = 0 ∧ correctedSourceTest L K u L = 0 ∧
      Differentiable ℝ (correctedSourceTest L K u) := by
  dsimp only
  exact ⟨correctedSourceTest_lower_endpoint L K _, correctedSourceTest_upper_endpoint hL K _,
    fun y => (correctedSourceTest_hasDerivAt L K _ y).differentiableAt⟩

/-- The odd adjoint orientation selects its even resolvent input using the
actual corrected-source Riesz vector. It is not the even shifted ray. -/
theorem actual_odd_resolvent_test_prerequisites {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK) :
    let u := (poleNeutralEvenShiftedCanonicalEquiv hL K hK lam hlam).symm
      (poleNeutralCorrectedCubicRieszVector L K)
    correctedSourceTest L K u 0 = 0 ∧ correctedSourceTest L K u L = 0 ∧
      Differentiable ℝ (correctedSourceTest L K u) := by
  dsimp only
  exact ⟨correctedSourceTest_lower_endpoint L K _, correctedSourceTest_upper_endpoint hL K _,
    fun y => (correctedSourceTest_hasDerivAt L K _ y).differentiableAt⟩

end Zeta23.OPICARound4
