import Zeta23.OPICARound4.NativeConcentrationBudget
import Zeta23.OPICARound4.AbsoluteAnchor
import Zeta23.CCM.CanonicalPoleNeutralPublicAPI
import Zeta23.CCM.CanonicalPoleNeutralGroundConstraints

noncomputable section
namespace Zeta23.OPICARound4
open CCM MeasureTheory
open scoped BigOperators ComplexConjugate Interval

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  Submodule.seminormedAddCommGroup Submodule.normedAddCommGroup
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- Complete signed discrepancy of the actual corrected source test. -/
def nativeSignedPrimeDiscrepancy (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) : ℂ :=
  (∑ q ∈ Finset.Icc 2 ⌊Real.exp L⌋₊,
    primeSourceWeight q * correctedSourceTest L K u (Real.log q)) -
    ∫ y in (0 : ℝ)..L, (Real.exp (y / 2) : ℂ) * correctedSourceTest L K u y

/-- The full uncompressed Archimedean row, on the actual input. -/
def nativeGroundArchPairing (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) : ℂ :=
  inner ℂ (correctedSourceRow L K) ((canonicalArchMatrix L K).toEuclideanLin u.val.val)

/-- The full prime-power row, on the same actual input. -/
def nativeGroundPrimePairing (L : ℝ) (K : ℕ)
    (u : poleNeutralEvenSubspace L K) : ℂ :=
  inner ℂ (correctedSourceRow L K) ((canonicalPrimeMatrix L K).toEuclideanLin u.val.val)

theorem native_signed_source_decomposition {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 2 ≤ K) (u : poleNeutralEvenSubspace L K) :
    poleNeutralCorrectedCubicSource L K u =
      nativeArchContinuumRow L K u - nativeSignedPrimeDiscrepancy L K u := by
  rw [correctedSourceTest_complete_arithmetic hL K hK]
  unfold nativeArchContinuumRow nativeSignedPrimeDiscrepancy
  ring

theorem native_signed_discrepancy_integral {L : ℝ} (hL : 0 < L)
    (K : ℕ) (u : poleNeutralEvenSubspace L K) :
    nativeSignedPrimeDiscrepancy L K u =
      -∫ y in (0 : ℝ)..L,
        ((Chebyshev.psi (Real.exp y) - Real.exp y : ℝ) : ℂ) * (Real.exp (-y / 2) : ℂ) *
          (correctedSourceTestDerivative L K u y - correctedSourceTest L K u y / 2) :=
  native_prime_discrepancy_integral hL K u

/-- The source-normalized ray really is a nonzero eigenmode of the same
actual even operator. Source normalization is not a unit-norm assertion. -/
theorem actual_even_ground_ray_facts {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :
    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs
    r ≠ 0 ∧ poleNeutralEvenCompressedCanonical L K r =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • r ∧
      poleNeutralCorrectedCubicSource L K r = 1 := by
  dsimp only
  obtain ⟨_, _, _, _, _, hf⟩ := exists_poleNeutral_strictEven_ground_shifted_normalization hL K hK hs
  refine ⟨?_, ?_, hf⟩
  · intro hz
    change poleNeutralCorrectedCubicFunctional L K _ = 1 at hf
    rw [hz, map_zero] at hf
    exact zero_ne_one hf
  · have h := apply_secularResolventRay
      (Bi := poleNeutralOddShiftedCanonicalEquiv hL K hK _ hs)
      (poleNeutral_shifted_rankOneIntertwining hL K hK _) (fun _ => rfl)
    change poleNeutralEvenShiftedCanonical L K (poleNeutralEvenRayleighBottom L K hL hK)
      (poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs) =
      (1 - poleNeutralCorrectedCubicSource L K
        (poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs)) • _ at h
    rw [hf, sub_self, zero_smul] at h
    exact sub_eq_zero.mp h

theorem actual_odd_ground_ray_facts {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK) :
    let w := poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs
    w ≠ 0 ∧ poleNeutralOddCompressedCanonical L K w =
      (poleNeutralOddRayleighBottom L K hL hK : ℂ) • w ∧
      poleNeutralCubicPairingFunctional L K w = 1 := by
  dsimp only
  obtain ⟨_, _, _, _, _, hf⟩ := exists_poleNeutral_strictOdd_ground_adjoint_normalization hL K hK hs
  refine ⟨?_, ?_, hf⟩
  · intro hz
    rw [hz, map_zero] at hf
    exact zero_ne_one hf
  · have h := apply_secularResolventRay
      (Bi := poleNeutralEvenShiftedCanonicalEquiv hL K hK _ hs)
      (poleNeutral_odd_adjoint_shifted_rankOneIntertwining hL K hK _) (fun _ => rfl)
    change poleNeutralOddShiftedCanonical L K (poleNeutralOddRayleighBottom L K hL hK)
      (poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs) =
      (1 - poleNeutralCubicPairingFunctional L K
        (poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs)) • _ at h
    rw [hf, sub_self, zero_smul] at h
    exact sub_eq_zero.mp h

/-- Strict-even arithmetic is an exact complex equality before any norm
bound. It holds on positive strict grounds too, so it is not an exclusion. -/
theorem actual_even_ground_signed_discrepancy {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :
    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs
    poleNeutralCorrectedCubicSource L K r = 1 ∧
      nativeSignedPrimeDiscrepancy L K r = nativeArchContinuumRow L K r - 1 ∧
      nativeGroundPrimePairing L K r = -1 - nativeGroundArchPairing L K r ∧
      ‖1 + nativeGroundArchPairing L K r‖ ≤
        nativePrimeConcentrationBudget L K (correctedSourceRow L K) r.val.val := by
  dsimp only
  let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs
  have hf : poleNeutralCorrectedCubicSource L K r = 1 :=
    (actual_even_ground_ray_facts hL K hK hs).2.2
  have hd := native_signed_source_decomposition hL K (by omega) r
  have hp : nativeGroundPrimePairing L K r = -1 - nativeGroundArchPairing L K r := by
    have he := correctedSourceRow_pole_cancelled hL K (show 2 ≤ K by omega) r
    change poleNeutralCorrectedCubicSource L K r =
      -nativeGroundArchPairing L K r - nativeGroundPrimePairing L K r at he
    rw [hf] at he
    linear_combination he
  refine ⟨hf, ?_, hp, ?_⟩
  · rw [hf] at hd
    linear_combination hd
  · have hb := native_prime_concentration_budget hL K (correctedSourceRow L K) r.val.val
    change ‖nativeGroundPrimePairing L K r‖ ≤ _ at hb
    rw [hp] at hb
    have he : -1 - nativeGroundArchPairing L K r = -(1 + nativeGroundArchPairing L K r) := by ring
    simpa only [he, norm_neg] using hb

/-- The odd response uses its reciprocal EVEN input. Its minus sign and
conjugation force source value -1, not +1, on that different input. -/
theorem actual_odd_ground_reciprocal_discrepancy {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK) :
    let v := nativeOddReciprocalInput hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs
    poleNeutralCorrectedCubicSource L K v = -1 ∧
      nativeSignedPrimeDiscrepancy L K v = nativeArchContinuumRow L K v + 1 ∧
      nativeGroundPrimePairing L K v = 1 - nativeGroundArchPairing L K v ∧
      ‖1 - nativeGroundArchPairing L K v‖ ≤
        nativePrimeConcentrationBudget L K (correctedSourceRow L K) v.val.val := by
  dsimp only
  let v := nativeOddReciprocalInput hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs
  have hr := native_odd_response_eq_reciprocal_source hL K hK _ hs
  rw [(actual_odd_ground_ray_facts hL K hK hs).2.2] at hr
  have hf : poleNeutralCorrectedCubicSource L K v = -1 := by
    have hh := congrArg (fun z : ℂ => -conj z) hr
    simpa using hh.symm
  have hd := native_signed_source_decomposition hL K (by omega) v
  have hp : nativeGroundPrimePairing L K v = 1 - nativeGroundArchPairing L K v := by
    have he := correctedSourceRow_pole_cancelled hL K (show 2 ≤ K by omega) v
    change poleNeutralCorrectedCubicSource L K v =
      -nativeGroundArchPairing L K v - nativeGroundPrimePairing L K v at he
    rw [hf] at he
    linear_combination he
  refine ⟨hf, ?_, hp, ?_⟩
  · rw [hf] at hd
    linear_combination hd
  · have hb := native_prime_concentration_budget hL K (correctedSourceRow L K) v.val.val
    change ‖nativeGroundPrimePairing L K v‖ ≤ _ at hb
    simpa only [hp] using hb

theorem actual_even_ground_signed_budget_feasibility {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :
    poleNeutralOddRayleighBottom L K hL hK - poleNeutralEvenRayleighBottom L K hL hK ≤
      nativeCompleteRowBudget L K * ‖poleNeutralCubicCompressionVector L K‖ +
        (LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K)).re / 2 := by
  have h := native_even_complete_signed_budget hL K hK _ hs
  rw [(actual_even_ground_ray_facts hL K hK hs).2.2] at h
  simp only [Complex.one_re, mul_one] at h
  linarith

theorem actual_odd_ground_signed_budget_feasibility {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK) :
    poleNeutralEvenRayleighBottom L K hL hK - poleNeutralOddRayleighBottom L K hL hK ≤
      nativeCompleteRowBudget L K * ‖poleNeutralCubicCompressionVector L K‖ -
        (LinearMap.trace ℂ (poleNeutralOddSubspace L K) (poleNeutralOddCompressedCanonical L K) -
          LinearMap.trace ℂ (poleNeutralEvenSubspace L K) (poleNeutralEvenCompressedCanonical L K)).re / 2 := by
  have h := native_odd_complete_signed_budget hL K hK _ hs
  rw [(actual_odd_ground_ray_facts hL K hK hs).2.2] at h
  simp only [Complex.one_re, mul_one, Complex.sub_re] at *
  nlinarith

theorem actual_even_ground_ray_moment_feasibility {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK) :
    let r := poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs
    (poleNeutralOddRayleighBottom L K hL hK - poleNeutralEvenRayleighBottom L K hL hK) *
      ‖poleNeutralIndexLinearMap hL K r‖ ^ 2 ≤
        (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K r.val)).re ∧
    0 < (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K r.val)).re := by
  dsimp only
  obtain ⟨hr0, hr, hf⟩ := actual_even_ground_ray_facts hL K hK hs
  have hb := poleNeutral_source_moment_gap_le hL K hK _ _ hr
  have hp := poleNeutral_even_eigen_source_moment_pos_of_lt_odd_bottom hL K hK _ _ hr0 hr hs
  simpa only [hf, star_one, one_mul] using And.intro hb hp

end Zeta23.OPICARound4
