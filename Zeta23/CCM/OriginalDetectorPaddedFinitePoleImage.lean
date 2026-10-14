import Zeta23.CCM.OriginalDetectorPaddedFiniteWindowHigherFlat
import Zeta23.CCM.CanonicalPoleNeutralGeometry
import Zeta23.ExceptionalZero.UniversalSincPhysicalDetector

/-!
# Applying the actual pole killer to the fixed finite source image

The finite multiplier is the literal differential multiplier
`ω_n² - 1/4`. Its original-source endpoint moments imply the existing
native elementary-pole equations, with their unchanged profile scales.
-/

noncomputable section

open Set Complex
open scoped Topology

namespace Zeta23.CCM

private def finiteWeightedJet (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ)
    (r : ℕ) (x : ℝ) : ℂ :=
  ∑ i, u i * localizedFrequency L (centeredIndex N i) ^ r *
    localizedMode L (centeredIndex N i) x

private theorem finiteWeightedJet_hasDerivAt
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (r : ℕ) (x : ℝ) :
    HasDerivAt (finiteWeightedJet L N u r) (finiteWeightedJet L N u (r + 1) x) x := by
  unfold finiteWeightedJet
  apply HasDerivAt.fun_sum
  intro i hi
  convert (hasDerivAt_localizedMode L (centeredIndex N i) x).const_mul
    (u i * localizedFrequency L (centeredIndex N i) ^ r) using 1 <;>
    first | rfl | (simp only [pow_succ]; ring)

private theorem finiteWeightedJet_eq_iteratedDeriv
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (r : ℕ) :
    iteratedDeriv r (localizedFiniteFunction L N u) = finiteWeightedJet L N u r := by
  induction r with
  | zero =>
    funext x
    simp [finiteWeightedJet, localizedFiniteFunction]
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    exact (finiteWeightedJet_hasDerivAt L N u r x).deriv

/-- The exact coefficient moment corresponding to each true endpoint jet. -/
theorem padded_localizedFiniteFunction_iteratedDeriv_zero_eq_moment
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (r : ℕ) :
    iteratedDeriv r (localizedFiniteFunction L N u) 0 =
      (localizedBaseFrequency L ^ r * ((1 / Real.sqrt L : ℝ) : ℂ)) *
        centeredMoment N r u := by
  rw [finiteWeightedJet_eq_iteratedDeriv]
  simp only [finiteWeightedJet, localizedMode_zero, centeredMoment, localizedFrequency, mul_pow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- All endpoint moments below order eight vanish for the actual output
coordinates, before applying any differential multiplier or projection. -/
theorem originalDetectorPaddedFiniteWindowImageCoefficients_moment_zero
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) {r : ℕ} (hr : r < 8) :
    centeredMoment (originalDetectorQuarticCutoff L) r
      (originalDetectorPaddedFiniteWindowImageCoefficients s L c (by linarith)) = 0 := by
  have hLp : 0 < L := by linarith
  have hfun : localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFiniteWindowImageCoefficients s L c hLp) =
        originalDetectorPaddedFiniteWindowImage s L c hLp := by
    funext x
    exact localizedFiniteFunction_originalDetectorPaddedFiniteWindowImageCoefficients s c hL x
  have hzero := (originalDetectorPaddedFiniteWindowImage_endpoint_jets_lt_eight s c hLp hr).1
  rw [← hfun, padded_localizedFiniteFunction_iteratedDeriv_zero_eq_moment] at hzero
  apply (mul_eq_zero.mp hzero).resolve_left
  apply mul_ne_zero
  · apply pow_ne_zero
    unfold localizedBaseFrequency
    apply mul_ne_zero Complex.I_ne_zero
    exact Complex.ofReal_ne_zero.mpr
      (div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hLp.ne')
  · exact Complex.ofReal_ne_zero.mpr (one_div_ne_zero (Real.sqrt_ne_zero'.mpr hLp))

/-- Apply exactly `P=∂²-1/4` in the same centered Fourier coordinates. -/
def originalDetectorPaddedFinitePoleImageCoefficients (s L c : ℝ) (hL : 0 < L) :
    Fin (2 * originalDetectorQuarticCutoff L + 1) → ℂ :=
  fun i => (localizedFrequency L (centeredIndex (originalDetectorQuarticCutoff L) i) ^ 2 - 1 / 4) *
    originalDetectorPaddedFiniteWindowImageCoefficients s L c hL i

private theorem centeredMoment_pole_multiplier
    (L : ℝ) (N : ℕ) (u : Fin (2 * N + 1) → ℂ) (r : ℕ) :
    centeredMoment N r (fun i => (localizedFrequency L (centeredIndex N i) ^ 2 - 1 / 4) * u i) =
      localizedBaseFrequency L ^ 2 * centeredMoment N (r + 2) u -
        (1 / 4 : ℂ) * centeredMoment N r u := by
  simp only [centeredMoment, localizedFrequency, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [pow_add]
  ring

/-- The actual pole-killed output is still a legal finite vector. -/
theorem originalDetectorPaddedFinitePoleImageCoefficients_boundaryFlat
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    BoundaryFlatCoefficients (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFinitePoleImageCoefficients s L c (by linarith)) := by
  unfold BoundaryFlatCoefficients originalDetectorPaddedFinitePoleImageCoefficients
  constructor
  · rw [centeredMoment_pole_multiplier,
      originalDetectorPaddedFiniteWindowImageCoefficients_moment_zero s c hL (by norm_num : 0 + 2 < 8),
      originalDetectorPaddedFiniteWindowImageCoefficients_moment_zero s c hL (by norm_num : 0 < 8)]
    ring
  · constructor
    · rw [centeredMoment_pole_multiplier,
        originalDetectorPaddedFiniteWindowImageCoefficients_moment_zero s c hL (by norm_num : 1 + 2 < 8),
        originalDetectorPaddedFiniteWindowImageCoefficients_moment_zero s c hL (by norm_num : 1 < 8)]
      ring
    · rw [centeredMoment_pole_multiplier,
        originalDetectorPaddedFiniteWindowImageCoefficients_moment_zero s c hL (by norm_num : 2 + 2 < 8),
        originalDetectorPaddedFiniteWindowImageCoefficients_moment_zero s c hL (by norm_num : 2 < 8)]
      ring

private theorem pole_multiplier_even_profile {L : ℝ} (hL : 0 < L) (n : ℤ) :
    (poleEvenProfileReal n L : ℂ) * (localizedFrequency L n ^ 2 - 1 / 4) =
      -1 / (4 * L) := by
  have hden := (poleProfileDenominator_pos hL n).ne'
  have hdenC : (poleProfileDenominator n L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hden
  unfold poleEvenProfileReal localizedFrequency localizedBaseFrequency poleProfileDenominator
  push_cast
  unfold poleProfileDenominator at hdenC
  push_cast at hdenC
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  field_simp [hLC, hdenC]
  ring_nf
  simp [Complex.I_sq]

private theorem pole_multiplier_odd_profile {L : ℝ} (hL : 0 < L) (n : ℤ) :
    (poleOddProfileReal n L : ℂ) * (localizedFrequency L n ^ 2 - 1 / 4) =
      (-Real.pi / L ^ 2 : ℝ) * (n : ℂ) := by
  have hLC : (L : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hL.ne'
  have hrel : (poleOddProfileReal n L : ℂ) =
      ((4 * Real.pi * (n : ℂ)) / (L : ℂ)) * (poleEvenProfileReal n L : ℂ) := by
    unfold poleOddProfileReal poleEvenProfileReal
    push_cast
    field_simp [hLC]
  rw [hrel, mul_assoc, pole_multiplier_even_profile hL]
  push_cast
  field_simp [hLC]

/-- Both unchanged native elementary-pole functionals vanish on the
actual finite `Pq` output, even before choosing a reversal parity. -/
theorem originalDetectorPaddedFinitePoleImageCoefficients_native_poles_zero
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    canonicalPoleEvenFunctional L (originalDetectorQuarticCutoff L)
      (WithLp.toLp 2 (originalDetectorPaddedFinitePoleImageCoefficients s L c (by linarith))) = 0 ∧
    canonicalPoleOddFunctional L (originalDetectorQuarticCutoff L)
      (WithLp.toLp 2 (originalDetectorPaddedFinitePoleImageCoefficients s L c (by linarith))) = 0 := by
  have hLp : 0 < L := by linarith
  have hm0 := originalDetectorPaddedFiniteWindowImageCoefficients_moment_zero s c hL (r := 0) (by norm_num)
  have hm1 := originalDetectorPaddedFiniteWindowImageCoefficients_moment_zero s c hL (r := 1) (by norm_num)
  constructor
  · change (∑ i, (poleEvenProfileReal _ L : ℂ) *
      ((localizedFrequency L _ ^ 2 - 1 / 4) *
        originalDetectorPaddedFiniteWindowImageCoefficients s L c hLp i)) = 0
    simp_rw [← mul_assoc, pole_multiplier_even_profile hLp]
    rw [← Finset.mul_sum]
    simpa only [centeredMoment, pow_zero, one_mul, mul_zero] using congrArg (fun z : ℂ => (-1 / (4 * L)) * z) hm0
  · change (∑ i, (poleOddProfileReal _ L : ℂ) *
      ((localizedFrequency L _ ^ 2 - 1 / 4) *
        originalDetectorPaddedFiniteWindowImageCoefficients s L c hLp i)) = 0
    simp_rw [← mul_assoc, pole_multiplier_odd_profile hLp, mul_assoc]
    rw [← Finset.mul_sum]
    simpa only [centeredMoment, pow_one, mul_zero] using
      congrArg (fun z : ℂ => ((-Real.pi / L ^ 2 : ℝ) : ℂ) * z) hm1

/-- Exact differential realization of the constructed output coefficients. -/
theorem localizedFiniteFunction_originalDetectorPaddedFinitePoleImageCoefficients
    (s c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      (originalDetectorPaddedFinitePoleImageCoefficients s L c (by linarith)) =
        Zeta23.ExceptionalZero.poleKilled (originalDetectorPaddedFiniteWindowImage s L c (by linarith)) := by
  let N := originalDetectorQuarticCutoff L
  let u := originalDetectorPaddedFiniteWindowImageCoefficients s L c (by linarith)
  have hfun : localizedFiniteFunction L N u = originalDetectorPaddedFiniteWindowImage s L c (by linarith) := by
    funext x
    exact localizedFiniteFunction_originalDetectorPaddedFiniteWindowImageCoefficients s c hL x
  rw [← hfun]
  have hfirst : deriv (localizedFiniteFunction L N u) = localizedFiniteFirstJet L N u :=
    deriv_eq (hasDerivAt_localizedFiniteFunction L N u)
  have hsecond : deriv (localizedFiniteFirstJet L N u) = localizedFiniteSecondJet L N u :=
    deriv_eq (hasDerivAt_localizedFiniteFirstJet L N u)
  funext x
  simp only [Zeta23.ExceptionalZero.poleKilled, hfirst, hsecond,
    originalDetectorPaddedFinitePoleImageCoefficients, localizedFiniteFunction, localizedFiniteSecondJet]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change _ = u i * _ ^ 2 * _ - (1 / 4 : ℂ) * (u i * _)
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.padded_localizedFiniteFunction_iteratedDeriv_zero_eq_moment
#print axioms Zeta23.CCM.originalDetectorPaddedFiniteWindowImageCoefficients_moment_zero
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePoleImageCoefficients_boundaryFlat
#print axioms Zeta23.CCM.originalDetectorPaddedFinitePoleImageCoefficients_native_poles_zero
#print axioms Zeta23.CCM.localizedFiniteFunction_originalDetectorPaddedFinitePoleImageCoefficients
