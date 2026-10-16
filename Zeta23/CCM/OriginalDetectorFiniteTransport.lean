import Zeta23.CCM.OriginalDetectorPaddedFinitePhaseNativeProducer
import Zeta23.CCM.OriginalDetectorPaddedFinitePositivity
import Zeta23.CCM.OriginalDetectorPaddedFinitePoleImageC4

/-!
# The canonical actual finite transport interface

This image uses the original infinite-convolution source, literal positive
DC tail padding, the degree-four sine window, raw cutoff `ceil(L^4)-4`,
and the unchanged pole killer. Its actual coefficients use the repository's
normalized Fourier modes. The two source phases and their true native
normalizations are constructed by the imported producer.
-/

noncomputable section

open Set Complex MeasureTheory Filter
open scoped Topology

namespace Zeta23.CCM

/-- The actual positively padded `Pq` lobe in its native quartic coordinates. -/
def originalDetectorFiniteImage (L c : ℝ) (hL : 0 < L) :
    EuclideanSpace ℂ (Fin (2 * originalDetectorQuarticCutoff L + 1)) :=
  originalDetectorPaddedFinitePhaseLeft L c hL

theorem originalDetectorFiniteImage_legal (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    originalDetectorFiniteImage L c (by linarith) ∈
      euclideanBoundaryFlatSubspace (originalDetectorQuarticCutoff L) := by
  apply (mem_euclideanBoundaryFlatSubspace_iff _ _).mpr
  exact originalDetectorPaddedFinitePoleImageCoefficients_boundaryFlat UniversalSinc.fixedScale c hL

theorem originalDetectorFiniteImage_poleNeutral (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    canonicalPoleEvenFunctional L (originalDetectorQuarticCutoff L)
        (originalDetectorFiniteImage L c (by linarith)) = 0 ∧
      canonicalPoleOddFunctional L (originalDetectorQuarticCutoff L)
        (originalDetectorFiniteImage L c (by linarith)) = 0 :=
  originalDetectorPaddedFinitePoleImageCoefficients_native_poles_zero UniversalSinc.fixedScale c hL

/-- The constructed image has all six zero endpoint moments; in particular
it pays the prescribed fourth-order endpoint requirement. -/
theorem originalDetectorFiniteImage_endpointJets (c : ℝ) {L : ℝ} (hL : 2 ≤ L)
    {r : ℕ} (hr : r ≤ 4) :
    centeredMoment (originalDetectorQuarticCutoff L) r
      ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
        (originalDetectorFiniteImage L c (by linarith))) = 0 :=
  originalDetectorPaddedFinitePoleImageCoefficients_moment_zero_lt_six
    UniversalSinc.fixedScale c hL (by omega)

theorem originalDetectorFiniteImage_endpointJets_physical (c : ℝ) {L : ℝ} (hL : 2 ≤ L)
    {r : ℕ} (hr : r ≤ 4) :
    iteratedDeriv r (localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
        (originalDetectorFiniteImage L c (by linarith)))) 0 = 0 ∧
    iteratedDeriv r (localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
        (originalDetectorFiniteImage L c (by linarith)))) L = 0 :=
  originalDetectorPaddedFinitePoleImage_endpoint_jets_lt_six UniversalSinc.fixedScale c hL (by omega)

theorem originalDetectorFiniteImage_hard_contDiff_four (c : ℝ) {L : ℝ} (hL : 2 ≤ L) :
    ContDiff ℝ 4 (localizedFiniteVector L (originalDetectorQuarticCutoff L)
      ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
        (originalDetectorFiniteImage L c (by linarith)))) :=
  originalDetectorPaddedFinitePoleImage_hard_contDiff_four UniversalSinc.fixedScale c hL

theorem originalDetectorFiniteImage_error_bound {L c : ℝ} (hL : 2 ≤ L)
    (hleft : 1 + UniversalSinc.fixedScale ≤ c)
    (hright : c + UniversalSinc.fixedScale ≤ L - 1)
    (r : ℕ) {x : ℝ} (hx : x ∈ Icc 0 L) :
    ‖iteratedDeriv r (fun y => Zeta23.ExceptionalZero.originalSincTest UniversalSinc.fixedScale (y - c)) x -
      iteratedDeriv r (localizedFiniteFunction L (originalDetectorQuarticCutoff L)
        ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
          (originalDetectorFiniteImage L c (by linarith)))) x‖ ≤
      originalDetectorPaddedFinitePoleImageJetBudget UniversalSinc.fixedScale L r :=
  originalDetectorPaddedFinitePoleImage_iteratedDeriv_error_le_budget
    UniversalSinc.fixedScale_pos hL hleft hright r hx

theorem originalDetectorFiniteImage_quartic_error_tendsto_zero (r : ℕ) (β : ℝ) :
    Tendsto (fun L : ℝ =>
      originalDetectorPaddedFinitePoleImageJetBudget UniversalSinc.fixedScale L r * Real.exp (β * L))
      atTop (𝓝 0) :=
  originalDetectorPaddedFinitePoleImageJetBudget_mul_exp_tendsto_zero UniversalSinc.fixedScale r β

/-- The exact physical/coefficient normalization, with no convention change. -/
theorem originalDetectorFiniteImage_physical_norm (L c : ℝ) (hL : 0 < L) :
    (∫ x in (0 : ℝ)..L, ‖localizedFiniteFunction L (originalDetectorQuarticCutoff L)
      ((EuclideanSpace.equiv (Fin (2 * originalDetectorQuarticCutoff L + 1)) ℂ)
        (originalDetectorFiniteImage L c hL)) x‖ ^ 2) = ‖originalDetectorFiniteImage L c hL‖ ^ 2 :=
  localizedFiniteFunction_energy_eq_norm_sq hL _ _

end Zeta23.CCM

#print axioms Zeta23.CCM.originalDetectorFiniteImage_legal
#print axioms Zeta23.CCM.originalDetectorFiniteImage_poleNeutral
#print axioms Zeta23.CCM.originalDetectorFiniteImage_endpointJets
#print axioms Zeta23.CCM.originalDetectorFiniteImage_endpointJets_physical
#print axioms Zeta23.CCM.originalDetectorFiniteImage_hard_contDiff_four
#print axioms Zeta23.CCM.originalDetectorFiniteImage_error_bound
#print axioms Zeta23.CCM.originalDetectorFiniteImage_quartic_error_tendsto_zero
#print axioms Zeta23.CCM.originalDetectorFiniteImage_physical_norm
