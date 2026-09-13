import Zeta23.CCM.CanonicalSourceMomentJets
import Zeta23.CCM.CanonicalSourceRieszEnergy

noncomputable section

namespace Zeta23.CCM

open MeasureTheory Set
open scoped Interval

/-!
# FIRST-BAD-RIGIDITY-E4-A4-FB04A: exact Riesz boundary recurrence

The legal #155 Riesz engine discharges the right endpoint only when the next
production source jet vanishes.  This module retains that endpoint instead and
separates it into an arithmetic scalar depending only on `(L,r)` and the exact
production source jet depending on the coefficient vector.

The complete transformed source channel inherits the same recurrence because
its reduced archimedean diagonal/off-diagonal and scalar-correction terms do not
depend on the Riesz order.

No sign of the endpoint scalar, Riesz primitive, smoothed integrand, complete
channel, or RH-directed quantity is asserted here.
-/

/-- The pulled-back source jet at the physical right endpoint is the original
source-coordinate jet at `ω = 0`. -/
@[simp] theorem sourceAtomComposedJet_right
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (r : ℕ) :
    sourceAtomComposedJet L K x r L =
      iteratedDeriv r (sourceAtomRealEnergy K x) 0 := by
  unfold sourceAtomComposedJet
  rw [div_self hL.ne']
  norm_num

/-- One legal integration-by-parts step with the right endpoint retained.
The left endpoint still vanishes because every positive-order Riesz primitive
is anchored at zero. -/
theorem canonicalPolePrimeRiesz_integral_step_with_boundary
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (r : ℕ) :
    (∫ t in (0 : ℝ)..L,
      canonicalPolePrimeRieszPrimitive L r t *
        sourceAtomComposedJet L K x (r + 1) t) =
      canonicalPolePrimeRieszPrimitive L (r + 1) L *
        iteratedDeriv (r + 1) (sourceAtomRealEnergy K x) 0 +
      (1 / L) *
        ∫ t in (0 : ℝ)..L,
          canonicalPolePrimeRieszPrimitive L (r + 1) t *
            sourceAtomComposedJet L K x (r + 2) t := by
  let P : ℝ → ℝ := canonicalPolePrimeRieszPrimitive L (r + 1)
  let G : ℝ → ℝ := sourceAtomComposedJet L K x (r + 1)
  have hPac : AbsolutelyContinuousOnInterval P 0 L := by
    simpa [P] using
      absolutelyContinuousOnInterval_canonicalPolePrimeRieszPrimitive_succ hL r
  have hGac : AbsolutelyContinuousOnInterval G 0 L := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact (contDiff_one_sourceAtomComposedJet L K x (r + 1)).contDiffOn
  have hparts := hPac.integral_mul_deriv_eq_deriv_mul hGac
  have hP0 : P 0 = 0 := by
    simp [P]
  have hGL :
      G L = iteratedDeriv (r + 1) (sourceAtomRealEnergy K x) 0 := by
    dsimp [G]
    exact sourceAtomComposedJet_right hL K x (r + 1)
  have hleft :
      (∫ t in (0 : ℝ)..L, P t * deriv G t) =
        -(1 / L) *
          ∫ t in (0 : ℝ)..L,
            canonicalPolePrimeRieszPrimitive L (r + 1) t *
              sourceAtomComposedJet L K x (r + 2) t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _ht
    dsimp [P, G]
    rw [deriv_sourceAtomComposedJet hL K x (r + 1) t]
    ring
  have hright :
      (∫ t in (0 : ℝ)..L, deriv P t * G t) =
        ∫ t in (0 : ℝ)..L,
          canonicalPolePrimeRieszPrimitive L r t *
            sourceAtomComposedJet L K x (r + 1) t := by
    apply intervalIntegral.integral_congr_ae'
    · filter_upwards [ae_deriv_canonicalPolePrimeRieszPrimitive_succ hL r] with t ht hmem
      have htIcc : t ∈ uIcc (0 : ℝ) L := by
        rw [uIcc_of_le hL.le]
        exact ⟨hmem.1.le, hmem.2⟩
      dsimp [P, G]
      rw [ht htIcc]
    · filter_upwards with t
      intro hmem
      exfalso
      linarith [hL, hmem.1, hmem.2]
  rw [hleft, hright, hP0, hGL] at hparts
  dsimp [P, G] at hparts
  linarith

/-- Scalar arithmetic factor multiplying the right-endpoint source jet in one
normalized Riesz step.  No sign is built into this definition. -/
def canonicalPolePrimeRieszEndpointScalar
    (L : ℝ) (r : ℕ) : ℝ :=
  (1 / L) ^ (r + 1) *
    canonicalPolePrimeRieszPrimitive L (r + 1) L

/-- Exact signed right-endpoint term in the normalized Riesz recurrence. -/
def canonicalPolePrimeRieszBoundaryTerm
    (L : ℝ) (r K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) : ℝ :=
  canonicalPolePrimeRieszEndpointScalar L r *
    iteratedDeriv (r + 1) (sourceAtomRealEnergy K x) 0

/-- Generic normalized Riesz recurrence with no endpoint-vanishing hypothesis. -/
theorem canonicalPolePrimeRieszEnergy_eq_succ_add_boundary
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (r : ℕ) :
    canonicalPolePrimeRieszEnergy L r K x =
      canonicalPolePrimeRieszEnergy L (r + 1) K x +
        canonicalPolePrimeRieszBoundaryTerm L r K x := by
  unfold canonicalPolePrimeRieszEnergy
  rw [canonicalPolePrimeRiesz_integral_step_with_boundary hL K x r]
  unfold canonicalPolePrimeRieszBoundaryTerm
  unfold canonicalPolePrimeRieszEndpointScalar
  rw [show r + 1 + 1 = (r + 1) + 1 by omega, pow_succ]
  ring

/-- The complete transformed production source channel has the same exact
one-step boundary recurrence. -/
theorem canonicalRieszSourceChannelEnergy_eq_succ_add_boundary
    {L : ℝ} (hL : 0 < L)
    (r K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    canonicalRieszSourceChannelEnergy L r K x =
      canonicalRieszSourceChannelEnergy L (r + 1) K x +
        canonicalPolePrimeRieszBoundaryTerm L r K x := by
  unfold canonicalRieszSourceChannelEnergy
  rw [canonicalPolePrimeRieszEnergy_eq_succ_add_boundary hL K x r]
  ring

/-- On a boundary-flat production carrier, the first boundary term beyond
order six factors through the arithmetic endpoint scalar and `|M_3|^2`. -/
theorem canonicalPolePrimeRieszBoundaryTerm_six_eq_moment_three
    (L : ℝ)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    canonicalPolePrimeRieszBoundaryTerm L 6 K x =
      -2 * (2 * Real.pi) ^ 6 *
        canonicalPolePrimeRieszEndpointScalar L 6 *
        Complex.normSq
          (centeredMoment K 3
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) := by
  unfold canonicalPolePrimeRieszBoundaryTerm
  rw [show 6 + 1 = 7 by norm_num]
  rw [iteratedDeriv_seven_sourceAtomRealEnergy_eq_moment_three K x hflat]
  ring

/-- On the even boundary-flat production sector, the first boundary term beyond
order eight factors through the arithmetic endpoint scalar and `|M_4|^2`. -/
theorem canonicalPolePrimeRieszBoundaryTerm_eight_eq_moment_four_of_even
    (L : ℝ)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
    (heven :
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
        evenCoefficientSubspace K) :
    canonicalPolePrimeRieszBoundaryTerm L 8 K x =
      2 * (2 * Real.pi) ^ 8 *
        canonicalPolePrimeRieszEndpointScalar L 8 *
        Complex.normSq
          (centeredMoment K 4
            ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) := by
  unfold canonicalPolePrimeRieszBoundaryTerm
  rw [show 8 + 1 = 9 by norm_num]
  rw [iteratedDeriv_nine_sourceAtomRealEnergy_eq_moment_four_of_even_boundaryFlat
    K x hflat heven]
  ring

/-- Exact complete-channel relation between Riesz orders six and seven on every
boundary-flat production carrier. -/
theorem canonicalRieszSourceChannelEnergy_six_eq_seven_sub_moment_three
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) :
    canonicalRieszSourceChannelEnergy L 6 K x =
      canonicalRieszSourceChannelEnergy L 7 K x -
        2 * (2 * Real.pi) ^ 6 *
          canonicalPolePrimeRieszEndpointScalar L 6 *
          Complex.normSq
            (centeredMoment K 3
              ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) := by
  rw [canonicalRieszSourceChannelEnergy_eq_succ_add_boundary hL 6 K x]
  rw [canonicalPolePrimeRieszBoundaryTerm_six_eq_moment_three L K x hflat]
  norm_num
  ring

/-- Exact complete-channel relation between Riesz orders eight and nine on the
even boundary-flat production sector. -/
theorem canonicalRieszSourceChannelEnergy_eight_eq_nine_add_moment_four
    {L : ℝ} (hL : 0 < L)
    (K : ℕ)
    (x : EuclideanSpace ℂ (Fin (2 * K + 1)))
    (hflat : BoundaryFlatCoefficients K
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x))
    (heven :
      ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x) ∈
        evenCoefficientSubspace K) :
    canonicalRieszSourceChannelEnergy L 8 K x =
      canonicalRieszSourceChannelEnergy L 9 K x +
        2 * (2 * Real.pi) ^ 8 *
          canonicalPolePrimeRieszEndpointScalar L 8 *
          Complex.normSq
            (centeredMoment K 4
              ((EuclideanSpace.equiv (Fin (2 * K + 1)) ℂ) x)) := by
  rw [canonicalRieszSourceChannelEnergy_eq_succ_add_boundary hL 8 K x]
  rw [canonicalPolePrimeRieszBoundaryTerm_eight_eq_moment_four_of_even
    L K x hflat heven]

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalPolePrimeRiesz_integral_step_with_boundary
#print axioms Zeta23.CCM.canonicalPolePrimeRieszEnergy_eq_succ_add_boundary
#print axioms Zeta23.CCM.canonicalRieszSourceChannelEnergy_eq_succ_add_boundary
#print axioms Zeta23.CCM.canonicalRieszSourceChannelEnergy_six_eq_seven_sub_moment_three
#print axioms Zeta23.CCM.canonicalRieszSourceChannelEnergy_eight_eq_nine_add_moment_four
