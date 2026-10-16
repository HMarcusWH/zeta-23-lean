import Zeta23.CCM.CanonicalPoleNeutralTrialResidualBounds
import Zeta23.CCM.CanonicalPoleNeutralSimpleEvenTie

/-!
# Canonical corrected source, trial-residual and simple-eigenspace constraints

The imported exact R2/R3 statements use the native corrected source. The
simple-even theorem permits a parity tie and keeps its simplicity hypothesis;
it makes no assertion that the corrected source is nonzero at a tie.
-/

noncomputable section

namespace Zeta23.CCM

/-- The general eigenvalue version keeps the actual spectral parameter. -/
theorem poleNeutral_even_eigen_source_moment_pos_of_lt_odd_bottom
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)
    (hgap : lam < poleNeutralOddRayleighBottom L K hL hK) :
    0 < (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re := by
  have hnormu : 0 < ‖u‖ ^ 2 := pow_pos (norm_pos_iff.mpr hu0) 2
  have hindex := poleNeutralIndex_norm_lower hL K u
  have hnormD : 0 < ‖poleNeutralIndexLinearMap hL K u‖ ^ 2 := by nlinarith
  exact (mul_pos (sub_pos.mpr hgap) hnormD).trans_le
    (poleNeutral_source_moment_gap_le hL K hK lam u hu)

theorem poleNeutral_even_eigen_momentFour_ne_zero_of_lt_odd_bottom
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)
    (hgap : lam < poleNeutralOddRayleighBottom L K hL hK) :
    centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) ≠ 0 := by
  intro hm
  have hp := poleNeutral_even_eigen_source_moment_pos_of_lt_odd_bottom
    hL K hK lam u hu0 hu hgap
  rw [hm, mul_zero, Complex.zero_re] at hp
  exact (lt_irrefl 0) hp

theorem poleNeutral_simpleEven_momentFour_ne_zero
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)
    (hlam : lam ≤ poleNeutralOddRayleighBottom L K hL hK)
    (hsimple : Module.finrank ℂ
      (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K) (lam : ℂ)) = 1) :
    centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val) ≠ 0 :=
  poleNeutral_momentFour_ne_zero_of_simple_even_of_le_odd_bottom
    hL K hK lam u hu0 hu hlam hsimple

end Zeta23.CCM

#print axioms Zeta23.CCM.poleNeutral_simpleEven_momentFour_ne_zero
#print axioms Zeta23.CCM.poleNeutral_even_eigen_source_moment_pos_of_lt_odd_bottom
#print axioms Zeta23.CCM.poleNeutral_even_eigen_momentFour_ne_zero_of_lt_odd_bottom
