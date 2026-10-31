import Zeta23.CCM.CanonicalPoleNeutralShiftedSecular
import Mathlib.Tactic

noncomputable section

namespace Zeta23.OPICARound4

open CCM

/-!
These are deliberately CONDITIONAL source-native applications of already
compiled shifted-ray theorems.  They never assert the required strict source
bound, a negative eigenvalue, Step 4 closure, or RH.
-/

/-- An independently supplied strict even corrected-source bound excludes an
actual even eigenvector below the ACTUAL odd parity bottom. -/
theorem no_even_eigen_from_independent_ray_bound
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (hlam : lam < poleNeutralOddRayleighBottom L K hL hK)
    (hbound : (poleNeutralCorrectedCubicSource L K
      (poleNeutralEvenShiftedRay hL K hK lam hlam)).re < 1) :
    ¬ ∃ u : poleNeutralEvenSubspace L K, u ≠ 0 ∧
      poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u := by
  rintro ⟨u, hu0, hu⟩
  have hsource := poleNeutral_even_eigen_shiftedRay_source_eq_one
    hL K hK lam hlam u hu0 hu
  rw [hsource] at hbound
  norm_num at hbound

/-- The corresponding odd result uses the genuine adjoint and its own source
pairing; replacing it with the even source is not permitted. -/
theorem no_odd_eigen_from_independent_ray_bound
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (lam : ℝ) (hlam : lam < poleNeutralEvenRayleighBottom L K hL hK)
    (hbound : (poleNeutralCubicPairingFunctional L K
      (poleNeutralOddAdjointShiftedRay hL K hK lam hlam)).re < 1) :
    ¬ ∃ w : poleNeutralOddSubspace L K, w ≠ 0 ∧
      poleNeutralOddCompressedCanonical L K w = (lam : ℂ) • w := by
  rintro ⟨w, hw0, hw⟩
  have hsource := poleNeutral_odd_eigen_adjointRay_pairing_eq_one
    hL K hK lam hlam w hw0 hw
  rw [hsource] at hbound
  norm_num at hbound

end Zeta23.OPICARound4
