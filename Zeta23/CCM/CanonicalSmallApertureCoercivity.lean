import Zeta23.CCM.CanonicalSourceChannels
import Zeta23.CCM.CanonicalSourceEnergy
import Zeta23.CCM.CanonicalArchUpperBound
import Zeta23.CCM.CanonicalPoleUniformBound

noncomputable section

namespace Zeta23.CCM

/-!
# Closure campaign A1: exact assembly of the uniform base

The analytic channel estimates are explicit hypotheses. The matrix-level
assembly itself is proved here without RH, project axioms, or placeholders.
-/

/-- Prime-channel vanishing required in the conservative small-aperture range. -/
def CanonicalSmallAperturePrimeVanishing : Prop :=
  ∀ L : ℝ, 0 < L → L ≤ (1 : ℝ) / 512 →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      matrixRealEnergy (canonicalPrimeMatrix L K) x = 0

/-- The three exact channel obligations for the paper proof. -/
def CanonicalSmallApertureChannelBounds : Prop :=
  CanonicalArchSmallApertureUpperBound ∧
    CanonicalPoleCubicLowerBound ∧
      CanonicalSmallAperturePrimeVanishing

/-- Exact algebraic assembly of the three channel bounds in the production
normalization. -/
theorem canonicalSourceMatrix_small_aperture_lower_of_channel_bounds
    (hb : CanonicalSmallApertureChannelBounds)
    (L : ℝ) (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512)
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    (2 - L - (2 / 9 : ℝ) * L ^ 3) * ‖x‖ ^ 2 ≤
      matrixRealEnergy (canonicalSourceMatrix L K) x := by
  have harch := hb.1 L hL hsmall K x
  have hpole := hb.2.1 L hL hsmall K x
  have hprime := hb.2.2 L hL hsmall K x
  rw [canonicalSourceMatrix_eq_pole_sub_arch_sub_prime,
    matrixRealEnergy_sub, matrixRealEnergy_sub, hprime]
  nlinarith

/-- The conservative scalar margin in the paper proof is at least one. -/
theorem smallAperture_scalar_margin_ge_one
    (L : ℝ) (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512) :
    1 ≤ 2 - L - (2 / 9 : ℝ) * L ^ 3 := by
  have hL0 : 0 ≤ L := le_of_lt hL
  have hL1 : L ≤ 1 := by
    linarith
  have hquad : 0 ≤ L * (1 - L) :=
    mul_nonneg hL0 (sub_nonneg.mpr hL1)
  have hcubic : 0 ≤ L ^ 2 * (1 - L) :=
    mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL1)
  have hL3 : L ^ 3 ≤ L := by
    nlinarith
  nlinarith

/-- Full-space coercivity follows once the three analytic channel obligations
are supplied. This theorem itself is unconditional relative to those explicit
inputs and is not an RH theorem. -/
theorem canonicalSourceMatrix_small_aperture_coercive_of_channel_bounds
    (hb : CanonicalSmallApertureChannelBounds)
    (L : ℝ) (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512)
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖x‖ ^ 2 ≤ matrixRealEnergy (canonicalSourceMatrix L K) x := by
  have hraw :=
    canonicalSourceMatrix_small_aperture_lower_of_channel_bounds
      hb L hL hsmall K x
  have hmargin := smallAperture_scalar_margin_ge_one L hL hsmall
  have hnorm : 0 ≤ ‖x‖ ^ 2 := sq_nonneg ‖x‖
  have hscale :
      ‖x‖ ^ 2 ≤
        (2 - L - (2 / 9 : ℝ) * L ^ 3) * ‖x‖ ^ 2 := by
    nlinarith
  exact le_trans hscale hraw

/-- Named target used by the closure obligation overlay. -/
def CanonicalSmallApertureCoercivity : Prop :=
  ∀ L : ℝ, 0 < L → L ≤ (1 : ℝ) / 512 →
    ∀ K : ℕ, ∀ x : EuclideanSpace ℂ (Fin (2 * K + 1)),
      ‖x‖ ^ 2 ≤ matrixRealEnergy (canonicalSourceMatrix L K) x

theorem canonicalSmallApertureCoercivity_of_channel_bounds
    (hb : CanonicalSmallApertureChannelBounds) :
    CanonicalSmallApertureCoercivity := by
  intro L hL hsmall K x
  exact canonicalSourceMatrix_small_aperture_coercive_of_channel_bounds
    hb L hL hsmall K x

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalSourceMatrix_small_aperture_lower_of_channel_bounds
#print axioms Zeta23.CCM.smallAperture_scalar_margin_ge_one
#print axioms Zeta23.CCM.canonicalSourceMatrix_small_aperture_coercive_of_channel_bounds
