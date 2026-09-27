import Mathlib.Analysis.Complex.Exponential
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

/-- The conservative aperture range lies below the first prime
threshold, so the prime-power channel is exactly empty. -/
theorem canonicalPrimeMatrix_eq_zero_of_small_aperture
    (L : ℝ) (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512)
    (K : ℕ) :
    canonicalPrimeMatrix L K = 0 := by
  have hL2 : L < 2 := by
    linarith
  have hexpBound := Real.exp_lt_two_add_div_two_sub hL hL2
  have hden : 0 < 2 - L := by
    linarith
  have hratio : (2 + L) / (2 - L) < (2 : ℝ) := by
    rw [div_lt_iff₀ hden]
    nlinarith
  have hexp2 : Real.exp L < (2 : ℝ) :=
    lt_trans hexpBound hratio
  have hfloor : ⌊Real.exp L⌋₊ < 2 :=
    (Nat.floor_lt (Real.exp_pos L).le).2 hexp2
  have hIcc : Finset.Icc 2 ⌊Real.exp L⌋₊ = ∅ :=
    Finset.Icc_eq_empty_of_lt hfloor
  ext i j
  simp [canonicalPrimeMatrix, primeComponent, hIcc]

/-- The prime-energy vanishing premise of the base theorem is discharged
unconditionally on the chosen aperture range. -/
theorem canonicalSmallAperturePrimeVanishing_proved :
    CanonicalSmallAperturePrimeVanishing := by
  intro L hL hsmall K x
  rw [canonicalPrimeMatrix_eq_zero_of_small_aperture L hL hsmall K]
  exact matrixRealEnergy_zero x

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

#print axioms Zeta23.CCM.canonicalPrimeMatrix_eq_zero_of_small_aperture
#print axioms Zeta23.CCM.canonicalSmallAperturePrimeVanishing_proved
#print axioms Zeta23.CCM.canonicalSourceMatrix_small_aperture_lower_of_channel_bounds
#print axioms Zeta23.CCM.smallAperture_scalar_margin_ge_one
#print axioms Zeta23.CCM.canonicalSourceMatrix_small_aperture_coercive_of_channel_bounds
