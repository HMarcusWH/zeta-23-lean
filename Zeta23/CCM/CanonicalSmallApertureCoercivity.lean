import Mathlib.Analysis.Complex.Exponential
import Zeta23.CCM.CanonicalSourceChannels
import Zeta23.CCM.CanonicalSourceEnergy
import Zeta23.CCM.CanonicalArchUpperBound
import Zeta23.CCM.CanonicalPoleUniformBound
import Zeta23.CCM.CanonicalPoleSourceBound

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

/-- After prime vanishing is proved, only the two analytic channel estimates
remain as genuine premises of the uniform base. -/
def CanonicalSmallApertureAnalyticBounds : Prop :=
  CanonicalArchSmallApertureUpperBound ∧ CanonicalPoleCubicLowerBound

theorem canonicalSmallApertureChannelBounds_of_analytic_bounds
    (h : CanonicalSmallApertureAnalyticBounds) :
    CanonicalSmallApertureChannelBounds :=
  ⟨h.1, h.2, canonicalSmallAperturePrimeVanishing_proved⟩

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

/-- Reduced two-premise form of the base theorem after exact prime vanishing. -/
theorem canonicalSmallApertureCoercivity_of_analytic_bounds
    (h : CanonicalSmallApertureAnalyticBounds) :
    CanonicalSmallApertureCoercivity :=
  canonicalSmallApertureCoercivity_of_channel_bounds
    (canonicalSmallApertureChannelBounds_of_analytic_bounds h)

/-- Cheaper analytic input package discovered by the closure campaign.
The cubic pole estimate remains available as a stronger historical target, but
is not required for the tiny-aperture positive base: source contraction already
supplies a sufficient uniform pole lower bound. -/
def CanonicalSmallApertureSourceArchBounds : Prop :=
  SourceContractionBound ∧ CanonicalArchSmallApertureUpperBound

/-- Source contraction gives a coarse pole estimate strong enough to combine
with the canonical archimedean upper bound and exact prime vanishing. -/
theorem canonicalSourceMatrix_small_aperture_lower_of_source_arch
    (hsrc : SourceContractionBound)
    (harch : CanonicalArchSmallApertureUpperBound)
    (L : ℝ) (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512)
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    (2 - L - (1 / 64 : ℝ)) * ‖x‖ ^ 2 ≤
      matrixRealEnergy (canonicalSourceMatrix L K) x := by
  have ha := harch L hL hsmall K x
  have hp :
      -(1 / 64 : ℝ) * ‖x‖ ^ 2 ≤
        matrixRealEnergy (canonicalPoleMatrix L K) x :=
    (canonicalPoleSmallApertureLowerBound_of_sourceContraction hsrc)
      L hL hsmall K x
  have hprime :=
    canonicalSmallAperturePrimeVanishing_proved L hL hsmall K x
  rw [canonicalSourceMatrix_eq_pole_sub_arch_sub_prime,
    matrixRealEnergy_sub, matrixRealEnergy_sub, hprime]
  nlinarith

/-- The coarse source-derived pole estimate still leaves a strict margin above
one throughout the frozen base interval. -/
theorem smallAperture_source_arch_margin_ge_one
    (L : ℝ) (_hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512) :
    1 ≤ 2 - L - (1 / 64 : ℝ) := by
  linarith

/-- Full-space tiny-aperture coercivity from the two genuinely needed analytic
inputs: source contraction and the canonical archimedean bound. -/
theorem canonicalSourceMatrix_small_aperture_coercive_of_source_arch
    (hsrc : SourceContractionBound)
    (harch : CanonicalArchSmallApertureUpperBound)
    (L : ℝ) (hL : 0 < L) (hsmall : L ≤ (1 : ℝ) / 512)
    (K : ℕ) (x : EuclideanSpace ℂ (Fin (2 * K + 1))) :
    ‖x‖ ^ 2 ≤ matrixRealEnergy (canonicalSourceMatrix L K) x := by
  have hraw :=
    canonicalSourceMatrix_small_aperture_lower_of_source_arch
      hsrc harch L hL hsmall K x
  have hmargin :=
    smallAperture_source_arch_margin_ge_one L hL hsmall
  have hnorm : 0 ≤ ‖x‖ ^ 2 := sq_nonneg ‖x‖
  have hscale :
      ‖x‖ ^ 2 ≤
        (2 - L - (1 / 64 : ℝ)) * ‖x‖ ^ 2 := by
    nlinarith
  exact le_trans hscale hraw

/-- Dependency-compressed base theorem.  Prime vanishing and the coarse pole
bound are discharged internally. -/
theorem canonicalSmallApertureCoercivity_of_source_arch
    (h : CanonicalSmallApertureSourceArchBounds) :
    CanonicalSmallApertureCoercivity := by
  intro L hL hsmall K x
  exact canonicalSourceMatrix_small_aperture_coercive_of_source_arch
    h.1 h.2 L hL hsmall K x

end Zeta23.CCM

#print axioms Zeta23.CCM.canonicalPrimeMatrix_eq_zero_of_small_aperture
#print axioms Zeta23.CCM.canonicalSmallAperturePrimeVanishing_proved
#print axioms Zeta23.CCM.canonicalSmallApertureChannelBounds_of_analytic_bounds
#print axioms Zeta23.CCM.canonicalSmallApertureCoercivity_of_analytic_bounds
#print axioms Zeta23.CCM.canonicalSourceMatrix_small_aperture_lower_of_channel_bounds
#print axioms Zeta23.CCM.smallAperture_scalar_margin_ge_one
#print axioms Zeta23.CCM.canonicalSourceMatrix_small_aperture_coercive_of_channel_bounds

#print axioms Zeta23.CCM.canonicalSourceMatrix_small_aperture_lower_of_source_arch
#print axioms Zeta23.CCM.smallAperture_source_arch_margin_ge_one
#print axioms Zeta23.CCM.canonicalSourceMatrix_small_aperture_coercive_of_source_arch
#print axioms Zeta23.CCM.canonicalSmallApertureCoercivity_of_source_arch
