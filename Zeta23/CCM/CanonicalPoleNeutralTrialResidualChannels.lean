import Zeta23.CCM.CanonicalPoleNeutralPublicAPI
import Zeta23.CCM.NativeDetectorSchur
import Zeta23.CCM.CanonicalPoleNeutralTrialResidualBounds

noncomputable section
namespace Zeta23.CCM
open scoped BigOperators ComplexConjugate

/-! The old legal residual is preserved verbatim. Its public facade and the
new neutral residual have deliberately different domains. -/
alias canonicalTrialResidual_variance_eq := canonicalTrialResidual_variance
alias canonicalTrialResidual_gram_sum := canonicalTrialResidual_channelGram

theorem canonicalTrialResidual_channels_sum (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : euclideanParityBoundaryFlatSubspace sigma K) :
    canonicalTrialResidual sigma L K p =
      ∑ i, nativeTrialResidual (parityCanonicalTrialChannel sigma L K i) p := by
  unfold canonicalTrialResidual
  rw [← parityCanonicalTrialChannel_sum]
  exact nativeTrialResidual_sum _ _

/-- Real Rayleigh value of the actual own-parity neutral trial operator. -/
def canonicalPoleNeutralTrialRayleigh (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) : ℝ :=
  (inner ℂ p (nativePoleNeutralParityCanonical sigma L K p)).re

/-- The neutral residual, independent of any later selected-ground parity. -/
def canonicalPoleNeutralTrialResidual (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) : nativePoleNeutralParitySpace sigma L K :=
  nativePoleNeutralParityCanonical sigma L K p -
    (canonicalPoleNeutralTrialRayleigh sigma L K p : ℂ) • p

def canonicalPoleNeutralTrialChannel (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (i : Fin 4) :
    nativePoleNeutralParitySpace sigma L K →ₗ[ℂ] nativePoleNeutralParitySpace sigma L K := by
  cases sigma
  · exact poleNeutralEvenCanonicalTrialChannel L K i
  · exact poleNeutralOddCanonicalTrialChannel L K i

theorem canonicalPoleNeutralTrialChannel_sum (sigma : ReversalParity) (L : ℝ) (K : ℕ) :
    (∑ i, canonicalPoleNeutralTrialChannel sigma L K i) =
      nativePoleNeutralParityCanonical sigma L K := by
  cases sigma
  · exact poleNeutralEvenCanonicalTrialChannel_sum L K
  · exact poleNeutralOddCanonicalTrialChannel_sum L K

theorem canonicalPoleNeutralTrial_operator_isSymmetric
    (sigma : ReversalParity) (L : ℝ) (K : ℕ) :
    (nativePoleNeutralParityCanonical sigma L K).IsSymmetric := by
  cases sigma
  · exact poleNeutralEvenCompressedCanonical_isSymmetric L K
  · exact poleNeutralOddCompressedCanonical_isSymmetric L K

theorem canonicalPoleNeutralTrialRayleigh_complex_eq
    (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) :
    nativeTrialRayleigh (nativePoleNeutralParityCanonical sigma L K) p =
      (canonicalPoleNeutralTrialRayleigh sigma L K p : ℂ) := by
  apply Complex.ext
  · rfl
  · exact nativeTrialRayleigh_im_eq_zero _
      (canonicalPoleNeutralTrial_operator_isSymmetric sigma L K) p

theorem canonicalPoleNeutralTrialResidual_eq_native
    (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) :
    canonicalPoleNeutralTrialResidual sigma L K p =
      nativeTrialResidual (nativePoleNeutralParityCanonical sigma L K) p := by
  simp only [canonicalPoleNeutralTrialResidual, nativeTrialResidual,
    canonicalPoleNeutralTrialRayleigh_complex_eq]

theorem canonicalPoleNeutralTrialResidual_orthogonal
    (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) (hp : ‖p‖ = 1) :
    inner ℂ p (canonicalPoleNeutralTrialResidual sigma L K p) = 0 := by
  rw [canonicalPoleNeutralTrialResidual_eq_native]
  exact nativeTrialResidual_orthogonal _ p hp

theorem canonicalPoleNeutralTrialResidual_variance_eq
    (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) (hp : ‖p‖ = 1) :
    ‖canonicalPoleNeutralTrialResidual sigma L K p‖ ^ 2 =
      (inner ℂ p (nativePoleNeutralParityCanonical sigma L K
        (nativePoleNeutralParityCanonical sigma L K p))).re -
      canonicalPoleNeutralTrialRayleigh sigma L K p ^ 2 := by
  rw [canonicalPoleNeutralTrialResidual_eq_native,
    nativeTrialResidual_symmetric_variance _
      (canonicalPoleNeutralTrial_operator_isSymmetric sigma L K) p hp,
    canonicalPoleNeutralTrialRayleigh_complex_eq]
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]

theorem canonicalPoleNeutralTrialResidual_channels_sum
    (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) :
    canonicalPoleNeutralTrialResidual sigma L K p =
      ∑ i, nativeTrialResidual (canonicalPoleNeutralTrialChannel sigma L K i) p := by
  rw [canonicalPoleNeutralTrialResidual_eq_native, ← canonicalPoleNeutralTrialChannel_sum]
  exact nativeTrialResidual_sum _ _

/-- Full complex Gram, including every off-diagonal pairing. -/
def canonicalPoleNeutralTrialChannelGram (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) (i j : Fin 4) : ℂ :=
  nativeTrialChannelGram (canonicalPoleNeutralTrialChannel sigma L K) p i j

theorem canonicalPoleNeutralTrialResidual_gram_sum
    (sigma : ReversalParity) (L : ℝ) (K : ℕ)
    (p : nativePoleNeutralParitySpace sigma L K) :
    ‖canonicalPoleNeutralTrialResidual sigma L K p‖ ^ 2 =
      (∑ i, ∑ j, canonicalPoleNeutralTrialChannelGram sigma L K p i j).re := by
  rw [canonicalPoleNeutralTrialResidual_eq_native, ← canonicalPoleNeutralTrialChannel_sum]
  exact nativeTrialResidual_gram_sum _ _

/-- R3 is an eligible-even statement at the measured Rayleigh parameter.
Neither negative depth nor the selected even ground is substituted here. -/
theorem canonicalPoleNeutralTrialResidual_even_eq_R3 (L : ℝ) (K : ℕ)
    (p : poleNeutralEvenSubspace L K) :
    canonicalPoleNeutralTrialResidual .even L K p =
      poleNeutralTrialResidual L K (canonicalPoleNeutralTrialRayleigh .even L K p) p := rfl

theorem canonicalPoleNeutralTrialResidual_even_momentFour_lower
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (p : poleNeutralEvenSubspace L K)
    (hgap : canonicalPoleNeutralTrialRayleigh .even L K p <
      poleNeutralOddRayleighBottom L K hL hK)
    (hm : centeredMoment K 4 (evenBoundaryFlatRawCoefficients K p.val) = 0) :
    (poleNeutralOddRayleighBottom L K hL hK -
      canonicalPoleNeutralTrialRayleigh .even L K p) * ‖p‖ / (2 * (K : ℝ)) ≤
        ‖canonicalPoleNeutralTrialResidual .even L K p‖ := by
  rw [canonicalPoleNeutralTrialResidual_even_eq_R3]
  exact poleNeutral_momentFour_zero_residual_lower hL K hK _ p hgap hm

end Zeta23.CCM
#print axioms Zeta23.CCM.canonicalTrialResidual_channels_sum
#print axioms Zeta23.CCM.canonicalPoleNeutralTrialResidual_orthogonal
#print axioms Zeta23.CCM.canonicalPoleNeutralTrialResidual_variance_eq
#print axioms Zeta23.CCM.canonicalPoleNeutralTrialResidual_channels_sum
#print axioms Zeta23.CCM.canonicalPoleNeutralTrialResidual_gram_sum
#print axioms Zeta23.CCM.canonicalPoleNeutralTrialResidual_even_eq_R3
#print axioms Zeta23.CCM.canonicalPoleNeutralTrialResidual_even_momentFour_lower

