import Zeta23.CCM.ReciprocalApertureConcavity
import Zeta23.CCM.CanonicalSmallApertureGroundSpectrum

noncomputable section

namespace Zeta23.CCM

open Set

/-!
# WP2: the K=2 even-bottom gluing interface

The left endpoint is the unconditional #276 small-aperture theorem.
The interpolation inequality is an explicitly named hypothesis until
the WP1 canonical concavity application is compiled. The entire M51
range [1/400,log16] remains an *explicit hypothesis*: an external Arb
calculation is not promoted by this Lean implication.
-/

/-- A conditional interpolation/gluing theorem. The computational M51 lower
bound and the WP1 interpolation property remain independent inputs. -/
theorem k2EvenBottomGluing_of_interpolation_and_window
    (hEndpointBelowLog16 : (1 : ℝ) / 400 ≤ Real.log 16)
    (hInterpolation : ∀ L : ℝ,
      (1 : ℝ) / 512 ≤ L → L ≤ (1 : ℝ) / 400 →
        min (parityRayleighBottom .even ((1 : ℝ) / 512) 2)
            (parityRayleighBottom .even ((1 : ℝ) / 400) 2) ≤
          parityRayleighBottom .even L 2)
    (hM51 : ∀ L : ℝ, (1 : ℝ) / 400 ≤ L →
      L ≤ Real.log 16 → 0 < parityRayleighBottom .even L 2)
    (L : ℝ) (hL : 0 < L) (hL16 : L ≤ Real.log 16) :
    0 < parityRayleighBottom .even L 2 := by
  by_cases hsmall : L ≤ (1 : ℝ) / 512
  · have h := one_le_parityRayleighBottom_succ_of_smallAperture
      .even hL hsmall 1 (by norm_num)
    norm_num at h ⊢
    linarith
  · have hLower : (1 : ℝ) / 512 ≤ L := by
      have hs : (1 : ℝ) / 512 < L := lt_of_not_ge hsmall
      exact hs.le
    by_cases hupper : L ≤ (1 : ℝ) / 400
    · have hleft : 0 < parityRayleighBottom .even ((1 : ℝ) / 512) 2 := by
        have h := one_le_parityRayleighBottom_succ_of_smallAperture
          .even (by norm_num : (0 : ℝ) < 1 / 512)
          (by norm_num : (1 : ℝ) / 512 ≤ 1 / 512) 1 (by norm_num)
        linarith
      have hright : 0 < parityRayleighBottom .even ((1 : ℝ) / 400) 2 :=
        hM51 _ le_rfl hEndpointBelowLog16
      exact lt_of_lt_of_le (lt_min hleft hright)
        (hInterpolation L hLower hupper)
    · have hLower400 : (1 : ℝ) / 400 ≤ L :=
        (lt_of_not_ge hupper).le
      exact hM51 L hLower400 hL16

end Zeta23.CCM

#print axioms Zeta23.CCM.k2EvenBottomGluing_of_interpolation_and_window
