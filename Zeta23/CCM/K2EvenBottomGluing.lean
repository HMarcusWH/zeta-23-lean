import Zeta23.CCM.ReciprocalApertureConcavity
import Zeta23.CCM.CanonicalSmallApertureGroundSpectrum

noncomputable section

namespace Zeta23.CCM

/-!
# WP2: K2 even positivity hybrid with explicit M51 evidence premise

This integration lemma combines the PROVED uniform small-aperture bound,
the (not-yet-exported) reciprocal-aperture bottom interpolation, and the
research-only M51 Arb positive interval.  Both latter facts are deliberately
exposed as hypotheses.  Thus this file does NOT assert an unconditional
continuous K2 positivity theorem and does not promote the Arb transcript
to Lean authority.  It provides a compiler-checked destination for WP1
and M51 once their exact certificates are separately verified.
-/

/-- Conditional and scope-correct gap-gluing: the small-aperture theorem
supplies a unit margin through 1/512, while the explicit bottom-interpolation
input transports the positive M51 endpoint at 1/400 to the gap.

The closing M51 interval is an explicit input, *not* a theorem of this module.
-/
theorem k2EvenBottom_positive_of_interpolation_and_M51
    (hGap :
      ∀ L ∈ Set.Icc ((1 : ℝ) / 512) ((1 : ℝ) / 400),
        min (parityRayleighBottom .even ((1 : ℝ) / 512) 2)
            (parityRayleighBottom .even ((1 : ℝ) / 400) 2) ≤
          parityRayleighBottom .even L 2)
    (hM51endpoint :
      0 < parityRayleighBottom .even ((1 : ℝ) / 400) 2)
    (hM51 :
      ∀ L ∈ Set.Icc ((1 : ℝ) / 400) (Real.log 16),
        0 < parityRayleighBottom .even L 2)
    {L : ℝ} (hL : 0 < L) (hUpper : L ≤ Real.log 16) :
    0 < parityRayleighBottom .even L 2 := by
  by_cases hsmall : L ≤ (1 : ℝ) / 512
  · have hbase : 1 ≤ parityRayleighBottom .even L 2 := by
      simpa using
        (one_le_parityRayleighBottom_succ_of_smallAperture
          .even hL hsmall 1 (by omega))
    linarith
  · have hLgt : (1 : ℝ) / 512 < L := lt_of_not_ge hsmall
    by_cases hmid : L ≤ (1 : ℝ) / 400
    · have hbase : 1 ≤ parityRayleighBottom .even ((1 : ℝ) / 512) 2 := by
        have hpos : 0 < (1 : ℝ) / 512 := by norm_num
        simpa using
          (one_le_parityRayleighBottom_succ_of_smallAperture
            .even hpos (le_refl _) 1 (by omega))
      have hmin : 0 <
          min (parityRayleighBottom .even ((1 : ℝ) / 512) 2)
              (parityRayleighBottom .even ((1 : ℝ) / 400) 2) :=
        lt_min (by linarith) hM51endpoint
      exact lt_of_lt_of_le hmin
        (hGap L ⟨le_of_lt hLgt, hmid⟩)
    · have hleft : (1 : ℝ) / 400 ≤ L :=
        le_of_lt (lt_of_not_ge hmid)
      exact hM51 L ⟨hleft, hUpper⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.k2EvenBottom_positive_of_interpolation_and_M51
