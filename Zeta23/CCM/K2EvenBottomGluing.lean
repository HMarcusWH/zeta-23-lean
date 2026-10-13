import Zeta23.CCM.ReciprocalApertureConcavity
import Zeta23.CCM.CanonicalSmallApertureGroundSpectrum

noncomputable section

namespace Zeta23.CCM

/-!
# WP2: K2 even positivity hybrid with explicit M51 evidence premise

This module combines the PROVED uniform small-aperture bound and M66
reciprocal-aperture bottom interpolation with an explicit M51 positive-window
premise. The auxiliary adapters expose the interpolation inputs separately;
`k2EvenBottom_positive_of_M66_and_M51` discharges those analytic inputs using
the canonical C² family and the proved M66 curvature radius.

The M51 whole-window positivity premise remains explicit in the final theorem.
An Arb transcript is research evidence and is not promoted to Lean authority,
so unconditional continuous K2 positivity is not asserted here.
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

/-- The WP2 hybrid K2 positivity theorem in its actual canonical
reciprocal-concavity interface.  It is stronger than the elementary gluing
adapter: the interpolation hypothesis has now been replaced by per-vector
normalized canonical concavity, discharged for the Rayleigh iInf by WP1.

The M51 finite-window certificate is *still an explicit premise*; Arb
research evidence is never silently converted to Lean theorem authority.
-/
theorem k2EvenBottom_positive_of_reciprocal_concavity_and_M51
    (hlog : (1 : ℝ) / 400 ≤ Real.log 16)
    (hConcave :
      ∀ z : euclideanEvenBoundaryFlatSubspace 2, z ≠ 0 →
        ConcaveOn ℝ
          (Set.Icc (((1 : ℝ) / 400)⁻¹) (((1 : ℝ) / 512)⁻¹))
          (fun s : ℝ =>
            productionContactFixedEnergy .even s⁻¹ 2 z / ‖z‖ ^ 2))
    (hM51 : ∀ L ∈ Set.Icc ((1 : ℝ) / 400) (Real.log 16),
        0 < parityRayleighBottom .even L 2)
    {L : ℝ} (hL : 0 < L) (hUpper : L ≤ Real.log 16) :
    0 < parityRayleighBottom .even L 2 := by
  have hgap :
      ∀ t ∈ Set.Icc ((1 : ℝ) / 512) ((1 : ℝ) / 400),
        min (parityRayleighBottom .even ((1 : ℝ) / 512) 2)
          (parityRayleighBottom .even ((1 : ℝ) / 400) 2) ≤
          parityRayleighBottom .even t 2 := by
    intro t ht
    exact evenRayleighBottom_ge_endpoint_min_of_reciprocal_concavity
      (K := 2) (by norm_num : 2 ≤ 2)
      (a := (1 : ℝ) / 512) (b := (1 : ℝ) / 400) (L := t)
      (by norm_num) ht.1 ht.2 hConcave
  have hM51endpoint : 0 <
      parityRayleighBottom .even ((1 : ℝ) / 400) 2 :=
    hM51 _ ⟨le_refl _, hlog⟩
  exact k2EvenBottom_positive_of_interpolation_and_M51
    hgap hM51endpoint hM51 hL hUpper

/-- WP4's independent K2 odd predecessor layer. The full finite-window
positivity hypothesis remains explicit: the only unconditional part
is the already proved #275 small-aperture coercivity on both parities.

This is a conditional Lean transfer, not a proof of the Arb certificate. -/
theorem k2OddBottom_positive_of_finite_window
    (hOdd : ∀ L ∈ Set.Icc ((1 : ℝ) / 512) (Real.log 16),
        0 < parityRayleighBottom .odd L 2)
    {L : ℝ} (hL : 0 < L) (hUpper : L ≤ Real.log 16) :
    0 < parityRayleighBottom .odd L 2 := by
  by_cases hsmall : L ≤ (1 : ℝ) / 512
  · have hb : 1 ≤ parityRayleighBottom .odd L 2 := by
      simpa using
        (one_le_parityRayleighBottom_succ_of_smallAperture
          .odd hL hsmall 1 (by omega))
    linarith
  · have hgt : (1 : ℝ) / 512 ≤ L :=
      (lt_of_not_ge hsmall).le
    exact hOdd L ⟨hgt,hUpper⟩

/-- K2 gap gluing from concavity of the *unnormalized* native
source energies, the direct shape supplied by the M66 Euler-curvature
calculus.  The actual analytic concavity and the externally computed M51
interval remain visible premises until established by their exact gates. -/
theorem k2EvenBottom_positive_of_raw_concavity_and_M51
    (hlog : (1 : ℝ) / 400 ≤ Real.log 16)
    (hRawConcave :
      ∀ z : euclideanEvenBoundaryFlatSubspace 2, z ≠ 0 →
        ConcaveOn ℝ
          (Set.Icc (((1 : ℝ) / 400)⁻¹) (((1 : ℝ) / 512)⁻¹))
          (fun s : ℝ => productionContactFixedEnergy .even s⁻¹ 2 z))
    (hM51 : ∀ L ∈ Set.Icc ((1 : ℝ) / 400) (Real.log 16),
        0 < parityRayleighBottom .even L 2)
    {L : ℝ} (hL : 0 < L) (hUpper : L ≤ Real.log 16) :
    0 < parityRayleighBottom .even L 2 := by
  have hgap :
      ∀ t ∈ Set.Icc ((1 : ℝ) / 512) ((1 : ℝ) / 400),
        min (parityRayleighBottom .even ((1 : ℝ) / 512) 2)
          (parityRayleighBottom .even ((1 : ℝ) / 400) 2) ≤
          parityRayleighBottom .even t 2 := by
    intro t ht
    exact evenRayleighBottom_ge_endpoint_min_of_raw_reciprocal_concavity
      (K := 2) (by norm_num : 2 ≤ 2)
      (a := (1 : ℝ) / 512) (b := (1 : ℝ) / 400) (L := t)
      (by norm_num) ht.1 ht.2 hRawConcave
  have he : 0 < parityRayleighBottom .even ((1 : ℝ) / 400) 2 :=
    hM51 _ ⟨le_refl _, hlog⟩
  exact k2EvenBottom_positive_of_interpolation_and_M51
    hgap he hM51 hL hUpper

/-- Numerically simple but necessary exact radius comparison: K=2's
proved M66 radius extends strictly past the M51 start at 1/400.
The proof uses the pinned Mathlib pi < 3.15 bound, not sampling. -/
theorem one_div_400_lt_primeFreeRadius_two :
    (1 : ℝ) / 400 < primeFreeRadius 2 := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hpiTop : Real.pi < (63 : ℝ) / 20 := by
    simpa [show (3.15 : ℝ) = 63 / 20 by norm_num] using Real.pi_lt_d2
  have hpi2 : Real.pi ^ 2 < 10 := by
    nlinarith [sq_nonneg (Real.pi - 63 / 20)]
  have hRadius : primeFreeRadius 2 = 1 / (40 * Real.pi ^ 2) := by
    unfold primeFreeRadius
    congr 1
    norm_num
    ring
  rw [hRadius]
  apply (div_lt_div_iff₀ (by norm_num : (0 : ℝ) < 400)
      (by positivity : 0 < 40 * Real.pi ^ 2)).2
  nlinarith

/-- WP2's mathematical gap-closing result with **all analytic**
interpolation hypotheses discharged by M66 and the already proved
canonical C² operator realization. The interval-certified M51 premise
is deliberately STILL EXPLICIT and must be independently verified. -/
theorem k2EvenBottom_positive_of_M66_and_M51
    (hM51 : ∀ L ∈ Set.Icc ((1 : ℝ) / 400) (Real.log 16),
        0 < parityRayleighBottom .even L 2)
    {L : ℝ} (hL : 0 < L) (hUpper : L ≤ Real.log 16) :
    0 < parityRayleighBottom .even L 2 := by
  have hlog : (1 : ℝ) / 400 ≤ Real.log 16 := by
    have hLower := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 16)
    norm_num at hLower
    linarith
  have hgap :
      ∀ t ∈ Set.Icc ((1 : ℝ) / 512) ((1 : ℝ) / 400),
        min (parityRayleighBottom .even ((1 : ℝ) / 512) 2)
          (parityRayleighBottom .even ((1 : ℝ) / 400) 2) ≤
          parityRayleighBottom .even t 2 := by
    intro t ht
    exact evenRayleighBottom_ge_endpoint_min_of_M66 2 (by norm_num : 2 ≤ 2)
      (by norm_num : (0 : ℝ) < 1 / 512) ht.1 ht.2
      one_div_400_lt_primeFreeRadius_two
  have he : 0 < parityRayleighBottom .even ((1 : ℝ) / 400) 2 :=
    hM51 _ ⟨le_refl _, hlog⟩
  exact k2EvenBottom_positive_of_interpolation_and_M51
    hgap he hM51 hL hUpper

end Zeta23.CCM

#print axioms Zeta23.CCM.k2EvenBottom_positive_of_interpolation_and_M51

#print axioms Zeta23.CCM.k2EvenBottom_positive_of_reciprocal_concavity_and_M51

#print axioms Zeta23.CCM.k2OddBottom_positive_of_finite_window

#print axioms Zeta23.CCM.k2EvenBottom_positive_of_raw_concavity_and_M51

#print axioms Zeta23.CCM.one_div_400_lt_primeFreeRadius_two
#print axioms Zeta23.CCM.k2EvenBottom_positive_of_M66_and_M51
