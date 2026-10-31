import Zeta23.OPICARound4.NativeWitnessCosts
import Zeta23.RHRC.OpicaComposition.ResearchTargets

noncomputable section

namespace Zeta23.OPICARound4

open CCM OPICARound3 OPICAComposition

/-- Pointwise closure uses both actual resolvent rays and separately excludes
the negative shared ground. Each hypothesis is independent, and remains OPEN
for the actual arithmetic family. -/
theorem noBothNeg_of_actual_ray_comparisons {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (he : ∀ lam : ℝ, lam < 0 →
      ∀ hs : lam < poleNeutralOddRayleighBottom L K hL hK,
        (poleNeutralCorrectedCubicSource L K
          (poleNeutralEvenShiftedRay hL K hK lam hs)).re < 1)
    (ho : ∀ lam : ℝ, lam < 0 →
      ∀ hs : lam < poleNeutralEvenRayleighBottom L K hL hK,
        (poleNeutralCubicPairingFunctional L K
          (poleNeutralOddAdjointShiftedRay hL K hK lam hs)).re < 1)
    (hshared : ¬ (poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK ∧
        poleNeutralEvenRayleighBottom L K hL hK < 0)) :
    ¬ BothNeutralNegative L K := by
  intro hboth
  rcases common_cutoff_negative_ground_alternatives hL K hK hboth with
    ⟨_, hn, hs, hsource⟩ | ⟨_, hn, hs, hsource⟩ | htie
  · have h := he _ hn hs
    rw [hsource] at h
    norm_num at h
  · have h := ho _ hn hs
    rw [hsource] at h
    norm_num at h
  · exact hshared htie

/-- The existing research propositions suffice conditionally. In particular,
neither strict opposite-floor comparison silently covers a shared eigenvalue. -/
theorem noBothNeg_of_research_targets (he : EvenRayComparison)
    (ho : OddAdjointRayComparison) (hshared : SharedGroundExclusion)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) :
    ¬ BothNeutralNegative L K := by
  apply noBothNeg_of_actual_ray_comparisons hL K hK (he L hL K hK) (ho L hL K hK)
  exact fun h => hshared ⟨L, hL, K, hK, h⟩

/-- A common aperture threshold must precede every cutoff and every admissible
negative shift. It cannot be chosen after the resolvent state. -/
def EventualActualRayClosure : Prop :=
  ∃ R : ℝ, ∀ (L : ℝ), R < L → ∀ (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K),
    (∀ lam : ℝ, lam < 0 → ∀ hs : lam < poleNeutralOddRayleighBottom L K hL hK,
      (poleNeutralCorrectedCubicSource L K
        (poleNeutralEvenShiftedRay hL K hK lam hs)).re < 1) ∧
    (∀ lam : ℝ, lam < 0 → ∀ hs : lam < poleNeutralEvenRayleighBottom L K hL hK,
      (poleNeutralCubicPairingFunctional L K
        (poleNeutralOddAdjointShiftedRay hL K hK lam hs)).re < 1) ∧
    ¬ (poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK ∧
        poleNeutralEvenRayleighBottom L K hL hK < 0)

theorem eventual_noBothNeg_of_actual_ray_closure (h : EventualActualRayClosure) :
    EventualNoSimultaneousNegativity := by
  obtain ⟨R, hR⟩ := h
  refine ⟨max R 0, ?_⟩
  intro L hL K hK
  have hp : 0 < L := lt_of_le_of_lt (le_max_right R 0) hL
  obtain ⟨he, ho, ht⟩ := hR L (lt_of_le_of_lt (le_max_left R 0) hL) hp K hK
  exact noBothNeg_of_actual_ray_comparisons hp K hK he ho ht

/-- Independent thresholds may be combined, but all three are uniform in K
and the real negative shift before the common maximum is taken. -/
theorem eventual_actual_ray_closure_of_three_thresholds
    (he : ∃ R : ℝ, ∀ (L : ℝ), R < L → ∀ (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
      (lam : ℝ), lam < 0 → ∀ hs : lam < poleNeutralOddRayleighBottom L K hL hK,
        (poleNeutralCorrectedCubicSource L K
          (poleNeutralEvenShiftedRay hL K hK lam hs)).re < 1)
    (ho : ∃ R : ℝ, ∀ (L : ℝ), R < L → ∀ (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
      (lam : ℝ), lam < 0 → ∀ hs : lam < poleNeutralEvenRayleighBottom L K hL hK,
        (poleNeutralCubicPairingFunctional L K
          (poleNeutralOddAdjointShiftedRay hL K hK lam hs)).re < 1)
    (ht : ∃ R : ℝ, ∀ (L : ℝ), R < L → ∀ (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K),
      ¬ (poleNeutralEvenRayleighBottom L K hL hK =
        poleNeutralOddRayleighBottom L K hL hK ∧
          poleNeutralEvenRayleighBottom L K hL hK < 0)) :
    EventualActualRayClosure := by
  obtain ⟨Re, he⟩ := he
  obtain ⟨Ro, ho⟩ := ho
  obtain ⟨Rt, ht⟩ := ht
  refine ⟨max Re (max Ro Rt), ?_⟩
  intro L hL hp K hK
  have heL : Re < L := lt_of_le_of_lt (le_max_left _ _) hL
  have hoL : Ro < L := lt_of_le_of_lt ((le_max_left Ro Rt).trans (le_max_right _ _)) hL
  have htL : Rt < L := lt_of_le_of_lt ((le_max_right Ro Rt).trans (le_max_right _ _)) hL
  exact ⟨he L heL hp K hK, ho L hoL hp K hK, ht L htL hp K hK⟩

/-- D02 supplies the contradiction at the same real aperture and common cutoff.
This is a conditional consumer, not a proof of any of its OPEN hypotheses. -/
theorem no_off_line_zero_of_eventual_noBothNeg
    (h : EventualNoSimultaneousNegativity) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 := by
  intro ρ
  by_contra hoff
  obtain ⟨R, hR⟩ := h
  obtain ⟨L, hRL, _, K, hK, hboth⟩ :=
    cofinally_both_neutral_negative_of_off_line_zero ρ hoff R
  exact hR L hRL K hK hboth

theorem no_off_line_zero_of_eventual_actual_ray_closure
    (h : EventualActualRayClosure) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 :=
  no_off_line_zero_of_eventual_noBothNeg (eventual_noBothNeg_of_actual_ray_closure h)

/-- The weaker even obligation tests only the actual negative even bottom
when it lies strictly below the actual odd bottom. It is not an all-ray claim. -/
def EvenNegativeGroundRestriction : Prop :=
  ∀ (L : ℝ) (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K),
    poleNeutralEvenRayleighBottom L K hL hK < 0 →
    ∀ hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK,
      (poleNeutralCorrectedCubicSource L K
        (poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs)).re < 1

/-- The odd ground obligation retains the actual adjoint ray and its source
pairing, at exactly the negative odd bottom. -/
def OddNegativeGroundRestriction : Prop :=
  ∀ (L : ℝ) (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K),
    poleNeutralOddRayleighBottom L K hL hK < 0 →
    ∀ hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK,
      (poleNeutralCubicPairingFunctional L K
        (poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs)).re < 1

theorem even_negative_ground_restriction_of_all_ray (h : EvenRayComparison) :
    EvenNegativeGroundRestriction := by
  intro L hL K hK hn hs
  exact h L hL K hK _ hn hs

theorem odd_negative_ground_restriction_of_all_ray (h : OddAdjointRayComparison) :
    OddNegativeGroundRestriction := by
  intro L hL K hK hn hs
  exact h L hL K hK _ hn hs

/-- Pointwise no-both-negativity needs only the two exact ground tests and
the separately stated shared negative ground exclusion. -/
theorem noBothNeg_of_actual_ground_comparisons {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (he : poleNeutralEvenRayleighBottom L K hL hK < 0 →
      ∀ hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK,
        (poleNeutralCorrectedCubicSource L K
          (poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs)).re < 1)
    (ho : poleNeutralOddRayleighBottom L K hL hK < 0 →
      ∀ hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK,
        (poleNeutralCubicPairingFunctional L K
          (poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs)).re < 1)
    (hshared : ¬ (poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK ∧ poleNeutralEvenRayleighBottom L K hL hK < 0)) :
    ¬ BothNeutralNegative L K := by
  intro hboth
  rcases common_cutoff_negative_ground_alternatives hL K hK hboth with
    ⟨_, hn, hs, hsource⟩ | ⟨_, hn, hs, hsource⟩ | htie
  · have h := he hn hs
    rw [hsource] at h
    norm_num at h
  · have h := ho hn hs
    rw [hsource] at h
    norm_num at h
  · exact hshared htie

theorem noBothNeg_of_ground_restrictions (he : EvenNegativeGroundRestriction)
    (ho : OddNegativeGroundRestriction) (ht : SharedGroundExclusion)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) : ¬ BothNeutralNegative L K :=
  noBothNeg_of_actual_ground_comparisons hL K hK (he L hL K hK) (ho L hL K hK)
    (fun h => ht ⟨L, hL, K, hK, h⟩)

/-- A common threshold is selected before the real aperture and cutoff.
Only the actual negative ground of each parity is tested. -/
def EventualNegativeGroundClosure : Prop :=
  ∃ R : ℝ, ∀ L : ℝ, R < L → ∀ (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K),
    (poleNeutralEvenRayleighBottom L K hL hK < 0 →
      ∀ hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK,
        (poleNeutralCorrectedCubicSource L K
          (poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs)).re < 1) ∧
    (poleNeutralOddRayleighBottom L K hL hK < 0 →
      ∀ hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK,
        (poleNeutralCubicPairingFunctional L K
          (poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs)).re < 1) ∧
    ¬ (poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK ∧ poleNeutralEvenRayleighBottom L K hL hK < 0)

theorem eventual_noBothNeg_of_ground_closure (h : EventualNegativeGroundClosure) :
    EventualNoSimultaneousNegativity := by
  obtain ⟨R, hR⟩ := h
  refine ⟨max R 0, ?_⟩
  intro L hL K hK
  have hp : 0 < L := lt_of_le_of_lt (le_max_right R 0) hL
  obtain ⟨he, ho, ht⟩ := hR L (lt_of_le_of_lt (le_max_left R 0) hL) hp K hK
  exact noBothNeg_of_actual_ground_comparisons hp K hK he ho ht

theorem eventual_ground_closure_of_three_thresholds
    (he : ∃ R : ℝ, ∀ L : ℝ, R < L → ∀ (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K),
      poleNeutralEvenRayleighBottom L K hL hK < 0 →
      ∀ hs : poleNeutralEvenRayleighBottom L K hL hK < poleNeutralOddRayleighBottom L K hL hK,
        (poleNeutralCorrectedCubicSource L K
          (poleNeutralEvenShiftedRay hL K hK (poleNeutralEvenRayleighBottom L K hL hK) hs)).re < 1)
    (ho : ∃ R : ℝ, ∀ L : ℝ, R < L → ∀ (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K),
      poleNeutralOddRayleighBottom L K hL hK < 0 →
      ∀ hs : poleNeutralOddRayleighBottom L K hL hK < poleNeutralEvenRayleighBottom L K hL hK,
        (poleNeutralCubicPairingFunctional L K
          (poleNeutralOddAdjointShiftedRay hL K hK (poleNeutralOddRayleighBottom L K hL hK) hs)).re < 1)
    (ht : ∃ R : ℝ, ∀ L : ℝ, R < L → ∀ (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K),
      ¬ (poleNeutralEvenRayleighBottom L K hL hK = poleNeutralOddRayleighBottom L K hL hK ∧
        poleNeutralEvenRayleighBottom L K hL hK < 0)) : EventualNegativeGroundClosure := by
  obtain ⟨Re, he⟩ := he
  obtain ⟨Ro, ho⟩ := ho
  obtain ⟨Rt, ht⟩ := ht
  refine ⟨max Re (max Ro Rt), ?_⟩
  intro L hL hp K hK
  have heL : Re < L := lt_of_le_of_lt (le_max_left _ _) hL
  have hoL : Ro < L := lt_of_le_of_lt ((le_max_left Ro Rt).trans (le_max_right _ _)) hL
  have htL : Rt < L := lt_of_le_of_lt ((le_max_right Ro Rt).trans (le_max_right _ _)) hL
  exact ⟨he L heL hp K hK, ho L hoL hp K hK, ht L htL hp K hK⟩

theorem no_off_line_zero_of_eventual_ground_closure (h : EventualNegativeGroundClosure) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 :=
  no_off_line_zero_of_eventual_noBothNeg (eventual_noBothNeg_of_ground_closure h)

end Zeta23.OPICARound4
