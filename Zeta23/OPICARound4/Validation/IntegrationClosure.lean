import Zeta23.OPICARound4.NativeJointIndex
import Zeta23.OPICARound4.NeutralContactPencil

noncomputable section

namespace Zeta23.OPICARound4.Validation

open CCM OPICARound3 OPICAComposition RegularCells Set
open scoped BigOperators

/-- Independent expected-type consumer for all three source-specific leaves. -/
theorem actual_ray_closure_consumer
    (he : ∀ (L : ℝ) (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ),
      lam < 0 → ∀ hs : lam < poleNeutralOddRayleighBottom L K hL hK,
        (poleNeutralCorrectedCubicSource L K
          (poleNeutralEvenShiftedRay hL K hK lam hs)).re < 1)
    (ho : ∀ (L : ℝ) (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ),
      lam < 0 → ∀ hs : lam < poleNeutralEvenRayleighBottom L K hL hK,
        (poleNeutralCubicPairingFunctional L K
          (poleNeutralOddAdjointShiftedRay hL K hK lam hs)).re < 1)
    (ht : ¬ ∃ (L : ℝ) (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K),
      poleNeutralEvenRayleighBottom L K hL hK = poleNeutralOddRayleighBottom L K hL hK ∧
        poleNeutralEvenRayleighBottom L K hL hK < 0)
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) :
    ¬ BothNeutralNegative L K :=
  noBothNeg_of_research_targets he ho ht hL K hK

/-- D02's real threshold is independent of both the aperture and cutoff. -/
theorem eventual_noBothNeg_no_off_line_consumer
    (h : ∃ R : ℝ, ∀ L : ℝ, R < L → ∀ K : ℕ, 3 ≤ K → ¬ BothNeutralNegative L K) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 :=
  no_off_line_zero_of_eventual_noBothNeg h

theorem eventual_actual_ray_no_off_line_consumer
    (h : ∃ R : ℝ, ∀ (L : ℝ), R < L → ∀ (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K),
      (∀ lam : ℝ, lam < 0 → ∀ hs : lam < poleNeutralOddRayleighBottom L K hL hK,
        (poleNeutralCorrectedCubicSource L K
          (poleNeutralEvenShiftedRay hL K hK lam hs)).re < 1) ∧
      (∀ lam : ℝ, lam < 0 → ∀ hs : lam < poleNeutralEvenRayleighBottom L K hL hK,
        (poleNeutralCubicPairingFunctional L K
          (poleNeutralOddAdjointShiftedRay hL K hK lam hs)).re < 1) ∧
      ¬ (poleNeutralEvenRayleighBottom L K hL hK =
        poleNeutralOddRayleighBottom L K hL hK ∧ poleNeutralEvenRayleighBottom L K hL hK < 0)) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 :=
  no_off_line_zero_of_eventual_actual_ray_closure h

/-- The index cap is on the joint physical neutral carrier and every strictly
negative subspace; separate parity caps are not substituted for it. -/
theorem eventual_joint_index_no_off_line_consumer
    (h : ∃ R : ℝ, ∀ L : ℝ, R < L → ∀ K : ℕ, 3 ≤ K →
      ∀ S : Submodule ℂ (EuclideanSpace ℂ (Fin (2 * K + 1))),
        (∀ w ∈ S, w ∈ euclideanBoundaryFlatSubspace K ∧
          canonicalPoleExponentialMoment 1 L K ((EuclideanSpace.equiv _ ℂ) w) = 0 ∧
          canonicalPoleExponentialMoment (-1) L K ((EuclideanSpace.equiv _ ℂ) w) = 0) →
        (∀ w ∈ S, w ≠ 0 → fullCanonicalEnergy L K w < 0) →
          Module.finrank ℂ S ≤ 1) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 :=
  no_off_line_zero_of_eventual_native_joint_index h

/-- These separate restrictions test only the actual negative lower grounds.
They do not redefine either original all-ray research proposition. -/
theorem actual_ground_closure_consumer
    (he : EvenNegativeGroundRestriction) (ho : OddNegativeGroundRestriction)
    (ht : SharedGroundExclusion) {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) :
    ¬ BothNeutralNegative L K :=
  noBothNeg_of_ground_restrictions he ho ht hL K hK

theorem eventual_ground_no_off_line_consumer (h : EventualNegativeGroundClosure) :
    ∀ ρ : zetaZeroConfig.carrier, (ρ : ℂ).re = 1 / 2 :=
  no_off_line_zero_of_eventual_ground_closure h

/-- Explicit all-cutoff equivalences into the actual native carriers. -/
theorem fixed_seed_native_equivalences_consumer {L : ℝ} (hL : 0 < L) (K : ℕ) :
    Nonempty (fixedEvenSeed K ≃ₗ[ℂ] poleNeutralEvenSubspace L K) ∧
      Nonempty (fixedOddSeed K ≃ₗ[ℂ] poleNeutralOddSubspace L K) :=
  ⟨⟨fixedEvenSeedPhysicalEquiv hL K⟩, ⟨fixedOddSeedPhysicalEquiv hL K⟩⟩

theorem fixed_even_seed_raw_moments_consumer {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    (fixedSeedDiagonal L K u ∈ evenBoundaryFlatSubspace K ∧
      (∑ i, poleEvenProfile L K i * fixedSeedDiagonal L K u i) = 0) ↔
        u ∈ evenCoefficientSubspace K ∧ centeredMoment K 0 u = 0 ∧
          centeredMoment K 2 u = 0 ∧ centeredMoment K 4 u = 0 :=
  (fixedEvenSeed_diagonal_iff hL K u).trans (mem_fixedEvenSeed_iff K u)

theorem fixed_odd_seed_raw_moments_consumer {L : ℝ} (hL : 0 < L) (K : ℕ)
    (u : Fin (2 * K + 1) → ℂ) :
    (fixedSeedDiagonal L K u ∈ oddBoundaryFlatSubspace K ∧
      (∑ i, poleOddProfile L K i * fixedSeedDiagonal L K u i) = 0) ↔
        u ∈ oddCoefficientSubspace K ∧ centeredMoment K 1 u = 0 ∧
          centeredMoment K 3 u = 0 :=
  (fixedOddSeed_diagonal_iff hL K u).trans (mem_fixedOddSeed_iff K u)

theorem fixed_seed_metric_consumer {L : ℝ} (hL : 0 < L) (K : ℕ)
    (ue ve : fixedEvenSeed K) (uo vo : fixedOddSeed K) :
    inner ℂ (fixedEvenSeedPhysicalEquiv hL K ue) (fixedEvenSeedPhysicalEquiv hL K ve) =
      (∑ i, (fixedSeedDiagonalEntry L K i : ℂ) ^ 2 * star (ue.val i) * ve.val i) ∧
    inner ℂ (fixedOddSeedPhysicalEquiv hL K uo) (fixedOddSeedPhysicalEquiv hL K vo) =
      (∑ i, (fixedSeedDiagonalEntry L K i : ℂ) ^ 2 * star (uo.val i) * vo.val i) :=
  ⟨fixedEvenSeedPhysicalEquiv_gram hL K ue ve, fixedOddSeedPhysicalEquiv_gram hL K uo vo⟩

theorem fixed_seed_physical_poles_consumer {L : ℝ} (hL : 0 < L) (K : ℕ)
    (ue : fixedEvenSeed K) (uo : fixedOddSeed K) :
    (canonicalPoleExponentialMoment 1 L K (fixedSeedDiagonal L K ue) = 0 ∧
      canonicalPoleExponentialMoment (-1) L K (fixedSeedDiagonal L K ue) = 0) ∧
    (canonicalPoleExponentialMoment 1 L K (fixedSeedDiagonal L K uo) = 0 ∧
      canonicalPoleExponentialMoment (-1) L K (fixedSeedDiagonal L K uo) = 0) :=
  ⟨fixedEvenSeedPhysicalEquiv_exponentialMoments hL K ue,
    fixedOddSeedPhysicalEquiv_exponentialMoments hL K uo⟩

theorem native_fixed_seed_contact_consumer {κ : Type*}
    (K : ℕ) (U : Fin (2 * K + 1) → κ → ℂ)
    (A' : Fin (2 * K + 1) → Fin (2 * K + 1) → ℂ) (t lam : ℝ)
    (hA : ∀ m n, HasDerivAt (fun s => canonicalSourceMatrix s K m n) (A' m n) t)
    (i j : κ) :
    HasDerivAt (fun s => frameEnergyEntry (fun s => canonicalSourceMatrix s K)
      (fixedSeedFrame K U) s i j - (lam : ℂ) * frameGramEntry (fixedSeedFrame K U) s i j)
      (frameEnergyDerivative (canonicalSourceMatrix t K) A' (fixedSeedFrame K U t)
        (fixedSeedFrameDerivative K U t) i j - (lam : ℂ) *
          frameGramDerivative (fixedSeedFrame K U t) (fixedSeedFrameDerivative K U t) i j) t :=
  native_fixedSeed_contact_pencil_hasDerivAt K U A' t lam hA i j

end Zeta23.OPICARound4.Validation

#print axioms Zeta23.OPICARound4.noBothNeg_of_actual_ray_comparisons
#print axioms Zeta23.OPICARound4.noBothNeg_of_research_targets
#print axioms Zeta23.OPICARound4.eventual_actual_ray_closure_of_three_thresholds
#print axioms Zeta23.OPICARound4.no_off_line_zero_of_eventual_actual_ray_closure
#print axioms Zeta23.OPICARound4.frame_strictly_negative_native_plane
#print axioms Zeta23.OPICARound4.no_off_line_zero_of_eventual_native_joint_index
#print axioms Zeta23.OPICARound4.native_odd_visible_or_invisible_competitor
#print axioms Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv
#print axioms Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv
#print axioms Zeta23.OPICARound4.RegularCells.fixedSeedGram_pos
#print axioms Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_gram
#print axioms Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_gram
#print axioms Zeta23.OPICARound4.RegularCells.fixedEvenSeedPhysicalEquiv_exponentialMoments
#print axioms Zeta23.OPICARound4.RegularCells.fixedOddSeedPhysicalEquiv_exponentialMoments
#print axioms Zeta23.OPICARound4.neutral_contact_pencil_hasDerivAt
#print axioms Zeta23.OPICARound4.moving_neutral_contact_pencil_hasDerivAt
#print axioms Zeta23.OPICARound4.native_fixedSeed_contact_pencil_hasDerivAt
#print axioms Zeta23.OPICARound4.Validation.actual_ray_closure_consumer
#print axioms Zeta23.OPICARound4.Validation.eventual_noBothNeg_no_off_line_consumer
#print axioms Zeta23.OPICARound4.Validation.eventual_actual_ray_no_off_line_consumer
#print axioms Zeta23.OPICARound4.Validation.eventual_joint_index_no_off_line_consumer
#print axioms Zeta23.OPICARound4.Validation.actual_ground_closure_consumer
#print axioms Zeta23.OPICARound4.Validation.eventual_ground_no_off_line_consumer
#print axioms Zeta23.OPICARound4.Validation.fixed_seed_native_equivalences_consumer
#print axioms Zeta23.OPICARound4.Validation.fixed_even_seed_raw_moments_consumer
#print axioms Zeta23.OPICARound4.Validation.fixed_odd_seed_raw_moments_consumer
#print axioms Zeta23.OPICARound4.Validation.fixed_seed_metric_consumer
#print axioms Zeta23.OPICARound4.Validation.fixed_seed_physical_poles_consumer
#print axioms Zeta23.OPICARound4.Validation.native_fixed_seed_contact_consumer
