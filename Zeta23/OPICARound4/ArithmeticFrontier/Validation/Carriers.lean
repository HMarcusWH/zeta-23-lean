import Zeta23.OPICARound4.ArithmeticFrontier.CofinalMomentClosure
import Zeta23.OPICARound4.ArithmeticFrontier.MomentSliceCoordinates
import Zeta23.OPICARound4.ArithmeticFrontier.SelectedPacketClosure
import Zeta23.OPICARound4.ArithmeticFrontier.PhysicalBlockCertificate
import Zeta23.OPICARound4.ArithmeticFrontier.SourceColumnCore

/-!
# Independent complete-type consumers for the arithmetic-frontier carriers

Each consumer restates its statement with every definition expanded to the
literal native objects: compressed canonical energies, physical centered
moments, the inherited Euclidean norm, the literal quartic cutoff and the full
seed Gram. They check that the defined contracts mean what they say. The
arithmetic premises remain explicit hypotheses and remain OPEN.
-/

noncomputable section

namespace Zeta23.OPICARound4.ArithmeticFrontier.Validation

open CCM ExceptionalZero OPICARound3 RegularCells Module Filter
open scoped BigOperators ComplexConjugate

/-- (C1), fully expanded, is a sufficient condition for Mathlib's RH. -/
theorem cofinal_moment_closure_consumer
    (h : ∀ n : ℕ, 1 ≤ n → ∃ L : ℝ, (n : ℝ) + 2 ≤ L ∧
      ((∀ u : poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L),
          centeredMoment (originalDetectorQuarticCutoff L) 4
            ((EuclideanSpace.equiv _ ℂ) u.val.val) = 0 →
          -(1 / (n : ℝ)) * ‖u‖ ^ 2 ≤
            (inner ℂ (poleNeutralEvenCompressedCanonical L (originalDetectorQuarticCutoff L) u) u).re) ∨
       (∀ v : poleNeutralOddSubspace L (originalDetectorQuarticCutoff L),
          centeredMoment (originalDetectorQuarticCutoff L) 3
              ((EuclideanSpace.equiv _ ℂ) v.val.val) = 0 ∧
            centeredMoment (originalDetectorQuarticCutoff L) 5
              ((EuclideanSpace.equiv _ ℂ) v.val.val) = 0 →
          -(1 / (n : ℝ)) * ‖v‖ ^ 2 ≤
            (inner ℂ (poleNeutralOddCompressedCanonical L (originalDetectorQuarticCutoff L) v) v).re))) :
    RiemannHypothesis :=
  riemannHypothesis_of_cofinal_moment_slice_bounds h

/-- The opposing witnesses are the literal moment-zero trials at the literal cutoff. -/
theorem moment_slice_witness_consumer (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) :
    ∃ d : ℝ, 0 < d ∧ ∀ᶠ L : ℝ in atTop, 2 ≤ L ∧
      (∃ u : poleNeutralEvenSubspace L (originalDetectorQuarticCutoff L), u ≠ 0 ∧
        centeredMoment (originalDetectorQuarticCutoff L) 4 ((EuclideanSpace.equiv _ ℂ) u.val.val) = 0 ∧
        (inner ℂ (poleNeutralEvenCompressedCanonical L (originalDetectorQuarticCutoff L) u) u).re <
          -d * ‖u‖ ^ 2) ∧
      (∃ v : poleNeutralOddSubspace L (originalDetectorQuarticCutoff L), v ≠ 0 ∧
        (centeredMoment (originalDetectorQuarticCutoff L) 3 ((EuclideanSpace.equiv _ ℂ) v.val.val) = 0 ∧
          centeredMoment (originalDetectorQuarticCutoff L) 5 ((EuclideanSpace.equiv _ ℂ) v.val.val) = 0) ∧
        (inner ℂ (poleNeutralOddCompressedCanonical L (originalDetectorQuarticCutoff L) v) v).re <
          -d * ‖v‖ ^ 2) :=
  eventually_both_moment_slice_witnesses ρ hoff

/-- Exact slice dimensions at the literal quartic cutoff; both are nonzero. -/
theorem quartic_slice_dimension_consumer {L : ℝ} (hL : 2 ≤ L) :
    finrank ℂ (LinearMap.ker (evenPhysicalMoment L (originalDetectorQuarticCutoff L) 4)) =
        originalDetectorQuarticCutoff L - 3 ∧
      finrank ℂ ↥(LinearMap.ker (oddPhysicalMoment L (originalDetectorQuarticCutoff L) 3) ⊓
          LinearMap.ker (oddPhysicalMoment L (originalDetectorQuarticCutoff L) 5) :
            Submodule ℂ (poleNeutralOddSubspace L (originalDetectorQuarticCutoff L))) =
        originalDetectorQuarticCutoff L - 4 ∧
      13 ≤ originalDetectorQuarticCutoff L - 3 := by
  have hK := originalDetectorQuarticCutoff_ge_sixteen hL
  refine ⟨finrank_evenMomentSlice (by linarith) _ (by omega),
    finrank_oddMomentSlice (by linarith) _ (by omega), by omega⟩

/-- Physical congruence transport retains the full nonunitary Gram. -/
theorem seed_gram_transport_consumer {L : ℝ} (hL : 0 < L) (K : ℕ) (ε : ℝ) :
    EvenMomentSliceLowerBound L K ε ↔ ∀ y : fixedEvenMomentSeed K,
      -ε * (∑ i, (fixedSeedDiagonalEntry L K i : ℂ) ^ 2 * star ((y : Fin (2 * K + 1) → ℂ) i) *
          (y : Fin (2 * K + 1) → ℂ) i).re ≤
        (inner ℂ (poleNeutralEvenCompressedCanonical L K
            ((evenMomentSliceSeedEquiv hL K y : evenMomentSlice L K) : poleNeutralEvenSubspace L K))
          ((evenMomentSliceSeedEquiv hL K y : evenMomentSlice L K) : poleNeutralEvenSubspace L K)).re :=
  evenMomentSliceLowerBound_iff_seed_gram hL K ε

/-- The narrow packet route needs only the two exact ground tests at late
disjoint quartic states; no global shared-ground exclusion is assumed. -/
theorem disjoint_quartic_ground_consumer
    (h : ∃ R : ℝ, ∀ L : ℝ, R < L → ∀ (hL : 0 < L) (hK : 3 ≤ originalDetectorQuarticCutoff L),
      (∀ μ : ℂ, Module.End.HasEigenvalue
          (nativePoleNeutralParityCanonical .even L (originalDetectorQuarticCutoff L)) μ →
        ¬ Module.End.HasEigenvalue
          (nativePoleNeutralParityCanonical .odd L (originalDetectorQuarticCutoff L)) μ) →
      (poleNeutralEvenRayleighBottom L _ hL hK < 0 →
          ∀ hs : poleNeutralEvenRayleighBottom L _ hL hK < poleNeutralOddRayleighBottom L _ hL hK,
            (poleNeutralCorrectedCubicSource L _
              (poleNeutralEvenShiftedRay hL _ hK (poleNeutralEvenRayleighBottom L _ hL hK) hs)).re < 1) ∧
      (poleNeutralOddRayleighBottom L _ hL hK < 0 →
          ∀ hs : poleNeutralOddRayleighBottom L _ hL hK < poleNeutralEvenRayleighBottom L _ hL hK,
            (poleNeutralCubicPairingFunctional L _
              (poleNeutralOddAdjointShiftedRay hL _ hK (poleNeutralOddRayleighBottom L _ hL hK) hs)).re < 1)) :
    RiemannHypothesis :=
  riemannHypothesis_of_eventual_disjoint_quartic_ground_restriction h

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The complete inverse-residual certificate, with the coupling expanded. -/
theorem inverse_residual_certificate_consumer
    (D : E →ₗ[ℂ] E) (C : F →ₗ[ℂ] E) (Cadj : E →ₗ[ℂ] F) (A : F →ₗ[ℂ] F) (X : E →ₗ[ℂ] F)
    {a : ℝ} (ha : 0 < a)
    (hA : ∀ z z' : F, inner ℂ (A z) z' = inner ℂ z (A z'))
    (hApos : ∀ z : F, a * ‖z‖ ^ 2 ≤ (inner ℂ (A z) z).re)
    (hC : ∀ (u : E) (w : F), inner ℂ (C w) u = inner ℂ w (Cadj u))
    (hcert : ∀ u : E, a⁻¹ * ‖Cadj u - A (X u)‖ ^ 2 ≤
      (inner ℂ (D u) u).re - 2 * (inner ℂ (C (X u)) u).re + (inner ℂ (A (X u)) (X u)).re)
    (u : E) (w : F) :
    0 ≤ (inner ℂ (D u) u).re + 2 * (inner ℂ (C w) u).re + (inner ℂ (A w) w).re :=
  blockEnergy_nonneg_of_inverse_residual_certificate D C Cadj A X ha hA hApos hC hcert u w

/-- The source-core consumer, with the complete-complement leakage expanded. -/
theorem core_shift_consumer (H : E →ₗ[ℂ] E) (S : Submodule ℂ E) [S.HasOrthogonalProjection]
    (hH : ∀ x y : E, inner ℂ (H x) y = inner ℂ x (H y)) {ε η : ℝ}
    (hη : 0 ≤ η) (hηε : η ≤ ε / 4)
    (hleak : ∀ (x q : E), q ∈ Sᗮ → ‖inner ℂ (H x) q‖ ≤ η * ‖x‖ * ‖q‖)
    (hcore : ∀ p ∈ S, -(11 * ε / 12) * ‖p‖ ^ 2 ≤ (inner ℂ (H p) p).re) (v : E) :
    -ε * ‖v‖ ^ 2 ≤ (inner ℂ (H v) v).re :=
  core_shift_certificate H S hH hη hηε hleak hcore v

end Zeta23.OPICARound4.ArithmeticFrontier.Validation
