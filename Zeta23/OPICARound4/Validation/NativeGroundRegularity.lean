import Zeta23.OPICARound4.TiedNewbornResponse
import Zeta23.OPICARound4.NewbornSpectralVisibility
import Zeta23.OPICARound4.TiedCubicEnergy
import Zeta23.OPICARound4.TiedSilentMoment
import Zeta23.OPICARound4.RegularCells.NativeZeroRegularity
import Zeta23.OPICARound4.RegularCells.NativeRegularBirthSelection

noncomputable section
open Set Complex
open scoped ComplexConjugate

namespace Zeta23.OPICARound4.Validation
open CCM OPICARound3 RegularCells

/-- Complete tied response interval; the actual odd newborn and active source remain explicit. -/
theorem tied_newborn_active_response_consumer
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ) • u)
    (hf : poleNeutralCorrectedCubicSource L K u ≠ 0) :
    0 < (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ∧
      (star (poleNeutralCorrectedCubicSource L K u) *
        centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re ≤
        ‖poleNeutralCorrectedCubicSource L K u‖^2 * ‖poleNeutralCubicCompressionVector L K‖^2 /
          (-poleNeutralEvenRayleighBottom L K hL s.cutoff_lower) :=
  actual_odd_newborn_tied_active_source_moment_bounds s htie u hu hf

/-- Both genuine channels survive away from the own newborn's single negative eigenvalue. -/
theorem newborn_opposite_source_channels_consumer
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL) (lam : ℝ) (hlam : lam < 0)
    (hne : lam ≠ poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u) :
    poleNeutralCorrectedCubicSource L K u ≠ 0 ∧
      poleNeutralCubicPairingFunctional L K
        ((poleNeutralIndexAdjointEquiv hL K s.cutoff_lower).symm u) ≠ 0 :=
  oddNewborn_even_negative_eigen_channels_visible s lam hlam hne u hu0 hu

/-- Exact source normalization, full cubic energy, and the eigenvalue bound by the odd bottom. -/
theorem normalized_cubic_energy_lower_consumer
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)
    (hle : lam ≤ poleNeutralOddRayleighBottom L K hL hK)
    (hf : poleNeutralCorrectedCubicSource L K u = 1) :
    (‖poleNeutralCubicCompressionVector L K‖^2)^2 ≤
      (centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re *
        ((inner ℂ (poleNeutralOddCompressedCanonical L K
          (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re -
          lam * ‖poleNeutralCubicCompressionVector L K‖^2) :=
  actual_normalized_even_moment_cubic_energy_lower hL K hK lam u hu hle hf

/-- Negative actual cubic energy supplies even simplicity without an own-even-newborn premise. -/
theorem negative_cubic_energy_ground_simple_consumer
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .odd L K hL)
    (htie : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower =
      poleNeutralOddRayleighBottom L K hL s.cutoff_lower)
    (hgneg : (inner ℂ (poleNeutralOddCompressedCanonical L K
      (poleNeutralCubicCompressionVector L K)) (poleNeutralCubicCompressionVector L K)).re < 0) :
    Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ)) = 1 :=
  actual_odd_newborn_tied_negative_cubic_energy_even_ground_simple s htie hgneg

/-- Fixed source cell and finite native family are chosen before the common aperture. -/
theorem native_fixed_cell_regular_selection_consumer
    {Q : ℕ} (hQ : 1 ≤ Q) (s : Finset (ReversalParity × ℕ))
    {J : Set ℝ} (hJo : IsOpen J) (hJn : J.Nonempty)
    (hJc : J ⊆ fixedCanonicalCutoffCell Q) :
    ∃ L ∈ J, ∀ i ∈ s, Function.Bijective (nativePoleNeutralParityCanonical i.1 L i.2) :=
  exists_finite_native_regular_in_open_fixedCell hQ s hJo hJn hJc

/-- Cofinal selection keeps each parity's own cutoff and predecessor; it does not identify them. -/
theorem cofinal_native_regular_births_consumer
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1/2) (R : ℝ) :
    ∃ (L : ℝ) (Ke Ko : ℕ), R < L ∧ 2 ≤ L ∧ 3 ≤ Ke ∧ 3 ≤ Ko ∧
      EvenNeutralNegative L Ke ∧ OddNeutralNegative L Ko ∧
      BothNeutralNegative L (max Ke Ko) ∧ max Ke Ko ≤ originalDetectorQuarticCutoff L ∧
      PoleNeutralParityPSD .even L (Ke-1) ∧ PoleNeutralParityPSD .odd L (Ko-1) ∧
      NeutralNewbornSchur .even L Ke ∧ NeutralNewbornSchur .odd L Ko ∧
      Function.Bijective (nativePoleNeutralParityCanonical .even L (Ke-1)) ∧
      Function.Bijective (nativePoleNeutralParityCanonical .odd L (Ko-1)) :=
  cofinally_regular_first_common_births ρ hoff R

/-- Regularity chooses the actual witness's branch and preserves that same vector and energy. -/
theorem same_newborn_regular_realization_consumer
    {p : ReversalParity} {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness p L K hL)
    (hreg : Function.Bijective (nativePoleNeutralParityCanonical p L (K-1))) :
    let J := newbornCutoffInclusion p L K
    let T := nativePoleNeutralParityCanonical p L K
    ∃ hb : J.toLinearMap.adjoint (T s.e.val) ∈ (predecessorBlock J T).range,
      oneShellSchurScalar J T s.e hb < 0 ∧
      s.w = regularSchurWitness J T s.e hb ∧
      (inner ℂ (T s.w) s.w).re = oneShellSchurScalar J T s.e hb :=
  native_newborn_realization_regular_of_bijective s hreg

end Zeta23.OPICARound4.Validation
