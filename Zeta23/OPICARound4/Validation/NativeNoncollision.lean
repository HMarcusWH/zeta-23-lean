import Zeta23.OPICARound4.RegularCells.NativeCompressionSeparation
import Zeta23.OPICARound4.RegularCells.PrimeLaurentNonidentity
import Zeta23.OPICARound4.RegularCells.NativeParityRegularSelection
import Zeta23.OPICARound4.RegularCells.PacketNoncollisionSelection
import Zeta23.OPICARound4.RegularCells.PacketSpectralSelection
import Zeta23.OPICARound4.SeparatedSourceVisibility

noncomputable section

namespace Zeta23.OPICARound4.Validation.NativeNoncollision

open CCM ExceptionalZero OPICARound3 RegularCells NativeParitySeparation NativeParityPencils
open Filter Set
open scoped Topology BigOperators

theorem limiting_full_compressions_check
    (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (x : nativeLimitingEvenCarrier K) (y : nativeLimitingOddCarrier K)
    (hx : x ≠ 0) (hy : y ≠ 0)
    (hxe : nativeSquaredIndexCompression K (nativeLimitingEvenCarrier K) x = (lam : ℂ) • x)
    (hyo : nativeSquaredIndexCompression K (nativeLimitingOddCarrier K) y = (lam : ℂ) • y) :
    False :=
  native_limiting_compressed_squared_index_no_common_eigenvalue K hK lam x y hx hy hxe hyo

theorem grouped_genuine_prime_laurent_check {ι : Type*} [DecidableEq ι]
    (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p)
    (t : Finset ι) (e : ι → s → ℤ) (a : ι → ℂ → ℂ)
    (ha : ∀ i ∈ t, MeromorphicAt (a i) 0)
    (hne : ∃ k ∈ t.image e, ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      groupedPrimeLaurentCoefficient s t e a k z = 0) :
    ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ),
      ∑ i ∈ t, a i z * primeLaurentMonomial s (e i) z = 0 :=
  primeLaurent_sum_germ_nonzero s hs t e a ha hne

theorem actual_full_source_nonidentity_check (Q K : ℕ) (hQ : 2 ≤ Q) (hK : 3 ≤ K) :
    ¬ ∀ᶠ z in 𝓝[≠] (0 : ℂ), nativeActualSeparationDet Q K z = 0 :=
  nativeActualSeparationDet_germ_nonzero Q K hQ hK

theorem bounded_actual_regular_separation_selection_check (N : ℕ)
    {J : Set ℝ} (hJo : IsOpen J) (hJn : J.Nonempty) (hJ1 : J ⊆ Ioi 1) :
    ∃ L ∈ J, (∀ (p : ReversalParity) (K : ℕ), K ≤ N →
      Function.Bijective (nativePoleNeutralParityCanonical p L K)) ∧
      ∀ K : ℕ, 3 ≤ K → K ≤ N → nativeActualSeparationDet ⌊Real.exp L⌋₊ K (L : ℂ) ≠ 0 :=
  exists_bounded_regular_and_separationDet_in_open_above_one N hJo hJn hJ1

theorem genuine_packet_same_detector_check
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1/2) :
    ∃ R0 : ℝ, ∀ (β : ℝ), 0 < β → β < |(ρ : ℂ).re - 1/2| →
      ∀ (p : ReversalParity) (R : ℝ), R0 ≤ R →
      ∃ out : GeneratedStep123ComposedEvidencePacket ρ β p R,
      let g := out.integrated.boundary.generated
      let native := g.native
      let L := fixedOriginalSincTrialAperture g.sourceData.separation
      let Kd := originalDetectorQuarticCutoff L
      let hKd : 3 ≤ Kd := native.retained.state.selection.cutoff_nonempty.trans
        native.retained.state.selection.cutoff_le_detector
      BothNeutralNegative L Kd ∧
        NativeJointGroundConstraints native.aperture_pos Kd hKd ∧
        ‖native.retained.state.detector‖ = 1 ∧
        (inner ℂ (nativePoleNeutralParityCanonical p L Kd native.retained.state.detector)
          native.retained.state.detector).re ≤ -Real.exp (β*L) ∧
        native.retained.state.selection.cutoff ≤ Kd ∧
        (∀ q K, K ≤ Kd → Function.Bijective (nativePoleNeutralParityCanonical q L K)) ∧
        ∀ K : ℕ, 3 ≤ K → K ≤ Kd →
          nativeActualSeparationDet ⌊Real.exp L⌋₊ K (L : ℂ) ≠ 0 :=
  cofinally_actual_packet_joint_regular_separationDet ρ hoff

theorem complete_even_source_and_eigenspace_check {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hsep : ∀ μ : ℂ, Module.End.HasEigenvalue (poleNeutralEvenCompressedCanonical L K) μ →
      ¬ Module.End.HasEigenvalue (poleNeutralOddCompressedCanonical L K) μ)
    (μ : ℂ) (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u = μ • u) :
    poleNeutralCorrectedCubicSource L K u ≠ 0 ∧
      poleNeutralCubicPairingFunctional L K ((poleNeutralIndexAdjointEquiv hL K hK).symm u) ≠ 0 ∧
      Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K) μ) ≤ 1 := by
  have h := separated_native_even_eigen_channels_visible hL K hK hsep μ u hu0 hu
  exact ⟨h.1,h.2,separated_native_even_eigenspace_finrank_le_one hL K hK hsep μ⟩

theorem complete_odd_source_and_eigenspace_check {L : ℝ} (hL : 0 < L)
    (K : ℕ) (hK : 3 ≤ K)
    (hsep : ∀ μ : ℂ, Module.End.HasEigenvalue (poleNeutralEvenCompressedCanonical L K) μ →
      ¬ Module.End.HasEigenvalue (poleNeutralOddCompressedCanonical L K) μ)
    (μ : ℂ) (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w = μ • w) :
    poleNeutralCubicPairingFunctional L K w ≠ 0 ∧
      poleNeutralCorrectedCubicSource L K ((poleNeutralIndexEquiv hL K (by omega)).symm w) ≠ 0 ∧
      Module.finrank ℂ (Module.End.eigenspace (poleNeutralOddCompressedCanonical L K) μ) ≤ 1 := by
  have h := separated_native_odd_eigen_channels_visible hL K hK hsep μ w hw0 hw
  exact ⟨h.1,h.2,separated_native_odd_eigenspace_finrank_le_one hL K hK hsep μ⟩

theorem genuine_packet_same_detector_spectral_check
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1/2) :
    ∃ R0 : ℝ, ∀ (β : ℝ), 0 < β → β < |(ρ : ℂ).re - 1/2| →
      ∀ (p : ReversalParity) (R : ℝ), R0 ≤ R →
      ∃ out : GeneratedStep123ComposedEvidencePacket ρ β p R,
      let g := out.integrated.boundary.generated
      let native := g.native
      let L := fixedOriginalSincTrialAperture g.sourceData.separation
      let Kd := originalDetectorQuarticCutoff L
      let hKd : 3 ≤ Kd := native.retained.state.selection.cutoff_nonempty.trans
        native.retained.state.selection.cutoff_le_detector
      BothNeutralNegative L Kd ∧
        NativeJointGroundConstraints native.aperture_pos Kd hKd ∧
        ‖native.retained.state.detector‖ = 1 ∧
        (inner ℂ (nativePoleNeutralParityCanonical p L Kd native.retained.state.detector)
          native.retained.state.detector).re ≤ -Real.exp (β*L) ∧
        native.retained.state.selection.cutoff ≤ Kd ∧
        (∀ q K, K ≤ Kd → Function.Bijective (nativePoleNeutralParityCanonical q L K)) ∧
        ∀ K : ℕ, 3 ≤ K → K ≤ Kd → ∀ μ : ℂ,
          Module.End.HasEigenvalue (nativePoleNeutralParityCanonical .even L K) μ →
            ¬ Module.End.HasEigenvalue (nativePoleNeutralParityCanonical .odd L K) μ :=
  cofinally_actual_packet_joint_regular_disjoint_spectra ρ hoff

end Zeta23.OPICARound4.Validation.NativeNoncollision
