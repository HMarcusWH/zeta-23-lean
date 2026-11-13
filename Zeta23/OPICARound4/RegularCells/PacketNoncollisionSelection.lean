import Zeta23.OPICARound4.RegularCells.PacketRegularSelection
import Zeta23.OPICARound4.RegularCells.NativeParityRegularSelection

noncomputable section

namespace Zeta23.OPICARound4.NativeParityPencils

open CCM ExceptionalZero OPICARound3 RegularCells

/-- Both exact finite families coexist on a genuine original packet, selected on the
strict open window of its own source depth. The determinant condition is literal. -/
theorem exists_actual_generated_packet_regular_separationDet
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1/2|) (p : ReversalParity) (R : ℝ) :
    ∃ out : GeneratedStep123Output ρ β p R,
      let L := fixedOriginalSincTrialAperture out.sourceData.separation
      let Kd := originalDetectorQuarticCutoff L
      (∀ q K, K ≤ Kd → Function.Bijective (nativePoleNeutralParityCanonical q L K)) ∧
        ∀ K : ℕ, 3 ≤ K → K ≤ Kd →
          nativeActualSeparationDet ⌊Real.exp L⌋₊ K (L : ℂ) ≠ 0 := by
  apply exists_actual_generated_packet_with_open_selection
    (fun L N =>
      (∀ q K, K ≤ N → Function.Bijective (nativePoleNeutralParityCanonical q L K)) ∧
        ∀ K : ℕ, 3 ≤ K → K ≤ N →
          nativeActualSeparationDet ⌊Real.exp L⌋₊ K (L : ℂ) ≠ 0)
    (fun L N K hKN h => ⟨fun q j hj => h.1 q j (hj.trans hKN),
      fun j hj hjK => h.2 j hj (hjK.trans hKN)⟩)
    (fun N J hJo hJn hJ1 =>
      exists_bounded_regular_and_separationDet_in_open_above_one N hJo hJn hJ1)
    ρ hβ hβρ p R

/-- The full boundary/arithmetic/source-spectral packet is built from that SAME output. -/
theorem exists_actual_composed_packet_regular_separationDet
    (ρ : zetaZeroConfig.carrier) {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1/2|) (p : ReversalParity) (R : ℝ) :
    ∃ out : GeneratedStep123ComposedEvidencePacket ρ β p R,
      let L := fixedOriginalSincTrialAperture out.integrated.boundary.generated.sourceData.separation
      let Kd := originalDetectorQuarticCutoff L
      (∀ q K, K ≤ Kd → Function.Bijective (nativePoleNeutralParityCanonical q L K)) ∧
        ∀ K : ℕ, 3 ≤ K → K ≤ Kd →
          nativeActualSeparationDet ⌊Real.exp L⌋₊ K (L : ℂ) ≠ 0 := by
  obtain ⟨g,hg⟩ := exists_actual_generated_packet_regular_separationDet ρ hβ hβρ p R
  exact ⟨GeneratedStep123ComposedEvidencePacket.fromIntegrated
    (GeneratedStep123IntegratedPacket.fromActualBoundary
      (GeneratedStep123BoundaryPacket.fromActualGenerated g)),hg⟩

/-- One cofinal threshold precedes the requested exponent, phase and final packet.
The full source-coupled detector depth, joint grounds, regularity and exact nonzero
separation determinants all refer to that SAME generated aperture and detector. -/
theorem cofinally_actual_packet_joint_regular_separationDet
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
          nativeActualSeparationDet ⌊Real.exp L⌋₊ K (L : ℂ) ≠ 0 := by
  obtain ⟨R0,hR0⟩ := every_late_generated_packet_has_joint_detector_ground ρ hoff
  refine ⟨R0,?_⟩
  intro β hβ hβρ p R hR
  obtain ⟨out,hreg,hsep⟩ := exists_actual_composed_packet_regular_separationDet ρ hβ hβρ p R
  have h := hR0 β p R hR out
  exact ⟨out,h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2,hreg,hsep⟩

end Zeta23.OPICARound4.NativeParityPencils
