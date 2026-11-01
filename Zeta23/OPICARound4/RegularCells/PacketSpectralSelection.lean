import Zeta23.OPICARound4.RegularCells.PacketNoncollisionSelection
import Zeta23.OPICARound4.RegularCells.NativeParityPhysicalSeparation

noncomputable section

namespace Zeta23.OPICARound4.NativeParityPencils

open CCM ExceptionalZero OPICARound3 RegularCells

/-- The same genuine exponentially deep generated packet has full physical cross-parity
spectral disjointness at every native cutoff from three through its own detector.
No quantitative separation, eigenvalue lower gap or source-overlap magnitude is asserted. -/
theorem cofinally_actual_packet_joint_regular_disjoint_spectra
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
            ¬ Module.End.HasEigenvalue (nativePoleNeutralParityCanonical .odd L K) μ := by
  obtain ⟨R0,hR0⟩ := cofinally_actual_packet_joint_regular_separationDet ρ hoff
  refine ⟨R0,?_⟩
  intro β hβ hβρ p R hR
  obtain ⟨out,hboth,hjoint,hu,hd,hcap,hreg,hsep⟩ := hR0 β hβ hβρ p R hR
  refine ⟨out,hboth,hjoint,hu,hd,hcap,hreg,?_⟩
  intro K hK hKd
  apply (coordinateFrame_physical_det_iff_disjoint
    out.integrated.boundary.generated.native.aperture_pos _ K rfl).mp
  exact hsep K hK hKd

end Zeta23.OPICARound4.NativeParityPencils
