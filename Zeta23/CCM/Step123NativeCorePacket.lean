import Zeta23.CCM.NativeExteriorSourceRecord
import Zeta23.CCM.OriginalDetectorPaddedRetainedSelection

/-!
# Same-state native Step 1-3 core packet

A *partial* mathematical packet, not the mandatory all-44-fields output
record.  It preserves one exact original detector, one actual selected
state, its projected forcing and original (generally nonzero) history.
Every view is a projection of this packet, never an independently
selected witness.  The complete M22/M23 producer remains OPEN.
-/

noncomputable section

namespace Zeta23.CCM

open Zeta23.ExceptionalZero

structure Step123NativeCorePacket (σ : ReversalParity) (L : ℝ)
    (Kd : ℕ) (D : ℝ) (hL : 0 < L) where
  state : DetectorRetainedSchurState σ L Kd D hL
  predecessorForcing :
    nativePoleNeutralParitySpace σ L (state.selection.cutoff - 1)
  forcing_eq :
    predecessorForcing =
      originalDetectorNativeForcing σ state.selection state.detector
  nativeHistory :
    OriginalDetectorNativeExteriorHistory σ L Kd state.detector
  history_eq :
    nativeHistory = originalDetectorRetainedExteriorHistory σ state

/-- Nothing can be swapped after state selection: detector, forcing and
history are constructed at the same retained state. -/
def Step123NativeCorePacket.ofState
    (σ : ReversalParity) {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (state : DetectorRetainedSchurState σ L Kd D hL) :
    Step123NativeCorePacket σ L Kd D hL where
  state := state
  predecessorForcing :=
    originalDetectorNativeForcing σ state.selection state.detector
  forcing_eq := rfl
  nativeHistory := originalDetectorRetainedExteriorHistory σ state
  history_eq := rfl

/-- The complete detector Schur-loss lower bound is retained on its
original full complement.  This is a component identity, not an
independent C-Schur upper law. -/
theorem Step123NativeCorePacket.original_negative_schur
    (σ : ReversalParity) {L D : ℝ} {Kd : ℕ} {hL : 0 < L}
    (packet : Step123NativeCorePacket σ L Kd D hL) :
    let y := isometricDetectorComplementCoordinate
      (nativeDetectorPredecessorEmbedding σ packet.state.selection)
        packet.state.detector
    y ≠ 0 ∧
      (inner ℂ (nativeDetectorSchurOperator σ packet.state.inverses y) y).re ≤
        -(D - packet.state.selection.eta) ∧
      (inner ℂ (nativeDetectorSchurOperator σ packet.state.inverses y) y).re <
        -D / 2 :=
  originalDetector_schur_loss_lower packet.state

/-- The one-state packet cofinality theorem uses the existing native
producer *once* for the given phase.  It does not assert that all 44
mandatory fields are present. -/
theorem exists_originalDetectorPaddedPhase_nativeCorePacket
    (σ : ReversalParity) (ρ : zetaZeroConfig.carrier)
    {β : ℝ} (hβ : 0 < β)
    (hβρ : β < |(ρ : ℂ).re - 1 / 2|) (R : ℝ) :
    ∃ d : OriginalDetectorPaddedFinitePhaseData
        β (nativeOriginalDetectorPhaseSign σ) R,
      ∃ packet : Step123NativeCorePacket σ
        (fixedOriginalSincTrialAperture d.separation)
        (originalDetectorQuarticCutoff (fixedOriginalSincTrialAperture d.separation))
        (Real.exp (β * fixedOriginalSincTrialAperture d.separation))
        d.aperture_pos,
        packet.state.detector =
          nativeOriginalDetectorPaddedUnit σ fixedOriginalSincLobeCenter
            d.two_le_aperture ∧
        AdmissibleDetectorSelector β (fixedOriginalSincTrialAperture d.separation)
          packet.state.selection.eta packet.state.selection.cutoff := by
  obtain ⟨d, state, hdet, hadm⟩ :=
    exists_originalDetectorPaddedPhase_admissible_retained_state σ ρ hβ hβρ R
  exact ⟨d, Step123NativeCorePacket.ofState σ state, hdet, hadm⟩

end Zeta23.CCM

#print axioms Zeta23.CCM.Step123NativeCorePacket.original_negative_schur
#print axioms Zeta23.CCM.exists_originalDetectorPaddedPhase_nativeCorePacket
