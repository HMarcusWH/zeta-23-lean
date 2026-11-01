import Zeta23.OPICARound4.CommonQuarticGround
import Zeta23.OPICARound4.JointGroundBirth

noncomputable section
open Set Complex Filter
open scoped Topology ComplexConjugate
namespace Zeta23.OPICARound4.Validation
open CCM ExceptionalZero OPICARound3

/-- The aperture threshold is selected once, before every larger aperture. -/
theorem common_quartic_uniform_threshold_consumer (ρ : zetaZeroConfig.carrier)
    (hoff : (ρ : ℂ).re ≠ 1/2) :
    ∃ R0 : ℝ, ∀ L : ℝ, R0 ≤ L → 2 ≤ L ∧
      BothNeutralNegative L (originalDetectorQuarticCutoff L) :=
  eventually_atTop.mp (eventually_both_negative_at_original_quartic ρ hoff)

/-- Same actual packet, exact detector cutoff, with selected cutoff separate. -/
theorem generated_packet_joint_consumer
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1/2) :
    ∃ R0 : ℝ, ∀ (β : ℝ) (p : ReversalParity) (R : ℝ), R0 ≤ R →
      ∀ out : GeneratedStep123ComposedEvidencePacket ρ β p R,
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
        native.retained.state.selection.cutoff ≤ Kd :=
  every_late_generated_packet_has_joint_detector_ground ρ hoff

/-- First cutoffs retain their own predecessors; only an upper cutoff bound. -/
theorem first_common_quartic_bound_consumer {L : ℝ} (hL : 2 ≤ L)
    (hb : BothNeutralNegative L (originalDetectorQuarticCutoff L)) :
    ∃ Ke Ko : ℕ, 3 ≤ Ke ∧ 3 ≤ Ko ∧
      EvenNeutralNegative L Ke ∧ OddNeutralNegative L Ko ∧
      BothNeutralNegative L (max Ke Ko) ∧ max Ke Ko ≤ originalDetectorQuarticCutoff L ∧
      PoleNeutralParityPSD .even L (Ke-1) ∧ PoleNeutralParityPSD .odd L (Ko-1) ∧
      NeutralNewbornSchur .even L Ke ∧ NeutralNewbornSchur .odd L Ko :=
  first_common_cutoff_le_original_quartic hL hb

/-- The full complement cost is tied to the actual own-newborn eigenvalue. -/
theorem native_newborn_complement_consumer
    (p : ReversalParity) {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness p L K hL) (lam : ℝ) (hlam : lam < 0)
    (u : nativePoleNeutralParitySpace p L K) (hu0 : u ≠ 0)
    (hu : nativePoleNeutralParityCanonical p L K u = (lam : ℂ) • u)
    (x : nativePoleNeutralParitySpace p L K) (hx : inner ℂ u x = 0) :
    0 ≤ (inner ℂ (nativePoleNeutralParityCanonical p L K x) x).re ∧
      (-lam)*‖x‖^2 ≤ (inner ℂ
        (nativePoleNeutralParityCanonical p L K x-(lam : ℂ) • x) x).re ∧
      ‖x‖ ≤ ‖nativePoleNeutralParityCanonical p L K x-(lam : ℂ) • x‖/(-lam) :=
  nativeNewborn_negative_eigen_complement_bounds p s lam hlam u hu0 hu x hx

/-- This works at equality, but preserves the actual source-active hypothesis. -/
theorem source_active_ground_moment_consumer
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K) (lam : ℝ)
    (u : poleNeutralEvenSubspace L K)
    (hu : poleNeutralEvenCompressedCanonical L K u = (lam : ℂ) • u)
    (hle : lam ≤ poleNeutralOddRayleighBottom L K hL hK)
    (hf : poleNeutralCorrectedCubicSource L K u ≠ 0) :
    0 < (star (poleNeutralCorrectedCubicSource L K u) *
      centeredMoment K 4 (evenBoundaryFlatRawCoefficients K u.val)).re :=
  native_source_active_moment_pos_of_le_odd_bottom hL K hK lam u hu hle hf

/-- Genuine own-newborn data discharges simplicity, regardless of odd ordering. -/
theorem actual_newborn_even_ground_simple_consumer
    {L : ℝ} {K : ℕ} {hL : 0 < L}
    (s : NativeNewbornSourceWitness .even L K hL)
    (hneg : poleNeutralEvenRayleighBottom L K hL s.cutoff_lower < 0) :
    Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL s.cutoff_lower : ℂ)) = 1 :=
  nativeNewborn_even_ground_simple s hneg

/-- Both complete ground eigenspaces and the actual two source functionals. -/
theorem tied_ground_not_both_silent_consumer
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (htie : poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK)
    (heSimple : Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ)) = 1)
    (hoSimple : Module.finrank ℂ (Module.End.eigenspace (poleNeutralOddCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ)) = 1)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u)
    (w : poleNeutralOddSubspace L K) (hw0 : w ≠ 0)
    (hw : poleNeutralOddCompressedCanonical L K w =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • w) :
    ¬ (poleNeutralCorrectedCubicSource L K u = 0 ∧
      poleNeutralCubicPairingFunctional L K w = 0) :=
  simple_native_tied_ground_not_both_silent hL K hK htie heSimple hoSimple u hu0 hu w hw0 hw

/-- Independent complete-type consumer; no simplicity of the odd kernel is assumed. -/
theorem tied_ground_whole_kernel_visibility_consumer
    {L : ℝ} (hL : 0 < L) (K : ℕ) (hK : 3 ≤ K)
    (htie : poleNeutralEvenRayleighBottom L K hL hK =
      poleNeutralOddRayleighBottom L K hL hK)
    (hsimple : Module.finrank ℂ (Module.End.eigenspace (poleNeutralEvenCompressedCanonical L K)
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ)) = 1)
    (u : poleNeutralEvenSubspace L K) (hu0 : u ≠ 0)
    (hu : poleNeutralEvenCompressedCanonical L K u =
      (poleNeutralEvenRayleighBottom L K hL hK : ℂ) • u) :
    (poleNeutralCorrectedCubicSource L K u = 0 ∧
      poleNeutralOddShiftedKernelProjection L K (poleNeutralEvenRayleighBottom L K hL hK)
        (poleNeutralCubicCompressionVector L K) ≠ 0) ∨
    (poleNeutralCorrectedCubicSource L K u ≠ 0 ∧
      poleNeutralOddShiftedKernelProjection L K (poleNeutralEvenRayleighBottom L K hL hK)
        (poleNeutralCubicCompressionVector L K) = 0) :=
  simple_even_tie_whole_kernel_exclusive_visibility hL K hK htie hsimple u hu0 hu

end Zeta23.OPICARound4.Validation
