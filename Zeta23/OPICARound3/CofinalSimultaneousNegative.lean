import Zeta23.OPICARound3.NeutralParityTopology
import Zeta23.CCM.Step123NativeSourceSpectralEvidence

noncomputable section

namespace Zeta23.OPICARound3

open CCM Set
open Zeta23.ExceptionalZero

set_option allowUnsafeReducibility true in
attribute [local reducible] Submodule.innerProductSpace
  poleNeutralEven_innerProductSpace poleNeutralOdd_innerProductSpace
  euclideanParityBoundaryFlatSubspace

/-- Each requested parity is produced by the original actual-zero source
at cofinally large apertures. No detector is replaced by a selected ground
or by the causal one-copy dictionary. -/
theorem neutral_parity_cofinal_of_off_line_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2)
    (p : ReversalParity) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ L ∈ NeutralParityApertures p := by
  have habs : 0 < |(ρ : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  let β := |(ρ : ℂ).re - 1 / 2| / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβρ : β < |(ρ : ℂ).re - 1 / 2| := by dsimp [β]; linarith
  obtain ⟨out, hlate⟩ := exists_generatedStep123ComposedEvidencePacket_cofinal ρ hβ hβρ p R
  let native := out.integrated.boundary.generated.native
  let L := fixedOriginalSincTrialAperture out.integrated.boundary.generated.sourceData.separation
  let K := originalDetectorQuarticCutoff L
  have hL : 0 < L := native.aperture_pos
  have hK : 3 ≤ K :=
    native.retained.state.selection.cutoff_nonempty.trans
      native.retained.state.selection.cutoff_le_detector
  refine ⟨L, (le_max_left R 4).trans_lt hlate, hL, K, hK, ?_⟩
  apply (native_neutral_parity_negative_iff p L K).mpr
  refine ⟨native.retained.state.detector, ?_⟩
  exact native.retained.state.detector_depth.trans_lt (neg_lt_zero.mpr (Real.exp_pos (β * L)))

/-- This is a source theorem about exact same-aperture centered extension,
not a general assertion that arbitrary cutoff families are nested. -/
theorem poleNeutralParityNegative_centered_extension (p : ReversalParity)
    {L : ℝ} (hL : 0 < L) {N M : ℕ} (hNM : N ≤ M)
    (hneg : PoleNeutralParityNegative p L N) : PoleNeutralParityNegative p L M := by
  cases p
  · obtain ⟨u, hu⟩ := hneg
    refine ⟨poleNeutralEvenCenteredZeroExtend L hNM u, ?_⟩
    rw [inner_poleNeutralEvenCompressedCanonical_centeredZeroExtend hL hNM u]
    exact hu
  · obtain ⟨u, hu⟩ := hneg
    refine ⟨poleNeutralOddCenteredZeroExtend L hNM u, ?_⟩
    rw [inner_poleNeutralOddCompressedCanonical_centeredZeroExtend hL hNM u]
    exact hu

/-- R3-D02: the tail cover, actual each-parity cofinal producer, moving
neutral openness and native nesting give common-aperture, common-cutoff
strict negativity. No common quartic cutoff or exponential depth is claimed. -/
theorem cofinally_both_neutral_negative_of_off_line_zero
    (ρ : zetaZeroConfig.carrier) (hoff : (ρ : ℂ).re ≠ 1 / 2) (R : ℝ) :
    ∃ L : ℝ, R < L ∧ 0 < L ∧ ∃ K : ℕ, 3 ≤ K ∧ BothNeutralNegative L K := by
  obtain ⟨L₀, hL₀, hcover⟩ := neutral_parity_cover_of_off_line_zero ρ hoff
  have hcover' : ∃ T : ℝ, ∀ L : ℝ, T < L →
      L ∈ NeutralParityApertures .even ∨ L ∈ NeutralParityApertures .odd := by
    refine ⟨L₀, ?_⟩
    intro L hL
    obtain ⟨K, hK, he | ho⟩ := hcover L hL
    · exact Or.inl ⟨hL₀.trans hL, K, hK, he⟩
    · exact Or.inr ⟨hL₀.trans hL, K, hK, ho⟩
  obtain ⟨L, hLR, he, ho⟩ := cofinal_open_overlap
    (NeutralParityApertures .even) (NeutralParityApertures .odd)
    (isOpen_neutralParityApertures .even) (isOpen_neutralParityApertures .odd)
    hcover' (neutral_parity_cofinal_of_off_line_zero ρ hoff .even)
    (neutral_parity_cofinal_of_off_line_zero ρ hoff .odd) R
  obtain ⟨hL, Ke, hKe, he⟩ := he
  obtain ⟨_, Ko, hKo, ho⟩ := ho
  refine ⟨L, hLR, hL, max Ke Ko, hKe.trans (le_max_left Ke Ko), ?_, ?_⟩
  · exact poleNeutralParityNegative_centered_extension .even hL (le_max_left Ke Ko) he
  · exact poleNeutralParityNegative_centered_extension .odd hL (le_max_right Ke Ko) ho

end Zeta23.OPICARound3

#print axioms Zeta23.OPICARound3.neutral_parity_cofinal_of_off_line_zero
#print axioms Zeta23.OPICARound3.cofinally_both_neutral_negative_of_off_line_zero
