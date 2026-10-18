import Zeta23.ExceptionalZero.Step123CompleteOutput

/-! Typed projections of all 44 contract fields from one generated packet.
These accessors expose their exact Lean types; release and semantic approval
remain separate gates. N14/N37 use the threshold already paid by this output. -/

noncomputable section
namespace Zeta23.RHRC
open Zeta23.CCM Zeta23.ExceptionalZero
variable {ρ : zetaZeroConfig.carrier} {β R : ℝ} {σ : ReversalParity}

/-- N01: the same stored packet, with its original field type. -/
def consumeN01 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n01_source_scale

/-- N02: the same stored packet, with its original field type. -/
def consumeN02 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n02_source_q_k_j

/-- N03: the same stored packet, with its original field type. -/
def consumeN03 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n03_source_properties

/-- N04: the same stored packet, with its original field type. -/
def consumeN04 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n04_source_bounds

/-- N05: the same stored packet, with its original field type. -/
def consumeN05 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n05_trial_index

/-- N06: the same stored packet, with its original field type. -/
def consumeN06 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n06_trial_original

/-- N07: the same stored packet, with its original field type. -/
def consumeN07 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n07_trial_original_properties

/-- N08: the same stored packet, with its original field type. -/
def consumeN08 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n08_image_raw

/-- N09: the same stored packet, with its original field type. -/
def consumeN09 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n09_image_positive_primitive

/-- N10: the same stored packet, with its original field type. -/
def consumeN10 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n10_image_endpoint_jets

/-- N11: the same stored packet, with its original field type. -/
def consumeN11 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n11_image_native_p

/-- N12: the same stored packet, with its original field type. -/
def consumeN12 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n12_image_unit_and_poles

/-- N13: the same stored packet, with its original field type. -/
def consumeN13 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n13_image_physical_equality

/-- N14: the same stored packet, with its original field type. -/
def consumeN14 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.imageErrors

/-- N15: the same stored packet, with its original field type. -/
def consumeN15 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n15_phase_full_matrices

/-- N16: the same stored packet, with its original field type. -/
def consumeN16 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n16_phase_scalar_contract

/-- N17: the same stored packet, with its original field type. -/
def consumeN17 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n17_retained_state

/-- N18: the same stored packet, with its original field type. -/
def consumeN18 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n18_retained_eta_lambda

/-- N19: the same stored packet, with its original field type. -/
def consumeN19 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n19_retained_inverses

/-- N20: the same stored packet, with its original field type. -/
def consumeN20 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n20_retained_ground

/-- N21: the same stored packet, with its original field type. -/
def consumeN21 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.sameState.n21_retained_branch

/-- N22: the same stored packet, with its original field type. -/
def consumeN22 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n22_retained_source_correction

/-- N23: the same stored packet, with its original field type. -/
def consumeN23 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.sameState.n23_retained_tie

/-- N24: the same stored packet, with its original field type. -/
def consumeN24 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n24_retained_admissible

/-- N25: the same stored packet, with its original field type. -/
def consumeN25 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n25_schur_detector

/-- N26: the same stored packet, with its original field type. -/
def consumeN26 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n26_schur_ground

/-- N27: the same stored packet, with its original field type. -/
def consumeN27 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n27_residual_neutral

/-- N28: the same stored packet, with its original field type. -/
def consumeN28 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n28_residual_gram

/-- N29: the same stored packet, with its original field type. -/
def consumeN29 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n29_native_X_U

/-- N30: the same stored packet, with its original field type. -/
def consumeN30 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n30_native_input_decay

/-- N31: the same stored packet, with its original field type. -/
def consumeN31 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n31_native_a_Y

/-- N32: the same stored packet, with its original field type. -/
def consumeN32 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n32_native_transforms

/-- N33: the same stored packet, with its original field type. -/
def consumeN33 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n33_range_operator

/-- N34: the same stored packet, with its original field type. -/
def consumeN34 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n34_range_residual_iteration

/-- N35: the same stored packet, with its original field type. -/
def consumeN35 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n35_forcing_direct

/-- N36: the same stored packet, with its original field type. -/
def consumeN36 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.sameState.n36_forcing_source_channels

/-- N37: the same stored packet, with its original field type. -/
def consumeN37 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.forcingErrors

/-- N38: the same stored packet, with its original field type. -/
def consumeN38 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.sameState.n38_forcing_ambient_residuals

/-- N39: the same stored packet, with its original field type. -/
def consumeN39 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n39_exterior_original

/-- N40: the same stored packet, with its original field type. -/
def consumeN40 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.fields.n40_exterior_history

/-- G01: the actual zero gap and positive exponent. -/
def consumeG01 (out : GeneratedStep123CompleteOutput ρ β σ R) :
    (ρ : ℂ).re ≠ 1 / 2 ∧ 0 < β ∧ β < |(ρ : ℂ).re - 1 / 2| :=
  ⟨out.generated.offLine, out.generated.beta_pos, out.generated.beta_below⟩

/-- G02: exact generated record projection. -/
def consumeG02 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.thresholds_paid

/-- G03: exact generated record projection. -/
def consumeG03 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.completeNative

/-- G04: exact generated record projection. -/
def consumeG04 (out : GeneratedStep123CompleteOutput ρ β σ R) :=
  out.rangeObstruction

end Zeta23.RHRC
