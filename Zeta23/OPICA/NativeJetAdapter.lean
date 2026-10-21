import Zeta23.OPICA.LocalObstruction
import Zeta23.OPICA.RangeSeparation
import Zeta23.ExceptionalZero.Step123CompleteOutput

/-! Source-bound observations of the existing physical input.  The same
complete output is retained throughout the view and its consumer. -/

noncomputable section
open Complex Set MeasureTheory Filter
open scoped Topology

namespace Zeta23.OPICA
open Zeta23.ExceptionalZero Zeta23.CCM

private theorem nativeKernel_analyticAt (rho : zetaZeroConfig.carrier) :
    AnalyticAt ℂ nativeZeroJetKernelMultiplier ((rho : ℂ) - 1 / 2) := by
  have hrho : IsNontrivialZero (rho : ℂ) := rho.property
  have hz : AnalyticAt ℂ riemannZeta ((rho : ℂ) - 1 / 2 + 1 / 2) := by
    simpa only [sub_add_cancel] using
      riemannZeta_analyticOnNhd_compl_one _ hrho.not_trivial.2
  have hs : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) ((rho : ℂ) - 1 / 2) := by fun_prop
  exact (nativeCompletionRationalMultiplier_at_zero_analyticAt rho).mul
    (hz.comp (f := fun z : ℂ => z + 1 / 2) (x := (rho : ℂ) - 1 / 2) hs)

/-- A factorization witness of the literal native kernel multiplier, built
from its proved order and analyticity. No factorization is a caller input. -/
def nativeKernelMultiplierOrderData (rho : zetaZeroConfig.carrier) :
    MultiplierOrderData ((rho : ℂ) - 1 / 2) :=
  let hfact := (nativeKernel_analyticAt rho).analyticOrderAt_eq_natCast.mp
    (nativeZeroJetKernelMultiplier_order rho)
  { multiplier := nativeZeroJetKernelMultiplier
    order := zeroMult (rho : ℂ)
    unit := Classical.choose hfact
    unit_analytic := (Classical.choose_spec hfact).1
    unit_ne_zero := (Classical.choose_spec hfact).2.1
    multiplier_eq := (Classical.choose_spec hfact).2.2 }

private theorem multiplierOrder_transport {c d : ℂ} (h : c = d)
    (M : MultiplierOrderData c) : (h ▸ M).order = M.order := by
  cases h
  rfl

private theorem multiplierFunction_transport {c d : ℂ} (h : c = d)
    (M : MultiplierOrderData c) : (h ▸ M).multiplier = M.multiplier := by
  cases h
  rfl

/-- The generic local multiplier law is consumed with the actual native
kernel, on a separately supplied visible pole datum. The source datum is
kept explicit: this does not assert a new native pole or contact equation. -/
theorem native_kernel_completion_consumer {Source : Type*}
    (rho : zetaZeroConfig.carrier) (s : SimplePoleData Source)
    (hcenter : s.center = (rho : ℂ) - 1 / 2) :
    let M : MultiplierOrderData s.center := hcenter.symm ▸ nativeKernelMultiplierOrderData rho
    analyticOrderAt (s.regularRepresentative M) s.center = (M.order - 1 : ℕ) ∧
      iteratedDeriv (M.order - 1) (s.regularRepresentative M) s.center =
        (M.order - 1).factorial * M.unit s.center * s.residue := by
  dsimp only
  exact ⟨completion_order _ _, completion_leading_jet _ _⟩

theorem native_kernel_residual_consumer {Source : Type*}
    (rho : zetaZeroConfig.carrier) (s : SimplePoleData Source)
    (hcenter : s.center = (rho : ℂ) - 1 / 2)
    (b : ℂ → ℂ) (hb : AnalyticAt ℂ b s.center) :
    Tendsto (fun z => (z - s.center) *
      ((1 + nativeZeroJetKernelMultiplier z * b z) * s.field z))
      (𝓝[≠] s.center) (𝓝 s.residue) := by
  let M : MultiplierOrderData s.center := hcenter.symm ▸ nativeKernelMultiplierOrderData rho
  have hm : 0 < M.order := by
    rw [show M.order = zeroMult (rho : ℂ) from
      multiplierOrder_transport hcenter.symm (nativeKernelMultiplierOrderData rho)]
    exact zetaZeroConfig.one_le_mult _ rho.property
  have hM : M.multiplier = nativeZeroJetKernelMultiplier :=
    multiplierFunction_transport hcenter.symm (nativeKernelMultiplierOrderData rho)
  have h := (residual_congr_preserves_residue s M hm b hb).1
  simpa only [hM] using h

theorem native_completed_input_obstruction_order
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    analyticOrderAt
      (fun z => nativeCausalLaplaceMoment z 0
        (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le : NativeCompletionL2))
      (nativeZeroJetParameter rho) = (zeroMult (rho : ℂ) - 1 : ℕ) :=
  by
    have h := nativeActualInputLaplace_order_of_zero (nativeZeroJetDamping rho)
      (nativeZeroJetDamping_pos rho hoff).le (nativeZeroJetRightZero rho)
      (ne_of_gt (nativeZeroJetRightZero_re_gt_half rho hoff)) (nativeZeroJetParameter rho)
      (nativeZeroJetParameter_re_pos rho hoff) (nativeZeroJetParameter_add_damping rho)
    simpa only [nativeZeroJetRightZero_mult] using h

/-- The literal physical input transform, with its proved local order at
the existing damping-shifted parameter. Its unit factor is obtained from
analyticity and the actual-input order theorem, rather than supplied by
the caller. -/
def nativeCompletedInputMultiplierOrderData
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    MultiplierOrderData (nativeZeroJetParameter rho) :=
  let hfact := (nativeCausalLaplaceMoment_analyticAt (nativeZeroJetParameter rho)
    (nativeZeroJetParameter_re_pos rho hoff) 0
    (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
      (nativeZeroJetDamping_pos rho hoff).le)).analyticOrderAt_eq_natCast.mp
        (native_completed_input_obstruction_order rho hoff)
  { multiplier := fun z => nativeCausalLaplaceMoment z 0
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho hoff).le : NativeCompletionL2)
    order := zeroMult (rho : ℂ) - 1
    unit := Classical.choose hfact
    unit_analytic := (Classical.choose_spec hfact).1
    unit_ne_zero := (Classical.choose_spec hfact).2.1
    multiplier_eq := (Classical.choose_spec hfact).2.2 }

/-- The actual-input local witness retains the complete physical
transform and its genuine-neighborhood identification, at precisely the
right-zero parameter and damping already chosen by the native source. -/
theorem native_completed_input_witness_correct
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    let M := nativeCompletedInputMultiplierOrderData rho hoff
    M.multiplier = (fun z => nativeCausalLaplaceMoment z 0
        (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le : NativeCompletionL2)) ∧
      M.order = zeroMult (rho : ℂ) - 1 ∧
      M.multiplier =ᶠ[𝓝 (nativeZeroJetParameter rho)]
        (fun z => nativeZeroJetInputMultiplier (z + (nativeZeroJetDamping rho : ℂ))) := by
  refine ⟨rfl, rfl, ?_⟩
  have hne : nativeZeroJetParameter rho + (nativeZeroJetDamping rho : ℂ) ≠
      (1 / 2 : ℂ) := by
    rw [nativeZeroJetParameter_add_damping rho]
    have hr : IsNontrivialZero (nativeZeroJetRightZero rho : ℂ) :=
      (nativeZeroJetRightZero rho).property
    intro h
    apply hr.not_trivial.2
    linear_combination h
  exact nativeActualInputLaplace_eventuallyEq_multiplier (nativeZeroJetDamping rho)
    (nativeZeroJetDamping_pos rho hoff).le (nativeZeroJetParameter rho)
    (nativeZeroJetParameter_re_pos rho hoff) hne

theorem native_completed_input_obstruction_jet
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    inner ℂ (nativeZeroJetAdjointWitness rho hoff)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho hoff).le) =
      (-1 : ℂ) ^ zeroMult (rho : ℂ) *
        nativeCompletionRationalMultiplier ((nativeZeroJetRightZero rho : ℂ) - 1 / 2) *
        nativeOriginalSourceLaplace ((nativeZeroJetRightZero rho : ℂ) - 1 / 2) *
        iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (nativeZeroJetRightZero rho : ℂ) :=
  nativeCompletedInput_zeroJet_value rho hoff

theorem native_completed_input_obstruction_ne_zero
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    inner ℂ (nativeZeroJetAdjointWitness rho hoff)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho hoff).le) ≠ 0 :=
  nativeCompletedInput_zeroJet_ne_zero rho hoff

theorem native_range_distance_lower
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    0 < ‖inner ℂ (nativeZeroJetAdjointWitness rho hoff)
        (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le)‖ /
        ‖nativeZeroJetAdjointWitness rho hoff‖ ∧
      ‖inner ℂ (nativeZeroJetAdjointWitness rho hoff)
        (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le)‖ /
        ‖nativeZeroJetAdjointWitness rho hoff‖ ≤
      Metric.infDist
        (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le)
        (closure (Set.range (nativeDampedCompletionCausalL2Operator
          (nativeZeroJetDamping rho) (nativeZeroJetDamping_pos rho hoff).le))) := by
  simpa only [innerSL_apply_apply, innerSL_apply_norm] using
    range_distance_of_annihilator
      (nativeDampedCompletionCausalL2Operator (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho hoff).le)
      (innerSL ℂ (nativeZeroJetAdjointWitness rho hoff))
      (nativeZeroJet_annihilates_range rho hoff)
      (nativeCompletedInput_zeroJet_ne_zero rho hoff)

structure Step123OpicaView {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late) where
  source : ℝ → ℝ
  source_eq : source = nativeOriginalIntegerDrive
  field : ℝ → ℝ
  field_eq : field = nativeOriginalPrimeField
  input : ℝ → ℝ
  input_eq : input = nativeCompletedInput
  input_obstruction : GeneratedStep123RangeObstruction rho out.generated.offLine
  same_state_fields : Step123SameStateFieldRecord out.generated.native

def step123OpicaView {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late) : Step123OpicaView out where
  source := nativeOriginalIntegerDrive
  source_eq := rfl
  field := nativeOriginalPrimeField
  field_eq := rfl
  input := nativeCompletedInput
  input_eq := rfl
  input_obstruction := out.rangeObstruction
  same_state_fields := out.sameState

theorem step123_output_opica_view_correct {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late) :
    (step123OpicaView out).source = nativeOriginalIntegerDrive ∧
    (step123OpicaView out).field = nativeOriginalPrimeField ∧
    (step123OpicaView out).input = nativeCompletedInput ∧
    Step123SameStateFieldRecord out.generated.native ∧
    GeneratedStep123RangeObstruction rho out.generated.offLine :=
  ⟨rfl, rfl, rfl, out.sameState, out.rangeObstruction⟩

theorem step123_eachPhase_opica_consumer (rho : zetaZeroConfig.carrier) {beta : ℝ}
    (hbeta : 0 < beta) (hgap : beta < |(rho : ℂ).re - 1 / 2|) :
    ∀ (phase : ReversalParity) (late : ℝ),
      ∃ out : GeneratedStep123CompleteOutput rho beta phase late,
        max late step123SameStateThreshold <
          fixedOriginalSincTrialAperture out.generated.sourceData.separation ∧
        (step123OpicaView out).source = nativeOriginalIntegerDrive ∧
        (step123OpicaView out).field = nativeOriginalPrimeField ∧
        (step123OpicaView out).input = nativeCompletedInput ∧
        Step123SameStateFieldRecord out.generated.native ∧
        GeneratedStep123RangeObstruction rho out.generated.offLine := by
  intro phase late
  obtain ⟨out, hlate⟩ := exists_eachPhase_cofinal_generatedStep123CompleteOutput
    rho hbeta hgap phase late
  exact ⟨out, hlate, step123_output_opica_view_correct out⟩

end Zeta23.OPICA
