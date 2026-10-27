import Zeta23.OPICARound2.SyntheticControls

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ComplexConjugate

namespace Zeta23.OPICARound2.Validation

/-! S12a: literal kernels, actual strong convolution operators and exact mass. -/
theorem twins_literal_minus (t : ℝ) : syntheticMinusKernel t=
    ((if 0≤t then Real.exp (-t) else 0)+
      (3/2:ℝ)*(if 0≤t-1 then Real.exp (-(t-1)) else 0))/4 := rfl

theorem twins_literal_plus (t : ℝ) : syntheticPlusKernel t=
    ((3/2:ℝ)*(if 0≤t then Real.exp (-t) else 0)+
      (if 0≤t-1 then Real.exp (-(t-1)) else 0))/4 := rfl

theorem twins_kernel_domains : Integrable syntheticMinusKernel ∧ Integrable syntheticPlusKernel ∧
    (∀ t : ℝ, t<0 → syntheticMinusKernel t=0 ∧ syntheticPlusKernel t=0) := by
  refine ⟨synthetic_minus_integrable,synthetic_plus_integrable,?_⟩
  intro t ht
  exact ⟨synthetic_minus_zero_negative t ht,synthetic_plus_zero_negative t ht⟩

theorem twins_positive_envelopes (t : ℝ) :
    0≤syntheticMinusKernel t ∧ syntheticMinusKernel t≤Real.exp (-t/2) ∧
    0≤syntheticPlusKernel t ∧ syntheticPlusKernel t≤Real.exp (-t/2) :=
  ⟨(synthetic_twins_nonneg t).1,(synthetic_twins_dominating_exponential t).1,
    (synthetic_twins_nonneg t).2,(synthetic_twins_dominating_exponential t).2⟩

theorem twins_exact_mass_and_operator_bounds :
    (∫ t : ℝ,syntheticMinusKernel t)=(5/8:ℝ) ∧
    (∫ t : ℝ,syntheticPlusKernel t)=(5/8:ℝ) ∧
    ‖syntheticMinusOperator‖≤(5/8:ℝ) ∧ ‖syntheticPlusOperator‖≤(5/8:ℝ) :=
  ⟨synthetic_twins_mass.1,synthetic_twins_mass.2,synthetic_twins_contractions⟩

theorem twins_expected_physical_laplace (z : ℂ) (hz : 0≤z.re) :
    (∫ t : ℝ,Complex.exp (-z*(t:ℂ))*(syntheticMinusKernel t:ℂ))=
      (1+(3/2:ℂ)*Complex.exp (-z))/(4*(z+1)) ∧
    (∫ t : ℝ,Complex.exp (-z*(t:ℂ))*(syntheticPlusKernel t:ℂ))=
      ((3/2:ℂ)+Complex.exp (-z))/(4*(z+1)) := synthetic_twins_laplace hz

/-! S12b: phase-sensitive normalization and the actual causal adjoint identity. -/
theorem twins_expected_boundary_power (xi : ℝ) :
    ‖(1+(3/2:ℂ)*Complex.exp (-((xi:ℂ)*Complex.I)))/(4*((xi:ℂ)*Complex.I+1))‖^2=
      (13+12*Real.cos xi)/(64*(1+xi^2)) ∧
    ‖((3/2:ℂ)+Complex.exp (-((xi:ℂ)*Complex.I)))/(4*((xi:ℂ)*Complex.I+1))‖^2=
      (13+12*Real.cos xi)/(64*(1+xi^2)) := synthetic_boundary_power xi

theorem twins_expected_causal_power :
    (ContinuousLinearMap.adjoint syntheticMinusOperator).comp syntheticMinusOperator=
      (ContinuousLinearMap.adjoint syntheticPlusOperator).comp syntheticPlusOperator :=
  synthetic_twins_equal_power

theorem twins_expected_causal_norms (f : CausalProbeL2) :
    ‖syntheticMinusOperator f‖=‖syntheticPlusOperator f‖ := synthetic_twins_equal_norm f

/-! S12c: a boundedly invertible input factor, genuine dense range and right zeros. -/
theorem twins_actual_plus_factor : IsUnit syntheticPlusFactor := syntheticPlusFactor_isUnit

theorem twins_smooth_inverse (phi : SchwartzMap ℝ ℂ) :
    kernelL2Operator syntheticExponential synthetic_exponential_integrable
      ((SchwartzMap.derivCLM ℂ ℂ phi+phi).toLp 2 (volume:Measure ℝ))=
      phi.toLp 2 (volume:Measure ℝ) := synthetic_exponential_derivative_inverse phi

theorem twins_actual_dense_causal_range : DenseRange syntheticPlusOperator := synthetic_plus_dense_causal_range

theorem twins_expected_right_zeros (k : ℤ) :
    0<(syntheticRightZero k).re ∧
    syntheticRightZero k=(Real.log (3/2):ℂ)+(2*(k:ℂ)+1)*Real.pi*Complex.I ∧
    syntheticMinusMultiplier (syntheticRightZero k)=0 :=
  ⟨synthetic_right_zero_positive k,rfl,synthetic_minus_right_zeros k⟩

theorem twins_actual_range_annihilator (k : ℤ) (f : CausalProbeL2) :
    CCM.nativeCausalLaplaceMoment (syntheticRightZero k) 0 (syntheticMinusOperator f:ProbeL2)=0 :=
  synthetic_minus_range_annihilated k f

theorem twins_expected_distinct_causal_closures :
    ¬DenseRange syntheticMinusOperator ∧
    closure (Set.range syntheticMinusOperator)≠closure (Set.range syntheticPlusOperator) :=
  ⟨synthetic_minus_not_dense_causal_range,synthetic_causal_range_closures_differ⟩

/-! S12d: the exact local equation with a genuinely unstable input. -/
theorem twins_actual_unstable_parameter :
    syntheticUnstableLambda=(Real.log (3/2):ℂ)+9*Real.pi*Complex.I := syntheticUnstableLambda_literal

theorem twins_actual_local_input (t : ℝ) : syntheticUnstableInput t=
    if 0≤t then Complex.exp (syntheticUnstableLambda*(t:ℂ)) else 0 := rfl

theorem twins_unstable_input_control : ¬MemLp syntheticUnstableInput 2 volume := synthetic_unstable_input_not_memLp

theorem twins_actual_completed_output :
    (syntheticStableOutput:ProbeL2)=ᵐ[volume] syntheticStablePhysical := syntheticStableOutput_coe

theorem twins_actual_local_equation (t : ℝ) :
    (∫ s : ℝ,(syntheticMinusKernel s:ℂ)*syntheticUnstableInput (t-s))=syntheticStablePhysical t :=
  syntheticLocalCompletion_eq_output t

theorem twins_expected_first_output (t : ℝ) (ht0 : 0≤t) (ht1 : t<1) :
    syntheticStablePhysical t=(1/4:ℂ)*
      (Complex.exp (syntheticUnstableLambda*(t:ℂ))-Complex.exp (-(t:ℂ)))/(syntheticUnstableLambda+1) :=
  syntheticStablePhysical_first ht0 ht1

theorem twins_expected_tail_output (t : ℝ) (ht : 1≤t) :
    syntheticStablePhysical t=-(1/4:ℂ)*(1+(3/2)*Complex.exp 1)*
      Complex.exp (-(t:ℂ))/(syntheticUnstableLambda+1) := syntheticStablePhysical_tail ht

theorem twins_expected_nonzero_pairing :
    CCM.nativeCausalLaplaceMoment syntheticUnstableLambda 0 (syntheticStableOutput:ProbeL2)=
      (1/4:ℂ)/(syntheticUnstableLambda+1) := syntheticStableOutput_laplace

theorem twins_expected_positive_distance :
    0<Real.sqrt (2*syntheticUnstableLambda.re)*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖ ∧
    Real.sqrt (2*syntheticUnstableLambda.re)*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖≤
      Metric.infDist syntheticStableOutput (closure (Set.range syntheticMinusOperator)) :=
  ⟨synthetic_output_separation_positive,synthetic_output_distance⟩

/-! S12e: full-line convolution domains and the shifted causal witness. -/
theorem twins_actual_full_line_operators :
    syntheticFullMinusOperator=kernelL2Operator syntheticMinusKernel synthetic_minus_integrable ∧
    syntheticFullPlusOperator=kernelL2Operator syntheticPlusKernel synthetic_plus_integrable := ⟨rfl,rfl⟩

theorem twins_expected_full_line_density :
    DenseRange syntheticFullMinusOperator ∧ DenseRange syntheticFullPlusOperator := synthetic_full_twins_dense_ranges

theorem twins_actual_nonzero_boundary (xi : ℝ) :
    syntheticMinusMultiplier ((xi:ℂ)*Complex.I)≠0 ∧ syntheticPlusMultiplier ((xi:ℂ)*Complex.I)≠0 :=
  synthetic_boundary_multipliers_nonzero xi

theorem twins_actual_damped_output (epsilon : ℝ) (hepsilon : 0≤epsilon) :
    (syntheticDampedOutput epsilon hepsilon:ProbeL2)=ᵐ[volume] syntheticDampedPhysical epsilon :=
  syntheticDampedOutput_coe epsilon hepsilon

theorem twins_expected_damped_local_equation (epsilon t : ℝ) :
    (∫ s : ℝ,((Real.exp (-epsilon*s)*syntheticMinusKernel s:ℝ):ℂ)*syntheticDampedInput epsilon (t-s))=
      (Real.exp (-epsilon*t):ℂ)*syntheticStablePhysical t := synthetic_damped_local_completion epsilon t

theorem twins_expected_shifted_pairing (epsilon : ℝ) (hepsilon : 0≤epsilon) :
    CCM.nativeCausalLaplaceMoment (syntheticUnstableLambda-(epsilon:ℂ)) 0
      (syntheticDampedOutput epsilon hepsilon:ProbeL2)=(1/4:ℂ)/(syntheticUnstableLambda+1) :=
  syntheticDampedOutput_laplace epsilon hepsilon

theorem twins_expected_damped_obstruction (epsilon : ℝ) (hepsilon : 0<epsilon)
    (hsmall : epsilon<syntheticUnstableLambda.re) :
    ¬MemLp (syntheticDampedInput epsilon) 2 volume ∧
    0<Real.sqrt (2*(syntheticUnstableLambda.re-epsilon))*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖ ∧
    Real.sqrt (2*(syntheticUnstableLambda.re-epsilon))*‖(1/4:ℂ)/(syntheticUnstableLambda+1)‖≤
      Metric.infDist (syntheticDampedOutput epsilon hepsilon.le)
        (closure (Set.range (syntheticDampedOperator epsilon hepsilon.le))) :=
  ⟨synthetic_damped_input_not_memLp epsilon hsmall,synthetic_damped_output_distance epsilon hepsilon.le hsmall⟩

/-! Typed falsification controls: equal power is insufficient; norm<1 inverts I-T. -/
theorem twins_small_norm_does_not_invert_T :
    IsUnit ((1:CausalProbeL2 →L[ℂ] CausalProbeL2)-syntheticMinusOperator) ∧
      ¬IsUnit syntheticMinusOperator := synthetic_small_operator_inverse_control

theorem twins_completed_output_not_in_causal_range :
    syntheticStableOutput∉closure (Set.range syntheticMinusOperator) ∧
      syntheticStableOutput∈Set.range syntheticPlusOperator :=
  ⟨synthetic_output_not_mem_minus_closure,synthetic_output_mem_plus_range⟩

#print axioms Zeta23.OPICARound2.positive_equal_power_causal_twins
#print axioms Zeta23.OPICARound2.Validation.twins_expected_physical_laplace
#print axioms Zeta23.OPICARound2.Validation.twins_expected_causal_power
#print axioms Zeta23.OPICARound2.Validation.twins_smooth_inverse
#print axioms Zeta23.OPICARound2.Validation.twins_expected_distinct_causal_closures
#print axioms Zeta23.OPICARound2.Validation.twins_actual_local_equation
#print axioms Zeta23.OPICARound2.Validation.twins_expected_positive_distance
#print axioms Zeta23.OPICARound2.Validation.twins_expected_full_line_density
#print axioms Zeta23.OPICARound2.Validation.twins_expected_damped_obstruction
#print axioms Zeta23.OPICARound2.Validation.twins_small_norm_does_not_invert_T

end Zeta23.OPICARound2.Validation
