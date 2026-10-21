import Zeta23.OPICA

/-!
# Explicit OPICA expected-type consumers (AUDIT_ONLY)

Each declaration below repeats the complete mathematical binders and result
of one required semantic root and supplies that root at the stated type.
The declarations live in the audit namespace, outside the mathematical public
inventory. In particular, the native consumers retain the actual source,
actual completed input, same generated output, and same-state equations.
-/

noncomputable section
namespace Zeta23.RHRC.OpicaValidation
open Zeta23.OPICA

section LocalObstruction
open Filter
open scoped Topology BigOperators

-- OPICA_L1_UNIT_MUL_SIMPLEPOLE_RESIDUE
theorem consume_unit_mul_simplePole_residue {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) (hk : m.order = 0) :
    Tendsto (fun z => (z - p.center) * (m.multiplier z * p.field z))
      (𝓝[≠] p.center) (𝓝 (m.unit p.center * p.residue)) := by
  exact Zeta23.OPICA.unit_mul_simplePole_residue p m hk

-- OPICA_L1_COMPLETION_REGULARREPRESENTATIVE_ANALYTIC
theorem consume_completion_regularRepresentative_analytic {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) :
    AnalyticAt ℂ (p.regularRepresentative m) p.center := by
  exact Zeta23.OPICA.completion_regularRepresentative_analytic p m

-- OPICA_L1_COMPLETION_ORDER
theorem consume_completion_order {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) :
    analyticOrderAt (p.regularRepresentative m) p.center = (m.order - 1 : ℕ) := by
  exact Zeta23.OPICA.completion_order p m

-- OPICA_L1_COMPLETION_LEADING_JET
theorem consume_completion_leading_jet {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) :
    iteratedDeriv (m.order - 1) (p.regularRepresentative m) p.center =
      (m.order - 1).factorial * m.unit p.center * p.residue := by
  exact Zeta23.OPICA.completion_leading_jet p m

-- OPICA_L2_RESIDUAL_CONGR_PRESERVES_RESIDUE
theorem consume_residual_congr_preserves_residue {Source : Type*}
    (s : SimplePoleData Source) (Z : MultiplierOrderData s.center)
    (hm : 0 < Z.order) (b : ℂ → ℂ) (hb : AnalyticAt ℂ b s.center) :
    Tendsto (fun z => (z - s.center) * ((1 + Z.multiplier z * b z) * s.field z))
      (𝓝[≠] s.center) (𝓝 s.residue) ∧
    (fun z => ((1 + Z.multiplier z * b z) * s.field z) - s.field z) =ᶠ[𝓝[≠] s.center]
      (fun z => b z * s.regularRepresentative Z z) := by
  exact Zeta23.OPICA.residual_congr_preserves_residue s Z hm b hb

-- OPICA_L2_FINITE_RESIDUAL_PRODUCTS_PRESERVE_RESIDUE
theorem consume_finite_residual_products_preserve_residue {Source : Type*}
    (s : SimplePoleData Source) (Z : MultiplierOrderData s.center)
    (hm : 0 < Z.order) (b : ℕ → ℂ → ℂ) (hb : ∀ i, AnalyticAt ℂ (b i) s.center)
    (n : ℕ) :
    Tendsto (fun z => (z - s.center) *
      ((∏ i ∈ Finset.range n, (1 + Z.multiplier z * b i z)) * s.field z))
      (𝓝[≠] s.center) (𝓝 s.residue) := by
  exact Zeta23.OPICA.finite_residual_products_preserve_residue s Z hm b hb n

-- OPICA_L3_ITERATED_COMPLETION_LEADING_JET
theorem consume_iterated_completion_leading_jet {Source : Type*}
    (s : SimplePoleData Source) (m : MultiplierOrderData s.center)
    (p : ℕ) (_hp : 0 < p) (_hm : 0 < m.order) :
    analyticOrderAt (s.regularRepresentative (m.pow p)) s.center =
        (p * m.order - 1 : ℕ) ∧
      iteratedDeriv (p * m.order - 1) (s.regularRepresentative (m.pow p)) s.center =
        (p * m.order - 1).factorial * m.unit s.center ^ p * s.residue := by
  exact Zeta23.OPICA.iterated_completion_leading_jet s m p _hp _hm

-- OPICA_L3_DOUBLE_COMPLETION_LEIBNIZ_FACTOR
theorem consume_double_completion_leibniz_factor {Source : Type*}
    (s : SimplePoleData Source) (m A : MultiplierOrderData s.center)
    (hm : 0 < m.order) (hA : A.order = m.order) :
    iteratedDeriv (2 * m.order - 1)
        (fun z => A.multiplier z * s.regularRepresentative m z) s.center =
      ((2 * m.order - 1).choose m.order : ℂ) *
        iteratedDeriv m.order A.multiplier s.center *
        iteratedDeriv (m.order - 1) (s.regularRepresentative m) s.center := by
  exact Zeta23.OPICA.double_completion_leibniz_factor s m A hm hA

-- Additional clause: Zeta23.OPICA.completion_agrees_punctured
theorem consume_completion_agrees_punctured {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) (hk : 0 < m.order) :
    (fun z => m.multiplier z * p.field z) =ᶠ[𝓝[≠] p.center]
      p.regularRepresentative m := by
  exact Zeta23.OPICA.completion_agrees_punctured p m hk

-- Additional clause: Zeta23.OPICA.completion_lower_derivatives
theorem consume_completion_lower_derivatives {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center)
    (j : ℕ) (hj : j < m.order - 1) :
    iteratedDeriv j (p.regularRepresentative m) p.center = 0 := by
  exact Zeta23.OPICA.completion_lower_derivatives p m j hj

-- Additional clause: Zeta23.OPICA.completion_taylor_coefficient
theorem consume_completion_taylor_coefficient {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) :
    normalizedTaylorObservation (m.order - 1) (p.regularRepresentative m) p.center =
      m.unit p.center * p.residue := by
  exact Zeta23.OPICA.completion_taylor_coefficient p m

-- Additional clause: Zeta23.OPICA.completion_leading_jet_ne_zero
theorem consume_completion_leading_jet_ne_zero {Source : Type*}
    (p : SimplePoleData Source) (m : MultiplierOrderData p.center) :
    iteratedDeriv (m.order - 1) (p.regularRepresentative m) p.center ≠ 0 := by
  exact Zeta23.OPICA.completion_leading_jet_ne_zero p m

-- Additional clause: Zeta23.OPICA.residual_correction_lower_derivatives
theorem consume_residual_correction_lower_derivatives {Source : Type*}
    (s : SimplePoleData Source) (Z : MultiplierOrderData s.center)
    (b : ℂ → ℂ) (hb : AnalyticAt ℂ b s.center) :
    AnalyticAt ℂ (fun z => b z * s.regularRepresentative Z z) s.center ∧
      ∀ j < Z.order - 1,
        iteratedDeriv j (fun z => b z * s.regularRepresentative Z z) s.center = 0 := by
  exact Zeta23.OPICA.residual_correction_lower_derivatives s Z b hb

-- Additional clause: Zeta23.OPICA.finite_residual_products_difference
theorem consume_finite_residual_products_difference {Source : Type*}
    (s : SimplePoleData Source) (Z : MultiplierOrderData s.center)
    (hm : 0 < Z.order) (b : ℕ → ℂ → ℂ) (hb : ∀ i, AnalyticAt ℂ (b i) s.center)
    (n : ℕ) :
    (fun z => ((∏ i ∈ Finset.range n, (1 + Z.multiplier z * b i z)) * s.field z) -
        s.field z) =ᶠ[𝓝[≠] s.center]
      (fun z => finiteResidualCofactor Z.multiplier b n z * s.regularRepresentative Z z) ∧
      AnalyticAt ℂ
        (fun z => finiteResidualCofactor Z.multiplier b n z * s.regularRepresentative Z z)
        s.center ∧
      ∀ j < Z.order - 1, iteratedDeriv j
        (fun z => finiteResidualCofactor Z.multiplier b n z * s.regularRepresentative Z z)
        s.center = 0 := by
  exact Zeta23.OPICA.finite_residual_products_difference s Z hm b hb n

-- Additional clause: Zeta23.OPICA.residual_power_preserves_residue
theorem consume_residual_power_preserves_residue {Source : Type*}
    (s : SimplePoleData Source) (Z : MultiplierOrderData s.center)
    (hm : 0 < Z.order) (b : ℂ → ℂ) (hb : AnalyticAt ℂ b s.center) (n : ℕ) :
    Tendsto (fun z => (z - s.center) * ((1 - Z.multiplier z * b z) ^ n * s.field z))
      (𝓝[≠] s.center) (𝓝 s.residue) := by
  exact Zeta23.OPICA.residual_power_preserves_residue s Z hm b hb n

end LocalObstruction

section LocalQuotients
open Filter
open scoped Topology BigOperators

-- OPICA_L2_ZERO_IDEAL_EQ_COORDINATE_POWER
theorem consume_zero_ideal_eq_coordinate_power (center : ℂ)
    (m : MultiplierOrderData center) :
    Ideal.span ({holomorphicGermOf center m.multiplier (multiplier_analytic m)} :
      Set (HolomorphicGerm center)) =
      Ideal.span ({coordinateGerm center ^ m.order} : Set (HolomorphicGerm center)) := by
  exact Zeta23.OPICA.zero_ideal_eq_coordinate_power center m

-- OPICA_L2_TRUNCATED_TAYLOR_QUOTIENT_EQUIV
theorem consume_truncated_taylor_quotient_equiv (center : ℂ) (m : MultiplierOrderData center) :
    ∃ e : (HolomorphicGerm center ⧸
        Ideal.span ({holomorphicGermOf center m.multiplier (multiplier_analytic m)} :
          Set (HolomorphicGerm center))) ≃+*
      (Polynomial ℂ ⧸ Ideal.span ({Polynomial.X ^ m.order} : Set (Polynomial ℂ))),
      ∀ p : Polynomial ℂ,
        e (Ideal.Quotient.mk _ (polynomialGerm center p)) = Ideal.Quotient.mk _ p := by
  exact Zeta23.OPICA.truncated_taylor_quotient_equiv center m

-- OPICA_L2_COMPLETION_QUOTIENT_EQUIV
theorem consume_completion_quotient_equiv (center : ℂ) (m : MultiplierOrderData center)
    (hm : 0 < m.order) :
    ∃ e : (LocalPoleCarrier center ⧸ LocalPoleBackground center) ≃ₗ[HolomorphicGerm center]
        (LocalCompletedCarrier center m.order ⧸ LocalCompletedBackground center m.order),
      (∀ f : LocalPoleCarrier center,
        e (Submodule.Quotient.mk f) = Submodule.Quotient.mk (localCompletionMap center m hm f)) ∧
      ∀ a : HolomorphicGerm center,
        e (Submodule.Quotient.mk
          (meromorphicSpanEquiv center (meromorphicCoordinate center)⁻¹
            (inv_ne_zero (meromorphicCoordinate_ne_zero center)) a)) =
          Submodule.Quotient.mk
            (meromorphicSpanEquiv center (meromorphicCoordinate center ^ (m.order - 1))
              (pow_ne_zero _ (meromorphicCoordinate_ne_zero center))
              (holomorphicGermOf center m.unit m.unit_analytic * a)) := by
  exact Zeta23.OPICA.completion_quotient_equiv center m hm

end LocalQuotients

section AffineTransport
open Filter
open scoped Topology BigOperators

-- OPICA_L4_AFFINE_TRANSPORT_CORRECTED_EQ
theorem consume_affine_transport_corrected_eq (f : ℂ → ℂ) (M B : ℕ → ℂ → ℂ)
    (n : ℕ) (z : ℂ) :
    localAffineIterate f M B n z - localAffineCorrection M B n z =
      (∏ i ∈ Finset.range n, M i z) * f z := by
  exact Zeta23.OPICA.affine_transport_corrected_eq f M B n z

-- OPICA_L4_AFFINE_TRANSPORT_LEADING_JET
theorem consume_affine_transport_leading_jet {Source : Type*} (s : SimplePoleData Source)
    (m : ℕ → MultiplierOrderData s.center) (B : ℕ → ℂ → ℂ) (n : ℕ)
    (horder : 0 < (MultiplierOrderData.prod m n).order) :
    (fun z => localAffineIterate s.field (fun i => (m i).multiplier) B n z -
        localAffineCorrection (fun i => (m i).multiplier) B n z)
        =ᶠ[𝓝[≠] s.center] s.regularRepresentative (MultiplierOrderData.prod m n) ∧
      analyticOrderAt (s.regularRepresentative (MultiplierOrderData.prod m n)) s.center =
        ((∑ i ∈ Finset.range n, (m i).order) - 1 : ℕ) ∧
      iteratedDeriv ((MultiplierOrderData.prod m n).order - 1)
        (s.regularRepresentative (MultiplierOrderData.prod m n)) s.center =
        ((MultiplierOrderData.prod m n).order - 1).factorial *
          (MultiplierOrderData.prod m n).unit s.center * s.residue := by
  exact Zeta23.OPICA.affine_transport_leading_jet s m B n horder

-- Additional clause: Zeta23.OPICA.affine_correction_expansion
theorem consume_affine_correction_expansion (M B : ℕ → ℂ → ℂ) (n : ℕ) (z : ℂ) :
    localAffineCorrection M B n z =
      ∑ j ∈ Finset.range n, (∏ i ∈ Finset.Ico (j + 1) n, M i z) * B j z := by
  exact Zeta23.OPICA.affine_correction_expansion M B n z

-- Additional clause: Zeta23.OPICA.affine_correction_analytic
theorem consume_affine_correction_analytic (center : ℂ) (M B : ℕ → ℂ → ℂ)
    (hM : ∀ i, AnalyticAt ℂ (M i) center)
    (hB : ∀ i, AnalyticAt ℂ (B i) center) (n : ℕ) :
    AnalyticAt ℂ (localAffineCorrection M B n) center := by
  exact Zeta23.OPICA.affine_correction_analytic center M B hM hB n

-- Additional clause: Zeta23.OPICA.affine_transport_unit_residue
theorem consume_affine_transport_unit_residue {Source : Type*} (s : SimplePoleData Source)
    (m : ℕ → MultiplierOrderData s.center) (B : ℕ → ℂ → ℂ) (n : ℕ)
    (horder : (MultiplierOrderData.prod m n).order = 0) :
    Tendsto (fun z => (z - s.center) *
      (localAffineIterate s.field (fun i => (m i).multiplier) B n z -
        localAffineCorrection (fun i => (m i).multiplier) B n z))
      (𝓝[≠] s.center) (𝓝 ((MultiplierOrderData.prod m n).unit s.center * s.residue)) := by
  exact Zeta23.OPICA.affine_transport_unit_residue s m B n horder

end AffineTransport

section Counterexamples
open Filter Topology
open scoped BigOperators Matrix

-- OPICA_L4_ANALYTIC_ADDITION_CAN_CANCEL_COMPLETED_JET
theorem consume_analytic_addition_can_cancel_completed_jet :
    AnalyticAt ℂ (fun _ : ℂ => (-1:ℂ)) 0 ∧
      AnalyticAt ℂ (fun z : ℂ => z) 0 ∧
      (∀ z : ℂ, z ≠ 0 → z * (1/z) = 1) ∧
      (1:ℂ) ≠ 0 ∧ (1:ℂ) + (-1:ℂ) = 0 := by
  exact Zeta23.OPICA.analytic_addition_can_cancel_completed_jet

-- OPICA_O1_CONTRAST_CANNOT_RECOVER_SUM
theorem consume_contrast_cannot_recover_sum (d : ℕ) (hd : 0 < d) :
    contrast d (fun _ => 1) = 0 ∧
      ¬ ∃ recovered : (Fin d → ℝ) →ₗ[ℝ] ℝ,
        ∀ v, recovered (contrast d v) = ∑ j, v j := by
  exact Zeta23.OPICA.contrast_cannot_recover_sum d hd

-- OPICA_O2_GRAM_INTEGRAL_NOT_RANK_ONE
theorem consume_gram_integral_not_rank_one :
    linearGram.det = (1:ℝ)/12 ∧ linearGram.rank = 2 ∧ linearGram.rank ≠ 1 := by
  exact Zeta23.OPICA.gram_integral_not_rank_one

-- OPICA_O2_SINGLE_VECTOR_BOUND_NOT_OPERATOR_BOUND
theorem consume_single_vector_bound_not_operator_bound (C : ℝ) :
    ∃ L : Matrix (Fin 2) (Fin 2) ℝ,
      (![1,0] : Fin 2 → ℝ) ⬝ᵥ (L *ᵥ ![1,0]) = 0 ∧
      C < (![0,1] : Fin 2 → ℝ) ⬝ᵥ (L *ᵥ ![0,1]) := by
  exact Zeta23.OPICA.single_vector_bound_not_operator_bound C

-- OPICA_O2_OFFDIAGONAL_MASK_NOT_POSSEMIDEF
theorem consume_offDiagonal_mask_not_posSemidef :
    ¬ Matrix.PosSemidef (!![0,1;1,0] : Matrix (Fin 2) (Fin 2) ℝ) := by
  exact Zeta23.OPICA.offDiagonal_mask_not_posSemidef

-- OPICA_O3_SEVEN_SAMPLES_SIX_COEFFICIENTS_CONSISTENT
theorem consume_seven_samples_six_coefficients_consistent (sample : Fin 7 → ℂ)
    (coeff : Fin 6 → ℂ) :
    ∃ a : Fin 6 → ℂ, ∀ i : Fin 7,
      (∑ j : Fin 6, a j * sample i ^ (j:ℕ)) =
        ∑ j : Fin 6, coeff j * sample i ^ (j:ℕ) := by
  exact Zeta23.OPICA.seven_samples_six_coefficients_consistent sample coeff

-- Additional clause: Zeta23.OPICA.inverse_scale_can_erase_rate
theorem consume_inverse_scale_can_erase_rate (T : HorizonSchedule) :
    (∀ n,0<Real.exp (-(2*T.time n)) ∧ Real.exp (-(2*T.time n))≤1) ∧
      Tendsto (magnitudeRate T (fun n =>Real.exp (2*T.time n))) atTop (𝓝 1) ∧
      SubexpAlong T (fun n =>Real.exp (-(2*T.time n))*Real.exp (2*T.time n)) := by
  exact Zeta23.OPICA.inverse_scale_can_erase_rate T

-- Additional clause: Zeta23.OPICA.negative_scale_can_erase_positive_rate
theorem consume_negative_scale_can_erase_positive_rate (T : HorizonSchedule) :
    Tendsto (positiveRate T (fun n =>Real.exp (2*T.time n))) atTop (𝓝 1) ∧
      Tendsto (positiveRate T (fun n =>-Real.exp (2*T.time n))) atTop (𝓝 0) := by
  exact Zeta23.OPICA.negative_scale_can_erase_positive_rate T

-- Additional clause: Zeta23.OPICA.accumulated_cost_counterexample
theorem consume_accumulated_cost_counterexample :
    Tendsto (fun n =>Real.log 2/(2*integerHorizonSchedule.time n)) atTop (𝓝 0) ∧
      (∀ n : ℕ, Real.log (∏ _i∈Finset.range (n+1),(2:ℝ))/(2*integerHorizonSchedule.time n)=Real.log 2/2) ∧
      0<Real.log 2/2 := by
  exact Zeta23.OPICA.accumulated_cost_counterexample

-- Additional clause: Zeta23.OPICA.high_primitive_does_not_mean_both_high
theorem consume_high_primitive_does_not_mean_both_high :
    7<max (1:ℕ) 11 ∧ ¬(7<(1:ℕ) ∧ 7<(11:ℕ)) := by
  exact Zeta23.OPICA.high_primitive_does_not_mean_both_high

-- Additional clause: Zeta23.OPICA.common_gcd_need_not_be_coprime_to_primitives
theorem consume_common_gcd_need_not_be_coprime_to_primitives :
    Nat.gcd 121 1331=121 ∧ 121/121=1 ∧ 1331/121=11 ∧ Nat.gcd 121 11≠1 := by
  exact Zeta23.OPICA.common_gcd_need_not_be_coprime_to_primitives

end Counterexamples

section ResidueLimits
open Complex Filter Metric Set
open scoped Topology

-- OPICA_L5_RESIDUE_CONTINUOUS_OF_CIRCLE_UNIFORM
theorem consume_residue_continuous_of_circle_uniform (center : ℂ) (radius : ℝ)
    (hr : 0 < radius) (f : ℕ → MeromorphicDiskData center radius)
    (g : MeromorphicDiskData center radius) (error : ℕ → ℝ)
    (hbound : ∀ n z, z ∈ sphere center radius → ‖(f n).field z - g.field z‖ ≤ error n)
    (herror : Tendsto error atTop (𝓝 0)) :
    Tendsto (fun n => (f n).residue) atTop (𝓝 g.residue) := by
  exact Zeta23.OPICA.residue_continuous_of_circle_uniform center radius hr f g error hbound herror

-- OPICA_L5_ESCAPING_TAIL_KEEPS_RESIDUE
theorem consume_escaping_tail_keeps_residue (center : ℂ) (n : ℕ) :
    Tendsto (fun z => (z - center) * escapingTailTransform center n z)
      (𝓝[≠] center) (𝓝 1) := by
  exact Zeta23.OPICA.escaping_tail_keeps_residue center n

-- Additional clause: Zeta23.OPICA.simplePole_residues_continuous_of_circle_uniform
theorem consume_simplePole_residues_continuous_of_circle_uniform (center : ℂ) (radius : ℝ)
    (hr : 0 < radius) (residues : ℕ → ℂ) (residue : ℂ)
    (remainders : ℕ → ℂ → ℂ) (remainder : ℂ → ℂ)
    (hrem : ∀ n, AnalyticOnNhd ℂ (remainders n) (closedBall center radius))
    (hlimit : AnalyticOnNhd ℂ remainder (closedBall center radius))
    (error : ℕ → ℝ)
    (hbound : ∀ n z, z ∈ sphere center radius →
      ‖(residues n / (z-center) + remainders n z) -
        (residue / (z-center) + remainder z)‖ ≤ error n)
    (herror : Tendsto error atTop (𝓝 0)) :
    Tendsto residues atTop (𝓝 residue) := by
  exact Zeta23.OPICA.simplePole_residues_continuous_of_circle_uniform center radius hr residues residue remainders remainder hrem hlimit error hbound herror

-- Additional clause: Zeta23.OPICA.simplePole_circleIntegrable
theorem consume_simplePole_circleIntegrable (center residue : ℂ) (radius : ℝ)
    (hr : 0 < radius) (h : ℂ → ℂ)
    (hh : AnalyticOnNhd ℂ h (closedBall center radius)) :
    CircleIntegrable (fun z => residue / (z-center) + h z) center radius := by
  exact Zeta23.OPICA.simplePole_circleIntegrable center residue radius hr h hh

-- Additional clause: Zeta23.OPICA.escaping_tail_compact_eventually_zero
theorem consume_escaping_tail_compact_eventually_zero (center : ℂ) (bound : ℝ) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ, t ≤ bound → escapingTailPhysical center n t = 0 := by
  exact Zeta23.OPICA.escaping_tail_compact_eventually_zero center bound

-- Additional clause: Zeta23.OPICA.escaping_tail_laplace_formula
theorem consume_escaping_tail_laplace_formula (center z : ℂ) (hz : center.re < z.re) (n : ℕ) :
    (∫ t : ℝ in Ioi (n : ℝ),
      Complex.exp (-z * (t : ℂ)) * Complex.exp (center * (t : ℂ))) =
      escapingTailTransform center n z := by
  exact Zeta23.OPICA.escaping_tail_laplace_formula center z hz n

-- Additional clause: Zeta23.OPICA.escaping_tail_safe_halfPlane_tendsto
theorem consume_escaping_tail_safe_halfPlane_tendsto (center z : ℂ) (hz : center.re < z.re) :
    Tendsto (fun n => escapingTailTransform center n z) atTop (𝓝 0) := by
  exact Zeta23.OPICA.escaping_tail_safe_halfPlane_tendsto center z hz

-- Additional clause: Zeta23.OPICA.escaping_tail_halfPlane_bound
theorem consume_escaping_tail_halfPlane_bound (center z : ℂ) (n : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hz : epsilon ≤ (z - center).re) :
    ‖escapingTailTransform center n z‖ ≤ Real.exp (-(n : ℝ) * epsilon) / epsilon := by
  exact Zeta23.OPICA.escaping_tail_halfPlane_bound center z n epsilon hepsilon hz

-- Additional clause: Zeta23.OPICA.escaping_tail_safe_halfPlane_uniform
theorem consume_escaping_tail_safe_halfPlane_uniform (center : ℂ) (epsilon : ℝ)
    (hepsilon : 0 < epsilon) (tolerance : ℝ) (htol : 0 < tolerance) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℂ, epsilon ≤ (z - center).re →
      ‖escapingTailTransform center n z‖ < tolerance := by
  exact Zeta23.OPICA.escaping_tail_safe_halfPlane_uniform center epsilon hepsilon tolerance htol

-- Additional clause: Zeta23.OPICA.MeromorphicDiskData.circleIntegrable
theorem consume_circleIntegrable {center : ℂ} {radius : ℝ}
    (f : MeromorphicDiskData center radius) (hr : 0 < radius) :
    CircleIntegrable f.field center radius := by
  exact Zeta23.OPICA.MeromorphicDiskData.circleIntegrable f hr

-- Additional clause: Zeta23.OPICA.MeromorphicDiskData.residue_sub_norm_le
theorem consume_residue_sub_norm_le {center : ℂ} {radius : ℝ}
    (f g : MeromorphicDiskData center radius) (hr : 0 < radius) (error : ℝ)
    (hbound : ∀ z ∈ sphere center radius, ‖f.field z-g.field z‖ ≤ error) :
    ‖f.residue-g.residue‖ ≤ radius*error := by
  exact Zeta23.OPICA.MeromorphicDiskData.residue_sub_norm_le f g hr error hbound

-- Additional clause: Zeta23.OPICA.inversePowerMeromorphicDisk_residue_two
theorem consume_inversePowerMeromorphicDisk_residue_two (center : ℂ) (radius : ℝ) :
    (inversePowerMeromorphicDisk center radius 2).residue = 0 := by
  exact Zeta23.OPICA.inversePowerMeromorphicDisk_residue_two center radius

end ResidueLimits

section EnergyRate
open Filter Topology

-- OPICA_E1_LOG_ONE_ADD_POSPART_SUB_LE
theorem consume_log_one_add_posPart_sub_le (a b : ℝ) :
    |Real.log (1 + max a 0) - Real.log (1 + max b 0)| ≤
      Real.log (1 + |a - b|) := by
  exact Zeta23.OPICA.log_one_add_posPart_sub_le a b

-- OPICA_E1_LOG_ONE_ADD_NORM_SUB_LE
theorem consume_log_one_add_norm_sub_le {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    |Real.log (1 + ‖a‖) - Real.log (1 + ‖b‖)| ≤ Real.log (1 + ‖a - b‖) := by
  exact Zeta23.OPICA.log_one_add_norm_sub_le a b

-- OPICA_E2_SUBEXPALONG_ADD
theorem consume_subexpAlong_add {E : Type*} [SeminormedAddCommGroup E] (T : HorizonSchedule)
    {u v : ℕ → E} (hu : SubexpAlong T u) (hv : SubexpAlong T v) :
    SubexpAlong T (u + v) := by
  exact Zeta23.OPICA.subexpAlong_add T hu hv

-- OPICA_E2_SUBEXPALONG_MUL
theorem consume_subexpAlong_mul {𝕜 : Type*} [NormedRing 𝕜] (T : HorizonSchedule)
    {u v : ℕ → 𝕜} (hu : SubexpAlong T u) (hv : SubexpAlong T v) :
    SubexpAlong T (u * v) := by
  exact Zeta23.OPICA.subexpAlong_mul T hu hv

-- OPICA_E2_SUBEXPALONG_CONST_SMUL
theorem consume_subexpAlong_const_smul {𝕜 E : Type*} [NormedField 𝕜]
    [SeminormedAddCommGroup E] [NormedSpace 𝕜 E] (T : HorizonSchedule) (c : 𝕜)
    {u : ℕ → E} (hu : SubexpAlong T u) : SubexpAlong T (c • u) := by
  exact Zeta23.OPICA.subexpAlong_const_smul T c hu

-- OPICA_E2_RATE_CONGR_OF_SUBEXP_ERROR
theorem consume_rate_congr_of_subexp_error {E : Type*} [SeminormedAddCommGroup E]
    (T : HorizonSchedule) (u v : ℕ → E) (h : SubexpAlong T (u - v)) :
    Tendsto (fun n => magnitudeRate T u n - magnitudeRate T v n) atTop (𝓝 0) := by
  exact Zeta23.OPICA.rate_congr_of_subexp_error T u v h

-- OPICA_E2_POSRATE_CONGR_OF_SUBEXP_ERROR
theorem consume_posRate_congr_of_subexp_error (T : HorizonSchedule) (u v : ℕ → ℝ)
    (h : SubexpAlong T (u - v)) :
    Tendsto (fun n => positiveRate T u n - positiveRate T v n) atTop (𝓝 0) := by
  exact Zeta23.OPICA.posRate_congr_of_subexp_error T u v h

-- OPICA_E2_RATE_LIMSUP_LIMINF_CONGR
theorem consume_rate_limsup_liminf_congr {E : Type*} [SeminormedAddCommGroup E]
    (T : HorizonSchedule) (u v : ℕ → E) (h : SubexpAlong T (u-v)) :
    Filter.limsup (fun n => ENNReal.ofReal (magnitudeRate T u n)) atTop =
      Filter.limsup (fun n => ENNReal.ofReal (magnitudeRate T v n)) atTop ∧
    Filter.liminf (fun n => ENNReal.ofReal (magnitudeRate T u n)) atTop =
      Filter.liminf (fun n => ENNReal.ofReal (magnitudeRate T v n)) atTop := by
  exact Zeta23.OPICA.rate_limsup_liminf_congr T u v h

-- OPICA_E3_RATE_CONGR_OF_TEMPERED_SCALE
theorem consume_rate_congr_of_tempered_scale {𝕜 : Type*} [NormedDivisionRing 𝕜]
    (T : HorizonSchedule) (a u : ℕ → 𝕜) (ha : TemperedAlong T a) :
    Tendsto (fun n => magnitudeRate T (a*u) n - magnitudeRate T u n) atTop (𝓝 0) := by
  exact Zeta23.OPICA.rate_congr_of_tempered_scale T a u ha

-- OPICA_E3_POSRATE_CONGR_OF_POSITIVE_TEMPERED_SCALE
theorem consume_posRate_congr_of_positive_tempered_scale (T : HorizonSchedule) (a u : ℕ → ℝ)
    (ha : TemperedAlong T a) (hpos : ∀ n, 0 < a n) :
    Tendsto (fun n => positiveRate T (a*u) n - positiveRate T u n) atTop (𝓝 0) := by
  exact Zeta23.OPICA.posRate_congr_of_positive_tempered_scale T a u ha hpos

-- Additional clause: Zeta23.OPICA.temperedAlong_of_max_inverse_cost
theorem consume_temperedAlong_of_max_inverse_cost {𝕜 : Type*} [NormedDivisionRing 𝕜]
    (T : HorizonSchedule) (a : ℕ → 𝕜) (ha : ∀ n, a n ≠ 0)
    (hc : Tendsto (fun n => Real.log (max ‖a n‖ ‖(a n)⁻¹‖)/(2*T.time n)) atTop (𝓝 0)) :
    TemperedAlong T a := by
  exact Zeta23.OPICA.temperedAlong_of_max_inverse_cost T a ha hc

-- Additional clause: Zeta23.OPICA.eventually_positive_of_positive_rate
theorem consume_eventually_positive_of_positive_rate (T : HorizonSchedule) (u : ℕ → ℝ)
    {θ : ℝ} (hθ : 0 < θ) (h : Tendsto (positiveRate T u) atTop (𝓝 θ)) :
    ∀ᶠ n in atTop, 0 < u n := by
  exact Zeta23.OPICA.eventually_positive_of_positive_rate T u hθ h

-- Additional clause: Zeta23.OPICA.posRate_limsup_liminf_congr
theorem consume_posRate_limsup_liminf_congr (T : HorizonSchedule) (u v : ℕ → ℝ)
    (h : SubexpAlong T (u-v)) :
    Filter.limsup (fun n => ENNReal.ofReal (positiveRate T u n)) atTop =
      Filter.limsup (fun n => ENNReal.ofReal (positiveRate T v n)) atTop ∧
    Filter.liminf (fun n => ENNReal.ofReal (positiveRate T u n)) atTop =
      Filter.liminf (fun n => ENNReal.ofReal (positiveRate T v n)) atTop := by
  exact Zeta23.OPICA.posRate_limsup_liminf_congr T u v h

end EnergyRate

section Composition
open Filter Topology Finset
open scoped BigOperators
variable {K V W X : Type*} [Field K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  [AddCommGroup X] [Module K X]

-- OPICA_E4_AFFINE_CHAIN_EXPANSION
theorem consume_affine_chain_expansion {R : Type*} [CommSemiring R] (a b : ℕ → R) (z : R)
    (N : ℕ) : affineChain a b z N = affineProduct a N * z + affineCorrection a b N := by
  exact Zeta23.OPICA.affine_chain_expansion a b z N

-- OPICA_E4_AFFINE_CHAIN_BUDGET
theorem consume_affine_chain_budget (a b Z : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (hstep : ∀ n, Z (n+1) ≤ a n * Z n + b n) (N : ℕ) :
    Z N ≤ affineProduct a N * Z 0 + affineCorrection a b N := by
  exact Zeta23.OPICA.affine_chain_budget a b Z ha hstep N

-- OPICA_E4_RATE_CONGR_OF_ACCUMULATED_BUDGET
theorem consume_rate_congr_of_accumulated_budget {𝕜 : Type*} [NormedField 𝕜]
    (T : HorizonSchedule) (a b : ℕ → ℕ → 𝕜) (u : ℕ → 𝕜) (depth : ℕ → ℕ)
    (hA : TemperedAlong T (fun n => affineProduct (fun i => a i n) (depth n)))
    (hB : SubexpAlong T (fun n => affineCorrection (fun i => a i n) (fun i => b i n) (depth n))) :
    Tendsto (fun n => magnitudeRate T (fun n => affineChain (fun i => a i n)
      (fun i => b i n) (u n) (depth n)) n - magnitudeRate T u n) atTop (𝓝 0) := by
  exact Zeta23.OPICA.rate_congr_of_accumulated_budget T a b u depth hA hB

-- OPICA_E5_QUIET_COFINAL_RATE_ZERO
theorem consume_quiet_cofinal_rate_zero (T : HorizonSchedule) (E : ℝ → ℝ) (θ : ℝ)
    (hθ : 0 ≤ θ) (hE : ∀ t, 0 ≤ E t)
    (hfull : Tendsto (fun t => Real.log (1+E t)/(2*t)) atTop (𝓝 θ))
    (C b : ℕ → ℝ) (hC : ∀ n, 0 < C n)
    (hb : Tendsto b atTop (𝓝 0))
    (hcost : Tendsto (fun n => Real.log (C n)/(2*T.time n)) atTop (𝓝 0))
    (hquiet : ∀ n, 1+E (T.time n) ≤ C n * Real.exp (2*b n*T.time n)) : θ = 0 := by
  exact Zeta23.OPICA.quiet_cofinal_rate_zero T E θ hθ hE hfull C b hC hb hcost hquiet

-- OPICA_C1_QUOTIENT_MAP_INJECTIVE_IFF
theorem consume_quotient_map_injective_iff (N : Submodule K V) (N' : Submodule K W)
    (f : V →ₗ[K] W) (hf : N ≤ N'.comap f) :
    Function.Injective (N.mapQ N' f hf) ↔ N'.comap f = N := by
  exact Zeta23.OPICA.quotient_map_injective_iff N N' f hf

-- OPICA_C1_FAITHFUL_TRANSFER_COMP
theorem consume_faithful_transfer_comp (N : Submodule K V) (N' : Submodule K W)
    (N'' : Submodule K X) (f : V →ₗ[K] W) (g : W →ₗ[K] X)
    (hf : N ≤ N'.comap f) (hg : N' ≤ N''.comap g)
    (hfi : Function.Injective (N.mapQ N' f hf))
    (hgi : Function.Injective (N'.mapQ N'' g hg)) :
    Function.Injective (N.mapQ N'' (g.comp f) (hf.trans (Submodule.comap_mono hg))) := by
  exact Zeta23.OPICA.faithful_transfer_comp N N' N'' f g hf hg hfi hgi

-- OPICA_C2_OBSTRUCTION_PATH_NONZERO
theorem consume_obstruction_path_nonzero
    (S Ω : ℕ → Type*) (zero : ∀ i, Ω i)
    (admissible : ∀ i, S i → Prop) (obs : ∀ i, S i → Ω i)
    (transition : ∀ i, S i → S (i+1)) (carrier : ∀ i, Ω i → Ω (i+1))
    (preserve : ∀ i s, admissible i s → admissible (i+1) (transition i s))
    (commute : ∀ i s, admissible i s → obs (i+1) (transition i s) = carrier i (obs i s))
    (reflect : ∀ i w, carrier i w = zero (i+1) → w = zero i)
    (states : ∀ i, S i) (hstates : ∀ i, states (i+1) = transition i (states i))
    (ha : admissible 0 (states 0)) (h0 : obs 0 (states 0) ≠ zero 0) (N : ℕ) :
    admissible N (states N) ∧ obs N (states N) ≠ zero N := by
  exact Zeta23.OPICA.obstruction_path_nonzero S Ω zero admissible obs transition carrier preserve commute reflect states hstates ha h0 N

-- OPICA_C2_IMPLICATION_PATH_NONZERO
theorem consume_implication_path_nonzero (S Ω : ℕ → Type*) (zero : ∀ i, Ω i)
    (obs : ∀ i, S i → Ω i) (transition : ∀ i, S i → S (i+1))
    (edge : ∀ i s, obs i s ≠ zero i → obs (i+1) (transition i s) ≠ zero (i+1))
    (states : ∀ i, S i) (hstates : ∀ i, states (i+1) = transition i (states i))
    (h0 : obs 0 (states 0) ≠ zero 0) (N : ℕ) : obs N (states N) ≠ zero N := by
  exact Zeta23.OPICA.implication_path_nonzero S Ω zero obs transition edge states hstates h0 N

-- Additional clause: Zeta23.OPICA.finite_affine_chain_rate
theorem consume_finite_affine_chain_rate {𝕜 : Type*} [NormedField 𝕜]
    (T : HorizonSchedule) (a b : ℕ → ℕ → 𝕜) (u : ℕ → 𝕜)
    (ha : ∀ i, TemperedAlong T (a i)) (hb : ∀ i, SubexpAlong T (b i)) (N : ℕ) :
    Tendsto (fun n => magnitudeRate T (fun n => affineChain (fun i => a i n)
      (fun i => b i n) (u n) N) n - magnitudeRate T u n) atTop (𝓝 0) := by
  exact Zeta23.OPICA.finite_affine_chain_rate T a b u ha hb N

-- Additional clause: Zeta23.OPICA.posRate_congr_of_accumulated_budget
theorem consume_posRate_congr_of_accumulated_budget
    (T : HorizonSchedule) (a b : ℕ → ℕ → ℝ) (u : ℕ → ℝ) (depth : ℕ → ℕ)
    (hA : TemperedAlong T (fun n => affineProduct (fun i => a i n) (depth n)))
    (hpos : ∀ n, 0 < affineProduct (fun i => a i n) (depth n))
    (hB : SubexpAlong T (fun n => affineCorrection (fun i => a i n) (fun i => b i n) (depth n))) :
    Tendsto (fun n => positiveRate T (fun n => affineChain (fun i => a i n)
      (fun i => b i n) (u n) (depth n)) n - positiveRate T u n) atTop (𝓝 0) := by
  exact Zeta23.OPICA.posRate_congr_of_accumulated_budget T a b u depth hA hpos hB

-- Additional clause: Zeta23.OPICA.finite_affine_chain_posRate
theorem consume_finite_affine_chain_posRate
    (T : HorizonSchedule) (a b : ℕ → ℕ → ℝ) (u : ℕ → ℝ)
    (ha : ∀ i, TemperedAlong T (a i)) (hpos : ∀ i n, 0 < a i n)
    (hb : ∀ i, SubexpAlong T (b i)) (N : ℕ) :
    Tendsto (fun n => positiveRate T (fun n => affineChain (fun i => a i n)
      (fun i => b i n) (u n) N) n - positiveRate T u n) atTop (𝓝 0) := by
  exact Zeta23.OPICA.finite_affine_chain_posRate T a b u ha hpos hb N

end Composition

section DivisorBounds
open Finset
open scoped BigOperators

-- OPICA_A1_DIVISOR_COUNT_SUBMULTIPLICATIVE
theorem consume_divisor_count_submultiplicative (order a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    divisorCount order (a*b) ≤ divisorCount order a * divisorCount order b := by
  exact Zeta23.OPICA.divisor_count_submultiplicative order a b ha hb

-- OPICA_A1_DIVISOR_COUNT_SQUARE_LE
theorem consume_divisor_count_square_le (order n : ℕ) (hn : 0 < n) :
    divisorCount order n ^ 2 ≤ divisorCount (order*order) n := by
  exact Zeta23.OPICA.divisor_count_square_le order n hn

-- OPICA_A1_DIVISOR_COUNT_HARMONIC_SUM_LE
theorem consume_divisor_count_harmonic_sum_le (order : ℕ) (X : ℝ) (hX : 1 ≤ X) :
    (∑ n ∈ Icc 1 ⌊X⌋₊, (divisorCount order n : ℝ)^2/(n:ℝ)) ≤
      (1+Real.log X)^(order*order) := by
  exact Zeta23.OPICA.divisor_count_harmonic_sum_le order X hX

-- OPICA_A1_DIVISOR_COUNT_SQRT_SUM_LE
theorem consume_divisor_count_sqrt_sum_le (order : ℕ) (horder : 0<order) (X : ℝ) (hX : 1≤X) :
    (∑ n ∈ Icc 1 ⌊X⌋₊,(divisorCount order n : ℝ)/Real.sqrt (n:ℝ)) ≤
      2*Real.sqrt X*(1+Real.log X)^(order-1) := by
  exact Zeta23.OPICA.divisor_count_sqrt_sum_le order horder X hX

end DivisorBounds

section PrimitiveMasks
open Finset Set MeasureTheory
open scoped BigOperators

-- OPICA_A2_PRIMITIVE_MASK_PARTITION
theorem consume_primitive_mask_partition (U : BoundedCausalDrive) (x y : ℕ → ℝ)
    (B : ℝ → ℝ) (H T : ℝ)
    (hlow : IntegrableOn (finiteLowPair U (driveIndexBound T) x y B) (Icc H T))
    (hhigh : IntegrableOn (finiteHighPair U (driveIndexBound T) x y B) (Icc H T)) :
    (∫ t in Icc H T, finiteHighPair U (driveIndexBound T) x y B t) =
      (∫ t in Icc H T, (∑' d : ℕ, x d * translatedDrive U d t) *
        (∑' e : ℕ, y e * translatedDrive U e t)) -
      ∫ t in Icc H T, finiteLowPair U (driveIndexBound T) x y B t := by
  exact Zeta23.OPICA.primitive_mask_partition U x y B H T hlow hhigh

-- Additional clause: Zeta23.OPICA.drive_sum_eq_finite
theorem consume_drive_sum_eq_finite (U : BoundedCausalDrive) (x : ℕ → ℝ) {T t : ℝ}
    (ht : t ≤ T) :
    (∑' d : ℕ, x d * translatedDrive U d t) =
      ∑ d ∈ range (driveIndexBound T + 1), x d * translatedDrive U d t := by
  exact Zeta23.OPICA.drive_sum_eq_finite U x ht

-- Additional clause: Zeta23.OPICA.lowPrimitiveMask_measurable
theorem consume_lowPrimitiveMask_measurable {B : ℝ → ℝ} (hB : Measurable B) (d e : ℕ) :
    Measurable (fun t => lowPrimitiveMask (B t) d e) := by
  exact Zeta23.OPICA.lowPrimitiveMask_measurable hB d e

-- Additional clause: Zeta23.OPICA.lowPrimitiveMask_diagonal
theorem consume_lowPrimitiveMask_diagonal {d : ℕ} (hd : 0 < d) {B : ℝ} (hB : 1 ≤ B) :
    lowPrimitiveMask B d d = 1 := by
  exact Zeta23.OPICA.lowPrimitiveMask_diagonal hd hB

end PrimitiveMasks

section DivisorMask
open Set MeasureTheory Filter
open scoped Topology
open Finset
open scoped BigOperators

-- OPICA_A2_LOW_PRIMITIVE_BILINEAR_BOUND
theorem consume_low_primitive_bilinear_bound (U : BoundedCausalDrive) (order : ℕ) (horder : 0<order)
    (x y : ℕ→ℝ) (Ax Ay Bmax H T : ℝ) (hAx : 0≤Ax) (hAy : 0≤Ay)
    (hBmax : 1≤Bmax) (hT : 0≤T) (hHT : H≤T)
    (hx : ∀ d,0<d→|x d|≤Ax*(divisorCount order d:ℝ))
    (hy : ∀ d,0<d→|y d|≤Ay*(divisorCount order d:ℝ))
    (B : ℝ→ℝ) (hB : ∀ t∈Icc H T,B t≤Bmax) :
    |∫ t in Icc H T,finiteLowPair U (driveIndexBound T) x y B t| ≤
      Ax*Ay*(4*(T-H)*U.bound^2*Bmax*(1+Real.log Bmax)^(2*order-2)*(1+T)^(order*order)) := by
  exact Zeta23.OPICA.low_primitive_bilinear_bound U order horder x y Ax Ay Bmax H T hAx hAy hBmax hT hHT hx hy B hB

-- OPICA_A2_MASKED_TYPEI_MIXED_BOUND
theorem consume_masked_typeI_mixed_bound (U : BoundedCausalDrive) (order : ℕ) (horder : 0<order)
    (s c : ℕ→ℝ) (A eI Bmax H T : ℝ) (hA : 0≤A) (heI : 0≤eI)
    (hBmax : 1≤Bmax) (hT : 0≤T) (hHT : H≤T)
    (hs : ∀ d,0<d→|s d|≤A*(divisorCount order d:ℝ))
    (hc : ∀ d,0<d→|c d|≤(divisorCount order d:ℝ))
    (hfull : ∀ d,0<d→|s d+c d|≤1)
    (herror : ∀ t∈Icc H T,|finiteDriveField U (driveIndexBound T) s t|≤eI)
    (B : ℝ→ℝ) (hB : ∀ t∈Icc H T,B t≤Bmax)
    (hL : IntegrableOn (finiteLowPair U (driveIndexBound T) s c B) (Icc H T))
    (hQ : IntegrableOn (finiteHighPair U (driveIndexBound T) s c B) (Icc H T)) :
    |∫ t in Icc H T,finiteHighPair U (driveIndexBound T) s c B t| ≤
      (T-H)*eI*(2*U.bound*Real.exp (T/2)+eI)+A*lowMaskCost U order Bmax H T := by
  exact Zeta23.OPICA.masked_typeI_mixed_bound U order horder s c A eI Bmax H T hA heI hBmax hT hHT hs hc hfull herror B hB hL hQ

-- OPICA_A2_MASKED_TYPEI_SQUARE_BOUND
theorem consume_masked_typeI_square_bound (U : BoundedCausalDrive) (order : ℕ) (horder : 0<order)
    (s : ℕ→ℝ) (A eI Bmax H T : ℝ) (hA : 0≤A) (heI : 0≤eI)
    (hBmax : 1≤Bmax) (hT : 0≤T) (hHT : H≤T)
    (hs : ∀ d,0<d→|s d|≤A*(divisorCount order d:ℝ))
    (herror : ∀ t∈Icc H T,|finiteDriveField U (driveIndexBound T) s t|≤eI)
    (B : ℝ→ℝ) (hB : ∀ t∈Icc H T,B t≤Bmax)
    (hL : IntegrableOn (finiteLowPair U (driveIndexBound T) s s B) (Icc H T))
    (hQ : IntegrableOn (finiteHighPair U (driveIndexBound T) s s B) (Icc H T)) :
    |∫ t in Icc H T,finiteHighPair U (driveIndexBound T) s s B t| ≤
      (T-H)*eI^2+A^2*lowMaskCost U order Bmax H T := by
  exact Zeta23.OPICA.masked_typeI_square_bound U order horder s A eI Bmax H T hA heI hBmax hT hHT hs herror B hB hL hQ

-- OPICA_A2_BALANCED_ENERGY_COMPARISON
theorem consume_balanced_energy_comparison (U : BoundedCausalDrive) (order : ℕ) (horder : 0<order)
    (s c : ℕ→ℝ) (eI Bmax H T : ℝ) (heI : 0≤eI)
    (hBmax : 1≤Bmax) (hT : 0≤T) (hHT : H≤T)
    (hc : ∀ d,0<d→|c d|≤(divisorCount order d:ℝ))
    (hfull : ∀ d,0<d→|s d+c d|≤1)
    (herror : ∀ t∈Icc H T,|finiteDriveField U (driveIndexBound T) s t|≤eI)
    (B : ℝ→ℝ) (hB : ∀ t∈Icc H T,B t≤Bmax)
    (hL : IntegrableOn (finiteLowPair U (driveIndexBound T) c c B) (Icc H T))
    (hQ : IntegrableOn (finiteHighPair U (driveIndexBound T) c c B) (Icc H T)) :
    |(∫ t in Icc H T,(finiteDriveField U (driveIndexBound T) (s+c) t)^2)-
      (∫ t in Icc H T,finiteHighPair U (driveIndexBound T) c c B t)| ≤
      lowMaskCost U order Bmax H T+4*(T-H)*eI*U.bound*Real.exp (T/2)+(T-H)*eI^2 := by
  exact Zeta23.OPICA.balanced_energy_comparison U order horder s c eI Bmax H T heI hBmax hT hHT hc hfull herror B hB hL hQ

-- OPICA_A3_MASK_REGROUPING_DIFFERENCE
theorem consume_mask_regrouping_difference
    (U V : BoundedCausalDrive) (N M : ℕ) (x y : ℕ → ℝ) (B C : ℝ → ℝ)
    (I : Set ℝ) (hI : MeasurableSet I)
    (hfield : ∀ t ∈ I, finiteDriveField U N x t = finiteDriveField V M y t)
    (hUL : IntegrableOn (finiteLowPair U N x x B) I)
    (hUH : IntegrableOn (finiteHighPair U N x x B) I)
    (hVL : IntegrableOn (finiteLowPair V M y y C) I)
    (hVH : IntegrableOn (finiteHighPair V M y y C) I) :
    highPairObservation U N x B I - highPairObservation V M y C I =
      lowPairObservation V M y C I - lowPairObservation U N x B I := by
  exact Zeta23.OPICA.mask_regrouping_difference U V N M x y B C I hI hfield hUL hUH hVL hVH

-- OPICA_A3_REGROUPED_MASK_RATE_CONGR
theorem consume_regrouped_mask_rate_congr
    (T : HorizonSchedule) (U V : BoundedCausalDrive) (N M : ℕ → ℕ)
    (x y : ℕ → ℕ → ℝ) (B C : ℕ → ℝ → ℝ) (H : ℕ → ℝ)
    (hfield : ∀ n t, t ∈ Icc (H n) (T.time n) →
      finiteDriveField U (N n) (x n) t = finiteDriveField V (M n) (y n) t)
    (hUL : ∀ n, IntegrableOn (finiteLowPair U (N n) (x n) (x n) (B n))
      (Icc (H n) (T.time n)))
    (hUH : ∀ n, IntegrableOn (finiteHighPair U (N n) (x n) (x n) (B n))
      (Icc (H n) (T.time n)))
    (hVL : ∀ n, IntegrableOn (finiteLowPair V (M n) (y n) (y n) (C n))
      (Icc (H n) (T.time n)))
    (hVH : ∀ n, IntegrableOn (finiteHighPair V (M n) (y n) (y n) (C n))
      (Icc (H n) (T.time n)))
    (hUbudget : SubexpAlong T (fun n =>
      lowPairObservation U (N n) (x n) (B n) (Icc (H n) (T.time n))))
    (hVbudget : SubexpAlong T (fun n =>
      lowPairObservation V (M n) (y n) (C n) (Icc (H n) (T.time n)))) :
    Tendsto (fun n =>
      magnitudeRate T (fun k => highPairObservation U (N k) (x k) (B k)
        (Icc (H k) (T.time k))) n -
      magnitudeRate T (fun k => highPairObservation V (M k) (y k) (C k)
        (Icc (H k) (T.time k))) n) atTop (𝓝 0) ∧
    Tendsto (fun n =>
      positiveRate T (fun k => highPairObservation U (N k) (x k) (B k)
        (Icc (H k) (T.time k))) n -
      positiveRate T (fun k => highPairObservation V (M k) (y k) (C k)
        (Icc (H k) (T.time k))) n) atTop (𝓝 0) := by
  exact Zeta23.OPICA.regrouped_mask_rate_congr T U V N M x y B C H hfield hUL hUH hVL hVH hUbudget hVbudget

-- Additional clause: Zeta23.OPICA.finiteLowPair_measurable
theorem consume_finiteLowPair_measurable (U : BoundedCausalDrive) (N : ℕ) (x y : ℕ→ℝ)
    (B : ℝ→ℝ) (hB : Measurable B) : Measurable (finiteLowPair U N x y B) := by
  exact Zeta23.OPICA.finiteLowPair_measurable U N x y B hB

-- Additional clause: Zeta23.OPICA.finiteLowPair_integrableOn
theorem consume_finiteLowPair_integrableOn (U : BoundedCausalDrive) (order : ℕ) (horder : 0<order)
    (x y : ℕ→ℝ) (Ax Ay Bmax H T : ℝ) (hAx : 0≤Ax) (hAy : 0≤Ay)
    (hBmax : 1≤Bmax) (hT : 0≤T)
    (hx : ∀ d,0<d→|x d|≤Ax*(divisorCount order d:ℝ))
    (hy : ∀ d,0<d→|y d|≤Ay*(divisorCount order d:ℝ))
    (B : ℝ→ℝ) (hBm : Measurable B) (hB : ∀ t∈Icc H T,B t≤Bmax) :
    IntegrableOn (finiteLowPair U (driveIndexBound T) x y B) (Icc H T) := by
  exact Zeta23.OPICA.finiteLowPair_integrableOn U order horder x y Ax Ay Bmax H T hAx hAy hBmax hT hx hy B hBm hB

-- Additional clause: Zeta23.OPICA.finiteHighPair_integrableOn
theorem consume_finiteHighPair_integrableOn (U : BoundedCausalDrive) (N : ℕ) (x y : ℕ→ℝ)
    (B : ℝ→ℝ) (H T : ℝ)
    (hL : IntegrableOn (finiteLowPair U N x y B) (Icc H T)) :
    IntegrableOn (finiteHighPair U N x y B) (Icc H T) := by
  exact Zeta23.OPICA.finiteHighPair_integrableOn U N x y B H T hL

end DivisorMask

section WeightedLaplace
open Set MeasureTheory Filter
open scoped Topology
open Zeta23.CCM

-- OPICA_B1_LAPLACE_HOLOMORPHIC_OF_WEIGHTED_L2
theorem consume_laplace_holomorphic_of_weighted_L2 (f : WeightedL2Data) (z : ℂ)
    (hz : f.epsilon < z.re) : AnalyticAt ℂ (weightedLaplace f) z := by
  exact Zeta23.OPICA.laplace_holomorphic_of_weighted_L2 f z hz

-- OPICA_B1_LAPLACE_ITERATEDDERIV_BOUND_OF_WEIGHTED_L2
theorem consume_laplace_iteratedDeriv_bound_of_weighted_L2 (f : WeightedL2Data) (z : ℂ)
    (hz : f.epsilon < z.re) (j : ℕ) :
    ‖iteratedDeriv j (weightedLaplace f) z‖ ≤ ‖f.causalVector‖ *
      Real.sqrt ((2*j).factorial / (2*(z.re-f.epsilon))^(2*j+1)) := by
  exact Zeta23.OPICA.laplace_iteratedDeriv_bound_of_weighted_L2 f z hz j

-- OPICA_B1_NO_VISIBLE_POLE_OF_WEIGHTED_L2
theorem consume_no_visible_pole_of_weighted_L2 (f : WeightedL2Data) (M : ℂ → ℂ)
    (D O : Set ℂ) (hD : IsPreconnected D) (hM : MeromorphicOn M D)
    (hhalf : ∀ z ∈ D, f.epsilon < z.re) (hO : IsOpen O) (hOD : O ⊆ D)
    (hOnonempty : O.Nonempty) (hsource : EqOn M (weightedLaplace f) O) :
    ∀ z ∈ D, 0 ≤ meromorphicOrderAt M z := by
  exact Zeta23.OPICA.no_visible_pole_of_weighted_L2 f M D O hD hM hhalf hO hOD hOnonempty hsource

-- Additional clause: Zeta23.OPICA.weightedLaplace_eq_causalMoment
theorem consume_weightedLaplace_eq_causalMoment (f : WeightedL2Data) (z : ℂ) :
    weightedLaplace f z = nativeCausalLaplaceMoment (z - (f.epsilon : ℂ)) 0
      (f.causalVector : NativeCompletionL2) := by
  exact Zeta23.OPICA.weightedLaplace_eq_causalMoment f z

-- Additional clause: Zeta23.OPICA.weightedLaplace_iteratedDeriv
theorem consume_weightedLaplace_iteratedDeriv (f : WeightedL2Data) (z : ℂ)
    (hz : f.epsilon < z.re) (j : ℕ) :
    iteratedDeriv j (weightedLaplace f) z = (-1 : ℂ)^j *
      nativeCausalLaplaceMoment (z - (f.epsilon : ℂ)) j
        (f.causalVector : NativeCompletionL2) := by
  exact Zeta23.OPICA.weightedLaplace_iteratedDeriv f z hz j

-- Additional clause: Zeta23.OPICA.exponentialPolynomial_L2_norm
theorem consume_exponentialPolynomial_L2_norm (w : ℂ) (hw : 0 < w.re) (j : ℕ) :
    ‖nativeCausalExponentialWitness w hw j‖ =
      Real.sqrt ((2*j).factorial / (2*w.re)^(2*j+1)) := by
  exact Zeta23.OPICA.exponentialPolynomial_L2_norm w hw j

end WeightedLaplace

section RangeSeparation
open Set Metric
variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]

-- OPICA_B2_RANGE_DISTANCE_OF_ANNIHILATOR
theorem consume_range_distance_of_annihilator (A : E →L[𝕜] F) (l : F →L[𝕜] 𝕜)
    (h : ∀ x, l (A x) = 0) {Y : F} (hY : l Y ≠ 0) :
    0 < ‖l Y‖ / ‖l‖ ∧
      ‖l Y‖ / ‖l‖ ≤ infDist Y (closure (Set.range A)) := by
  exact Zeta23.OPICA.range_distance_of_annihilator A l h hY

-- OPICA_B2_NOT_MEM_RANGECLOSURE_OF_ANNIHILATOR
theorem consume_not_mem_rangeClosure_of_annihilator (A : E →L[𝕜] F) (l : F →L[𝕜] 𝕜)
    (h : ∀ x, l (A x) = 0) {Y : F} (hY : l Y ≠ 0) :
    Y ∉ closure (Set.range A) := by
  exact Zeta23.OPICA.not_mem_rangeClosure_of_annihilator A l h hY

end RangeSeparation

section ObservationCompatibility
open scoped ComplexOrder
open scoped InnerProductSpace
open ComplexConjugate
open Metric
variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]
variable {d n : ℕ}
local notation "Input" => EuclideanSpace ℂ (Fin d)
local notation "Output" => EuclideanSpace ℂ (Fin n)

-- OPICA_O1_OBSERVATION_FACTORS_IFF_KER_LE
theorem consume_observation_factors_iff_ker_le (P : V →ₗ[K] W) (l : V →ₗ[K] K) :
    (∃ recovered : P.range →ₗ[K] K, l = recovered.comp P.rangeRestrict) ↔
      P.ker ≤ l.ker := by
  exact Zeta23.OPICA.observation_factors_iff_ker_le P l

-- OPICA_O2_GRAM_INTEGRAL_POSSEMIDEF
theorem consume_gram_integral_posSemidef {A I 𝕜 : Type*} [RCLike 𝕜] [MeasurableSpace A] [Fintype I]
    (μ : MeasureTheory.Measure A) (ψ : I → MeasureTheory.Lp 𝕜 2 μ) :
    Matrix.PosSemidef (fun i j => ∫ t, inner 𝕜 (ψ i t) (ψ j t) ∂μ) := by
  exact Zeta23.OPICA.gram_integral_posSemidef μ ψ

-- OPICA_O3_INCOMPATIBLE_IFF_LEFT_ANNIHILATOR
theorem consume_incompatible_iff_left_annihilator (B : Input →L[ℂ] Output) (b : Output) :
    b ∉ B.range ↔ ∃ y : Output, B.adjoint y = 0 ∧ ⟪y, b⟫_ℂ ≠ 0 := by
  exact Zeta23.OPICA.incompatible_iff_left_annihilator B b

-- OPICA_O3_RANGE_DISTANCE_EQ_ANNIHILATOR_SUP
theorem consume_range_distance_eq_annihilator_sup (B : Input →L[ℂ] Output) (b : Output) :
    infDist b (B.range : Set Output) =
      sSup {q : ℝ | ∃ y : Output, B.adjoint y = 0 ∧ ‖y‖ ≤ 1 ∧ q = ‖⟪y,b⟫_ℂ‖} := by
  exact Zeta23.OPICA.range_distance_eq_annihilator_sup B b

-- OPICA_O4_COMPATIBILITY_UNDER_INVERTIBLE_LEFT_MAP
theorem consume_compatibility_under_invertible_left_map {X : Type*} [AddCommGroup X] [Module K X]
    (B : V →ₗ[K] W) (S : W ≃ₗ[K] X) (b : W) :
    {v | B v = b} = {v | S (B v) = S b} := by
  exact Zeta23.OPICA.compatibility_under_invertible_left_map B S b

-- OPICA_O4_SOLUTIONS_PRESERVED_UNDER_LEFT_MAP
theorem consume_solutions_preserved_under_left_map {X : Type*} [AddCommGroup X] [Module K X]
    (B : V →ₗ[K] W) (S : W →ₗ[K] X) (b : W) :
    {v | B v = b} ⊆ {v | (S.comp B) v = S b} := by
  exact Zeta23.OPICA.solutions_preserved_under_left_map B S b

end ObservationCompatibility

section SignedHeatSeparator
open Set MeasureTheory Filter
open scoped SchwartzMap FourierTransform Convolution Topology

-- OPICA_H1_SIGNED_SHARP_GAP_SEPARATOR
theorem consume_signed_sharp_gap_separator (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) (hself : ν.FourierSelfdual hν)
    (hgap : ν.HasUnitGap) (hoff : ν.OffLatticeNonnegative) :
    ν.positive = 0 ∧ ν.negative = 0 := by
  exact Zeta23.OPICA.signed_sharp_gap_separator ν hν hself hgap hoff

-- OPICA_H2_SIGNED_GAP_NEGATIVE_MASS_BUDGET
theorem consume_signed_gap_negative_mass_budget (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) (hself : ν.FourierSelfdual hν) (hgap : ν.HasUnitGap)
    {R d : ℝ} (hR : 1 ≤ R) (hd : 0 < d) (hdhalf : d ≤ 1/2) :
    (4*d^2 / (Real.pi^2*R^2)) * ν.positive.real (signedBudgetRegion R d) ≤
        ∫ x in integerLatticeᶜ, sincSquared x ∂ν.negative ∧
      ENNReal.ofReal ((4*d^2 / (Real.pi^2*R^2)) *
        ν.positive.real (signedBudgetRegion R d)) ≤ ν.negative integerLatticeᶜ := by
  exact Zeta23.OPICA.signed_gap_negative_mass_budget ν hν hself hgap hR hd hdhalf

-- Additional clause: Zeta23.OPICA.signed_sinc_triangle_pairing
theorem consume_signed_sinc_triangle_pairing (ν : LocallyFiniteSignedMeasure)
    (hν : ν.HasLinearGrowth) (hself : ν.FourierSelfdual hν) :
    ν.integral sincSquared = ν.integral unitTriangle := by
  exact Zeta23.OPICA.signed_sinc_triangle_pairing ν hν hself

-- Additional clause: Zeta23.OPICA.singleton_zero_of_unit_gap
theorem consume_singleton_zero_of_unit_gap (μ : Measure ℝ)
    (hgap : μ (Ioo (-1) 1) = 0) : μ {0} = 0 := by
  exact Zeta23.OPICA.singleton_zero_of_unit_gap μ hgap

-- Additional clause: Zeta23.OPICA.lattice_support_of_sincSquared_integral_zero
theorem consume_lattice_support_of_sincSquared_integral_zero (μ : Measure ℝ)
    [IsLocallyFiniteMeasure μ] (hμ : LinearMassGrowth μ)
    (hzero : (∫ x, sincSquared x ∂μ) = 0) : μ integerLatticeᶜ = 0 := by
  exact Zeta23.OPICA.lattice_support_of_sincSquared_integral_zero μ hμ hzero

-- Additional clause: Zeta23.OPICA.LocallyFiniteSignedMeasure.integerTranslate_pairing
theorem consume_integerTranslate_pairing
    (ν : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth)
    (hself : ν.FourierSelfdual hν)
    (hpos : ν.positive integerLatticeᶜ = 0) (hneg : ν.negative integerLatticeᶜ = 0)
    (test : SchwartzMap ℝ ℂ) (k : ℤ) :
    ν.distributionOfLinearGrowth hν (test.compSubConstCLM ℂ (k : ℝ)) =
      ν.distributionOfLinearGrowth hν test := by
  exact Zeta23.OPICA.LocallyFiniteSignedMeasure.integerTranslate_pairing ν hν hself hpos hneg test k

end SignedHeatSeparator

section Involution

variable {𝕜 V : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]

-- OPICA_H3_COMMUTATOR_ANTI_INVARIANT
theorem consume_commutator_anti_invariant (P F : V →ₗ[𝕜] V)
    (hF : Function.Involutive F) {v : V} (hv : F v = v) :
    F (involutionCommutator P F v) = -involutionCommutator P F v := by
  exact Zeta23.OPICA.commutator_anti_invariant P F hF hv

-- OPICA_H3_COMMUTATOR_SELFDUAL_PROJECTION_ZERO
theorem consume_commutator_selfdual_projection_zero (P F : V →ₗ[𝕜] V)
    (hF : Function.Involutive F) {v : V} (hv : F v = v) :
    involutionSelfdualProjection F (involutionCommutator P F v) = 0 := by
  exact Zeta23.OPICA.commutator_selfdual_projection_zero P F hF hv

end Involution

section FejerCompletion
open Filter Set MeasureTheory
open scoped Topology
open Zeta23.CCM

-- OPICA_H4_FEJER_FLOOR_FORMULA
theorem consume_fejer_floor_formula {t : ℝ} (ht : 0 ≤ t) :
    fejerLatticeKernel t =
      (2 * (⌊Real.exp t⌋₊ : ℝ) + 1) * Real.exp (-(t / 2)) -
        (⌊Real.exp t⌋₊ : ℝ) * ((⌊Real.exp t⌋₊ : ℝ) + 1) *
          Real.exp (-(3 * t / 2)) - Real.exp (t / 2) := by
  exact Zeta23.OPICA.fejer_floor_formula ht

-- OPICA_H4_FEJER_NATIVECOMPLETION_POINTWISE
theorem consume_fejer_nativeCompletion_pointwise {t : ℝ} (ht : 0 ≤ t) :
    fejerLatticeKernel t =
        (expFloorRemainder t / (⌊Real.exp t⌋₊ : ℝ)) *
          Zeta23.CCM.nativePositiveCompletion t ∧
      fejerLatticeKernel t + Zeta23.CCM.nativePositiveCompletion t =
        (1 - expFloorRemainder t) * Real.exp (-(t / 2)) ∧
      0 ≤ fejerLatticeKernel t ∧
      fejerLatticeKernel t ≤ (1 / 4 : ℝ) * Real.exp (-(3 * t / 2)) := by
  exact Zeta23.OPICA.fejer_nativeCompletion_pointwise ht

-- OPICA_H4_FEJER_COMPLETION_AFFINE_IDENTITY
theorem consume_fejer_completion_affine_identity {w : ℂ} (hw : -(1 / 2 : ℝ) < w.re) :
    nativePositiveCompletionLaplace w =
      (1 / 2 : ℂ) * (w - 1 / 2) * fejerLaplace w + 1 / (2 * (w + 1 / 2)) := by
  exact Zeta23.OPICA.fejer_completion_affine_identity hw

-- OPICA_H4_FEJER_LOGINTEGER_ONESIDEDDERIVATIVES
theorem consume_fejer_logInteger_oneSidedDerivatives {n : ℕ} (hn : 2 ≤ n) :
    HasDerivWithinAt fejerLatticeKernel (-(1 / Real.sqrt (n : ℝ)))
        (Set.Iic (Real.log (n : ℝ))) (Real.log (n : ℝ)) ∧
      HasDerivWithinAt fejerLatticeKernel (1 / Real.sqrt (n : ℝ))
        (Set.Ici (Real.log (n : ℝ))) (Real.log (n : ℝ)) := by
  exact Zeta23.OPICA.fejer_logInteger_oneSidedDerivatives hn

-- Additional clause: Zeta23.OPICA.fejerLattice_hasSum
theorem consume_fejerLattice_hasSum (t : ℝ) :
    HasSum (fun n : ℕ => sincSquared (((n + 1 : ℕ) : ℝ) * Real.exp t))
      (expFloorRemainder t * (1 - expFloorRemainder t) / (2 * Real.exp t ^ 2)) := by
  exact Zeta23.OPICA.fejerLattice_hasSum t

-- Additional clause: Zeta23.OPICA.fejerLaplace_analyticAt
theorem consume_fejerLaplace_analyticAt {w : ℂ} (hw : -(1 / 2 : ℝ) < w.re) :
    AnalyticAt ℂ fejerLaplace w := by
  exact Zeta23.OPICA.fejerLaplace_analyticAt hw

-- Additional clause: Zeta23.OPICA.fejerLaplace_analyticAt_fullStrip
theorem consume_fejerLaplace_analyticAt_fullStrip {w : ℂ} (hw : -(3 / 2 : ℝ) < w.re) :
    AnalyticAt ℂ fejerLaplace w := by
  exact Zeta23.OPICA.fejerLaplace_analyticAt_fullStrip hw

end FejerCompletion

section NativeJetAdapter
open Complex Set MeasureTheory Filter
open scoped Topology
open Zeta23.ExceptionalZero Zeta23.CCM

-- OPICA_NATIVE_NATIVE_COMPLETED_INPUT_OBSTRUCTION_ORDER
theorem consume_native_completed_input_obstruction_order
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    analyticOrderAt
      (fun z => nativeCausalLaplaceMoment z 0
        (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le : NativeCompletionL2))
      (nativeZeroJetParameter rho) = (zeroMult (rho : ℂ) - 1 : ℕ) := by
  exact Zeta23.OPICA.native_completed_input_obstruction_order rho hoff

-- OPICA_NATIVE_NATIVE_COMPLETED_INPUT_OBSTRUCTION_JET
theorem consume_native_completed_input_obstruction_jet
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    inner ℂ (nativeZeroJetAdjointWitness rho hoff)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho hoff).le) =
      (-1 : ℂ) ^ zeroMult (rho : ℂ) *
        nativeCompletionRationalMultiplier ((nativeZeroJetRightZero rho : ℂ) - 1 / 2) *
        nativeOriginalSourceLaplace ((nativeZeroJetRightZero rho : ℂ) - 1 / 2) *
        iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta (nativeZeroJetRightZero rho : ℂ) := by
  exact Zeta23.OPICA.native_completed_input_obstruction_jet rho hoff

-- OPICA_NATIVE_NATIVE_COMPLETED_INPUT_OBSTRUCTION_NE_ZERO
theorem consume_native_completed_input_obstruction_ne_zero
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    inner ℂ (nativeZeroJetAdjointWitness rho hoff)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho hoff).le) ≠ 0 := by
  exact Zeta23.OPICA.native_completed_input_obstruction_ne_zero rho hoff

-- OPICA_NATIVE_NATIVE_RANGE_DISTANCE_LOWER
theorem consume_native_range_distance_lower
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
  exact Zeta23.OPICA.native_range_distance_lower rho hoff

-- OPICA_NATIVE_STEP123_OUTPUT_OPICA_VIEW_CORRECT
theorem consume_step123_output_opica_view_correct {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late) :
    (step123OpicaView out).source = nativeOriginalIntegerDrive ∧
    (step123OpicaView out).field = nativeOriginalPrimeField ∧
    (step123OpicaView out).input = nativeCompletedInput ∧
    Step123SameStateFieldRecord out.generated.native ∧
    GeneratedStep123RangeObstruction rho out.generated.offLine := by
  exact Zeta23.OPICA.step123_output_opica_view_correct out

-- OPICA_NATIVE_STEP123_EACHPHASE_OPICA_CONSUMER
theorem consume_step123_eachPhase_opica_consumer (rho : zetaZeroConfig.carrier) {beta : ℝ}
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
  exact Zeta23.OPICA.step123_eachPhase_opica_consumer rho hbeta hgap

-- Additional clause: Zeta23.OPICA.native_kernel_completion_consumer
theorem consume_native_kernel_completion_consumer {Source : Type*}
    (rho : zetaZeroConfig.carrier) (s : SimplePoleData Source)
    (hcenter : s.center = (rho : ℂ) - 1 / 2) :
    let M : MultiplierOrderData s.center := hcenter.symm ▸ nativeKernelMultiplierOrderData rho
    analyticOrderAt (s.regularRepresentative M) s.center = (M.order - 1 : ℕ) ∧
      iteratedDeriv (M.order - 1) (s.regularRepresentative M) s.center =
        (M.order - 1).factorial * M.unit s.center * s.residue := by
  exact Zeta23.OPICA.native_kernel_completion_consumer rho s hcenter

-- Additional clause: Zeta23.OPICA.native_kernel_residual_consumer
theorem consume_native_kernel_residual_consumer {Source : Type*}
    (rho : zetaZeroConfig.carrier) (s : SimplePoleData Source)
    (hcenter : s.center = (rho : ℂ) - 1 / 2)
    (b : ℂ → ℂ) (hb : AnalyticAt ℂ b s.center) :
    Tendsto (fun z => (z - s.center) *
      ((1 + nativeZeroJetKernelMultiplier z * b z) * s.field z))
      (𝓝[≠] s.center) (𝓝 s.residue) := by
  exact Zeta23.OPICA.native_kernel_residual_consumer rho s hcenter b hb

-- Additional clause: Zeta23.OPICA.native_completed_input_witness_correct
theorem consume_native_completed_input_witness_correct
    (rho : zetaZeroConfig.carrier) (hoff : (rho : ℂ).re ≠ 1 / 2) :
    let M := nativeCompletedInputMultiplierOrderData rho hoff
    M.multiplier = (fun z => nativeCausalLaplaceMoment z 0
        (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
          (nativeZeroJetDamping_pos rho hoff).le : NativeCompletionL2)) ∧
      M.order = zeroMult (rho : ℂ) - 1 ∧
      M.multiplier =ᶠ[𝓝 (nativeZeroJetParameter rho)]
        (fun z => nativeZeroJetInputMultiplier (z + (nativeZeroJetDamping rho : ℂ))) := by
  exact Zeta23.OPICA.native_completed_input_witness_correct rho hoff

end NativeJetAdapter

section NativeArithmeticAdapter
open Finset
open Zeta23.CCM

-- OPICA_NATIVE_NATIVE_ORIGINAL_DRIVE_LOW_MASK_BOUND
theorem consume_native_original_drive_low_mask_bound (order : ℕ) (horder : 0 < order)
    (x y : ℕ → ℝ) (Ax Ay Bmax H T : ℝ) (hAx : 0 ≤ Ax) (hAy : 0 ≤ Ay)
    (hBmax : 1 ≤ Bmax) (hT : 0 ≤ T) (hHT : H ≤ T)
    (hx : ∀ d, 0 < d → |x d| ≤ Ax * (divisorCount order d : ℝ))
    (hy : ∀ d, 0 < d → |y d| ≤ Ay * (divisorCount order d : ℝ))
    (B : ℝ → ℝ) (hBm : Measurable B) (hB : ∀ t ∈ Set.Icc H T, B t ≤ Bmax) :
    MeasureTheory.IntegrableOn
      (finiteLowPair nativeOriginalBoundedCausalDrive (driveIndexBound T) x y B)
      (Set.Icc H T) ∧
    |∫ t in Set.Icc H T,
      finiteLowPair nativeOriginalBoundedCausalDrive (driveIndexBound T) x y B t| ≤
      Ax * Ay * (4 * (T - H) *
        (nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale)) ^ 2 *
        Bmax * (1 + Real.log Bmax) ^ (2 * order - 2) * (1 + T) ^ (order * order)) := by
  exact Zeta23.OPICA.native_original_drive_low_mask_bound order horder x y Ax Ay Bmax H T hAx hAy hBmax hT hHT hx hy B hBm hB

-- Additional clause: Zeta23.OPICA.native_original_drive_uniform_bound
theorem consume_native_original_drive_uniform_bound (t : ℝ) :
    |nativeOriginalIntegerDrive t| ≤
      nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale) := by
  exact Zeta23.OPICA.native_original_drive_uniform_bound t

-- Additional clause: Zeta23.OPICA.native_finite_palette_low_mask_bound
theorem consume_native_finite_palette_low_mask_bound (S : Finset ℕ) (c : ℕ → ℝ)
    (hS : ∀ d ∈ S, 0 < d) (order : ℕ) (horder : 0 < order)
    (x y : ℕ → ℝ) (Ax Ay Bmax H T : ℝ) (hAx : 0 ≤ Ax) (hAy : 0 ≤ Ay)
    (hBmax : 1 ≤ Bmax) (hT : 0 ≤ T) (hHT : H ≤ T)
    (hx : ∀ d, 0 < d → |x d| ≤ Ax * (divisorCount order d : ℝ))
    (hy : ∀ d, 0 < d → |y d| ≤ Ay * (divisorCount order d : ℝ))
    (B : ℝ → ℝ) (hBm : Measurable B) (hB : ∀ t ∈ Set.Icc H T, B t ≤ Bmax) :
    MeasureTheory.IntegrableOn
      (finiteLowPair (finitePaletteDrive nativeOriginalBoundedCausalDrive S c hS)
        (driveIndexBound T) x y B) (Set.Icc H T) ∧
    |∫ t in Set.Icc H T,
      finiteLowPair (finitePaletteDrive nativeOriginalBoundedCausalDrive S c hS)
        (driveIndexBound T) x y B t| ≤
      Ax * Ay * (4 * (T - H) *
        ((∑ d ∈ S, |c d|) *
          (nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale))) ^ 2 *
        Bmax * (1 + Real.log Bmax) ^ (2 * order - 2) * (1 + T) ^ (order * order)) := by
  exact Zeta23.OPICA.native_finite_palette_low_mask_bound S c hS order horder x y Ax Ay Bmax H T hAx hAy hBmax hT hHT hx hy B hBm hB

-- Additional clause: Zeta23.OPICA.nativeOriginalBoundedCausalDrive_apply
theorem consume_nativeOriginalBoundedCausalDrive_apply (t : ℝ) :
    nativeOriginalBoundedCausalDrive t = nativeOriginalIntegerDrive t := by
  exact Zeta23.OPICA.nativeOriginalBoundedCausalDrive_apply t

-- Additional clause: Zeta23.OPICA.inverseSqrtArithmeticFunction_multiplicative
theorem consume_inverseSqrtArithmeticFunction_multiplicative :
    inverseSqrtArithmeticFunction.IsMultiplicative := by
  exact Zeta23.OPICA.inverseSqrtArithmeticFunction_multiplicative

-- Additional clause: Zeta23.OPICA.squarefree_palette_absolute_cost
theorem consume_squarefree_palette_absolute_cost (Q : ℕ) (hQ : Squarefree Q) :
    (∑ d ∈ Q.divisors, |moebiusPaletteCoefficient d|) = squarefreePaletteCost Q := by
  exact Zeta23.OPICA.squarefree_palette_absolute_cost Q hQ

-- Additional clause: Zeta23.OPICA.squarefreePaletteDrive_apply
theorem consume_squarefreePaletteDrive_apply (U : BoundedCausalDrive) (Q : ℕ) (t : ℝ) :
    squarefreePaletteDrive U Q t =
      ∑ d ∈ Q.divisors, (ArithmeticFunction.moebius d : ℝ) / Real.sqrt (d : ℝ) *
        U (t - Real.log d) := by
  exact Zeta23.OPICA.squarefreePaletteDrive_apply U Q t

-- Additional clause: Zeta23.OPICA.squarefreePaletteDrive_bound
theorem consume_squarefreePaletteDrive_bound (U : BoundedCausalDrive) (Q : ℕ)
    (hQ : Squarefree Q) :
    (squarefreePaletteDrive U Q).bound = squarefreePaletteCost Q * U.bound := by
  exact Zeta23.OPICA.squarefreePaletteDrive_bound U Q hQ

-- Additional clause: Zeta23.OPICA.native_squarefree_palette_uniform_bound
theorem consume_native_squarefree_palette_uniform_bound (Q : ℕ) (hQ : Squarefree Q) (t : ℝ) :
    |squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q t| ≤
      squarefreePaletteCost Q *
        (nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale)) := by
  exact Zeta23.OPICA.native_squarefree_palette_uniform_bound Q hQ t

-- Additional clause: Zeta23.OPICA.native_squarefree_palette_low_mask_bound
theorem consume_native_squarefree_palette_low_mask_bound (Q : ℕ) (hQ : Squarefree Q)
    (order : ℕ) (horder : 0 < order)
    (x y : ℕ → ℝ) (Ax Ay Bmax H T : ℝ) (hAx : 0 ≤ Ax) (hAy : 0 ≤ Ay)
    (hBmax : 1 ≤ Bmax) (hT : 0 ≤ T) (hHT : H ≤ T)
    (hx : ∀ d, 0 < d → |x d| ≤ Ax * (divisorCount order d : ℝ))
    (hy : ∀ d, 0 < d → |y d| ≤ Ay * (divisorCount order d : ℝ))
    (B : ℝ → ℝ) (hBm : Measurable B) (hB : ∀ t ∈ Set.Icc H T, B t ≤ Bmax) :
    MeasureTheory.IntegrableOn
      (finiteLowPair (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q)
        (driveIndexBound T) x y B) (Set.Icc H T) ∧
    |∫ t in Set.Icc H T,
      finiteLowPair (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q)
        (driveIndexBound T) x y B t| ≤
      Ax * Ay * (4 * (T - H) *
        squarefreePaletteCost Q ^ 2 *
        (nativeOriginalDriveDecayConstant * (3 + UniversalSinc.fixedScale)) ^ 2 *
        Bmax * (1 + Real.log Bmax) ^ (2 * order - 2) * (1 + T) ^ (order * order)) := by
  exact Zeta23.OPICA.native_squarefree_palette_low_mask_bound Q hQ order horder x y Ax Ay Bmax H T hAx hAy hBmax hT hHT hx hy B hBm hB

end NativeArithmeticAdapter

section SincTriangle
open Set MeasureTheory
open scoped FourierTransform Convolution ContDiff

-- Additional clause: Zeta23.OPICA.unitTriangle_fourier
theorem consume_unitTriangle_fourier (xi : ℝ) :
    𝓕 (fun x => (unitTriangle x : ℂ)) xi = (sincSquared xi : ℂ) := by
  exact Zeta23.OPICA.unitTriangle_fourier xi

-- Additional clause: Zeta23.OPICA.sincSquared_fourier
theorem consume_sincSquared_fourier (xi : ℝ) :
    𝓕 (fun x => (sincSquared x : ℂ)) xi = (unitTriangle xi : ℂ) := by
  exact Zeta23.OPICA.sincSquared_fourier xi

end SincTriangle

section LocallyFiniteSignedMeasure
open MeasureTheory Set Filter
open scoped SchwartzMap ContDiff CompactlySupported Convolution Topology Pointwise

-- Additional clause: Zeta23.OPICA.LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply
theorem consume_distributionOfLinearGrowth_apply
    (ν : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth) (f : SchwartzMap ℝ ℂ) :
    ν.distributionOfLinearGrowth hν f =
      (∫ x, f x ∂ν.positive) - ∫ x, f x ∂ν.negative := by
  exact Zeta23.OPICA.LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply ν hν f

-- Additional clause: Zeta23.OPICA.LocallyFiniteSignedMeasure.parts_eq_zero_of_distribution_eq_zero
theorem consume_parts_eq_zero_of_distribution_eq_zero
    (ν : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth)
    (hzero : ν.distributionOfLinearGrowth hν = 0) :
    ν.positive = 0 ∧ ν.negative = 0 := by
  exact Zeta23.OPICA.LocallyFiniteSignedMeasure.parts_eq_zero_of_distribution_eq_zero ν hν hzero

-- Additional clause: Zeta23.OPICA.LocallyFiniteSignedMeasure.parts_eq_of_distribution_eq
theorem consume_parts_eq_of_distribution_eq
    (ν η : LocallyFiniteSignedMeasure) (hν : ν.HasLinearGrowth) (hη : η.HasLinearGrowth)
    (heq : ν.distributionOfLinearGrowth hν = η.distributionOfLinearGrowth hη) :
    ν.positive = η.positive ∧ ν.negative = η.negative := by
  exact Zeta23.OPICA.LocallyFiniteSignedMeasure.parts_eq_of_distribution_eq ν η hν hη heq

-- Additional clause: Zeta23.OPICA.LocallyFiniteSignedMeasure.distributionOfLinearGrowth_injective
theorem consume_distributionOfLinearGrowth_injective :
    Function.Injective (fun ν : {ν : LocallyFiniteSignedMeasure // ν.HasLinearGrowth} =>
      ν.val.distributionOfLinearGrowth ν.property) := by
  exact Zeta23.OPICA.LocallyFiniteSignedMeasure.distributionOfLinearGrowth_injective

end LocallyFiniteSignedMeasure

-- Explicit removable-value and distinct-cusp specializations of H4.
theorem consume_fejer_completion_removable_half :
    Zeta23.CCM.nativePositiveCompletionLaplace (1 / 2 : ℂ) = 1 / 2 := by
  have h := Zeta23.OPICA.fejer_completion_affine_identity (w := (1 / 2 : ℂ))
    (by norm_num)
  norm_num at h
  exact h

theorem consume_fejer_cusp_slopes_distinct {n : ℕ} (hn : 2 ≤ n) :
    -(1 / Real.sqrt (n : ℝ)) ≠ 1 / Real.sqrt (n : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hpos : 0 < 1 / Real.sqrt (n : ℝ) := div_pos zero_lt_one (Real.sqrt_pos.mpr hnreal)
  intro heq
  linarith

end Zeta23.RHRC.OpicaValidation
