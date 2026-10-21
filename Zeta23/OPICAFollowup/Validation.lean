import Zeta23.OPICAFollowup.NormFirstTransfer
import Zeta23.OPICAFollowup.JointObservation
import Zeta23.OPICAFollowup.Counterexamples

/-! Partial expected-type audit: 11 of the 100 planned primary roots.
This module does not assert full follow-up acceptance. -/


namespace Zeta23.OPICAFollowup.Validation

open Filter Topology
open Zeta23.OPICA

def expected_norm_first_log_comparison {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    |Real.log (1+‖F‖^2)-Real.log (1+max q 0)| ≤
      2*Real.log (1+‖S‖)+Real.log (1+|l|) :=
  norm_first_log_comparison F S B q l hF hq

def expected_norm_first_rate_transfer {E : Type*} [SeminormedAddCommGroup E]
    (T : HorizonSchedule) (F S B : ℕ → E) (q l : ℕ → ℝ)
    (hF : ∀ n, F n = S n+B n) (hq : ∀ n, q n = ‖B n‖^2-l n)
    (hS : SubexpAlong T S) (hl : SubexpAlong T l) :
    Tendsto (fun n => positiveRate T (fun k => ‖F k‖^2) n -
      positiveRate T q n) atTop (𝓝 0) ∧
    (∀ r : ℝ, Tendsto (positiveRate T (fun k => ‖F k‖^2)) atTop (𝓝 r) ↔
      Tendsto (positiveRate T q) atTop (𝓝 r)) ∧
    (Filter.limsup (fun n => ENNReal.ofReal (positiveRate T (fun k => ‖F k‖^2) n)) atTop =
      Filter.limsup (fun n => ENNReal.ofReal (positiveRate T q n)) atTop ∧
    Filter.liminf (fun n => ENNReal.ofReal (positiveRate T (fun k => ‖F k‖^2) n)) atTop =
      Filter.liminf (fun n => ENNReal.ofReal (positiveRate T q n)) atTop) :=
  norm_first_rate_transfer T F S B q l hF hq hS hl

def expected_energy_allocation_bound {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    ‖F‖^2 ≤ 2*‖S‖^2+2*max q 0+2*|l| :=
  energy_allocation_bound F S B q l hF hq

def expected_energy_allocation_rate_lower {E : Type*} [SeminormedAddCommGroup E]
    (T : HorizonSchedule) (F S B : ℕ → E) (q l : ℕ → ℝ)
    (hF : ∀ n, F n = S n+B n) (hq : ∀ n, q n = ‖B n‖^2-l n)
    (hl : SubexpAlong T l) {θ : ℝ} (hθ : 0 < θ)
    (hfull : Tendsto (positiveRate T (fun n => ‖F n‖^2)) atTop (𝓝 θ)) :
    (∀ b : ℝ, b < θ → ∀ᶠ n in atTop,
      b ≤ positiveRate T (fun k => max (‖S k‖^2) (max (q k) 0)) n) ∧
    ENNReal.ofReal θ ≤ Filter.liminf
      (fun n => ENNReal.ofReal
        (positiveRate T (fun k => max (‖S k‖^2) (max (q k) 0)) n)) atTop :=
  energy_allocation_rate_lower T F S B q l hF hq hl hθ hfull

-- The norm-general roots specialize to either scalar Hilbert field.
example (F S B : ℂ) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    |Real.log (1+‖F‖^2)-Real.log (1+max q 0)| ≤
      2*Real.log (1+‖S‖)+Real.log (1+|l|) :=
  expected_norm_first_log_comparison F S B q l hF hq

example (F S B : ℝ) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    ‖F‖^2 ≤ 2*‖S‖^2+2*max q 0+2*|l| :=
  expected_energy_allocation_bound F S B q l hF hq

#print axioms Zeta23.OPICAFollowup.norm_first_log_comparison
#print axioms Zeta23.OPICAFollowup.norm_first_rate_transfer
#print axioms Zeta23.OPICAFollowup.energy_allocation_bound
#print axioms Zeta23.OPICAFollowup.energy_allocation_rate_lower
#print axioms Zeta23.OPICAFollowup.norm_first_scalar_bound
#print axioms Zeta23.OPICAFollowup.norm_first_log_upper
#print axioms Zeta23.OPICAFollowup.norm_first_log_norms
#print axioms Zeta23.OPICAFollowup.norm_first_log_positive_part
#print axioms Zeta23.OPICAFollowup.norm_first_rate_difference
#print axioms Zeta23.OPICAFollowup.nonnegative_rate_extended_congr
#print axioms Zeta23.OPICAFollowup.energy_allocation_log_bound

end Zeta23.OPICAFollowup.Validation


/-! Explicit expected-type consumers. This is a partial audit module; native consumers
and the remaining planned root types are still required by the full specification. -/
namespace Zeta23.OPICAFollowup
noncomputable section

variable {𝕜 E Y H : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y] [FiniteDimensional 𝕜 Y]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [FiniteDimensional 𝕜 H]

local instance expectedCompleteInput : CompleteSpace E := FiniteDimensional.complete 𝕜 E
local instance expectedCompleteOutput : CompleteSpace Y := FiniteDimensional.complete 𝕜 Y

omit [FiniteDimensional 𝕜 Y] [FiniteDimensional 𝕜 H] in
theorem expected_joint_recovery_iff
    (P : E →L[𝕜] Y) (C : E →L[𝕜] H) (ell : E →L[𝕜] 𝕜) :
    (∃ R : WithLp 2 (Y × H) →L[𝕜] 𝕜,
      ∀ x : E, R (jointObservation P C x) = ell x) ↔
      P.ker ⊓ C.ker ≤ ell.ker :=
  joint_recovery_iff P C ell

omit [FiniteDimensional 𝕜 Y] [FiniteDimensional 𝕜 H] in
theorem expected_joint_recovery_optimal_norm
    (P : E →L[𝕜] Y) (C : E →L[𝕜] H) (ell : E →L[𝕜] 𝕜)
    (recoverable : P.ker ⊓ C.ker ≤ ell.ker) :
    ∃ R : WithLp 2 (Y × H) →L[𝕜] 𝕜,
      (∀ x : E, R (jointObservation P C x) = ell x) ∧
      ‖R‖ = sSup {q : ℝ | ∃ x : E, jointObservation P C x ≠ 0 ∧
        q = ‖ell x‖ / ‖jointObservation P C x‖} ∧
      (‖R‖ = 0 ↔ ell = 0) ∧
      (∀ S : WithLp 2 (Y × H) →L[𝕜] 𝕜,
        (∀ x : E, S (jointObservation P C x) = ell x) → ‖R‖ ≤ ‖S‖) :=
  joint_recovery_optimal_norm P C ell recoverable

omit [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 Y] [FiniteDimensional 𝕜 H] in
theorem expected_joint_recovery_noise_bound
    (P : E →L[𝕜] Y) (C : E →L[𝕜] H) (ell : E →L[𝕜] 𝕜)
    (R : WithLp 2 (Y × H) →L[𝕜] 𝕜)
    (recovers : ∀ x : E, R (jointObservation P C x) = ell x)
    (epsilon : ℝ) (nonnegative_error : 0 ≤ epsilon)
    (x : E) (y : WithLp 2 (Y × H))
    (error_budget : ‖y - jointObservation P C x‖ ≤ epsilon) :
    ‖ell x - R y‖ ≤ ‖R‖ * epsilon :=
  joint_recovery_noise_bound P C ell R recovers epsilon nonnegative_error x y error_budget

theorem expected_approx_compatibility_left_null
    (B : E →L[𝕜] Y) (b : Y) (epsilon : ℝ) (nonnegative_error : 0 ≤ epsilon) :
    (Metric.infDist b (B.range : Set Y) ≤ epsilon ↔
      ∃ x : E, ‖b - B x‖ ≤ epsilon) ∧
    (∀ v : Y, B.adjoint v = 0 → ‖v‖ = 1 → epsilon < ‖inner 𝕜 v b‖ →
      ¬ ∃ x : E, ‖b - B x‖ ≤ epsilon) :=
  approx_compatibility_left_null B b epsilon nonnegative_error

omit [FiniteDimensional 𝕜 Y] [FiniteDimensional 𝕜 H] in
/-- The noise bound is consumed at the attained exact optimum, rather than with
an unspecified or assumed inexpensive recovery map. -/
theorem expected_optimal_recovery_noise_composition
    (P : E →L[𝕜] Y) (C : E →L[𝕜] H) (ell : E →L[𝕜] 𝕜)
    (recoverable : P.ker ⊓ C.ker ≤ ell.ker) :
    ∃ R : WithLp 2 (Y × H) →L[𝕜] 𝕜,
      (∀ x : E, R (jointObservation P C x) = ell x) ∧
      ‖R‖ = sSup {q : ℝ | ∃ x : E, jointObservation P C x ≠ 0 ∧
        q = ‖ell x‖ / ‖jointObservation P C x‖} ∧
      ∀ (epsilon : ℝ), 0 ≤ epsilon → ∀ (x : E) (y : WithLp 2 (Y × H)),
        ‖y - jointObservation P C x‖ ≤ epsilon →
        ‖ell x - R y‖ ≤ ‖R‖ * epsilon := by
  obtain ⟨R, hR, hnorm, hzero, hminimal⟩ := joint_recovery_optimal_norm P C ell recoverable
  exact ⟨R, hR, hnorm, fun epsilon hepsilon x y herror =>
    joint_recovery_noise_bound P C ell R hR epsilon hepsilon x y herror⟩

theorem expected_recovery_subexp_budget {F : ℕ → Type*}
    [∀ n, NormedAddCommGroup (F n)] [∀ n, NormedSpace 𝕜 (F n)]
    (T : Zeta23.OPICA.HorizonSchedule) (R : ∀ n, F n →L[𝕜] 𝕜)
    (complete_error : ∀ n, F n)
    (recovery_budget : Zeta23.OPICA.SubexpAlong T (fun n => ‖R n‖))
    (error_budget : Zeta23.OPICA.SubexpAlong T (fun n => ‖complete_error n‖)) :
    Zeta23.OPICA.SubexpAlong T (fun n => R n (complete_error n)) :=
  recovery_subexp_budget T R complete_error recovery_budget error_budget

end
end Zeta23.OPICAFollowup

#print axioms Zeta23.OPICAFollowup.joint_recovery_iff
#print axioms Zeta23.OPICAFollowup.joint_recovery_optimal_norm
#print axioms Zeta23.OPICAFollowup.joint_recovery_noise_bound
#print axioms Zeta23.OPICAFollowup.approx_compatibility_left_null
#print axioms Zeta23.OPICAFollowup.recovery_subexp_budget


namespace Zeta23.OPICAFollowup.Validation
open Filter Topology
open Zeta23.OPICA
open scoped Matrix

theorem expected_norm_first_strictly_weaker_control (T : HorizonSchedule) {θ : ℝ} (hθ : 0 < θ) :
    (∀ n, exponentialFull T θ n = 1+exponentialBalanced T θ n) ∧
    Tendsto (positiveRate T (fun n => ‖exponentialBalanced T θ n‖^2))
      atTop (𝓝 θ) ∧
    Tendsto (positiveRate T (fun n => ‖exponentialFull T θ n‖^2))
      atTop (𝓝 θ) ∧
    (∀ n, ‖exponentialFull T θ n‖^2-‖exponentialBalanced T θ n‖^2 =
      2*exponentialBalanced T θ n+1) ∧
    Tendsto (magnitudeRate T (fun n =>
      ‖exponentialFull T θ n‖^2-‖exponentialBalanced T θ n‖^2))
      atTop (𝓝 (θ/2)) ∧
    ¬ SubexpAlong T (fun n =>
      ‖exponentialFull T θ n‖^2-‖exponentialBalanced T θ n‖^2) :=
  norm_first_strictly_weaker_control T hθ

theorem expected_coupled_gram_collision_control :
    (∀ h : ℝ, 0 < h → h < 1 →
      (∀ τ : ℝ, ‖collisionInner h (Complex.I*τ)‖ = 1) ∧
      (∀ i : Fin 2, collisionInner h (collisionPole h i) = 0 ∧
        -deriv (collisionInner h) (collisionPole h i) = (collisionTarget h i : ℂ)) ∧
      collisionGram h = !![1/(2*(1-h)), (1:ℝ)/2; 1/2, 1/(2*(1+h))] ∧
      (collisionGram h).det = h^2/(4*(1-h^2)) ∧
      0 < (collisionGram h).det ∧
      collisionCost h = (2-h^2)/(1-h^2)) ∧
    Tendsto collisionCost (𝓝[>] (0:ℝ)) (𝓝 2) ∧
    Tendsto (fun h => (collisionGram h).det) (𝓝[>] (0:ℝ)) (𝓝 0) ∧
    (collisionGram 0).det = 0 :=
  coupled_gram_collision_control

#print axioms Zeta23.OPICAFollowup.norm_first_strictly_weaker_control
#print axioms Zeta23.OPICAFollowup.coupled_gram_collision_control

end Zeta23.OPICAFollowup.Validation

namespace Zeta23.OPICAFollowup.Validation
/- Optional Candidate1 consumers. These append supporting scope checks without
changing any of the four required primary expected signatures. -/
theorem expected_sharp_norm_first_arsinh_bound
    {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    |Real.log (1+‖u‖^2)-Real.log (1+‖v‖^2)| ≤
      2*Real.arsinh (‖u-v‖/2) ∧
      2*Real.arsinh (‖u-v‖/2) ≤ 2*Real.log (1+‖u-v‖) :=
  sharp_norm_first_arsinh_bound u v

theorem expected_sharp_norm_first_scalar_attained {d : ℝ} (hd : 0 ≤ d) :
    ‖sharpNormAlpha d-(sharpNormAlpha d)⁻¹‖ = d ∧
    |Real.log (1+‖sharpNormAlpha d‖^2)-Real.log (1+‖(sharpNormAlpha d)⁻¹‖^2)| =
      2*Real.log (sharpNormAlpha d) :=
  sharp_norm_first_scalar_attained hd

theorem expected_sharp_norm_first_log_comparison
    {E : Type*} [SeminormedAddCommGroup E] (F S B : E) (q l : ℝ)
    (field_decomposition : F = S+B) (signed_quadratic : q = ‖B‖^2-l) :
    |Real.log (1+‖F‖^2)-Real.log (1+max q 0)| ≤
      2*Real.arsinh (‖S‖/2)+Real.log (1+|l|) :=
  sharp_norm_first_log_comparison F S B q l field_decomposition signed_quadratic

/-- Explicitly recover the unchanged mandatory comparison interface. -/
theorem expected_sharp_norm_first_recovers_primary
    {E : Type*} [SeminormedAddCommGroup E] (F S B : E) (q l : ℝ)
    (field_decomposition : F = S+B) (signed_quadratic : q = ‖B‖^2-l) :
    |Real.log (1+‖F‖^2)-Real.log (1+max q 0)| ≤
      2*Real.log (1+‖S‖)+Real.log (1+|l|) := by
  have hsharp := sharp_norm_first_log_comparison F S B q l
    field_decomposition signed_quadratic
  have hbound : 2*Real.arsinh (‖S‖/2) ≤ 2*Real.log (1+‖S‖) := by
    simpa only [sub_zero] using (sharp_norm_first_arsinh_bound S 0).2
  linarith

open Filter Topology
theorem expected_collisionGram_inverse_zero_zero {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    ((collisionGram h)⁻¹) 0 0 = 2*(1-h)/h^2 :=
  collisionGram_inverse_zero_zero h0 h1

theorem expected_collisionGram_inverse_zero_zero_tendsto :
    Tendsto (fun h : ℝ => ((collisionGram h)⁻¹) 0 0) (𝓝[>] (0:ℝ)) atTop :=
  collisionGram_inverse_zero_zero_tendsto

end Zeta23.OPICAFollowup.Validation

