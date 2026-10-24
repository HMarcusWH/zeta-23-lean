import Zeta23.OPICAFollowup.LogSlackBalance
import Zeta23.OPICAFollowup.MaskedNativeRate
import Zeta23.OPICAFollowup.AuxiliaryCompletions
import Zeta23.OPICAFollowup.ComplexLocalMeasures
import Zeta23.OPICAFollowup.NativeTransformationWords
import Zeta23.OPICAFollowup.UniformSourceBounds
import Zeta23.OPICAFollowup.NativeFilters
import Zeta23.OPICAFollowup.ForwardLocalization
import Zeta23.OPICAFollowup.NativeSourceTransforms
import Zeta23.OPICAFollowup.NativeExplicitFormula
import Zeta23.OPICAFollowup.ZetaLeftLineBounds
import Zeta23.OPICAFollowup.NativeSourceFamily
import Zeta23.OPICAFollowup.SourceVerticalBounds
import Zeta23.OPICAFollowup.BalancedCoefficients
import Zeta23.OPICAFollowup.RobustLaurent
import Zeta23.OPICAFollowup.NormFirstTransfer
import Zeta23.OPICAFollowup.JointObservation
import Zeta23.OPICAFollowup.Counterexamples

/-! Partial expected-type audit: 41 of the 100 planned primary roots.
This module does not assert full follow-up acceptance. -/


namespace Zeta23.OPICAFollowup.Validation

open Filter Topology
open Zeta23.OPICA

theorem expected_norm_first_log_comparison {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    |Real.log (1+‖F‖^2)-Real.log (1+max q 0)| ≤
      2*Real.log (1+‖S‖)+Real.log (1+|l|) :=
  norm_first_log_comparison F S B q l hF hq

theorem expected_norm_first_rate_transfer {E : Type*} [SeminormedAddCommGroup E]
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

theorem expected_energy_allocation_bound {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    ‖F‖^2 ≤ 2*‖S‖^2+2*max q 0+2*|l| :=
  energy_allocation_bound F S B q l hF hq

theorem expected_energy_allocation_rate_lower {E : Type*} [SeminormedAddCommGroup E]
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


noncomputable section
namespace Zeta23.OPICAFollowup.Validation
open Filter Topology Zeta23.OPICA Zeta23.CCM
open scoped Matrix ComplexOrder

theorem expected_sourceFamily_zero_eq_original :
    sourceOrderFamily 0 = nativeOriginalSource ∧
    primeFieldFamily 0 = nativeOriginalPrimeField ∧
    integerDriveFamily 0 = nativeOriginalIntegerDrive :=
  sourceFamily_zero_eq_original

theorem expected_sourceFamily_support_smooth_moments (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (sourceOrderFamily d) ∧
    NativeSourceSupported UniversalSinc.fixedScale (sourceOrderFamily d) ∧
    0 < nativeCausalGap ∧
    (∀ t < nativeCausalGap, primeFieldFamily d t = 0 ∧ integerDriveFamily d t = 0) ∧
    (∀ k < d+2, sourceWeightedMoment k (1/2) (sourceOrderFamily d) = 0 ∧
      sourceWeightedMoment k (-1/2) (sourceOrderFamily d) = 0) :=
  sourceFamily_support_smooth_moments d

theorem expected_sourceFamily_physical_histories (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (primeFieldFamily d) ∧
    ContDiff ℝ (⊤ : ℕ∞) (integerDriveFamily d) ∧
    (∀ T t : ℝ, t ≤ T → primeFieldFamily d t =
      ∑ n ∈ Finset.range (nativeHistoryCutoff UniversalSinc.fixedScale T+1),
        nativePrimeCoefficient n*sourceOrderFamily d (t-Real.log n)) ∧
    (∀ T t : ℝ, t ≤ T → integerDriveFamily d t =
      ∑ n ∈ Finset.range (nativeHistoryCutoff UniversalSinc.fixedScale T+1),
        nativeIntegerDriveCoefficient n*sourceOrderFamily d (t-Real.log n)) :=
  ⟨primeFieldFamily_contDiff d, integerDriveFamily_contDiff d,
    fun _ _ ht => primeFieldFamily_history d ht,
    fun _ _ ht => integerDriveFamily_history d ht⟩

theorem expected_source_product_vertical_bound (σ τ : ℝ) :
    ‖sourceBoxProduct ((σ : ℂ)+Complex.I*(τ : ℂ))‖ ≤
      8*Real.exp (UniversalSinc.fixedScale*|σ|)*
        Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|) :=
  source_product_vertical_bound σ τ

-- This checks the prescribed one-copy product and exact constant, not a caller envelope.
example (w : ℂ) : sourceBoxProduct w =
    UniversalSinc.product UniversalSinc.fixedScale (Complex.I*w) := rfl
example : sourceVerticalDecayConstant = Real.log 8*Real.sqrt UniversalSinc.fixedScale/4 := rfl

theorem expected_history_recovery_cost_control {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (u : E) (hu : ‖u‖ = 1) :
    (∀ ε : ℝ, ε ≠ 0 → ∃ R : WithLp 2 (E × ℂ) →L[ℂ] ℂ,
      (∀ x, R (jointObservation (historyContrast u) (historyChannel u ε) x) = inner ℂ u x) ∧
      ‖R‖ = 1 / |ε| ∧
      (∀ R' : WithLp 2 (E × ℂ) →L[ℂ] ℂ,
        (∀ x, R' (jointObservation (historyContrast u) (historyChannel u ε) x) = inner ℂ u x) →
        ‖R‖ ≤ ‖R'‖)) ∧
    (∀ (T : HorizonSchedule) (a : ℝ), 0 < a →
      Tendsto (magnitudeRate T (fun n => historyRecovery E (Real.exp (-a*T.time n))))
        atTop (𝓝 (a/2)) ∧
      ¬ SubexpAlong T (fun n => historyRecovery E (Real.exp (-a*T.time n)))) :=
  history_recovery_cost_control u hu

theorem expected_forced_positive_gram_nonreal_control {ι δ : Type*}
    [Fintype ι] [Fintype δ] [DecidableEq δ]
    (a g : δ → ℝ) (κ : ι → ℂ) (ha : ∀ n, 0 < a n)
    (hg : ∃ n, g n ≠ 0) (hκ : ∀ i, (κ i).im ≠ 0) :
    (forcedProfileGram a g κ).PosSemidef ∧
    (forcedProfileEnergy a g κ).PosSemidef ∧
    (∀ i, 0 < (forcedProfileGram a g κ i i).re) ∧
    (∀ i, forcedDiagonalProfile a g (κ i) =
      κ i • ((Matrix.diagonal (fun n => (a n : ℂ)) - κ i • (1 : Matrix δ δ ℂ))⁻¹ *ᵥ
        (fun n => (g n : ℂ)))) ∧
    (∀ i j,
      forcedProfileEnergy a g κ i j =
        κ i * (forcedProfileGram a g κ i j + star (forcedProfileSample a g (κ j))) ∧
      forcedProfileEnergy a g κ i j =
        star (κ j) * (forcedProfileGram a g κ i j + forcedProfileSample a g (κ i)) ∧
      (κ i - star (κ j)) * forcedProfileGram a g κ i j =
        star (κ j) * forcedProfileSample a g (κ i) -
          κ i * star (forcedProfileSample a g (κ j)) ∧
      (κ i - star (κ j) ≠ 0 →
        forcedProfileGram a g κ i j / (κ i * star (κ j)) =
          (forcedProfileSample a g (κ i) / κ i -
            star (forcedProfileSample a g (κ j) / κ j)) / (κ i - star (κ j)))) ∧
    ((∀ n, 1/4 ≤ a n) →
      (forcedProfileEnergy a g κ - (1/4 : ℂ) • forcedProfileGram a g κ).PosSemidef) :=
  forced_positive_gram_nonreal_control a g κ ha hg hκ

-- An inhabited positive diagonal system with two explicitly nonreal parameters.
theorem expected_forced_concrete_witness :
    (forcedProfileGram (fun _ : Fin 1 => 1) (fun _ => 1) forcedNonrealParameters).PosSemidef ∧
    (forcedProfileEnergy (fun _ : Fin 1 => 1) (fun _ => 1) forcedNonrealParameters).PosSemidef ∧
    (∀ i, 0 < (forcedProfileGram (fun _ : Fin 1 => 1) (fun _ => 1)
      forcedNonrealParameters i i).re) := by
  have h := expected_forced_positive_gram_nonreal_control (fun _ : Fin 1 => 1) (fun _ => 1)
    forcedNonrealParameters (by intro n; norm_num)
    ⟨0, by norm_num⟩ forcedNonrealParameters_im_ne
  exact ⟨h.1,h.2.1,h.2.2.1⟩

#print axioms Zeta23.OPICAFollowup.sourceFamily_zero_eq_original
#print axioms Zeta23.OPICAFollowup.sourceFamily_support_smooth_moments
#print axioms Zeta23.OPICAFollowup.source_product_vertical_bound
#print axioms Zeta23.OPICAFollowup.history_recovery_cost_control
#print axioms Zeta23.OPICAFollowup.forced_positive_gram_nonreal_control
end Zeta23.OPICAFollowup.Validation

-- Add `import Zeta23.OPICAFollowup.BalancedCoefficients` to Validation's imports.
-- This fragment is checked against a byte-identical copy of the leaf source,
-- because producing the .olean remains serialized with the other writers.

noncomputable section
open scoped BigOperators

namespace Zeta23.OPICAFollowup.Validation
open Zeta23.OPICA

theorem expected_native_binomial_inverse_identity (Q : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (r : ℕ) (hr : 2 ≤ r) :
    nativeInverseCoefficients Q = typeICoefficients Q Y r + balancedInverseCoefficients Q Y r ∧
    (∀ (U : BoundedCausalDrive) (T t : ℝ), t ≤ T →
      (∀ n : ℕ, driveIndexBound T < n →
        nativeInverseCoefficients Q n * translatedDrive U n t = 0) ∧
      (∑' n : ℕ, nativeInverseCoefficients Q n * translatedDrive U n t) =
        finiteDriveField U (driveIndexBound T) (typeICoefficients Q Y r) t +
        finiteDriveField U (driveIndexBound T) (balancedInverseCoefficients Q Y r) t) :=
  native_binomial_inverse_identity Q Y hY r hr

theorem expected_balanced_coeff_divisor_bound (Q : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (r : ℕ) (hr : 2 ≤ r) (n : ℕ) :
    |balancedInverseCoefficients Q Y r n| ≤ (divisorCount (2 * r - 1) n : ℝ) ∧
    |typeICoefficients Q Y r n| ≤
      ((2 : ℝ) ^ r - 1) * (divisorCount (2 * r - 1) n : ℝ) :=
  balanced_coeff_divisor_bound Q Y hY r hr n

-- These are the literal J17 coefficients, including the free integer powers.
example (Q : ℕ) (Y : ℝ) (r : ℕ) :
    typeICoefficients Q Y r =
      ∑ i ∈ Finset.range r, ((-1 : ℝ) ^ i * (r.choose (i + 1) : ℝ)) •
        (smallInverseCoefficients Q Y ^ (i + 1) * nativeFreeCoefficients Q ^ i) := rfl

example (Q : ℕ) (Y : ℝ) (r : ℕ) :
    balancedInverseCoefficients Q Y r =
      nativeLargeCoefficients Q Y ^ r * nativeFreeCoefficients Q ^ (r - 1) := rfl

-- Actual P0 native source, multiplied by its actual finite palette filter.
-- No caller supplies a coefficient identity, a physical field or a bound.
theorem native_j17_original_palette_physical_consumer (Q : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (r : ℕ) (hr : 2 ≤ r) (T t : ℝ) (ht : t ≤ T) :
    (∑' n : ℕ, nativeInverseCoefficients Q n *
      translatedDrive (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q) n t) =
      finiteDriveField (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q)
        (driveIndexBound T) (typeICoefficients Q Y r) t +
      finiteDriveField (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q)
        (driveIndexBound T) (balancedInverseCoefficients Q Y r) t :=
  ((expected_native_binomial_inverse_identity Q Y hY r hr).2
    (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q) T t ht).2

-- A nonsquarefree total product is included in the public envelope.
example :
    |balancedInverseCoefficients 1 (3/2) 2 4| ≤ (divisorCount 3 4 : ℝ) ∧
    |typeICoefficients 1 (3/2) 2 4| ≤ 3 * (divisorCount 3 4 : ℝ) := by
  convert expected_balanced_coeff_divisor_bound 1 (3/2) (by norm_num) 2 (by norm_num) 4 using 1
  norm_num

#print axioms Zeta23.OPICAFollowup.native_binomial_inverse_identity
#print axioms Zeta23.OPICAFollowup.balanced_coeff_divisor_bound
#print axioms native_j17_original_palette_physical_consumer

end Zeta23.OPICAFollowup.Validation

noncomputable section
namespace Zeta23.OPICAFollowup.Validation
open Filter Topology Metric Set Complex
open scoped Real
theorem expected_laurent_coefficient_error_bound {f g : ℂ → ℂ} {c : ℂ} {r E : ℝ}
    (radius_positive : 0 < r) (original_meromorphic : MeromorphicAt f c)
    (observed_meromorphic : MeromorphicAt g c)
    (original_domain : AnalyticOnNhd ℂ f (closedBall c r \ {c}))
    (observed_domain : AnalyticOnNhd ℂ g (closedBall c r \ {c}))
    (actual_circle_budget : ContourErrorBudget f g c r E)
    (j : ℤ) (degree_in_scope : -1 ≤ j) :
    ‖laurentObservedCoefficient g c observed_meromorphic j-
      laurentObservedCoefficient f c original_meromorphic j‖ ≤ r^(-j)*E :=
  laurent_coefficient_error_bound radius_positive original_meromorphic observed_meromorphic
    original_domain observed_domain actual_circle_budget degree_in_scope

theorem expected_laurent_observation_survives {f g : ℂ → ℂ} {c : ℂ} {r E : ℝ}
    (radius_positive : 0 < r) (original_meromorphic : MeromorphicAt f c)
    (observed_meromorphic : MeromorphicAt g c)
    (original_domain : AnalyticOnNhd ℂ f (closedBall c r \ {c}))
    (observed_domain : AnalyticOnNhd ℂ g (closedBall c r \ {c}))
    (actual_circle_budget : ContourErrorBudget f g c r E)
    (j : ℤ) (degree_in_scope : -1 ≤ j)
    (strict_threshold : E < ‖laurentObservedCoefficient f c original_meromorphic j‖*r^j) :
    laurentObservedCoefficient g c observed_meromorphic j ≠ 0 :=
  laurent_observation_survives radius_positive original_meromorphic observed_meromorphic
    original_domain observed_domain actual_circle_budget degree_in_scope strict_threshold

theorem expected_laurent_derivative_error_bound {f g : ℂ → ℂ} {c : ℂ} {r E : ℝ}
    (radius_positive : 0 < r) (original_meromorphic : MeromorphicAt f c)
    (observed_meromorphic : MeromorphicAt g c)
    (original_holomorphic : AnalyticOnNhd ℂ f (closedBall c r))
    (observed_holomorphic : AnalyticOnNhd ℂ g (closedBall c r))
    (actual_circle_budget : ∀ z ∈ sphere c r, ‖g z-f z‖ ≤ E) (n : ℕ) :
    ‖iteratedDeriv n g c-iteratedDeriv n f c‖ ≤
      (n.factorial : ℝ)*(r^(-(n:ℤ))*E) :=
  laurent_derivative_error_bound radius_positive original_meromorphic observed_meromorphic
    original_holomorphic observed_holomorphic actual_circle_budget n

theorem expected_laurent_equality_sharp_cancellation {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (radius_positive : 0 < r) (original_meromorphic : MeromorphicAt f c)
    (original_domain : AnalyticOnNhd ℂ f (closedBall c r \ {c}))
    (j : ℤ) (degree_in_scope : -1 ≤ j) :
    let a := laurentObservedCoefficient f c original_meromorphic j
    let cancelled := fun z => f z-laurentMonomial a c j z
    ∃ cancelled_meromorphic : MeromorphicAt cancelled c,
      laurentObservedCoefficient cancelled c cancelled_meromorphic j = 0 ∧
      ∀ z ∈ sphere c r, ‖cancelled z-f z‖ = ‖a‖*r^j :=
  laurent_equality_sharp_cancellation radius_positive original_meromorphic original_domain degree_in_scope

theorem expected_laurent_monomial_coefficient (a c : ℂ) (j : ℤ)
    (degree_in_scope : -1 ≤ j) (r : ℝ) (radius_positive : 0 < r) :
    laurentObservedCoefficient (laurentMonomial a c j) c
      (laurentMonomial_meromorphicAt a c j) j = a :=
  meromorphicLaurentCoefficient_monomial a c degree_in_scope radius_positive

theorem expected_laurent_monomial_circle_norm (a c : ℂ) (j : ℤ) (r : ℝ)
    (z : ℂ) (on_actual_circle : z ∈ sphere c r) :
    ‖laurentMonomial a c j z‖ = ‖a‖*r^j :=
  laurentMonomial_circle_norm a c j on_actual_circle

#print axioms Zeta23.OPICAFollowup.laurent_coefficient_error_bound
#print axioms Zeta23.OPICAFollowup.laurent_observation_survives
end Zeta23.OPICAFollowup.Validation

noncomputable section
namespace Zeta23.OPICAFollowup.Validation

theorem expected_zeta_left_line_uniform_bound : ∃ A0 : ℝ, 1 ≤ A0 ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ τ : ℝ,
      ‖riemannZeta (-(n:ℂ)+Complex.I*(τ:ℂ))‖+
        ‖deriv riemannZeta (-(n:ℂ)+Complex.I*(τ:ℂ))‖ ≤
      A0^(n+1)*((n:ℝ)+2+|τ|)^(n+2) :=
  zeta_left_line_uniform_bound

-- Includes zero ordinate and the trivial zero at -2, with the actual derivative.
theorem expected_zeta_left_trivial_zero_boundary : ∃ A0 : ℝ, 1 ≤ A0 ∧
    ‖riemannZeta (-2)‖+‖deriv riemannZeta (-2)‖ ≤ A0^3*4^4 := by
  obtain ⟨A0,hA,h⟩ := expected_zeta_left_line_uniform_bound
  refine ⟨A0,hA,?_⟩
  convert h 2 (by norm_num) 0 using 1
  all_goals norm_num

#print axioms Zeta23.OPICAFollowup.gamma_one_vertical_norm_sq
#print axioms Zeta23.OPICAFollowup.gamma_one_vertical_exp_bound
#print axioms Zeta23.OPICAFollowup.gamma_integer_vertical_exp_bound
#print axioms Zeta23.OPICAFollowup.zeta_right_halfplane_value_derivative_bound
#print axioms Zeta23.OPICAFollowup.digamma_integer_vertical_bound
#print axioms Zeta23.OPICAFollowup.zeta_reflected_value_derivative
#print axioms Zeta23.OPICAFollowup.gamma_integer_trig_bound
#print axioms Zeta23.OPICAFollowup.zeta_reflection_uniform_integer_bound
#print axioms Zeta23.OPICAFollowup.zeta_left_line_uniform_bound
end Zeta23.OPICAFollowup.Validation


noncomputable section
open MeasureTheory Complex
namespace Zeta23.OPICAFollowup.Validation

theorem expected_sourceFamily_laplace_identity (d : ℕ) :
    (∀ w : ℂ, sourceFamilyLaplace d w = (w^2-1/4)^d*CCM.nativeOriginalSourceLaplace w) ∧
    (∀ rho : zetaZeroConfig.carrier, 1/2<(rho:ℂ).re →
      sourceFamilyLaplace d ((rho:ℂ)-1/2) ≠ 0) :=
  sourceFamily_laplace_identity d

theorem expected_nativePrimeField_visiblePole (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    ∃ pole : OPICA.SimplePoleData (ℝ → ℝ),
      pole.source=CCM.nativeOriginalSource ∧ pole.center=(rho:ℂ)-1/2 ∧
      pole.field=nativePrimeTransformGerm ∧
      pole.residue=-(zeroMult (rho:ℂ):ℂ)*CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2) ∧
      Meromorphic pole.field ∧
      (∀ w : ℂ, 1/2<w.re →
        (∫ t : ℝ, Complex.exp (-w*(t:ℂ))*(CCM.nativeOriginalPrimeField t:ℂ))=pole.field w) :=
  nativePrimeField_visiblePole rho hright

theorem expected_nativePrimePole_physical_source (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) {w : ℂ} (hw : 1/2<w.re) :
    (nativePrimePoleData rho hright).source=CCM.nativeOriginalSource ∧
    (nativePrimePoleData rho hright).center=(rho:ℂ)-1/2 ∧
    (nativePrimePoleData rho hright).residue=
      -(zeroMult (rho:ℂ):ℂ)*CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2) ∧
    (∫ t : ℝ, Complex.exp (-w*(t:ℂ))*(CCM.nativeOriginalPrimeField t:ℂ))=
      (nativePrimePoleData rho hright).field w :=
  ⟨nativePrimePoleData_source rho hright,nativePrimePoleData_center rho hright,
    nativePrimePoleData_residue rho hright,nativePrimePoleData_physical_laplace rho hright hw⟩

end Zeta23.OPICAFollowup.Validation

#print axioms Zeta23.OPICAFollowup.sourceFamily_laplace_identity
#print axioms Zeta23.OPICAFollowup.nativePrimeField_visiblePole
#print axioms Zeta23.OPICAFollowup.nativePrimePoleData
#print axioms Zeta23.OPICAFollowup.actualZeta_meromorphic
#print axioms Zeta23.OPICAFollowup.nativePrimeTransformGerm_meromorphic
#print axioms Zeta23.OPICAFollowup.primeFieldFamily_physical_laplace
#print axioms Zeta23.OPICAFollowup.Validation.expected_sourceFamily_laplace_identity
#print axioms Zeta23.OPICAFollowup.Validation.expected_nativePrimeField_visiblePole
#print axioms Zeta23.OPICAFollowup.Validation.expected_nativePrimePole_physical_source

noncomputable section
namespace Zeta23.OPICAFollowup.Validation
open MeasureTheory Complex Zeta23.CCM
/- Independently stated NativeExplicitFormula consumers for aggregate Validation. -/

example : zetaZeroConfig.carrier = {rho : ℂ | IsNontrivialZero rho} := rfl
example (rho : ℂ) : zetaZeroConfig.mult rho = (analyticOrderAt riemannZeta rho).toNat := rfl

theorem expected_native_zero_count_summability :
    Summable (fun rho : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult rho : ℝ) / (1 + Complex.normSq (gammaOf rho))) ∧
    Summable (fun rho : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult rho : ℝ) / (1 + ((rho : ℂ).im)^2)) :=
  native_zero_count_summability

example : nativeZeroDisplacementSup =
    sSup (insert 0 (Set.range (fun rho : zetaZeroConfig.carrier =>
      max ((rho : ℂ).re - 1/2) 0))) := rfl

theorem expected_native_zero_sup_bounds :
    0 ≤ nativeZeroDisplacementSup ∧ nativeZeroDisplacementSup ≤ 1/2 ∧
    (∀ rho : zetaZeroConfig.carrier,
      max ((rho : ℂ).re - 1/2) 0 ≤ nativeZeroDisplacementSup) ∧
    (∀ b : ℝ, 0 ≤ b → b < nativeZeroDisplacementSup →
      ∃ rho : zetaZeroConfig.carrier, b < (rho : ℂ).re - 1/2) :=
  native_zero_sup_bounds

theorem expected_native_source_explicit_formula (d : ℕ) {t : ℝ} (ht : UniversalSinc.fixedScale < t) :
    (paperFT (fun u : ℝ => (sourceOrderFamily d (t-u) : ℂ)) (I/2) +
      paperFT (fun u : ℝ => (sourceOrderFamily d (t-u) : ℂ)) (-I/2) = 0) ∧
    Summable (fun rho : zetaZeroConfig.carrier =>
      ‖(zetaZeroConfig.mult rho : ℂ) *
        (∫ u : ℝ, Complex.exp (-((rho : ℂ)-1/2)*(u:ℂ)) *
          (sourceOrderFamily d u : ℂ)) *
        Complex.exp (((rho : ℂ)-1/2)*(t:ℂ))‖) ∧
    Summable (fun n : ℕ =>
      ‖(∫ u : ℝ, Complex.exp (-(-((2*((n:ℝ)+1)+1/2 : ℝ):ℂ))*(u:ℂ)) *
          (sourceOrderFamily d u : ℂ)) *
        Complex.exp (-((2*((n:ℝ)+1)+1/2 : ℝ):ℂ)*(t:ℂ))‖) ∧
    (nativePrimeField (sourceOrderFamily d) t : ℂ) =
      -(∑' rho : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult rho : ℂ) *
          (∫ u : ℝ, Complex.exp (-((rho : ℂ)-1/2)*(u:ℂ)) *
            (sourceOrderFamily d u : ℂ)) *
          Complex.exp (((rho : ℂ)-1/2)*(t:ℂ))) -
      (∑' n : ℕ,
        (∫ u : ℝ, Complex.exp (-(-((2*((n:ℝ)+1)+1/2 : ℝ):ℂ))*(u:ℂ)) *
          (sourceOrderFamily d u : ℂ)) *
        Complex.exp (-((2*((n:ℝ)+1)+1/2 : ℝ):ℂ)*(t:ℂ))) := by
  exact native_source_explicit_formula d ht

#print axioms native_zero_count_summability
#print axioms native_zero_sup_bounds
#print axioms native_source_explicit_formula

example (n : ℕ) : riemannZeta (1/2-(2*((n:ℝ)+1)+1/2 : ℝ)) = 0 :=
  nativeTrivialZeroDecay_zeta_zero n
end Zeta23.OPICAFollowup.Validation


noncomputable section
open Complex
namespace Zeta23.OPICAFollowup.Validation

theorem expected_nativeGenerator_unit_or_completion (g : NativeGenerator)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    (∀ z : ℂ, g.multiplier z=g.unitMultiplier z*riemannZeta (z+1/2)^g.completionCount) ∧
    AnalyticAt ℂ g.unitMultiplier ((rho:ℂ)-1/2) ∧
    g.unitMultiplier ((rho:ℂ)-1/2) ≠ 0 ∧
    (∀ Y r : ℕ, (NativeGenerator.residualPower Y r).multiplier ((rho:ℂ)-1/2)=1) :=
  nativeGenerator_unit_or_completion g rho hright

theorem expected_source_generator_unit (d : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ (fun z : ℂ => (z^2-1/4)^d) ((rho:ℂ)-1/2) ∧
    (((rho:ℂ)-1/2)^2-1/4)^d ≠ 0 :=
  ⟨(NativeGenerator.sourceDerivative d).unit_analytic rho hright,
    (NativeGenerator.sourceDerivative d).unit_ne_zero rho hright⟩

theorem expected_delay_generator_unit (tau : ℝ) (htau : 0≤tau)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(tau:ℂ)*z)) ((rho:ℂ)-1/2) ∧
    Complex.exp (-(tau:ℂ)*((rho:ℂ)-1/2)) ≠ 0 :=
  ⟨(NativeGenerator.delay tau htau).unit_analytic rho hright,
    (NativeGenerator.delay tau htau).unit_ne_zero rho hright⟩

theorem expected_finiteEuler_generator_units (Q : ℕ) (hQ : 0<Q)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ (finiteEulerMultiplier Q) ((rho:ℂ)-1/2) ∧
    finiteEulerMultiplier Q ((rho:ℂ)-1/2) ≠ 0 ∧
    AnalyticAt ℂ (fun z => (finiteEulerMultiplier Q z)⁻¹) ((rho:ℂ)-1/2) ∧
    (finiteEulerMultiplier Q ((rho:ℂ)-1/2))⁻¹ ≠ 0 :=
  ⟨(NativeGenerator.finiteEuler Q hQ).unit_analytic rho hright,
    (NativeGenerator.finiteEuler Q hQ).unit_ne_zero rho hright,
    (NativeGenerator.inverseFiniteEuler Q hQ).unit_analytic rho hright,
    (NativeGenerator.inverseFiniteEuler Q hQ).unit_ne_zero rho hright⟩

theorem expected_rational_generator_units (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ (fun z : ℂ => (z+(a:ℂ))/(z+(b:ℂ))) ((rho:ℂ)-1/2) ∧
    (((rho:ℂ)-1/2+(a:ℂ))/((rho:ℂ)-1/2+(b:ℂ))) ≠ 0 ∧
    AnalyticAt ℂ (fun z : ℂ => (z+(b:ℂ))/(z+(a:ℂ))) ((rho:ℂ)-1/2) ∧
    (((rho:ℂ)-1/2+(b:ℂ))/((rho:ℂ)-1/2+(a:ℂ))) ≠ 0 :=
  ⟨(NativeGenerator.rational a b ha hb).unit_analytic rho hright,
    (NativeGenerator.rational a b ha hb).unit_ne_zero rho hright,
    (NativeGenerator.inverseRational a b ha hb).unit_analytic rho hright,
    (NativeGenerator.inverseRational a b ha hb).unit_ne_zero rho hright⟩

theorem expected_residual_generator_unit (Y r : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ (fun z : ℂ => (1-riemannZeta (z+1/2)*truncatedMoebiusMultiplier Y z)^r)
      ((rho:ℂ)-1/2) ∧
    (1-riemannZeta (rho:ℂ)*truncatedMoebiusMultiplier Y ((rho:ℂ)-1/2))^r=1 := by
  refine ⟨(NativeGenerator.residualPower Y r).unit_analytic rho hright,?_⟩
  simpa only [NativeGenerator.multiplier,sub_add_cancel] using
    NativeGenerator.residual_value_one Y r rho

theorem expected_completion_generator_unit (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    (∀ z : ℂ, NativeGenerator.completion.multiplier z=
      CCM.nativeCompletionRationalMultiplier z*riemannZeta (z+1/2)) ∧
    AnalyticAt ℂ CCM.nativeCompletionRationalMultiplier ((rho:ℂ)-1/2) ∧
    CCM.nativeCompletionRationalMultiplier ((rho:ℂ)-1/2) ≠ 0 :=
  ⟨fun _ => rfl,NativeGenerator.completion.unit_analytic rho hright,
    NativeGenerator.completion.unit_ne_zero rho hright⟩

end Zeta23.OPICAFollowup.Validation

#print axioms Zeta23.OPICAFollowup.nativeGenerator_unit_or_completion
#print axioms Zeta23.OPICAFollowup.Validation.expected_nativeGenerator_unit_or_completion
#print axioms Zeta23.OPICAFollowup.Validation.expected_source_generator_unit
#print axioms Zeta23.OPICAFollowup.Validation.expected_delay_generator_unit
#print axioms Zeta23.OPICAFollowup.Validation.expected_finiteEuler_generator_units
#print axioms Zeta23.OPICAFollowup.Validation.expected_rational_generator_units
#print axioms Zeta23.OPICAFollowup.Validation.expected_residual_generator_unit
#print axioms Zeta23.OPICAFollowup.Validation.expected_completion_generator_unit

noncomputable section
open MeasureTheory
namespace Zeta23.OPICAFollowup.Validation

theorem expected_forwardKernel_left_contour_budget (d ell k : ℕ) :
    ∃ C D : ℝ, ∃ B : ℕ, 0 < C ∧ 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n →
      Integrable (fun τ : ℝ => (forwardLeftContour n τ)^k*
        forwardKernelTransformGerm d ell (forwardLeftContour n τ)) ∧
      (∫ τ : ℝ, ‖(forwardLeftContour n τ)^k*
        forwardKernelTransformGerm d ell (forwardLeftContour n τ)‖) ≤
        C*Real.exp (D*(n:ℝ))*(n:ℝ)^(2*(ell+1)*n+B) :=
  forwardKernel_left_contour_budget d ell k

-- The source in the contour is its literal physical compact-source integral.
theorem expected_forward_contour_literal_source (d ell k n : ℕ) (τ : ℝ) :
    forwardContourIntegrand d ell k n τ =
      let z : ℂ := -(((n:ℝ)+1/2):ℂ)+Complex.I*(τ:ℂ)
      z^k*(-(∫ u : ℝ, Complex.exp (-z*(u:ℂ))*(sourceOrderFamily d u:ℂ))*
        riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2)) := rfl

theorem expected_forward_contour_zero_degree_moment {c : ℝ} (hc : 0 < c) :
    (∫ τ : ℝ, Real.exp (-c*Real.sqrt |τ|)) = 4/c^2 := by
  simpa using sqrt_decay_moment_integral hc 0

#print axioms Zeta23.OPICAFollowup.sqrt_decay_moment_integral
#print axioms Zeta23.OPICAFollowup.shifted_sqrt_decay_integral_bound
#print axioms Zeta23.OPICAFollowup.fixed_linear_factorial_envelope
#print axioms Zeta23.OPICAFollowup.forwardContour_pointwise_budget
#print axioms Zeta23.OPICAFollowup.forwardKernel_left_contour_budget
end Zeta23.OPICAFollowup.Validation

noncomputable section
open Complex
namespace Zeta23.OPICAFollowup.Validation
theorem expected_realCutoff_physical_transform (Y : ℝ) (hY : 1≤Y) (r : ℕ)
    (state : NativeCausalState) :
    (∀ f : ℝ → ℂ, ∀ t : ℝ,
      (∑' n : ℕ, if (n:ℝ)≤Y then
        (ArithmeticFunction.moebius n:ℂ)*(CCM.nativeIntegerCoefficient n:ℂ)*f (t-Real.log n) else 0) =
      ∑ n ∈ Finset.range (Nat.floor Y+1),
        (ArithmeticFunction.moebius n:ℂ)*(CCM.nativeIntegerCoefficient n:ℂ)*f (t-Real.log n)) ∧
    (∀ z : ℂ, (NativeGenerator.residualPowerReal Y r).multiplier z=
      (1-riemannZeta (z+1/2)*truncatedMoebiusRealMultiplier Y z)^r) ∧
    (∃ S : ℝ, ∀ z : ℂ, S<z.re →
      (state.residualPowerRealAction Y r).laplace z=
        (1-riemannZeta (z+1/2)*truncatedMoebiusRealMultiplier Y z)^r*state.laplace z) :=
  ⟨fun f t => truncatedMoebiusReal_physical_history Y (by linarith) f t,
    NativeGenerator.residualPowerReal_multiplier Y (by linarith) r,
    state.laplace_residualPowerRealAction Y (by linarith) r⟩

theorem expected_nonintegral_residual_cutoff (r : ℕ) (state : NativeCausalState)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    (∀ z : ℂ, (NativeGenerator.residualPowerReal (3/2) r).multiplier z=
      (1-riemannZeta (z+1/2)*truncatedMoebiusRealMultiplier (3/2) z)^r) ∧
    AnalyticAt ℂ (NativeGenerator.residualPowerReal (3/2) r).unitMultiplier ((rho:ℂ)-1/2) ∧
    (NativeGenerator.residualPowerReal (3/2) r).unitMultiplier ((rho:ℂ)-1/2) ≠ 0 ∧
    (∃ S : ℝ, ∀ z : ℂ, S<z.re →
      (state.residualPowerRealAction (3/2) r).laplace z=
        (1-riemannZeta (z+1/2)*truncatedMoebiusRealMultiplier (3/2) z)^r*state.laplace z) :=
  ⟨NativeGenerator.residualPowerReal_multiplier (3/2) (by norm_num) r,
    (NativeGenerator.residualPowerReal (3/2) r).unit_analytic rho hright,
    (NativeGenerator.residualPowerReal (3/2) r).unit_ne_zero rho hright,
    state.laplace_residualPowerRealAction (3/2) (by norm_num) r⟩


#print axioms expected_realCutoff_physical_transform
#print axioms expected_nonintegral_residual_cutoff
end Zeta23.OPICAFollowup.Validation

open Complex MeasureTheory
namespace Zeta23.OPICAFollowup.Validation
theorem expected_nativeGenerator_transform (g : NativeGenerator) (state : NativeCausalState) :
    (∃ S : ℝ, ∀ z : ℂ, S<z.re →
      (∀ term∈state, Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t)) ∧
      (∀ term∈g.act state, Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t)) ∧
      (g.act state).laplace z=g.multiplier z*state.laplace z) ∧
    (∀ d : ℕ, ∀ test : NativeCompactTest,
      ((NativeGenerator.sourceDerivative d).act (primeFamilyCausalState 0)).applyTest test=
        (primeFamilyCausalState d).applyTest test) :=
  nativeGenerator_transform g state

theorem expected_literal_source_differentiation (d : ℕ) (test : NativeCompactTest) :
    ((NativeGenerator.sourceDerivative d).act (primeFamilyCausalState 0)).applyTest test=
      ∫ t : ℝ, (CCM.nativePrimeField (sourceOrderFamily d) t:ℂ)*test t := by
  rw [primeFamilyCausalState_sourceDerivative_applyTest,primeFamilyCausalState_applyTest]
  rfl

theorem expected_arbitrary_history_distributional_P (state : NativeCausalState)
    (test : NativeCompactTest) :
    state.sourceDifferentialAction.applyTest test=
      state.applyTest (test.derivative.derivative.add (test.constMul (-(1/4:ℂ)))) :=
  state.applyTest_sourceDifferentialAction test

theorem expected_actual_completion_convolution (f : NativeRegularCausal) (t : ℝ) :
    nativeCompletionCausalKernel.convolve f t=
      ∫ s : ℝ, (CCM.nativePositiveCompletion s:ℂ)*f (t-s) := rfl

theorem expected_actual_inverseEuler (Q : ℕ) (state : NativeCausalState) :
    ∃ S : ℝ, ∀ z : ℂ, S<z.re →
      (state.inverseFiniteEulerAction Q).laplace z=
        (∏ p ∈ Q.primeFactors, (1-Complex.exp (-(z+1/2)*(Real.log p:ℂ))))⁻¹*state.laplace z :=
  state.laplace_inverseFiniteEulerAction Q

end Zeta23.OPICAFollowup.Validation

open Complex MeasureTheory
namespace Zeta23.OPICAFollowup.Validation
theorem expected_forwardKernel_physical_laplace (d ell : ℕ) (hd : ell≤d) :
    (∀ z : ℂ, 1/2<z.re →
      Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(forwardKernel d ell t:ℂ)) ∧
      (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(forwardKernel d ell t:ℂ))=
        -sourceFamilyLaplace d z*riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2)) ∧
    (∀ z : ℂ, AnalyticAt ℂ (forwardKernelEntireContinuation d ell) z) ∧
    (∀ z : ℂ, z≠1/2 →
      forwardKernelEntireContinuation d ell z=
        -sourceFamilyLaplace d z*riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2)) :=
  forwardKernel_physical_laplace d ell hd

theorem expected_forward_diagonal_removable_value (d : ℕ) :
    forwardKernelEntireContinuation d d (1/2)=
      CCM.UniversalSinc.product CCM.UniversalSinc.fixedScale (Complex.I*(1/2)) ∧
    forwardKernelEntireContinuation d d (1/2) ≠ 0 ∧
    forwardKernelTransformGerm d d (1/2)=0 ∧
    forwardKernelEntireContinuation d d (1/2) ≠ forwardKernelTransformGerm d d (1/2) :=
  ⟨forwardKernelEntireContinuation_diagonal_half d,
    forwardKernelEntireContinuation_diagonal_half_ne_zero d,
    forwardKernelTransformGerm_half d d,
    forwardKernelEntireContinuation_diagonal_half_ne_raw d⟩

end Zeta23.OPICAFollowup.Validation

open Complex MeasureTheory Zeta23.CCM
namespace Zeta23.OPICAFollowup.Validation

/- Independent full Appendix order-norm and actual-field consumers. -/
 theorem expected_source_order_uniform_norms :
    ∃ C : ℝ, 0<C ∧ ∀ d : ℕ,
      (∀ k : ℕ, k≤2 →
        eLpNorm (iteratedDeriv k (sourceOrderFamily d)) (⊤:ENNReal) volume ≤
          ENNReal.ofReal (Real.exp (C*((d:ℝ)+1)*Real.log ((d:ℝ)+2))) ∧
        (eLpNorm (iteratedDeriv k (sourceOrderFamily d)) (⊤:ENNReal) volume).toReal +
          (∫ u : ℝ, |iteratedDeriv k (sourceOrderFamily d) u|) ≤
            Real.exp (C*((d:ℝ)+1)*Real.log ((d:ℝ)+2))) ∧
      MemLp (nativeIntegerDriveField (sourceOrderFamily d)) 2 volume ∧
      ‖(integerDriveFamily_memLp_two d).toLp (nativeIntegerDriveField (sourceOrderFamily d))‖ ≤
        Real.exp (C*((d:ℝ)+1)*Real.log ((d:ℝ)+2)) ∧
      (∀ t : ℝ, (∫ x : ℝ, if 0<x then Real.log x/Real.sqrt x*
        sourceOrderFamily d (t-Real.log x) else 0)=0) := by
  obtain ⟨C,hC,h⟩ := source_order_uniform_norms
  refine ⟨C,hC,fun d => ?_⟩
  have hd := h d
  refine ⟨fun k hk => ⟨(hd.1 k hk).2.1,(hd.1 k hk).2.2⟩,hd.2.1,?_,?_⟩
  · exact hd.2.2.1
  · exact hd.2.2.2

 theorem expected_native_field_theta_envelope :
    ∃ C : ℝ, 0<C ∧ ∃ Cd : ℕ → ℝ, ∀ d : ℕ,
      0<Cd d ∧
      (∀ t : ℝ, 0≤t → |nativePrimeField (sourceOrderFamily d) t| ≤
        Cd d*Real.exp ((sSup (insert 0 (Set.range
          (fun rho : zetaZeroConfig.carrier => max ((rho:ℂ).re-1/2) 0))))*t)) ∧
      Real.log (1+Cd d) ≤ C*((d:ℝ)+1)*Real.log ((d:ℝ)+2) := by
  obtain ⟨C,hC,h⟩ := native_field_theta_envelope
  refine ⟨C,hC,nativeFieldOrderConstant,fun d => ?_⟩
  exact h d

#print axioms source_order_uniform_norms
#print axioms native_field_theta_envelope
#print axioms expected_source_order_uniform_norms
#print axioms expected_native_field_theta_envelope
#print axioms uniform_nativeOrderLogDriveSummand_integral_zero
#print axioms integerDriveFamilyL2_norm_eq

end Zeta23.OPICAFollowup.Validation


open Filter Complex Set MeasureTheory
open scoped Topology BigOperators

open Filter Complex Set MeasureTheory
open scoped Topology BigOperators
namespace Zeta23.OPICAFollowup.Validation

theorem expected_nativeWord_corrected_transform (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    (∃ S : ℝ, wordHistorySafeThreshold w history≤S ∧ 1/2≤S ∧ ∀ z : ℂ, S<z.re →
      (∀ term∈nativeWordCausalState w rho history,
        Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t)) ∧
      (nativeWordCausalState w rho history).laplace z=nativeWordTransformedField w rho history z) ∧
    MeromorphicAt (nativeWordTransformedField w rho history) ((rho:ℂ)-1/2) ∧
    (∀ z : ℂ, nativeWordCorrectedField w rho history z=
      wordUnitFactor w z*riemannZeta (z+1/2)^wordCompletionCount w*nativePrimeTransformGerm z) ∧
    wordUnitFactor w ((rho:ℂ)-1/2)≠0 ∧
    (nativeWordPrimePole rho hright).source=Zeta23.CCM.nativeOriginalSource ∧
    primeFieldFamily 0=Zeta23.CCM.nativeOriginalPrimeField ∧
    (∀ d : ℕ, ∀ test : NativeCompactTest,
      ((NativeGenerator.sourceDerivative d).act (primeFamilyCausalState 0)).applyTest test=
        (primeFamilyCausalState d).applyTest test) :=
  nativeWord_corrected_transform w rho hright history

theorem expected_nativeWord_order_and_leading (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    MeromorphicAt (nativeWordTransformedField w rho history) ((rho:ℂ)-1/2) ∧
    meromorphicOrderAt (nativeWordCorrectedField w rho history) ((rho:ℂ)-1/2)=
      (((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1:ℤ) ∧
    (nativeWordCorrectedField w rho history =ᶠ[𝓝[≠] ((rho:ℂ)-1/2)]
      fun z => (z-((rho:ℂ)-1/2))^
        (((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1)*nativeWordGermFactor w rho hright z) ∧
    AnalyticAt ℂ (nativeWordGermFactor w rho hright) ((rho:ℂ)-1/2) ∧
    nativeWordGermFactor w rho hright ((rho:ℂ)-1/2)=
      -(zeroMult (rho:ℂ):ℂ)*Zeta23.CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2)*
        wordUnitFactor w ((rho:ℂ)-1/2)*
          (iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)/
            ((zeroMult (rho:ℂ)).factorial:ℂ))^wordCompletionCount w ∧
    nativeWordLeadingCoefficient w rho≠0 ∧
    Tendsto (fun z => (z-((rho:ℂ)-1/2))^
      (-(((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1))*
        nativeWordCorrectedField w rho history z)
      (𝓝[≠] ((rho:ℂ)-1/2)) (𝓝 (nativeWordLeadingCoefficient w rho)) ∧
    (wordCompletionCount w=0 → Tendsto
      (fun z => (z-((rho:ℂ)-1/2))*nativeWordCorrectedField w rho history z)
      (𝓝[≠] ((rho:ℂ)-1/2)) (𝓝 (nativeWordLeadingCoefficient w rho))) :=
  nativeWord_order_and_leading w rho hright history

theorem expected_nativeWord_first_nonzero_derivative (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) (hp : 0<wordCompletionCount w) :
    (nativeWordCorrectedField w rho history =ᶠ[𝓝[≠] ((rho:ℂ)-1/2)]
      nativeWordRegularRepresentative w rho hright) ∧
    AnalyticAt ℂ (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2) ∧
    (∀ j : ℕ, j<wordCompletionCount w*zeroMult (rho:ℂ)-1 →
      iteratedDeriv j (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2)=0) ∧
    iteratedDeriv (wordCompletionCount w*zeroMult (rho:ℂ)-1)
      (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2)=
        ((wordCompletionCount w*zeroMult (rho:ℂ)-1).factorial:ℂ)*
          (-(zeroMult (rho:ℂ):ℂ)*Zeta23.CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2)*
            wordUnitFactor w ((rho:ℂ)-1/2)*
              (iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)/
                ((zeroMult (rho:ℂ)).factorial:ℂ))^wordCompletionCount w) ∧
    iteratedDeriv (wordCompletionCount w*zeroMult (rho:ℂ)-1)
      (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2)≠0 :=
  nativeWord_first_nonzero_derivative w rho hright history hp

theorem expected_nativeWord_factor_costs (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    (∀ g : NativeGenerator, |Real.log ‖g.unitMultiplier ((rho:ℂ)-1/2)‖|≤
      g.leadingLogCost ((rho:ℂ)-1/2)) ∧
    |Real.log ‖nativeWordLeadingCoefficient w rho‖|≤
      |Real.log ‖-(zeroMult (rho:ℂ):ℂ)*Zeta23.CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2)‖|+
        wordExplicitLogCost w ((rho:ℂ)-1/2)+(wordCompletionCount w:ℝ)*
          |Real.log ‖iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)/
            ((zeroMult (rho:ℂ)).factorial:ℂ)‖| ∧
    (0<wordCompletionCount w → Real.log ‖iteratedDeriv (wordCompletionCount w*zeroMult (rho:ℂ)-1)
      (nativeWordRegularRepresentative w rho hright) ((rho:ℂ)-1/2)‖-
        Real.log ‖nativeWordLeadingCoefficient w rho‖=
          Real.log ((wordCompletionCount w*zeroMult (rho:ℂ)-1).factorial:ℝ)) ∧
    Real.log ((wordCompletionCount w*zeroMult (rho:ℂ)-1).factorial:ℝ)≤
      (wordCompletionCount w*zeroMult (rho:ℂ)-1:ℕ)*
        Real.log ((wordCompletionCount w*zeroMult (rho:ℂ)-1:ℕ)+2:ℝ) :=
  nativeWord_factor_costs w rho hright

example (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) (history : NativeWordHistory ((rho:ℂ)-1/2)) (hp : 0<wordCompletionCount w)
    (hdegree : wordCompletionCount w*zeroMult (rho:ℂ)=1) :
    nativeWordRegularRepresentative w rho hright ((rho:ℂ)-1/2)≠0 := by
  simpa only [hdegree,Nat.sub_self,iteratedDeriv_zero] using
    (nativeWord_first_nonzero_derivative w rho hright history hp).2.2.2.2


end Zeta23.OPICAFollowup.Validation

open Complex Filter MeasureTheory
open scoped Topology
namespace Zeta23.OPICAFollowup.Validation

example (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    Tendsto (fun z => (z-((rho:ℂ)-1/2))*nativeWordCorrectedField [] rho history z)
      (𝓝[≠] ((rho:ℂ)-1/2))
      (𝓝 (-(zeroMult (rho:ℂ):ℂ)*Zeta23.CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2))) := by
  rcases nativeWord_order_and_leading [] rho hright history with ⟨_,_,_,_,_,_,_,hzero⟩
  simpa only [nativeWordLeadingCoefficient,wordCompletionCount,wordUnitFactor,pow_zero,mul_one] using
    hzero rfl

example (Y : ℝ) (hY : 1≤Y) (r : ℕ) (z : ℂ) :
    wordMultiplier [NativeGenerator.residualPowerReal Y r] z=
      (1-riemannZeta (z+1/2)*truncatedMoebiusRealMultiplier Y z)^r := by
  simp only [wordMultiplier,mul_one]
  exact NativeGenerator.residualPowerReal_multiplier Y (by linarith) r z

end Zeta23.OPICAFollowup.Validation


open Filter Complex Set MeasureTheory
open scoped Topology
namespace Zeta23.OPICAFollowup.Validation

/-- A common global continuation domain is sufficient for this additional
    global statement and is not required by the local primary roots. -/
theorem expected_nativeWord_global_continuation (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (history : NativeWordHistory ((rho:ℂ)-1/2))
    (D : NativeWordHistoryContinuationDomain w history) :
    MeromorphicOn (nativeWordTransformedField w rho history) D.domain :=
  nativeWordTransformedField_meromorphicOn w rho history D

end Zeta23.OPICAFollowup.Validation

open Complex Filter MeasureTheory
open scoped Topology
namespace Zeta23.OPICAFollowup.Validation

example (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    Tendsto (fun z => (z-((rho:ℂ)-1/2))*nativeWordCorrectedField [] rho history z)
      (𝓝[≠] ((rho:ℂ)-1/2))
      (𝓝 (-(zeroMult (rho:ℂ):ℂ)*Zeta23.CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2))) := by
  rcases nativeWord_order_and_leading [] rho hright history with ⟨_,_,_,_,_,_,_,hzero⟩
  simpa only [nativeWordLeadingCoefficient,wordCompletionCount,wordUnitFactor,pow_zero,mul_one] using
    hzero rfl

example (Y : ℝ) (hY : 1≤Y) (r : ℕ) (z : ℂ) :
    wordMultiplier [NativeGenerator.residualPowerReal Y r] z=
      (1-riemannZeta (z+1/2)*truncatedMoebiusRealMultiplier Y z)^r := by
  simp only [wordMultiplier,mul_one]
  exact NativeGenerator.residualPowerReal_multiplier Y (by linarith) r z

end Zeta23.OPICAFollowup.Validation




open Filter Complex Set MeasureTheory Metric
open scoped Topology BigOperators

open Filter Complex Set MeasureTheory Metric
open scoped Topology BigOperators
namespace Zeta23.OPICAFollowup.Validation

theorem expected_nativeWord_contour_consumer (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2))
    (raw correction recovery : ℂ → ℂ) (r Eraw Ecorrection Erecovery : ℝ)
    (hr : 0<r)
    (hg : MeromorphicAt (nativeWordObservedField raw correction recovery) ((rho:ℂ)-1/2))
    (hfd : AnalyticOnNhd ℂ (nativeWordCorrectedField w rho history)
      (closedBall ((rho:ℂ)-1/2) r \ {((rho:ℂ)-1/2)}))
    (hgd : AnalyticOnNhd ℂ (nativeWordObservedField raw correction recovery)
      (closedBall ((rho:ℂ)-1/2) r \ {((rho:ℂ)-1/2)}))
    (hraw : ContourErrorBudget (nativeWordTransformedField w rho history) raw ((rho:ℂ)-1/2) r Eraw)
    (hcorrection : ContourErrorBudget (wordCorrection w history) correction ((rho:ℂ)-1/2) r Ecorrection)
    (hrecovery : ∀ z∈sphere ((rho:ℂ)-1/2) r, ‖recovery z‖≤Erecovery)
    (hstrict : Eraw+Ecorrection+Erecovery<‖nativeWordLeadingCoefficient w rho‖*
      r^(((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1)) :
    (∃ S : ℝ, wordHistorySafeThreshold w history≤S ∧ 1/2≤S ∧ ∀ z : ℂ, S<z.re →
      (∀ term∈nativeWordCausalState w rho history,
        Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t)) ∧
      (nativeWordCausalState w rho history).laplace z=nativeWordTransformedField w rho history z) ∧
    laurentObservedCoefficient (nativeWordCorrectedField w rho history) ((rho:ℂ)-1/2)
      (nativeWordCorrectedField_meromorphicAt w rho hright history)
        (((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1)=nativeWordLeadingCoefficient w rho ∧
    ‖laurentObservedCoefficient (nativeWordObservedField raw correction recovery) ((rho:ℂ)-1/2) hg
      (((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1)-nativeWordLeadingCoefficient w rho‖≤
        r^(-(((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1))*(Eraw+Ecorrection+Erecovery) ∧
    laurentObservedCoefficient (nativeWordObservedField raw correction recovery) ((rho:ℂ)-1/2) hg
      (((wordCompletionCount w*zeroMult (rho:ℂ):ℕ):ℤ)-1)≠0 :=
  nativeWord_contour_consumer w rho hright history raw correction recovery r Eraw Ecorrection Erecovery
    hr hg hfd hgd hraw hcorrection hrecovery hstrict


end Zeta23.OPICAFollowup.Validation





#print axioms Zeta23.OPICAFollowup.nativeGenerator_transform
#print axioms Zeta23.OPICAFollowup.forwardKernel_physical_laplace

open Complex MeasureTheory
namespace Zeta23.OPICAFollowup.Validation
theorem expected_literal_forward_iteratedDeriv (d ell k : ℕ) {z : ℂ} (hz : 1/2<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*
      Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t))=
      z^k*(-sourceFamilyLaplace d z*riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2)) :=
  forwardKernel_iteratedDeriv_physical_laplace d ell k hz

theorem expected_literal_forward_derivative_entire (d ell k : ℕ) (hd : ell≤d)
    {z : ℂ} (hz : 1/2<z.re) :
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t))=
      z^k*forwardKernelEntireContinuation d ell z :=
  forwardKernel_iteratedDeriv_laplace_entire d ell k hd hz

theorem expected_literal_forward_smooth_positive_gap (d ell k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (forwardKernel d ell) ∧
    0<Real.log 2-CCM.UniversalSinc.fixedScale ∧
    (∀ t : ℝ, t<Real.log 2-CCM.UniversalSinc.fixedScale →
      iteratedDeriv k (forwardKernel d ell) t=0) :=
  ⟨forwardKernel_contDiff d ell,nativeCausalGap_pos,
    fun _t ht => forwardKernel_iteratedDeriv_zero_before d ell k ht⟩

end Zeta23.OPICAFollowup.Validation

open Complex MeasureTheory
namespace Zeta23.OPICAFollowup.Validation

theorem expected_fractional_strip_zeta_control (a b : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ (σ τ : ℝ), a≤σ → σ≤b → 2≤|τ| →
      ‖riemannZeta ((σ:ℂ)+(τ:ℂ)*I)‖+‖deriv riemannZeta ((σ:ℂ)+(τ:ℂ)*I)‖ ≤
        C*(1+|τ|)^N := zeta_fixed_strip_polynomial_value_derivative_bound a b

theorem expected_positive_fractional_gamma_control :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ (σ τ : ℝ), (1/2:ℝ)≤σ → σ≤2 →
      ‖Complex.Gamma ((σ:ℂ)+I*(τ:ℂ))‖ ≤
        C*(1+|τ|)^N*Real.exp (-(Real.pi*|τ|)/2) :=
  gamma_positive_fixed_strip_exp_bound (by norm_num) (by norm_num)

#print axioms expected_fractional_strip_zeta_control
#print axioms expected_positive_fractional_gamma_control
#print axioms bilateralLaplace_inverse
#print axioms integer_contour_saddle_decay
#print axioms norm_bilateralLaplace_inverse_le

end Zeta23.OPICAFollowup.Validation


noncomputable section
open Complex MeasureTheory
namespace Zeta23.OPICAFollowup.Validation

theorem expected_forwardKernel_double_exp_decay (d ell k : ℕ) (hd : ell≤d) :
    ∃ A c : ℝ, 0<A ∧ 0<c ∧ ∀ t : ℝ, 0≤t →
      |iteratedDeriv k (forwardKernel d ell) t| ≤
        A*Real.exp (-c*Real.exp (t/(2*((ell:ℝ)+1)))) :=
  forwardKernel_double_exp_decay d ell k hd

theorem expected_actual_integer_drive_double_exp_decay (d k : ℕ) :
    ∃ A c : ℝ, 0<A ∧ 0<c ∧ ∀ t : ℝ, 0≤t →
      |iteratedDeriv k (CCM.nativeIntegerDriveField (sourceOrderFamily d)) t| ≤
        A*Real.exp (-c*Real.exp (t/2)) := by
  simpa only [forwardKernel,integerDriveFamily,Nat.cast_zero,zero_add,mul_one] using
    forwardKernel_double_exp_decay d 0 k (Nat.zero_le d)

theorem expected_forward_all_derivatives_at_zero (d ell k : ℕ) :
    iteratedDeriv k (forwardKernel d ell) 0=0 :=
  forwardKernel_iteratedDeriv_zero_before d ell k nativeCausalGap_pos

#print axioms forwardKernel_double_exp_decay
#print axioms forwardKernel_iteratedDeriv_contour_formula
#print axioms forwardKernel_iteratedDeriv_contour_norm
#print axioms forwardEntire_fixed_strip_majorant
#print axioms forwardEntire_vertical_line_shift
#print axioms expected_forwardKernel_double_exp_decay
#print axioms expected_actual_integer_drive_double_exp_decay
#print axioms expected_forward_all_derivatives_at_zero

end Zeta23.OPICAFollowup.Validation


/-! CONTINUATION INDEPENDENT CONSUMERS: three full primary types and actual-domain supporting checks. Full100 acceptance remains closed. -/


/-! Independently stated expected-type and actual-source consumers.
These are not additions to the normative registry or a replacement for its
complete Validation module. Compiler status is recorded in adjacent logs. -/
noncomputable section
open Set MeasureTheory Finset
open Zeta23.OPICAFollowup
namespace OPICAContinuationChecks

theorem expected_log_slack_native_decomposition (r d : ℕ) (hr : 2≤r) (hd : r-1≤d)
    (C eta K : ℝ) (hC : 1<C) (heta : 0≤eta)
    (hK : C+(r:ℝ)*eta+2*(r:ℝ)<K) :
    ∃ T0 : ℝ, 1≤T0 ∧ ∀ T : ℝ, T0≤T → ∀ Q : ℕ, Squarefree Q → (Q:ℝ)≤T^eta →
      ∀ t∈Icc (T-C*Real.log T) T,
        primeFieldFamily d t=typeIField d r Q (logSlackY r K T) t+
          balancedField d r Q (logSlackY r K T) t ∧
        balancedField d r Q (logSlackY r K T) t=
          balancedTupleHistory d r Q (logSlackY r K T) (logSlackZ r K T) T t ∧
        (∀ n : ℕ, ∀ w∈Nat.finMulAntidiag r n,
          (∏ i, (ArithmeticFunction.moebius (w i):ℝ))/Real.sqrt (n:ℝ)*
            paletteForwardKernel d (r-1) Q (t-Real.log n)≠0 →
          (∏ i, (w i:ℝ))≤Real.exp (t-nativeCausalGap)) := by
  exact log_slack_native_decomposition r d hr hd C eta K hC heta hK

theorem expected_log_slack_typeI_error (r d : ℕ) (hr : 2 ≤ r) (hd : r-1 ≤ d)
    (C eta K : ℝ) (hC : 1 < C) (heta : 0 ≤ eta)
    (hK : C+(r:ℝ)*eta+2*(r:ℝ) < K) :
    ∃ C1 c T0 : ℝ, 0 < C1 ∧ 0 < c ∧ 1 ≤ T0 ∧
      1 < (K-C-(r:ℝ)*eta)/(2*(r:ℝ)) ∧
      ∀ T : ℝ, T0 ≤ T → ∀ Q : ℕ, Squarefree Q → (Q:ℝ) ≤ T^eta →
        ∀ t ∈ Icc (T-C*Real.log T) T,
          |typeIField d r Q (logSlackY r K T) t| ≤
            C1*T^((r:ℝ)*eta)*
              Real.exp (T/2-c*T^((K-C-(r:ℝ)*eta)/(2*(r:ℝ)))) := by
  exact log_slack_typeI_error r d hr hd C eta K hC heta hK

/-- The top palette/source constants precede the horizon and every permitted
squarefree palette. This consumer does not fix an integer horizon. -/
example : ∃ A c T0 : ℝ, 0 < A ∧ 0 < c ∧ 1 ≤ T0 ∧
    ∀ T : ℝ, T0 ≤ T → ∀ Q : ℕ, Squarefree Q → (Q:ℝ) ≤ T →
      ∀ t ∈ Icc (T-2*Real.log T) T,
        |typeIField 1 2 Q (logSlackY 2 10 T) t| ≤
          A*T^(2:ℝ)*Real.exp (T/2-c*T^(3/2:ℝ)) := by
  obtain ⟨A,c,T0,hA,hc,hT0,_hp,h⟩ :=
    log_slack_typeI_error 2 1 (by norm_num) (by norm_num)
      2 1 10 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨A,c,T0,hA,hc,hT0,?_⟩
  norm_num at h ⊢
  exact h

theorem expected_fixed_two_factor_preparation : ∃ C1 c T0 : ℝ, 0 < C1 ∧ 0 < c ∧ 1 ≤ T0 ∧
    ∀ T : ℝ, T0 ≤ T → ∀ t ∈ Icc (T-2*Real.log T) T,
      logSlackY 2 8 T = Real.exp (T/2)*T^(-4:ℝ) ∧
      logSlackZ 2 8 T = Real.exp (T/2-nativeCausalGap)*T^(4:ℝ) ∧
      primeFieldFamily 1 t = typeIField 1 2 1 (logSlackY 2 8 T) t +
        balancedField 1 2 1 (logSlackY 2 8 T) t ∧
      balancedField 1 2 1 (logSlackY 2 8 T) t =
        balancedTupleHistory 1 2 1 (logSlackY 2 8 T) (logSlackZ 2 8 T) T t ∧
      |typeIField 1 2 1 (logSlackY 2 8 T) t| ≤
        C1*Real.exp (T/2-c*T^(3/2:ℝ)) ∧
      (∀ n : ℕ, ∀ w ∈ Nat.finMulAntidiag 2 n,
        (∏ i, (ArithmeticFunction.moebius (w i):ℝ))/Real.sqrt (n:ℝ)*
          paletteForwardKernel 1 1 1 (t-Real.log n) ≠ 0 →
        (∏ i, (w i:ℝ)) ≤ Real.exp (t-nativeCausalGap)) := by
  exact fixed_two_factor_preparation

/-- The whole unchanged real-cutoff family is still available; the proof is
not an integer-cutoff or source-order-zero substitute. -/
example (r d Q : ℕ) (hr : 2 ≤ r) (_hQ : 0 < Q) (Y : ℝ) (hY : 1 ≤ Y) (t : ℝ) :
    primeFieldFamily d t = typeIField d r Q Y t + balancedField d r Q Y t := by
  exact native_balanced_physical_identity d r Q hr Y hY t

example (d r Q : ℕ) (hr : 2 ≤ r) (_hQ : 0 < Q) (t : ℝ) :
    primeFieldFamily d t = typeIField d r Q (3/2) t + balancedField d r Q (3/2) t := by
  exact native_balanced_physical_identity d r Q hr (3/2) (by norm_num) t

/-- The fixed source is the actual differential image of the parent source. -/
example : sourceOrderFamily 1 = fun t : ℝ =>
    deriv (deriv Zeta23.CCM.nativeOriginalSource) t-(1/4:ℝ)*Zeta23.CCM.nativeOriginalSource t := rfl

example : primeFieldFamily 1 = Zeta23.CCM.nativePrimeField
    (fun t : ℝ => deriv (deriv Zeta23.CCM.nativeOriginalSource) t-
      (1/4:ℝ)*Zeta23.CCM.nativeOriginalSource t) := rfl

/-- The compensation is the literal finite divisor filter with its square-root weights. -/
example (d Q : ℕ) (hQ : 0<Q) (t : ℝ) : nativePaletteDrive d Q t=
    ∑ n∈Q.divisors, (ArithmeticFunction.moebius n:ℝ)/Real.sqrt (n:ℝ)*
      Zeta23.CCM.nativeIntegerDriveField (sourceOrderFamily d) (t-Real.log n) := by
  simpa only [nativePaletteDrive,integerDriveFamily,Zeta23.OPICA.moebiusPaletteCoefficient] using
    arithmeticHistoryAction_palette_finite Q hQ (integerDriveFamily d) t

#print axioms expected_log_slack_native_decomposition
#print axioms expected_log_slack_typeI_error
#print axioms expected_fixed_two_factor_preparation

#print axioms Zeta23.OPICAFollowup.forwardKernel_common_finite_tail
#print axioms Zeta23.OPICAFollowup.small_palette_block_tail_bound
#print axioms Zeta23.OPICAFollowup.logSlack_filter_mass_bound
#print axioms Zeta23.OPICAFollowup.log_slack_native_decomposition
#print axioms Zeta23.OPICAFollowup.log_slack_typeI_error
#print axioms Zeta23.OPICAFollowup.fixed_two_factor_preparation
end OPICAContinuationChecks
end


/-! Independent expected types for the auxiliary supporting continuation.
No full auxiliary primary is certified by these helpers. -/
noncomputable section
open Set MeasureTheory Polynomial
open Zeta23.OPICAFollowup
namespace OPICAContinuationChecks

example (k : ℕ) {z : ℂ} (hz : -((k:ℝ)+3/2)<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionFilter k t)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionFilter k t))=
      (z-1/2)/(∏ j ∈ Finset.range (k+2), (z+(k+1+j:ℕ)+1/2)) :=
  auxCompletionFilter_integrable_laplace k hz

example (k : ℕ) {z : ℂ} (hz : 1/2<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionKernel k t)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionKernel k t))=
      ((z-1/2)/(∏ j ∈ Finset.range (k+2), (z+(k+1+j:ℕ)+1/2)))*riemannZeta (z+1/2) :=
  auxCompletionKernel_initial_laplace k hz

example (k : ℕ) : (∫ t : ℝ, ‖auxCompletionFilter k t‖)≤2/(Nat.factorial (k+1):ℝ) :=
  auxCompletionFilter_L1_bound k

example (k j : ℕ) :
    ((k+2+j).descFactorial (k+2):ℝ)/(Nat.factorial (k+1):ℝ)=
      (j+1:ℕ)*((k+2+j).choose (k+1):ℝ) :=
  auxDensity_descFactorial_ratio k j

example (k : ℕ) :
    (∫ u : ℝ in 0..1,
      |(Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u|) ≤
      (2:ℝ)^(3*k+4) := by
  exact auxCompletionProfile_density_L1_bound k

example (k : ℕ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ u ∈ Icc (0:ℝ) 1, ‖ψ u‖ ≤ M) :
    ‖(-1:ℂ)^(k+1)*(∫ u : ℝ,
      Complex.ofReal (auxCompletionProfile k u)*iteratedDeriv (k+1) ψ u)‖ ≤
      (1+(2:ℝ)^(3*k+4))*M := by
  exact auxCompletionProfile_derivative_test_bound k ψ hψ M hM hb

example (k : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖∫ u : ℝ, Complex.ofReal (auxCompletionProfile k u)*
      Complex.exp (-((2*Real.pi*ξ:ℝ):ℂ)*Complex.I*(u:ℂ))‖ ≤
      (1+(2:ℝ)^(3*k+4))/(2*Real.pi*|ξ|)^(k+1) := by
  exact auxCompletionProfile_fourier_decay k ξ hξ

/-- Negative ordinate is not removed by an accidental positive-frequency premise. -/
example (k : ℕ) (ξ : ℝ) (hξ : ξ < 0) :
    ‖auxProfileFourierIntegral k ξ‖ ≤
      (1+(2:ℝ)^(3*k+4))/(2*Real.pi*|ξ|)^(k+1) := by
  exact auxCompletionProfile_fourier_decay k ξ (ne_of_lt hξ)

/-- k=0 still includes the endpoint atom, even though later Poisson continuity
requires k>=1. This is the actual test identity, not only a density estimate. -/
example (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (-1:ℂ)*(∫ u : ℝ, Complex.ofReal (auxCompletionProfile 0 u)*deriv ψ u) =
      (∫ u : ℝ in 0..1, Complex.ofReal ((auxProfilePolynomial 0).derivative.eval u)*ψ u) - ψ 1 := by
  simpa only [Nat.zero_add,Function.iterate_one,iteratedDeriv_one,pow_one,neg_mul,
    one_mul,sub_eq_add_neg] using auxCompletionProfile_distributional_derivative 0 ψ hψ

example (k : ℕ) : ‖(-1:ℂ)^(k+1)‖ = 1 := auxCompletionProfile_endpoint_atom_norm k

#print axioms Zeta23.OPICAFollowup.auxDensityCoefficientBudget_le
#print axioms Zeta23.OPICAFollowup.auxDensity_descFactorial_ratio
#print axioms Zeta23.OPICAFollowup.auxProfilePrimitive_expansion
#print axioms Zeta23.OPICAFollowup.auxProfileDensity_polynomial
#print axioms Zeta23.OPICAFollowup.auxCompletionProfile_density_L1_bound
#print axioms Zeta23.OPICAFollowup.auxCompletionProfile_distributional_derivative
#print axioms Zeta23.OPICAFollowup.auxCompletionProfile_derivative_test_bound
#print axioms Zeta23.OPICAFollowup.auxProfileFourierTest_iteratedDeriv
#print axioms Zeta23.OPICAFollowup.auxCompletionProfile_fourier_decay
#print axioms Zeta23.OPICAFollowup.auxCompletionFilter_integrable_laplace
#print axioms Zeta23.OPICAFollowup.auxCompletionKernel_initial_laplace
#print axioms Zeta23.OPICAFollowup.auxCompletionFilter_L1_bound
end OPICAContinuationChecks
end


/-! UNCHECKED actual-domain consumers: arbitrary locally finite measures, not
an easier globally finite ComplexMeasure replacement. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology
open Zeta23.OPICAFollowup
namespace OPICAContinuationChecks

example (mu : LocallyFiniteComplexMeasure) (K L : Set ℝ)
    (hK : IsCompact K) (hL : IsCompact L) :
    (mu.compactRestriction K hK).restrict L =
      mu.compactRestriction (K∩L) (hK.inter_right hL.isClosed) := by
  exact mu.compactRestriction_restrict K L hK hL

example (mu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K) :
    mu.totalVariation.restrict K = (mu.compactRestriction K hK).variation := by
  exact mu.totalVariation_restrict_compact K hK

example (mu : LocallyFiniteComplexMeasure) :
    mu.HasLinearGrowth ↔ Zeta23.OPICA.LinearMassGrowth mu.totalVariation := by
  exact mu.hasLinearGrowth_iff_totalVariation

example (mu nu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K)
    (f : ℝ → ℂ) (hf : Continuous f) (hs : Function.support f ⊆ K)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖f x‖ ≤ M) :
    ‖mu.integral f-nu.integral f‖ ≤
      2*M*(mu.compactRestriction K hK-nu.compactRestriction K hK).variation.real univ := by
  exact mu.compact_integral_difference_bound nu K hK f hf hs M hM hb

example {seq : ℕ → LocallyFiniteComplexMeasure} {mu : LocallyFiniteComplexMeasure}
    (h : LocalVariationConvergence seq mu) (f : ℝ → ℂ)
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun n => (seq n).integral f) atTop (𝓝 (mu.integral f)) := by
  exact h.tendsto_compact_test f hf hs

/-- Actual complex scalar restriction, including genuinely imaginary scalars. -/
example (mu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K) :
    (mu.scale Complex.I).compactRestriction K hK = Complex.I • mu.compactRestriction K hK := by
  exact mu.compactRestriction_scale Complex.I K hK

#print axioms Zeta23.OPICAFollowup.LocallyFiniteComplexMeasure.totalVariation_restrict_compact
#print axioms Zeta23.OPICAFollowup.LocallyFiniteComplexMeasure.hasLinearGrowth_iff_totalVariation
#print axioms Zeta23.OPICAFollowup.LocallyFiniteComplexMeasure.compact_integral_difference_bound
#print axioms Zeta23.OPICAFollowup.LocalVariationConvergence.tendsto_compact_test
#print axioms Zeta23.OPICAFollowup.LocallyFiniteComplexMeasure.compactRestriction_scale
end OPICAContinuationChecks
end


/-! Independent exact source/domain consumers. These do not certify the missing
scheduled logarithmic/rate primary statements. -/
noncomputable section
open Set MeasureTheory
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace OPICAContinuationChecks

example (d ell : ℕ) (hd : ell ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, |forwardKernel d ell t| ≤ A := by
  exact forwardKernel_actual_bounded d ell hd

example (r d Q : ℕ) (hr : 2 ≤ r) (hd : r-1 ≤ d) (hQ : 0 < Q)
    (Y : ℝ) (_hY : 1 ≤ Y) {T t : ℝ} (ht : t ≤ T) :
    finiteDriveField (nativeRawPaletteDrive d Q) (driveIndexBound T)
        (balancedInverseCoefficients Q Y r) t = balancedField d r Q Y t ∧
    finiteDriveField (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
        ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) t = balancedField d r Q Y t := by
  exact native_balanced_two_realizations r d Q hr hd hQ Y ht

example (r d Q : ℕ) (hr : 2 ≤ r) (hd : r-1 ≤ d) (hQ : 0 < Q)
    (Y H T : ℝ) (hY : 1 ≤ Y) (hT : 0 ≤ T) (hHT : H ≤ T) :
    highPairObservation (nativeRawPaletteDrive d Q) (driveIndexBound T)
        (balancedInverseCoefficients Q Y r) nativeMovingPrimitiveCutoff (Icc H T) -
      highPairObservation (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
        ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) nativeMovingPrimitiveCutoff (Icc H T) =
    lowPairObservation (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
        ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) nativeMovingPrimitiveCutoff (Icc H T) -
      lowPairObservation (nativeRawPaletteDrive d Q) (driveIndexBound T)
        (balancedInverseCoefficients Q Y r) nativeMovingPrimitiveCutoff (Icc H T) := by
  exact native_balanced_mask_regrouping r d Q hr hd hQ Y H T hY hT hHT

example : Measurable nativeMovingPrimitiveCutoff := nativeMovingPrimitiveCutoff_measurable

/-- Nonsquarefree product index 4 is not removed from the actual r-fold sum. -/
example (Q : ℕ) (Y : ℝ) :
    |((nativeLargeCoefficients Q Y ^ 2 : ArithmeticFunction ℝ)) 4| ≤ (divisorCount 2 4 : ℝ) := by
  exact nativeLargeCoefficients_power_abs_le_divisor Q 2 4 Y

example (B : ℝ) (d e : ℕ) : lowPrimitiveMask B d e + highPrimitiveMask B d e = 1 := by
  exact primitiveMask_add_high _ _ _

#print axioms Zeta23.OPICAFollowup.forwardKernel_actual_bounded
#print axioms Zeta23.OPICAFollowup.nativeLargeCoefficients_power_abs_le_divisor
#print axioms Zeta23.OPICAFollowup.native_balanced_two_realizations
#print axioms Zeta23.OPICAFollowup.native_balanced_low_masks_explicit
#print axioms Zeta23.OPICAFollowup.native_balanced_mask_regrouping
end OPICAContinuationChecks
end

/-! Adversarial distinction: Dirichlet convolution versus pointwise powers. -/

/-! Exact control distinguishing actual Dirichlet power from pointwise
function power at a nonsquarefree total product. -/
noncomputable section
open Zeta23.OPICAFollowup
namespace OPICAContinuationChecks

theorem large_at_one : nativeLargeCoefficients 1 (3/2) 1=0 := by
  norm_num [nativeLargeCoefficients]

theorem large_at_two : nativeLargeCoefficients 1 (3/2) 2=(-1:ℝ) := by
  norm_num [nativeLargeCoefficients,nativeInverseCoefficients,coprimeCoefficients,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

theorem large_at_four : nativeLargeCoefficients 1 (3/2) 4=0 := by
  have hmu : ArithmeticFunction.moebius 4=0 := by
    convert ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by decide : (2:ℕ)≠0) using 1 <;>
      norm_num
  norm_num [nativeLargeCoefficients,nativeInverseCoefficients,coprimeCoefficients,hmu]

theorem actual_dirichlet_square_at_four :
    (nativeLargeCoefficients 1 (3/2)^2 : ArithmeticFunction ℝ) 4=1 := by
  have hanti : (4:ℕ).divisorsAntidiagonal={(1,4),(2,2),(4,1)} := by decide
  rw [pow_two,ArithmeticFunction.mul_apply,hanti]
  norm_num [large_at_one,large_at_two,large_at_four]

theorem pointwise_square_at_four :
    ((fun n : ℕ => nativeLargeCoefficients 1 (3/2) n)^2) 4=0 := by
  change (nativeLargeCoefficients 1 (3/2) 4)^2=0
  rw [large_at_four]
  norm_num

theorem dirichlet_square_differs_from_pointwise :
    (nativeLargeCoefficients 1 (3/2)^2 : ArithmeticFunction ℝ) 4≠
      ((fun n : ℕ => nativeLargeCoefficients 1 (3/2) n)^2) 4 := by
  rw [actual_dirichlet_square_at_four,pointwise_square_at_four]
  norm_num

#print axioms actual_dirichlet_square_at_four
#print axioms pointwise_square_at_four
#print axioms dirichlet_square_differs_from_pointwise
end OPICAContinuationChecks
