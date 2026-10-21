import Zeta23.OPICAFollowup.NativeSourceFamily
import Zeta23.OPICAFollowup.SourceVerticalBounds
import Zeta23.OPICAFollowup.BalancedCoefficients
import Zeta23.OPICAFollowup.RobustLaurent
import Zeta23.OPICAFollowup.NormFirstTransfer
import Zeta23.OPICAFollowup.JointObservation
import Zeta23.OPICAFollowup.Counterexamples

/-! Partial expected-type audit: 20 of the 100 planned primary roots.
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
