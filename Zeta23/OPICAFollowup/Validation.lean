import Zeta23.OPICAFollowup

/-! UNACCEPTED explicit consumer assembly proposal. This is mechanically relocated
source, not independent review, a full compiler receipt, or release authority.
No placeholder is inserted for an absent original root. RH and Step4 remain OPEN. -/

set_option maxHeartbeats 800000

/- PRESERVED LEGACY VALIDATION; only foreign continuation helper namespace relocated. -/
section

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
namespace Zeta23.OPICAFollowup.Validation

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
end Zeta23.OPICAFollowup.Validation
end


/-! Independent expected types for the auxiliary supporting continuation.
No full auxiliary primary is certified by these helpers. -/
noncomputable section
open Set MeasureTheory Polynomial
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation

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
end Zeta23.OPICAFollowup.Validation
end


/-! UNCHECKED actual-domain consumers: arbitrary locally finite measures, not
an easier globally finite ComplexMeasure replacement. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation

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
end Zeta23.OPICAFollowup.Validation
end


/-! Independent exact source/domain consumers. These do not certify the missing
scheduled logarithmic/rate primary statements. -/
noncomputable section
open Set MeasureTheory
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation

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
end Zeta23.OPICAFollowup.Validation
end

/-! Adversarial distinction: Dirichlet convolution versus pointwise powers. -/

/-! Exact control distinguishing actual Dirichlet power from pointwise
function power at a nonsquarefree total product. -/
noncomputable section
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation

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
end Zeta23.OPICAFollowup.Validation

end
end
end
end
end
end
end
end
end
end
end
end

/- SOURCE COPY: Zeta23/OPICAFollowup/Validation.lean; SHA256 664de0cac07b933d27f741742fd93b0fa81bc77bb54b546a4d5430a9dc68609d -/
section

/-! Partial expected-type audit: 41 of the 100 planned primary roots.
This module does not assert full follow-up acceptance. -/


namespace Zeta23.OPICAFollowup.Validation
open Filter Topology
open Zeta23.OPICA

theorem FullAudit0_expected_norm_first_log_comparison {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    |Real.log (1+‖F‖^2)-Real.log (1+max q 0)| ≤
      2*Real.log (1+‖S‖)+Real.log (1+|l|) :=
  norm_first_log_comparison F S B q l hF hq

theorem FullAudit0_expected_norm_first_rate_transfer {E : Type*} [SeminormedAddCommGroup E]
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

theorem FullAudit0_expected_energy_allocation_bound {E : Type*} [SeminormedAddCommGroup E]
    (F S B : E) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    ‖F‖^2 ≤ 2*‖S‖^2+2*max q 0+2*|l| :=
  energy_allocation_bound F S B q l hF hq

theorem FullAudit0_expected_energy_allocation_rate_lower {E : Type*} [SeminormedAddCommGroup E]
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
theorem FullAudit0_example_67 (F S B : ℂ) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    |Real.log (1+‖F‖^2)-Real.log (1+max q 0)| ≤
      2*Real.log (1+‖S‖)+Real.log (1+|l|) :=
  FullAudit0_expected_norm_first_log_comparison F S B q l hF hq

theorem FullAudit0_example_72 (F S B : ℝ) (q l : ℝ) (hF : F = S+B) (hq : q = ‖B‖^2-l) :
    ‖F‖^2 ≤ 2*‖S‖^2+2*max q 0+2*|l| :=
  FullAudit0_expected_energy_allocation_bound F S B q l hF hq


end Zeta23.OPICAFollowup.Validation
/-! Explicit expected-type consumers. This is a partial audit module; native consumers
and the remaining planned root types are still required by the full specification. -/
namespace Zeta23.OPICAFollowup.Validation
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
theorem FullAudit0_expected_optimal_recovery_noise_composition
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
end Zeta23.OPICAFollowup.Validation


namespace Zeta23.OPICAFollowup.Validation
open Filter Topology
open Zeta23.OPICA
open scoped Matrix

theorem FullAudit0_expected_norm_first_strictly_weaker_control (T : HorizonSchedule) {θ : ℝ} (hθ : 0 < θ) :
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

theorem FullAudit0_expected_coupled_gram_collision_control :
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


end Zeta23.OPICAFollowup.Validation
namespace Zeta23.OPICAFollowup.Validation
/- Optional Candidate1 consumers. These append supporting scope checks without
changing any of the four required primary expected signatures. -/
theorem FullAudit0_expected_sharp_norm_first_arsinh_bound
    {E : Type*} [SeminormedAddCommGroup E] (u v : E) :
    |Real.log (1+‖u‖^2)-Real.log (1+‖v‖^2)| ≤
      2*Real.arsinh (‖u-v‖/2) ∧
      2*Real.arsinh (‖u-v‖/2) ≤ 2*Real.log (1+‖u-v‖) :=
  sharp_norm_first_arsinh_bound u v

theorem FullAudit0_expected_sharp_norm_first_scalar_attained {d : ℝ} (hd : 0 ≤ d) :
    ‖sharpNormAlpha d-(sharpNormAlpha d)⁻¹‖ = d ∧
    |Real.log (1+‖sharpNormAlpha d‖^2)-Real.log (1+‖(sharpNormAlpha d)⁻¹‖^2)| =
      2*Real.log (sharpNormAlpha d) :=
  sharp_norm_first_scalar_attained hd

theorem FullAudit0_expected_sharp_norm_first_log_comparison
    {E : Type*} [SeminormedAddCommGroup E] (F S B : E) (q l : ℝ)
    (field_decomposition : F = S+B) (signed_quadratic : q = ‖B‖^2-l) :
    |Real.log (1+‖F‖^2)-Real.log (1+max q 0)| ≤
      2*Real.arsinh (‖S‖/2)+Real.log (1+|l|) :=
  sharp_norm_first_log_comparison F S B q l field_decomposition signed_quadratic

/-- Explicitly recover the unchanged mandatory comparison interface. -/
theorem FullAudit0_expected_sharp_norm_first_recovers_primary
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
theorem FullAudit0_expected_collisionGram_inverse_zero_zero {h : ℝ} (h0 : 0 < h) (h1 : h < 1) :
    ((collisionGram h)⁻¹) 0 0 = 2*(1-h)/h^2 :=
  collisionGram_inverse_zero_zero h0 h1

theorem FullAudit0_expected_collisionGram_inverse_zero_zero_tendsto :
    Tendsto (fun h : ℝ => ((collisionGram h)⁻¹) 0 0) (𝓝[>] (0:ℝ)) atTop :=
  collisionGram_inverse_zero_zero_tendsto

end Zeta23.OPICAFollowup.Validation
noncomputable section
namespace Zeta23.OPICAFollowup.Validation
open Filter Topology Zeta23.OPICA Zeta23.CCM
open scoped Matrix ComplexOrder

theorem FullAudit0_expected_sourceFamily_zero_eq_original :
    sourceOrderFamily 0 = nativeOriginalSource ∧
    primeFieldFamily 0 = nativeOriginalPrimeField ∧
    integerDriveFamily 0 = nativeOriginalIntegerDrive :=
  sourceFamily_zero_eq_original

theorem FullAudit0_expected_sourceFamily_support_smooth_moments (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (sourceOrderFamily d) ∧
    NativeSourceSupported UniversalSinc.fixedScale (sourceOrderFamily d) ∧
    0 < nativeCausalGap ∧
    (∀ t < nativeCausalGap, primeFieldFamily d t = 0 ∧ integerDriveFamily d t = 0) ∧
    (∀ k < d+2, sourceWeightedMoment k (1/2) (sourceOrderFamily d) = 0 ∧
      sourceWeightedMoment k (-1/2) (sourceOrderFamily d) = 0) :=
  sourceFamily_support_smooth_moments d

theorem FullAudit0_expected_sourceFamily_physical_histories (d : ℕ) :
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

theorem FullAudit0_expected_source_product_vertical_bound (σ τ : ℝ) :
    ‖sourceBoxProduct ((σ : ℂ)+Complex.I*(τ : ℂ))‖ ≤
      8*Real.exp (UniversalSinc.fixedScale*|σ|)*
        Real.exp (-sourceVerticalDecayConstant*Real.sqrt |τ|) :=
  source_product_vertical_bound σ τ

-- This checks the prescribed one-copy product and exact constant, not a caller envelope.
theorem FullAudit0_example_306 (w : ℂ) : sourceBoxProduct w =
    UniversalSinc.product UniversalSinc.fixedScale (Complex.I*w) := rfl
theorem FullAudit0_example_308 : sourceVerticalDecayConstant = Real.log 8*Real.sqrt UniversalSinc.fixedScale/4 := rfl

theorem FullAudit0_expected_history_recovery_cost_control {E : Type*} [NormedAddCommGroup E]
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

theorem FullAudit0_expected_forced_positive_gram_nonreal_control {ι δ : Type*}
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
theorem FullAudit0_expected_forced_concrete_witness :
    (forcedProfileGram (fun _ : Fin 1 => 1) (fun _ => 1) forcedNonrealParameters).PosSemidef ∧
    (forcedProfileEnergy (fun _ : Fin 1 => 1) (fun _ => 1) forcedNonrealParameters).PosSemidef ∧
    (∀ i, 0 < (forcedProfileGram (fun _ : Fin 1 => 1) (fun _ => 1)
      forcedNonrealParameters i i).re) := by
  have h := FullAudit0_expected_forced_positive_gram_nonreal_control (fun _ : Fin 1 => 1) (fun _ => 1)
    forcedNonrealParameters (by intro n; norm_num)
    ⟨0, by norm_num⟩ forcedNonrealParameters_im_ne
  exact ⟨h.1,h.2.1,h.2.2.1⟩

end Zeta23.OPICAFollowup.Validation
-- Add `import Zeta23.OPICAFollowup.BalancedCoefficients` to Validation's imports.
-- This fragment is checked against a byte-identical copy of the leaf source,
-- because producing the .olean remains serialized with the other writers.

noncomputable section
open scoped BigOperators

namespace Zeta23.OPICAFollowup.Validation
open Zeta23.OPICA

theorem FullAudit0_expected_native_binomial_inverse_identity (Q : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (r : ℕ) (hr : 2 ≤ r) :
    nativeInverseCoefficients Q = typeICoefficients Q Y r + balancedInverseCoefficients Q Y r ∧
    (∀ (U : BoundedCausalDrive) (T t : ℝ), t ≤ T →
      (∀ n : ℕ, driveIndexBound T < n →
        nativeInverseCoefficients Q n * translatedDrive U n t = 0) ∧
      (∑' n : ℕ, nativeInverseCoefficients Q n * translatedDrive U n t) =
        finiteDriveField U (driveIndexBound T) (typeICoefficients Q Y r) t +
        finiteDriveField U (driveIndexBound T) (balancedInverseCoefficients Q Y r) t) :=
  native_binomial_inverse_identity Q Y hY r hr

theorem FullAudit0_expected_balanced_coeff_divisor_bound (Q : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (r : ℕ) (hr : 2 ≤ r) (n : ℕ) :
    |balancedInverseCoefficients Q Y r n| ≤ (divisorCount (2 * r - 1) n : ℝ) ∧
    |typeICoefficients Q Y r n| ≤
      ((2 : ℝ) ^ r - 1) * (divisorCount (2 * r - 1) n : ℝ) :=
  balanced_coeff_divisor_bound Q Y hY r hr n

-- These are the literal J17 coefficients, including the free integer powers.
theorem FullAudit0_example_397 (Q : ℕ) (Y : ℝ) (r : ℕ) :
    typeICoefficients Q Y r =
      ∑ i ∈ Finset.range r, ((-1 : ℝ) ^ i * (r.choose (i + 1) : ℝ)) •
        (smallInverseCoefficients Q Y ^ (i + 1) * nativeFreeCoefficients Q ^ i) := rfl

theorem FullAudit0_example_402 (Q : ℕ) (Y : ℝ) (r : ℕ) :
    balancedInverseCoefficients Q Y r =
      nativeLargeCoefficients Q Y ^ r * nativeFreeCoefficients Q ^ (r - 1) := rfl

-- Actual P0 native source, multiplied by its actual finite palette filter.
-- No caller supplies a coefficient identity, a physical field or a bound.
theorem FullAudit0_native_j17_original_palette_physical_consumer (Q : ℕ) (Y : ℝ) (hY : 1 ≤ Y)
    (r : ℕ) (hr : 2 ≤ r) (T t : ℝ) (ht : t ≤ T) :
    (∑' n : ℕ, nativeInverseCoefficients Q n *
      translatedDrive (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q) n t) =
      finiteDriveField (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q)
        (driveIndexBound T) (typeICoefficients Q Y r) t +
      finiteDriveField (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q)
        (driveIndexBound T) (balancedInverseCoefficients Q Y r) t :=
  ((FullAudit0_expected_native_binomial_inverse_identity Q Y hY r hr).2
    (squarefreePaletteDrive nativeOriginalBoundedCausalDrive Q) T t ht).2

-- A nonsquarefree total product is included in the public envelope.
theorem FullAudit0_example_420 :
    |balancedInverseCoefficients 1 (3/2) 2 4| ≤ (divisorCount 3 4 : ℝ) ∧
    |typeICoefficients 1 (3/2) 2 4| ≤ 3 * (divisorCount 3 4 : ℝ) := by
  convert FullAudit0_expected_balanced_coeff_divisor_bound 1 (3/2) (by norm_num) 2 (by norm_num) 4 using 1
  norm_num


end Zeta23.OPICAFollowup.Validation
noncomputable section
namespace Zeta23.OPICAFollowup.Validation
open Filter Topology Metric Set Complex
open scoped Real
theorem FullAudit0_expected_laurent_coefficient_error_bound {f g : ℂ → ℂ} {c : ℂ} {r E : ℝ}
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

theorem FullAudit0_expected_laurent_observation_survives {f g : ℂ → ℂ} {c : ℂ} {r E : ℝ}
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

theorem FullAudit0_expected_laurent_derivative_error_bound {f g : ℂ → ℂ} {c : ℂ} {r E : ℝ}
    (radius_positive : 0 < r) (original_meromorphic : MeromorphicAt f c)
    (observed_meromorphic : MeromorphicAt g c)
    (original_holomorphic : AnalyticOnNhd ℂ f (closedBall c r))
    (observed_holomorphic : AnalyticOnNhd ℂ g (closedBall c r))
    (actual_circle_budget : ∀ z ∈ sphere c r, ‖g z-f z‖ ≤ E) (n : ℕ) :
    ‖iteratedDeriv n g c-iteratedDeriv n f c‖ ≤
      (n.factorial : ℝ)*(r^(-(n:ℤ))*E) :=
  laurent_derivative_error_bound radius_positive original_meromorphic observed_meromorphic
    original_holomorphic observed_holomorphic actual_circle_budget n

theorem FullAudit0_expected_laurent_equality_sharp_cancellation {f : ℂ → ℂ} {c : ℂ} {r : ℝ}
    (radius_positive : 0 < r) (original_meromorphic : MeromorphicAt f c)
    (original_domain : AnalyticOnNhd ℂ f (closedBall c r \ {c}))
    (j : ℤ) (degree_in_scope : -1 ≤ j) :
    let a := laurentObservedCoefficient f c original_meromorphic j
    let cancelled := fun z => f z-laurentMonomial a c j z
    ∃ cancelled_meromorphic : MeromorphicAt cancelled c,
      laurentObservedCoefficient cancelled c cancelled_meromorphic j = 0 ∧
      ∀ z ∈ sphere c r, ‖cancelled z-f z‖ = ‖a‖*r^j :=
  laurent_equality_sharp_cancellation radius_positive original_meromorphic original_domain degree_in_scope

theorem FullAudit0_expected_laurent_monomial_coefficient (a c : ℂ) (j : ℤ)
    (degree_in_scope : -1 ≤ j) (r : ℝ) (radius_positive : 0 < r) :
    laurentObservedCoefficient (laurentMonomial a c j) c
      (laurentMonomial_meromorphicAt a c j) j = a :=
  meromorphicLaurentCoefficient_monomial a c degree_in_scope radius_positive

theorem FullAudit0_expected_laurent_monomial_circle_norm (a c : ℂ) (j : ℤ) (r : ℝ)
    (z : ℂ) (on_actual_circle : z ∈ sphere c r) :
    ‖laurentMonomial a c j z‖ = ‖a‖*r^j :=
  laurentMonomial_circle_norm a c j on_actual_circle

end Zeta23.OPICAFollowup.Validation
noncomputable section
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_zeta_left_line_uniform_bound : ∃ A0 : ℝ, 1 ≤ A0 ∧
    ∀ (n : ℕ), 1 ≤ n → ∀ τ : ℝ,
      ‖riemannZeta (-(n:ℂ)+Complex.I*(τ:ℂ))‖+
        ‖deriv riemannZeta (-(n:ℂ)+Complex.I*(τ:ℂ))‖ ≤
      A0^(n+1)*((n:ℝ)+2+|τ|)^(n+2) :=
  zeta_left_line_uniform_bound

-- Includes zero ordinate and the trivial zero at -2, with the actual derivative.
theorem FullAudit0_expected_zeta_left_trivial_zero_boundary : ∃ A0 : ℝ, 1 ≤ A0 ∧
    ‖riemannZeta (-2)‖+‖deriv riemannZeta (-2)‖ ≤ A0^3*4^4 := by
  obtain ⟨A0,hA,h⟩ := FullAudit0_expected_zeta_left_line_uniform_bound
  refine ⟨A0,hA,?_⟩
  convert h 2 (by norm_num) 0 using 1
  all_goals norm_num

end Zeta23.OPICAFollowup.Validation
noncomputable section
open MeasureTheory Complex
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_sourceFamily_laplace_identity (d : ℕ) :
    (∀ w : ℂ, sourceFamilyLaplace d w = (w^2-1/4)^d*CCM.nativeOriginalSourceLaplace w) ∧
    (∀ rho : zetaZeroConfig.carrier, 1/2<(rho:ℂ).re →
      sourceFamilyLaplace d ((rho:ℂ)-1/2) ≠ 0) :=
  sourceFamily_laplace_identity d

theorem FullAudit0_expected_nativePrimeField_visiblePole (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    ∃ pole : OPICA.SimplePoleData (ℝ → ℝ),
      pole.source=CCM.nativeOriginalSource ∧ pole.center=(rho:ℂ)-1/2 ∧
      pole.field=nativePrimeTransformGerm ∧
      pole.residue=-(zeroMult (rho:ℂ):ℂ)*CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2) ∧
      Meromorphic pole.field ∧
      (∀ w : ℂ, 1/2<w.re →
        (∫ t : ℝ, Complex.exp (-w*(t:ℂ))*(CCM.nativeOriginalPrimeField t:ℂ))=pole.field w) :=
  nativePrimeField_visiblePole rho hright

theorem FullAudit0_expected_nativePrimePole_physical_source (rho : zetaZeroConfig.carrier)
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

noncomputable section
namespace Zeta23.OPICAFollowup.Validation
open MeasureTheory Complex Zeta23.CCM
/- Independently stated NativeExplicitFormula consumers for aggregate Validation. -/

theorem FullAudit0_example_576 : zetaZeroConfig.carrier = {rho : ℂ | IsNontrivialZero rho} := rfl
theorem FullAudit0_example_577 (rho : ℂ) : zetaZeroConfig.mult rho = (analyticOrderAt riemannZeta rho).toNat := rfl

theorem FullAudit0_expected_native_zero_count_summability :
    Summable (fun rho : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult rho : ℝ) / (1 + Complex.normSq (gammaOf rho))) ∧
    Summable (fun rho : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult rho : ℝ) / (1 + ((rho : ℂ).im)^2)) :=
  native_zero_count_summability

theorem FullAudit0_example_586 : nativeZeroDisplacementSup =
    sSup (insert 0 (Set.range (fun rho : zetaZeroConfig.carrier =>
      max ((rho : ℂ).re - 1/2) 0))) := rfl

theorem FullAudit0_expected_native_zero_sup_bounds :
    0 ≤ nativeZeroDisplacementSup ∧ nativeZeroDisplacementSup ≤ 1/2 ∧
    (∀ rho : zetaZeroConfig.carrier,
      max ((rho : ℂ).re - 1/2) 0 ≤ nativeZeroDisplacementSup) ∧
    (∀ b : ℝ, 0 ≤ b → b < nativeZeroDisplacementSup →
      ∃ rho : zetaZeroConfig.carrier, b < (rho : ℂ).re - 1/2) :=
  native_zero_sup_bounds

theorem FullAudit0_expected_native_source_explicit_formula (d : ℕ) {t : ℝ} (ht : UniversalSinc.fixedScale < t) :
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


theorem FullAudit0_example_626 (n : ℕ) : riemannZeta (1/2-(2*((n:ℝ)+1)+1/2 : ℝ)) = 0 :=
  nativeTrivialZeroDecay_zeta_zero n
end Zeta23.OPICAFollowup.Validation
noncomputable section
open Complex
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_nativeGenerator_unit_or_completion (g : NativeGenerator)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    (∀ z : ℂ, g.multiplier z=g.unitMultiplier z*riemannZeta (z+1/2)^g.completionCount) ∧
    AnalyticAt ℂ g.unitMultiplier ((rho:ℂ)-1/2) ∧
    g.unitMultiplier ((rho:ℂ)-1/2) ≠ 0 ∧
    (∀ Y r : ℕ, (NativeGenerator.residualPower Y r).multiplier ((rho:ℂ)-1/2)=1) :=
  nativeGenerator_unit_or_completion g rho hright

theorem FullAudit0_expected_source_generator_unit (d : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ (fun z : ℂ => (z^2-1/4)^d) ((rho:ℂ)-1/2) ∧
    (((rho:ℂ)-1/2)^2-1/4)^d ≠ 0 :=
  ⟨(NativeGenerator.sourceDerivative d).unit_analytic rho hright,
    (NativeGenerator.sourceDerivative d).unit_ne_zero rho hright⟩

theorem FullAudit0_expected_delay_generator_unit (tau : ℝ) (htau : 0≤tau)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ (fun z : ℂ => Complex.exp (-(tau:ℂ)*z)) ((rho:ℂ)-1/2) ∧
    Complex.exp (-(tau:ℂ)*((rho:ℂ)-1/2)) ≠ 0 :=
  ⟨(NativeGenerator.delay tau htau).unit_analytic rho hright,
    (NativeGenerator.delay tau htau).unit_ne_zero rho hright⟩

theorem FullAudit0_expected_finiteEuler_generator_units (Q : ℕ) (hQ : 0<Q)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ (finiteEulerMultiplier Q) ((rho:ℂ)-1/2) ∧
    finiteEulerMultiplier Q ((rho:ℂ)-1/2) ≠ 0 ∧
    AnalyticAt ℂ (fun z => (finiteEulerMultiplier Q z)⁻¹) ((rho:ℂ)-1/2) ∧
    (finiteEulerMultiplier Q ((rho:ℂ)-1/2))⁻¹ ≠ 0 :=
  ⟨(NativeGenerator.finiteEuler Q hQ).unit_analytic rho hright,
    (NativeGenerator.finiteEuler Q hQ).unit_ne_zero rho hright,
    (NativeGenerator.inverseFiniteEuler Q hQ).unit_analytic rho hright,
    (NativeGenerator.inverseFiniteEuler Q hQ).unit_ne_zero rho hright⟩

theorem FullAudit0_expected_rational_generator_units (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (rho : zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ (fun z : ℂ => (z+(a:ℂ))/(z+(b:ℂ))) ((rho:ℂ)-1/2) ∧
    (((rho:ℂ)-1/2+(a:ℂ))/((rho:ℂ)-1/2+(b:ℂ))) ≠ 0 ∧
    AnalyticAt ℂ (fun z : ℂ => (z+(b:ℂ))/(z+(a:ℂ))) ((rho:ℂ)-1/2) ∧
    (((rho:ℂ)-1/2+(b:ℂ))/((rho:ℂ)-1/2+(a:ℂ))) ≠ 0 :=
  ⟨(NativeGenerator.rational a b ha hb).unit_analytic rho hright,
    (NativeGenerator.rational a b ha hb).unit_ne_zero rho hright,
    (NativeGenerator.inverseRational a b ha hb).unit_analytic rho hright,
    (NativeGenerator.inverseRational a b ha hb).unit_ne_zero rho hright⟩

theorem FullAudit0_expected_residual_generator_unit (Y r : ℕ) (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    AnalyticAt ℂ (fun z : ℂ => (1-riemannZeta (z+1/2)*truncatedMoebiusMultiplier Y z)^r)
      ((rho:ℂ)-1/2) ∧
    (1-riemannZeta (rho:ℂ)*truncatedMoebiusMultiplier Y ((rho:ℂ)-1/2))^r=1 := by
  refine ⟨(NativeGenerator.residualPower Y r).unit_analytic rho hright,?_⟩
  simpa only [NativeGenerator.multiplier,sub_add_cancel] using
    NativeGenerator.residual_value_one Y r rho

theorem FullAudit0_expected_completion_generator_unit (rho : zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) :
    (∀ z : ℂ, NativeGenerator.completion.multiplier z=
      CCM.nativeCompletionRationalMultiplier z*riemannZeta (z+1/2)) ∧
    AnalyticAt ℂ CCM.nativeCompletionRationalMultiplier ((rho:ℂ)-1/2) ∧
    CCM.nativeCompletionRationalMultiplier ((rho:ℂ)-1/2) ≠ 0 :=
  ⟨fun _ => rfl,NativeGenerator.completion.unit_analytic rho hright,
    NativeGenerator.completion.unit_ne_zero rho hright⟩

end Zeta23.OPICAFollowup.Validation

noncomputable section
open MeasureTheory
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_forwardKernel_left_contour_budget (d ell k : ℕ) :
    ∃ C D : ℝ, ∃ B : ℕ, 0 < C ∧ 0 ≤ D ∧ ∀ n : ℕ, 1 ≤ n →
      Integrable (fun τ : ℝ => (forwardLeftContour n τ)^k*
        forwardKernelTransformGerm d ell (forwardLeftContour n τ)) ∧
      (∫ τ : ℝ, ‖(forwardLeftContour n τ)^k*
        forwardKernelTransformGerm d ell (forwardLeftContour n τ)‖) ≤
        C*Real.exp (D*(n:ℝ))*(n:ℝ)^(2*(ell+1)*n+B) :=
  forwardKernel_left_contour_budget d ell k

-- The source in the contour is its literal physical compact-source integral.
theorem FullAudit0_expected_forward_contour_literal_source (d ell k n : ℕ) (τ : ℝ) :
    forwardContourIntegrand d ell k n τ =
      let z : ℂ := -(((n:ℝ)+1/2):ℂ)+Complex.I*(τ:ℂ)
      z^k*(-(∫ u : ℝ, Complex.exp (-z*(u:ℂ))*(sourceOrderFamily d u:ℂ))*
        riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2)) := rfl

theorem FullAudit0_expected_forward_contour_zero_degree_moment {c : ℝ} (hc : 0 < c) :
    (∫ τ : ℝ, Real.exp (-c*Real.sqrt |τ|)) = 4/c^2 := by
  simpa using sqrt_decay_moment_integral hc 0

end Zeta23.OPICAFollowup.Validation
noncomputable section
open Complex
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_realCutoff_physical_transform (Y : ℝ) (hY : 1≤Y) (r : ℕ)
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

theorem FullAudit0_expected_nonintegral_residual_cutoff (r : ℕ) (state : NativeCausalState)
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


end Zeta23.OPICAFollowup.Validation
open Complex MeasureTheory
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_nativeGenerator_transform (g : NativeGenerator) (state : NativeCausalState) :
    (∃ S : ℝ, ∀ z : ℂ, S<z.re →
      (∀ term∈state, Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t)) ∧
      (∀ term∈g.act state, Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*term.regular t)) ∧
      (g.act state).laplace z=g.multiplier z*state.laplace z) ∧
    (∀ d : ℕ, ∀ test : NativeCompactTest,
      ((NativeGenerator.sourceDerivative d).act (primeFamilyCausalState 0)).applyTest test=
        (primeFamilyCausalState d).applyTest test) :=
  nativeGenerator_transform g state

theorem FullAudit0_expected_literal_source_differentiation (d : ℕ) (test : NativeCompactTest) :
    ((NativeGenerator.sourceDerivative d).act (primeFamilyCausalState 0)).applyTest test=
      ∫ t : ℝ, (CCM.nativePrimeField (sourceOrderFamily d) t:ℂ)*test t := by
  rw [primeFamilyCausalState_sourceDerivative_applyTest,primeFamilyCausalState_applyTest]
  rfl

theorem FullAudit0_expected_arbitrary_history_distributional_P (state : NativeCausalState)
    (test : NativeCompactTest) :
    state.sourceDifferentialAction.applyTest test=
      state.applyTest (test.derivative.derivative.add (test.constMul (-(1/4:ℂ)))) :=
  state.applyTest_sourceDifferentialAction test

theorem FullAudit0_expected_actual_completion_convolution (f : NativeRegularCausal) (t : ℝ) :
    nativeCompletionCausalKernel.convolve f t=
      ∫ s : ℝ, (CCM.nativePositiveCompletion s:ℂ)*f (t-s) := rfl

theorem FullAudit0_expected_actual_inverseEuler (Q : ℕ) (state : NativeCausalState) :
    ∃ S : ℝ, ∀ z : ℂ, S<z.re →
      (state.inverseFiniteEulerAction Q).laplace z=
        (∏ p ∈ Q.primeFactors, (1-Complex.exp (-(z+1/2)*(Real.log p:ℂ))))⁻¹*state.laplace z :=
  state.laplace_inverseFiniteEulerAction Q

end Zeta23.OPICAFollowup.Validation
open Complex MeasureTheory
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_forwardKernel_physical_laplace (d ell : ℕ) (hd : ell≤d) :
    (∀ z : ℂ, 1/2<z.re →
      Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(forwardKernel d ell t:ℂ)) ∧
      (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(forwardKernel d ell t:ℂ))=
        -sourceFamilyLaplace d z*riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2)) ∧
    (∀ z : ℂ, AnalyticAt ℂ (forwardKernelEntireContinuation d ell) z) ∧
    (∀ z : ℂ, z≠1/2 →
      forwardKernelEntireContinuation d ell z=
        -sourceFamilyLaplace d z*riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2)) :=
  forwardKernel_physical_laplace d ell hd

theorem FullAudit0_expected_forward_diagonal_removable_value (d : ℕ) :
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
 theorem FullAudit0_expected_source_order_uniform_norms :
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

 theorem FullAudit0_expected_native_field_theta_envelope :
    ∃ C : ℝ, 0<C ∧ ∃ Cd : ℕ → ℝ, ∀ d : ℕ,
      0<Cd d ∧
      (∀ t : ℝ, 0≤t → |nativePrimeField (sourceOrderFamily d) t| ≤
        Cd d*Real.exp ((sSup (insert 0 (Set.range
          (fun rho : zetaZeroConfig.carrier => max ((rho:ℂ).re-1/2) 0))))*t)) ∧
      Real.log (1+Cd d) ≤ C*((d:ℝ)+1)*Real.log ((d:ℝ)+2) := by
  obtain ⟨C,hC,h⟩ := native_field_theta_envelope
  refine ⟨C,hC,nativeFieldOrderConstant,fun d => ?_⟩
  exact h d


end Zeta23.OPICAFollowup.Validation
open Filter Complex Set MeasureTheory
open scoped Topology BigOperators

open Filter Complex Set MeasureTheory
open scoped Topology BigOperators
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_nativeWord_corrected_transform (w : NativeWord)
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

theorem FullAudit0_expected_nativeWord_order_and_leading (w : NativeWord)
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

theorem FullAudit0_expected_nativeWord_first_nonzero_derivative (w : NativeWord)
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

theorem FullAudit0_expected_nativeWord_factor_costs (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
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

theorem FullAudit0_example_971 (w : NativeWord) (rho : Zeta23.zetaZeroConfig.carrier)
    (hright : 1/2<(rho:ℂ).re) (history : NativeWordHistory ((rho:ℂ)-1/2)) (hp : 0<wordCompletionCount w)
    (hdegree : wordCompletionCount w*zeroMult (rho:ℂ)=1) :
    nativeWordRegularRepresentative w rho hright ((rho:ℂ)-1/2)≠0 := by
  simpa only [hdegree,Nat.sub_self,iteratedDeriv_zero] using
    (nativeWord_first_nonzero_derivative w rho hright history hp).2.2.2.2


end Zeta23.OPICAFollowup.Validation
open Complex Filter MeasureTheory
open scoped Topology
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_example_985 (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    Tendsto (fun z => (z-((rho:ℂ)-1/2))*nativeWordCorrectedField [] rho history z)
      (𝓝[≠] ((rho:ℂ)-1/2))
      (𝓝 (-(zeroMult (rho:ℂ):ℂ)*Zeta23.CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2))) := by
  rcases nativeWord_order_and_leading [] rho hright history with ⟨_,_,_,_,_,_,_,hzero⟩
  simpa only [nativeWordLeadingCoefficient,wordCompletionCount,wordUnitFactor,pow_zero,mul_one] using
    hzero rfl

theorem FullAudit0_example_994 (Y : ℝ) (hY : 1≤Y) (r : ℕ) (z : ℂ) :
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
theorem FullAudit0_expected_nativeWord_global_continuation (w : NativeWord)
    (rho : Zeta23.zetaZeroConfig.carrier)
    (history : NativeWordHistory ((rho:ℂ)-1/2))
    (D : NativeWordHistoryContinuationDomain w history) :
    MeromorphicOn (nativeWordTransformedField w rho history) D.domain :=
  nativeWordTransformedField_meromorphicOn w rho history D

end Zeta23.OPICAFollowup.Validation
open Complex Filter MeasureTheory
open scoped Topology
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_example_1022 (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re)
    (history : NativeWordHistory ((rho:ℂ)-1/2)) :
    Tendsto (fun z => (z-((rho:ℂ)-1/2))*nativeWordCorrectedField [] rho history z)
      (𝓝[≠] ((rho:ℂ)-1/2))
      (𝓝 (-(zeroMult (rho:ℂ):ℂ)*Zeta23.CCM.nativeOriginalSourceLaplace ((rho:ℂ)-1/2))) := by
  rcases nativeWord_order_and_leading [] rho hright history with ⟨_,_,_,_,_,_,_,hzero⟩
  simpa only [nativeWordLeadingCoefficient,wordCompletionCount,wordUnitFactor,pow_zero,mul_one] using
    hzero rfl

theorem FullAudit0_example_1031 (Y : ℝ) (hY : 1≤Y) (r : ℕ) (z : ℂ) :
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
theorem FullAudit0_expected_nativeWord_contour_consumer (w : NativeWord)
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

open Complex MeasureTheory
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_literal_forward_iteratedDeriv (d ell k : ℕ) {z : ℂ} (hz : 1/2<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*
      Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t))=
      z^k*(-sourceFamilyLaplace d z*riemannZeta (z+1/2)^ell*deriv riemannZeta (z+1/2)) :=
  forwardKernel_iteratedDeriv_physical_laplace d ell k hz

theorem FullAudit0_expected_literal_forward_derivative_entire (d ell k : ℕ) (hd : ell≤d)
    {z : ℂ} (hz : 1/2<z.re) :
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (iteratedDeriv k (forwardKernel d ell) t))=
      z^k*forwardKernelEntireContinuation d ell z :=
  forwardKernel_iteratedDeriv_laplace_entire d ell k hd hz

theorem FullAudit0_expected_literal_forward_smooth_positive_gap (d ell k : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (forwardKernel d ell) ∧
    0<Real.log 2-CCM.UniversalSinc.fixedScale ∧
    (∀ t : ℝ, t<Real.log 2-CCM.UniversalSinc.fixedScale →
      iteratedDeriv k (forwardKernel d ell) t=0) :=
  ⟨forwardKernel_contDiff d ell,nativeCausalGap_pos,
    fun _t ht => forwardKernel_iteratedDeriv_zero_before d ell k ht⟩

end Zeta23.OPICAFollowup.Validation
open Complex MeasureTheory
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_fractional_strip_zeta_control (a b : ℝ) :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ (σ τ : ℝ), a≤σ → σ≤b → 2≤|τ| →
      ‖riemannZeta ((σ:ℂ)+(τ:ℂ)*I)‖+‖deriv riemannZeta ((σ:ℂ)+(τ:ℂ)*I)‖ ≤
        C*(1+|τ|)^N := zeta_fixed_strip_polynomial_value_derivative_bound a b

theorem FullAudit0_expected_positive_fractional_gamma_control :
    ∃ C : ℝ, 0<C ∧ ∃ N : ℕ, ∀ (σ τ : ℝ), (1/2:ℝ)≤σ → σ≤2 →
      ‖Complex.Gamma ((σ:ℂ)+I*(τ:ℂ))‖ ≤
        C*(1+|τ|)^N*Real.exp (-(Real.pi*|τ|)/2) :=
  gamma_positive_fixed_strip_exp_bound (by norm_num) (by norm_num)


end Zeta23.OPICAFollowup.Validation
noncomputable section
open Complex MeasureTheory
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_forwardKernel_double_exp_decay (d ell k : ℕ) (hd : ell≤d) :
    ∃ A c : ℝ, 0<A ∧ 0<c ∧ ∀ t : ℝ, 0≤t →
      |iteratedDeriv k (forwardKernel d ell) t| ≤
        A*Real.exp (-c*Real.exp (t/(2*((ell:ℝ)+1)))) :=
  forwardKernel_double_exp_decay d ell k hd

theorem FullAudit0_expected_actual_integer_drive_double_exp_decay (d k : ℕ) :
    ∃ A c : ℝ, 0<A ∧ 0<c ∧ ∀ t : ℝ, 0≤t →
      |iteratedDeriv k (CCM.nativeIntegerDriveField (sourceOrderFamily d)) t| ≤
        A*Real.exp (-c*Real.exp (t/2)) := by
  simpa only [forwardKernel,integerDriveFamily,Nat.cast_zero,zero_add,mul_one] using
    forwardKernel_double_exp_decay d 0 k (Nat.zero_le d)

theorem FullAudit0_expected_forward_all_derivatives_at_zero (d ell k : ℕ) :
    iteratedDeriv k (forwardKernel d ell) 0=0 :=
  forwardKernel_iteratedDeriv_zero_before d ell k nativeCausalGap_pos


end Zeta23.OPICAFollowup.Validation
/-! CONTINUATION INDEPENDENT CONSUMERS: three full primary types and actual-domain supporting checks. Full100 acceptance remains closed. -/


/-! Independently stated expected-type and actual-source consumers.
These are not additions to the normative registry or a replacement for its
complete Validation module. Compiler status is recorded in adjacent logs. -/
noncomputable section
open Set MeasureTheory Finset
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_expected_log_slack_native_decomposition (r d : ℕ) (hr : 2≤r) (hd : r-1≤d)
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

theorem FullAudit0_expected_log_slack_typeI_error (r d : ℕ) (hr : 2 ≤ r) (hd : r-1 ≤ d)
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
theorem FullAudit0_example_1210 : ∃ A c T0 : ℝ, 0 < A ∧ 0 < c ∧ 1 ≤ T0 ∧
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

theorem FullAudit0_expected_fixed_two_factor_preparation : ∃ C1 c T0 : ℝ, 0 < C1 ∧ 0 < c ∧ 1 ≤ T0 ∧
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
theorem FullAudit0_example_1240 (r d Q : ℕ) (hr : 2 ≤ r) (_hQ : 0 < Q) (Y : ℝ) (hY : 1 ≤ Y) (t : ℝ) :
    primeFieldFamily d t = typeIField d r Q Y t + balancedField d r Q Y t := by
  exact native_balanced_physical_identity d r Q hr Y hY t

theorem FullAudit0_example_1244 (d r Q : ℕ) (hr : 2 ≤ r) (_hQ : 0 < Q) (t : ℝ) :
    primeFieldFamily d t = typeIField d r Q (3/2) t + balancedField d r Q (3/2) t := by
  exact native_balanced_physical_identity d r Q hr (3/2) (by norm_num) t

/-- The fixed source is the actual differential image of the parent source. -/
theorem FullAudit0_example_1249 : sourceOrderFamily 1 = fun t : ℝ =>
    deriv (deriv Zeta23.CCM.nativeOriginalSource) t-(1/4:ℝ)*Zeta23.CCM.nativeOriginalSource t := rfl

theorem FullAudit0_example_1252 : primeFieldFamily 1 = Zeta23.CCM.nativePrimeField
    (fun t : ℝ => deriv (deriv Zeta23.CCM.nativeOriginalSource) t-
      (1/4:ℝ)*Zeta23.CCM.nativeOriginalSource t) := rfl

/-- The compensation is the literal finite divisor filter with its square-root weights. -/
theorem FullAudit0_example_1257 (d Q : ℕ) (hQ : 0<Q) (t : ℝ) : nativePaletteDrive d Q t=
    ∑ n∈Q.divisors, (ArithmeticFunction.moebius n:ℝ)/Real.sqrt (n:ℝ)*
      Zeta23.CCM.nativeIntegerDriveField (sourceOrderFamily d) (t-Real.log n) := by
  simpa only [nativePaletteDrive,integerDriveFamily,Zeta23.OPICA.moebiusPaletteCoefficient] using
    arithmeticHistoryAction_palette_finite Q hQ (integerDriveFamily d) t


end Zeta23.OPICAFollowup.Validation
end


/-! Independent expected types for the auxiliary supporting continuation.
No full auxiliary primary is certified by these helpers. -/
noncomputable section
open Set MeasureTheory Polynomial
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_example_1284 (k : ℕ) {z : ℂ} (hz : -((k:ℝ)+3/2)<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionFilter k t)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionFilter k t))=
      (z-1/2)/(∏ j ∈ Finset.range (k+2), (z+(k+1+j:ℕ)+1/2)) :=
  auxCompletionFilter_integrable_laplace k hz

theorem FullAudit0_example_1290 (k : ℕ) {z : ℂ} (hz : 1/2<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionKernel k t)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*Complex.ofReal (auxCompletionKernel k t))=
      ((z-1/2)/(∏ j ∈ Finset.range (k+2), (z+(k+1+j:ℕ)+1/2)))*riemannZeta (z+1/2) :=
  auxCompletionKernel_initial_laplace k hz

theorem FullAudit0_example_1296 (k : ℕ) : (∫ t : ℝ, ‖auxCompletionFilter k t‖)≤2/(Nat.factorial (k+1):ℝ) :=
  auxCompletionFilter_L1_bound k

theorem FullAudit0_example_1299 (k j : ℕ) :
    ((k+2+j).descFactorial (k+2):ℝ)/(Nat.factorial (k+1):ℝ)=
      (j+1:ℕ)*((k+2+j).choose (k+1):ℝ) :=
  auxDensity_descFactorial_ratio k j

theorem FullAudit0_example_1304 (k : ℕ) :
    (∫ u : ℝ in 0..1,
      |(Polynomial.derivative^[k+1] (auxProfilePolynomial k)).eval u|) ≤
      (2:ℝ)^(3*k+4) := by
  exact auxCompletionProfile_density_L1_bound k

theorem FullAudit0_example_1310 (k : ℕ) (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ u ∈ Icc (0:ℝ) 1, ‖ψ u‖ ≤ M) :
    ‖(-1:ℂ)^(k+1)*(∫ u : ℝ,
      Complex.ofReal (auxCompletionProfile k u)*iteratedDeriv (k+1) ψ u)‖ ≤
      (1+(2:ℝ)^(3*k+4))*M := by
  exact auxCompletionProfile_derivative_test_bound k ψ hψ M hM hb

theorem FullAudit0_example_1317 (k : ℕ) (ξ : ℝ) (hξ : ξ ≠ 0) :
    ‖∫ u : ℝ, Complex.ofReal (auxCompletionProfile k u)*
      Complex.exp (-((2*Real.pi*ξ:ℝ):ℂ)*Complex.I*(u:ℂ))‖ ≤
      (1+(2:ℝ)^(3*k+4))/(2*Real.pi*|ξ|)^(k+1) := by
  exact auxCompletionProfile_fourier_decay k ξ hξ

/-- Negative ordinate is not removed by an accidental positive-frequency premise. -/
theorem FullAudit0_example_1324 (k : ℕ) (ξ : ℝ) (hξ : ξ < 0) :
    ‖auxProfileFourierIntegral k ξ‖ ≤
      (1+(2:ℝ)^(3*k+4))/(2*Real.pi*|ξ|)^(k+1) := by
  exact auxCompletionProfile_fourier_decay k ξ (ne_of_lt hξ)

/-- k=0 still includes the endpoint atom, even though later Poisson continuity
requires k>=1. This is the actual test identity, not only a density estimate. -/
theorem FullAudit0_example_1331 (ψ : ℝ → ℂ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    (-1:ℂ)*(∫ u : ℝ, Complex.ofReal (auxCompletionProfile 0 u)*deriv ψ u) =
      (∫ u : ℝ in 0..1, Complex.ofReal ((auxProfilePolynomial 0).derivative.eval u)*ψ u) - ψ 1 := by
  simpa only [Nat.zero_add,Function.iterate_one,iteratedDeriv_one,pow_one,neg_mul,
    one_mul,sub_eq_add_neg] using auxCompletionProfile_distributional_derivative 0 ψ hψ

theorem FullAudit0_example_1337 (k : ℕ) : ‖(-1:ℂ)^(k+1)‖ = 1 := auxCompletionProfile_endpoint_atom_norm k

end Zeta23.OPICAFollowup.Validation
end


/-! UNCHECKED actual-domain consumers: arbitrary locally finite measures, not
an easier globally finite ComplexMeasure replacement. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_example_1363 (mu : LocallyFiniteComplexMeasure) (K L : Set ℝ)
    (hK : IsCompact K) (hL : IsCompact L) :
    (mu.compactRestriction K hK).restrict L =
      mu.compactRestriction (K∩L) (hK.inter_right hL.isClosed) := by
  exact mu.compactRestriction_restrict K L hK hL

theorem FullAudit0_example_1369 (mu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K) :
    mu.totalVariation.restrict K = (mu.compactRestriction K hK).variation := by
  exact mu.totalVariation_restrict_compact K hK

theorem FullAudit0_example_1373 (mu : LocallyFiniteComplexMeasure) :
    mu.HasLinearGrowth ↔ Zeta23.OPICA.LinearMassGrowth mu.totalVariation := by
  exact mu.hasLinearGrowth_iff_totalVariation

theorem FullAudit0_example_1377 (mu nu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K)
    (f : ℝ → ℂ) (hf : Continuous f) (hs : Function.support f ⊆ K)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ x, ‖f x‖ ≤ M) :
    ‖mu.integral f-nu.integral f‖ ≤
      2*M*(mu.compactRestriction K hK-nu.compactRestriction K hK).variation.real univ := by
  exact mu.compact_integral_difference_bound nu K hK f hf hs M hM hb

theorem FullAudit0_example_1384 {seq : ℕ → LocallyFiniteComplexMeasure} {mu : LocallyFiniteComplexMeasure}
    (h : LocalVariationConvergence seq mu) (f : ℝ → ℂ)
    (hf : Continuous f) (hs : HasCompactSupport f) :
    Tendsto (fun n => (seq n).integral f) atTop (𝓝 (mu.integral f)) := by
  exact h.tendsto_compact_test f hf hs

/-- Actual complex scalar restriction, including genuinely imaginary scalars. -/
theorem FullAudit0_example_1391 (mu : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K) :
    (mu.scale Complex.I).compactRestriction K hK = Complex.I • mu.compactRestriction K hK := by
  exact mu.compactRestriction_scale Complex.I K hK

end Zeta23.OPICAFollowup.Validation
end


/-! Independent exact source/domain consumers. These do not certify the missing
scheduled logarithmic/rate primary statements. -/
noncomputable section
open Set MeasureTheory
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_example_1411 (d ell : ℕ) (hd : ell ≤ d) :
    ∃ A : ℝ, 0 < A ∧ ∀ t : ℝ, |forwardKernel d ell t| ≤ A := by
  exact forwardKernel_actual_bounded d ell hd

theorem FullAudit0_example_1415 (r d Q : ℕ) (hr : 2 ≤ r) (hd : r-1 ≤ d) (hQ : 0 < Q)
    (Y : ℝ) (_hY : 1 ≤ Y) {T t : ℝ} (ht : t ≤ T) :
    finiteDriveField (nativeRawPaletteDrive d Q) (driveIndexBound T)
        (balancedInverseCoefficients Q Y r) t = balancedField d r Q Y t ∧
    finiteDriveField (nativeAbsorbedPaletteDrive d r Q hd) (driveIndexBound T)
        ((nativeLargeCoefficients Q Y ^ r : ArithmeticFunction ℝ)) t = balancedField d r Q Y t := by
  exact native_balanced_two_realizations r d Q hr hd hQ Y ht

theorem FullAudit0_example_1423 (r d Q : ℕ) (hr : 2 ≤ r) (hd : r-1 ≤ d) (hQ : 0 < Q)
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

theorem FullAudit0_example_1435 : Measurable nativeMovingPrimitiveCutoff := nativeMovingPrimitiveCutoff_measurable

/-- Nonsquarefree product index 4 is not removed from the actual r-fold sum. -/
theorem FullAudit0_example_1438 (Q : ℕ) (Y : ℝ) :
    |((nativeLargeCoefficients Q Y ^ 2 : ArithmeticFunction ℝ)) 4| ≤ (divisorCount 2 4 : ℝ) := by
  exact nativeLargeCoefficients_power_abs_le_divisor Q 2 4 Y

theorem FullAudit0_example_1442 (B : ℝ) (d e : ℕ) : lowPrimitiveMask B d e + highPrimitiveMask B d e = 1 := by
  exact primitiveMask_add_high _ _ _

end Zeta23.OPICAFollowup.Validation
end

/-! Adversarial distinction: Dirichlet convolution versus pointwise powers. -/

/-! Exact control distinguishing actual Dirichlet power from pointwise
function power at a nonsquarefree total product. -/
noncomputable section
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit0_large_at_one : nativeLargeCoefficients 1 (3/2) 1=0 := by
  norm_num [nativeLargeCoefficients]

theorem FullAudit0_large_at_two : nativeLargeCoefficients 1 (3/2) 2=(-1:ℝ) := by
  norm_num [nativeLargeCoefficients,nativeInverseCoefficients,coprimeCoefficients,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

theorem FullAudit0_large_at_four : nativeLargeCoefficients 1 (3/2) 4=0 := by
  have hmu : ArithmeticFunction.moebius 4=0 := by
    convert ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two (by decide : (2:ℕ)≠0) using 1 <;>
      norm_num
  norm_num [nativeLargeCoefficients,nativeInverseCoefficients,coprimeCoefficients,hmu]

theorem FullAudit0_actual_dirichlet_square_at_four :
    (nativeLargeCoefficients 1 (3/2)^2 : ArithmeticFunction ℝ) 4=1 := by
  have hanti : (4:ℕ).divisorsAntidiagonal={(1,4),(2,2),(4,1)} := by decide
  rw [pow_two,ArithmeticFunction.mul_apply,hanti]
  norm_num [FullAudit0_large_at_one,FullAudit0_large_at_two,FullAudit0_large_at_four]

theorem FullAudit0_pointwise_square_at_four :
    ((fun n : ℕ => nativeLargeCoefficients 1 (3/2) n)^2) 4=0 := by
  change (nativeLargeCoefficients 1 (3/2) 4)^2=0
  rw [FullAudit0_large_at_four]
  norm_num

theorem FullAudit0_dirichlet_square_differs_from_pointwise :
    (nativeLargeCoefficients 1 (3/2)^2 : ArithmeticFunction ℝ) 4≠
      ((fun n : ℕ => nativeLargeCoefficients 1 (3/2) n)^2) 4 := by
  rw [FullAudit0_actual_dirichlet_square_at_four,FullAudit0_pointwise_square_at_four]
  norm_num

end Zeta23.OPICAFollowup.Validation
end
end
end
end
end
end
end
end
end
end
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedActualFixedBudget.lean; SHA256 9883387228ae6b161058a81055710bdde19c3ff00177154783577a04b3a0c2bd -/
section

noncomputable section
open Set MeasureTheory
open scoped Topology
open Zeta23 Zeta23.OPICA Zeta23.OPICAFollowup
open Zeta23.OPICAFollowup.FiniteSpan
namespace Zeta23.OPICAFollowup.Validation
/-- Independent inline consumer expands the coefficient construction to
literal actual normalized zero-jet data and the norm to sqrt(sum squares). -/
theorem expected_fixed_basis_negative_mass_budget {n : ℕ}
    (basis : Fin n → List (ℂ × ℂ × ℕ))
    (valid : ∀ i, ∀ j ∈ basis i, riemannZeta j.2.1=0 ∧
      0<j.2.1.re ∧ j.2.1.re<1 ∧ j.2.2<zeroJetOrder j.2.1)
    (independent : LinearIndependent ℝ (fun i =>
      (actualZeroJetSum (basis i)).rePart.distributionOfLinearGrowth
        (zeroJetRealSpan_growth (basis i) (valid i)))) :
    ∃ c_basis : ℝ, 0<c_basis ∧ ∀ a : Fin n → ℝ,
      c_basis*Real.sqrt (∑ i,‖a i‖^2) ≤
        ∫ x in (Set.range (fun m : ℤ => (m : ℝ)))ᶜ,sincSquared x
          ∂(actualZeroJetSum ((List.ofFn (fun i =>
            (basis i).map (fun j => ((a i : ℂ)*j.1,j.2.1,j.2.2)))).flatten)).rePart.negative := by
  obtain ⟨c,hc,hbound⟩ := fixed_basis_negative_mass_budget basis valid independent
  refine ⟨c,hc,fun a => ?_⟩
  simpa only [EuclideanSpace.norm_eq,realBasisCombinationData,scaleJetData,Zeta23.OPICAFollowup.zeroJetRealSpan,
    Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan,integerLattice] using hbound (WithLp.toLp 2 a)

theorem FullAudit1_no_positive_budget_without_independence :
    ¬ ∃ c : ℝ, 0<c ∧ ∀ a : EuclideanSpace ℝ (Fin 1),
      c*‖a‖ ≤ ∫ x in integerLatticeᶜ,sincSquared x
        ∂(Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan (realBasisCombinationData (fun _ : Fin 1 => []) (fun i => a i))).negative := by
  rintro ⟨c,hc,hbound⟩
  have h := hbound (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  simp [realBasisCombinationData,scaleJetData,Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan,actualZeroJetSum,
    zeroComplex,zeroJordan] at h
  linarith

end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedArithmeticPhysical.lean; SHA256 550876c3fb6997256437c159c5de514685305c76124b358fd5385a4f038885aa -/
section

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Zeta23 Zeta23.CCM Zeta23.OPICA Zeta23.ExceptionalZero Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit2_expected_literal_raw_high_mask :
    Tendsto (fun T : ℝ => Real.log (1+max
      (∫ t in Icc (T-2*Real.log T) T,
        finiteHighPair (nativeRawPaletteDrive 1 1) (driveIndexBound T)
          (balancedInverseCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T)) 2)
          (balancedInverseCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T)) 2)
          (fun u : ℝ => Real.exp (Real.sqrt u)) t) 0)/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) :=
  fixed_two_factor_mask_rate_theta.1

theorem FullAudit2_expected_literal_absorbed_high_mask :
    Tendsto (fun T : ℝ => Real.log (1+max
      (∫ t in Icc (T-2*Real.log T) T,
        finiteHighPair (nativeAbsorbedPaletteDrive 1 2 1 (by norm_num)) (driveIndexBound T)
          ((nativeLargeCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T))^2 : ArithmeticFunction ℝ))
          ((nativeLargeCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T))^2 : ArithmeticFunction ℝ))
          (fun u : ℝ => Real.exp (Real.sqrt u)) t) 0)/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) :=
  fixed_two_factor_mask_rate_theta.2

theorem FullAudit2_expected_quiet_full_original_domain
    (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop)
    (quiet :
      (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
        Real.log (1+max (nativeRawHigh 1 2 1 (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon) ∨
      (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
        Real.log (1+max (nativeAbsorbedHigh 1 2 1 (by norm_num)
          (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon)) :
    nativeZeroDisplacementSup=0 ∧
    (∀ epsilon : ℝ, 0 < epsilon → MemLp
      (fun t : ℝ => ((Real.exp (-epsilon*t)*primeFieldFamily 0 t : ℝ) : ℂ)) 2 volume) ∧
    (∀ epsilon : ℝ, 0 < epsilon →
      (∫⁻ t : ℝ in Ici 0, ENNReal.ofReal
        (Real.exp (-2*epsilon*t)*|primeFieldFamily 0 t|^2)) < ∞) ∧
    RiemannHypothesis := by
  have h := quiet_balanced_observation_implies_native_cut time cofinal quiet
  refine ⟨h.1,h.2.1,?_,h.2.2.2.2⟩
  simpa only [NativeOriginalPrimeFieldAllDampedIntegral,
    sourceFamily_zero_eq_original.2.1] using h.2.2.2.1

theorem FullAudit2_expected_zero_supremum_all_positive_dampings
    (theta_zero : nativeZeroDisplacementSup=0) :
    ∀ epsilon : ℝ, 0 < epsilon → MemLp
      (fun t : ℝ => ((Real.exp (-epsilon*t)*primeFieldFamily 0 t : ℝ) : ℂ)) 2 volume :=
  originalPrimeField_allDampedL2_of_native_theta_zero theta_zero

/-- The upper law is precisely as strong as zero displacement. This is a
logical strength audit; no independent quiet upper law is supplied. -/
theorem FullAudit2_complete_quiet_upper_iff_zero_supremum
    (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop) :
    ((∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
      Real.log (1+max (nativeRawHigh 1 2 1 (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon) ∨
     (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
      Real.log (1+max (nativeAbsorbedHigh 1 2 1 (by norm_num)
        (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon)) ↔
      nativeZeroDisplacementSup=0 := by
  constructor
  · intro quiet
    exact (quiet_balanced_observation_implies_native_cut time cofinal quiet).1
  · intro theta_zero
    left
    intro epsilon hepsilon
    have h := (tendsto_order.1
      (fixed_two_factor_mask_rate_theta.1.comp cofinal)).2 epsilon
      (by simpa only [theta_zero] using hepsilon)
    filter_upwards [h] with n hn
    exact le_of_lt hn

/-- This auxiliary sequence is an adversarial logical control, not a native
prime-field observation. Every finite quiet prefix can coexist with rate one. -/
theorem FullAudit2_finite_quiet_samples_do_not_supply_cofinal_upper (N : ℕ) :
    ∃ rate : ℕ → ℝ, (∀ n ≤ N, rate n=0) ∧ Tendsto rate atTop (𝓝 1) := by
  refine ⟨fun n => if n ≤ N then 0 else 1,?_,?_⟩
  · intro n hn
    exact if_pos hn
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop N] with n hn
    simp [not_le_of_gt hn]

end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedAuxiliary.lean; SHA256 133c23de7e4f473575d0a18645dc47ae9924c73fe1066c00d63ccb069da31623 -/
section

/-! Independent expected statements and actual-domain/boundary uses for the
three original auxiliary-completion roots. No theorem type is inferred or
reconstructed from a compiler reflection API. -/
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology FourierTransform
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem expected_aux_completion_actual_transform :
    (∀ k : ℕ, ∀ z : ℂ, -((k:ℝ)+3/2)<z.re →
      Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(auxCompletionFilter k t:ℂ)) ∧
      (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(auxCompletionFilter k t:ℂ))=auxRationalFactor k z) ∧
    (∀ k : ℕ, ∀ z : ℂ, 1/2<z.re →
      auxCompletionLaplace k z=auxRationalFactor k z*riemannZeta (z+1/2)) ∧
    (∀ k : ℕ, 1≤k → ∀ z : ℂ, -((k:ℝ)+1/2)<z.re →
      Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(auxCompletionKernel k t:ℂ)) ∧
      AnalyticAt ℂ (auxCompletionLaplace k) z ∧
      auxCompletionLaplace k z=auxCompletionFilledTransform k z) ∧
    (∀ k : ℕ, 1≤k → auxCompletionLaplace k (1/2)=
      (Nat.factorial (k+1):ℂ)/(Nat.factorial (2*k+3):ℂ)) := by
  exact aux_completion_actual_transform

theorem expected_aux_completion_uniform_decay (k : ℕ) (hk : 1≤k) :
    (∀ t : ℝ, Summable (fun n : ℤ =>
      𝓕 (auxScaledProfile k (Real.exp (-t))) n)) ∧
    (∀ t : ℝ, |auxCompletionKernel k t|≤
      auxCompletionBound k*Real.exp (-((k:ℝ)+1/2)*t)) := by
  exact aux_completion_uniform_decay k hk

theorem expected_aux_completion_ratio_bounds (rho : Zeta23.zetaZeroConfig.carrier) (hright : 1/2<(rho:ℂ).re) :
    ∃ Cp : ℝ, 0<Cp ∧ ∀ k : ℕ, 1≤k →
      (∫ t : ℝ, ‖auxCompletionFilter k t‖)≤2/(Nat.factorial (k+1):ℝ) ∧
      (∫ t : ℝ, ‖auxCompletionFilter k t‖)/‖auxRationalFactor k ((rho:ℂ)-1/2)‖≤
        Real.exp (Cp*(k+1)) ∧
      Real.exp (-(k:ℝ)*Real.log (k+1)-Cp*(k+1))≤
        ‖auxRationalFactor k ((rho:ℂ)-1/2)‖/auxCompletionBound k := by
  exact aux_completion_ratio_bounds rho hright

/-- Actual half-point value, not a cancelled meromorphic-expression value. -/
theorem FullAudit3_example_43 : auxCompletionLaplace 1 (1/2)=1/60 := by
  have h := aux_completion_actual_transform.2.2.2 1 (by norm_num)
  norm_num at h ⊢
  exact h

/-- Original filter identity still covers order zero and its full safe domain. -/
theorem FullAudit3_example_49 (z : ℂ) (hz : -(3/2:ℝ)<z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z*(t:ℂ))*(auxCompletionFilter 0 t:ℂ)) ∧
    (∫ t : ℝ, Complex.exp (-z*(t:ℂ))*(auxCompletionFilter 0 t:ℂ))=
      auxRationalFactor 0 z := by
  exact aux_completion_actual_transform.1 0 z (by simpa using hz)

/-- The improved kernel domain extends strictly left of the original half-plane. -/
theorem FullAudit3_example_56 : AnalyticAt ℂ (auxCompletionLaplace 2) (-2:ℂ) := by
  exact (aux_completion_actual_transform.2.2.1 2 (by norm_num) (-2) (by norm_num [auxCompletionAlpha])).2.1

theorem FullAudit3_example_59 (k : ℕ) (hk : 1≤k) (epsilon : ℝ) (he : -((k:ℝ)+1/2)<epsilon) :
    MemLp (Zeta23.OPICA.weightedCausalProfile epsilon
      (fun t => (auxCompletionKernel k t:ℂ))) 2 volume := by
  exact auxCompletion_weightedL2 k hk epsilon he

/-- Explicit negative frequency is included, and zero frequency is treated separately. -/
theorem FullAudit3_example_65 (k : ℕ) (xi : ℝ) (hxi : xi<0) :
    ‖auxProfileFourierIntegral k xi‖≤
      (1+(2:ℝ)^(3*k+4))/(2*Real.pi*|xi|)^(k+1) := by
  exact auxCompletionProfile_fourier_decay k xi (ne_of_lt hxi)

theorem FullAudit3_example_70 (k : ℕ) : auxProfileFourierIntegral k 0=0 := auxProfileFourier_zero k

theorem FullAudit3_example_72 (psi : ℝ→ℂ) (hpsi : ContDiff ℝ (⊤:ℕ∞) psi) :
    (-1:ℂ)*(∫ u : ℝ,(auxCompletionProfile 0 u:ℂ)*deriv psi u)=
      (∫ u : ℝ in 0..1, Complex.ofReal ((auxProfilePolynomial 0).derivative.eval u)*psi u)-psi 1 := by
  simpa only [Nat.zero_add,Function.iterate_one,iteratedDeriv_one,pow_one,neg_mul,
    one_mul,sub_eq_add_neg] using auxCompletionProfile_distributional_derivative 0 psi hpsi

end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedBoundaryAmplitude.lean; SHA256 b114b1a7ac9e264cac4f6cf4606ac9a4d6b1b9f4f28b5853dbf11dc6d86ec6cc -/
section

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.generic_forced_profile_unique`
and `Zeta23.OPICAFollowup.generic_boundary_amplitude` (F3).

Definition audits pin the boundary amplitude ζ(ρ)/b_ρ and the generic forced profile
h̃ = 1 - S_ρ/b_ρ - ζ(ρ) x^(ρ-1)/b_ρ built from the actual finite sums, with its explicit
derivative. Both roots are restated in full. Domain consumers check:
- at an actual off-line zero with 1/2 < Re ρ < 1 the generic profile is the zero profile, and the
  two routes (F2 and F3) to the forced log-resolvent agree;
- the plateau diagnostic: a nonzero boundary amplitude means h̃ ≢ 1 on (0, 1), and h̃ is then
  unbounded near 0, so it is not a sharp-gap profile;
- no L¹ assertion is possible in general: if ζ(1 - ρ) ≠ 0 then h̃ is not integrable on (1, ∞),
  because its retained homogeneous term x^(-ρ) is not;
- the generic profile is the only log-form-domain solution of the actual force equation. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real SchwartzMap
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit4_audit_boundaryAmplitude (ρ : ℂ) :
    boundaryAmplitude ρ = riemannZeta ρ / normalizationBrho ρ := rfl

theorem FullAudit4_audit_genericForcedProfile (ρ : ℂ) (x : ℝ) :
    genericForcedProfile ρ x =
      (1 - finiteSumSrho ρ |x| / normalizationBrho ρ) -
        riemannZeta ρ / normalizationBrho ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) := rfl

theorem FullAudit4_audit_genericForcedProfileDeriv (ρ : ℂ) (x : ℝ) :
    genericForcedProfileDeriv ρ x =
      zeroProfileDeriv ρ x - riemannZeta ρ / normalizationBrho ρ * ((ρ - 1) * (x : ℂ) ^ (ρ - 2)) := rfl

theorem FullAudit4_audit_normalizationBrho (ρ : ℂ) : normalizationBrho ρ = (1 - 2 * ρ) / (ρ * (1 - ρ)) := rfl

/-! ### Restated roots -/

theorem expected_generic_forced_profile_unique {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    (him : ρ.im ≠ 0) :
    LogFormDomain (genericForcedProfile ρ) (genericForcedProfileDeriv ρ) ∧
    (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * genericForcedProfileDeriv ρ x * deriv φ x) =
        spectralKappa ρ * ((∫ x in Ioi (0 : ℝ), (genericForcedProfile ρ x - 1) * φ x) +
          ∑' n : ℕ, φ (n + 1))) ∧
    (∀ g g' : ℝ → ℂ, LogFormDomain g g' →
      (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
        (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * g' x * deriv φ x) =
          spectralKappa ρ * ((∫ x in Ioi (0 : ℝ), (g x - 1) * φ x) + ∑' n : ℕ, φ (n + 1))) →
      ∀ x : ℝ, 0 < x → g x = genericForcedProfile ρ x) ∧
    LogH1 (logUnitary (genericForcedProfile ρ))
      (logUnitaryDeriv (genericForcedProfile ρ) (genericForcedProfileDeriv ρ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ),
      (∫ t, logUnitaryDeriv (genericForcedProfile ρ) (genericForcedProfileDeriv ρ) t * deriv φ t) +
        (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (genericForcedProfile ρ) t * φ t =
          spectralKappa ρ * nativeLogForce φ) ∧
    (∀ D D' : ℝ → ℂ, LogH1 D D' →
      (∀ φ : 𝓢(ℝ, ℂ), (∫ t, D' t * deriv φ t) + (1 / 4 - spectralKappa ρ) * ∫ t, D t * φ t =
        spectralKappa ρ * nativeLogForce φ) → D = logUnitary (genericForcedProfile ρ)) ∧
    (∀ ξ : ℝ, logFourier (logUnitary (genericForcedProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ)) ∧
    logUnitary (genericForcedProfile ρ) = nativeLogResolvent (spectralKappa ρ) ∧
    (∀ x : ℝ, 0 < x → x ≤ 1 →
      ‖genericForcedProfile ρ x‖ ≤ (1 + ‖boundaryAmplitude ρ‖) * x ^ (ρ.re - 1)) ∧
    (∀ x : ℝ, 0 < x → x < 1 →
      ‖genericForcedProfileDeriv ρ x‖ = ‖boundaryAmplitude ρ * (ρ - 1)‖ * x ^ (ρ.re - 2)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖genericForcedProfile ρ x‖ ≤ C * x ^ (-ρ.re)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ‖genericForcedProfileDeriv ρ x‖ ≤ C * x ^ (-ρ.re - 1)) :=
  generic_forced_profile_unique h12 h1 him

theorem expected_generic_boundary_amplitude {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) :
    boundaryAmplitude ρ = riemannZeta ρ / normalizationBrho ρ ∧
    normalizationBrho ρ = (1 - 2 * ρ) / spectralKappa ρ ∧
    (∀ x ∈ Ioo (0 : ℝ) 1, genericForcedProfile ρ x = 1 - boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1)) ∧
    ((∀ x ∈ Ioo (0 : ℝ) 1, genericForcedProfile ρ x = 1) ↔ riemannZeta ρ = 0) ∧
    (riemannZeta ρ = 0 → genericForcedProfile ρ = zeroProfile ρ) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖genericForcedProfile ρ x - (-(riemannZeta (1 - ρ) / normalizationBrho ρ) * (x : ℂ) ^ (-ρ) +
        spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2))‖ ≤ C * x ^ (-3 : ℝ)) :=
  generic_boundary_amplitude h12 h1

/-! ### Domain consumers -/

/-- At an actual off-line zero with 1/2 < Re ρ < 1 the generic profile is the zero profile, and the
F2 and F3 identifications of the forced log-resolvent agree. -/
theorem FullAudit4_expected_actual_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    (him : ρ.im ≠ 0) :
    genericForcedProfile ρ = zeroProfile ρ ∧
    logUnitary (zeroProfile ρ) = nativeLogResolvent (spectralKappa ρ) ∧
    logUnitary (genericForcedProfile ρ) = logUnitary (zeroProfile ρ) := by
  have hE := (generic_boundary_amplitude h12 h1).2.2.2.2.1 hz
  have hF3 := (generic_forced_profile_unique h12 h1 him).2.2.2.2.2.2.2.1
  rw [hE] at hF3
  exact ⟨hE, hF3, by rw [hE]⟩

/-- A nonzero boundary amplitude destroys the plateau, and h̃ is then unbounded near 0. -/
theorem FullAudit4_expected_no_plateau {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1) (hζ : riemannZeta ρ ≠ 0) :
    (∃ x ∈ Ioo (0 : ℝ) 1, genericForcedProfile ρ x ≠ 1) ∧
    ∀ B : ℝ, ∃ x ∈ Ioo (0 : ℝ) 1, B < ‖genericForcedProfile ρ x‖ := by
  obtain ⟨-, -, hBA, hiff, -⟩ := generic_boundary_amplitude h12 h1
  refine ⟨?_, fun B => ?_⟩
  · by_contra h
    exact hζ (hiff.mp fun x hx => not_not.mp fun hne => h ⟨x, hx, hne⟩)
  · have h0 : 0 < ρ.re := by linarith
    have hh : ρ ≠ 1 / 2 := fun h => by rw [h] at h12; norm_num at h12
    obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
    have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
    have hA : 0 < ‖boundaryAmplitude ρ‖ := norm_pos_iff.mpr (div_ne_zero hζ hb)
    -- choose x small so that ‖A‖ x^(Re ρ - 1) > B + 1
    set r := 1 - ρ.re
    have hr : 0 < r := by simp only [r]; linarith
    set y := (max B 0 + 2) / ‖boundaryAmplitude ρ‖
    have hy : 0 < y := by positivity
    set x := min (1 / 2) (y ^ (-(1 / r))) with hxdef
    have hx0 : 0 < x := lt_min (by norm_num) (Real.rpow_pos_of_pos hy _)
    have hx1 : x < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
    refine ⟨x, ⟨hx0, hx1⟩, ?_⟩
    rw [hBA x ⟨hx0, hx1⟩]
    have hp : ‖(x : ℂ) ^ (ρ - 1)‖ = x ^ (-r) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx0]; simp [r]
    have hpow : y ≤ x ^ (-r) := by
      have hle : x ≤ y ^ (-(1 / r)) := min_le_right _ _
      have := Real.rpow_le_rpow_of_nonpos hx0 hle (by linarith : -r ≤ 0)
      rwa [← Real.rpow_mul hy.le, show -(1 / r) * -r = 1 by field_simp, Real.rpow_one] at this
    have hbig : max B 0 + 2 ≤ ‖boundaryAmplitude ρ‖ * x ^ (-r) := by
      calc max B 0 + 2 = ‖boundaryAmplitude ρ‖ * y := by simp only [y]; field_simp
        _ ≤ _ := by gcongr
    have htri : ‖boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1)‖ - 1 ≤
        ‖1 - boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1)‖ := by
      have := norm_sub_norm_le (boundaryAmplitude ρ * (x : ℂ) ^ (ρ - 1)) 1
      rw [norm_one, norm_sub_rev] at this; linarith
    rw [norm_mul, hp] at htri
    linarith [le_max_left B 0]

/-- No L¹ assertion in general: when ζ(1 - ρ) ≠ 0 the generic profile is not integrable on (1, ∞). -/
theorem FullAudit4_expected_not_integrable {ρ : ℂ} (h12 : 1 / 2 < ρ.re) (h1 : ρ.re < 1)
    (hζ' : riemannZeta (1 - ρ) ≠ 0) :
    ¬ IntegrableOn (genericForcedProfile ρ) (Ioi 1) := by
  intro hI
  have h0 : 0 < ρ.re := by linarith
  have hh : ρ ≠ 1 / 2 := fun h => by rw [h] at h12; norm_num at h12
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hb := normalizationBrho_ne_zero hρ0 hρ1 hh
  obtain ⟨-, -, -, -, -, C, hC0, hC⟩ := generic_boundary_amplitude h12 h1
  set c := -(riemannZeta (1 - ρ) / normalizationBrho ρ)
  have hc : c ≠ 0 := neg_ne_zero.mpr (div_ne_zero hζ' hb)
  -- the Bernoulli term and the remainder are integrable on (1, ∞)
  have hB : IntegrableOn (fun x : ℝ => spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2)) (Ioi 1) := by
    refine ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-2 : ℝ) < -1) one_pos).const_mul
      (‖spectralKappa ρ‖ / 2)).mono' ?_ ((ae_restrict_iff' measurableSet_Ioi).mpr
        (Eventually.of_forall fun x hx => ?_))
    · exact ((measurable_const.mul (Complex.measurable_ofReal.comp measurable_bernoulliTwo)).div
        (measurable_const.mul (Complex.measurable_ofReal.pow_const 2))).aestronglyMeasurable
    · have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
      rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real, Complex.norm_ofNat,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0, Real.rpow_neg hx0.le, Real.rpow_two]
      have := abs_bernoulliTwo_le x
      have hx2 : 0 < x ^ 2 := by positivity
      rw [div_le_iff₀ (by positivity)]
      field_simp
      nlinarith [norm_nonneg (spectralKappa ρ)]
  have hmeas : AEStronglyMeasurable (fun x : ℝ => c * (x : ℂ) ^ (-ρ) +
      spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2)) (volume.restrict (Ioi 1)) :=
    ((measurable_const.mul (Complex.measurable_ofReal.pow_const _)).add
      ((measurable_const.mul (Complex.measurable_ofReal.comp measurable_bernoulliTwo)).div
        (measurable_const.mul (Complex.measurable_ofReal.pow_const 2)))).aestronglyMeasurable
  have hR : IntegrableOn (fun x : ℝ => genericForcedProfile ρ x -
      (c * (x : ℂ) ^ (-ρ) + spectralKappa ρ * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2))) (Ioi 1) :=
    Integrable.mono' ((integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 : ℝ) < -1) one_pos).const_mul C)
      (hI.aestronglyMeasurable.sub hmeas)
      ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun x hx => hC x (le_of_lt hx)))
  have hpow : IntegrableOn (fun x : ℝ => c * (x : ℂ) ^ (-ρ)) (Ioi 1) :=
    ((hI.sub hR).sub hB).congr (Eventually.of_forall fun x => by simp only [Pi.sub_apply]; ring)
  have hnorm : IntegrableOn (fun x : ℝ => x ^ (-ρ.re)) (Ioi 1) := by
    refine (hpow.norm.const_mul ‖c‖⁻¹).congr ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := lt_trans one_pos hx
    simp only
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0, ← mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hc), one_mul]
    simp
  have := (integrableOn_Ioi_rpow_iff one_pos).mp hnorm
  linarith

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedBudgetLimit.lean; SHA256 24665dcf253694e0d76c0f9555b10f23aa3cdf1f5122d0dc6c1adbd8e88c9668 -/
section

/-!
Post-green supporting consequence, outside the original primary-root inventory.

The basis is fixed and independent in the literal actual real zero-jet
distribution space. The negative mass is global off-lattice sinc-squared
mass of the canonical Jordan negative measure of the actual combination.
The only quantitative input is the original full fixed-basis budget.
-/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23 Zeta23.OPICA Zeta23.OPICAFollowup
open Zeta23.OPICAFollowup.FiniteSpan

namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit5_coefficients_tendsto_zero_of_actual_negative_mass_tendsto_zero {n : ℕ}
    (basis : Fin n → List (ℂ × ℂ × ℕ))
    (valid : ∀ i, ∀ j ∈ basis i, riemannZeta j.2.1 = 0 ∧
      0 < j.2.1.re ∧ j.2.1.re < 1 ∧ j.2.2 < zeroJetOrder j.2.1)
    (independent : LinearIndependent ℝ (fun i =>
      (actualZeroJetSum (basis i)).rePart.distributionOfLinearGrowth
        (zeroJetRealSpan_growth (basis i) (valid i))))
    (a : ℕ → EuclideanSpace ℝ (Fin n))
    (hmass : Tendsto (fun k => ∫ x in (Set.range (fun m : ℤ => (m : ℝ)))ᶜ,
      sincSquared x ∂(actualZeroJetSum ((List.ofFn (fun i =>
        (basis i).map (fun j => (((a k i : ℝ) : ℂ) * j.1, j.2.1, j.2.2)))).flatten)).rePart.negative)
      atTop (𝓝 0)) :
    Tendsto a atTop (𝓝 0) := by
  obtain ⟨c, hc, hbound⟩ :=
    Zeta23.OPICAFollowup.fixed_basis_negative_mass_budget basis valid independent
  have hdiv : Tendsto (fun k => (∫ x in (Set.range (fun m : ℤ => (m : ℝ)))ᶜ,
      sincSquared x ∂(actualZeroJetSum ((List.ofFn (fun i =>
        (basis i).map (fun j => (((a k i : ℝ) : ℂ) * j.1, j.2.1, j.2.2)))).flatten)).rePart.negative) / c)
      atTop (𝓝 0) := by
    simpa only [zero_div] using hmass.div_const c
  refine squeeze_zero_norm (fun k => ?_) hdiv
  apply (le_div_iff₀ hc).2
  have hb : c * ‖a k‖ ≤ ∫ x in (Set.range (fun m : ℤ => (m : ℝ)))ᶜ,
      sincSquared x ∂(actualZeroJetSum ((List.ofFn (fun i =>
        (basis i).map (fun j => (((a k i : ℝ) : ℂ) * j.1, j.2.1, j.2.2)))).flatten)).rePart.negative := by
    simpa only [realBasisCombinationData, scaleJetData,
      Zeta23.OPICAFollowup.zeroJetRealSpan,
      Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan, integerLattice] using hbound (a k)
  simpa only [mul_comm] using hb


end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedComb.lean; SHA256 3a5305b65175d6b046075ecbebc9a9f37690e6677bb74ed9d3bd8796d58100f9 -/
section

/-! Independent full-type and actual-domain consumers for the original comb root. -/
noncomputable section
open Set MeasureTheory
open scoped FourierTransform SchwartzMap ENNReal
namespace Zeta23.OPICAFollowup.Validation
theorem expected_dilated_comb_fourier :
    ∀ t : ℝ,
      (∀ R : ℝ, 0≤R → dilatedCombMeasure t (Icc (-R) R)≤
        ENNReal.ofReal (Real.exp (t/2)*(3+2*Real.exp (-t)*R))) ∧
      (∀ f : SchwartzMap ℝ ℂ, Summable (fun n : ℤ => f (Real.exp t*(n:ℝ))) ∧
        dilatedCombDistribution t f=(Real.exp (t/2):ℂ)*∑' n : ℤ, f (Real.exp t*(n:ℝ))) ∧
      𝓕 (dilatedCombDistribution t)=dilatedCombDistribution (-t) :=
  dilated_comb_fourier

theorem FullAudit6_expected_comb_actual_carrier (t : ℝ) :
    dilatedCombMeasure t=
      ENNReal.ofReal (Real.exp (t/2)) •
        Measure.map (fun n : ℤ => Real.exp t*(n:ℝ)) (Measure.count : Measure ℤ) := rfl

theorem FullAudit6_expected_comb_origin_amplitude (t : ℝ) :
    dilatedCombMeasure t ({0} : Set ℝ)=ENNReal.ofReal (Real.exp (t/2)) :=
  dilatedCombMeasure_origin t

theorem FullAudit6_expected_comb_unit_selfdual : 𝓕 (dilatedComb 0)=dilatedComb 0 := by
  simpa only [neg_zero] using (dilated_comb_fourier 0).2.2

theorem FullAudit6_expected_comb_positive_negative_lattice (t : ℝ) (n : ℤ) :
    scaledLatticePoint t (-n)=-scaledLatticePoint t n := by
  simp [scaledLatticePoint]

theorem FullAudit6_expected_comb_negative_dilation :
    𝓕 (dilatedComb (-Real.log 2))=dilatedComb (Real.log 2) := by
  simpa only [neg_neg] using (dilated_comb_fourier (-Real.log 2)).2.2

theorem FullAudit6_expected_comb_absolute_pairing (t : ℝ) (f : SchwartzMap ℝ ℂ) :
    Summable (fun n : ℤ => ‖f (Real.exp t*(n:ℝ))‖) ∧
      dilatedComb t f=combPairing t f :=
  ⟨(dilatedComb_schwartz_summable t f).norm,dilatedComb_apply t f⟩


end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedComplex.lean; SHA256 2d84b62e92e93c133bed5b827e44e583db9d22d7c48bc38868f1ddf5c5373c1c -/
section

/-! Full expected interface stated independently of the primary's inferred type.
The domain is the actual locally finite complex carrier, not finite whole-line
ComplexMeasure. Growth is one common bound for the sequence and its limit. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology SchwartzMap
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem expected_complex_local_measure_embedding_faithful :
    (∀ μ : LocallyFiniteComplexMeasure, μ.totalVariation ≤ μ.variationControl ∧
      (μ.HasLinearGrowth ↔ LinearMassGrowth μ.totalVariation)) ∧
    (∀ μ : LocallyFiniteComplexMeasure, ∀ K L : Set ℝ,
      ∀ hK : IsCompact K, ∀ hL : IsCompact L,
      (μ.compactRestriction K hK).restrict L =
        μ.compactRestriction (K ∩ L) (hK.inter_right hL.isClosed)) ∧
    (∀ μ : LocallyFiniteComplexMeasure, ∀ K : Set ℝ, ∀ hK : IsCompact K,
      μ.totalVariation.restrict K = (μ.compactRestriction K hK).variation) ∧
    (∀ μ ν : LocallyFiniteComplexMeasure, ∀ c : ℂ, ∀ K : Set ℝ,
      ∀ hK : IsCompact K,
      (μ.add ν).compactRestriction K hK = μ.compactRestriction K hK + ν.compactRestriction K hK ∧
      (μ.scale c).compactRestriction K hK = c • μ.compactRestriction K hK) ∧
    Function.Injective
      (fun μ : {μ : LocallyFiniteComplexMeasure // μ.HasLinearGrowth} =>
        μ.val.distributionOfLinearGrowth μ.property) ∧
    (∀ μ : LocallyFiniteComplexMeasure, ∀ hμ : μ.HasLinearGrowth, ∀ f : SchwartzMap ℝ ℂ,
      μ.distributionOfLinearGrowth hμ f = μ.integral f ∧
      realifyComplexDistribution (μ.distributionOfLinearGrowth hμ) f =
        μ.rePart.distributionOfLinearGrowth (μ.re_hasLinearGrowth hμ) f) ∧
    (∀ seq : ℕ → LocallyFiniteComplexMeasure, ∀ μ : LocallyFiniteComplexMeasure,
      LocalVariationConvergence seq μ → ∀ f : ℝ → ℂ,
      Continuous f → HasCompactSupport f →
      Tendsto (fun n => (seq n).integral f) atTop (𝓝 (μ.integral f))) ∧
    (∀ seq : ℕ → LocallyFiniteComplexMeasure, ∀ μ : LocallyFiniteComplexMeasure,
      LocalVariationConvergence seq μ → ∀ C : ℝ,
      (∀ n, CommonLinearMassBound C (seq n).variationControl) →
      CommonLinearMassBound C μ.variationControl → ∀ f : SchwartzMap ℝ ℂ,
      Tendsto (fun n => (seq n).integral f) atTop (𝓝 (μ.integral f))) := by
  exact complex_local_measure_embedding_faithful

/-- Growth of genuine Euclidean variation is sufficient: coordinate control
is derived with the required factor two rather than identified with it. -/
theorem FullAudit7_example_45 (μ : LocallyFiniteComplexMeasure) (h : LinearMassGrowth μ.totalVariation) :
    μ.HasLinearGrowth := by
  exact μ.hasLinearGrowth_iff_totalVariation.mpr h

/-- Truly imaginary scalar, arbitrary compact sets, no whole-line finiteness. -/
theorem FullAudit7_example_50 (μ : LocallyFiniteComplexMeasure) (K : Set ℝ) (hK : IsCompact K) :
    (μ.scale I).compactRestriction K hK = I • μ.compactRestriction K hK := by
  exact μ.compactRestriction_scale I K hK

theorem FullAudit7_example_54 (μ ν : LocallyFiniteComplexMeasure) (hμ : μ.HasLinearGrowth)
    (hν : ν.HasLinearGrowth) (c : ℂ) :
    (μ.add (ν.scale c)).HasLinearGrowth := by
  exact μ.hasLinearGrowth_add (ν.scale c) hμ (ν.hasLinearGrowth_scale hν c)

theorem FullAudit7_example_59 (seq : ℕ → LocallyFiniteComplexMeasure) (μ : LocallyFiniteComplexMeasure)
    (hlocal : LocalVariationConvergence seq μ) (C : ℝ)
    (hseq : ∀ n, CommonLinearMassBound C (seq n).variationControl)
    (hμ : CommonLinearMassBound C μ.variationControl) (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (seq n).distributionOfLinearGrowth (hseq n).linearGrowth f)
      atTop (𝓝 (μ.distributionOfLinearGrowth hμ.linearGrowth f)) := by
  exact hlocal.tendsto_schwartz_common_growth C hseq hμ f

/-- The quantitative tail comes from the same fixed growth and test budgets. -/
theorem FullAudit7_example_68 (μ : LocallyFiniteComplexMeasure) (C M R : ℝ)
    (hg : CommonLinearMassBound C μ.variationControl) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (f : SchwartzMap ℝ ℂ) (hd : ∀ x, |x|^3 * ‖f x‖ ≤ M) :
    ‖μ.integral f - finiteComplexIntegral
      (μ.compactRestriction (Icc (-R) R) isCompact_Icc) f‖ ≤ 4*C*M/R^2 := by
  exact complexIntegral_cutoff_error μ C M R hg hM hR f hd

end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedConfluentProfiles.lean; SHA256 5862885c0235798817be2103c3ae600638327c1b0cc26916ea59e2ad133d6aed -/
section

noncomputable section
open Set MeasureTheory Filter Complex Finset
open scoped Topology SchwartzMap FourierTransform
namespace Zeta23.OPICAFollowup.Validation
open Zeta23.OPICAFollowup

/-- Independent full determinant type: the matrix entries and both exact
grouped products are written explicitly. -/
theorem expected_profile_jet_confluent_determinant {r : ℕ} (κ : Fin r → ℂ)
    (hκ : Function.Injective κ) (hκ0 : ∀ j, κ j ≠ 0) (m : Fin r → ℕ) :
    (Matrix.of (fun n i : Fin (∑ j, m j) =>
      iteratedDeriv (((Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm i).2 : ℕ)
        (fun w : ℂ => w * (1 / 4 - w) ^ (n : ℕ))
        (κ ((Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm i).1) /
          ((((Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm i).2 : ℕ).factorial : ℂ))).det =
      (-1 : ℂ) ^ ((∑ j, m j) * ((∑ j, m j) - 1) / 2) *
        (∏ j, κ j ^ m j) * ∏ j, ∏ i ∈ Iio j, (κ j - κ i) ^ (m i * m j) := by
  exact profile_jet_confluent_determinant κ hκ hκ0 m

/-- Independent full physical type, retaining every actual zero hypothesis,
the reflection quotient, and exactly the available multiplicity jets. -/
theorem expected_finite_zero_jet_independent {r : ℕ} (ρ : Fin r → ℂ)
    (hz : ∀ j, riemannZeta (ρ j) = 0)
    (h0 : ∀ j, 0 < (ρ j).re) (h1 : ∀ j, (ρ j).re < 1)
    (hdist : Function.Injective (fun j => (ρ j) * (1 - ρ j))) :
    LinearIndependent ℂ (fun p : (j : Fin r) × Fin (zeroJetOrder (ρ j)) =>
      (normalizedZeroMeasureJet (ρ p.1) (p.2 : ℕ)).distributionOfLinearGrowth
        (normalizedZeroMeasureJet_hasLinearGrowth (h0 p.1) (h1 p.1)
          (zero_ne_half (hz p.1)) p.2.isLt)) := by
  exact finite_zero_jet_independent ρ hz h0 h1 hdist

theorem FullAudit8_expected_exact_local_column {r : ℕ} (κ : Fin r → ℂ) (m : Fin r → ℕ)
    (n : Fin (∑ j, m j)) (j : Fin r) (k : Fin (m j)) :
    profileJetMatrix κ m n (Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupIndex m ⟨j, k⟩) =
      iteratedDeriv (k : ℕ) (fun w : ℂ => w * (1 / 4 - w) ^ (n : ℕ)) (κ j) /
        ((k : ℕ).factorial : ℂ) := by
  have he : (Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm
      (Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupIndex m ⟨j, k⟩) = ⟨j, k⟩ :=
    (Zeta23.OPICAFollowup.OPICAGroupedConfluent.groupEquiv m).symm_apply_apply ⟨j, k⟩
  have hkcol := congrArg (fun p : (j : Fin r) × Fin (m j) => (p.2 : ℕ)) he
  have hjcol := congrArg (fun p : (j : Fin r) × Fin (m j) => p.1) he
  unfold profileJetMatrix
  rw [hkcol, hjcol]

end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedCoPoissonFamily.lean; SHA256 1fd0255554f7a095a9ae441731c4329ea3220f994d7d5a9713fc42ada7073cfe -/
section

/- Independent consumers for the original R1-CP1 root
`Zeta23.OPICAFollowup.renormalized_copoisson_tempered_family`.

Definition audits pin A_t, K_t and the family V_lam to their constructions from the actual
dilated comb distribution and the Dirac delta. The root is restated in full. Domain consumers
check the literal pairing of (CP1.1) on every Schwartz test,
K_t(φ) = e^(t/2) Σ φ(e^t n) + e^(-t/2) Σ φ(e^(-t) n) - e^(t/2) (φ(0) + ∫ φ),
the paper's decay constant 2ζ(N) at N = 2, analyticity of V_lam(φ) on all of ℂ, and the
self-dual pairing V_lam(𝓕φ) = V_lam(φ). -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit9_audit_coPoissonA (t : ℝ) : coPoissonA t = dilatedCombDistribution t -
    ((Real.exp (t / 2) : ℝ) : ℂ) • TemperedDistribution.delta (0 : ℝ) := rfl

theorem FullAudit9_audit_kernel (t : ℝ) : renormalizedCombKernel t = coPoissonA t + 𝓕 (coPoissonA t) := rfl

theorem FullAudit9_audit_family (lam : ℂ) : coPoissonFamily lam = coPoissonW lam + 𝓕 (coPoissonW lam) := rfl

theorem FullAudit9_audit_W_apply (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonW lam φ = ∫ t in Ioi (0 : ℝ), cexp (-lam * t) * coPoissonA t φ := rfl

/-! ### Restated root -/

theorem expected_renormalized_copoisson_tempered_family :
    (∀ t : ℝ, renormalizedCombKernel t = dilatedCombDistribution t +
      dilatedCombDistribution (-t) - ((Real.exp (t / 2) : ℝ) : ℂ) •
        (TemperedDistribution.delta (0 : ℝ) + 𝓕 (TemperedDistribution.delta (0 : ℝ)))) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (𝓕 (TemperedDistribution.delta (0 : ℝ))) φ = ∫ x, φ x) ∧
    (∀ (t : ℝ) (φ : 𝓢(ℝ, ℂ)), coPoissonA t φ = (Real.exp (t / 2) : ℂ) *
      ∑' n : ℤ, if n = 0 then 0 else φ (Real.exp t * n)) ∧
    (∀ (t : ℝ) (φ : 𝓢(ℝ, ℂ)) (k : ℕ), 2 ≤ k → ‖coPoissonA t φ‖ ≤
      latticeZetaConst k * SchwartzMap.seminorm ℂ k 0 φ * Real.exp ((1 / 2 - k) * t)) ∧
    (∀ k : ℕ, 2 ≤ k → ((latticeZetaConst k : ℝ) : ℂ) = 2 * riemannZeta k) ∧
    (∀ t : ℝ, 𝓕 (renormalizedCombKernel t) = renormalizedCombKernel t) ∧
    (∀ (t : ℝ) (φ : 𝓢(ℝ, ℂ)),
      renormalizedCombKernel t (schwartzReflect φ) = renormalizedCombKernel t φ) ∧
    (∀ (lam : ℂ) (φ : 𝓢(ℝ, ℂ)),
      IntegrableOn (fun t : ℝ => cexp (-lam * t) * renormalizedCombKernel t φ) (Ioi 0)) ∧
    (∀ (lam : ℂ) (φ : 𝓢(ℝ, ℂ)), coPoissonFamily lam φ =
      ∫ t in Ioi (0 : ℝ), cexp (-lam * t) * renormalizedCombKernel t φ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), Differentiable ℂ (fun lam : ℂ => coPoissonFamily lam φ)) ∧
    (∀ lam : ℂ, 𝓕 (coPoissonFamily lam) = coPoissonFamily lam) ∧
    (∀ (lam : ℂ) (φ : 𝓢(ℝ, ℂ)),
      coPoissonFamily lam (schwartzReflect φ) = coPoissonFamily lam φ) :=
  renormalized_copoisson_tempered_family

/-! ### Domain consumers -/

/-- The literal (CP1.1) pairing on every Schwartz test. -/
theorem FullAudit9_expected_kernel_pairing (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    renormalizedCombKernel t φ =
      (Real.exp (t / 2) : ℂ) * ∑' n : ℤ, φ (Real.exp t * n) +
      (Real.exp (-t / 2) : ℂ) * ∑' n : ℤ, φ (Real.exp (-t) * n) -
      (Real.exp (t / 2) : ℂ) * (φ 0 + ∫ x, φ x) := by
  rw [(renormalized_copoisson_tempered_family.1 t)]
  simp only [sub_apply, add_apply, smul_apply, smul_eq_mul, TemperedDistribution.delta_apply]
  rw [renormalized_copoisson_tempered_family.2.1 φ, dilatedCombDistribution_apply,
    dilatedCombDistribution_apply, neg_div]

/-- The paper's constant: |⟨A_t, φ⟩| ≤ 2ζ(2) p_2(φ) e^(-3t/2). -/
theorem FullAudit9_expected_decay_N2 (t : ℝ) (φ : 𝓢(ℝ, ℂ)) :
    ‖coPoissonA t φ‖ ≤ latticeZetaConst 2 * SchwartzMap.seminorm ℂ 2 0 φ *
        Real.exp (-(3 / 2) * t) ∧
    ((latticeZetaConst 2 : ℝ) : ℂ) = 2 * riemannZeta 2 := by
  refine ⟨?_, renormalized_copoisson_tempered_family.2.2.2.2.1 2 le_rfl⟩
  have h := renormalized_copoisson_tempered_family.2.2.2.1 t φ 2 le_rfl
  convert h using 3
  norm_num

/-- Entire family: V_lam(φ) is analytic at every complex lam. -/
theorem FullAudit9_expected_family_analytic (φ : 𝓢(ℝ, ℂ)) (lam : ℂ) :
    AnalyticAt ℂ (fun z : ℂ => coPoissonFamily z φ) lam :=
  (renormalized_copoisson_tempered_family.2.2.2.2.2.2.2.2.2.1 φ).analyticAt lam

/-- Self-dual pairing on tests, at every lam (including the strip 0 < Re(1/2 + lam) < 1). -/
theorem FullAudit9_expected_family_selfdual_pairing (lam : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    coPoissonFamily lam (𝓕 φ) = coPoissonFamily lam φ := by
  have h := renormalized_copoisson_tempered_family.2.2.2.2.2.2.2.2.2.2.1 lam
  exact congrArg (fun T : TemperedDistribution ℝ ℂ => T φ) h

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedCoPoissonJets.lean; SHA256 871a4419cbb3c02b699d07be9b815bb119d127cce6ab553a4c1d20afad5d7155 -/
section

/- Independent consumers for the original root `Zeta23.OPICAFollowup.copoisson_zero_jets_measures`
(R2-H1).

Definition audits pin the multiplicity (the analytic order of ζ), the entire κ-family density
built from the actual finite sums, the normalized κ-jets (1/k!) ∂_κ^k, the jet measures (the CP1 zero
measure at order zero, the jet density with its canonical Jordan pairs otherwise), the actual
construction (CP1.7)/b at an arbitrary parameter and the local inverse branch. The root is restated
in full. Domain consumers check:
- at every actual strip zero the order-zero jet exists and is the CP1 zero measure, and its
  parameter limit is the construction itself;
- the k = 0 forced chain is exactly the Stage 11 forced Euler identity of `ForcedEuler`;
- at a zero of multiplicity at least two the first jet is a pure density measure with the exact gap,
  density tail -B₂({|x|})/(2x²) + O(|x|⁻³) and forced equation (L - κ₀) h₁ = h₀ + G;
- the reflected zero gives the same node and the same jets, so it is not a separate node;
- on real tests the jets at the conjugate zero are the conjugate pairings. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology SchwartzMap FourierTransform
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit10_audit_zeroJetOrder (ρ : ℂ) : zeroJetOrder ρ = analyticOrderNatAt riemannZeta ρ := rfl

theorem FullAudit10_audit_shKernel (w : ℂ) (u : ℝ) :
    shKernel w u = ∑' n : ℕ, w ^ n * (u : ℂ) ^ (2 * n + 1) / ((2 * n + 1).factorial : ℂ) := rfl

theorem FullAudit10_audit_zeroFamilyDensity (κ : ℂ) (y : ℝ) :
    zeroFamilyDensity κ y = κ * ∑ k ∈ Finset.Icc 1 ⌊|y|⌋₊,
      ((Real.exp (-Real.log (|y| / k) / 2) / k : ℝ) : ℂ) * shKernel (1 / 4 - κ) (Real.log (|y| / k)) :=
  rfl

theorem FullAudit10_audit_zeroJetDensity (κ₀ : ℂ) (k : ℕ) (y : ℝ) :
    zeroJetDensity κ₀ k y = iteratedDeriv k (fun κ => zeroFamilyDensity κ y) κ₀ / (k.factorial : ℂ) :=
  rfl

theorem FullAudit10_audit_normalizedZeroMeasureJet (ρ : ℂ) (k : ℕ) :
    normalizedZeroMeasureJet ρ k = if k = 0 then zeroMeasure ρ else
      jetDensityMeasure (zeroJetDensity (spectralKappa ρ) k) (measurable_zeroJetDensity _ _)
        (locallyIntegrable_zeroJetDensity _ _) := rfl

theorem FullAudit10_audit_jetDensityMeasure (g : ℝ → ℂ) (hgm : Measurable g) (hg : LocallyIntegrable g volume) :
    (jetDensityMeasure g hgm hg).rePart.positive = volume.withDensity (fun x => ENNReal.ofReal (g x).re) ∧
    (jetDensityMeasure g hgm hg).rePart.negative = volume.withDensity (fun x => ENNReal.ofReal (-(g x).re)) ∧
    (jetDensityMeasure g hgm hg).imPart.positive = volume.withDensity (fun x => ENNReal.ofReal (g x).im) ∧
    (jetDensityMeasure g hgm hg).imPart.negative = volume.withDensity (fun x => ENNReal.ofReal (-(g x).im)) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem FullAudit10_audit_zeroFamilyFunctional (ρ : ℂ) (φ : 𝓢(ℝ, ℂ)) :
    zeroFamilyFunctional ρ φ = (coPoissonFamily (ρ - 1 / 2) φ - 1 / (1 - ρ) * (φ 0 + ∫ x, φ x) -
      normalizationBrho ρ * dilatedCombDistribution 0 φ) / normalizationBrho ρ := rfl

theorem FullAudit10_audit_zeroLocalInverse (ρ₀ κ : ℂ) :
    zeroLocalInverse ρ₀ κ = 1 / 2 + (ρ₀ - 1 / 2) *
      (1 + (spectralKappa ρ₀ - κ) / (ρ₀ - 1 / 2) ^ 2) ^ ((2 : ℕ)⁻¹ : ℂ) := rfl

theorem FullAudit10_audit_zeroJetProfile (κ₀ : ℂ) (k : ℕ) (x : ℝ) :
    zeroJetProfile κ₀ k x = (if k = 0 then 1 else 0) - zeroJetDensity κ₀ k x := rfl

theorem FullAudit10_audit_positiveAxisTest (ψ : ℝ → ℂ) : CoPoissonJets.PositiveAxisTest ψ ↔ PositiveAxisTest ψ :=
  Iff.rfl

/-- The κ-family is the actual zero-measure density at every strip parameter ρ ≠ 1/2. -/
theorem FullAudit10_expected_family_is_actual {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) (hh : ρ ≠ 1 / 2) (y : ℝ) :
    coPoissonComplexDensity ρ y = zeroFamilyDensity (spectralKappa ρ) y :=
  coPoissonComplexDensity_eq_family h0 h1 hh y

/-! ### Restated root -/

theorem expected_copoisson_zero_jets_measures (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (k : ℕ) (hk : k < zeroJetOrder ρ) :
    1 ≤ zeroJetOrder ρ ∧ analyticOrderAt riemannZeta ρ = zeroJetOrder ρ ∧
    (zeroLocalInverse ρ (spectralKappa ρ) = ρ ∧ AnalyticAt ℂ (zeroLocalInverse ρ) (spectralKappa ρ) ∧
      deriv (zeroLocalInverse ρ) (spectralKappa ρ) = -1 / (2 * (ρ - 1 / 2)) ∧
      (∀ κ, spectralKappa (zeroLocalInverse ρ κ) = κ) ∧
      analyticOrderAt (fun κ => riemannZeta (zeroLocalInverse ρ κ)) (spectralKappa ρ) = zeroJetOrder ρ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral φ =
      iteratedDeriv k (fun κ => zeroFamilyFunctional (zeroLocalInverse ρ κ) φ) (spectralKappa ρ) /
        (k.factorial : ℂ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral φ =
      (∫ x, zeroJetDensity (spectralKappa ρ) k x * φ x) -
        if k = 0 then ∑' n : ℤ, (if n = 0 then (0 : ℂ) else φ n) else 0) ∧
    (∀ y : ℝ, zeroJetDensity (spectralKappa ρ) k y =
      iteratedDeriv k (fun κ => zeroFamilyDensity κ y) (spectralKappa ρ) / (k.factorial : ℂ)) ∧
    (k = 0 → normalizedZeroMeasureJet ρ k = zeroMeasure ρ) ∧
    (normalizedZeroMeasureJet ρ k).variationControl (Ioo (-1) 1) = 0 ∧
    (normalizedZeroMeasureJet ρ k).variationControl {0} = 0 ∧
    (Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).rePart.positive =
        (normalizedZeroMeasureJet ρ k).rePart.positive ∧
      Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).rePart.negative =
        (normalizedZeroMeasureJet ρ k).rePart.negative ∧
      Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).imPart.positive =
        (normalizedZeroMeasureJet ρ k).imPart.positive ∧
      Measure.map (fun x : ℝ => -x) (normalizedZeroMeasureJet ρ k).imPart.negative =
        (normalizedZeroMeasureJet ρ k).imPart.negative) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ |y| →
      ‖zeroJetDensity (spectralKappa ρ) k y -
        ((if k = 0 then 1 else 0) - ((if k = 0 then spectralKappa ρ else 0) + (if k = 1 then 1 else 0)) *
          ((bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2)))‖ ≤ C * |y| ^ (-3 : ℝ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) =
      (normalizedZeroMeasureJet ρ k).integral φ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ k).integral (schwartzReflect φ) =
      (normalizedZeroMeasureJet ρ k).integral φ) ∧
    (∃ hL : (normalizedZeroMeasureJet ρ k).HasLinearGrowth,
      𝓕 ((normalizedZeroMeasureJet ρ k).distributionOfLinearGrowth hL) =
          (normalizedZeroMeasureJet ρ k).distributionOfLinearGrowth hL ∧
        𝓕 ((normalizedZeroMeasureJet ρ k).rePart.distributionOfLinearGrowth
            ((normalizedZeroMeasureJet ρ k).re_hasLinearGrowth hL)) =
          (normalizedZeroMeasureJet ρ k).rePart.distributionOfLinearGrowth
            ((normalizedZeroMeasureJet ρ k).re_hasLinearGrowth hL)) ∧
    (∀ ψ : ℝ → ℂ, CoPoissonJets.PositiveAxisTest ψ →
      -(∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) k x *
          deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv ψ y) x) -
        spectralKappa ρ * (∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) k x * ψ x) =
      if k = 0 then spectralKappa ρ * ((∑' n : ℕ, ψ (n + 1)) - ∫ x in Ioi 0, ψ x)
      else if k = 1 then (∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) 0 x * ψ x) +
        ((∑' n : ℕ, ψ (n + 1)) - ∫ x in Ioi 0, ψ x)
      else ∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) (k - 1) x * ψ x) ∧
    (zeroJetOrder (1 - ρ) = zeroJetOrder ρ ∧ spectralKappa (1 - ρ) = spectralKappa ρ ∧
      normalizedZeroMeasureJet (1 - ρ) k = normalizedZeroMeasureJet ρ k ∧
      (∀ κ, zeroLocalInverse (1 - ρ) κ = 1 - zeroLocalInverse ρ κ) ∧
      ∀ φ : 𝓢(ℝ, ℂ), iteratedDeriv k (fun κ => zeroFamilyFunctional (1 - zeroLocalInverse ρ κ) φ)
          (spectralKappa ρ) / (k.factorial : ℂ) = (normalizedZeroMeasureJet ρ k).integral φ) ∧
    (zeroJetOrder (starRingEnd ℂ ρ) = zeroJetOrder ρ ∧
      ∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet (starRingEnd ℂ ρ) k).integral φ =
        starRingEnd ℂ ((normalizedZeroMeasureJet ρ k).integral (complexSchwartzConj φ))) :=
  copoisson_zero_jets_measures ρ hz h0 h1 k hk

/-! ### Domain consumers -/

/-- At every actual strip zero the order-zero jet exists, is the CP1 zero measure, and its parameter
limit is the actual construction itself. -/
theorem FullAudit10_expected_order_zero_jet (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    0 < zeroJetOrder ρ ∧ normalizedZeroMeasureJet ρ 0 = zeroMeasure ρ ∧
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ 0).integral φ = zeroFamilyFunctional ρ φ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (zeroMeasure ρ).integral ((𝓕 φ : 𝓢(ℝ, ℂ)) : ℝ → ℂ) = (zeroMeasure ρ).integral φ) := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have h0m : 0 < zeroJetOrder ρ := Nat.lt_of_lt_of_le zero_lt_one (one_le_zeroJetOrder hz hρ1)
  obtain ⟨-, -, ⟨hc, -⟩, hpl, -, -, hz0, -, -, -, -, hF, -⟩ := copoisson_zero_jets_measures ρ hz h0 h1 0 h0m
  have hν := hz0 rfl
  refine ⟨h0m, hν, fun φ => ?_, fun φ => ?_⟩
  · rw [hpl φ, iteratedDeriv_zero, hc]; simp
  · rw [← hν]; exact hF φ

/-- The k = 0 forced chain is exactly the Stage 11 forced Euler identity of `ForcedEuler`. -/
theorem FullAudit10_expected_chain_is_forced_euler (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    {ψ : ℝ → ℂ} (hψ : PositiveAxisTest ψ) :
    eulerImage ρ ψ = spectralKappa ρ * ((∫ x in Ioi 0, (zeroProfile ρ x - 1) * ψ x) +
      ∑' n : ℕ, ψ (n + 1)) := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hh := zero_ne_half hz
  have hm : 0 < zeroJetOrder ρ := Nat.lt_of_lt_of_le zero_lt_one (one_le_zeroJetOrder hz hρ1)
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, hchain, -⟩ := copoisson_zero_jets_measures ρ hz h0 h1 0 hm
  have hc := hchain ψ hψ
  simp only [if_true] at hc
  have hp : ∀ x, zeroJetProfile (spectralKappa ρ) 0 x = zeroProfile ρ x := zeroJetProfile_zero ρ hρ0 hρ1 hh
  simp only [hp] at hc
  have hψc : Continuous ψ := hψ.1.continuous
  have hI : Integrable (fun x => zeroProfile ρ x * ψ x) (volume.restrict (Ioi 0)) :=
    (((continuous_zeroProfile ρ).mul hψc).integrable_of_hasCompactSupport hψ.2.1.mul_left).restrict
  have hW : Integrable ψ (volume.restrict (Ioi 0)) := (hψc.integrable_of_hasCompactSupport hψ.2.1).restrict
  have hsplit : (∫ x in Ioi 0, (zeroProfile ρ x - 1) * ψ x) =
      (∫ x in Ioi 0, zeroProfile ρ x * ψ x) - ∫ x in Ioi 0, ψ x := by
    rw [← integral_sub hI hW]; congr 1; funext x; ring
  rw [eulerImage, hsplit]
  linear_combination hc

/-- At a zero of multiplicity at least two the first jet is a pure density measure. -/
theorem FullAudit10_expected_first_jet (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hm : 2 ≤ zeroJetOrder ρ) :
    (∀ φ : 𝓢(ℝ, ℂ), (normalizedZeroMeasureJet ρ 1).integral φ =
      ∫ x, zeroJetDensity (spectralKappa ρ) 1 x * φ x) ∧
    (normalizedZeroMeasureJet ρ 1).variationControl (Ioo (-1) 1) = 0 ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 1 ≤ |y| →
      ‖zeroJetDensity (spectralKappa ρ) 1 y + (bernoulliTwo |y| : ℂ) / (2 * ((|y| : ℝ) : ℂ) ^ 2)‖ ≤
        C * |y| ^ (-3 : ℝ)) ∧
    (∀ ψ : ℝ → ℂ, PositiveAxisTest ψ →
      -(∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) 1 x *
          deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv ψ y) x) -
        spectralKappa ρ * (∫ x in Ioi 0, zeroJetProfile (spectralKappa ρ) 1 x * ψ x) =
      (∫ x in Ioi 0, zeroProfile ρ x * ψ x) + ((∑' n : ℕ, ψ (n + 1)) - ∫ x in Ioi 0, ψ x)) := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  have hh := zero_ne_half hz
  obtain ⟨-, -, -, -, hint, -, -, hgap, -, -, ⟨C, hC, htail⟩, -, -, -, hchain, -⟩ :=
    copoisson_zero_jets_measures ρ hz h0 h1 1 (by omega)
  refine ⟨fun φ => by rw [hint φ]; simp, hgap, ⟨C, hC, fun y hy => ?_⟩, fun ψ hψ => ?_⟩
  · have := htail y hy
    simp only [one_ne_zero, if_false, if_true, zero_add, one_mul, zero_sub] at this
    simpa [sub_neg_eq_add] using this
  · have hc := hchain ψ hψ
    simp only [one_ne_zero, if_false, if_true] at hc
    rw [hc]
    congr 2
    funext x
    rw [zeroJetProfile_zero ρ hρ0 hρ1 hh]

/-- The reflected zero gives the same node κ₀ and the same jets: it is not a separate node. -/
theorem FullAudit10_expected_reflection_not_new_node (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (k : ℕ) (hk : k < zeroJetOrder ρ) :
    riemannZeta (1 - ρ) = 0 ∧ spectralKappa (1 - ρ) = spectralKappa ρ ∧
      zeroJetOrder (1 - ρ) = zeroJetOrder ρ ∧ normalizedZeroMeasureJet (1 - ρ) k = normalizedZeroMeasureJet ρ k := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hm, hκ, hν, -, -⟩, -⟩ :=
    copoisson_zero_jets_measures ρ hz h0 h1 k hk
  refine ⟨?_, hκ, hm, hν⟩
  rw [zetaFunctionalFactor_eq h0 hρ1, hz, mul_zero]

/-- On real tests the jets at the conjugate zero are the conjugate pairings. -/
theorem FullAudit10_expected_conj_real_test (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (k : ℕ) (hk : k < zeroJetOrder ρ) (φ : 𝓢(ℝ, ℂ)) (hφ : complexSchwartzConj φ = φ) :
    riemannZeta (starRingEnd ℂ ρ) = 0 ∧ zeroJetOrder (starRingEnd ℂ ρ) = zeroJetOrder ρ ∧
      (normalizedZeroMeasureJet (starRingEnd ℂ ρ) k).integral φ =
        starRingEnd ℂ ((normalizedZeroMeasureJet ρ k).integral φ) := by
  obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, ⟨hm, hc⟩⟩ :=
    copoisson_zero_jets_measures ρ hz h0 h1 k hk
  refine ⟨by rw [_root_.riemannZeta_conj, hz, map_zero], hm, ?_⟩
  rw [hc φ, hφ]

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedCoPoissonOrderZero.lean; SHA256 68a01d31ef49ae9ac79dc06b1752577758413740cc4190fd4dca3763061c8453 -/
section

/- Independent consumers for the original R1-CP1 root
`Zeta23.OPICAFollowup.renormalized_copoisson_order_zero`.

Definition audits pin the cutoff density (CP1.5), the cutoff origin atom, the limit density
(CP1.4) and both measures to their explicit constructions. The root is restated in full.
Domain consumers check, on the open strip 0 < Re ρ < 1:
- the cutoff and limit origin atoms (1 - e^(-ρT))/ρ and 1/ρ on every compact window containing 0;
- that the limit density near the origin is ζ(ρ)|x|^(ρ-1) + 1/(1-ρ) (S_ρ vanishes on |x| < 1);
- convergence of the actual cutoff pairings to V_(ρ-1/2)(φ) for every Schwartz test;
- convergence of bounded measurable compact-window integrals under the parent
  `LocalVariationConvergence`;
- non-vacuity at ρ = 1/2. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit11_audit_cutoff_density (ρ : ℂ) (T x : ℝ) : coPoissonCutoffDensity ρ T x =
    ((|x| : ℝ) : ℂ) ^ (-ρ) *
        ∑ n ∈ Finset.Icc (max 1 ⌈|x| * Real.exp (-T)⌉₊) ⌊|x|⌋₊, (n : ℂ) ^ (ρ - 1) +
      ((|x| : ℝ) : ℂ) ^ (ρ - 1) * ∑ n ∈ Finset.Ioc ⌊|x|⌋₊ ⌊|x| * Real.exp T⌋₊, (n : ℂ) ^ (-ρ) -
      (cexp ((1 - ρ) * T) - 1) / (1 - ρ) := rfl

theorem FullAudit11_audit_cutoff_atom (ρ : ℂ) (T : ℝ) :
    coPoissonCutoffAtom ρ T = (1 - cexp (-ρ * T)) / ρ := rfl

theorem FullAudit11_audit_limit_density (ρ : ℂ) (x : ℝ) : coPoissonLimitDensity ρ x =
    coPoissonPowerSums ρ |x| + riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) + 1 / (1 - ρ) := rfl

theorem FullAudit11_audit_cutoff_measure (ρ : ℂ) (T : ℝ) : coPoissonCutoff ρ T =
    densityAtomMeasure (coPoissonCutoffDensity ρ T) (coPoissonCutoffAtom ρ T)
      (locallyIntegrable_coPoissonCutoffDensity ρ T) := rfl

theorem FullAudit11_audit_limit_measure (ρ : ℂ) (h0 : 0 < ρ.re) : coPoissonLimitMeasure ρ h0 =
    densityAtomMeasure (coPoissonLimitDensity ρ) (1 / ρ)
      (locallyIntegrable_coPoissonLimitDensity h0) := rfl

/-! ### Restated root -/

theorem expected_renormalized_copoisson_order_zero (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (∀ T : ℝ, 0 ≤ T → ∀ φ : 𝓢(ℝ, ℂ), (coPoissonCutoff ρ T).integral φ =
      ∫ t in (0 : ℝ)..T, cexp (-(ρ - 1 / 2) * t) * renormalizedCombKernel t φ) ∧
    (∀ T : ℝ, 0 ≤ T → ∀ φ : 𝓢(ℝ, ℂ), (coPoissonCutoff ρ T).integral φ =
      (∫ x, coPoissonCutoffDensity ρ T x * φ x) + (1 - cexp (-ρ * T)) / ρ * φ 0) ∧
    (∀ (T : ℝ) (K : Set ℝ) (hK : IsCompact K) (E : Set ℝ), MeasurableSet E →
      (coPoissonCutoff ρ T).compactRestriction K hK E =
        (∫ x in E ∩ K, coPoissonCutoffDensity ρ T x) +
          (E ∩ K).indicator (fun _ => (1 - cexp (-ρ * T)) / ρ) 0) ∧
    (∀ (K : Set ℝ) (hK : IsCompact K) (E : Set ℝ), MeasurableSet E →
      (coPoissonLimitMeasure ρ h0).compactRestriction K hK E =
        (∫ x in E ∩ K, (finiteSumSrho ρ |x| + riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) +
          1 / (1 - ρ))) + (E ∩ K).indicator (fun _ => 1 / ρ) 0) ∧
    (∀ (K : Set ℝ) (hK : IsCompact K), Tendsto (fun T : ℝ =>
      ((coPoissonCutoff ρ T).compactRestriction K hK -
        (coPoissonLimitMeasure ρ h0).compactRestriction K hK).variation.real univ) atTop (𝓝 0)) ∧
    LocalVariationConvergence (fun n : ℕ => coPoissonCutoff ρ n) (coPoissonLimitMeasure ρ h0) ∧
    (∀ φ : 𝓢(ℝ, ℂ), coPoissonFamily (ρ - 1 / 2) φ = (coPoissonLimitMeasure ρ h0).integral φ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), coPoissonFamily (ρ - 1 / 2) φ =
      (∫ x, (finiteSumSrho ρ |x| + riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) + 1 / (1 - ρ)) * φ x) +
        1 / ρ * φ 0) :=
  renormalized_copoisson_order_zero ρ h0 h1

/-! ### Domain consumers -/

lemma FullAudit11_singleton_window (K : Set ℝ) (h0 : (0 : ℝ) ∈ K) :
    ({0} : Set ℝ) ∩ K = {0} := by
  ext x; simp only [mem_inter_iff, mem_singleton_iff]
  constructor
  · exact fun h => h.1
  · rintro rfl; exact ⟨rfl, h0⟩

/-- The limit measure carries exactly the origin atom 1/ρ (the origin correction). -/
theorem FullAudit11_expected_limit_origin_atom (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (K : Set ℝ)
    (hK : IsCompact K) (hK0 : (0 : ℝ) ∈ K) :
    (coPoissonLimitMeasure ρ h0).compactRestriction K hK {0} = 1 / ρ := by
  rw [(renormalized_copoisson_order_zero ρ h0 h1).2.2.2.1 K hK {0} (measurableSet_singleton 0),
    FullAudit11_singleton_window K hK0, Set.indicator_of_mem (mem_singleton 0),
    setIntegral_measure_zero _ (measure_singleton 0), zero_add]

/-- The actual cutoff carries the origin atom (1 - e^(-ρT))/ρ = ∫_0^T e^(-ρt) dt. -/
theorem FullAudit11_expected_cutoff_origin_atom (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (T : ℝ)
    (K : Set ℝ) (hK : IsCompact K) (hK0 : (0 : ℝ) ∈ K) :
    (coPoissonCutoff ρ T).compactRestriction K hK {0} = (1 - cexp (-ρ * T)) / ρ := by
  rw [(renormalized_copoisson_order_zero ρ h0 h1).2.2.1 T K hK {0} (measurableSet_singleton 0),
    FullAudit11_singleton_window K hK0, Set.indicator_of_mem (mem_singleton 0),
    setIntegral_measure_zero _ (measure_singleton 0), zero_add]

/-- S_ρ vanishes on |x| < 1, so the limit density there is ζ(ρ)|x|^(ρ-1) + 1/(1-ρ). -/
theorem FullAudit11_expected_limit_density_near_origin (ρ : ℂ) {x : ℝ} (hx : |x| < 1) :
    coPoissonLimitDensity ρ x = riemannZeta ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) + 1 / (1 - ρ) := by
  have hf : ⌊|x|⌋₊ = 0 := Nat.floor_eq_zero.mpr hx
  simp [coPoissonLimitDensity, finiteSumSrho, coPoissonPowerSums, hf]

/-- The actual cutoff pairings converge to the entire family on every Schwartz test. -/
theorem FullAudit11_expected_cutoff_pairing_tendsto (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun T : ℝ => (coPoissonCutoff ρ T).integral φ) atTop
      (𝓝 ((coPoissonLimitMeasure ρ h0).integral φ)) := by
  have hroot := renormalized_copoisson_order_zero ρ h0 h1
  rw [← hroot.2.2.2.2.2.2.1 φ, coPoissonFamily_apply]
  refine Tendsto.congr' ?_ (intervalIntegral_tendsto_integral_Ioi 0
    (renormalizedCombKernel_laplace_integrable _ φ) tendsto_id)
  filter_upwards [eventually_ge_atTop 0] with T hT
  exact (hroot.1 T hT φ).symm

/-- Compact-window integrals of bounded measurable tests converge (parent notion). -/
theorem FullAudit11_expected_local_test_convergence (ρ : ℂ) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (K : Set ℝ) (hK : IsCompact K) (f : ℝ → ℂ) (hf : StronglyMeasurable f) (C : ℝ)
    (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    Tendsto (fun n : ℕ => finiteComplexIntegral ((coPoissonCutoff ρ n).compactRestriction K hK) f)
      atTop (𝓝 (finiteComplexIntegral ((coPoissonLimitMeasure ρ h0).compactRestriction K hK) f)) :=
  ((renormalized_copoisson_order_zero ρ h0 h1).2.2.2.2.2.1).tendsto_local_test K hK f hf C hC
    hbound

/-- Non-vacuity: the critical point ρ = 1/2 lies in the domain. -/
theorem FullAudit11_expected_nonvacuous_half (φ : 𝓢(ℝ, ℂ)) :
    coPoissonFamily ((1 / 2 : ℂ) - 1 / 2) φ =
      (∫ x, (finiteSumSrho (1 / 2) |x| + riemannZeta (1 / 2) * ((|x| : ℝ) : ℂ) ^ ((1 / 2 : ℂ) - 1) +
        1 / (1 - 1 / 2)) * φ x) + 1 / (1 / 2) * φ 0 :=
  (renormalized_copoisson_order_zero (1 / 2) (by norm_num) (by norm_num)).2.2.2.2.2.2.2 φ

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedEulerMaclaurin.lean; SHA256 2a6736080dec794de13cdcaeb249aeb81264876f26d0c95940918ea522f96ff4 -/
section

/- Independent consumers for the original root
`Zeta23.OPICAFollowup.finite_sum_euler_maclaurin_uniform` (R2-S1a, R2-H1, F3; display S1.3).

Definition audits pin the periodic Bernoulli functions, the right-endpoint power sum and the
explicit remainder to their constructions. The root is restated in full. Domain consumers check:
- the paper's O-form for every fixed parameter in `0 < Re s`, `s ≠ 1`;
- that the finite sum is right-closed: crossing an integer `n` adds exactly `n^(-s)`;
- composition with the actual CP1 construction `finiteSumSrho` at `s = ρ` and `s = 1 - ρ`:
  the two `B₁/x` terms cancel and the exact S1a identity holds for every strip parameter;
- at an actual zero in the strip (with the functional equation for `ζ(1 - ρ) = 0`),
  `S_ρ(x) = b_ρ + (2ρ - 1) B₂({x}) / (2x²) + O(x^(-3))`, uniformly in real cutoffs `x ≥ 1`;
- the exact differentiated remainder is `O(x^(-Re s - 2))` inside every cell;
- non-vacuity at the critical point `s = 1/2` and the integer cutoff `x = 1`. -/
noncomputable section
open Set MeasureTheory Filter Complex Asymptotics
open scoped Topology
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit12_audit_bernoulliOneRight (x : ℝ) : bernoulliOneRight x = Int.fract x - 1 / 2 := rfl

theorem FullAudit12_audit_bernoulliTwo (x : ℝ) :
    bernoulliTwo x = Int.fract x ^ 2 - Int.fract x + 1 / 6 := rfl

theorem FullAudit12_audit_rightPowerSum (s : ℂ) (x : ℝ) :
    rightPowerSum s x = ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (n : ℂ) ^ (-s) := rfl

theorem FullAudit12_audit_remainder (s : ℂ) (x : ℝ) : eulerMaclaurinRemainder s x =
    -(s * (s + 1) / 6) * (bernoulliThree x : ℂ) * (x : ℂ) ^ (-s - 2) +
      s * (s + 1) * (s + 2) / 6 * ∫ t in Ioi x, (bernoulliThree t : ℂ) * (t : ℂ) ^ (-s - 3) := rfl

theorem FullAudit12_audit_bernoulliThree (x : ℝ) : bernoulliThree x =
    Int.fract x ^ 3 - 3 / 2 * Int.fract x ^ 2 + 1 / 2 * Int.fract x := rfl

/-! ### Restated root -/

theorem expected_finite_sum_euler_maclaurin_uniform :
    (∀ (s : ℂ) (n : ℕ) (y : ℝ), y ∈ Ico (n : ℝ) (n + 1) →
      rightPowerSum s y = ∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (-s)) ∧
    (∀ n : ℕ, bernoulliOneRight n = -1 / 2 ∧ bernoulliTwo n = 1 / 6) ∧
    (∀ s : ℂ, 0 < s.re → s ≠ 1 → ∀ x : ℝ, 1 ≤ x →
      rightPowerSum s x = riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
        (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
          s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2 + eulerMaclaurinRemainder s x) ∧
    (∀ s : ℂ, 0 < s.re → ∀ x : ℝ, 0 < x →
      ‖eulerMaclaurinRemainder s x‖ ≤
        (‖s‖ * (‖s‖ + 1) / 6 + ‖s‖ * (‖s‖ + 1) * (‖s‖ + 2) / 12) * x ^ (-s.re - 2)) ∧
    (∀ K : Set ℂ, IsCompact K → K ⊆ {s : ℂ | 0 < s.re ∧ s ≠ 1} → ∃ C : ℝ, 0 ≤ C ∧
      ∀ s ∈ K, ∀ x : ℝ, 1 ≤ x →
        ‖rightPowerSum s x - (riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
          (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
            s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2)‖ ≤ C * x ^ (-s.re - 2)) ∧
    (∀ x : ℝ, 1 ≤ x →
      DifferentiableOn ℂ (fun s => eulerMaclaurinRemainder s x) {s : ℂ | 0 < s.re ∧ s ≠ 1}) ∧
    (∀ (s : ℂ) (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) → HasDerivAt (rightPowerSum s) 0 x) ∧
    (∀ s : ℂ, 0 < s.re → ∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) →
      HasDerivAt (eulerMaclaurinRemainder s)
        (-(s * (s + 1) / 2) * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 2)) x) :=
  finite_sum_euler_maclaurin_uniform

/-! ### Domain consumers -/

/-- The paper's O-form (S1.3) for every fixed parameter of the domain. -/
theorem FullAudit12_expected_isBigO {s : ℂ} (h0 : 0 < s.re) (h1 : s ≠ 1) :
    (fun x : ℝ => rightPowerSum s x - (riemannZeta s + (x : ℂ) ^ (1 - s) / (1 - s) -
      (bernoulliOneRight x : ℂ) * (x : ℂ) ^ (-s) -
        s * (bernoulliTwo x : ℂ) * (x : ℂ) ^ (-s - 1) / 2)) =O[atTop]
      (fun x : ℝ => x ^ (-s.re - 2)) := by
  obtain ⟨C, -, hC⟩ := finite_sum_euler_maclaurin_uniform.2.2.2.2.1 {s} isCompact_singleton
    (by simpa using ⟨h0, h1⟩)
  refine IsBigO.of_bound C ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)]
  exact hC s rfl x hx

/-- Right-closed convention: crossing the integer `n ≥ 1` adds exactly the endpoint term. -/
theorem FullAudit12_expected_right_endpoint_jump (s : ℂ) {n : ℕ} (hn : 1 ≤ n) :
    rightPowerSum s n = rightPowerSum s ((n : ℝ) - 1 / 2) + (n : ℂ) ^ (-s) := by
  have hroot := finite_sum_euler_maclaurin_uniform.1
  have h1 := hroot s n n ⟨le_rfl, by linarith⟩
  have h2 := hroot s (n - 1) ((n : ℝ) - 1 / 2) (by
    constructor <;> push_cast [Nat.cast_sub hn] <;> linarith)
  rw [h1, h2]
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Finset.sum_Icc_succ_top (by omega)]

lemma FullAudit12_cpow_sub_one {x : ℝ} (hx : 0 < x) (a : ℂ) : (x : ℂ) ^ (a - 1) = (x : ℂ) ^ a / x := by
  rw [Complex.cpow_sub _ _ (Complex.ofReal_ne_zero.mpr hx.ne'), Complex.cpow_one]

/-- Composition with the actual CP1 construction: at `s = ρ` and `s = 1 - ρ` the `B₁/x` terms
cancel and the exact S1a identity holds for every strip parameter and real cutoff `x ≥ 1`. -/
theorem FullAudit12_expected_srho_expansion {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {x : ℝ} (hx : 1 ≤ x) :
    finiteSumSrho ρ x = riemannZeta (1 - ρ) * (x : ℂ) ^ (-ρ) - riemannZeta ρ * (x : ℂ) ^ (ρ - 1) +
      (1 / ρ - 1 / (1 - ρ)) + (2 * ρ - 1) * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2) +
        ((x : ℂ) ^ (-ρ) * eulerMaclaurinRemainder (1 - ρ) x -
          (x : ℂ) ^ (ρ - 1) * eulerMaclaurinRemainder ρ x) := by
  have hx0 : 0 < x := by linarith
  have hxne : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hσ0 : 0 < (1 - ρ).re := by simp; linarith
  have hσ1 : 1 - ρ ≠ 1 := fun h => hρ0 (by linear_combination -h)
  have hroot := finite_sum_euler_maclaurin_uniform.2.2.1
  have eA := hroot (1 - ρ) hσ0 hσ1 x hx
  have eB := hroot ρ h0 hρ1 x hx
  have hS : finiteSumSrho ρ x = (x : ℂ) ^ (-ρ) * rightPowerSum (1 - ρ) x -
      (x : ℂ) ^ (ρ - 1) * rightPowerSum ρ x := by
    simp only [finiteSumSrho, coPoissonPowerSums, rightPowerSum, neg_sub]
  have hv : (x : ℂ) ^ ρ ≠ 0 := (Complex.cpow_ne_zero_iff_of_exponent_ne_zero hρ0).mpr hxne
  have hneg : (x : ℂ) ^ (-ρ) = ((x : ℂ) ^ ρ)⁻¹ := Complex.cpow_neg _ _
  have p1 : (x : ℂ) ^ (1 - (1 - ρ)) = (x : ℂ) ^ ρ := by ring_nf
  have p2 : (x : ℂ) ^ (-(1 - ρ)) = (x : ℂ) ^ ρ / x := by
    rw [show -(1 - ρ) = ρ - 1 by ring, FullAudit12_cpow_sub_one hx0]
  have p3 : (x : ℂ) ^ (-(1 - ρ) - 1) = (x : ℂ) ^ ρ / x / x := by
    rw [FullAudit12_cpow_sub_one hx0, p2]
  have p4 : (x : ℂ) ^ (1 - ρ) = x * ((x : ℂ) ^ ρ)⁻¹ := by
    rw [Complex.cpow_sub _ _ hxne, Complex.cpow_one, div_eq_mul_inv]
  have p5 : (x : ℂ) ^ (-ρ - 1) = ((x : ℂ) ^ ρ)⁻¹ / x := by rw [FullAudit12_cpow_sub_one hx0, hneg]
  have p6 : (x : ℂ) ^ (ρ - 1) = (x : ℂ) ^ ρ / x := FullAudit12_cpow_sub_one hx0 ρ
  have hs1 : (1 : ℂ) - (1 - ρ) = ρ := by ring
  have hs2 : (1 : ℂ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  rw [hS, eA, eB, p1, p2, p3, p4, p5, p6, hneg, hs1]
  field_simp
  ring

/-- At an actual zero in the strip, `S_ρ(x) = b_ρ + (2ρ - 1) B₂({x}) / (2x²) + O(x^(-3))`
uniformly in real cutoffs `x ≥ 1` (paper, proof of S1.1). -/
theorem FullAudit12_expected_srho_tail_at_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      ‖finiteSumSrho ρ x - (1 / ρ - 1 / (1 - ρ)) -
        (2 * ρ - 1) * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2)‖ ≤ C * x ^ (-3 : ℝ) := by
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  have hz' : riemannZeta (1 - ρ) = 0 := by
    have hn : ∀ n : ℕ, ρ ≠ -n := fun n h => by
      have := congrArg Complex.re h; simp at this; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [riemannZeta_one_sub hn hρ1, hz, mul_zero]
  set A := ‖1 - ρ‖ * (‖1 - ρ‖ + 1) / 6 + ‖1 - ρ‖ * (‖1 - ρ‖ + 1) * (‖1 - ρ‖ + 2) / 12
  set B := ‖ρ‖ * (‖ρ‖ + 1) / 6 + ‖ρ‖ * (‖ρ‖ + 1) * (‖ρ‖ + 2) / 12
  refine ⟨A + B, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hroot := finite_sum_euler_maclaurin_uniform.2.2.2.1
  have hσ0 : 0 < (1 - ρ).re := by simp; linarith
  rw [FullAudit12_expected_srho_expansion h0 h1 hx, hz, hz']
  have hcancel : (0 : ℂ) * (x : ℂ) ^ (-ρ) - 0 * (x : ℂ) ^ (ρ - 1) + (1 / ρ - 1 / (1 - ρ)) +
      (2 * ρ - 1) * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2) +
        ((x : ℂ) ^ (-ρ) * eulerMaclaurinRemainder (1 - ρ) x -
          (x : ℂ) ^ (ρ - 1) * eulerMaclaurinRemainder ρ x) - (1 / ρ - 1 / (1 - ρ)) -
        (2 * ρ - 1) * (bernoulliTwo x : ℂ) / (2 * (x : ℂ) ^ 2) =
      (x : ℂ) ^ (-ρ) * eulerMaclaurinRemainder (1 - ρ) x -
        (x : ℂ) ^ (ρ - 1) * eulerMaclaurinRemainder ρ x := by ring
  rw [hcancel]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  have hA := hroot (1 - ρ) hσ0 x hx0
  have hB := hroot ρ h0 x hx0
  have e1 : x ^ (-ρ).re * x ^ (-(1 - ρ).re - 2) = x ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hx0]; congr 1; simp; ring
  have e2 : x ^ (ρ - 1).re * x ^ (-ρ.re - 2) = x ^ (-3 : ℝ) := by
    rw [← Real.rpow_add hx0]; congr 1; simp; ring
  have hp1 : 0 ≤ x ^ (-ρ).re := Real.rpow_nonneg hx0.le _
  have hp2 : 0 ≤ x ^ (ρ - 1).re := Real.rpow_nonneg hx0.le _
  calc x ^ (-ρ).re * ‖eulerMaclaurinRemainder (1 - ρ) x‖ +
        x ^ (ρ - 1).re * ‖eulerMaclaurinRemainder ρ x‖
      ≤ x ^ (-ρ).re * (A * x ^ (-(1 - ρ).re - 2)) + x ^ (ρ - 1).re * (B * x ^ (-ρ.re - 2)) := by
        gcongr
    _ = (A + B) * x ^ (-3 : ℝ) := by
        rw [mul_left_comm, e1, mul_left_comm, e2]; ring

/-- The exact differentiated remainder is `O(x^(-Re s - 2))` inside every cell. -/
theorem FullAudit12_expected_remainder_derivative_bound {s : ℂ} (h0 : 0 < s.re) {n : ℕ} {x : ℝ}
    (hx : x ∈ Ioo (n : ℝ) (n + 1)) :
    ‖deriv (eulerMaclaurinRemainder s) x‖ ≤ ‖s‖ * (‖s‖ + 1) / 2 * x ^ (-s.re - 2) := by
  have hx0 : 0 < x := lt_of_le_of_lt (Nat.cast_nonneg n) hx.1
  rw [(finite_sum_euler_maclaurin_uniform.2.2.2.2.2.2.2 s h0 n x hx).deriv, norm_mul, norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, Complex.norm_real, Real.norm_eq_abs, norm_neg,
    norm_div, norm_mul]
  have hB2 : |bernoulliTwo x| ≤ 1 := by
    unfold bernoulliTwo
    have h0' := Int.fract_nonneg x
    have h1' := Int.fract_lt_one x
    rw [abs_le]; constructor <;> nlinarith
  have hre : (-s - 2).re = -s.re - 2 := by simp
  rw [hre]
  have hn1 : ‖s + 1‖ ≤ ‖s‖ + 1 := (norm_add_le _ _).trans (by simp)
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2]
  have hp : 0 ≤ x ^ (-s.re - 2) := Real.rpow_nonneg hx0.le _
  calc ‖s‖ * ‖s + 1‖ / 2 * |bernoulliTwo x| * x ^ (-s.re - 2)
      ≤ ‖s‖ * (‖s‖ + 1) / 2 * 1 * x ^ (-s.re - 2) := by gcongr
    _ = ‖s‖ * (‖s‖ + 1) / 2 * x ^ (-s.re - 2) := by ring

/-- Non-vacuity at the critical point `s = 1/2` and the integer cutoff `x = 1`:
`1 = ζ(1/2) + 2 + 1/2 - 1/24 + R(1/2, 1)`. -/
theorem FullAudit12_expected_nonvacuous_half :
    (1 : ℂ) = riemannZeta (1 / 2) + 2 + 1 / 2 - 1 / 24 + eulerMaclaurinRemainder (1 / 2) 1 := by
  have h := finite_sum_euler_maclaurin_uniform.2.2.1 (1 / 2) (by norm_num) (by norm_num) 1 le_rfl
  have hint := finite_sum_euler_maclaurin_uniform.2.1 1
  have hsum : rightPowerSum (1 / 2) 1 = 1 := by simp [rightPowerSum]
  rw [hsum] at h
  simp only [Nat.cast_one] at hint
  rw [hint.1, hint.2] at h
  simp only [Complex.ofReal_one, Complex.one_cpow] at h
  push_cast at h
  linear_combination h

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedFirstCell.lean; SHA256 a3a18d428b3d35ef2b14f1dce9839e0e70e86a98eb6e7345db062f7cd47d4d4a -/
section

/- Independent full-domain consumers for the two original first-cell roots.
These statements concern the literal finite-power-sum density. They do not
assert existence, selfduality or growth of the global co-Poisson measure. -/
noncomputable section
open Set MeasureTheory Complex
open Zeta23 Zeta23.OPICA Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem expected_zero_measure_first_cell_sign (delta gamma : ℝ)
    (hheight : 3*Real.pi/(2*Real.log 2) < |gamma|) :
    (let u := 3*Real.pi/(2*|gamma|)
     0<u ∧ u<Real.log 2 ∧
     coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)=
       -|gamma| *(1+1/(4*(delta^2+gamma^2)))*Real.exp (-u/2)*Real.cosh (delta*u) ∧
     coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)<0) ∧
    (delta≠0 → 2*Real.pi/Real.log 2 < |gamma| → ∀ z : ℂ, z≠0 →
      ∃ x y : ℝ, x∈Ioo (1:ℝ) 2 ∧ y∈Ioo (1:ℝ) 2 ∧
        0<(z*coPoissonComplexDensity (coPoissonRho delta gamma) x).re ∧
        (z*coPoissonComplexDensity (coPoissonRho delta gamma) y).re<0) :=
  zero_measure_first_cell_sign delta gamma hheight

theorem expected_first_cell_negative_mass_cost (delta gamma : ℝ)
    (hd : |delta|<1/2) (hg : 16≤|gamma|) :
    (∀ u∈Icc (4*Real.pi/(3*|gamma|)) (5*Real.pi/(3*|gamma|)),
      coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)≤
        -|gamma| *Real.exp (-u/2)/2) ∧
    Real.pi/6≤
      ∫ x in Real.exp (4*Real.pi/(3*|gamma|))..Real.exp (5*Real.pi/(3*|gamma|)),
        max (-coPoissonRealDensity (coPoissonRho delta gamma) x) 0 ∧
    8*Real.pi/(27*gamma^2)≤
      ∫ x in Real.exp (4*Real.pi/(3*|gamma|))..Real.exp (5*Real.pi/(3*|gamma|)),
        sincSquared x*max (-coPoissonRealDensity (coPoissonRho delta gamma) x) 0 := by
  simpa only [firstCellLowerLog,firstCellUpperLog,firstCellNegativeMass,
    firstCellNegativeSincMass,firstCellNegativePart] using
    first_cell_negative_mass_cost delta gamma hd hg

theorem FullAudit13_expected_actual_zero_first_cell_cost (rho : ℂ)
    (hzero : IsNontrivialZero rho) (hg : 16≤|rho.im|) :
    (∀ u∈Icc (4*Real.pi/(3*|rho.im|)) (5*Real.pi/(3*|rho.im|)),
      coPoissonRealDensity rho (Real.exp u)≤-|rho.im| *Real.exp (-u/2)/2) ∧
    Real.pi/6≤
      ∫ x in Real.exp (4*Real.pi/(3*|rho.im|))..Real.exp (5*Real.pi/(3*|rho.im|)),
        max (-coPoissonRealDensity rho x) 0 ∧
    8*Real.pi/(27*rho.im^2)≤
      ∫ x in Real.exp (4*Real.pi/(3*|rho.im|))..Real.exp (5*Real.pi/(3*|rho.im|)),
        sincSquared x*max (-coPoissonRealDensity rho x) 0 := by
  have hd : |rho.re-1/2|<1/2 := abs_lt.mpr ⟨by linarith [hzero.2.1],by linarith [hzero.2.2]⟩
  have hrho : coPoissonRho (rho.re-1/2) rho.im=rho := by
    apply Complex.ext <;> simp [coPoissonRho]
  simpa only [hrho] using expected_first_cell_negative_mass_cost (rho.re-1/2) rho.im hd hg

theorem FullAudit13_expected_negative_ordinate_endpoint (delta : ℝ) (hd : |delta|<1/2) :
    Real.pi/6≤firstCellNegativeMass delta (-16) ∧
    8*Real.pi/(27*256)≤firstCellNegativeSincMass delta (-16) := by
  have h := first_cell_negative_mass_cost delta (-16) hd (by norm_num)
  norm_num only [neg_sq,show (16:ℝ)^2=256 by norm_num] at h
  simpa only [show (27:ℝ)*256=6912 by norm_num] using h.2

theorem FullAudit13_expected_positive_ordinate_endpoint (delta : ℝ) (hd : |delta|<1/2) :
    Real.pi/6≤firstCellNegativeMass delta 16 ∧
    8*Real.pi/(27*256)≤firstCellNegativeSincMass delta 16 := by
  have h := first_cell_negative_mass_cost delta 16 hd (by norm_num)
  norm_num only [show (16:ℝ)^2=256 by norm_num] at h
  simpa only [show (27:ℝ)*256=6912 by norm_num] using h.2

theorem FullAudit13_expected_online_cost_both_ordinates (gamma : ℝ) (hg : 16≤|gamma|) :
    Real.pi/6≤firstCellNegativeMass 0 gamma ∧
    8*Real.pi/(27*gamma^2)≤firstCellNegativeSincMass 0 gamma :=
  (first_cell_negative_mass_cost 0 gamma (by norm_num) hg).2

/-- This falsifies removal of the off-line condition from the phase clause:
on the critical line the imaginary scalar projection is identically zero
throughout the first open cell, even though the real density has a negative point. -/
theorem FullAudit13_expected_online_imaginary_projection_zero (gamma x : ℝ)
    (hg : gamma≠0) (hx : x∈Ioo (1:ℝ) 2) :
    (I*coPoissonComplexDensity (coPoissonRho 0 gamma) x).re=0 := by
  have hxpos : 0<x := zero_lt_one.trans hx.1
  have h := coPoisson_phase_formula 0 gamma (Real.log x) I hg
    (Real.log_pos hx.1) (Real.log_lt_log hxpos hx.2)
  have hQ := (coPoisson_quotient_re_im 0 gamma hg).1
  dsimp only at h
  simp only [Complex.ofReal_zero,zero_add] at h hQ
  have hAi : (I*((1/4-((gamma:ℂ)*I)^2)/((gamma:ℂ)*I))).im=0 := by
    simp only [Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_add]
    simpa only [zero_mul] using hQ
  rw [hAi] at h
  simpa only [Real.exp_log hxpos,zero_mul,Real.sinh_zero,mul_zero,sub_zero] using h

/-- Per-profile costs cannot be summed blindly over conjugate ordinates:
their real first-cell profiles agree, so opposite real coefficients cancel. -/
theorem FullAudit13_expected_conjugate_pair_first_cell_cancellation (delta gamma u : ℝ)
    (hg : gamma≠0) (hu : 0<u) (hu1 : u<Real.log 2) :
    coPoissonRealDensity (coPoissonRho delta gamma) (Real.exp u)-
      coPoissonRealDensity (coPoissonRho delta (-gamma)) (Real.exp u)=0 := by
  rw [coPoisson_first_cell_gamma_abs delta gamma u hg hu hu1,
    coPoisson_first_cell_gamma_abs delta (-gamma) u (neg_ne_zero.mpr hg) hu hu1,abs_neg]
  exact sub_self _

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedForcedEuler.lean; SHA256 230723787b3badebfa2862fc6168f6f7e76210fd9c00c009729d3f1906fdfca5 -/
section

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.zero_profile_forced_euler`
and `Zeta23.OPICAFollowup.zero_profile_not_homogeneous_operator_vector` (R2-S1b).

Definition audits pin the test class, the distributional Euler image -∫ h (x² φ')' and the
explicit derivative. Both roots are restated in full. Domain consumers check:
- the test class is non-degenerate (an independent smooth bump at 2 belongs to it);
- the atoms are seen by actual tests: on an independent bump at 1 the Euler image of the actual
  zero profile differs from its ordinary part κ ∫ (h - 1) φ by exactly κ ≠ 0;
- the jump clause agrees with the Stage 9 jump -κ/n² and its one-sided derivatives are unique;
- the explicit derivative is the right derivative on (0, ∞) and the a.e. derivative;
- at the non-zero parameter ρ = 3/4 the same forced Euler identity holds and its Euler image is
  not a function, so the construction-level statements are exercised. The zero-dependent roots
  need an actual zero, which Mathlib cannot exhibit. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology ContDiff
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit14_audit_positiveAxisTest (φ : ℝ → ℂ) :
    PositiveAxisTest φ ↔ ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Ioi 0 := Iff.rfl

theorem FullAudit14_audit_eulerImage (ρ : ℂ) (φ : ℝ → ℂ) : eulerImage ρ φ =
    -∫ x in Ioi 0, zeroProfile ρ x * deriv (fun y : ℝ => (y : ℂ) ^ 2 * deriv φ y) x := rfl

theorem FullAudit14_audit_zeroProfileDeriv (ρ : ℂ) (x : ℝ) :
    zeroProfileDeriv ρ x = -(srhoCellDeriv ρ ⌊x⌋₊ x / normalizationBrho ρ) := rfl

/-! ### Restated roots -/

theorem expected_zero_profile_forced_euler (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = spectralKappa ρ * ((∫ x in Ioi 0, (zeroProfile ρ x - 1) * φ x) +
        ∑' n : ℕ, φ (n + 1))) ∧
    (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      (∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * deriv (zeroProfile ρ) x * deriv φ x) = eulerImage ρ φ) ∧
    (∀ x : ℝ, 0 < x → x ∉ Set.range (fun n : ℕ => (n : ℝ)) →
      HasDerivAt (fun y : ℝ => (y : ℂ) ^ 2 * deriv (zeroProfile ρ) y)
        (spectralKappa ρ * (1 - zeroProfile ρ x)) x) ∧
    (∀ n : ℕ, 1 ≤ n → ContinuousAt (zeroProfile ρ) n ∧
      ∃ dR dL : ℂ, HasDerivWithinAt (zeroProfile ρ) dR (Ici (n : ℝ)) n ∧
        HasDerivWithinAt (zeroProfile ρ) dL (Iic (n : ℝ)) n ∧
        (n : ℂ) ^ 2 * (dR - dL) = -spectralKappa ρ) :=
  zero_profile_forced_euler ρ hz h0 h1

theorem expected_zero_profile_not_homogeneous_operator_vector (ρ : ℂ) (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    spectralKappa ρ ≠ 0 ∧
    (¬ ∃ g : ℝ → ℂ, LocallyIntegrableOn g (Ioi 0) ∧
      ∀ φ : ℝ → ℂ, PositiveAxisTest φ → eulerImage ρ φ = ∫ x in Ioi 0, g x * φ x) ∧
    (¬ ∃ g : ℝ → ℂ, MemLp g 2 (volume.restrict (Ioi 0)) ∧
      ∀ φ : ℝ → ℂ, PositiveAxisTest φ → eulerImage ρ φ = ∫ x in Ioi 0, g x * φ x) ∧
    (∀ c : ℂ, ¬ ∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = c * ∫ x in Ioi 0, zeroProfile ρ x * φ x) ∧
    LogFormDomain (zeroProfile ρ) (zeroProfileDeriv ρ) ∧
    logForm (zeroProfileDeriv ρ) =
      (∫ t, ‖logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t‖ ^ 2) +
        1 / 4 * ∫ x in Ioi 0, ‖zeroProfile ρ x‖ ^ 2 :=
  zero_profile_not_homogeneous_operator_vector ρ hz h0 h1

/-! ### Domain consumers -/

/-- An independent bump of radius 1/2 at a point c ≥ 1. -/
def FullAudit14_bumpAt (c : ℝ) : ContDiffBump c := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

lemma FullAudit14_tsupport_bumpAt (c : ℝ) : tsupport (fun x => ((FullAudit14_bumpAt c x : ℝ) : ℂ)) ⊆ Icc (c - 1 / 2) (c + 1 / 2) := by
  refine (tsupport_comp_subset Complex.ofReal_zero (FullAudit14_bumpAt c)).trans ?_
  rw [(FullAudit14_bumpAt c).tsupport_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  change -(1 / 2 : ℝ) ≤ x - c ∧ x - c ≤ 1 / 2 at hx
  constructor <;> linarith [hx.1, hx.2]

theorem FullAudit14_expected_test_bump {c : ℝ} (hc : 1 ≤ c) : PositiveAxisTest (fun x => ((FullAudit14_bumpAt c x : ℝ) : ℂ)) :=
  ⟨Complex.ofRealCLM.contDiff.comp (FullAudit14_bumpAt c).contDiff,
    (FullAudit14_bumpAt c).hasCompactSupport.comp_left Complex.ofReal_zero,
    (FullAudit14_tsupport_bumpAt c).trans fun x hx => by simp only [mem_Ioi]; linarith [hx.1]⟩

/-- The test class is non-degenerate: the bump at 2 is a test with value 1 at 2. -/
theorem FullAudit14_expected_test_class_nondegenerate :
    PositiveAxisTest (fun x => ((FullAudit14_bumpAt 2 x : ℝ) : ℂ)) ∧ ((FullAudit14_bumpAt 2 2 : ℝ) : ℂ) = 1 := by
  refine ⟨FullAudit14_expected_test_bump (by norm_num), ?_⟩
  rw [(FullAudit14_bumpAt 2).one_of_mem_closedBall (Metric.mem_closedBall_self (FullAudit14_bumpAt _).rIn_pos.le), Complex.ofReal_one]

/-- The atoms are seen by actual tests: on the bump at 1 the Euler image of the actual zero
profile exceeds its ordinary part by exactly κ ≠ 0. -/
theorem FullAudit14_expected_atom_detected (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    eulerImage ρ (fun x => ((FullAudit14_bumpAt 1 x : ℝ) : ℂ)) -
        spectralKappa ρ * (∫ x in Ioi 0, (zeroProfile ρ x - 1) * ((FullAudit14_bumpAt 1 x : ℝ) : ℂ)) =
      spectralKappa ρ ∧ spectralKappa ρ ≠ 0 := by
  have hT := FullAudit14_expected_test_bump (le_refl (1 : ℝ))
  have hsum : ∑' n : ℕ, ((FullAudit14_bumpAt 1 ((n : ℝ) + 1) : ℝ) : ℂ) = 1 := by
    rw [tsum_eq_single 0 fun n hn => ?_]
    · simp [(FullAudit14_bumpAt 1).one_of_mem_closedBall (Metric.mem_closedBall_self (FullAudit14_bumpAt _).rIn_pos.le)]
    · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      refine image_eq_zero_of_notMem_tsupport (f := fun x => ((FullAudit14_bumpAt 1 x : ℝ) : ℂ)) fun h => ?_
      have := (FullAudit14_tsupport_bumpAt 1 h).2
      linarith
  refine ⟨?_, (zero_profile_not_homogeneous_operator_vector ρ hz h0 h1).1⟩
  rw [(zero_profile_forced_euler ρ hz h0 h1).1 _ hT, hsum]; ring

/-- The jump clause agrees with the Stage 9 jump -κ/n², and any one-sided derivatives satisfy
it (they are unique). -/
theorem FullAudit14_expected_jump_matches_stage9 (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (n : ℕ) (dR dL : ℂ)
    (hR : HasDerivWithinAt (zeroProfile ρ) dR (Ici ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ))
    (hL : HasDerivWithinAt (zeroProfile ρ) dL (Iic ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ)) :
    ((n + 1 : ℕ) : ℂ) ^ 2 * (dR - dL) = -spectralKappa ρ ∧
      dR - dL = -spectralKappa ρ / ((n + 1 : ℕ) : ℂ) ^ 2 := by
  obtain ⟨-, dR', dL', hR', hL', hj⟩ := (zero_profile_forced_euler ρ hz h0 h1).2.2.2 (n + 1) (by omega)
  have e1 : dR = dR' := (uniqueDiffWithinAt_Ici _).eq_deriv _ hR hR'
  have e2 : dL = dL' := (uniqueDiffWithinAt_Iic _).eq_deriv _ hL hL'
  obtain ⟨dR9, dL9, hR9, hL9, hj9⟩ := (zero_profile_tail_and_jumps ρ hz h0 h1).2.2.2.2.1 n
  have e3 : dR = dR9 := (uniqueDiffWithinAt_Ici _).eq_deriv _ hR hR9
  have e4 : dL = dL9 := (uniqueDiffWithinAt_Iic _).eq_deriv _ hL hL9
  exact ⟨by rw [e1, e2]; exact hj, by rw [e3, e4]; exact hj9⟩

/-- The explicit derivative is the right derivative on (0, ∞) and equals deriv h between
integers. -/
theorem FullAudit14_expected_explicit_derivative (ρ : ℂ) :
    (∀ x : ℝ, 0 < x → HasDerivWithinAt (zeroProfile ρ) (zeroProfileDeriv ρ x) (Ioi x) x) ∧
    (∀ x : ℝ, 0 < x → x ∉ Set.range (fun n : ℕ => (n : ℝ)) →
      deriv (zeroProfile ρ) x = zeroProfileDeriv ρ x) :=
  ⟨fun _ hx => hasDerivWithinAt_zeroProfile_Ioi ρ hx, fun _ hx hn => deriv_zeroProfile_eq hx hn⟩

/-- Construction level at the non-zero parameter ρ = 3/4: the forced Euler identity holds and
its Euler image is not given by any function integrable on [1/2, 3/2]. -/
theorem FullAudit14_expected_construction_nonvacuous :
    spectralKappa (3 / 4) = 3 / 16 ∧
    (∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage (3 / 4) φ = spectralKappa (3 / 4) *
        ((∫ x in Ioi 0, (zeroProfile (3 / 4) x - 1) * φ x) + ∑' n : ℕ, φ (n + 1))) ∧
    (¬ ∃ g : ℝ → ℂ, IntegrableOn g (Icc (1 / 2) (3 / 2)) ∧
      ∀ φ : ℝ → ℂ, PositiveAxisTest φ → eulerImage (3 / 4) φ = ∫ x in Ioi 0, g x * φ x) := by
  have h0 : (0 : ℝ) < (3 / 4 : ℂ).re := by norm_num
  have h1 : (3 / 4 : ℂ).re < 1 := by norm_num
  have hh : (3 / 4 : ℂ) ≠ 1 / 2 := by norm_num
  have hk : spectralKappa (3 / 4) = 3 / 16 := by unfold spectralKappa; norm_num
  refine ⟨hk, fun φ hφ => (forced_euler_identity h0 h1 hh hφ).1, fun ⟨g, hg, hrep⟩ =>
    eulerImage_not_function h0 h1 hh (by rw [hk]; norm_num) hg hrep⟩

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedForceSampling.lean; SHA256 6fc99bc203b2c9ac3815df43f588cce2da746a1051ecc0ae20f84e4354255904 -/
section

/- Independent full-type and physical-definition consumer for the original F1-F3 root.
All hypotheses concern the actual zeta function and the full strip. No off-line zero
is asserted to exist. Definition audits prevent synthetic source/measure substitution.
The original word/jet consumer is separately replayed by ExpectedWordJet. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit15_audit_spectralKappa (ρ : ℂ) : spectralKappa ρ = ρ * (1 - ρ) := rfl

theorem FullAudit15_audit_logFourier (f : ℝ → ℂ) (ξ : ℝ) :
    logFourier f ξ = ∫ t, cexp (-((ξ * t : ℝ) : ℂ) * I) * f t := rfl

theorem FullAudit15_audit_force : nativeLogForce =
    -(TemperedDistribution.derivCLM ℂ sawtoothWeightTD) - (1 / 2 : ℂ) • sawtoothWeightTD := rfl

theorem FullAudit15_audit_density : arithmeticSpectralMeasure =
    volume.withDensity (fun ξ : ℝ => ENNReal.ofReal
      (‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (2 * π))) := rfl

theorem FullAudit15_audit_sample (ρ : ℂ) :
    profileSampleDefect ρ = (∑' n : ℕ, zeroProfile ρ (n + 1)) - 1 / 2 := rfl

theorem FullAudit15_audit_boundary (ρ : ℂ) :
    boundaryAmplitude ρ = riemannZeta ρ / normalizationBrho ρ := rfl

theorem FullAudit15_audit_generic (ρ : ℂ) (x : ℝ) :
    genericForcedProfile ρ x =
      (1 - finiteSumSrho ρ |x| / normalizationBrho ρ) -
        riemannZeta ρ / normalizationBrho ρ * ((|x| : ℝ) : ℂ) ^ (ρ - 1) := rfl

theorem expected_actual_force_sampling_consumer {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : (spectralKappa ρ).im ≠ 0) :
    (∀ (f : ℝ → ℂ) (ξ : ℝ), logFourier f ξ = 𝓕 f (ξ / (2 * π))) ∧
    (∀ (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      nativeLogForce (hc.toSchwartzMap hφ) =
        ∑' n : ℕ, ((((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * φ (Real.log (n + 1)) -
          ∫ t, (Real.exp (t / 2) : ℂ) * φ t) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (𝓕 nativeLogForce) φ = ∫ η : ℝ, riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) * φ η) ∧
    (∀ ξ : ℝ, -(1 / 2 + ξ * I) * logFourier sawtoothWeight ξ = riemannZeta (1 / 2 + ξ * I)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv φ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (zeroProfile ρ) t * φ t =
        spectralKappa ρ * nativeLogForce φ) ∧
    (∀ ξ : ℝ, logFourier (logUnitary (zeroProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ)) ∧
    (∀ η : ℝ, 𝓕 (logUnitary (zeroProfile ρ)) η =
      spectralKappa ρ * riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) /
        ((spectralEnergy (2 * π * η) : ℂ) - spectralKappa ρ)) ∧
    arithmeticSpectralMeasure =
      volume.withDensity (fun ξ : ℝ => ENNReal.ofReal (‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (2 * π))) ∧
    profileSampleDefect ρ = spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ) ∧
    (∃ ρ' : ℂ, (ρ' = ρ ∨ ρ' = 1 - ρ) ∧ 1 / 2 < ρ'.re ∧ ρ'.re < 1 ∧ riemannZeta ρ' = 0 ∧
      spectralKappa ρ' = spectralKappa ρ ∧ boundaryAmplitude ρ' = 0 ∧
      genericForcedProfile ρ' = zeroProfile ρ' ∧
      logUnitary (genericForcedProfile ρ') = logUnitary (zeroProfile ρ)) ∧
    (∀ c : ℂ, ¬ ∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = c * ∫ x in Ioi 0, zeroProfile ρ x * φ x) :=
  actual_force_sampling_consumer hz h0 h1 hκ

/-- Every hypothetical off-line strip zero lies in the actual theorem domain. -/
theorem FullAudit15_offline_kappa {ρ : ℂ} (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    (spectralKappa ρ).im ≠ 0 := by
  have h : (spectralKappa ρ).im = (1 - 2 * ρ.re) * ρ.im := by
    simp only [spectralKappa, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.one_re, Complex.one_im]
    ring
  rw [h]
  exact mul_ne_zero (by intro he; apply hre; linarith) him

/-- The sample identity and the actual nonhomogeneous Euler obstruction coexist.
This exercises the full root at an actual source with no extra spectral packet. -/
theorem FullAudit15_actual_offline_domain {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    profileSampleDefect ρ = spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ) ∧
    (∀ c : ℂ, ¬ ∀ φ : ℝ → ℂ, PositiveAxisTest φ →
      eulerImage ρ φ = c * ∫ x in Ioi 0, zeroProfile ρ x * φ x) := by
  obtain ⟨_, _, _, _, _, _, _, _, hs, _, hn⟩ :=
    expected_actual_force_sampling_consumer hz h0 h1 (FullAudit15_offline_kappa hre him)
  exact ⟨hs, hn⟩

/-- Both sides of the critical line choose the same κ node, with the actual
right-half-strip representative and zero boundary amplitude. -/
theorem FullAudit15_actual_right_representative {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    ∃ σ : ℂ, (σ = ρ ∨ σ = 1 - ρ) ∧ 1 / 2 < σ.re ∧ σ.re < 1 ∧
      riemannZeta σ = 0 ∧ spectralKappa σ = spectralKappa ρ ∧ boundaryAmplitude σ = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨σ, ha, hb, hc, hd, he, hf, _, _⟩, _⟩ :=
    expected_actual_force_sampling_consumer hz h0 h1 (FullAudit15_offline_kappa hre him)
  exact ⟨σ, ha, hb, hc, hd, he, hf⟩

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedFullFiniteSpan.lean; SHA256 3c8b892698091f69c5987c1f3d2b2e7a0bd3f068610c5355a1fe61fbf5b7eba2 -/
section
noncomputable section
open Set MeasureTheory Complex
open Zeta23.OPICA Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan

namespace Zeta23.OPICAFollowup.Validation
theorem expected_finite_zero_span_positive_only_zero :
    (∀ data : List (ℂ × ℂ × ℕ),
      ∀ h : ∀ j ∈ data, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
        j.2.2 < zeroJetOrder j.2.1,
      (Zeta23.OPICAFollowup.zeroJetRealSpan data).negative integerLatticeᶜ = 0 →
        (Zeta23.OPICAFollowup.zeroJetRealSpan data).positive = 0 ∧
          (Zeta23.OPICAFollowup.zeroJetRealSpan data).negative = 0) ∧
    (∀ n : ℕ, ∀ basis : Fin n → List (ℂ × ℂ × ℕ),
      ∀ h : ∀ i, ∀ j ∈ basis i, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
        j.2.2 < zeroJetOrder j.2.1,
      LinearIndependent ℝ (fun i =>
        (Zeta23.OPICAFollowup.zeroJetRealSpan (basis i)).distributionOfLinearGrowth
          (zeroJetRealSpan_growth _ (h i))) →
      ∀ a : Fin n → ℝ,
      (Zeta23.OPICAFollowup.zeroJetRealSpan (realBasisCombinationData basis a)).negative
        integerLatticeᶜ = 0 → a = 0) :=
  Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero

end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedLogFourierSobolev.lean; SHA256 29b6f838afddbdbf369bcc209583031f6a3f1d5746783217707e5532efa36136 -/
section

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.log_unitary_form_identity`
and `Zeta23.OPICAFollowup.log_fourier_plancherel` (R2-S1b, F1, F2, F3).

Definition audits pin the log transform, the log unitary, the form and the form domain. Both
roots are restated in full. Domain consumers check:
- the two roots fit together: ψ' - ψ/2 = e^(3t/2) h'(e^t), and the H¹ shift norm of ψ = U h equals
  the log form of h;
- the actual form domain is nonempty and non-degenerate (h = e^(-x));
- the actual zero profile at an actual zero lies in the form domain with its explicit
  right derivative, so the paper's identity (S1.5) holds for it:
  ∫_0^∞ x²|h'|² = ∫ |ψ'|² + (1/4) ∫_0^∞ |h|². -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform Real
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit17_audit_logFourier (f : ℝ → ℂ) (ξ : ℝ) :
    logFourier f ξ = ∫ t, cexp (-((ξ * t : ℝ) : ℂ) * I) * f t := rfl

theorem FullAudit17_audit_logUnitary (h : ℝ → ℂ) (t : ℝ) :
    logUnitary h t = (Real.exp (t / 2) : ℂ) * h (Real.exp t) := rfl

theorem FullAudit17_audit_logForm (h' : ℝ → ℂ) : logForm h' = ∫ x in Ioi 0, x ^ 2 * ‖h' x‖ ^ 2 := rfl

theorem FullAudit17_audit_logFormDomain (h h' : ℝ → ℂ) : LogFormDomain h h' ↔
    ((∀ a b : ℝ, 0 < a → 0 < b → h b - h a = ∫ x in a..b, h' x) ∧
      (∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable h' volume a b) ∧ Measurable h' ∧
      MemLp h 2 (volume.restrict (Ioi 0)) ∧
      MemLp (fun x : ℝ => (x : ℂ) * h' x) 2 (volume.restrict (Ioi 0))) :=
  ⟨fun hD => ⟨hD.1, hD.2, hD.3, hD.4, hD.5⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩⟩

/-! ### Restated roots -/

theorem expected_log_unitary_form_identity (h h' : ℝ → ℂ) (hD : LogFormDomain h h') :
    MemLp (logUnitary h) 2 ∧
    (∫ t, ‖logUnitary h t‖ ^ 2) = ∫ x in Ioi 0, ‖h x‖ ^ 2 ∧
    (∀ a b : ℝ, logUnitary h b - logUnitary h a = ∫ t in a..b, logUnitaryDeriv h h' t) ∧
    MemLp (logUnitaryDeriv h h') 2 ∧
    logForm h' = (∫ t, ‖logUnitaryDeriv h h' t‖ ^ 2) + 1 / 4 * ∫ x in Ioi 0, ‖h x‖ ^ 2 ∧
    LogH1 (logUnitary h) (logUnitaryDeriv h h') :=
  log_unitary_form_identity h h' hD

theorem expected_log_fourier_plancherel :
    (∀ (f : ℝ → ℂ) (ξ : ℝ), logFourier f ξ = ∫ t, cexp (-((ξ * t : ℝ) : ℂ) * I) * f t) ∧
    (∀ (f : ℝ → ℂ) (ξ : ℝ), logFourier f ξ = 𝓕 f (ξ / (2 * π))) ∧
    (∀ f : ℝ → ℂ, Integrable f → MemLp f 2 →
      Integrable (fun ξ => ‖logFourier f ξ‖ ^ 2) ∧
        ∫ t, ‖f t‖ ^ 2 = 1 / (2 * π) * ∫ ξ, ‖logFourier f ξ‖ ^ 2) ∧
    (∀ f : ℝ → ℂ, Integrable f → Differentiable ℝ f → Integrable (deriv f) →
      ∀ ξ : ℝ, logFourier (deriv f) ξ = (ξ : ℂ) * I * logFourier f ξ) ∧
    (∀ f : ℝ → ℂ, Integrable f → MemLp f 2 → Differentiable ℝ f → Integrable (deriv f) →
      MemLp (deriv f) 2 →
        (∫ t, ‖deriv f t‖ ^ 2) + 1 / 4 * ∫ t, ‖f t‖ ^ 2 =
          1 / (2 * π) * ∫ ξ, (ξ ^ 2 + 1 / 4) * ‖logFourier f ξ‖ ^ 2) ∧
    (∀ φ φ' : ℝ → ℂ, LogH1 φ φ' →
      ∫ t, ‖φ' t - φ t / 2‖ ^ 2 = (∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ∧
    (∀ w φ φ' : ℝ → ℂ, MemLp w 2 → LogH1 φ φ' →
      ‖∫ t, w t * (φ' t - φ t / 2)‖ ≤
        (∫ t, ‖w t‖ ^ 2) ^ (1 / 2 : ℝ) * ((∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ)) :=
  log_fourier_plancherel

/-! ### Domain consumers -/

/-- ψ' - ψ/2 = e^(3t/2) h'(e^t) pointwise. -/
lemma FullAudit17_shift_eq (h h' : ℝ → ℂ) (t : ℝ) :
    logUnitaryDeriv h h' t - logUnitary h t / 2 =
      (Real.exp (t / 2) : ℂ) * ((Real.exp t : ℂ) * h' (Real.exp t)) := by
  simp only [logUnitaryDeriv, logUnitary]; ring

/-- The roots fit together: the H¹ shift norm of ψ = U h is the log form of h. -/
theorem FullAudit17_expected_shift_norm_eq_logForm (h h' : ℝ → ℂ) (hD : LogFormDomain h h') :
    ∫ t, ‖logUnitaryDeriv h h' t - logUnitary h t / 2‖ ^ 2 = logForm h' := by
  obtain ⟨-, hU, -, -, hF, hH1⟩ := log_unitary_form_identity h h' hD
  rw [(log_fourier_plancherel.2.2.2.2.2.1) _ _ hH1, hU, hF]

/-- The form domain is non-degenerate: h(x) = e^(-x), h' = -e^(-x). -/
theorem FullAudit17_expected_domain_nonempty :
    LogFormDomain (fun x => (Real.exp (-x) : ℂ)) (fun x => -(Real.exp (-x) : ℂ)) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => (Real.exp (-x) : ℂ)) (-(Real.exp (-x) : ℂ)) x := by
    intro x
    have h := ((hasDerivAt_neg x).exp).ofReal_comp
    simpa using h
  have hcont : Continuous (fun x : ℝ => -(Real.exp (-x) : ℂ)) := by fun_prop
  have hint : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa using exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1)
  refine ⟨fun a b _ _ => ?_, fun a b _ _ => hcont.intervalIntegrable a b, hcont.measurable, ?_, ?_⟩
  · rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x)
      (hcont.intervalIntegrable a b)]
  · refine (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr ?_
    refine hint.mono' (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall (fun x hx => ?_)))
    have hx0 : (0 : ℝ) < x := hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _), sq, ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith)
  · refine (memLp_two_iff_integrable_sq_norm (by fun_prop)).mpr ?_
    refine (hint.const_mul 2).mono' (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall (fun x hx => ?_)))
    have hx0 : (0 : ℝ) < x := hx
    have hq : x ^ 2 ≤ 2 * Real.exp x := by
      have := Real.pow_div_factorial_le_exp x hx0.le 2
      norm_num [Nat.factorial] at this; linarith
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, Complex.norm_real, norm_neg,
      Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hx0,
      abs_of_pos (Real.exp_pos _), mul_pow, sq (Real.exp (-x)), ← Real.exp_add]
    calc x ^ 2 * Real.exp (-x + -x) ≤ 2 * Real.exp x * Real.exp (-x + -x) :=
          mul_le_mul_of_nonneg_right hq (Real.exp_pos _).le
      _ = 2 * Real.exp (-x) := by rw [mul_assoc, ← Real.exp_add]; ring_nf

/-! ### The actual zero profile is in the form domain (paper S1.5) -/

/-- The explicit right derivative of the zero profile on (0, ∞). -/
def FullAudit17_zeroProfileRightDeriv (ρ : ℂ) (x : ℝ) : ℂ := -(srhoCellDeriv ρ ⌊x⌋₊ x / normalizationBrho ρ)

lemma FullAudit17_measurable_zeroProfileRightDeriv (ρ : ℂ) : Measurable (FullAudit17_zeroProfileRightDeriv ρ) := by
  have hA : Measurable (fun x : ℝ => cellSumA ρ ⌊x⌋₊) :=
    (measurable_from_nat (f := cellSumA ρ)).comp Nat.measurable_floor
  have hB : Measurable (fun x : ℝ => cellSumB ρ ⌊x⌋₊) :=
    (measurable_from_nat (f := cellSumB ρ)).comp Nat.measurable_floor
  unfold FullAudit17_zeroProfileRightDeriv srhoCellDeriv
  have h1 : Measurable (fun x : ℝ => (x : ℂ) ^ (-ρ - 1)) := Complex.measurable_ofReal.pow_const _
  have h2 : Measurable (fun x : ℝ => (x : ℂ) ^ (ρ - 1 - 1)) := Complex.measurable_ofReal.pow_const _
  exact (((measurable_const.mul h1).mul hA).sub ((measurable_const.mul h2).mul hB)).div_const _ |>.neg

lemma FullAudit17_hasDerivWithinAt_zeroProfile_Ioi (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    HasDerivWithinAt (zeroProfile ρ) (FullAudit17_zeroProfileRightDeriv ρ x) (Ioi x) x := by
  by_cases hn : x ∈ Set.range (fun n : ℕ => (n : ℝ))
  · obtain ⟨m, rfl⟩ := hn
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hx
      · exact h
    have h := hasDerivWithinAt_zeroProfile_right ρ hm
    rw [FullAudit17_zeroProfileRightDeriv, Nat.floor_natCast]
    exact h.mono Ioi_subset_Ici_self
  · have hcell := mem_cell_of_not_nat hx hn
    exact (hasDerivAt_zeroProfile_cell ρ hcell).hasDerivWithinAt

lemma FullAudit17_zeroProfileRightDeriv_bound {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → ‖FullAudit17_zeroProfileRightDeriv ρ x‖ ≤ C * min 1 (x ^ (-2 : ℝ)) := by
  set C := (‖2 * ρ - 1‖ + srhoDerivRemainderConst ρ) / ‖normalizationBrho ρ‖
  have hC0 : 0 ≤ C := by
    have : 0 ≤ srhoDerivRemainderConst ρ := by unfold srhoDerivRemainderConst; positivity
    positivity
  refine ⟨C, hC0, fun x hx => ?_⟩
  rw [FullAudit17_zeroProfileRightDeriv, norm_neg]
  rcases lt_or_ge x 1 with hx1 | hx1
  · rw [Nat.floor_eq_zero.mpr hx1, srhoCellDeriv_zero, zero_div, norm_zero]
    exact mul_nonneg hC0 (le_min zero_le_one (Real.rpow_nonneg hx.le _))
  · have hcell : x ∈ Ico (⌊x⌋₊ : ℝ) (⌊x⌋₊ + 1) := ⟨Nat.floor_le hx.le, Nat.lt_floor_add_one x⟩
    have hb := zeroProfile_deriv_bound hz h0 h1 hcell hx1
    have hmin : min 1 (x ^ (-2 : ℝ)) = x ^ (-2 : ℝ) :=
      min_eq_right (Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num))
    rw [hmin]; exact hb

/-- At an actual zero the zero profile, with its explicit right derivative, lies in the actual
log form domain. -/
theorem FullAudit17_expected_zero_profile_in_form_domain {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : LogFormDomain (zeroProfile ρ) (FullAudit17_zeroProfileRightDeriv ρ) := by
  obtain ⟨C, hC0, hC⟩ := FullAudit17_zeroProfileRightDeriv_bound hz h0 h1
  have hm := FullAudit17_measurable_zeroProfileRightDeriv ρ
  have hII : ∀ a b : ℝ, 0 < a → 0 < b → IntervalIntegrable (FullAudit17_zeroProfileRightDeriv ρ) volume a b := by
    intro a b ha hb
    refine (intervalIntegrable_const (c := C)).mono_fun hm.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_uIoc).mpr (Eventually.of_forall (fun x hx => ?_))
    have hx0 : 0 < x := by
      rcases le_total a b with hab | hab
      · rw [uIoc_of_le hab] at hx; linarith [hx.1]
      · rw [uIoc_of_ge hab] at hx; linarith [hx.1]
    refine (hC x hx0).trans ?_
    rw [Real.norm_eq_abs, abs_of_nonneg hC0]
    exact mul_le_of_le_one_right hC0 (min_le_left _ _)
  have hFTC : ∀ a b : ℝ, 0 < a → a ≤ b →
      zeroProfile ρ b - zeroProfile ρ a = ∫ x in a..b, FullAudit17_zeroProfileRightDeriv ρ x := by
    intro a b ha hab
    rw [intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
      ((continuous_zeroProfile ρ).continuousOn)
      (fun x hx => FullAudit17_hasDerivWithinAt_zeroProfile_Ioi ρ (lt_trans ha hx.1))
      (hII a b ha (lt_of_lt_of_le ha hab))]
  refine ⟨fun a b ha hb => ?_, hII, hm, (memLp_two_zeroProfile hz h0 h1).restrict _, ?_⟩
  · rcases le_total a b with hab | hab
    · exact hFTC a b ha hab
    · rw [intervalIntegral.integral_symm, ← hFTC b a hb hab]; ring
  · set g : ℝ → ℝ := fun x => C * min x (x ^ (-1 : ℝ)) with hg
    have hgL : MemLp g 2 (volume.restrict (Ioi 0)) := by
      have hgm : Measurable g := by fun_prop
      refine (memLp_two_iff_integrable_sq hgm.aestronglyMeasurable).mpr ?_
      have hdom : Integrable (fun x : ℝ => C ^ 2 * (Ioc 0 1).indicator (fun _ => (1 : ℝ)) x +
          C ^ 2 * (Ioi 1).indicator (fun x => x ^ (-2 : ℝ)) x) (volume.restrict (Ioi 0)) := by
        refine Integrable.add ?_ ?_
        · refine Integrable.const_mul ?_ _
          refine ((integrable_indicator_iff measurableSet_Ioc).mpr ?_).mono_measure
            Measure.restrict_le_self
          exact integrableOn_const (by simp) (by simp)
        · refine Integrable.const_mul ?_ _
          exact ((integrable_indicator_iff measurableSet_Ioi).mpr
            (integrableOn_Ioi_rpow_of_lt (by norm_num) one_pos)).mono_measure Measure.restrict_le_self
      refine hdom.mono' (hgm.pow_const 2).aestronglyMeasurable ?_
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun x hx => ?_))
      have hx0 : (0 : ℝ) < x := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), hg, mul_pow]
      rcases le_or_gt x 1 with hx1 | hx1
      · have hmin : min x (x ^ (-1 : ℝ)) = x := by
          refine min_eq_left ?_
          rw [Real.rpow_neg_one]; exact le_trans hx1 (one_le_inv₀ hx0 |>.mpr hx1)
        rw [hmin, indicator_of_mem (show x ∈ Ioc 0 1 from ⟨hx0, hx1⟩),
          indicator_of_notMem (show x ∉ Ioi 1 from not_lt.mpr hx1), mul_zero, add_zero, mul_one]
        exact mul_le_of_le_one_right (sq_nonneg C) (by nlinarith)
      · have hmin : min x (x ^ (-1 : ℝ)) = x ^ (-1 : ℝ) := by
          refine min_eq_right ?_
          rw [Real.rpow_neg_one]; exact le_trans (inv_le_one_of_one_le₀ hx1.le) hx1.le
        rw [hmin, indicator_of_notMem (show x ∉ Ioc 0 1 from fun h => absurd h.2 (not_le.mpr hx1)),
          indicator_of_mem (show x ∈ Ioi 1 from hx1), mul_zero, zero_add,
          ← Real.rpow_natCast (x ^ (-1 : ℝ)) 2, ← Real.rpow_mul hx0.le]
        norm_num
    refine hgL.of_le ((Complex.measurable_ofReal.mul hm).aestronglyMeasurable) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun x hx => ?_))
    have hx0 : (0 : ℝ) < x := hx
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0, hg, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hC0 (le_min hx0.le (Real.rpow_nonneg hx0.le _)))]
    calc x * ‖FullAudit17_zeroProfileRightDeriv ρ x‖ ≤ x * (C * min 1 (x ^ (-2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (hC x hx0) hx0.le
      _ = C * min x (x ^ (-1 : ℝ)) := by
          rw [show x * (C * min 1 (x ^ (-2 : ℝ))) = C * (min 1 (x ^ (-2 : ℝ)) * x) by ring,
            min_mul_of_nonneg _ _ hx0.le, one_mul,
            show x ^ (-2 : ℝ) * x = x ^ (-1 : ℝ) by
              rw [← Real.rpow_add_one hx0.ne']; norm_num]

/-- Paper S1.5 for the actual zero profile: ∫_0^∞ x²|h'|² = ∫ |ψ'|² + (1/4) ∫_0^∞ |h|². -/
theorem FullAudit17_expected_zero_profile_form_identity {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    logForm (FullAudit17_zeroProfileRightDeriv ρ) =
      (∫ t, ‖logUnitaryDeriv (zeroProfile ρ) (FullAudit17_zeroProfileRightDeriv ρ) t‖ ^ 2) +
        1 / 4 * ∫ x in Ioi 0, ‖zeroProfile ρ x‖ ^ 2 :=
  (log_unitary_form_identity _ _ (FullAudit17_expected_zero_profile_in_form_domain hz h0 h1)).2.2.2.2.1

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedMasks.lean; SHA256 46ebd67a354c4d73b4fbdd777a62594d10cbafe38b3d8db8029c5ba5570d6503 -/
section

/-! Independent consumers for the complete scheduled mask interfaces.
Constants precede all real horizons and allowed palettes. No Theta equality
is an input, and both retained-minus-full orientations are tested. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem expected_log_slack_both_low_masks_subexp (r d : ℕ) (hr : 2 ≤ r) (hd : r - 1 ≤ d)
    (C η K : ℝ) (hC : 1 < C) (hη : 0 ≤ η) :
    Measurable nativeMovingPrimitiveCutoff ∧
    ∃ a b a' b' T₀ : ℝ, 0 ≤ b ∧ 0 ≤ b' ∧ 1 ≤ T₀ ∧
      (∀ T : ℝ, T₀ ≤ T → ∀ Q : ℕ, Squarefree Q → (Q : ℝ) ≤ T ^ η →
        Real.log (1 + |nativeRawLow d r Q (logSlackY r K T) C T|)
          ≤ a + Real.sqrt T + b * Real.log T ∧
        Real.log (1 + |nativeAbsorbedLow d r Q hd (logSlackY r K T) C T|)
          ≤ a' + Real.sqrt T + b' * Real.log T) ∧
      (∀ (τ : HorizonSchedule) (Q : ℕ → ℕ), (∀ n, Squarefree (Q n)) →
        (∀ᶠ n in atTop, (Q n : ℝ) ≤ τ.time n ^ η) →
        SubexpAlong τ (fun n => nativeRawLow d r (Q n)
          (logSlackY r K (τ.time n)) C (τ.time n)) ∧
        SubexpAlong τ (fun n => nativeAbsorbedLow d r (Q n) hd
          (logSlackY r K (τ.time n)) C (τ.time n)) ∧
        (∀ᶠ n in atTop,
          nativeRawHigh d r (Q n) (logSlackY r K (τ.time n)) C (τ.time n) -
            nativeAbsorbedHigh d r (Q n) hd (logSlackY r K (τ.time n)) C (τ.time n) =
          nativeAbsorbedLow d r (Q n) hd (logSlackY r K (τ.time n)) C (τ.time n) -
            nativeRawLow d r (Q n) (logSlackY r K (τ.time n)) C (τ.time n))) := by
  exact log_slack_both_low_masks_subexp r d hr hd C η K hC hη

theorem expected_log_slack_masked_energy_rate_difference (r d : ℕ) (hr : 2 ≤ r) (hd : r - 1 ≤ d)
    (C η K : ℝ) (hC : 1 < C) (hη : 0 ≤ η)
    (hK : C + (r : ℝ) * η + 2 * r < K)
    (τ : HorizonSchedule) (Q : ℕ → ℕ)
    (hQ : ∀ n, Squarefree (Q n))
    (hbudget : ∀ᶠ n in atTop, (Q n : ℝ) ≤ τ.time n ^ η) :
    Tendsto (fun n =>
      Real.log (1 + max (nativeRawHigh d r (Q n)
        (logSlackY r K (τ.time n)) C (τ.time n)) 0) / (2 * τ.time n) -
      Real.log (1 + ∫ t in Icc (τ.time n - C * Real.log (τ.time n)) (τ.time n),
        (primeFieldFamily d t)^2) / (2 * τ.time n)) atTop (𝓝 0) ∧
    Tendsto (fun n =>
      Real.log (1 + max (nativeAbsorbedHigh d r (Q n) hd
        (logSlackY r K (τ.time n)) C (τ.time n)) 0) / (2 * τ.time n) -
      Real.log (1 + ∫ t in Icc (τ.time n - C * Real.log (τ.time n)) (τ.time n),
        (primeFieldFamily d t)^2) / (2 * τ.time n)) atTop (𝓝 0) := by
  exact log_slack_masked_energy_rate_difference r d hr hd C η K hC hη hK τ Q hQ hbudget

/-- The original Pj specialization, not an order-zero or autocorrelation source. -/
theorem FullAudit18_example_53 (τ : HorizonSchedule) :
    Tendsto (fun n => positiveRate τ (fun j => nativeRawHigh 1 2 1
      (logSlackY 2 8 (τ.time j)) 2 (τ.time j)) n -
      Real.log (1 + nativePhysicalWindowEnergy 1 2 (τ.time n))/(2*τ.time n)) atTop (𝓝 0) ∧
    Tendsto (fun n => positiveRate τ (fun j => nativeAbsorbedHigh 1 2 1 (by norm_num)
      (logSlackY 2 8 (τ.time j)) 2 (τ.time j)) n -
      Real.log (1 + nativePhysicalWindowEnergy 1 2 (τ.time n))/(2*τ.time n)) atTop (𝓝 0) := by
  apply log_slack_masked_energy_rate_difference 2 1 (by norm_num) (by norm_num)
    2 0 8 (by norm_num) (by norm_num) (by norm_num) τ (fun _ => 1)
    (fun _ => by simp)
  filter_upwards with n
  simp

/-- Actual L2 realizations remain available on every real initial window,
including reversed or degenerate intervals. No eventual positivity is needed
for constructing the vectors or their exact energy identity. -/
theorem FullAudit18_example_69 (d : ℕ) (C T : ℝ) :
    ‖nativePrimeWindowVector d C T‖^2 =
      ∫ t in Icc (T-C*Real.log T) T, (primeFieldFamily d t)^2 := by
  exact nativePrimeWindowVector_norm_sq d C T

theorem FullAudit18_example_74 (f : ℝ → ℝ) (hf : Continuous f) (C T : ℝ) :
    MemLp ((Icc (T-C*Real.log T) T).indicator f) 2 (volume : Measure ℝ) := by
  exact nativeWindowFunction_memLp f hf C T

/-- A noninteger cutoff and a nonsquarefree total product remain in the
Dirichlet-convolution coefficient, rather than a pointwise power. -/
theorem FullAudit18_example_80 : (((nativeLargeCoefficients 1 (3/2) ^ 2 : ArithmeticFunction ℝ)) 4) = 1 := by
  have h₁ : nativeLargeCoefficients 1 (3/2) 1=0 := by
    norm_num [nativeLargeCoefficients]
  have h₂ : nativeLargeCoefficients 1 (3/2) 2=(-1:ℝ) := by
    norm_num [nativeLargeCoefficients,nativeInverseCoefficients,coprimeCoefficients,
      ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have h₄ : nativeLargeCoefficients 1 (3/2) 4=0 := by
    have hμ : ArithmeticFunction.moebius 4=0 := by
      convert ArithmeticFunction.moebius_apply_prime_pow Nat.prime_two
        (by decide : (2:ℕ)≠0) using 1 <;> norm_num
    norm_num [nativeLargeCoefficients,nativeInverseCoefficients,coprimeCoefficients,hμ]
  have hanti : (4:ℕ).divisorsAntidiagonal={(1,4),(2,2),(4,1)} := by decide
  rw [pow_two,ArithmeticFunction.mul_apply,hanti]
  norm_num [h₁,h₂,h₄]

end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedMultiplicity.lean; SHA256 7457d65c129374a9f13bbee5e2dd67f53882eb64fd56dfb0d6ff5e673e85498f -/
section

/-! Independent full-scope Laguerre norm and physical-domain consumers.
The expected type is written explicitly rather than obtained by reflection.
No moment, residual or terminal-memory conclusion is supplied as an input. -/
noncomputable section
open Set MeasureTheory Polynomial
open scoped Topology
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem expected_laguerre_tail_norm (m : ℕ) (hm : 1 ≤ m) (p : ℂ) (hp : 0 < p.re) (T : ℝ) :
    (monicLaguerre (m-1)).Monic ∧
    (∀ Q : Polynomial ℝ, Q.natDegree < m-1 →
      laguerreWeightedPair (monicLaguerre (m-1)) Q = 0) ∧
    MemLp (monicLaguerreTail (m-1) p T) 2 volume ∧
    (monicLaguerreTailL2 (m-1) p T hp : ℝ → ℂ) =ᵐ[volume]
      monicLaguerreTail (m-1) p T ∧
    ‖monicLaguerreTailL2 (m-1) p T hp‖^2 =
      Real.exp (-2*p.re*T)*((m-1).factorial:ℝ)^2/(2*p.re)^(2*(m-1)+1) ∧
    ‖monicLaguerreTailL2 (m-1) p T hp‖ =
      Real.exp (-p.re*T)*((m-1).factorial:ℝ)/(2*p.re)^((m:ℝ)-1/2) := by
  exact laguerre_tail_norm m hm p hp T

/-- The degree-zero test is the literal constant polynomial. -/
theorem FullAudit19_example_26 : monicLaguerre 0 = (1 : Polynomial ℝ) := by
  simp [monicLaguerre]

/-- The pointwise representative retains the conjugation and real shift. -/
theorem FullAudit19_example_30 (n : ℕ) (p : ℂ) (T t : ℝ) (ht : T ≤ t) :
    monicLaguerreTail n p T t =
      (((2*p.re)^n)⁻¹*(monicLaguerre n).eval (2*p.re*(t-T)):ℝ)*
        Complex.exp (-(starRingEnd ℂ p)*(t:ℂ)) := by
  exact Set.indicator_of_mem ht _

theorem FullAudit19_example_36 (n : ℕ) (p : ℂ) (T t : ℝ) (ht : t < T) :
    monicLaguerreTail n p T t = 0 := by
  exact Set.indicator_of_notMem (not_le.mpr ht) _

/-- Negative lower endpoints and either sign of the ordinate are permitted. -/
theorem FullAudit19_example_41 (tau : ℝ) :
    ‖monicLaguerreTailL2 0 (1 + (tau:ℂ)*Complex.I) (-3) (by simp)‖ =
      Real.exp 3 / (2:ℝ)^(1/2:ℝ) := by
  have h := (laguerre_tail_norm 1 (by norm_num)
    (1 + (tau:ℂ)*Complex.I) (by simp) (-3)).2.2.2.2.2
  norm_num at h ⊢
  exact h

theorem FullAudit19_example_49 (n : ℕ) (p : ℂ) (hp : 0 < p.re) (T : ℝ) :
    (∫ t : ℝ, ‖monicLaguerreTail n p T t‖^2) =
      Real.exp (-2*p.re*T)*(n.factorial:ℝ)^2/(2*p.re)^(2*n+1) := by
  exact monicLaguerreTail_integral_norm_sq n p T hp

end Zeta23.OPICAFollowup.Validation
/-! Independent Stage2 consumers of the actual MultiplicityTail module.
The stated types expand the physical convolution, residual and memory. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory Filter
namespace Zeta23.OPICAFollowup.Validation
open Zeta23.CCM Zeta23.ExceptionalZero

theorem expected_native_auxiliary_top_moment :
    ∀ k d : ℕ, ∀ rho : zetaZeroConfig.carrier, 1/2<(rho:ℂ).re →
    MemLp (fun t : ℝ => ∫ s : ℝ,
      (auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)) 2 volume ∧
    (nativeAuxiliaryStableVector k d:NativeCompletionL2)=ᵐ[volume]
      (fun t : ℝ => ∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)) ∧
    (∀ t : ℝ,(∫ s : ℝ,(auxCompletionKernel k s:ℂ)*(primeFieldFamily d (t-s):ℂ))=
      ∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)) ∧
    ‖nativeAuxiliaryStableVector k d‖≤
      (∫ s : ℝ,‖auxCompletionFilter k s‖)*‖auxiliaryDriveCausalVector d‖ ∧
    (∀ j<zeroMult (rho:ℂ)-1,
      Integrable (fun t : ℝ => (t:ℂ)^j*Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
        (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ))) ∧
      (∫ t : ℝ,(t:ℂ)^j*Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
        (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))=0) ∧
    Integrable (fun t : ℝ => (t:ℂ)^(zeroMult (rho:ℂ)-1)*
      Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
        (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ))) ∧
    (∫ t : ℝ,(t:ℂ)^(zeroMult (rho:ℂ)-1)*Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
      (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))=
      (-1:ℂ)^zeroMult (rho:ℂ)*auxRationalFactor k ((rho:ℂ)-1/2)*
        sourceFamilyLaplace d ((rho:ℂ)-1/2)*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ) ∧
    (∫ t : ℝ,(t:ℂ)^(zeroMult (rho:ℂ)-1)*Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
      (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))≠0 := by
  intro k d rho hright
  exact native_auxiliary_top_moment k d rho hright

theorem FullAudit19_expected_actual_auxiliary_factorial_stability : ∀ k d : ℕ,
    ‖nativeAuxiliaryStableVector k d‖≤
      (2/(Nat.factorial (k+1):ℝ))*‖auxiliaryDriveCausalVector d‖ :=
  nativeAuxiliaryStableVector_factorial_bound

theorem FullAudit19_expected_actual_logweighted_drive : ∀ d : ℕ, ∀ t : ℝ,
    integerDriveFamily d t=
      ∑' n : ℕ,(Real.log n/Real.sqrt n)*sourceOrderFamily d (t-Real.log n) := by
  intro d t
  rfl

theorem FullAudit19_expected_actual_auxiliary_integrand : ∀ k d : ℕ, ∀ t : ℝ,
    Integrable (fun s : ℝ => (auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)) :=
  nativeAuxiliaryInput_integrand_integrable

theorem FullAudit19_expected_actual_auxiliary_safe_laplace : ∀ k d : ℕ, ∀ z : ℂ, 1/2<z.re →
    (∫ t : ℝ,Complex.exp (-z*(t:ℂ))*(∫ s : ℝ,
      (auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))=
      -auxRationalFactor k z*sourceFamilyLaplace d z*deriv riemannZeta (z+1/2) := by
  intro k d z hz
  exact (nativeAuxiliaryInput_initial_laplace k d hz).2

theorem FullAudit19_expected_actual_simple_zero_phase : ∀ k d : ℕ, ∀ rho : zetaZeroConfig.carrier,
    1/2<(rho:ℂ).re → zeroMult (rho:ℂ)=1 →
    (∫ t : ℝ,Complex.exp (-((rho:ℂ)-1/2)*(t:ℂ))*
      (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ)))=
        -auxRationalFactor k ((rho:ℂ)-1/2)*sourceFamilyLaplace d ((rho:ℂ)-1/2)*
          deriv riemannZeta (rho:ℂ) := by
  intro k d rho hright hm
  have h := nativeAuxiliaryMoment_top_value k d rho hright
  simpa only [hm,Nat.sub_self,nativeAuxiliaryMoment,nativeAuxiliaryInput,pow_zero,
    pow_one,one_mul,neg_mul,iteratedDeriv_one] using h

theorem expected_native_auxiliary_tail_residual_lower :
    ∀ k d : ℕ, 1≤k → ∀ rho : zetaZeroConfig.carrier, 1/2<(rho:ℂ).re → ∀ T : ℝ,
    0<((2*((rho:ℂ)-1/2).re)^((zeroMult (rho:ℂ):ℝ)-1/2)*
      ‖sourceFamilyLaplace d ((rho:ℂ)-1/2)*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)‖/
        ((zeroMult (rho:ℂ)-1).factorial:ℝ)) ∧
    MemLp (nativeTruncatedResidual k d T) 2 volume ∧
    (nativeTruncatedResidualVector k d T:NativeCompletionL2)=ᵐ[volume] nativeTruncatedResidual k d T ∧
    (∀ t<T,nativeTruncatedResidual k d T t=0) ∧
    ((2*((rho:ℂ)-1/2).re)^((zeroMult (rho:ℂ):ℝ)-1/2)*
      ‖sourceFamilyLaplace d ((rho:ℂ)-1/2)*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)‖/
        ((zeroMult (rho:ℂ)-1).factorial:ℝ))*‖auxRationalFactor k ((rho:ℂ)-1/2)‖*
          Real.exp (((rho:ℂ)-1/2).re*T)≤‖(nativeTruncatedResidualVector k d T:NativeCompletionL2)‖ := by
  intro k d hk rho hright T
  exact native_auxiliary_tail_residual_lower k d hk rho hright T

theorem FullAudit19_expected_native_residual_literal : ∀ k d : ℕ, ∀ T t : ℝ,
    nativeTruncatedResidual k d T t=
      (∫ s : ℝ,(auxCompletionFilter k s:ℂ)*(integerDriveFamily d (t-s):ℂ))-
        (∫ s : ℝ,(auxCompletionKernel k s:ℂ)*
          (((Icc (0:ℝ) T).indicator (primeFieldFamily d)) (t-s):ℂ)) := by
  intros
  rfl

theorem expected_native_terminal_memory_lower :
    ∀ k d : ℕ, 1≤k → ∀ rho : zetaZeroConfig.carrier, 1/2<(rho:ℂ).re → ∀ T : ℝ,
    Real.sqrt (2*auxCompletionAlpha k)/auxCompletionBound k*
      max (((2*((rho:ℂ)-1/2).re)^((zeroMult (rho:ℂ):ℝ)-1/2)*
        ‖sourceFamilyLaplace d ((rho:ℂ)-1/2)*iteratedDeriv (zeroMult (rho:ℂ)) riemannZeta (rho:ℂ)‖/
          ((zeroMult (rho:ℂ)-1).factorial:ℝ))*‖auxRationalFactor k ((rho:ℂ)-1/2)‖*
            Real.exp (((rho:ℂ)-1/2).re*T)-‖nativeAuxiliaryStableVector k d‖) 0≤
      ∫ s : ℝ in Icc 0 T,Real.exp (-auxCompletionAlpha k*(T-s))*|primeFieldFamily d s| := by
  intro k d hk rho hright T
  exact native_terminal_memory_lower k d hk rho hright T


end Zeta23.OPICAFollowup.Validation
end
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedNativeResolvent.lean; SHA256 df50d36b3726e70979f0bce5ba28d39348f22d46aed30d49c4f4fa5ae2f6196b -/
section

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.native_forced_resolvent_unique`,
`Zeta23.OPICAFollowup.native_sample_stieltjes_identity` and
`Zeta23.OPICAFollowup.native_profile_spectral_norms` (F2).

Definition audits pin the forced log-resolvent as the inverse log-Fourier transform of the actual
quotient κ ζ(1/2 + iξ)/(a(ξ) - κ), the log profile e^(t/2) h(e^t) and the sample defect
b = Σ_{n ≥ 1} h(n) - 1/2. All three roots are restated in full. Domain consumers check:
- an actual off-line zero (Re ρ ≠ 1/2, Im ρ ≠ 0, as the statement requires) has nonreal κ, so its log
  profile is the forced log-resolvent and b = κ M(κ);
- for such a zero b ≠ 0 and Im(b/κ)/Im κ = ∫ dω/|a - κ|² > 0, with b/κ = M(κ) identified with the
  Stage 12 sampling ratio, so the two derivations of (S2.4) agree;
- the forced log-resolvent itself is an H¹ weak solution;
- the diagonal mixed pairing N(ρ, ρ) is the norm formula, cast to ℂ;
- at the conjugate zero conj ρ (conjugate coincidence) the undivided identity forces
  b_{conj ρ} = conj b_ρ, which is consistent with M(conj κ) = conj M(κ);
- at a critical-line zero (κ on the cut, where no root is asserted) the supporting undivided
  identity reads (ξ² - (Im ρ)²) 𝓕_log ψ(ξ) = κ ζ(1/2 + iξ); both sides vanish at ξ = Im ρ. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real SchwartzMap
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit20_audit_nativeLogResolvent (κ : ℂ) (t : ℝ) :
    nativeLogResolvent κ t = 1 / (2 * π) * ∫ ξ : ℝ, cexp (((ξ * t : ℝ) : ℂ) * I) *
      (κ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - κ)) := rfl

theorem FullAudit20_audit_logUnitary (h : ℝ → ℂ) (t : ℝ) :
    logUnitary h t = (Real.exp (t / 2) : ℂ) * h (Real.exp t) := rfl

theorem FullAudit20_audit_profileSampleDefect (ρ : ℂ) :
    profileSampleDefect ρ = (∑' n : ℕ, zeroProfile ρ (n + 1)) - 1 / 2 := rfl

theorem FullAudit20_audit_spectralKappa (ρ : ℂ) : spectralKappa ρ = ρ * (1 - ρ) := rfl

/-! ### Restated roots -/

theorem expected_native_forced_resolvent_unique {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    LogH1 (logUnitary (zeroProfile ρ)) (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv φ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, logUnitary (zeroProfile ρ) t * φ t =
        spectralKappa ρ * nativeLogForce φ) ∧
    (∀ D D' : ℝ → ℂ, LogH1 D D' →
      (∀ φ : 𝓢(ℝ, ℂ), (∫ t, D' t * deriv φ t) + (1 / 4 - spectralKappa ρ) * ∫ t, D t * φ t =
        spectralKappa ρ * nativeLogForce φ) → D = logUnitary (zeroProfile ρ)) ∧
    (∀ ξ : ℝ, logFourier (logUnitary (zeroProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I) / ((spectralEnergy ξ : ℂ) - spectralKappa ρ)) ∧
    logUnitary (zeroProfile ρ) = nativeLogResolvent (spectralKappa ρ) :=
  native_forced_resolvent_unique hz h0 h1 hκ

theorem expected_native_sample_stieltjes_identity {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    profileSampleDefect ρ = (∑' n : ℕ, zeroProfile ρ (n + 1)) - 1 / 2 ∧
    (∀ n : ℕ, ∫ x in (n : ℝ)..(n + 1), ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x =
      zeroProfile ρ ((n : ℝ) + 1) - ∫ x in (n : ℝ)..(n + 1), zeroProfile ρ x) ∧
    IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x) (Ioi 0) ∧
    profileSampleDefect ρ = ∫ x in Ioi (0 : ℝ), ((Int.fract x : ℝ) : ℂ) * zeroProfileDeriv ρ x ∧
    profileSampleDefect ρ = ∫ t, sawtoothWeight t *
      (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t - logUnitary (zeroProfile ρ) t / 2) ∧
    ‖profileSampleDefect ρ‖ ≤ (∫ t, ‖sawtoothWeight t‖ ^ 2) ^ (1 / 2 : ℝ) *
      ((∫ t, ‖logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t‖ ^ 2) +
        1 / 4 * ∫ t, ‖logUnitary (zeroProfile ρ) t‖ ^ 2) ^ (1 / 2 : ℝ) ∧
    (∀ t, starRingEnd ℂ (sawtoothWeight t) = sawtoothWeight t) ∧
    profileSampleDefect ρ = 1 / (2 * π) * ∫ ξ : ℝ, starRingEnd ℂ (logFourier sawtoothWeight ξ) *
      (((ξ : ℂ) * I - 1 / 2) * logFourier (logUnitary (zeroProfile ρ)) ξ) ∧
    profileSampleDefect ρ = spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ) :=
  native_sample_stieltjes_identity hz h0 h1 hκ

theorem expected_native_profile_spectral_norms {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : (spectralKappa ρ).im ≠ 0) :
    ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 =
      ‖spectralKappa ρ‖ ^ 2 *
        ∫ ξ, (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    logForm (zeroProfileDeriv ρ) =
      ‖spectralKappa ρ‖ ^ 2 * ∫ ξ, spectralEnergy ξ *
        (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 =
      ‖spectralKappa ρ‖ ^ 2 * ((arithmeticStieltjes (spectralKappa ρ)).im / (spectralKappa ρ).im) ∧
    (∀ σ : ℂ, riemannZeta σ = 0 → 0 < σ.re → σ.re < 1 → spectralKappa σ ∈ spectralResolventSet →
      profileGram ρ σ = spectralKappa ρ * starRingEnd ℂ (spectralKappa σ) *
        ∫ ξ, (((spectralEnergy ξ : ℂ) - spectralKappa ρ) *
          ((spectralEnergy ξ : ℂ) - starRingEnd ℂ (spectralKappa σ)))⁻¹ ∂arithmeticSpectralMeasure ∧
      profileFormGram ρ σ = spectralKappa ρ * starRingEnd ℂ (spectralKappa σ) *
        ∫ ξ, (spectralEnergy ξ : ℂ) * (((spectralEnergy ξ : ℂ) - spectralKappa ρ) *
          ((spectralEnergy ξ : ℂ) - starRingEnd ℂ (spectralKappa σ)))⁻¹ ∂arithmeticSpectralMeasure ∧
      (spectralKappa ρ - starRingEnd ℂ (spectralKappa σ)) * profileGram ρ σ =
        starRingEnd ℂ (spectralKappa σ) * profileSampleDefect ρ -
          spectralKappa ρ * starRingEnd ℂ (profileSampleDefect σ)) ∧
    ‖profileSampleDefect ρ‖ ≤ ‖spectralKappa ρ‖ * (1 + ‖spectralKappa ρ‖ / |(spectralKappa ρ).im|) *
      (Real.log (2 * π) - Real.eulerMascheroniConstant) :=
  native_profile_spectral_norms hz h0 h1 hκ

/-! ### Domain consumers -/

lemma FullAudit20_offline_kappa_im {ρ : ℂ} (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) : (spectralKappa ρ).im ≠ 0 := by
  have hk : (spectralKappa ρ).im = (1 - 2 * ρ.re) * ρ.im := by
    simp only [spectralKappa, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    ring
  rw [hk]
  exact mul_ne_zero (fun h => hre (by linarith)) him

/-- An actual off-line zero has nonreal κ: its log profile is the forced log-resolvent and
b = κ M(κ). -/
theorem FullAudit20_expected_offline_zero {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    (spectralKappa ρ).im ≠ 0 ∧
    logUnitary (zeroProfile ρ) = nativeLogResolvent (spectralKappa ρ) ∧
    profileSampleDefect ρ = spectralKappa ρ * arithmeticStieltjes (spectralKappa ρ) := by
  have hk := FullAudit20_offline_kappa_im hre him
  exact ⟨hk, (native_forced_resolvent_unique hz h0 h1 (Or.inl hk)).2.2.2.2,
    (native_sample_stieltjes_identity hz h0 h1 (Or.inl hk)).2.2.2.2.2.2.2.2⟩

/-- For nonreal κ the sample defect is nonzero, b/κ = M(κ), and the Stage 12 sampling ratio
Im(b/κ)/Im κ = N/|κ|² equals the measure ratio ∫ dω/|a - κ|² > 0. -/
theorem FullAudit20_expected_sample_ratio {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : (spectralKappa ρ).im ≠ 0) :
    profileSampleDefect ρ / spectralKappa ρ = arithmeticStieltjes (spectralKappa ρ) ∧
    (profileSampleDefect ρ / spectralKappa ρ).im / (spectralKappa ρ).im =
      ∫ ξ, (‖(spectralEnergy ξ : ℂ) - spectralKappa ρ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    0 < (profileSampleDefect ρ / spectralKappa ρ).im / (spectralKappa ρ).im ∧
    profileSampleDefect ρ ≠ 0 := by
  have hk0 : spectralKappa ρ ≠ 0 := fun h => hκ (by rw [h, Complex.zero_im])
  have hb := (native_sample_stieltjes_identity hz h0 h1 (Or.inl hκ)).2.2.2.2.2.2.2.2
  obtain ⟨-, hIm, hpos, -⟩ := arithmetic_stieltjes_sign_budget hκ
  have hM : profileSampleDefect ρ / spectralKappa ρ = arithmeticStieltjes (spectralKappa ρ) := by
    rw [hb]; field_simp
  refine ⟨hM, by rw [hM, hIm], by rw [hM, hIm]; exact hpos, fun h0b => ?_⟩
  have : (arithmeticStieltjes (spectralKappa ρ)).im = 0 := by
    rw [← hM, h0b, zero_div, Complex.zero_im]
  rw [this, zero_div] at hIm
  linarith

/-- The forced log-resolvent is itself an H¹ weak solution of the forced equation. -/
theorem FullAudit20_expected_resolvent_weak_solution {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : spectralKappa ρ ∈ spectralResolventSet) :
    LogH1 (nativeLogResolvent (spectralKappa ρ)) (logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ)) ∧
    ∀ φ : 𝓢(ℝ, ℂ), (∫ t, logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t * deriv φ t) +
      (1 / 4 - spectralKappa ρ) * ∫ t, nativeLogResolvent (spectralKappa ρ) t * φ t =
        spectralKappa ρ * nativeLogForce φ := by
  obtain ⟨hD, hW, -, -, hEq⟩ := native_forced_resolvent_unique hz h0 h1 hκ
  rw [← hEq]
  exact ⟨hD, hW⟩

/-- The diagonal mixed pairing is the norm formula: N(ρ, ρ) = ∫ |h|² = |κ|² ∫ dω/|a - κ|². -/
theorem FullAudit20_expected_diagonal_gram {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hκ : (spectralKappa ρ).im ≠ 0) :
    profileGram ρ ρ = ((∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 : ℝ) : ℂ) := by
  obtain ⟨hN, -, -, hmix, -⟩ := native_profile_spectral_norms hz h0 h1 hκ
  rw [(hmix ρ hz h0 h1 (Or.inl hκ)).1, hN, Complex.ofReal_mul, ← integral_complex_ofReal]
  have hk : spectralKappa ρ * starRingEnd ℂ (spectralKappa ρ) = ((‖spectralKappa ρ‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; ring
  rw [hk]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
  have hc : (spectralEnergy ξ : ℂ) - starRingEnd ℂ (spectralKappa ρ) =
      starRingEnd ℂ ((spectralEnergy ξ : ℂ) - spectralKappa ρ) := by
    rw [map_sub, Complex.conj_ofReal]
  simp only
  rw [hc, Complex.mul_conj']
  push_cast; ring

/-- Conjugate coincidence: conj ρ is again an actual zero with κ(conj ρ) = conj κ(ρ); the undivided
identity at (ρ, conj ρ) has vanishing left side and forces b_{conj ρ} = conj b_ρ, which matches
M(conj κ) = conj M(κ) on the measure side. -/
theorem FullAudit20_expected_conjugate_coincidence {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hκ : (spectralKappa ρ).im ≠ 0) :
    spectralKappa (starRingEnd ℂ ρ) = starRingEnd ℂ (spectralKappa ρ) ∧
    profileSampleDefect (starRingEnd ℂ ρ) = starRingEnd ℂ (profileSampleDefect ρ) := by
  have hzc : riemannZeta (starRingEnd ℂ ρ) = 0 := by rw [_root_.riemannZeta_conj, hz, map_zero]
  have hkc : spectralKappa (starRingEnd ℂ ρ) = starRingEnd ℂ (spectralKappa ρ) := by
    simp only [spectralKappa, map_mul, map_sub, map_one]
  have hκc : (spectralKappa (starRingEnd ℂ ρ)).im ≠ 0 := by
    rw [hkc, Complex.conj_im]; exact neg_ne_zero.mpr hκ
  have h0c : 0 < (starRingEnd ℂ ρ).re := by rwa [Complex.conj_re]
  have h1c : (starRingEnd ℂ ρ).re < 1 := by rwa [Complex.conj_re]
  refine ⟨hkc, ?_⟩
  obtain ⟨-, -, -, hmix, -⟩ := native_profile_spectral_norms hzc h0c h1c hκc
  have hU := (hmix ρ hz h0 h1 (Or.inl hκ)).2.2
  rw [hkc, sub_self, zero_mul] at hU
  have hk0 : starRingEnd ℂ (spectralKappa ρ) ≠ 0 := by
    intro h; apply hκ; rw [← Complex.conj_conj (spectralKappa ρ), h, map_zero, Complex.zero_im]
  have := mul_left_cancel₀ hk0 (sub_eq_zero.mp hU.symm)
  exact this

/-- At a critical-line zero the supporting undivided identity holds with multiplier ξ² - (Im ρ)²,
and both of its sides vanish at ξ = Im ρ (the quotient is not formed there). -/
theorem FullAudit20_expected_critical_line_undivided {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hre : ρ.re = 1 / 2) :
    (∀ ξ : ℝ, (((ξ ^ 2 - ρ.im ^ 2 : ℝ)) : ℂ) * logFourier (logUnitary (zeroProfile ρ)) ξ =
      spectralKappa ρ * riemannZeta (1 / 2 + ξ * I)) ∧
    spectralKappa ρ * riemannZeta (1 / 2 + ρ.im * I) = 0 := by
  have hρ : ρ = (1 / 2 : ℂ) + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hk : spectralKappa ρ = ((1 / 4 + ρ.im ^ 2 : ℝ) : ℂ) := by
    rw [spectralKappa]
    conv_lhs => rw [hρ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  refine ⟨fun ξ => ?_, ?_⟩
  · have h := logFourier_zeroProfile_undivided hz h0 h1 ξ
    rw [hk, spectralEnergy] at h
    rw [hk, ← h]
    push_cast; ring
  · rw [← hρ, hz, mul_zero]

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedNearGap.lean; SHA256 e6e20f293af961a40dbd26f944fa56fe1f7247c43acbf656c9afed3b53981e76 -/
section

/- Independent HT2 consumers for the actual locally finite Jordan measure.
The controlled weak limit and both CT1 family/normalized-limit roots remain OPEN. -/
noncomputable section
open Set MeasureTheory
open scoped SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem expected_near_gap_mass_bound (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth)
    (hself : 𝓕 (nu.distributionOfLinearGrowth hnu)=nu.distributionOfLinearGrowth hnu)
    (a R d : ℝ) (ha : 0<a) (ha1 : a≤1)
    (hgapPos : nu.positive (Ioo (-a) a)=0)
    (hgapNeg : nu.negative (Ioo (-a) a)=0)
    (hoff : nu.negative (Set.range (fun n : ℤ => (n:ℝ)))ᶜ=0)
    (hR : 1≤R) (hd : 0<d) (hdhalf : d≤1/2) :
    nu.negative {x : ℝ | |x|≤R ∧ d≤Metric.infDist x (Set.range (fun n : ℤ => (n:ℝ)))}=0 ∧
    nu.positive.real {x : ℝ | |x|≤R ∧ d≤Metric.infDist x (Set.range (fun n : ℤ => (n:ℝ)))}≤
      (Real.pi^2*R^2/(4*d^2))*(1-a)*(nu.positive+nu.negative).real (Icc (-1) 1) := by
  exact near_gap_mass_bound nu hnu hself ha ha1 ⟨hgapPos,hgapNeg⟩ hoff hR hd hdhalf

theorem FullAudit21_expected_common_linear_constant (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    (C a R d : ℝ) (_hC : 0≤C)
    (hlinear : ∀ S : ℝ, 0≤S → nu.totalVariation.real (Icc (-S) S)≤C*(1+S))
    (ha : 0<a) (ha1 : a≤1) (hgap : hasNearGap nu a)
    (hoff : nu.OffLatticeNonnegative) (hR : 1≤R) (hd : 0<d) (hdhalf : d≤1/2) :
    nu.positive.real (signedBudgetRegion R d)≤
      (Real.pi^2*R^2*C/(2*d^2))*(1-a) := by
  have hlocal : nu.totalVariation.real (Icc (-1) 1)≤2*C := by
    simpa only [show (1:ℝ)+1=2 by norm_num,mul_comm] using hlinear 1 (by norm_num)
  calc
    _ ≤ (Real.pi^2*R^2/(4*d^2))*(1-a)*nu.totalVariation.real (Icc (-1) 1) :=
      (near_gap_mass_bound nu hnu hself ha ha1 hgap hoff hR hd hdhalf).2
    _ ≤ (Real.pi^2*R^2/(4*d^2))*(1-a)*(2*C) :=
      mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = _ := by field_simp; ring

theorem FullAudit21_expected_critical_gap_zero_region (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    (hgap : nu.HasUnitGap) (hoff : nu.OffLatticeNonnegative)
    (R d : ℝ) (hR : 1≤R) (hd : 0<d) (hdhalf : d≤1/2) :
    nu.negative (signedBudgetRegion R d)=0 ∧
    nu.positive.real (signedBudgetRegion R d)=0 := by
  have h := near_gap_mass_bound nu hnu hself (a:=1) (by norm_num) le_rfl hgap hoff hR hd hdhalf
  refine ⟨h.1,le_antisymm ?_ (by positivity)⟩
  simpa only [sub_self,mul_zero,zero_mul] using h.2

theorem FullAudit21_expected_half_distance_endpoint (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    (a R : ℝ) (ha : 0<a) (ha1 : a≤1) (hgap : hasNearGap nu a)
    (hoff : nu.OffLatticeNonnegative) (hR : 1≤R) :
    nu.positive.real (signedBudgetRegion R (1/2))≤
      (Real.pi^2*R^2)*(1-a)*nu.totalVariation.real (Icc (-1) 1) := by
  have h := (near_gap_mass_bound nu hnu hself ha ha1 hgap hoff hR
    (by norm_num : (0:ℝ)<1/2) le_rfl).2
  norm_num only [show (4:ℝ)*(1/2)^2=1 by norm_num,div_one] at h
  exact h

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedNearGapLimit.lean; SHA256 dbd1ba447e025ceea3797e6843ba741365d404ddf3392bae47d665caa39405be -/
section

/- Independent consumers for the original R1-HT2 root
`Zeta23.OPICAFollowup.near_gap_controlled_limit_zero`.

Every predicate of the source statement (common linear variation bound, near
gap, off-lattice nonnegativity, canonical Fourier self-duality) is written out
explicitly below. The actual-domain consumer instantiates the root on the
genuine CT1 Jordan pairs at L_n = log 2/(n+2), discharging every premise from
the CT1 constructors, and checks that each term is a nonzero distribution, so
the limit is not vacuous. The unit-gap boundary consumer recovers the parent
sharp-gap separator on Schwartz tests. The CT1 normalized nonmeasure limit,
aggregate export and full release remain OPEN. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-- Complete expanded type of the controlled-limit root. -/
theorem expected_near_gap_controlled_limit_zero
    (nu : ℕ → LocallyFiniteSignedMeasure) (C : ℝ) (hC0 : 0 ≤ C)
    (hlinear : ∀ n, ∀ R : ℝ, 0 ≤ R →
      ((nu n).positive + (nu n).negative).real (Icc (-R) R) ≤ C * (1 + R))
    (hnu : ∀ n, (nu n).HasLinearGrowth)
    (hself : ∀ n, 𝓕 ((nu n).distributionOfLinearGrowth (hnu n)) =
      (nu n).distributionOfLinearGrowth (hnu n))
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (hgapPos : ∀ n, (nu n).positive (Ioo (-a n) (a n)) = 0)
    (hgapNeg : ∀ n, (nu n).negative (Ioo (-a n) (a n)) = 0)
    (hoff : ∀ n, (nu n).negative (Set.range (fun k : ℤ => (k : ℝ)))ᶜ = 0)
    (hlim : Tendsto a atTop (𝓝 1)) (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (nu n).distributionOfLinearGrowth (hnu n) φ) atTop (𝓝 0) :=
  near_gap_controlled_limit_zero nu C (fun n => ⟨hC0, hlinear n⟩) hself a ha ha1
    (fun n => ⟨hgapPos n, hgapNeg n⟩) hoff hlim φ

/-- The explicit single-measure estimate behind the limit, restated. -/
theorem FullAudit22_expected_near_gap_schwartz_pairing_bound (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth)
    (hself : 𝓕 (nu.distributionOfLinearGrowth hnu) = nu.distributionOfLinearGrowth hnu)
    (a C : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (hgapPos : nu.positive (Ioo (-a) a) = 0) (hgapNeg : nu.negative (Ioo (-a) a) = 0)
    (hoff : nu.negative (Set.range (fun k : ℤ => (k : ℝ)))ᶜ = 0) (hC0 : 0 ≤ C)
    (hlinear : ∀ R : ℝ, 0 ≤ R → (nu.positive + nu.negative).real (Icc (-R) R) ≤ C * (1 + R))
    (φ : SchwartzMap ℝ ℂ) (N : ℕ) (hN : 1 ≤ N) (d : ℝ) (hd : 0 < d) (hd2 : d ≤ 1 / 2) :
    ‖nu.distributionOfLinearGrowth hnu φ‖ ≤
      (1 - a) * (2 * C * ((2 * N + 3) * SchwartzMap.seminorm ℝ 0 0 φ)) +
      2 * SchwartzMap.seminorm ℝ 0 0 (SchwartzMap.derivCLM ℝ ℂ φ) * d * (C * (1 + N)) +
      2 * SchwartzMap.seminorm ℝ 0 0 φ *
        ((Real.pi ^ 2 * (N : ℝ) ^ 2 / (4 * d ^ 2)) * (1 - a) * (2 * C)) +
      4 * C * (9 * SchwartzMap.seminorm ℝ 3 0 φ + 8 * SchwartzMap.seminorm ℝ 0 0 φ) /
        (N : ℝ) ^ 2 :=
  nearGap_schwartz_pairing_bound nu hnu hself ha ha1 ⟨hgapPos, hgapNeg⟩ hoff
    ⟨hC0, hlinear⟩ φ hN hd hd2

/-- Actual-domain consumer: the genuine CT1 family at L_n = log 2/(n+2).
Every premise of the root is discharged by the CT1 constructors. -/
theorem FullAudit22_expected_CT1_controlled_limit (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n : ℕ => nearGapCombDistribution (Real.log 2 / ((n : ℝ) + 2)) φ)
      atTop (𝓝 0) := by
  set L : ℕ → ℝ := fun n => Real.log 2 / ((n : ℝ) + 2) with hLdef
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL (n : ℕ) : 0 < L n := by simp only [hLdef]; positivity
  have hu (n : ℕ) : L n < Real.log 2 := by
    simp only [hLdef]
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hlim : Tendsto L atTop (𝓝 0) := by
    have h := tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
    have hshift : Tendsto (fun n : ℕ => Real.log 2 / ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
      h.comp (tendsto_add_atTop_nat 2)
    refine hshift.congr (fun n => ?_)
    simp only [hLdef]
    push_cast
    ring
  have hfam (n : ℕ) := dilation_near_gap_family (L n) (hL n) (hu n)
  have ha : Tendsto (fun n => Real.exp (-L n)) atTop (𝓝 1) := by
    have hneg : Tendsto (fun n => -L n) atTop (𝓝 0) := by simpa using hlim.neg
    simpa [Function.comp_def] using (Real.continuous_exp.tendsto 0).comp hneg
  exact near_gap_controlled_limit_zero (fun n => nearGapCombFamily (L n)) 18
    (fun n => (hfam n).2.2.1) (fun n => (hfam n).2.2.2.1)
    (fun n => Real.exp (-L n)) (fun n => Real.exp_pos _)
    (fun n => ((hfam n).2.2.2.2.2.2.1).2.le) (fun n => (hfam n).2.2.2.2.2.1)
    (fun n => (hfam n).2.2.2.2.2.2.2.1) ha φ

/-- The family-level domain theorem, restated with explicit parameter domain. -/
theorem FullAudit22_expected_CT1_family_controlled_limit (L : ℕ → ℝ) (hL : ∀ n, 0 < L n)
    (hu : ∀ n, L n < Real.log 2) (hlim : Tendsto L atTop (𝓝 0))
    (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n =>
        (nearGapCombFamily (L n)).distributionOfLinearGrowth (nearGapCombFamily_growth (L n)) φ)
      atTop (𝓝 0) :=
  nearGapCombFamily_controlled_limit L hL hu hlim φ

/-- Non-vacuity: every term of the actual sequence is a nonzero distribution
(faithfulness of the parent Jordan-pair distribution map), so the controlled
limit is a genuine cancellation statement, not a statement about zero terms. -/
theorem expected_dilation_near_gap_family (L : ℝ) (hL : 0 < L) (hu : L < Real.log 2) :
    nearGapCombDistribution L ≠ 0 := by
  intro hzero
  have h := LocallyFiniteSignedMeasure.parts_eq_zero_of_distribution_eq_zero
    (nearGapCombFamily L) (nearGapCombFamily_growth L) hzero
  exact (dilation_near_gap_family L hL hu).2.2.2.2.2.2.2.2.2.1 h.1

/-- Boundary consumer a_n = 1: the constant sequence recovers the parent
unit-gap separator on every Schwartz test. -/
theorem FullAudit22_expected_unit_gap_zero_pairing (nu : LocallyFiniteSignedMeasure) (C : ℝ)
    (hC : CommonLinearMassBound C nu.totalVariation)
    (hself : nu.FourierSelfdual hC.linearGrowth) (hgap : nu.HasUnitGap)
    (hoff : nu.OffLatticeNonnegative) (φ : SchwartzMap ℝ ℂ) :
    nu.distributionOfLinearGrowth hC.linearGrowth φ = 0 := by
  have h := near_gap_controlled_limit_zero (fun _ => nu) C (fun _ => hC) (fun _ => hself)
    (fun _ => 1) (fun _ => one_pos) (fun _ => le_rfl) (fun _ => hgap) (fun _ => hoff)
    tendsto_const_nhds φ
  exact tendsto_const_nhds_iff.mp h

/-- Cross-check of the boundary consumer against the parent theorem. -/
theorem FullAudit22_expected_unit_gap_matches_parent (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu) (hgap : nu.HasUnitGap)
    (hoff : nu.OffLatticeNonnegative) :
    nu.positive = 0 ∧ nu.negative = 0 :=
  signed_sharp_gap_separator nu hnu hself hgap hoff

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedNormalizedLimit.lean; SHA256 e833dad08f5c3a1fd477ab56f65db12d984fa51e18fd638d2b2aeddae77f9187 -/
section

/- Independent consumers for the original R1-CT1 root
`Zeta23.OPICAFollowup.dilation_normalized_limit_not_measure`.

The limit is restated existentially and pinned down pointwise by its explicit
lattice formula, so no source definition can hide a different object. The
domain consumer uses the paper's explicit three-comb pairing
D_L + D_(-L) - 2cosh(L/2) D_0 on 0 < L < log 2. Boundary consumers check the
cancelled origin coefficient, the coefficient 2n² of a quadratic bump at every
integer, and the failure of any common normalized variation constant. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-- Explicit lattice value Σ_n (n² φ''(n) + 2n φ'(n)). -/
def FullAudit23_latticeValue (φ : SchwartzMap ℝ ℂ) : ℂ :=
  ∑' n : ℤ, ((n : ℂ) ^ 2 * deriv (deriv φ) n + 2 * n * deriv φ n)

/-- Complete semantic restatement: a tempered distribution exists that is the
𝓢'-limit of ν_L/L², equals the explicit lattice value on every test, is the
pointwise sum of n² δ_n'' − 2n δ_n', is nonzero, is not of order zero at any
nonzero integer and is not given by a locally finite Jordan pair. -/
theorem expected_dilation_normalized_limit_not_measure :
    ∃ T : TemperedDistribution ℝ ℂ,
      Tendsto (fun L : ℝ => ((L : ℂ) ^ 2)⁻¹ •
          (nearGapCombFamily L).distributionOfLinearGrowth (nearGapCombFamily_growth L))
        (𝓝[≠] 0) (𝓝 T) ∧
      (∀ φ : SchwartzMap ℝ ℂ, T φ = FullAudit23_latticeValue φ) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        HasSum (fun n : ℤ => ((n : ℂ) ^ 2 • TemperedDistribution.derivCLM ℂ
            (TemperedDistribution.derivCLM ℂ (TemperedDistribution.delta (n : ℝ))) -
          (2 * (n : ℂ)) • TemperedDistribution.derivCLM ℂ
            (TemperedDistribution.delta (n : ℝ))) φ) (T φ)) ∧
      T ≠ 0 ∧
      (∀ n : ℤ, n ≠ 0 → ¬ ∃ C : ℝ, ∀ φ : SchwartzMap ℝ ℂ,
        tsupport φ ⊆ Icc ((n : ℝ) - 1 / 2) (n + 1 / 2) →
          ‖T φ‖ ≤ C * SchwartzMap.seminorm ℝ 0 0 φ) ∧
      (¬ ∃ μ : LocallyFiniteSignedMeasure, ∀ φ : SchwartzMap ℝ ℂ,
        (∫ x, φ x ∂μ.positive) - (∫ x, φ x ∂μ.negative) = T φ) := by
  obtain ⟨h1, -, h3, -, h5, h6, h7, -⟩ := dilation_normalized_limit_not_measure
  exact ⟨ct1NormalizedLimit, h1, ct1NormalizedLimit_apply, h3, h5, h6, h7⟩

/-- The paper's domain 0 < L < log 2 as L → 0⁺, on the explicit three-comb
pairing e^{L/2}Σφ(e^L n) + e^{-L/2}Σφ(e^{-L} n) − 2cosh(L/2)Σφ(n). -/
theorem FullAudit23_expected_three_comb_normalized_limit (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun L : ℝ =>
        ((Real.exp (L / 2) : ℂ) * ∑' n : ℤ, φ (Real.exp L * n) +
          (Real.exp (-L / 2) : ℂ) * ∑' n : ℤ, φ (Real.exp (-L) * n) -
          ((2 * Real.cosh (L / 2) : ℝ) : ℂ) * ∑' n : ℤ, φ n) / (L : ℂ) ^ 2)
      (𝓝[>] 0) (𝓝 (FullAudit23_latticeValue φ)) := by
  have h := (dilation_normalized_limit_not_measure.2.1 φ).mono_left
    (nhdsWithin_mono (0 : ℝ) (fun x hx => ne_of_gt hx))
  refine h.congr (fun L => ?_)
  congr 1
  rw [nearGapCombDistribution_eq_explicit]
  change dilatedCombDistribution L φ + dilatedCombDistribution (-L) φ -
    ((2 * Real.cosh (L / 2) : ℝ) : ℂ) • dilatedCombDistribution 0 φ = _
  rw [dilatedCombDistribution_apply, dilatedCombDistribution_apply,
    dilatedCombDistribution_apply, smul_eq_mul]
  simp only [Real.exp_zero, zero_div, Complex.ofReal_one, one_mul, neg_div]

/-- The cancelled origin coefficient: tests near 0 see nothing. -/
theorem FullAudit23_expected_origin_coefficient_zero (φ : SchwartzMap ℝ ℂ)
    (hφ : tsupport φ ⊆ Icc (-(1 / 2) : ℝ) (1 / 2)) :
    ct1NormalizedLimit φ = 0 := by
  have h := dilation_normalized_limit_not_measure.2.2.2.1 0 φ (by simpa using hφ)
  simpa using h

/-- Every integer n carries the nonzero second-derivative coefficient n²:
a quadratic bump at n has limit value 2n². -/
theorem FullAudit23_expected_integer_coefficients (n : ℤ) (hn : n ≠ 0) :
    ∃ φ : SchwartzMap ℝ ℂ, tsupport φ ⊆ Icc ((n : ℝ) - 1 / 2) (n + 1 / 2) ∧
      ct1NormalizedLimit φ = 2 * (n : ℂ) ^ 2 ∧ ct1NormalizedLimit φ ≠ 0 := by
  refine ⟨ct1BumpTest n (ε := 1 / 4) (by norm_num),
    ct1BumpTest_tsupport_Icc n (by norm_num) (by norm_num),
    ct1NormalizedLimit_bumpTest n (by norm_num) (by norm_num), ?_⟩
  rw [ct1NormalizedLimit_bumpTest n (by norm_num) (by norm_num)]
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  exact mul_ne_zero two_ne_zero (pow_ne_zero 2 this)

/-- No common constant bounds the normalized variation near 1 on the CT1
domain: the HT2 common-growth premise genuinely fails after normalization. -/
theorem FullAudit23_expected_no_common_normalized_variation :
    ¬ ∃ C : ℝ, ∀ L : ℝ, 0 < L → L < Real.log 2 →
      (nearGapCombFamily L).totalVariation.real (Icc (1 / 2) (3 / 2)) / L ^ 2 ≤ C := by
  rintro ⟨C, hC⟩
  have hT := dilation_normalized_limit_not_measure.2.2.2.2.2.2.2
  have hev := hT.eventually (eventually_gt_atTop C)
  have hdom : ∀ᶠ L in 𝓝[>] (0 : ℝ), L ∈ Ioo 0 (Real.log 2) :=
    Ioo_mem_nhdsGT (Real.log_pos (by norm_num))
  obtain ⟨L, hL1, hL2⟩ := (hev.and hdom).exists
  linarith [hC L hL2.1 hL2.2]

/-- Self-duality of the limit, restated with the canonical Fourier transform
evaluated on tests: T(𝓕φ) = T(φ). -/
theorem FullAudit23_expected_normalized_limit_selfdual (φ : SchwartzMap ℝ ℂ) :
    ct1NormalizedLimit (𝓕 φ) = ct1NormalizedLimit φ := by
  have h := ct1NormalizedLimit_fourier_selfdual
  calc ct1NormalizedLimit (𝓕 φ) = (𝓕 ct1NormalizedLimit) φ := rfl
    _ = ct1NormalizedLimit φ := by rw [h]

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedPhysicalRates.lean; SHA256 0adcee1919d6a4bc897a7c9bd0077e772c6faf3dce8e6c7a3ae93bebc1b256c1 -/
section

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
open Zeta23 Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem expected_native_fixed_source_window_rate (d : ℕ) (C : ℝ) (C_gt_one : 1 < C) :
    Tendsto (fun T : ℝ =>
      Real.log (1+(∫ t : ℝ in Icc (T-C*Real.log T) T, |primeFieldFamily d t|^2))/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) :=
  native_fixed_source_window_rate d C C_gt_one

theorem expected_native_slow_source_window_rate (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop)
    (order : ℕ → ℕ)
    (slow : Tendsto (fun n => (order n : ℝ)*Real.log ((order n : ℝ)+2)/time n) atTop (𝓝 0))
    (C : ℝ) (C_gt_one : 1 < C) :
    Tendsto (fun n =>
      Real.log (1+(∫ t : ℝ in Icc (time n-C*Real.log (time n)) (time n),
        |primeFieldFamily (order n) t|^2))/(2*time n)) atTop (𝓝 nativeZeroDisplacementSup) :=
  native_slow_source_window_rate time cofinal order slow C C_gt_one

theorem FullAudit24_expected_order_zero (C : ℝ) (C_gt_one : 1 < C) :
    Tendsto (fun T : ℝ =>
      Real.log (1+(∫ t : ℝ in Icc (T-C*Real.log T) T, |primeFieldFamily 0 t|^2))/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) :=
  native_fixed_source_window_rate 0 C C_gt_one

theorem FullAudit24_expected_nonpositive_finite_prefix :
    Tendsto (fun n : ℕ =>
      Real.log (1+(∫ t : ℝ in Icc (((n : ℝ)-5)-2*Real.log ((n : ℝ)-5)) ((n : ℝ)-5),
        |primeFieldFamily 0 t|^2))/(2*((n : ℝ)-5))) atTop (𝓝 nativeZeroDisplacementSup) := by
  have ht : Tendsto (fun n : ℕ => (n : ℝ)-5) atTop atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right atTop (-5 : ℝ) tendsto_natCast_atTop_atTop)
  have hs : Tendsto (fun n : ℕ => ((0 : ℕ) : ℝ)*Real.log (((0 : ℕ) : ℝ)+2)/((n : ℝ)-5))
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _n : ℕ => (0 : ℝ)) atTop (𝓝 0))
  exact native_slow_source_window_rate (fun n => (n : ℝ)-5) ht (fun _ => 0) hs 2 (by norm_num)

theorem FullAudit24_expected_both_source_factor_log_signs (rho : zetaZeroConfig.carrier)
    (right_zero : 1/2 < (rho : ℂ).re) :
    ∃ Cp : ℝ, 0 < Cp ∧ ∀ d : ℕ,
      |Real.log ‖sourceFamilyLaplace d ((rho : ℂ)-1/2)‖| ≤ Cp*((d : ℝ)+1) :=
  NativeWindowProof.sourceFactor_abs_log_bound rho right_zero

theorem FullAudit24_expected_literal_rate_definition (d : ℕ) (C T : ℝ) :
    nativeWindowLogRate d C T =
      Real.log (1+(∫ t : ℝ in Icc (T-C*Real.log T) T, |primeFieldFamily d t|^2))/(2*T) := rfl

theorem FullAudit24_expected_zero_supremum_case (d : ℕ) (C : ℝ) (C_gt_one : 1 < C)
    (theta_zero : nativeZeroDisplacementSup=0) :
    Tendsto (fun T : ℝ =>
      Real.log (1+(∫ t : ℝ in Icc (T-C*Real.log T) T, |primeFieldFamily d t|^2))/(2*T))
      atTop (𝓝 0) := by
  simpa only [theta_zero] using native_fixed_source_window_rate d C C_gt_one

theorem FullAudit24_zero_order_cost_correction_control :
    ¬ (∀ d : ℕ, ((d : ℝ)+1)*Real.log ((d : ℝ)+2) ≤
      2*((d : ℝ)*Real.log ((d : ℝ)+2))) := by
  intro h
  have hz := h 0
  norm_num at hz
  exact (not_le_of_gt (Real.log_pos (by norm_num : (1 : ℝ)<2))) hz

theorem FullAudit24_upper_rate_does_not_force_zero_control {T : ℝ} (T_pos : 0 < T) :
    Real.log (1+(Real.exp (2*T)-1))/(2*T)=1 := by
  rw [show 1+(Real.exp (2*T)-1)=Real.exp (2*T) by ring,Real.log_exp]
  exact div_self (by positivity)

end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedSampleSign.lean; SHA256 9015dee14c0c55719b861b7d7604db0119bb43c3723fef216da512d12a3dcda7 -/
section

/- Supporting physical consumer for the raw-sample sign already stated after (F2.5)
   in the frozen paper. This is not an additional primary root or a new originality
   claim. The arithmetic sample defect differs from normalizationBrho. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit25_form_self (ρ : ℂ) :
    profileFormGram ρ ρ = ((logForm (zeroProfileDeriv ρ) : ℝ) : ℂ) := by
  rw [profileFormGram, logForm, ← integral_complex_ofReal]
  refine integral_congr_ae ?_
  filter_upwards [deriv_zeroProfile_ae ρ] with x hx
  rw [hx]
  calc
    (x : ℂ) ^ 2 * zeroProfileDeriv ρ x * starRingEnd ℂ (zeroProfileDeriv ρ x) =
        (x : ℂ) ^ 2 * (zeroProfileDeriv ρ x * starRingEnd ℂ (zeroProfileDeriv ρ x)) := by ring
    _ = _ := by rw [Complex.mul_conj']; push_cast; rfl

/-- A genuine necessary restriction on the sample at every hypothetical nonreal-κ zero.
It does not assert an independent reality/sign restriction on that arithmetic sample. -/
theorem FullAudit25_sample_im_ratio {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hκ : (spectralKappa ρ).im ≠ 0) :
    (profileSampleDefect ρ).im / (spectralKappa ρ).im =
      logForm (zeroProfileDeriv ρ) / ‖spectralKappa ρ‖ ^ 2 ∧
    0 < (profileSampleDefect ρ).im / (spectralKappa ρ).im ∧
    (profileSampleDefect ρ).im ≠ 0 := by
  let κ := spectralKappa ρ
  let b := profileSampleDefect ρ
  let N := ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2
  let Q := logForm (zeroProfileDeriv ρ)
  have hG : (Q : ℂ) = κ * ((N : ℂ) + starRingEnd ℂ b) := by
    simpa only [κ, b, N, Q, FullAudit25_form_self, profileGram_self] using
      (gram_identity hz h0 h1 hz h0 h1)
  have hre := congrArg Complex.re hG
  have him := congrArg Complex.im hG
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.conj_re, Complex.conj_im,
    zero_add] at hre him
  have hn : ‖κ‖ ^ 2 = κ.re ^ 2 + κ.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    ring
  have he : ‖κ‖ ^ 2 * b.im = Q * κ.im := by
    rw [hn]
    linear_combination κ.re * him - κ.im * hre
  have hk0 : κ ≠ 0 := by
    intro he
    apply hκ
    change κ.im = 0
    rw [he, Complex.zero_im]
  have hnorm : 0 < ‖κ‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hk0)
  have hN : 0 < N := integral_norm_sq_pos hz h0 h1
  have hQ : 0 < Q := by
    have heq := (zeroProfile_mem_logFormDomain hz h0 h1).logForm_eq.2
    have hi : 0 ≤ ∫ t, ‖logUnitaryDeriv (zeroProfile ρ) (zeroProfileDeriv ρ) t‖ ^ 2 :=
      integral_nonneg fun t => sq_nonneg _
    dsimp only [Q]
    rw [heq]
    dsimp only [N] at hN
    linarith
  have hratio : b.im / κ.im = Q / ‖κ‖ ^ 2 := by
    apply (div_eq_div_iff hκ (ne_of_gt hnorm)).mpr
    nlinarith [he]
  have hpos : 0 < b.im / κ.im := by rw [hratio]; exact div_pos hQ hnorm
  refine ⟨hratio, hpos, ?_⟩
  intro hb0
  rw [hb0, zero_div] at hpos
  exact (lt_irrefl 0) hpos

/-- An independently established real sample would exclude an off-line zero.
The reality hypothesis is explicit and is not established here. -/
theorem FullAudit25_real_sample_implies_on_line {ρ : ℂ} (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (him : ρ.im ≠ 0)
    (hb : (profileSampleDefect ρ).im = 0) : ρ.re = 1 / 2 := by
  by_contra hre
  have hk : (spectralKappa ρ).im ≠ 0 := by
    have he : (spectralKappa ρ).im = (1 - 2 * ρ.re) * ρ.im := by
      simp only [spectralKappa, Complex.mul_im, Complex.sub_re, Complex.sub_im,
        Complex.one_re, Complex.one_im]
      ring
    rw [he]
    exact mul_ne_zero (by intro he; apply hre; linarith) him
  exact (FullAudit25_sample_im_ratio hz h0 h1 hk).2.2 hb

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedSamplingCompatibility.lean; SHA256 6cbfca4ac5b49becffd45a81a380ef3e4a49a6b9fbe19f134f28a897bf0011e6 -/
section

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.native_sampling_gram_identity`
and `Zeta23.OPICAFollowup.native_sampling_form_positive` (R2-S2).

Definition audits pin the linear-first pairings N_ij = ∫_0^∞ h_i conj h_j and
Q_ij = ∫_0^∞ x² h_i' conj h_j' and the sample defect b_i = Σ_{n ≥ 1} h_i(n) - 1/2. Both roots are
restated in full. Domain consumers check:
- the diagonal: N_ii > 0 is real, Q_ii - N_ii/4 is real and nonnegative;
- at a zero on the critical line (κ real) the self-pairing forces b real;
- conjugate coincidence: for an actual zero ρ, conj ρ is an actual zero with κ(conj ρ) = conj κ(ρ),
  the divided identity is unavailable, and the retained undivided identity gives
  b_ρ = conj b_(conj ρ);
- the finite-cell pairing and the generic Gram positivity are construction-level: they hold at
  the non-zero parameters ρ = 3/4, σ = 2/3. The zero-dependent roots need an actual zero, which
  Mathlib cannot exhibit;
- the finite countercontrol is non-vacuous: with A = 1, g = 1 and the nonreal parameter κ = i,
  N_00 = 1/2 > 0 and the identities (S2.1) hold. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology ComplexConjugate ComplexOrder
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit26_audit_profileGram (ρ σ : ℂ) :
    profileGram ρ σ = ∫ x in Ioi (0 : ℝ), zeroProfile ρ x * conj (zeroProfile σ x) := rfl

theorem FullAudit26_audit_profileFormGram (ρ σ : ℂ) : profileFormGram ρ σ =
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ 2 * deriv (zeroProfile ρ) x * conj (deriv (zeroProfile σ) x) := rfl

theorem FullAudit26_audit_profileSampleDefect (ρ : ℂ) :
    profileSampleDefect ρ = (∑' n : ℕ, zeroProfile ρ (n + 1)) - 1 / 2 := rfl

/-! ### Restated roots -/

theorem expected_native_sampling_gram_identity {ι : Type*} (ρ : ι → ℂ)
    (hz : ∀ i, riemannZeta (ρ i) = 0) (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) :
    (∀ i, Summable (fun n : ℕ => zeroProfile (ρ i) (n + 1))) ∧
    (∀ i j, IntegrableOn (fun x => zeroProfile (ρ i) x * conj (zeroProfile (ρ j) x)) (Ioi 0)) ∧
    (∀ i j, IntegrableOn (fun x : ℝ => (x : ℂ) ^ 2 * deriv (zeroProfile (ρ i)) x *
      conj (deriv (zeroProfile (ρ j)) x)) (Ioi 0)) ∧
    (∀ i, ∫ x in Ioi (0 : ℝ), zeroProfile (ρ i) x = 1 / 2) ∧
    (∀ i j (N : ℕ), ∫ x in (0 : ℝ)..((N : ℝ) + 1),
      (x : ℂ) ^ 2 * zeroProfileDeriv (ρ i) x * conj (zeroProfileDeriv (ρ j) x) =
        spectralKappa (ρ i) * ((∫ x in (0 : ℝ)..((N : ℝ) + 1),
          (zeroProfile (ρ i) x - 1) * conj (zeroProfile (ρ j) x)) +
            ∑ m ∈ Finset.range N, conj (zeroProfile (ρ j) (m + 1))) +
        (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv (ρ i) N ((N : ℝ) + 1) / normalizationBrho (ρ i)) *
          conj (zeroProfile (ρ j) ((N : ℝ) + 1))) ∧
    (∀ i j, Tendsto (fun N : ℕ => (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 *
      -(srhoCellDeriv (ρ i) N ((N : ℝ) + 1) / normalizationBrho (ρ i)) *
        conj (zeroProfile (ρ j) ((N : ℝ) + 1))) atTop (𝓝 0)) ∧
    (∀ i j, profileFormGram (ρ i) (ρ j) =
      spectralKappa (ρ i) * (profileGram (ρ i) (ρ j) + conj (profileSampleDefect (ρ j)))) ∧
    (∀ i j, profileFormGram (ρ i) (ρ j) =
      conj (spectralKappa (ρ j)) * (profileGram (ρ i) (ρ j) + profileSampleDefect (ρ i))) :=
  native_sampling_gram_identity ρ hz h0 h1

theorem expected_native_sampling_form_positive {ι : Type*} [Fintype ι] (ρ : ι → ℂ)
    (hz : ∀ i, riemannZeta (ρ i) = 0) (h0 : ∀ i, 0 < (ρ i).re) (h1 : ∀ i, (ρ i).re < 1) :
    (Matrix.of fun i j => profileGram (ρ i) (ρ j)).PosSemidef ∧
    (Matrix.of fun i j => profileFormGram (ρ i) (ρ j)).PosSemidef ∧
    (Matrix.of fun i j => profileFormGram (ρ i) (ρ j) - profileGram (ρ i) (ρ j) / 4).PosSemidef ∧
    (∀ i j, (spectralKappa (ρ i) - conj (spectralKappa (ρ j))) * profileGram (ρ i) (ρ j) =
      conj (spectralKappa (ρ j)) * profileSampleDefect (ρ i) -
        spectralKappa (ρ i) * conj (profileSampleDefect (ρ j))) ∧
    (∀ i j, spectralKappa (ρ i) - conj (spectralKappa (ρ j)) ≠ 0 →
      profileGram (ρ i) (ρ j) / (spectralKappa (ρ i) * conj (spectralKappa (ρ j))) =
        (profileSampleDefect (ρ i) / spectralKappa (ρ i) -
          conj (profileSampleDefect (ρ j) / spectralKappa (ρ j))) /
            (spectralKappa (ρ i) - conj (spectralKappa (ρ j)))) ∧
    (∀ i, (spectralKappa (ρ i)).im ≠ 0 →
      (profileSampleDefect (ρ i) / spectralKappa (ρ i)).im / (spectralKappa (ρ i)).im =
        (∫ x in Ioi (0 : ℝ), ‖zeroProfile (ρ i) x‖ ^ 2) / ‖spectralKappa (ρ i)‖ ^ 2 ∧
      0 < ∫ x in Ioi (0 : ℝ), ‖zeroProfile (ρ i) x‖ ^ 2) :=
  native_sampling_form_positive ρ hz h0 h1

/-! ### Domain consumers -/

/-- The diagonal of the actual Gram data: N_ii > 0 is real and Q_ii - N_ii/4 ≥ 0. -/
theorem FullAudit26_expected_diagonal (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    0 < (profileGram ρ ρ).re ∧ (profileGram ρ ρ).im = 0 ∧
      0 ≤ profileFormGram ρ ρ - profileGram ρ ρ / 4 := by
  obtain ⟨-, -, hPSD, -⟩ := native_sampling_form_positive (fun _ : Unit => ρ) (fun _ => hz)
    (fun _ => h0) (fun _ => h1)
  have hN : profileGram ρ ρ = ((∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 : ℝ) : ℂ) := by
    rw [profileGram, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun x => by
      simp only; push_cast; rw [Complex.mul_conj'])
  have hpos := (native_sampling_form_positive (fun _ : Unit => ρ) (fun _ => hz) (fun _ => h0)
    (fun _ => h1)).2.2.2.2.2
  refine ⟨?_, by rw [hN]; simp, ?_⟩
  · have hint : 0 < ∫ x in Ioi (0 : ℝ), ‖zeroProfile ρ x‖ ^ 2 := by
      by_cases hk : (spectralKappa ρ).im = 0
      · -- independent of the imaginary part: h = 1 on (0, 1]
        have hI : IntegrableOn (fun x => ‖zeroProfile ρ x‖ ^ 2) (Ioi 0) :=
          ((memLp_two_zeroProfile hz h0 h1).restrict (Ioi 0)).integrable_norm_pow (p := 2) two_ne_zero
        have h1' : (∫ x in Ioc (0 : ℝ) 1, ‖zeroProfile ρ x‖ ^ 2) = 1 := by
          rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (1 : ℝ)) fun x hx => by
            simp only [zeroProfile_eq_one ρ (abs_le.mpr ⟨by linarith [hx.1], hx.2⟩), norm_one, one_pow]]
          simp
        have hle := setIntegral_mono_set hI (Eventually.of_forall fun x => sq_nonneg ‖zeroProfile ρ x‖)
          (Ioc_subset_Ioi_self : Ioc (0 : ℝ) 1 ⊆ Ioi 0).eventuallyLE
        linarith
      · exact (hpos () hk).2
    rw [hN]; simpa using hint
  · have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hPSD).2 (fun _ => 1)
    simpa [dotProduct, Matrix.mulVec] using this

/-- On the critical line κ is real and the self-pairing forces the sample defect to be real. -/
theorem FullAudit26_expected_online_sample_real (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hk : (spectralKappa ρ).im = 0) : (profileSampleDefect ρ).im = 0 := by
  obtain ⟨-, -, -, hU, -⟩ := native_sampling_form_positive (fun _ : Unit => ρ) (fun _ => hz)
    (fun _ => h0) (fun _ => h1)
  have h := congrArg Complex.im (hU () ())
  have hκ : spectralKappa ρ ≠ 0 := by
    obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
    exact mul_ne_zero hρ0 (sub_ne_zero.mpr (Ne.symm hρ1))
  have hre : (spectralKappa ρ).re ≠ 0 := fun hr => hκ (Complex.ext hr hk)
  simp only [Complex.mul_im, Complex.sub_im, Complex.sub_re, Complex.conj_re, Complex.conj_im, hk,
    neg_zero, sub_self, zero_mul, add_zero] at h
  have : 2 * (spectralKappa ρ).re * (profileSampleDefect ρ).im = 0 := by linarith
  rcases mul_eq_zero.mp this with h2 | h2
  · exact absurd (by linarith : (spectralKappa ρ).re = 0) hre
  · exact h2

/-- Conjugate coincidence: conj ρ is an actual zero, κ(conj ρ) = conj κ(ρ), the divided identity
does not apply, and the retained undivided identity gives b_ρ = conj b_(conj ρ). -/
theorem FullAudit26_expected_conjugate_coincidence (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    riemannZeta (conj ρ) = 0 ∧ spectralKappa (conj ρ) = conj (spectralKappa ρ) ∧
      spectralKappa ρ - conj (spectralKappa (conj ρ)) = 0 ∧
      profileSampleDefect ρ = conj (profileSampleDefect (conj ρ)) := by
  have hz' : riemannZeta (conj ρ) = 0 := by rw [_root_.riemannZeta_conj, hz, map_zero]
  have hκ : spectralKappa (conj ρ) = conj (spectralKappa ρ) := by
    simp [spectralKappa, map_mul, map_sub, map_one]
  let r : Bool → ℂ := fun b => if b then ρ else conj ρ
  obtain ⟨-, -, -, hU, -⟩ := native_sampling_form_positive r (fun b => by cases b <;> simp [r, hz, hz'])
    (fun b => by cases b <;> simp [r, h0]) (fun b => by cases b <;> simp [r, h1])
  have h := hU true false
  simp only [r, if_true, Bool.false_eq_true, if_false, hκ, Complex.conj_conj, sub_self, zero_mul] at h
  have hk0 : spectralKappa ρ ≠ 0 := by
    obtain ⟨hρ0, hρ1⟩ := strip_ne h0 h1
    exact mul_ne_zero hρ0 (sub_ne_zero.mpr (Ne.symm hρ1))
  refine ⟨hz', hκ, by rw [hκ, Complex.conj_conj, sub_self], ?_⟩
  have : spectralKappa ρ * (profileSampleDefect ρ - conj (profileSampleDefect (conj ρ))) = 0 := by
    linear_combination -h
  exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hk0)

/-- Construction level at the non-zero parameters ρ = 3/4, σ = 2/3: the finite-cell pairing with
its boundary term holds. -/
theorem FullAudit26_expected_construction_nonvacuous (N : ℕ) :
    ∫ x in (0 : ℝ)..((N : ℝ) + 1),
      (x : ℂ) ^ 2 * zeroProfileDeriv (3 / 4) x * conj (zeroProfileDeriv (2 / 3) x) =
        spectralKappa (3 / 4) * ((∫ x in (0 : ℝ)..((N : ℝ) + 1),
          (zeroProfile (3 / 4) x - 1) * conj (zeroProfile (2 / 3) x)) +
            ∑ m ∈ Finset.range N, conj (zeroProfile (2 / 3) (m + 1))) +
        (((N : ℝ) + 1 : ℝ) : ℂ) ^ 2 * -(srhoCellDeriv (3 / 4) N ((N : ℝ) + 1) / normalizationBrho (3 / 4)) *
          conj (zeroProfile (2 / 3) ((N : ℝ) + 1)) :=
  gram_finite (by norm_num) (by norm_num) (by norm_num) N

/-- The paper's falsification control with a nonreal parameter: A = 1, g = 1, κ = i. -/
theorem FullAudit26_expected_countercontrol_nonreal :
    (I : ℂ).im ≠ 0 ∧
    (∑ k : Fin 1, controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k *
      conj (controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k)) = 1 / 2 ∧
    (∑ k : Fin 1, ((1 : ℝ) : ℂ) * controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k *
      conj (controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k)) =
      I * ((∑ k : Fin 1, controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k *
        conj (controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k)) +
        conj (∑ k : Fin 1, ((1 : ℝ) : ℂ) * controlVector (fun _ => (1 : ℝ)) (fun _ => 1) I k)) := by
  have hI : (I : ℂ).im ≠ 0 := by simp
  obtain ⟨-, -, h1, -⟩ := finite_countercontrol (ι := Fin 1) (fun _ : Fin 1 => (1 : ℝ)) (fun _ => 1)
    (fun _ => one_pos) (fun _ => I) (fun _ => hI)
  refine ⟨hI, ?_, h1 0 0⟩
  have hd : ((1 : ℝ) : ℂ) - I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have hd' : (1 : ℂ) + I ≠ 0 := fun h => by simpa using congrArg Complex.im h
  have hd'' : (1 : ℂ) - I ≠ 0 := by simpa using hd
  have key : (1 - I) * (1 + I) = (2 : ℂ) := by ring_nf; rw [Complex.I_sq]; ring
  simp only [controlVector, Fin.sum_univ_one, map_div₀, map_mul, map_sub, Complex.conj_I, map_one,
    Complex.ofReal_one]
  rw [div_mul_div_comm, sub_neg_eq_add, key]
  ring_nf
  rw [Complex.I_sq]
  ring

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedSawtoothForce.lean; SHA256 fcbaf41bb5a4e4b0be7bf900568f61849e93e39c97bcedf68a498a757b100be0 -/
section

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.sawtooth_integrable_force_identity`,
`Zeta23.OPICAFollowup.sawtooth_actual_mellin_fourier` and
`Zeta23.OPICAFollowup.sawtooth_norm_weighted_zeta_moment` (F1).

Definition audits pin w(t) = e^(-t/2){e^t} and the tempered force 𝔤 = -(∂_t + 1/2) w built from
Mathlib's tempered-distribution derivative. All three roots are restated in full. Domain consumers
check:
- an independent compactly supported test around log 2 isolates the single atom 2^(-1/2)
  (the arithmetic part of 𝔤 is seen by an actual test, not assumed);
- the jump of w at log 2 equals minus that atom weight;
- the two transform conventions agree: 𝓕_log w(2πη) = 𝓕 w(η);
- the budget is a positive constant independent of any zero: 1/2 < log(2π) - γ < 2;
- the H⁻¹ bound applies to actual Schwartz tests. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real FourierTransform SchwartzMap ContDiff
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit27_audit_sawtoothWeight (t : ℝ) :
    sawtoothWeight t = ((Real.exp (-t / 2) * Int.fract (Real.exp t) : ℝ) : ℂ) := rfl

theorem FullAudit27_audit_nativeLogForce :
    nativeLogForce = -(TemperedDistribution.derivCLM ℂ sawtoothWeightTD) - (1 / 2 : ℂ) • sawtoothWeightTD :=
  rfl

/-! ### Restated roots -/

theorem expected_sawtooth_integrable_force_identity :
    Integrable sawtoothWeight ∧ MemLp sawtoothWeight 2 ∧
    (∀ t : ℝ, t < 0 → sawtoothWeight t = (Real.exp (t / 2) : ℂ)) ∧
    (∀ t : ℝ, ‖sawtoothWeight t‖ ≤ Real.exp (-t / 2)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), nativeLogForce φ = ∫ t, sawtoothWeight t * (deriv φ t - φ t / 2)) ∧
    (∀ (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      nativeLogForce (hc.toSchwartzMap hφ) =
        ∑' n : ℕ, ((((n : ℝ) + 1) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) * φ (Real.log (n + 1)) -
          ∫ t, (Real.exp (t / 2) : ℂ) * φ t) ∧
    (∀ n : ℕ, 1 ≤ n →
      Tendsto sawtoothWeight (𝓝[<] (Real.log n)) (𝓝 ((((n : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) ∧
        sawtoothWeight (Real.log n) = 0) :=
  sawtooth_integrable_force_identity

theorem expected_sawtooth_actual_mellin_fourier :
    (∀ s : ℂ, 0 < s.re → s.re < 1 →
      IntegrableOn (fun x : ℝ => ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1)) (Ioi 0) ∧
      ∫ x in Ioi (0 : ℝ), ((Int.fract x : ℝ) : ℂ) * (x : ℂ) ^ (-s - 1) = -riemannZeta s / s) ∧
    (∀ ξ : ℝ, logFourier sawtoothWeight ξ = -riemannZeta (1 / 2 + ξ * I) / (1 / 2 + ξ * I)) ∧
    (∀ ξ : ℝ, -(1 / 2 + ξ * I) * logFourier sawtoothWeight ξ = riemannZeta (1 / 2 + ξ * I)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (𝓕 nativeLogForce) φ =
      ∫ η : ℝ, riemannZeta (1 / 2 + (2 * π * η : ℝ) * I) * φ η) :=
  sawtooth_actual_mellin_fourier

theorem expected_sawtooth_norm_weighted_zeta_moment :
    (∫ x in (0 : ℝ)..1, Int.fract x ^ 2 / x ^ 2) = 1 ∧
    (∀ n : ℕ, 1 ≤ n → ∫ x in (n : ℝ)..(n + 1), Int.fract x ^ 2 / x ^ 2 =
      1 + n / (n + 1) - 2 * n * Real.log (1 + 1 / n)) ∧
    (∀ L : ℕ, 1 ≤ L → ∫ x in (0 : ℝ)..L, Int.fract x ^ 2 / x ^ 2 =
      2 * L - harmonic L - 2 * (L - 1) * Real.log L + 2 * Real.log (Real.Gamma L)) ∧
    Tendsto (fun L : ℕ => ∫ x in (0 : ℝ)..L, Int.fract x ^ 2 / x ^ 2) atTop
      (𝓝 (Real.log (2 * π) - Real.eulerMascheroniConstant)) ∧
    (∫ t, ‖sawtoothWeight t‖ ^ 2) = Real.log (2 * π) - Real.eulerMascheroniConstant ∧
    Integrable (fun ξ : ℝ => ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (ξ ^ 2 + 1 / 4)) ∧
    1 / (2 * π) * ∫ ξ : ℝ, ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (ξ ^ 2 + 1 / 4) =
      Real.log (2 * π) - Real.eulerMascheroniConstant ∧
    (∀ φ φ' : ℝ → ℂ, LogH1 φ φ' →
      ‖∫ t, sawtoothWeight t * (φ' t - φ t / 2)‖ ≤
        (Real.log (2 * π) - Real.eulerMascheroniConstant) ^ (1 / 2 : ℝ) *
          ((∫ t, ‖φ' t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), ‖nativeLogForce φ‖ ≤
        (Real.log (2 * π) - Real.eulerMascheroniConstant) ^ (1 / 2 : ℝ) *
          ((∫ t, ‖deriv φ t‖ ^ 2) + 1 / 4 * ∫ t, ‖φ t‖ ^ 2) ^ (1 / 2 : ℝ)) :=
  sawtooth_norm_weighted_zeta_moment

/-! ### Domain consumers -/

/-- An independent bump of radius 1/4 centred at log 2. -/
def FullAudit27_bumpLog2 : ContDiffBump (Real.log 2) := ⟨1 / 8, 1 / 4, by norm_num, by norm_num⟩

lemma FullAudit27_tsupport_bumpLog2 :
    tsupport (fun t => ((FullAudit27_bumpLog2 t : ℝ) : ℂ)) ⊆ Icc (Real.log 2 - 1 / 4) (Real.log 2 + 1 / 4) := by
  refine (tsupport_comp_subset Complex.ofReal_zero FullAudit27_bumpLog2).trans ?_
  rw [FullAudit27_bumpLog2.tsupport_eq]
  intro x hx
  rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
  change -(1 / 4 : ℝ) ≤ x - Real.log 2 ∧ x - Real.log 2 ≤ 1 / 4 at hx
  constructor <;> linarith [hx.1, hx.2]

/-- On the bump at log 2 the arithmetic part of 𝔤 is exactly the single atom 2^(-1/2). -/
theorem FullAudit27_expected_single_atom :
    ∃ (φ : ℝ → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ),
      φ (Real.log 2) = 1 ∧
      nativeLogForce (hc.toSchwartzMap hφ) =
        (((2 : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ) - ∫ t, (Real.exp (t / 2) : ℂ) * φ t := by
  set φ : ℝ → ℂ := fun t => ((FullAudit27_bumpLog2 t : ℝ) : ℂ)
  have hφ : ContDiff ℝ ∞ φ := Complex.ofRealCLM.contDiff.comp FullAudit27_bumpLog2.contDiff
  have hc : HasCompactSupport φ := FullAudit27_bumpLog2.hasCompactSupport.comp_left Complex.ofReal_zero
  have h1 : φ (Real.log 2) = 1 := by
    simp only [φ, FullAudit27_bumpLog2.one_of_mem_closedBall (Metric.mem_closedBall_self FullAudit27_bumpLog2.rIn_pos.le),
      Complex.ofReal_one]
  refine ⟨φ, hφ, hc, h1, ?_⟩
  rw [(sawtooth_integrable_force_identity).2.2.2.2.2.1 φ hφ hc]
  congr 1
  rw [tsum_eq_single 1 fun n hn => ?_]
  · norm_num [h1]
  · refine mul_eq_zero_of_right _ (image_eq_zero_of_notMem_tsupport (f := φ) fun h => ?_)
    have hb := FullAudit27_tsupport_bumpLog2 h
    have hl2 : (0.69 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hl2' : Real.log 2 < 0.7 := by have := Real.log_two_lt_d9; linarith
    rcases Nat.lt_or_gt_of_ne hn with h0 | h2
    · have : n = 0 := by omega
      subst this; simp only [CharP.cast_eq_zero, zero_add, Real.log_one] at hb; linarith [hb.1]
    · have h3 : Real.log 3 ≤ Real.log ((n : ℝ) + 1) :=
        Real.log_le_log (by norm_num)
          (by have h2' : (2 : ℝ) ≤ n := (by exact_mod_cast h2); linarith)
      have h32 : Real.log 3 = Real.log 2 + Real.log (3 / 2) := by
        rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
      have hl32 : (1 : ℝ) / 3 ≤ Real.log (3 / 2) := by
        have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
        norm_num at this ⊢; linarith
      linarith [hb.2]

/-- The jump of w at log 2 is minus the atom weight 2^(-1/2) of the compact-test identity. -/
theorem FullAudit27_expected_jump_matches_atom :
    Tendsto sawtoothWeight (𝓝[<] (Real.log 2)) (𝓝 ((((2 : ℝ) ^ (-(1 / 2) : ℝ) : ℝ) : ℂ))) ∧
      sawtoothWeight (Real.log 2) = 0 := by
  have := (sawtooth_integrable_force_identity).2.2.2.2.2.2 2 (by norm_num)
  simpa using this

/-- The two conventions agree: 𝓕_log w(2πη) = 𝓕 w(η). -/
theorem FullAudit27_expected_conventions (η : ℝ) :
    logFourier sawtoothWeight (2 * π * η) = 𝓕 sawtoothWeight η := by
  rw [logFourier_eq_fourier]; field_simp

/-- The source budget is a positive zero-free constant: 1/2 < log(2π) - γ < 2. -/
theorem FullAudit27_expected_budget_bounds :
    1 / 2 < Real.log (2 * π) - Real.eulerMascheroniConstant ∧
      Real.log (2 * π) - Real.eulerMascheroniConstant < 2 := by
  have hg1 := Real.one_half_lt_eulerMascheroniConstant
  have hg2 := Real.eulerMascheroniConstant_lt_two_thirds
  have hpi := Real.two_le_pi
  have hpi' := Real.pi_le_four
  have hl2 := Real.log_two_gt_d9
  have hl2' := Real.log_two_lt_d9
  have hlo : 2 * Real.log 2 ≤ Real.log (2 * π) := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num; linarith)
  have hhi : Real.log (2 * π) ≤ 3 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by positivity) (by norm_num; linarith)
  constructor <;> linarith

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedSpanPhysicalConsumer.lean; SHA256 143da66a5595d0206bf10ea6ec0143a887d318318f64e51c259b8fa372f2c444 -/
section
noncomputable section
open Set MeasureTheory Complex
open scoped SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan

namespace Zeta23.OPICAFollowup.Validation
theorem expected_actual_zero_measure_span_consumer (data : List (ℂ × ℂ × ℕ))
    (h : ∀ j ∈ data, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
      j.2.2 < zeroJetOrder j.2.1) :
    (∀ j ∈ data, Continuous (zeroProfile j.2.1) ∧ Integrable (zeroProfile j.2.1) ∧
      MemLp (zeroProfile j.2.1) 2 ∧ 𝓕 (zeroProfile j.2.1) = zeroProfile j.2.1 ∧
      (j.2.2 = 0 → normalizedZeroMeasureJet j.2.1 j.2.2 = zeroMeasure j.2.1)) ∧
    (∃ hg : (Zeta23.OPICAFollowup.zeroJetRealSpan data).HasLinearGrowth,
      (Zeta23.OPICAFollowup.zeroJetRealSpan data).FourierSelfdual hg ∧
      (Zeta23.OPICAFollowup.zeroJetRealSpan data).HasUnitGap ∧
      ((Zeta23.OPICAFollowup.zeroJetRealSpan data).negative integerLatticeᶜ = 0 →
        (Zeta23.OPICAFollowup.zeroJetRealSpan data).positive = 0 ∧
          (Zeta23.OPICAFollowup.zeroJetRealSpan data).negative = 0)) ∧
    (∀ n : ℕ, ∀ basis : Fin n → List (ℂ × ℂ × ℕ),
      ∀ hb : ∀ i, ∀ j ∈ basis i, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
        j.2.2 < zeroJetOrder j.2.1,
      LinearIndependent ℝ (fun i =>
        (Zeta23.OPICAFollowup.zeroJetRealSpan (basis i)).distributionOfLinearGrowth
          (zeroJetRealSpan_growth _ (hb i))) →
      ∀ a : Fin n → ℝ,
      (Zeta23.OPICAFollowup.zeroJetRealSpan (realBasisCombinationData basis a)).negative
        integerLatticeᶜ = 0 → a = 0) :=
  Zeta23.OPICAFollowup.actual_zero_measure_span_consumer data h

end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedSquareDefect.lean; SHA256 3735135eb0abad1f30935652c9bcdfc3ccee4e490697fe7a18b29806573176b2 -/
section

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.square_fourier_defect`,
`Zeta23.OPICAFollowup.square_defect_origin_positive`, `Zeta23.OPICAFollowup.square_no_lattice_repair`
and `Zeta23.OPICAFollowup.square_selfdual_projection_fills_gap` (R2-S3).

Definition audits pin τ_h = |A - h|² dx - |A|² Σ_(n ≠ 0) δ_n, the defect d = h ⋆ conj h - |h|²,
the lattice correction pairing and the Fourier action on functionals; the projection is the
parent `Zeta23.OPICA.involutionSelfdualProjection`. All four roots are restated in full. Domain
consumers instantiate them at the actual zero profile h = h_κ, A = 1, of an actual zero: every
hypothesis (evenness, continuity, L¹ ∩ L², ordinary self-duality, vanishing at infinity, plateau,
nonvanishing) is discharged from Stage 9, so the generic theorems apply to the actual square
construction. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ComplexConjugate
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit29_audit_squareGapMeasure (h : ℝ → ℂ) (A : ℂ) (φ : 𝓢(ℝ, ℂ)) : squareGapMeasure h A φ =
    (∫ x, ((‖A - h x‖ ^ 2 : ℝ) : ℂ) * φ x) - ((‖A‖ ^ 2 : ℝ) : ℂ) * ∑' n : ℤ, (if n = 0 then 0 else φ n) :=
  rfl

theorem FullAudit29_audit_squareDualityDefect (h : ℝ → ℂ) (x : ℝ) :
    squareDualityDefect h x = (∫ y, h y * conj (h (x - y))) - h x * conj (h x) := rfl

theorem FullAudit29_audit_projection (T : 𝓢(ℝ, ℂ) → ℂ) :
    Zeta23.OPICA.involutionSelfdualProjection fourierFunctional T = (2 : ℂ)⁻¹ • (T + fun φ => T (𝓕 φ)) :=
  rfl

/-! ### Restated roots -/

variable {h : ℝ → ℂ} {A : ℂ}

theorem expected_square_fourier_defect (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hint : Integrable h) (hL2 : MemLp h 2) (hsd : 𝓕 h = h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x, |x| ≤ 1 → h x = A) :
    (∀ φ : 𝓢(ℝ, ℂ), tsupport φ ⊆ Ioo (-1) 1 → squareGapMeasure h A φ = 0) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∀ x, 0 ≤ (φ x).re ∧ (φ x).im = 0) → (∀ n : ℤ, φ n = 0) →
      0 ≤ (squareGapMeasure h A φ).re) ∧
    (∃ M : ℝ, ∀ x, ‖A - h x‖ ^ 2 ≤ M) ∧
    Continuous (squareDualityDefect h) ∧ Tendsto (squareDualityDefect h) (cocompact ℝ) (𝓝 0) ∧
    (∀ x, (squareDualityDefect h x).im = 0) ∧
    (∀ x, squareDualityDefect h x = 𝓕 (fun y => h y * conj (h y)) x - h x * conj (h x)) ∧
    (∀ φ : 𝓢(ℝ, ℂ), squareGapMeasure h A (𝓕 φ) - squareGapMeasure h A φ = ∫ x, squareDualityDefect h x * φ x) :=
  square_fourier_defect hev hcont hint hL2 hsd hvan hpl

theorem expected_square_defect_origin_positive (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hL2 : MemLp h 2) (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    squareDualityDefect h 0 = (((∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2 : ℝ) : ℂ) ∧
    0 < (∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2 ∧
    (A ≠ 0 → ‖A‖ ^ 2 ≤ (∫ x, ‖h x‖ ^ 2) - ‖A‖ ^ 2) ∧
    (A = 0 → 0 < ∫ x, ‖h x‖ ^ 2) :=
  square_defect_origin_positive hev hcont hL2 hpl hne

theorem expected_square_no_lattice_repair (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hint : Integrable h) (hL2 : MemLp h 2) (hsd : 𝓕 h = h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    ¬ ∃ c : ℤ → ℂ, TemperedLatticeWeights c ∧ ∀ φ : 𝓢(ℝ, ℂ),
      squareGapMeasure h A (𝓕 φ) + latticePairing c (𝓕 φ) = squareGapMeasure h A φ + latticePairing c φ :=
  square_no_lattice_repair hev hcont hint hL2 hsd hvan hpl hne

theorem expected_square_selfdual_projection_fills_gap (hev : ∀ x, h (-x) = h x) (hcont : Continuous h)
    (hint : Integrable h) (hL2 : MemLp h 2) (hsd : 𝓕 h = h)
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    fourierFunctional (Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A)) =
      Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) ∧
    (∀ φ : 𝓢(ℝ, ℂ), Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) φ =
      squareGapMeasure h A φ + (1 / 2) * ∫ x, squareDualityDefect h x * φ x) ∧
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (∀ x ∈ Ioo (-ε) ε, 0 < (squareDualityDefect h x).re ∧ (squareDualityDefect h x).im = 0) ∧
      ∀ φ : 𝓢(ℝ, ℂ), tsupport φ ⊆ Ioo (-ε) ε →
        Zeta23.OPICA.involutionSelfdualProjection fourierFunctional (squareGapMeasure h A) φ =
          ∫ x, (squareDualityDefect h x / 2) * φ x :=
  square_selfdual_projection_fills_gap hev hcont hint hL2 hsd hpl hne

/-! ### Actual domain: the zero profile of an actual zero -/

lemma FullAudit29_zeroProfile_vanishing {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    Tendsto (zeroProfile ρ) (cocompact ℝ) (𝓝 0) := by
  obtain ⟨K, hK0, hK⟩ := zeroProfile_norm_le hz h0 h1
  have hlim : Tendsto (fun x : ℝ => K * (1 + x ^ 2)⁻¹) (cocompact ℝ) (𝓝 (K * 0)) := by
    refine (tendsto_inv_atTop_zero.comp ?_).const_mul K
    refine tendsto_atTop_add_const_left _ _ ?_
    have hn := (tendsto_pow_atTop (two_ne_zero : (2 : ℕ) ≠ 0)).comp (tendsto_norm_cocompact_atTop (E := ℝ))
    refine hn.congr fun x => ?_
    simp [Real.norm_eq_abs, sq_abs]
  rw [mul_zero] at hlim
  exact squeeze_zero_norm (fun x => hK x) hlim

lemma FullAudit29_zeroProfile_ne_zero (ρ : ℂ) : zeroProfile ρ ≠ 0 := fun h => by
  have := congrFun h 0
  rw [zeroProfile_eq_one ρ (by simp)] at this
  exact one_ne_zero this

/-- The actual square construction at an actual zero: all four roots hold for h = h_κ, A = 1; the
defect at the origin is d(0) = ‖h_κ‖₂² - 1 ≥ 1, and no lattice correction repairs it. -/
theorem FullAudit29_expected_actual_square {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    (∀ φ : 𝓢(ℝ, ℂ), squareGapMeasure (zeroProfile ρ) 1 (𝓕 φ) - squareGapMeasure (zeroProfile ρ) 1 φ =
      ∫ x, squareDualityDefect (zeroProfile ρ) x * φ x) ∧
    1 ≤ (∫ x, ‖zeroProfile ρ x‖ ^ 2) - 1 ∧
    squareDualityDefect (zeroProfile ρ) 0 = (((∫ x, ‖zeroProfile ρ x‖ ^ 2) - 1 : ℝ) : ℂ) ∧
    (¬ ∃ c : ℤ → ℂ, TemperedLatticeWeights c ∧ ∀ φ : 𝓢(ℝ, ℂ),
      squareGapMeasure (zeroProfile ρ) 1 (𝓕 φ) + latticePairing c (𝓕 φ) =
        squareGapMeasure (zeroProfile ρ) 1 φ + latticePairing c φ) ∧
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ ∀ x ∈ Ioo (-ε) ε, 0 < (squareDualityDefect (zeroProfile ρ) x).re := by
  have hev := zeroProfile_neg ρ
  have hcont := continuous_zeroProfile ρ
  have hint := integrable_zeroProfile hz h0 h1
  have hL2 := memLp_two_zeroProfile hz h0 h1
  have hsd := fourier_zeroProfile hz h0 h1
  have hvan := FullAudit29_zeroProfile_vanishing hz h0 h1
  have hpl : ∀ x, |x| ≤ 1 → zeroProfile ρ x = 1 := fun x hx => zeroProfile_eq_one ρ hx
  have hne := FullAudit29_zeroProfile_ne_zero ρ
  obtain ⟨hd0, -, hge, -⟩ := square_defect_origin_positive hev hcont hL2 hpl hne
  obtain ⟨-, -, ε, hε0, hε1, hεx, -⟩ := square_selfdual_projection_fills_gap hev hcont hint hL2 hsd hpl hne
  refine ⟨(square_fourier_defect hev hcont hint hL2 hsd hvan hpl).2.2.2.2.2.2.2, ?_, ?_,
    square_no_lattice_repair hev hcont hint hL2 hsd hvan hpl hne, ε, hε0, hε1, fun x hx => (hεx x hx).1⟩
  · simpa using hge one_ne_zero
  · simpa using hd0

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedWeighted.lean; SHA256 e137ed312f799cd589126a89281470c9f45293bcccf1386598dd66de30639bad -/
section

noncomputable section
open Set MeasureTheory Complex
open scoped ENNReal FourierTransform SchwartzMap
open Zeta23.OPICA Zeta23.OPICAFollowup

namespace Zeta23.OPICAFollowup.Validation
/-- Independent full frozen statement, with arbitrary complex locally finite
input and the true-variation exponential moment. No support assumption. -/
theorem expected_weighted_mixture_exists_fourier
    (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1/2<a) (hm : mixingExponentialMoment a sigma<∞) :
    ∃ (nu : LocallyFiniteComplexMeasure) (hg : nu.HasLinearGrowth),
      nu=weightedDilationMixture sigma a ha.le hm ∧
      (∀ f : SchwartzMap ℝ ℂ, nu.integral f=
        sigma.integral (fun t => dilatedCombDistribution t f)) ∧
      𝓕 (nu.distributionOfLinearGrowth hg)=
        (weightedDilationMixture (reflectedMixingMeasure sigma) a ha.le
          (mixingExponentialMoment_reflect_lt_top sigma a hm)).distributionOfLinearGrowth
            (weightedDilationMixture_growth _ _ _ _) ∧
      nu.compactRestriction ({0} : Set ℝ) isCompact_singleton ({0} : Set ℝ)=
        sigma.integral (fun t => (Real.exp (t/2) : ℂ)) ∧
      (∀ (f : SchwartzMap ℝ ℂ) (i : Fin 4),
        Integrable (fun z : ℝ × ℤ => (Real.exp (z.1/2) : ℂ)*f (mixtureLatticePoint z))
          ((mixingCoordinate sigma i).prod (Measure.count : Measure ℤ))) :=
  weighted_mixture_exists_fourier sigma a ha hm

/-- The actual positive constructor acts on the entire lattice, and evaluation
on arbitrary measurable sets is the literal mixture integral. -/
theorem FullAudit30_expected_positive_actual_measure (mu : Measure ℝ) [SFinite mu]
    (s : Set ℝ) (hs : MeasurableSet s) :
    positiveDilationMixture mu s=∫⁻ t, dilatedCombMeasure t s ∂mu :=
  positiveDilationMixture_apply mu s hs

theorem FullAudit30_expected_positive_parameter_atom (t : ℝ) :
    positiveDilationMixture (Measure.dirac t)=dilatedCombMeasure t := by
  apply Measure.ext
  intro s hs
  rw [positiveDilationMixture_apply _ s hs,lintegral_dirac]

/-- Even a finite input atom gives infinite whole-line output mass, so the
construction has not accidentally been confined to finite complex measures. -/
theorem FullAudit30_expected_infinite_output_mass :
    positiveDilationMixture (Measure.dirac (0 : ℝ)) univ=∞ := by
  rw [FullAudit30_expected_positive_parameter_atom]
  simp only [dilatedCombMeasure,zero_div,Real.exp_zero,ENNReal.ofReal_one,one_smul,
    scaledLatticeMeasure,Measure.map_apply (scaledLatticePoint_measurable 0) MeasurableSet.univ,
    preimage_univ]
  exact Measure.count_apply_infinite infinite_univ

theorem FullAudit30_expected_positive_origin (mu : Measure ℝ) [SFinite mu] :
    positiveDilationMixture mu ({0} : Set ℝ)=∫⁻ t, ENNReal.ofReal (Real.exp (t/2)) ∂mu :=
  positiveDilationMixture_origin mu

def FullAudit30_imaginaryParameterAtom : LocallyFiniteComplexMeasure :=
  ⟨localJordanDifference 0 0,localJordanDifference (Measure.dirac (0 : ℝ)) 0⟩

lemma FullAudit30_imaginaryParameterAtom_moment : mixingExponentialMoment 1 FullAudit30_imaginaryParameterAtom<∞ := by
  apply (lintegral_mono' FullAudit30_imaginaryParameterAtom.totalVariation_le_control le_rfl).trans_lt
  simp [FullAudit30_imaginaryParameterAtom,LocallyFiniteComplexMeasure.variationControl,
    LocallyFiniteSignedMeasure.totalVariation,localJordanDifference]

/-- Purely imaginary coefficients are retained, including their sign. -/
theorem FullAudit30_expected_imaginary_origin :
    (weightedDilationMixture FullAudit30_imaginaryParameterAtom 1 (by norm_num)
      FullAudit30_imaginaryParameterAtom_moment).compactRestriction ({0} : Set ℝ)
        isCompact_singleton ({0} : Set ℝ)=I := by
  rw [weightedDilationMixture_origin]
  simp [FullAudit30_imaginaryParameterAtom,LocallyFiniteComplexMeasure.integral,localJordanDifference]

/-- The absolute Fubini gate holds without a compact-support or positivity
premise on the complex parameter measure. -/
theorem FullAudit30_expected_full_product_integrability (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1/2<a) (hm : mixingExponentialMoment a sigma<∞)
    (f : SchwartzMap ℝ ℂ) (i : Fin 4) :
    Integrable (fun z : ℝ × ℤ => (Real.exp (z.1/2) : ℂ)*f (mixtureLatticePoint z))
      ((mixingCoordinate sigma i).prod (Measure.count : Measure ℤ)) :=
  positiveDilationMixture_product_integrable _ a ha.le (mixingCoordinate_moment sigma a hm i) f

def FullAudit30_realParameterMeasure (mu : LocallyFiniteSignedMeasure) : LocallyFiniteComplexMeasure :=
  ⟨mu,localJordanDifference 0 0⟩

/-- Every actual locally finite real signed parameter measure embeds in the
full theorem, and the constructed output has zero imaginary Jordan component. -/
theorem FullAudit30_expected_real_parameter_output (mu : LocallyFiniteSignedMeasure) (a : ℝ)
    (ha : 1/2<a) (hm : mixingExponentialMoment a (FullAudit30_realParameterMeasure mu)<∞) :
    (weightedDilationMixture (FullAudit30_realParameterMeasure mu) a ha.le hm).imPart=
      localJordanDifference 0 0 := by
  simp [weightedDilationMixture,mixingCoordinate,FullAudit30_realParameterMeasure,
    positiveDilationMixture,localJordanDifference]

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedWeightedInverse.lean; SHA256 d803b68b053f867a4ca7fd51484dbc13ddd1508accca481aadd2d133f5dc5773 -/
section

/- Independent consumers for the original R1-HT1 roots
`weighted_mobius_inverse`, `weighted_mixture_sharp_gap` and `weighted_gap_leakage`.

Definition audits pin the lattice measures N, M⁺, M⁻ and the weighted norm to
their explicit formulas. The root types are restated in full, including the
Jordan pair M⁺ ⟂ M⁻ behind ‖M_μ‖ and the leakage bound with the genuine complex
variations. Actual-domain consumers use genuine point-mass mixers built from
canonical Jordan pairs: the leakage lower bound is strictly positive for δ₋₁, the
sharp-gap hypotheses are satisfied by δ₀, whose mixture is exactly the integer comb
(so the sharp-gap theorem is not vacuous), leakage fails without the
negative-support restriction, and the endpoint witness e^(-b|t|) dt is an
admissible actual mixer whose mixture has the explicit density r_h. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology FourierTransform SchwartzMap
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit31_audit_integerLogComb : integerLogComb =
    Measure.sum (fun k : ℕ => (if k = 0 then 0 else ENNReal.ofReal (Real.sqrt (k : ℝ))⁻¹) •
      Measure.dirac (Real.log k)) := rfl

theorem FullAudit31_audit_moebiusPlusComb : moebiusPlusComb =
    Measure.sum (fun k : ℕ => (if ArithmeticFunction.moebius k = 1 then
      (if k = 0 then 0 else ENNReal.ofReal (Real.sqrt (k : ℝ))⁻¹) else 0) •
      Measure.dirac (Real.log k)) := rfl

theorem FullAudit31_audit_moebiusMinusComb : moebiusMinusComb =
    Measure.sum (fun k : ℕ => (if ArithmeticFunction.moebius k = -1 then
      (if k = 0 then 0 else ENNReal.ofReal (Real.sqrt (k : ℝ))⁻¹) else 0) •
      Measure.dirac (Real.log k)) := rfl

theorem FullAudit31_audit_weightedLogNorm (a : ℝ) (ρ : Measure ℝ) :
    weightedLogNorm a ρ = ∫⁻ y, ENNReal.ofReal (Real.exp (-a * y)) ∂ρ := rfl

theorem FullAudit31_audit_mixtureDensity (h : ℝ → ℂ) (x : ℝ) :
    mixtureDensity h x = ((Real.sqrt x)⁻¹ : ℝ) * ∑' n : ℕ,
      ((if n = 0 then 0 else (Real.sqrt (n : ℝ))⁻¹ : ℝ) : ℂ) * h (Real.log (x / n)) := rfl

/-! ### Restated roots -/

theorem FullAudit31_expected_moebius_lattice_identity :
    moebiusPlusComb ∗ integerLogComb = Measure.dirac 0 + moebiusMinusComb ∗ integerLogComb :=
  (weighted_mobius_inverse (⟨localJordanDifference 0 0, localJordanDifference 0 0⟩) 1
    (by norm_num) (by
      refine lt_of_le_of_lt (lintegral_mono' (LocallyFiniteComplexMeasure.totalVariation_le_control _)
        le_rfl) ?_
      change ∫⁻ t, ENNReal.ofReal (Real.exp (1 * |t|)) ∂(((0 - 0) + (0 - 0)) + ((0 - 0) + (0 - 0))) < ∞
      simp)).2.2.2.1

theorem FullAudit31_expected_weighted_mobius_inverse_real (σ : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a σ < ∞) :
    positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive +
        integerLogComb ∗ σ.rePart.negative =
      positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative +
        integerLogComb ∗ σ.rePart.positive ∧
    σ.rePart.positive +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive) =
      σ.rePart.negative +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative) ∧
    moebiusPlusComb ⟂ₘ moebiusMinusComb ∧
    weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) =
        ENNReal.ofReal (∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2))) ∧
    ((∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) =
      riemannZeta ((a + 1 / 2 : ℝ) : ℂ) / riemannZeta ((2 * a + 1 : ℝ) : ℂ) := by
  obtain ⟨-, hre, -, -, hinv, -, -, -, -, -, hM⟩ := weighted_mobius_inverse σ a ha hm
  exact ⟨hre, hinv, hM⟩

theorem FullAudit31_expected_weighted_mixture_sharp_gap (σ : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a σ < ∞)
    (hself : 𝓕 ((weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm)) =
      (weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm))
    (hgap : (weightedDilationMixture σ a ha.le hm).variationControl (Ioo (-1) 1 \ {0}) = 0) :
    σ.variationControl ({0}ᶜ) = 0 ∧
    (weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm) =
      σ.integral (fun _ => 1) • dilatedCombDistribution 0 ∧
    ((weightedDilationMixture σ a ha.le hm).compactRestriction {0} isCompact_singleton {0} = 0 →
      (weightedDilationMixture σ a ha.le hm).variationControl = 0) := by
  obtain ⟨-, h1, h2, -, h3⟩ := weighted_mixture_sharp_gap σ a ha hm hself hgap
  exact ⟨h1, h2, fun h0 => (h3 h0).2.2⟩

/-- HT1.7 with the genuine complex variations |σ| and |ν|. -/
theorem FullAudit31_expected_complex_gap_leakage (σ : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a σ < ∞) :
    ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
        ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.totalVariation ≤
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
        ∂(weightedDilationMixture σ a ha.le hm).totalVariation :=
  (weighted_gap_leakage.1 σ a ha hm).1

theorem FullAudit31_expected_weighted_gap_leakage_real (σ : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a σ < ∞) :
    ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
        ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t))
          ∂(σ.rePart.positive + σ.rePart.negative) ≤
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
        ∂((weightedDilationMixture σ a ha.le hm).rePart.positive +
          (weightedDilationMixture σ a ha.le hm).rePart.negative) :=
  (weighted_gap_leakage.1 σ a ha hm).2.1

/-! ### Actual point-mass mixers -/

/-- The genuine complex point mass δ_x (canonical Jordan pairs). -/
def FullAudit31_pointMixer (x : ℝ) : LocallyFiniteComplexMeasure :=
  ⟨localJordanDifference (Measure.dirac x) 0, localJordanDifference 0 0⟩

lemma FullAudit31_pointMixer_control (x : ℝ) : (FullAudit31_pointMixer x).variationControl = Measure.dirac x := by
  change ((Measure.dirac x - 0) + (0 - Measure.dirac x)) + ((0 - 0) + (0 - 0)) = _
  simp

lemma FullAudit31_pointMixer_moment (x a : ℝ) : mixingExponentialMoment a (FullAudit31_pointMixer x) < ∞ := by
  refine lt_of_le_of_lt (lintegral_mono' (LocallyFiniteComplexMeasure.totalVariation_le_control _)
    le_rfl) ?_
  rw [FullAudit31_pointMixer_control, lintegral_dirac]
  exact ENNReal.ofReal_lt_top

lemma FullAudit31_zeta_leakage_ratio_pos {a : ℝ} (ha : 1 / 2 < a) :
    0 < (riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re := by
  have hs : 1 < a + 1 / 2 := by linarith
  rw [show (2 * a + 1 : ℝ) = 2 * (a + 1 / 2) by ring, zeta_ratio_re hs]
  exact inv_pos.mpr (tsum_abs_moebius_rpow_pos hs)

/-- Non-vacuity of leakage: the actual mixture of δ₋₁ has strictly positive weighted
variation inside the gap (0,1), at least the explicit zeta-ratio bound. -/
theorem FullAudit31_expected_point_mixer_leakage_positive (a : ℝ) (ha : 1 / 2 < a) :
    ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
        ENNReal.ofReal (Real.exp a) ≤
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
        ∂(weightedDilationMixture (FullAudit31_pointMixer (-1)) a ha.le (FullAudit31_pointMixer_moment (-1) a)).rePart.totalVariation ∧
    0 < ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
        ∂(weightedDilationMixture (FullAudit31_pointMixer (-1)) a ha.le (FullAudit31_pointMixer_moment (-1) a)).rePart.totalVariation := by
  have hL := (weighted_gap_leakage.1 (FullAudit31_pointMixer (-1)) a ha (FullAudit31_pointMixer_moment (-1) a)).2.1
  have hσ : ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂(FullAudit31_pointMixer (-1)).rePart.totalVariation =
      ENNReal.ofReal (Real.exp a) := by
    change ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t))
      ∂((Measure.dirac (-1) - 0) + (0 - Measure.dirac (-1))) = _
    simp only [Measure.sub_zero, Measure.zero_sub, add_zero]
    classical
    rw [setLIntegral_dirac, if_pos (show (-1 : ℝ) ∈ Iio 0 by norm_num)]
    congr 2
    ring
  rw [hσ] at hL
  refine ⟨hL, lt_of_lt_of_le ?_ hL⟩
  exact ENNReal.mul_pos (by simpa using FullAudit31_zeta_leakage_ratio_pos ha) (by simp [Real.exp_pos])

/-- The δ₀ mixer: its mixture is exactly the integer comb measure. -/
lemma FullAudit31_pointMixer_zero_positive (a : ℝ) (ha : 1 / 2 ≤ a) (hm : mixingExponentialMoment a (FullAudit31_pointMixer 0) < ∞) :
    (weightedDilationMixture (FullAudit31_pointMixer 0) a ha hm).rePart.positive = dilatedCombMeasure 0 ∧
    (weightedDilationMixture (FullAudit31_pointMixer 0) a ha hm).rePart.negative = 0 ∧
    (weightedDilationMixture (FullAudit31_pointMixer 0) a ha hm).imPart.positive = 0 ∧
    (weightedDilationMixture (FullAudit31_pointMixer 0) a ha hm).imPart.negative = 0 := by
  have h0 : positiveDilationMixture (Measure.dirac (0 : ℝ) - 0) = dilatedCombMeasure 0 := by
    ext s hs
    rw [Measure.sub_zero, positiveDilationMixture_apply _ s hs, lintegral_dirac]
  have hz : positiveDilationMixture ((0 : Measure ℝ) - Measure.dirac 0) = 0 := by
    rw [Measure.zero_sub, positiveDilationMixture_zero]
  have hz' : positiveDilationMixture ((0 : Measure ℝ) - 0) = 0 := by
    rw [Measure.sub_zero, positiveDilationMixture_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · change positiveDilationMixture (Measure.dirac 0 - 0) -
      positiveDilationMixture (0 - Measure.dirac 0) = _
    rw [h0, hz, Measure.sub_zero]
  · change positiveDilationMixture (0 - Measure.dirac 0) -
      positiveDilationMixture (Measure.dirac 0 - 0) = _
    rw [hz, Measure.zero_sub]
  · change positiveDilationMixture (0 - 0) - positiveDilationMixture (0 - 0) = _
    rw [hz', Measure.sub_self]
  · change positiveDilationMixture (0 - 0) - positiveDilationMixture (0 - 0) = _
    rw [hz', Measure.sub_self]

/-- Non-vacuity of the sharp-gap hypotheses: the δ₀ mixture has the exact punctured
gap, and the sharp-gap theorem then returns c = 1 and the integer comb. -/
theorem FullAudit31_expected_point_mixer_gap (a : ℝ) (ha : 1 / 2 < a) :
    (weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).variationControl
        (Ioo (-1) 1 \ {0}) = 0 ∧
    (FullAudit31_pointMixer 0).integral (fun _ => 1) = 1 := by
  obtain ⟨h1, h2, h3, h4⟩ := FullAudit31_pointMixer_zero_positive a ha.le (FullAudit31_pointMixer_moment 0 a)
  refine ⟨?_, ?_⟩
  · change (((weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).rePart.positive +
        (weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).rePart.negative) +
      ((weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).imPart.positive +
        (weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).imPart.negative))
        (Ioo (-1) 1 \ {0}) = 0
    rw [h1, h2, h3, h4]
    simpa using dilatedCombMeasure_punctured_gap 0
  · unfold LocallyFiniteComplexMeasure.integral
    change ((∫ _x, (1 : ℂ) ∂(Measure.dirac (0 : ℝ) - 0)) - (∫ _x, (1 : ℂ) ∂(0 - Measure.dirac 0))) +
      Complex.I * ((∫ _x, (1 : ℂ) ∂((0 : Measure ℝ) - 0)) - (∫ _x, (1 : ℂ) ∂((0 : Measure ℝ) - 0))) = 1
    simp

/-- The δ₀ mixture is the integer Dirac comb as a tempered distribution. -/
lemma FullAudit31_pointMixer_zero_distribution (a : ℝ) (ha : 1 / 2 < a) :
    (weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)) =
      dilatedCombDistribution 0 := by
  obtain ⟨h1, h2, h3, h4⟩ := FullAudit31_pointMixer_zero_positive a ha.le (FullAudit31_pointMixer_moment 0 a)
  ext f
  rw [LocallyFiniteComplexMeasure.distributionOfLinearGrowth_apply, dilatedCombDistribution,
    LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply]
  unfold LocallyFiniteComplexMeasure.integral
  rw [h1, h2, h3, h4]
  simp [dilatedCombJordan, localJordanDifference]

/-- Full non-vacuity of the sharp-gap root: the actual δ₀ mixture satisfies both
hypotheses (canonical self-duality is Poisson summation, the gap is exact), and
the root applies to it. -/
theorem FullAudit31_expected_point_mixer_sharp_gap_instance (a : ℝ) (ha : 1 / 2 < a) :
    𝓕 ((weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a))) =
      (weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)) ∧
    (FullAudit31_pointMixer 0).variationControl ({0}ᶜ) = 0 ∧
    (weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)) =
      dilatedCombDistribution 0 := by
  have hD := FullAudit31_pointMixer_zero_distribution a ha
  have hself : 𝓕 ((weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le
        (FullAudit31_pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a))) =
      (weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).distributionOfLinearGrowth
        (weightedDilationMixture_growth (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)) := by
    rw [hD]
    simpa using (dilated_comb_fourier 0).2.2
  obtain ⟨hgap, hc⟩ := FullAudit31_expected_point_mixer_gap a ha
  obtain ⟨-, h1, h2, -, -⟩ :=
    weighted_mixture_sharp_gap (FullAudit31_pointMixer 0) a ha (FullAudit31_pointMixer_moment 0 a) hself hgap
  refine ⟨hself, h1, ?_⟩
  rw [h2, hc, one_smul]

/-- Falsification check: leakage needs the restriction to negative logarithmic
support. Integrated over all t, the δ₀ mixer has positive left side while its
actual mixture carries no variation in the gap (0,1). -/
theorem FullAudit31_expected_leakage_needs_negative_support (a : ℝ) (ha : 1 / 2 < a) :
    ¬ (ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
          ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t)) ∂(FullAudit31_pointMixer 0).rePart.totalVariation ≤
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
          ∂(weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).rePart.totalVariation) := by
  obtain ⟨h1, h2, -, -⟩ := FullAudit31_pointMixer_zero_positive a ha.le (FullAudit31_pointMixer_moment 0 a)
  have hR : ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
      ∂(weightedDilationMixture (FullAudit31_pointMixer 0) a ha.le (FullAudit31_pointMixer_moment 0 a)).rePart.totalVariation = 0 := by
    refine setLIntegral_measure_zero _ _ ?_
    rw [LocallyFiniteSignedMeasure.totalVariation, h1, h2, add_zero]
    refine measure_mono_null (fun x hx => ?_) (dilatedCombMeasure_punctured_gap 0)
    rw [Real.exp_zero]
    exact ⟨⟨by linarith [hx.1], hx.2⟩, fun h => (ne_of_gt hx.1) h⟩
  have hL : ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t)) ∂(FullAudit31_pointMixer 0).rePart.totalVariation = 1 := by
    change ∫⁻ t, ENNReal.ofReal (Real.exp (-a * t))
      ∂((Measure.dirac (0 : ℝ) - 0) + (0 - Measure.dirac 0)) = 1
    simp
  rw [hR, hL, mul_one, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero, not_le]
  exact FullAudit31_zeta_leakage_ratio_pos ha

/-- The density form of leakage and the endpoint witness, restated. -/
theorem FullAudit31_expected_density_leakage :
    (∀ (h : ℝ → ℂ) (H b : ℝ), 1 / 2 < b → Continuous h → (∀ t, h (-t) = h t) →
      (∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) →
      ENNReal.ofReal ((riemannZeta ((2 * b + 1 : ℝ) : ℂ) / riemannZeta ((b + 1 / 2 : ℝ) : ℂ)).re) *
          (⨆ t ∈ Ici (0 : ℝ), ENNReal.ofReal (Real.exp (b * t) * ‖h t‖)) ≤
        ⨆ x ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ (1 / 2 - b) * ‖mixtureDensity h x‖)) ∧
    (∀ b : ℝ, 1 / 2 < b → ∃ h : ℝ → ℂ, Continuous h ∧ (∀ t, h (-t) = h t) ∧
      (∀ t, ‖h t‖ ≤ 1 * Real.exp (-b * |t|)) ∧
      ∫⁻ t, ENNReal.ofReal (Real.exp (b * |t|) * ‖h t‖) = ∞) :=
  ⟨weighted_gap_leakage.2.1, weighted_gap_leakage.2.2.2.1⟩

/-- r_h is the actual density: restatement of the density identification. -/
theorem FullAudit31_expected_density_identification (h : ℝ → ℂ) (hc : Continuous h) (H b : ℝ)
    (hb : 1 / 2 < b) (hd : ∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) :
    (∀ a : ℝ, a < b → mixingExponentialMoment a (densityMixer h hc) < ∞) ∧
    (∀ s : Set ℝ, MeasurableSet s → s ⊆ Ioi 0 →
      positiveDilationMixture (mixingCoordinate (densityMixer h hc) 0) s =
        ∫⁻ x in s, ENNReal.ofReal (Real.sqrt x)⁻¹ * ∑' n : ℕ,
          (if n = 0 then 0 else ENNReal.ofReal (Real.sqrt (n : ℝ))⁻¹) *
            ENNReal.ofReal (h (Real.log (x / n))).re) ∧
    (∀ x : ℝ, 0 < x → mixtureDensity h x =
      (((positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 0 t)) x).toReal -
        (positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 1 t)) x).toReal :
          ℝ) : ℂ) +
      Complex.I * (((positiveMixtureDensity
          (fun t => ENNReal.ofReal (densityCoordinate h 2 t)) x).toReal -
        (positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 3 t)) x).toReal :
          ℝ) : ℂ)) := by
  obtain ⟨hmom, hcoord, -, hpt⟩ := weighted_gap_leakage.2.2.2.2 h hc H b hb hd
  refine ⟨hmom, fun s hs hpos => ?_, hpt⟩
  rw [hcoord 0 s hs hpos]
  rfl

/-- Domain check: the endpoint witness e^(-b|t|) dt is an admissible actual mixer below b,
and its actual mixture has the explicit density x^(-1/2) Σ n^(-1/2) e^(-b|log(x/n)|). -/
theorem FullAudit31_expected_endpoint_witness_mixture (b : ℝ) (hb : 1 / 2 < b) :
    ∃ hc : Continuous (fun t : ℝ => ((Real.exp (-b * |t|) : ℝ) : ℂ)),
      mixingExponentialMoment ((1 / 2 + b) / 2) (densityMixer _ hc) < ∞ ∧
      ∀ s : Set ℝ, MeasurableSet s → s ⊆ Ioi 0 →
        positiveDilationMixture (mixingCoordinate (densityMixer _ hc) 0) s =
          ∫⁻ x in s, ENNReal.ofReal (Real.sqrt x)⁻¹ * ∑' n : ℕ,
            (if n = 0 then 0 else ENNReal.ofReal (Real.sqrt (n : ℝ))⁻¹) *
              ENNReal.ofReal (Real.exp (-b * |Real.log (x / n)|)) := by
  obtain ⟨hc, -, hd, -⟩ := endpoint_density_witness b
  refine ⟨hc, (FullAudit31_expected_density_identification _ hc 1 b hb hd).1 _ (by linarith),
    fun s hs hpos => ?_⟩
  rw [(FullAudit31_expected_density_identification _ hc 1 b hb hd).2.1 s hs hpos]
  simp only [Complex.ofReal_re]

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedWeightedSpectralMeasure.lean; SHA256 3f5843a25bc9b01179292b46b963e5807c59d459d5cc8e19b273475bfe40ee71 -/
section

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.arithmetic_stieltjes_holomorphic`
and `Zeta23.OPICAFollowup.arithmetic_stieltjes_sign_budget` (F2).

Definition audits pin a(ξ) = ξ² + 1/4, dω = |ζ(1/2 + iξ)|² dξ/(2π) as a density measure, the
Stieltjes function M(κ) = ∫ dω/(a - κ) and the resolvent set ℂ \ [1/4, ∞). Both roots are restated
in full. Domain consumers check:
- the weighted moment of ω is the F1 source norm ‖w‖₂² of the actual sawtooth weight;
- at the real resolvent point κ = -1, M is real and positive (no sign is imposed: it is computed);
- at κ = i the sign identity gives Im M(i) > 0 and the budget gives |M(i)| ≤ 2(log(2π) - γ);
- an actual off-line strip parameter (Re ρ ≠ 1/2, Im ρ ≠ 0) has Im κ ≠ 0, so κ = ρ(1 - ρ) lies in
  the resolvent set and both roots apply to it; a critical-line parameter has real κ ≥ 1/4, on
  the cut, where neither root is asserted. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology Real
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit32_audit_spectralEnergy (ξ : ℝ) : spectralEnergy ξ = ξ ^ 2 + 1 / 4 := rfl

theorem FullAudit32_audit_arithmeticDensity (ξ : ℝ) :
    arithmeticDensity ξ = ‖riemannZeta (1 / 2 + ξ * I)‖ ^ 2 / (2 * π) := rfl

theorem FullAudit32_audit_arithmeticSpectralMeasure :
    arithmeticSpectralMeasure = volume.withDensity fun ξ => ENNReal.ofReal (arithmeticDensity ξ) := rfl

theorem FullAudit32_audit_arithmeticStieltjes (κ : ℂ) :
    arithmeticStieltjes κ = ∫ ξ, ((spectralEnergy ξ : ℂ) - κ)⁻¹ ∂arithmeticSpectralMeasure := rfl

theorem FullAudit32_audit_spectralResolventSet : spectralResolventSet = {κ : ℂ | κ.im ≠ 0 ∨ κ.re < 1 / 4} := rfl

/-! ### Restated roots -/

theorem expected_arithmetic_stieltjes_holomorphic :
    spectralResolventSet = ((↑) '' Ici (1 / 4 : ℝ) : Set ℂ)ᶜ ∧
    IsOpen spectralResolventSet ∧
    (∀ ξ, 0 ≤ arithmeticDensity ξ) ∧
    Integrable (fun ξ => (spectralEnergy ξ)⁻¹) arithmeticSpectralMeasure ∧
    ∫ ξ, (spectralEnergy ξ)⁻¹ ∂arithmeticSpectralMeasure =
      Real.log (2 * π) - Real.eulerMascheroniConstant ∧
    (∀ κ₀ ∈ spectralResolventSet, ∃ ε > 0, ∃ C : ℝ, ∀ κ ∈ Metric.ball κ₀ ε, ∀ ξ,
      ‖((spectralEnergy ξ : ℂ) - κ)⁻¹‖ ≤ C * (spectralEnergy ξ)⁻¹) ∧
    (∀ κ ∈ spectralResolventSet,
      Integrable (fun ξ => ((spectralEnergy ξ : ℂ) - κ)⁻¹) arithmeticSpectralMeasure) ∧
    (∀ κ ∈ spectralResolventSet, HasDerivAt arithmeticStieltjes
      (∫ ξ, (((spectralEnergy ξ : ℂ) - κ) ^ 2)⁻¹ ∂arithmeticSpectralMeasure) κ) ∧
    DifferentiableOn ℂ arithmeticStieltjes spectralResolventSet :=
  arithmetic_stieltjes_holomorphic

theorem expected_arithmetic_stieltjes_sign_budget {κ : ℂ} (hκ : κ.im ≠ 0) :
    Integrable (fun ξ => (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹) arithmeticSpectralMeasure ∧
    (arithmeticStieltjes κ).im / κ.im =
      ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    0 < ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ∧
    ‖arithmeticStieltjes κ‖ ≤
      (1 + ‖κ‖ / |κ.im|) * (Real.log (2 * π) - Real.eulerMascheroniConstant) ∧
    ∫ ξ, (‖(spectralEnergy ξ : ℂ) - κ‖ ^ 2)⁻¹ ∂arithmeticSpectralMeasure ≤
      (1 + ‖κ‖ / |κ.im|) * (Real.log (2 * π) - Real.eulerMascheroniConstant) / |κ.im| :=
  arithmetic_stieltjes_sign_budget hκ

/-! ### Domain consumers -/

/-- The weighted moment of ω is the source norm ‖w‖₂² of the actual F1 sawtooth weight. -/
theorem FullAudit32_expected_moment_is_source_norm :
    ∫ ξ, (spectralEnergy ξ)⁻¹ ∂arithmeticSpectralMeasure = ∫ t, ‖sawtoothWeight t‖ ^ 2 := by
  rw [arithmetic_stieltjes_holomorphic.2.2.2.2.1, sawtooth_weighted_zeta_moment.2.1]

/-- At the real resolvent point κ = -1 the Stieltjes value is real and positive. -/
theorem FullAudit32_expected_real_point :
    (arithmeticStieltjes (-1)).im = 0 ∧ 0 < (arithmeticStieltjes (-1)).re := by
  have hR : (-1 : ℂ) ∈ spectralResolventSet := Or.inr (by norm_num)
  have hI := arithmetic_stieltjes_holomorphic.2.2.2.2.2.2.1 (-1) hR
  have hpt : ∀ ξ, ((spectralEnergy ξ : ℂ) - (-1))⁻¹ = (((spectralEnergy ξ + 1)⁻¹ : ℝ) : ℂ) := by
    intro ξ; push_cast; ring
  have hIr : Integrable (fun ξ => (spectralEnergy ξ + 1)⁻¹) arithmeticSpectralMeasure := by
    have := hI.norm
    refine this.congr (Eventually.of_forall fun ξ => ?_)
    simp only [hpt, Complex.norm_real, Real.norm_eq_abs]
    exact abs_of_pos (inv_pos.mpr (by linarith [spectralEnergy_pos ξ]))
  have hM : arithmeticStieltjes (-1) =
      ((∫ ξ, (spectralEnergy ξ + 1)⁻¹ ∂arithmeticSpectralMeasure : ℝ) : ℂ) := by
    rw [arithmeticStieltjes, ← integral_complex_ofReal]
    exact integral_congr_ae (Eventually.of_forall fun ξ => hpt ξ)
  have hpos : 0 < ∫ ξ, (spectralEnergy ξ + 1)⁻¹ ∂arithmeticSpectralMeasure := by
    rw [integral_pos_iff_support_of_nonneg (fun ξ => (inv_pos.mpr
      (by linarith [spectralEnergy_pos ξ])).le) hIr]
    have hs : Function.support (fun ξ => (spectralEnergy ξ + 1)⁻¹) = univ := by
      ext ξ
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (inv_pos.mpr (by linarith [spectralEnergy_pos ξ])).ne'
    rw [hs]
    exact arithmeticSpectralMeasure_univ_pos
  rw [hM]
  exact ⟨Complex.ofReal_im _, by rw [Complex.ofReal_re]; exact hpos⟩

/-- At κ = i: Im M(i) > 0 and |M(i)| ≤ 2(log(2π) - γ). -/
theorem FullAudit32_expected_point_i :
    0 < (arithmeticStieltjes I).im ∧
    ‖arithmeticStieltjes I‖ ≤ 2 * (Real.log (2 * π) - Real.eulerMascheroniConstant) := by
  obtain ⟨-, h1, h2, h3, -⟩ := arithmetic_stieltjes_sign_budget (κ := I) (by simp)
  simp only [Complex.I_im, div_one, Complex.norm_I, abs_one] at h1 h3
  refine ⟨h1 ▸ h2, ?_⟩
  linarith

/-- An off-line strip parameter has Im κ ≠ 0, so κ = ρ(1 - ρ) is in the resolvent set and both
roots apply; Im κ = (1 - 2 Re ρ) Im ρ. -/
theorem FullAudit32_expected_offline_parameter {ρ : ℂ} (hre : ρ.re ≠ 1 / 2) (him : ρ.im ≠ 0) :
    ((ρ * (1 - ρ))).im = (1 - 2 * ρ.re) * ρ.im ∧ ((ρ * (1 - ρ))).im ≠ 0 ∧
    (ρ * (1 - ρ)) ∈ spectralResolventSet ∧
    DifferentiableAt ℂ arithmeticStieltjes ((ρ * (1 - ρ))) ∧
    0 < (arithmeticStieltjes ((ρ * (1 - ρ)))).im / ((ρ * (1 - ρ))).im := by
  have hk : ((ρ * (1 - ρ))).im = (1 - 2 * ρ.re) * ρ.im := by
    simp only [Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im]
    ring
  have hne : ((ρ * (1 - ρ))).im ≠ 0 := by
    rw [hk]
    exact mul_ne_zero (fun h => hre (by linarith)) him
  have hR : (ρ * (1 - ρ)) ∈ spectralResolventSet := Or.inl hne
  obtain ⟨-, h1, h2, -⟩ := arithmetic_stieltjes_sign_budget hne
  exact ⟨hk, hne, hR, (arithmetic_stieltjes_holomorphic.2.2.2.2.2.2.2.1 _ hR).differentiableAt,
    h1 ▸ h2⟩

/-- A critical-line parameter has real κ = 1/4 + (Im ρ)² on the cut [1/4, ∞): it is outside the
resolvent set, where neither root is asserted. -/
theorem FullAudit32_expected_critical_line_on_cut {ρ : ℂ} (hre : ρ.re = 1 / 2) :
    (ρ * (1 - ρ)) = ((1 / 4 + ρ.im ^ 2 : ℝ) : ℂ) ∧ (ρ * (1 - ρ)) ∉ spectralResolventSet := by
  have hρ : ρ = (1 / 2 : ℂ) + (ρ.im : ℂ) * I := by
    apply Complex.ext <;> simp [hre]
  have hk : (ρ * (1 - ρ)) = ((1 / 4 + ρ.im ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [hρ]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  refine ⟨hk, ?_⟩
  rw [spectralResolventSet_eq, hk, Set.notMem_compl_iff]
  exact ⟨_, by simp only [mem_Ici]; nlinarith [sq_nonneg ρ.im], rfl⟩

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedWordJet.lean; SHA256 3c14d4f76bdb72d8b5d5715bae34081b7381743433f510da6e8e53f8b4baaa80 -/
section

/-!
Independent expected-type and actual-domain consumers for the original root
`Zeta23.OPICAFollowup.step123_word_jet_consumer` (R1-NB1, R2-J1).

The 22 conclusion clauses are restated below with every `let` of the source
statement expanded, so no abbreviation can hide a weaker conclusion. The domain
consumer instantiates the root on outputs produced by the parent constructor
`exists_generatedStep123CompleteOutput` for every admissible off-line zero,
damping, phase, horizon, word and unrestricted history. No contour premise or
continuation-domain certificate is added.
-/

noncomputable section
open Complex Set MeasureTheory Filter Metric
open scoped Topology
open Zeta23 Zeta23.CCM Zeta23.ExceptionalZero Zeta23.OPICA

namespace Zeta23.OPICAFollowup.Validation
/-- Independent restatement of the complete same-output word/jet conclusion. -/
def FullAudit33_WordJetConclusion {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late)
    (w : Zeta23.OPICAFollowup.NativeWord)
    (history : Zeta23.OPICAFollowup.NativeWordHistory
      ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2)) : Prop :=
  (Zeta23.OPICA.step123OpicaView out).source = nativeOriginalIntegerDrive ∧
  (Zeta23.OPICA.step123OpicaView out).field = nativeOriginalPrimeField ∧
  (Zeta23.OPICA.step123OpicaView out).input = nativeCompletedInput ∧
  Step123SameStateFieldRecord out.generated.native ∧
  GeneratedStep123RangeObstruction rho out.generated.offLine ∧
  zeroMult (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) = zeroMult (rho : ℂ) ∧
  nativeZeroJetParameter rho + (nativeZeroJetDamping rho : ℂ) =
    (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2 ∧
  0 < nativeZeroJetDamping rho ∧
  (Zeta23.OPICAFollowup.nativeWordPrimePole (Zeta23.OPICAFollowup.step123WordRightZero out)
    (Zeta23.OPICAFollowup.step123WordRightZero_right out)).source = nativeOriginalSource ∧
  (Zeta23.OPICAFollowup.nativeWordPrimePole (Zeta23.OPICAFollowup.step123WordRightZero out)
    (Zeta23.OPICAFollowup.step123WordRightZero_right out)).center =
      (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2 ∧
  (Zeta23.OPICAFollowup.nativeWordPrimePole (Zeta23.OPICAFollowup.step123WordRightZero out)
    (Zeta23.OPICAFollowup.step123WordRightZero_right out)).field =
      Zeta23.OPICAFollowup.nativePrimeTransformGerm ∧
  (Zeta23.OPICAFollowup.nativeWordPrimePole (Zeta23.OPICAFollowup.step123WordRightZero out)
    (Zeta23.OPICAFollowup.step123WordRightZero_right out)).residue =
      -(zeroMult (rho : ℂ) : ℂ) * nativeOriginalSourceLaplace
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) ∧
  (∃ S : ℝ, Zeta23.OPICAFollowup.wordHistorySafeThreshold w history ≤ S ∧ 1/2 ≤ S ∧
    ∀ z : ℂ, S < z.re →
      (∀ term ∈ Zeta23.OPICAFollowup.nativeWordCausalState w
          (Zeta23.OPICAFollowup.step123WordRightZero out) history,
        Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * term.regular t)) ∧
      (Zeta23.OPICAFollowup.nativeWordCausalState w
          (Zeta23.OPICAFollowup.step123WordRightZero out) history).laplace z =
        Zeta23.OPICAFollowup.nativeWordTransformedField w
          (Zeta23.OPICAFollowup.step123WordRightZero out) history z) ∧
  MeromorphicAt (Zeta23.OPICAFollowup.nativeWordTransformedField w
      (Zeta23.OPICAFollowup.step123WordRightZero out) history)
    ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) ∧
  (∀ z : ℂ, Zeta23.OPICAFollowup.nativeWordCorrectedField w
      (Zeta23.OPICAFollowup.step123WordRightZero out) history z =
    Zeta23.OPICAFollowup.wordUnitFactor w z * riemannZeta (z + 1/2) ^
      Zeta23.OPICAFollowup.wordCompletionCount w *
        Zeta23.OPICAFollowup.nativePrimeTransformGerm z) ∧
  meromorphicOrderAt (Zeta23.OPICAFollowup.nativeWordCorrectedField w
      (Zeta23.OPICAFollowup.step123WordRightZero out) history)
    ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) =
    (((Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) : ℕ) : ℤ) - 1 : ℤ) ∧
  Zeta23.OPICAFollowup.nativeWordLeadingCoefficient w
      (Zeta23.OPICAFollowup.step123WordRightZero out) =
    -(zeroMult (rho : ℂ) : ℂ) * nativeOriginalSourceLaplace
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) *
      Zeta23.OPICAFollowup.wordUnitFactor w
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) *
      (iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta
          (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) /
        ((zeroMult (rho : ℂ)).factorial : ℂ)) ^ Zeta23.OPICAFollowup.wordCompletionCount w ∧
  Zeta23.OPICAFollowup.nativeWordLeadingCoefficient w
      (Zeta23.OPICAFollowup.step123WordRightZero out) ≠ 0 ∧
  Tendsto (fun z => (z - ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2)) ^
      (-(((Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) : ℕ) : ℤ) - 1)) *
      Zeta23.OPICAFollowup.nativeWordCorrectedField w
        (Zeta23.OPICAFollowup.step123WordRightZero out) history z)
    (𝓝[≠] ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2))
    (𝓝 (Zeta23.OPICAFollowup.nativeWordLeadingCoefficient w
      (Zeta23.OPICAFollowup.step123WordRightZero out))) ∧
  (0 < Zeta23.OPICAFollowup.wordCompletionCount w →
    (Zeta23.OPICAFollowup.nativeWordCorrectedField w
        (Zeta23.OPICAFollowup.step123WordRightZero out) history =ᶠ[𝓝[≠]
          ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2)]
      Zeta23.OPICAFollowup.nativeWordRegularRepresentative w
        (Zeta23.OPICAFollowup.step123WordRightZero out)
        (Zeta23.OPICAFollowup.step123WordRightZero_right out)) ∧
    AnalyticAt ℂ (Zeta23.OPICAFollowup.nativeWordRegularRepresentative w
        (Zeta23.OPICAFollowup.step123WordRightZero out)
        (Zeta23.OPICAFollowup.step123WordRightZero_right out))
      ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) ∧
    (∀ j : ℕ, j < Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) - 1 →
      iteratedDeriv j (Zeta23.OPICAFollowup.nativeWordRegularRepresentative w
          (Zeta23.OPICAFollowup.step123WordRightZero out)
          (Zeta23.OPICAFollowup.step123WordRightZero_right out))
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) = 0) ∧
    iteratedDeriv (Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) - 1)
        (Zeta23.OPICAFollowup.nativeWordRegularRepresentative w
          (Zeta23.OPICAFollowup.step123WordRightZero out)
          (Zeta23.OPICAFollowup.step123WordRightZero_right out))
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) =
      ((Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) - 1).factorial : ℂ) *
        Zeta23.OPICAFollowup.nativeWordLeadingCoefficient w
          (Zeta23.OPICAFollowup.step123WordRightZero out) ∧
    iteratedDeriv (Zeta23.OPICAFollowup.wordCompletionCount w * zeroMult (rho : ℂ) - 1)
        (Zeta23.OPICAFollowup.nativeWordRegularRepresentative w
          (Zeta23.OPICAFollowup.step123WordRightZero out)
          (Zeta23.OPICAFollowup.step123WordRightZero_right out))
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) ≠ 0) ∧
  inner ℂ (nativeZeroJetAdjointWitness rho out.generated.offLine)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho out.generated.offLine).le) =
    (-1 : ℂ) ^ zeroMult (rho : ℂ) * nativeCompletionRationalMultiplier
        ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) *
      nativeOriginalSourceLaplace ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2) *
        iteratedDeriv (zeroMult (rho : ℂ)) riemannZeta
          (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) ∧
  inner ℂ (nativeZeroJetAdjointWitness rho out.generated.offLine)
      (nativeCompletedInputCausalL2 (nativeZeroJetDamping rho)
        (nativeZeroJetDamping_pos rho out.generated.offLine).le) ≠ 0

/-- Expected type: the root proves exactly the independently restated
conclusion for every existing output, word and unrestricted history. -/
theorem expected_step123_word_jet_consumer {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late)
    (w : Zeta23.OPICAFollowup.NativeWord)
    (history : Zeta23.OPICAFollowup.NativeWordHistory
      ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2)) :
    FullAudit33_WordJetConclusion out w history :=
  Zeta23.OPICAFollowup.step123_word_jet_consumer out w history

/-- Actual-domain consumer: for every zero, admissible damping, phase and
horizon, the parent constructor supplies a genuine same-state output whose
threshold is paid, and the full conclusion holds for every word and history. -/
theorem FullAudit33_expected_step123_word_jet_actual_domain (rho : zetaZeroConfig.carrier) {beta : ℝ}
    (hbeta : 0 < beta) (hbetarho : beta < |(rho : ℂ).re - 1 / 2|)
    (phase : ReversalParity) (late : ℝ) (w : Zeta23.OPICAFollowup.NativeWord) :
    ∃ out : GeneratedStep123CompleteOutput rho beta phase late,
      max late step123SameStateThreshold <
          fixedOriginalSincTrialAperture out.generated.sourceData.separation ∧
        ∀ history : Zeta23.OPICAFollowup.NativeWordHistory
            ((Zeta23.OPICAFollowup.step123WordRightZero out : ℂ) - 1/2),
          FullAudit33_WordJetConclusion out w history := by
  obtain ⟨out, hpaid⟩ :=
    exists_eachPhase_cofinal_generatedStep123CompleteOutput rho hbeta hbetarho phase late
  exact ⟨out, hpaid, fun history => expected_step123_word_jet_consumer out w history⟩

/-- The selected right zero is genuinely to the right of the critical line. -/
theorem FullAudit33_expected_step123_word_right_zero {rho : zetaZeroConfig.carrier} {beta : ℝ}
    {phase : ReversalParity} {late : ℝ}
    (out : GeneratedStep123CompleteOutput rho beta phase late) :
    1/2 < (Zeta23.OPICAFollowup.step123WordRightZero out : ℂ).re :=
  Zeta23.OPICAFollowup.step123WordRightZero_right out

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedZeroMeasure.lean; SHA256 01f2f5d3c22aedcae2a3ec06b403129c78b7c76bf89b5673cd3b3e28968e9fe7 -/
section

/- Independent consumers for the original R1-CP1 root
`Zeta23.OPICAFollowup.zero_measure_exact_properties`.

Definition audits pin b_ρ, κ, the punctured lattice and the four canonical Jordan parts of the
normalized zero measure. The root is restated in full. Domain consumers check:
- the real part η_ρ satisfies the parent H1 predicates `HasUnitGap`, `FourierSelfdual` and
  `HasLinearGrowth` (Zeta23.OPICA.SignedHeatSeparator);
- the atom at -1 is also -1 (evenness);
- for every ρ = 1/2 + δ + iγ with |γ| > 3π/(2 log 2) (in particular every actual zero above that
  height), η_ρ is NOT off-lattice nonnegative: its negative part has positive mass on an open
  subinterval of (1, 2) (the first-cell sign root plus continuity of the first-cell density).
  At such an actual zero η_ρ therefore supplies every H1 hypothesis except off-lattice
  nonnegativity, as the paper states;
- the construction-level clauses that do not use ζ(ρ) = 0 are non-vacuous at ρ = 3/4. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ENNReal
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit34_audit_brho (ρ : ℂ) : normalizationBrho ρ = (1 - 2 * ρ) / (ρ * (1 - ρ)) := rfl

theorem FullAudit34_audit_kappa (ρ : ℂ) : coPoissonKappa ρ = ρ * (1 - ρ) := rfl

theorem FullAudit34_audit_lattice : puncturedLattice = (dilatedCombMeasure 0).restrict {0}ᶜ := rfl

theorem FullAudit34_audit_parts (ρ : ℂ) :
    (zeroMeasure ρ).rePart.positive =
      volume.withDensity (fun x => ENNReal.ofReal (coPoissonComplexDensity ρ x).re) ∧
    (zeroMeasure ρ).rePart.negative =
      volume.withDensity (fun x => ENNReal.ofReal (-(coPoissonComplexDensity ρ x).re)) +
        puncturedLattice ∧
    (zeroMeasure ρ).imPart.positive =
      volume.withDensity (fun x => ENNReal.ofReal (coPoissonComplexDensity ρ x).im) ∧
    (zeroMeasure ρ).imPart.negative =
      volume.withDensity (fun x => ENNReal.ofReal (-(coPoissonComplexDensity ρ x).im)) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem FullAudit34_audit_density (ρ : ℂ) (x : ℝ) :
    coPoissonComplexDensity ρ x = coPoissonPowerSums ρ |x| / (1 / ρ - 1 / (1 - ρ)) := rfl

/-! ### Restated root -/

theorem expected_zero_measure_exact_properties (ρ : ℂ) (hz : riemannZeta ρ = 0)
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    normalizationBrho ρ = (1 - 2 * ρ) / coPoissonKappa ρ ∧
    normalizationBrho ρ = 1 / ρ - 1 / (1 - ρ) ∧ normalizationBrho ρ ≠ 0 ∧
    (∀ φ : 𝓢(ℝ, ℂ), (zeroMeasure ρ).integral φ =
      (coPoissonFamily (ρ - 1 / 2) φ - 1 / (1 - ρ) * (φ 0 + ∫ x, φ x) -
        normalizationBrho ρ * dilatedCombDistribution 0 φ) / normalizationBrho ρ) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (zeroMeasure ρ).integral φ =
      (∫ x, coPoissonComplexDensity ρ x * φ x) - ∑' n : ℤ, if n = 0 then (0 : ℂ) else φ n) ∧
    (zeroMeasure ρ).HasLinearGrowth ∧
    𝓕 ((zeroMeasure ρ).distributionOfLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1)) =
      (zeroMeasure ρ).distributionOfLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1) ∧
    (Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).rePart.positive = (zeroMeasure ρ).rePart.positive ∧
      Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).rePart.negative = (zeroMeasure ρ).rePart.negative ∧
      Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).imPart.positive = (zeroMeasure ρ).imPart.positive ∧
      Measure.map (fun x : ℝ => -x) (zeroMeasure ρ).imPart.negative =
        (zeroMeasure ρ).imPart.negative) ∧
    (zeroMeasure ρ).variationControl (Ioo (-1) 1) = 0 ∧
    (zeroMeasure ρ).variationControl {0} = 0 ∧
    ((zeroMeasure ρ).rePart.positive {1} = 0 ∧ (zeroMeasure ρ).rePart.negative {1} = 1 ∧
      (zeroMeasure ρ).imPart.positive {1} = 0 ∧ (zeroMeasure ρ).imPart.negative {1} = 0) ∧
    ((zeroMeasure ρ).rePart.positive =
        volume.withDensity (fun x => ENNReal.ofReal (coPoissonRealDensity ρ x)) ∧
      (zeroMeasure ρ).rePart.negative =
        volume.withDensity (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) + puncturedLattice) ∧
    (zeroMeasure ρ).rePart.HasLinearGrowth ∧
    𝓕 ((zeroMeasure ρ).rePart.distributionOfLinearGrowth
        ((zeroMeasure ρ).re_hasLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1))) =
      (zeroMeasure ρ).rePart.distributionOfLinearGrowth
        ((zeroMeasure ρ).re_hasLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1)) ∧
    ((zeroMeasure ρ).rePart.positive (Ioo (-1) 1) = 0 ∧
      (zeroMeasure ρ).rePart.negative (Ioo (-1) 1) = 0) ∧
    ((zeroMeasure ρ).rePart.positive {0} = 0 ∧ (zeroMeasure ρ).rePart.negative {0} = 0) ∧
    ((zeroMeasure ρ).rePart.positive.real {1} = 0 ∧ (zeroMeasure ρ).rePart.negative.real {1} = 1) ∧
    (zeroMeasure ρ).rePart.negative ≠ 0 :=
  zero_measure_exact_properties ρ hz h0 h1 hh

/-! ### Domain consumers -/

/-- η_ρ satisfies the parent H1 predicates: exact unit gap, Fourier self-duality and linear growth. -/
theorem FullAudit34_expected_real_part_H1_hypotheses (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    (zeroMeasure ρ).rePart.HasUnitGap ∧
      (zeroMeasure ρ).rePart.FourierSelfdual
        ((zeroMeasure ρ).re_hasLinearGrowth (zeroMeasure_hasLinearGrowth h0 h1)) ∧
      (zeroMeasure ρ).rePart.HasLinearGrowth := by
  have h := zero_measure_exact_properties ρ hz h0 h1 hh
  exact ⟨h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.2.1⟩

/-- Evenness moves the atom -1 at 1 to an atom -1 at -1. -/
theorem FullAudit34_expected_atom_minus_one (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) (hh : ρ ≠ 1 / 2) :
    (zeroMeasure ρ).rePart.negative {-1} = 1 ∧ (zeroMeasure ρ).rePart.positive {-1} = 0 := by
  have h := zero_measure_exact_properties ρ hz h0 h1 hh
  obtain ⟨hp, hn, -, -⟩ := h.2.2.2.2.2.2.2.1
  obtain ⟨a1, a2, -, -⟩ := h.2.2.2.2.2.2.2.2.2.2.1
  have hpre : (fun x : ℝ => -x) ⁻¹' ({-1} : Set ℝ) = {1} := by ext x; simp
  constructor
  · rw [← hn, Measure.map_apply measurable_neg (measurableSet_singleton _), hpre, a2]
  · rw [← hp, Measure.map_apply measurable_neg (measurableSet_singleton _), hpre, a1]

/-- The first-cell density is continuous on (1, 2). -/
lemma FullAudit34_first_cell_density_continuousOn (ρ : ℂ) :
    ContinuousOn (coPoissonRealDensity ρ) (Ioo (1 : ℝ) 2) := by
  have heq : EqOn (coPoissonRealDensity ρ)
      (fun x : ℝ => (((x : ℂ) ^ (-ρ) - (x : ℂ) ^ (ρ - 1)) / coPoissonOriginNormalizer ρ).re)
      (Ioo (1 : ℝ) 2) := by
    intro x hx
    have hx0 : 0 ≤ x := zero_le_one.trans hx.1.le
    simp only [coPoissonRealDensity, coPoissonComplexDensity, abs_of_nonneg hx0,
      coPoisson_first_cell_sum ρ hx]
  refine ContinuousOn.congr ?_ heq
  intro x hx
  have hx0 : 0 < x := zero_lt_one.trans hx.1
  have hs : (x : ℂ) ∈ slitPlane := Complex.ofReal_mem_slitPlane.mpr hx0
  refine (Complex.continuous_re.continuousAt.comp ?_).continuousWithinAt
  refine ContinuousAt.div_const (ContinuousAt.sub ?_ ?_) _
  · exact (continuousAt_cpow_const hs).comp Complex.continuous_ofReal.continuousAt
  · exact (continuousAt_cpow_const hs).comp Complex.continuous_ofReal.continuousAt

/-- Above the first-cell height η_ρ is not off-lattice nonnegative (no zero hypothesis needed). -/
theorem FullAudit34_expected_not_offlattice_nonnegative (δ γ : ℝ)
    (hheight : 3 * Real.pi / (2 * Real.log 2) < |γ|) :
    ¬ (zeroMeasure (coPoissonRho δ γ)).rePart.OffLatticeNonnegative := by
  intro hnn
  obtain ⟨hu, hu1, -, hneg⟩ := (zero_measure_first_cell_sign δ γ hheight).1
  set ρ := coPoissonRho δ γ with hρ
  set u := 3 * Real.pi / (2 * |γ|) with hudef
  have hx : Real.exp u ∈ Ioo (1 : ℝ) 2 := ⟨Real.one_lt_exp_iff.mpr hu,
    (Real.exp_lt_exp.mpr hu1).trans_eq (Real.exp_log (by norm_num))⟩
  set U : Set ℝ := Ioo (1 : ℝ) 2 ∩ coPoissonRealDensity ρ ⁻¹' Iio 0 with hU
  have hUopen : IsOpen U :=
    (FullAudit34_first_cell_density_continuousOn ρ).isOpen_inter_preimage isOpen_Ioo isOpen_Iio
  have hUmem : Real.exp u ∈ U := ⟨hx, hneg⟩
  have hUpos : 0 < volume U := hUopen.measure_pos volume ⟨_, hUmem⟩
  have hUlat : U ⊆ Zeta23.OPICA.integerLatticeᶜ := by
    rintro x ⟨hx1, -⟩ ⟨n, rfl⟩
    have h1 : (1 : ℝ) < n := hx1.1
    have h2 : (n : ℝ) < 2 := hx1.2
    have h1' : (1 : ℤ) < n := by exact_mod_cast h1
    have h2' : n < (2 : ℤ) := by exact_mod_cast h2
    omega
  have hfm : Measurable (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) :=
    ENNReal.measurable_ofReal.comp (Complex.measurable_re.comp
      (measurable_coPoissonComplexDensity ρ)).neg
  have hmass : 0 < volume.withDensity (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) U := by
    rw [withDensity_apply _ hUopen.measurableSet, setLIntegral_pos_iff hfm]
    have hsub : U ⊆ Function.support (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) ∩ U :=
      fun x hx => ⟨by
        simp only [Function.mem_support, ne_eq, ENNReal.ofReal_eq_zero, not_le]
        have : coPoissonRealDensity ρ x < 0 := hx.2
        linarith, hx⟩
    exact hUpos.trans_le (measure_mono hsub)
  have hzero : (zeroMeasure ρ).rePart.negative Zeta23.OPICA.integerLatticeᶜ = 0 := hnn
  change (volume.withDensity (fun x => ENNReal.ofReal (-coPoissonRealDensity ρ x)) +
    puncturedLattice) Zeta23.OPICA.integerLatticeᶜ = 0 at hzero
  rw [Measure.add_apply, add_eq_zero] at hzero
  have := (measure_mono hUlat).trans_eq hzero.1
  exact absurd hmass (not_lt.mpr this)

/-- Non-vacuity of the construction-level clauses (they do not use ζ(ρ) = 0). -/
theorem FullAudit34_expected_construction_nonvacuous :
    (zeroMeasure (3 / 4)).HasLinearGrowth ∧
      (zeroMeasure (3 / 4)).variationControl (Ioo (-1) 1) = 0 ∧
      (zeroMeasure (3 / 4)).rePart.negative {1} = 1 :=
  ⟨zeroMeasure_hasLinearGrowth (by norm_num) (by norm_num), zeroMeasure_gap _,
    (zeroMeasure_atom_one _).2.1⟩

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: research/RHRC/integration/opica_followup/continuation/2026-10-22/consumers/ExpectedZeroProfiles.lean; SHA256 33ad11294eda85f3b5b3bddb83287e5208ed4bb965d574e42c227ec0ef74a485 -/
section

/- Independent consumers for the original roots `Zeta23.OPICAFollowup.zero_profile_regular_selfdual`
and `Zeta23.OPICAFollowup.zero_profile_tail_and_jumps` (R2-S1a).

Definition audits pin κ = ρ(1 - ρ) and h = 1 - S_ρ(|x|)/b_ρ to the actual CP1 finite sums and
normalization. Both roots are restated in full. Domain consumers check:
- h is one minus the actual zero-measure density on the whole line;
- h(0) = ∫ h = 𝓕h(0) = 1 (Fourier inversion at the origin is consistent);
- the one-sided derivatives in the jump clause are unique, so the clause is not vacuous;
- the lattice values h(n) are absolutely summable (paper: absolute convergence of Σ h(n));
- the construction-level clauses (continuity, evenness, h = 1 on [-1, 1], exact cell
  derivatives and the jump formula) hold at the non-zero parameter ρ = 3/4. The zero-dependent
  clauses need an actual zero, which Mathlib cannot exhibit. -/
noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap
open Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation
/-! ### Definition audits -/

theorem FullAudit35_audit_spectralKappa (ρ : ℂ) : spectralKappa ρ = ρ * (1 - ρ) := rfl

theorem FullAudit35_audit_zeroProfile (ρ : ℂ) (x : ℝ) :
    zeroProfile ρ x = 1 - finiteSumSrho ρ |x| / normalizationBrho ρ := rfl

theorem FullAudit35_audit_srhoCellDeriv (ρ : ℂ) (n : ℕ) (y : ℝ) : srhoCellDeriv ρ n y =
    -ρ * (y : ℂ) ^ (-ρ - 1) * ∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (ρ - 1) -
      (ρ - 1) * (y : ℂ) ^ (ρ - 1 - 1) * ∑ k ∈ Finset.Icc 1 n, (k : ℂ) ^ (-ρ) := rfl

/-! ### Restated roots -/

theorem expected_zero_profile_regular_selfdual (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    (∀ x : ℝ, zeroProfile ρ (-x) = zeroProfile ρ x) ∧
    Continuous (zeroProfile ρ) ∧
    Integrable (zeroProfile ρ) ∧ MemLp (zeroProfile ρ) 2 ∧
    (∀ x : ℝ, |x| ≤ 1 → zeroProfile ρ x = 1) ∧
    𝓕 (zeroProfile ρ) = zeroProfile ρ ∧
    (∀ φ : 𝓢(ℝ, ℂ), (∫ x, zeroProfile ρ x * (𝓕 φ : 𝓢(ℝ, ℂ)) x) = ∫ x, zeroProfile ρ x * φ x) ∧
    (∀ φ : 𝓢(ℝ, ℂ), (zeroMeasure ρ).integral φ =
      (∫ x, φ x) + φ 0 - dilatedCombDistribution 0 φ - ∫ x, zeroProfile ρ x * φ x) ∧
    (∫ x, zeroProfile ρ x) = 1 ∧
    (∫ x in Ioi (0 : ℝ), zeroProfile ρ x) = 1 / 2 :=
  zero_profile_regular_selfdual ρ hz h0 h1

theorem expected_zero_profile_tail_and_jumps (ρ : ℂ) (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) :
    (∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ |x| →
      ‖zeroProfile ρ x - spectralKappa ρ * (bernoulliTwo |x| : ℂ) / (2 * ((|x| : ℝ) : ℂ) ^ 2)‖ ≤
        C * |x| ^ (-3 : ℝ)) ∧
    (∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) →
      HasDerivAt (zeroProfile ρ) (-(srhoCellDeriv ρ n x / normalizationBrho ρ)) x) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) → 1 ≤ x →
      ‖deriv (zeroProfile ρ) x‖ ≤ C * x ^ (-2 : ℝ)) ∧
    (∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) → 1 ≤ x →
      ‖deriv (zeroProfile ρ) x - spectralKappa ρ * (bernoulliOneRight x : ℂ) / (x : ℂ) ^ 2‖ ≤
        C * x ^ (-4 : ℝ)) ∧
    (∀ n : ℕ, ∃ dR dL : ℂ,
      HasDerivWithinAt (zeroProfile ρ) dR (Ici ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) ∧
      HasDerivWithinAt (zeroProfile ρ) dL (Iic ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ) ∧
      dR - dL = -spectralKappa ρ / ((n + 1 : ℕ) : ℂ) ^ 2) ∧
    HasDerivWithinAt (zeroProfile ρ) 0 (Iic (1 : ℝ)) 1 ∧
    MemLp (fun x : ℝ => (x : ℂ) * deriv (zeroProfile ρ) x) 2 (volume.restrict (Ioi 0)) :=
  zero_profile_tail_and_jumps ρ hz h0 h1

/-! ### Domain consumers -/

/-- h is one minus the density of the actual normalized zero measure on the whole line. -/
theorem FullAudit35_expected_profile_is_one_minus_zero_density {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (x : ℝ) : zeroProfile ρ x = 1 - coPoissonComplexDensity ρ x := by
  have hρ0 : ρ ≠ 0 := fun h => by rw [h] at h0; simp at h0
  have hρ1 : ρ ≠ 1 := fun h => by rw [h] at h1; simp at h1
  unfold zeroProfile coPoissonComplexDensity
  rw [coPoissonOriginNormalizer_eq_brho hρ0 hρ1]

/-- h(0) = ∫ h = 𝓕h(0) = 1. -/
theorem FullAudit35_expected_origin_value {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    zeroProfile ρ 0 = 1 ∧ 𝓕 (zeroProfile ρ) 0 = 1 ∧ ∫ x, zeroProfile ρ x = 1 := by
  obtain ⟨-, -, -, -, hone, hF, -, -, hint, -⟩ := zero_profile_regular_selfdual ρ hz h0 h1
  have h00 : zeroProfile ρ 0 = 1 := hone 0 (by simp)
  exact ⟨h00, by rw [hF, h00], hint⟩

/-- The one-sided derivatives of the jump clause are unique: any right and left derivatives at
n + 1 satisfy the jump identity. -/
theorem FullAudit35_expected_jump_unique {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (n : ℕ) (dR dL : ℂ)
    (hR : HasDerivWithinAt (zeroProfile ρ) dR (Ici ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ))
    (hL : HasDerivWithinAt (zeroProfile ρ) dL (Iic ((n + 1 : ℕ) : ℝ)) ((n + 1 : ℕ) : ℝ)) :
    dR - dL = -spectralKappa ρ / ((n + 1 : ℕ) : ℂ) ^ 2 := by
  obtain ⟨dR', dL', hR', hL', hj⟩ := (zero_profile_tail_and_jumps ρ hz h0 h1).2.2.2.2.1 n
  have e1 : dR = dR' := (uniqueDiffWithinAt_Ici _).eq_deriv _ hR hR'
  have e2 : dL = dL' := (uniqueDiffWithinAt_Iic _).eq_deriv _ hL hL'
  rw [e1, e2, hj]

/-- The lattice values h(n) are absolutely summable. -/
theorem FullAudit35_expected_lattice_values_summable {ρ : ℂ} (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re)
    (h1 : ρ.re < 1) : Summable (fun n : ℕ => ‖zeroProfile ρ n‖) := by
  obtain ⟨C, hC0, hC⟩ := (zero_profile_tail_and_jumps ρ hz h0 h1).1
  set M : ℝ := ‖spectralKappa ρ‖ / 2 + C
  have hsum : Summable (fun n : ℕ => M * ((n : ℝ) ^ 2)⁻¹) :=
    (Real.summable_nat_pow_inv.mpr (by norm_num)).mul_left M
  refine Summable.of_norm_bounded_eventually (g := fun n : ℕ => M * ((n : ℝ) ^ 2)⁻¹) hsum ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have habs : |(n : ℝ)| = n := abs_of_pos hn0
  have ht := hC n (by rw [habs]; exact hn1)
  rw [habs] at ht
  rw [norm_norm]
  have hB : abs (bernoulliTwo n) ≤ 1 := abs_bernoulliTwo_le _
  have hmain : ‖spectralKappa ρ * (bernoulliTwo n : ℂ) / (2 * ((n : ℝ) : ℂ) ^ 2)‖ ≤
      ‖spectralKappa ρ‖ / 2 * ((n : ℝ) ^ 2)⁻¹ := by
    rw [norm_div, norm_mul, norm_mul, norm_pow, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hn0]
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    rw [h2, div_le_iff₀ (by positivity)]
    calc ‖spectralKappa ρ‖ * abs (bernoulliTwo n) ≤ ‖spectralKappa ρ‖ * 1 :=
          mul_le_mul_of_nonneg_left hB (norm_nonneg _)
      _ = ‖spectralKappa ρ‖ / 2 * ((n : ℝ) ^ 2)⁻¹ * (2 * (n : ℝ) ^ 2) := by field_simp
  have h3 : (n : ℝ) ^ (-3 : ℝ) ≤ ((n : ℝ) ^ 2)⁻¹ := by
    rw [← Real.rpow_two, ← Real.rpow_neg hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  calc ‖zeroProfile ρ n‖ ≤ ‖spectralKappa ρ * (bernoulliTwo n : ℂ) / (2 * ((n : ℝ) : ℂ) ^ 2)‖ +
        ‖zeroProfile ρ n - spectralKappa ρ * (bernoulliTwo n : ℂ) / (2 * ((n : ℝ) : ℂ) ^ 2)‖ :=
        norm_le_insert' _ _
    _ ≤ ‖spectralKappa ρ‖ / 2 * ((n : ℝ) ^ 2)⁻¹ + C * ((n : ℝ) ^ 2)⁻¹ := by
        gcongr; exact ht.trans (mul_le_mul_of_nonneg_left h3 hC0)
    _ = M * ((n : ℝ) ^ 2)⁻¹ := by ring

/-- Construction-level non-vacuity at ρ = 3/4 (ζ(3/4) ≠ 0, so no zero hypothesis is used):
continuity, evenness, h = 1 on [-1, 1], exact cell derivatives and the jump -κ/n². -/
theorem FullAudit35_expected_construction_nonvacuous :
    Continuous (zeroProfile (3 / 4)) ∧ (∀ x, zeroProfile (3 / 4) (-x) = zeroProfile (3 / 4) x) ∧
    (∀ x : ℝ, |x| ≤ 1 → zeroProfile (3 / 4) x = 1) ∧
    (∀ (n : ℕ) (x : ℝ), x ∈ Ioo (n : ℝ) (n + 1) →
      HasDerivAt (zeroProfile (3 / 4)) (-(srhoCellDeriv (3 / 4) n x / normalizationBrho (3 / 4))) x) ∧
    (∀ n : ℕ, -(srhoCellDeriv (3 / 4) (n + 1) (n + 1 : ℕ) / normalizationBrho (3 / 4)) -
        -(srhoCellDeriv (3 / 4) n (n + 1 : ℕ) / normalizationBrho (3 / 4)) =
      -spectralKappa (3 / 4) / ((n + 1 : ℕ) : ℂ) ^ 2) :=
  ⟨continuous_zeroProfile _, zeroProfile_neg _, fun x hx => zeroProfile_eq_one _ hx,
    fun n x hx => hasDerivAt_zeroProfile_cell _ hx,
    fun n => zeroProfile_deriv_jump (by norm_num) (by norm_num) (by norm_num) n⟩

end Zeta23.OPICAFollowup.Validation

end
end

/- SOURCE COPY: ../audit-finite-span/ExpectedFullFiniteSpanFinal.lean; SHA256 e689cf4eeab75901e2e34c243ec91360dc93dd055816d8b78d76294d3fbc3905 -/
section
noncomputable section
open Set MeasureTheory Complex
open Zeta23.OPICA Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan

namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit36_full_original_domain_and_independent_basis :
    (∀ data : List (ℂ × ℂ × ℕ),
      ∀ h : ∀ j ∈ data, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
        j.2.2 < zeroJetOrder j.2.1,
      (Zeta23.OPICAFollowup.zeroJetRealSpan data).negative integerLatticeᶜ = 0 →
        (Zeta23.OPICAFollowup.zeroJetRealSpan data).positive = 0 ∧
          (Zeta23.OPICAFollowup.zeroJetRealSpan data).negative = 0) ∧
    (∀ n : ℕ, ∀ basis : Fin n → List (ℂ × ℂ × ℕ),
      ∀ h : ∀ i, ∀ j ∈ basis i, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
        j.2.2 < zeroJetOrder j.2.1,
      LinearIndependent ℝ (fun i =>
        (Zeta23.OPICAFollowup.zeroJetRealSpan (basis i)).distributionOfLinearGrowth
          (zeroJetRealSpan_growth _ (h i))) →
      ∀ a : Fin n → ℝ,
      (Zeta23.OPICAFollowup.zeroJetRealSpan (realBasisCombinationData basis a)).negative
        integerLatticeᶜ = 0 → a = 0) :=
  Zeta23.OPICAFollowup.finite_zero_span_positive_only_zero

end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: ../audit-finite-span/ExpectedActualFixedBudgetFinal.lean; SHA256 ab0f7c46f20835de6d9a2ba9b202a193f70bc782f8e3f1f2887163ddd2b0223b -/
section

noncomputable section
open Set MeasureTheory
open scoped Topology
open Zeta23 Zeta23.OPICA Zeta23.OPICAFollowup
open Zeta23.OPICAFollowup.FiniteSpan
namespace Zeta23.OPICAFollowup.Validation
/-- Independent inline consumer expands the coefficient construction to
literal actual normalized zero-jet data and the norm to sqrt(sum squares). -/
theorem FullAudit37_expected_full_actual_euclidean_budget {n : ℕ}
    (basis : Fin n → List (ℂ × ℂ × ℕ))
    (valid : ∀ i, ∀ j ∈ basis i, riemannZeta j.2.1=0 ∧
      0<j.2.1.re ∧ j.2.1.re<1 ∧ j.2.2<zeroJetOrder j.2.1)
    (independent : LinearIndependent ℝ (fun i =>
      (actualZeroJetSum (basis i)).rePart.distributionOfLinearGrowth
        (zeroJetRealSpan_growth (basis i) (valid i)))) :
    ∃ c_basis : ℝ, 0<c_basis ∧ ∀ a : Fin n → ℝ,
      c_basis*Real.sqrt (∑ i,‖a i‖^2) ≤
        ∫ x in (Set.range (fun m : ℤ => (m : ℝ)))ᶜ,sincSquared x
          ∂(actualZeroJetSum ((List.ofFn (fun i =>
            (basis i).map (fun j => ((a i : ℂ)*j.1,j.2.1,j.2.2)))).flatten)).rePart.negative := by
  obtain ⟨c,hc,hbound⟩ := fixed_basis_negative_mass_budget basis valid independent
  refine ⟨c,hc,fun a => ?_⟩
  simpa only [EuclideanSpace.norm_eq,realBasisCombinationData,scaleJetData,Zeta23.OPICAFollowup.zeroJetRealSpan,
    Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan,integerLattice] using hbound (WithLp.toLp 2 a)

theorem FullAudit37_no_positive_budget_without_independence :
    ¬ ∃ c : ℝ, 0<c ∧ ∀ a : EuclideanSpace ℝ (Fin 1),
      c*‖a‖ ≤ ∫ x in integerLatticeᶜ,sincSquared x
        ∂(Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan (realBasisCombinationData (fun _ : Fin 1 => []) (fun i => a i))).negative := by
  rintro ⟨c,hc,hbound⟩
  have h := hbound (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  simp [realBasisCombinationData,scaleJetData,Zeta23.OPICAFollowup.FiniteSpan.zeroJetRealSpan,actualZeroJetSum,
    zeroComplex,zeroJordan] at h
  linarith

end Zeta23.OPICAFollowup.Validation
end
end

/- SOURCE COPY: ../audit-finite-span/ExpectedSpanPhysicalConsumerFinal.lean; SHA256 8fd6bfe66d571e599d268d229b6fc3dea3594d83ec479a35c4a8b83768bdaa41 -/
section
noncomputable section
open Set MeasureTheory Complex
open scoped SchwartzMap FourierTransform
open Zeta23.OPICA Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan

namespace Zeta23.OPICAFollowup.Validation
theorem FullAudit38_expected_actual_zero_measure_span_consumer (data : List (ℂ × ℂ × ℕ))
    (h : ∀ j ∈ data, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
      j.2.2 < zeroJetOrder j.2.1) :
    (∀ j ∈ data, Continuous (zeroProfile j.2.1) ∧ Integrable (zeroProfile j.2.1) ∧
      MemLp (zeroProfile j.2.1) 2 ∧ 𝓕 (zeroProfile j.2.1) = zeroProfile j.2.1 ∧
      (j.2.2 = 0 → normalizedZeroMeasureJet j.2.1 j.2.2 = zeroMeasure j.2.1)) ∧
    (∃ hg : (Zeta23.OPICAFollowup.zeroJetRealSpan data).HasLinearGrowth,
      (Zeta23.OPICAFollowup.zeroJetRealSpan data).FourierSelfdual hg ∧
      (Zeta23.OPICAFollowup.zeroJetRealSpan data).HasUnitGap ∧
      ((Zeta23.OPICAFollowup.zeroJetRealSpan data).negative integerLatticeᶜ = 0 →
        (Zeta23.OPICAFollowup.zeroJetRealSpan data).positive = 0 ∧
          (Zeta23.OPICAFollowup.zeroJetRealSpan data).negative = 0)) ∧
    (∀ n : ℕ, ∀ basis : Fin n → List (ℂ × ℂ × ℕ),
      ∀ hb : ∀ i, ∀ j ∈ basis i, riemannZeta j.2.1 = 0 ∧ 0 < j.2.1.re ∧ j.2.1.re < 1 ∧
        j.2.2 < zeroJetOrder j.2.1,
      LinearIndependent ℝ (fun i =>
        (Zeta23.OPICAFollowup.zeroJetRealSpan (basis i)).distributionOfLinearGrowth
          (zeroJetRealSpan_growth _ (hb i))) →
      ∀ a : Fin n → ℝ,
      (Zeta23.OPICAFollowup.zeroJetRealSpan (realBasisCombinationData basis a)).negative
        integerLatticeᶜ = 0 → a = 0) :=
  Zeta23.OPICAFollowup.actual_zero_measure_span_consumer data h

end Zeta23.OPICAFollowup.Validation
end
end

section

noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
open Zeta23 Zeta23.CCM Zeta23.OPICA Zeta23.ExceptionalZero Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation

/- Explicit compound signatures. These preserve both mask branches and every
conclusion of the conditional consumer; they are proposals until compiled and
independently reviewed against all frozen clauses. -/
theorem expected_fixed_two_factor_mask_rate_theta :
    Tendsto (fun T : ℝ => Real.log (1+max
      (∫ t in Icc (T-2*Real.log T) T,
        finiteHighPair (nativeRawPaletteDrive 1 1) (driveIndexBound T)
          (balancedInverseCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T)) 2)
          (balancedInverseCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T)) 2)
          (fun u : ℝ => Real.exp (Real.sqrt u)) t) 0)/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) ∧
    Tendsto (fun T : ℝ => Real.log (1+max
      (∫ t in Icc (T-2*Real.log T) T,
        finiteHighPair (nativeAbsorbedPaletteDrive 1 2 1 (by norm_num)) (driveIndexBound T)
          ((nativeLargeCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T))^2 : ArithmeticFunction ℝ))
          ((nativeLargeCoefficients 1 (Real.exp (T/2-(8/2)*Real.log T))^2 : ArithmeticFunction ℝ))
          (fun u : ℝ => Real.exp (Real.sqrt u)) t) 0)/(2*T))
      atTop (𝓝 nativeZeroDisplacementSup) :=
  fixed_two_factor_mask_rate_theta

theorem expected_quiet_balanced_observation_implies_native_cut
    (time : ℕ → ℝ) (cofinal : Tendsto time atTop atTop)
    (quiet :
      (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
        Real.log (1+max (nativeRawHigh 1 2 1 (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon) ∨
      (∀ epsilon : ℝ, 0 < epsilon → ∀ᶠ n : ℕ in atTop,
        Real.log (1+max (nativeAbsorbedHigh 1 2 1 (by norm_num)
          (logSlackY 2 8 (time n)) 2 (time n)) 0)/(2*time n) ≤ epsilon)) :
    nativeZeroDisplacementSup=0 ∧
    (∀ epsilon : ℝ, 0 < epsilon → MemLp
      (fun t : ℝ => ((Real.exp (-epsilon*t)*primeFieldFamily 0 t : ℝ) : ℂ)) 2 volume) ∧
    NativeOriginalPrimeFieldAllDampedL2 ∧
    NativeOriginalPrimeFieldAllDampedIntegral ∧ RiemannHypothesis :=
  quiet_balanced_observation_implies_native_cut time cofinal quiet

end Zeta23.OPICAFollowup.Validation


end
noncomputable section
open Set MeasureTheory Filter Complex
open scoped ENNReal Topology FourierTransform SchwartzMap
open Zeta23.OPICA Zeta23.OPICAFollowup
namespace Zeta23.OPICAFollowup.Validation

/- Complete written source signature, retaining every conjunct; independent review remains OPEN. -/
theorem expected_weighted_mobius_inverse (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
    (hm : mixingExponentialMoment a σ < ∞) :
    (∀ i : Fin 4, positiveLogMeasure (positiveDilationMixture (mixingCoordinate σ i)) =
      integerLogComb ∗ mixingCoordinate σ i) ∧
    (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive +
        integerLogComb ∗ σ.rePart.negative =
      positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative +
        integerLogComb ∗ σ.rePart.positive) ∧
    (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.positive +
        integerLogComb ∗ σ.imPart.negative =
      positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.negative +
        integerLogComb ∗ σ.imPart.positive) ∧
    (moebiusPlusComb ∗ integerLogComb = Measure.dirac 0 + moebiusMinusComb ∗ integerLogComb) ∧
    (σ.rePart.positive +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive) =
      σ.rePart.negative +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative)) ∧
    (σ.imPart.positive +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.negative +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.positive) =
      σ.imPart.negative +
        (moebiusPlusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.positive +
          moebiusMinusComb ∗ positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.negative)) ∧
    (∀ i : Fin 4, weightedLogNorm a (mixingCoordinate σ i) < ∞) ∧
    (weightedLogNorm a (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.positive) < ∞ ∧
      weightedLogNorm a (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).rePart.negative) < ∞ ∧
      weightedLogNorm a (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.positive) < ∞ ∧
      weightedLogNorm a (positiveLogMeasure (weightedDilationMixture σ a ha.le hm).imPart.negative) < ∞) ∧
    (∀ (μ ρ : Measure ℝ) [SFinite ρ],
      weightedLogNorm a (μ ∗ ρ) = weightedLogNorm a μ * weightedLogNorm a ρ) ∧
    (weightedLogNorm a integerLogComb = ENNReal.ofReal (∑' n : ℕ, (n : ℝ) ^ (-(a + 1 / 2))) ∧
      ((∑' n : ℕ, (n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) = riemannZeta ((a + 1 / 2 : ℝ) : ℂ)) ∧
    (moebiusPlusComb ⟂ₘ moebiusMinusComb ∧
      weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) =
        ENNReal.ofReal (∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2))) ∧
      ((∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) =
        riemannZeta ((a + 1 / 2 : ℝ) : ℂ) / riemannZeta ((2 * a + 1 : ℝ) : ℂ)) := by
  exact weighted_mobius_inverse σ a ha hm

/- Complete written source signature, retaining every conjunct; independent review remains OPEN. -/
theorem expected_weighted_mixture_sharp_gap (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
    (hm : mixingExponentialMoment a σ < ∞)
    (hself : 𝓕 ((weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm)) =
      (weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm))
    (hgap : (weightedDilationMixture σ a ha.le hm).variationControl (Ioo (-1) 1 \ {0}) = 0) :
    (∀ i : Fin 4, mixingCoordinate σ i = mixingCoordinate σ i {0} • Measure.dirac 0) ∧
    σ.variationControl ({0}ᶜ) = 0 ∧
    (weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm) =
      σ.integral (fun _ => 1) • dilatedCombDistribution 0 ∧
    (weightedDilationMixture σ a ha.le hm).compactRestriction {0} isCompact_singleton {0} =
      σ.integral (fun _ => 1) ∧
    ((weightedDilationMixture σ a ha.le hm).compactRestriction {0} isCompact_singleton {0} = 0 →
      (∀ i : Fin 4, mixingCoordinate σ i = 0) ∧
      (weightedDilationMixture σ a ha.le hm).distributionOfLinearGrowth
        (weightedDilationMixture_growth σ a ha.le hm) = 0 ∧
      (weightedDilationMixture σ a ha.le hm).variationControl = 0) := by
  exact weighted_mixture_sharp_gap σ a ha hm hself hgap

/- Complete written source signature, retaining every conjunct; independent review remains OPEN. -/
theorem expected_weighted_gap_leakage :
    (∀ (σ : LocallyFiniteComplexMeasure) (a : ℝ) (ha : 1 / 2 < a)
        (hm : mixingExponentialMoment a σ < ∞),
      ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
          ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.totalVariation ≤
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
          ∂(weightedDilationMixture σ a ha.le hm).totalVariation ∧
      ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
          ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.rePart.totalVariation ≤
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
          ∂(weightedDilationMixture σ a ha.le hm).rePart.totalVariation ∧
      ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
          ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.imPart.totalVariation ≤
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
          ∂(weightedDilationMixture σ a ha.le hm).imPart.totalVariation ∧
      ENNReal.ofReal ((riemannZeta ((2 * a + 1 : ℝ) : ℂ) / riemannZeta ((a + 1 / 2 : ℝ) : ℂ)).re) *
          ∫⁻ t in Iio 0, ENNReal.ofReal (Real.exp (-a * t)) ∂σ.variationControl ≤
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (x ^ (-a - 1 / 2))
          ∂(weightedDilationMixture σ a ha.le hm).variationControl) ∧
    (∀ (h : ℝ → ℂ) (H b : ℝ), 1 / 2 < b → Continuous h → (∀ t, h (-t) = h t) →
      (∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) →
      ENNReal.ofReal ((riemannZeta ((2 * b + 1 : ℝ) : ℂ) / riemannZeta ((b + 1 / 2 : ℝ) : ℂ)).re) *
          (⨆ t ∈ Ici (0 : ℝ), ENNReal.ofReal (Real.exp (b * t) * ‖h t‖)) ≤
        ⨆ x ∈ Ioo (0 : ℝ) 1, ENNReal.ofReal (x ^ (1 / 2 - b) * ‖mixtureDensity h x‖)) ∧
    (∀ (h : ℝ → ℂ) (H a b : ℝ), a < b → (∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) →
      ∫⁻ t, ENNReal.ofReal (Real.exp (a * |t|) * ‖h t‖) < ∞) ∧
    (∀ b : ℝ, 1 / 2 < b → ∃ h : ℝ → ℂ, Continuous h ∧ (∀ t, h (-t) = h t) ∧
      (∀ t, ‖h t‖ ≤ 1 * Real.exp (-b * |t|)) ∧
      ∫⁻ t, ENNReal.ofReal (Real.exp (b * |t|) * ‖h t‖) = ∞) ∧
    (∀ (h : ℝ → ℂ) (hc : Continuous h) (H b : ℝ), 1 / 2 < b →
      (∀ t, ‖h t‖ ≤ H * Real.exp (-b * |t|)) →
      (∀ a : ℝ, a < b → mixingExponentialMoment a (densityMixer h hc) < ∞) ∧
      (∀ i : Fin 4, ∀ s : Set ℝ, MeasurableSet s → s ⊆ Ioi 0 →
        positiveDilationMixture (mixingCoordinate (densityMixer h hc) i) s =
          ∫⁻ x in s, positiveMixtureDensity
            (fun t => ENNReal.ofReal (densityCoordinate h i t)) x) ∧
      (∀ i : Fin 4, ∀ x : ℝ, 0 < x →
        positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h i t)) x < ∞) ∧
      (∀ x : ℝ, 0 < x → mixtureDensity h x =
        (((positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 0 t)) x).toReal -
          (positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 1 t)) x).toReal :
            ℝ) : ℂ) +
        Complex.I * (((positiveMixtureDensity
            (fun t => ENNReal.ofReal (densityCoordinate h 2 t)) x).toReal -
          (positiveMixtureDensity (fun t => ENNReal.ofReal (densityCoordinate h 3 t)) x).toReal :
            ℝ) : ℂ))) := by
  exact weighted_gap_leakage

end Zeta23.OPICAFollowup.Validation

end
noncomputable section
open Set MeasureTheory Filter Complex
open scoped ENNReal Topology FourierTransform SchwartzMap
open Zeta23 Zeta23.OPICA Zeta23.OPICAFollowup Zeta23.OPICAFollowup.FiniteSpan
namespace Zeta23.OPICAFollowup.Validation
/- Complete explicit source-signature companions retain old consumer APIs.
No reflection-generated theorem type or independent review seal is used. -/
theorem expected_source_order_uniform_norms_full_signature :
    ∃ C : ℝ, 0<C ∧ ∀ d : ℕ,
      (∀ k : ℕ, k≤2 →
        (∀ x : ℝ, |iteratedDeriv k (sourceOrderFamily d) x| +
          (∫ u : ℝ, |iteratedDeriv k (sourceOrderFamily d) u|) ≤
            Real.exp (C*((d:ℝ)+1)*Real.log ((d:ℝ)+2))) ∧
        eLpNorm (iteratedDeriv k (sourceOrderFamily d)) (⊤:ENNReal) volume ≤
          ENNReal.ofReal (Real.exp (C*((d:ℝ)+1)*Real.log ((d:ℝ)+2))) ∧
        (eLpNorm (iteratedDeriv k (sourceOrderFamily d)) (⊤:ENNReal) volume).toReal +
          (∫ u : ℝ, |iteratedDeriv k (sourceOrderFamily d) u|) ≤
            Real.exp (C*((d:ℝ)+1)*Real.log ((d:ℝ)+2))) ∧
      MemLp (integerDriveFamily d) 2 volume ∧
      ‖integerDriveFamilyL2 d‖ ≤ Real.exp (C*((d:ℝ)+1)*Real.log ((d:ℝ)+2)) ∧
      (∀ t : ℝ, (∫ x : ℝ, uniform_nativeOrderLogDriveSummand d t x) = 0) := by
  exact source_order_uniform_norms

theorem expected_native_field_theta_envelope_full_signature :
    ∃ C : ℝ, 0<C ∧ ∀ d : ℕ,
      0<nativeFieldOrderConstant d ∧
      (∀ t : ℝ, 0≤t → |primeFieldFamily d t| ≤
        nativeFieldOrderConstant d*Real.exp (nativeZeroDisplacementSup*t)) ∧
      Real.log (1+nativeFieldOrderConstant d) ≤ C*((d:ℝ)+1)*Real.log ((d:ℝ)+2) := by
  exact native_field_theta_envelope

theorem expected_near_gap_mass_bound_full_signature (nu : LocallyFiniteSignedMeasure)
    (hnu : nu.HasLinearGrowth) (hself : nu.FourierSelfdual hnu)
    {a R d : ℝ} (ha : 0<a) (ha1 : a≤1) (hgap : hasNearGap nu a)
    (hoff : nu.OffLatticeNonnegative) (hR : 1≤R) (hd : 0<d) (_hdhalf : d≤1/2) :
    nu.negative (signedBudgetRegion R d)=0 ∧
    nu.positive.real (signedBudgetRegion R d)≤
      (Real.pi^2*R^2/(4*d^2))*(1-a)*nu.totalVariation.real (Icc (-1) 1) := by
  exact near_gap_mass_bound nu hnu hself ha ha1 hgap hoff hR hd _hdhalf

theorem expected_near_gap_controlled_limit_zero_full_signature
    (nu : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (hC : ∀ n, CommonLinearMassBound C (nu n).totalVariation)
    (hself : ∀ n, (nu n).FourierSelfdual (hC n).linearGrowth)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (ha1 : ∀ n, a n ≤ 1)
    (hgap : ∀ n, hasNearGap (nu n) (a n))
    (hoff : ∀ n, (nu n).OffLatticeNonnegative)
    (hlim : Tendsto a atTop (𝓝 1)) (φ : SchwartzMap ℝ ℂ) :
    Tendsto (fun n => (nu n).distributionOfLinearGrowth (hC n).linearGrowth φ)
      atTop (𝓝 0) := by
  exact near_gap_controlled_limit_zero nu C hC hself a ha ha1 hgap hoff hlim φ

theorem expected_dilation_near_gap_family_full_signature
    (L : ℝ) (hL : 0 < L) (hu : L < Real.log 2) :
    (∀ K : Set ℝ, ∀ hK : IsCompact K,
      localSignedCompactRestriction (nearGapCombFamily L) K hK =
        localSignedCompactRestriction (dilatedCombJordan L) K hK +
        localSignedCompactRestriction (dilatedCombJordan (-L)) K hK -
        (2 * Real.cosh (L / 2)) •
          localSignedCompactRestriction (dilatedCombJordan 0) K hK) ∧
    (nearGapCombFamily L).HasLinearGrowth ∧
    CommonLinearMassBound 18 (nearGapCombFamily L).totalVariation ∧
    (nearGapCombFamily L).FourierSelfdual (nearGapCombFamily_growth L) ∧
    (∀ f : SchwartzMap ℝ ℂ,
      nearGapCombDistribution L
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
          (LinearIsometryEquiv.neg ℝ (E := ℝ)) f) =
        nearGapCombDistribution L f) ∧
    hasNearGap (nearGapCombFamily L) (Real.exp (-L)) ∧
    ((1 / 2 : ℝ) < Real.exp (-L) ∧ Real.exp (-L) < 1) ∧
    (nearGapCombFamily L).OffLatticeNonnegative ∧
    ((nearGapCombFamily L).positive ({0} : Set ℝ) = 0 ∧
      (nearGapCombFamily L).negative ({0} : Set ℝ) = 0) ∧
    (nearGapCombFamily L).positive ≠ 0 ∧
    (Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).positive =
        (nearGapCombFamily L).positive ∧
      Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).negative =
        (nearGapCombFamily L).negative) ∧
    ((nearGapCombFamily L).positive.real ({Real.exp (-L)} : Set ℝ) =
        Real.exp (-L / 2) ∧
      (nearGapCombFamily L).negative ({Real.exp (-L)} : Set ℝ) = 0) := by
  exact dilation_near_gap_family L hL hu

theorem expected_dilation_normalized_limit_not_measure_full_signature :
    Tendsto (fun L : ℝ => ((L : ℂ) ^ 2)⁻¹ • nearGapCombDistribution L) (𝓝[≠] 0)
        (𝓝 ct1NormalizedLimit) ∧
    (∀ φ : SchwartzMap ℝ ℂ,
      Tendsto (fun L : ℝ => nearGapCombDistribution L φ / (L : ℂ) ^ 2) (𝓝[≠] 0)
        (𝓝 (∑' n : ℤ, ((n : ℂ) ^ 2 * deriv (deriv φ) n + 2 * n * deriv φ n)))) ∧
    (∀ φ : SchwartzMap ℝ ℂ,
      HasSum (fun n : ℤ => ((n : ℂ) ^ 2 • TemperedDistribution.derivCLM ℂ
          (TemperedDistribution.derivCLM ℂ (TemperedDistribution.delta (n : ℝ))) -
        (2 * (n : ℂ)) • TemperedDistribution.derivCLM ℂ
          (TemperedDistribution.delta (n : ℝ))) φ) (ct1NormalizedLimit φ)) ∧
    (∀ (n : ℤ) (φ : SchwartzMap ℝ ℂ), tsupport φ ⊆ Icc ((n : ℝ) - 1 / 2) (n + 1 / 2) →
      ct1NormalizedLimit φ = (n : ℂ) ^ 2 * deriv (deriv φ) n + 2 * n * deriv φ n) ∧
    ct1NormalizedLimit ≠ 0 ∧
    (∀ n : ℤ, n ≠ 0 → ¬ ∃ C : ℝ, ∀ φ : SchwartzMap ℝ ℂ,
      tsupport φ ⊆ Icc ((n : ℝ) - 1 / 2) (n + 1 / 2) →
        ‖ct1NormalizedLimit φ‖ ≤ C * SchwartzMap.seminorm ℝ 0 0 φ) ∧
    (¬ ∃ μ : LocallyFiniteSignedMeasure, ∀ φ : SchwartzMap ℝ ℂ,
      (∫ x, φ x ∂μ.positive) - (∫ x, φ x ∂μ.negative) = ct1NormalizedLimit φ) ∧
    Tendsto (fun L : ℝ =>
        (nearGapCombFamily L).totalVariation.real (Icc (1 / 2) (3 / 2)) / L ^ 2)
      (𝓝[>] 0) atTop := by
  exact dilation_normalized_limit_not_measure

theorem expected_fixed_basis_negative_mass_budget_full_signature {n : ℕ}
    (basis : Fin n → List JetDatum) (valid : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (independent : LinearIndependent ℝ (fun i =>
      (zeroJetRealSpan (basis i)).distributionOfLinearGrowth (zeroJetRealSpan_growth _ (valid i)))) :
    ∃ c_basis : ℝ, 0<c_basis ∧ ∀ a : EuclideanSpace ℝ (Fin n),
      c_basis*‖a‖ ≤ ∫ x in integerLatticeᶜ, sincSquared x
        ∂(zeroJetRealSpan (realBasisCombinationData basis (fun i => a i))).negative := by
  exact fixed_basis_negative_mass_budget basis valid independent

end Zeta23.OPICAFollowup.Validation

end

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology
namespace Zeta23.OPICAFollowup.Validation
open Zeta23 Zeta23.OPICA Zeta23.CCM Zeta23.ExceptionalZero

theorem expected_canonical_recovery
    {𝕜 E Y H : Type*} [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
    [NormedAddCommGroup Y] [InnerProductSpace 𝕜 Y]
    [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]
    (P : E →L[𝕜] Y) (C : E →L[𝕜] H) (ell : E →L[𝕜] 𝕜)
    (hker : P.ker ⊓ C.ker ≤ ell.ker) :
    (∀ x, orthogonalRecovery P C ell hker (jointObservation P C x) = ell x) ∧
    (∀ y : WithLp 2 (Y × H), y ∈ (jointObservation P C).rangeᗮ →
      orthogonalRecovery P C ell hker y = 0) ∧
    ‖orthogonalRecovery P C ell hker‖ =
      sSup {q : ℝ | ∃ x : E, jointObservation P C x ≠ 0 ∧
        q = ‖ell x‖ / ‖jointObservation P C x‖} ∧
    (∀ R : WithLp 2 (Y × H) →L[𝕜] 𝕜,
      (∀ x, R (jointObservation P C x) = ell x) →
        ‖orthogonalRecovery P C ell hker‖ ≤ ‖R‖) ∧
    (∀ epsilon : ℝ, 0 ≤ epsilon → ∀ x : E, ∀ y : WithLp 2 (Y × H),
      ‖y - jointObservation P C x‖ ≤ epsilon →
        ‖ell x - orthogonalRecovery P C ell hker y‖ ≤
          optimalRecoveryCost P C ell * epsilon) := by
  exact ⟨orthogonalRecovery_on_observation P C ell hker,
    orthogonalRecovery_zero_on_orthogonal P C ell hker,
    orthogonalRecovery_norm_eq_optimalRecoveryCost P C ell hker,
    orthogonalRecovery_minimal P C ell hker,
    orthogonalRecovery_noise_bound P C ell hker⟩

theorem expected_filter_causal_actions (state : NativeCausalState)
    (Q : ℕ) (hQ : 0 < Q) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (Y : ℝ) (hY : 0 ≤ Y) (r : ℕ) :
    finiteEulerFilter Q state = (NativeGenerator.finiteEuler Q hQ).act state ∧
    inverseFiniteEulerFilter Q state = (NativeGenerator.inverseFiniteEuler Q hQ).act state ∧
    rationalCausalFilter a b hb state = (NativeGenerator.rational a b ha hb).act state ∧
    truncatedInverseResidual Y r state = (NativeGenerator.residualPowerReal Y r).act state ∧
    (∀ z : ℂ, (finiteEulerFilter Q state).laplace z =
      finiteEulerMultiplier Q z * state.laplace z) ∧
    (∃ S : ℝ, ∀ z : ℂ, S < z.re →
      (inverseFiniteEulerFilter Q state).laplace z =
        (finiteEulerMultiplier Q z)⁻¹ * state.laplace z) ∧
    (∀ z : ℂ, 0 ≤ z.re → (∀ term ∈ state, term.regular.exponent < z.re) →
      (rationalCausalFilter a b hb state).laplace z =
        ((z + (a : ℂ)) / (z + (b : ℂ))) * state.laplace z) ∧
    (∃ S : ℝ, ∀ z : ℂ, S < z.re →
      (truncatedInverseResidual Y r state).laplace z =
        (1 - riemannZeta (z + 1 / 2) * truncatedMoebiusRealMultiplier Y z)^r *
          state.laplace z) := by
  exact ⟨finiteEulerFilter_actual_action Q hQ state,
    inverseFiniteEulerFilter_actual_action Q hQ state,
    rationalCausalFilter_actual_action a b ha hb state,
    truncatedInverseResidual_actual_action Y r state,
    finiteEulerFilter_laplace Q state,
    inverseFiniteEulerFilter_laplace Q state,
    fun z hz0 hz => rationalCausalFilter_laplace a b hb state hz0 hz,
    truncatedInverseResidual_laplace Y hY r state⟩

theorem expected_followup_native_output
    {rho : zetaZeroConfig.carrier} {beta : ℝ} {phase : ReversalParity} {late : ℝ}
    (out : FollowupNativeOutput rho beta phase late) :
    (step123OpicaView out).source = nativeOriginalIntegerDrive ∧
    (step123OpicaView out).field = nativeOriginalPrimeField ∧
    (step123OpicaView out).input = nativeCompletedInput ∧
    Step123SameStateFieldRecord out.generated.native ∧
    GeneratedStep123RangeObstruction rho out.generated.offLine :=
  followupNativeOutput_actual_source_and_input out

theorem expected_followup_native_output_each_phase
    (rho : zetaZeroConfig.carrier) {beta : ℝ}
    (hbeta : 0 < beta) (hgap : beta < |(rho : ℂ).re - 1 / 2|) :
    ∀ (phase : ReversalParity) (late : ℝ),
      ∃ out : FollowupNativeOutput rho beta phase late,
        max late step123SameStateThreshold <
          fixedOriginalSincTrialAperture out.generated.sourceData.separation ∧
        (step123OpicaView out).source = nativeOriginalIntegerDrive ∧
        (step123OpicaView out).field = nativeOriginalPrimeField ∧
        (step123OpicaView out).input = nativeCompletedInput ∧
        Step123SameStateFieldRecord out.generated.native ∧
        GeneratedStep123RangeObstruction rho out.generated.offLine :=
  followupNativeOutput_eachPhase rho hbeta hgap

end Zeta23.OPICAFollowup.Validation


end
end
#print axioms Zeta23.OPICAFollowup.Validation.expected_sourceFamily_zero_eq_original
#print axioms Zeta23.OPICAFollowup.Validation.expected_sourceFamily_support_smooth_moments
#print axioms Zeta23.OPICAFollowup.Validation.expected_sourceFamily_laplace_identity
#print axioms Zeta23.OPICAFollowup.Validation.expected_forwardKernel_physical_laplace
#print axioms Zeta23.OPICAFollowup.Validation.expected_nativePrimeField_visiblePole
#print axioms Zeta23.OPICAFollowup.Validation.expected_nativeGenerator_transform
#print axioms Zeta23.OPICAFollowup.Validation.expected_nativeGenerator_unit_or_completion
#print axioms Zeta23.OPICAFollowup.Validation.expected_nativeWord_corrected_transform
#print axioms Zeta23.OPICAFollowup.Validation.expected_nativeWord_order_and_leading
#print axioms Zeta23.OPICAFollowup.Validation.expected_nativeWord_first_nonzero_derivative
#print axioms Zeta23.OPICAFollowup.Validation.expected_nativeWord_factor_costs
#print axioms Zeta23.OPICAFollowup.Validation.expected_norm_first_log_comparison
#print axioms Zeta23.OPICAFollowup.Validation.expected_norm_first_rate_transfer
#print axioms Zeta23.OPICAFollowup.Validation.expected_energy_allocation_bound
#print axioms Zeta23.OPICAFollowup.Validation.expected_energy_allocation_rate_lower
#print axioms Zeta23.OPICAFollowup.Validation.expected_joint_recovery_iff
#print axioms Zeta23.OPICAFollowup.Validation.expected_joint_recovery_optimal_norm
#print axioms Zeta23.OPICAFollowup.Validation.expected_joint_recovery_noise_bound
#print axioms Zeta23.OPICAFollowup.Validation.expected_approx_compatibility_left_null
#print axioms Zeta23.OPICAFollowup.Validation.expected_recovery_subexp_budget
#print axioms Zeta23.OPICAFollowup.Validation.expected_laurent_coefficient_error_bound
#print axioms Zeta23.OPICAFollowup.Validation.expected_laurent_observation_survives
#print axioms Zeta23.OPICAFollowup.Validation.expected_nativeWord_contour_consumer
#print axioms Zeta23.OPICAFollowup.Validation.expected_source_product_vertical_bound
#print axioms Zeta23.OPICAFollowup.Validation.expected_zeta_left_line_uniform_bound
#print axioms Zeta23.OPICAFollowup.Validation.expected_forwardKernel_left_contour_budget
#print axioms Zeta23.OPICAFollowup.Validation.expected_forwardKernel_double_exp_decay
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_binomial_inverse_identity
#print axioms Zeta23.OPICAFollowup.Validation.expected_balanced_coeff_divisor_bound
#print axioms Zeta23.OPICAFollowup.Validation.expected_log_slack_native_decomposition
#print axioms Zeta23.OPICAFollowup.Validation.expected_log_slack_typeI_error
#print axioms Zeta23.OPICAFollowup.Validation.expected_fixed_two_factor_preparation
#print axioms Zeta23.OPICAFollowup.Validation.expected_log_slack_both_low_masks_subexp
#print axioms Zeta23.OPICAFollowup.Validation.expected_log_slack_masked_energy_rate_difference
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_zero_count_summability
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_source_explicit_formula
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_zero_sup_bounds
#print axioms Zeta23.OPICAFollowup.Validation.expected_source_order_uniform_norms
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_field_theta_envelope
#print axioms Zeta23.OPICAFollowup.Validation.expected_aux_completion_actual_transform
#print axioms Zeta23.OPICAFollowup.Validation.expected_aux_completion_uniform_decay
#print axioms Zeta23.OPICAFollowup.Validation.expected_aux_completion_ratio_bounds
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_auxiliary_top_moment
#print axioms Zeta23.OPICAFollowup.Validation.expected_laguerre_tail_norm
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_auxiliary_tail_residual_lower
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_terminal_memory_lower
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_fixed_source_window_rate
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_slow_source_window_rate
#print axioms Zeta23.OPICAFollowup.Validation.expected_complex_local_measure_embedding_faithful
#print axioms Zeta23.OPICAFollowup.Validation.expected_dilated_comb_fourier
#print axioms Zeta23.OPICAFollowup.Validation.expected_weighted_mixture_exists_fourier
#print axioms Zeta23.OPICAFollowup.Validation.expected_weighted_mobius_inverse
#print axioms Zeta23.OPICAFollowup.Validation.expected_weighted_mixture_sharp_gap
#print axioms Zeta23.OPICAFollowup.Validation.expected_weighted_gap_leakage
#print axioms Zeta23.OPICAFollowup.Validation.expected_near_gap_mass_bound
#print axioms Zeta23.OPICAFollowup.Validation.expected_near_gap_controlled_limit_zero
#print axioms Zeta23.OPICAFollowup.Validation.expected_dilation_near_gap_family
#print axioms Zeta23.OPICAFollowup.Validation.expected_dilation_normalized_limit_not_measure
#print axioms Zeta23.OPICAFollowup.Validation.expected_renormalized_copoisson_tempered_family
#print axioms Zeta23.OPICAFollowup.Validation.expected_renormalized_copoisson_order_zero
#print axioms Zeta23.OPICAFollowup.Validation.expected_zero_measure_exact_properties
#print axioms Zeta23.OPICAFollowup.Validation.expected_zero_measure_first_cell_sign
#print axioms Zeta23.OPICAFollowup.Validation.expected_finite_sum_euler_maclaurin_uniform
#print axioms Zeta23.OPICAFollowup.Validation.expected_zero_profile_regular_selfdual
#print axioms Zeta23.OPICAFollowup.Validation.expected_zero_profile_tail_and_jumps
#print axioms Zeta23.OPICAFollowup.Validation.expected_log_unitary_form_identity
#print axioms Zeta23.OPICAFollowup.Validation.expected_log_fourier_plancherel
#print axioms Zeta23.OPICAFollowup.Validation.expected_zero_profile_forced_euler
#print axioms Zeta23.OPICAFollowup.Validation.expected_zero_profile_not_homogeneous_operator_vector
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_sampling_gram_identity
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_sampling_form_positive
#print axioms Zeta23.OPICAFollowup.Validation.expected_copoisson_zero_jets_measures
#print axioms Zeta23.OPICAFollowup.Validation.expected_profile_jet_confluent_determinant
#print axioms Zeta23.OPICAFollowup.Validation.expected_finite_zero_jet_independent
#print axioms Zeta23.OPICAFollowup.Validation.expected_finite_zero_span_positive_only_zero
#print axioms Zeta23.OPICAFollowup.Validation.expected_fixed_basis_negative_mass_budget
#print axioms Zeta23.OPICAFollowup.Validation.expected_first_cell_negative_mass_cost
#print axioms Zeta23.OPICAFollowup.Validation.expected_square_fourier_defect
#print axioms Zeta23.OPICAFollowup.Validation.expected_square_defect_origin_positive
#print axioms Zeta23.OPICAFollowup.Validation.expected_square_no_lattice_repair
#print axioms Zeta23.OPICAFollowup.Validation.expected_square_selfdual_projection_fills_gap
#print axioms Zeta23.OPICAFollowup.Validation.expected_sawtooth_integrable_force_identity
#print axioms Zeta23.OPICAFollowup.Validation.expected_sawtooth_actual_mellin_fourier
#print axioms Zeta23.OPICAFollowup.Validation.expected_sawtooth_norm_weighted_zeta_moment
#print axioms Zeta23.OPICAFollowup.Validation.expected_arithmetic_stieltjes_holomorphic
#print axioms Zeta23.OPICAFollowup.Validation.expected_arithmetic_stieltjes_sign_budget
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_forced_resolvent_unique
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_sample_stieltjes_identity
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_profile_spectral_norms
#print axioms Zeta23.OPICAFollowup.Validation.expected_generic_forced_profile_unique
#print axioms Zeta23.OPICAFollowup.Validation.expected_generic_boundary_amplitude
#print axioms Zeta23.OPICAFollowup.Validation.expected_coupled_gram_collision_control
#print axioms Zeta23.OPICAFollowup.Validation.expected_norm_first_strictly_weaker_control
#print axioms Zeta23.OPICAFollowup.Validation.expected_history_recovery_cost_control
#print axioms Zeta23.OPICAFollowup.Validation.expected_forced_positive_gram_nonreal_control
#print axioms Zeta23.OPICAFollowup.Validation.expected_fixed_two_factor_mask_rate_theta
#print axioms Zeta23.OPICAFollowup.Validation.expected_quiet_balanced_observation_implies_native_cut
#print axioms Zeta23.OPICAFollowup.Validation.expected_step123_word_jet_consumer
#print axioms Zeta23.OPICAFollowup.Validation.expected_actual_zero_measure_span_consumer
#print axioms Zeta23.OPICAFollowup.Validation.expected_actual_force_sampling_consumer
#print axioms Zeta23.OPICAFollowup.Validation.expected_dilation_near_gap_family_full_signature
#print axioms Zeta23.OPICAFollowup.Validation.expected_dilation_normalized_limit_not_measure_full_signature
#print axioms Zeta23.OPICAFollowup.Validation.expected_fixed_basis_negative_mass_budget_full_signature
#print axioms Zeta23.OPICAFollowup.Validation.expected_native_field_theta_envelope_full_signature
#print axioms Zeta23.OPICAFollowup.Validation.expected_near_gap_controlled_limit_zero_full_signature
#print axioms Zeta23.OPICAFollowup.Validation.expected_near_gap_mass_bound_full_signature
#print axioms Zeta23.OPICAFollowup.Validation.expected_source_order_uniform_norms_full_signature
#print axioms Zeta23.OPICAFollowup.Validation.expected_canonical_recovery
#print axioms Zeta23.OPICAFollowup.Validation.expected_filter_causal_actions
#print axioms Zeta23.OPICAFollowup.Validation.expected_followup_native_output
#print axioms Zeta23.OPICAFollowup.Validation.expected_followup_native_output_each_phase

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ComplexConjugate
namespace Zeta23.OPICAFollowup.Validation
open Zeta23.OPICA

/-- Independent literal physical type: real Jordan measure, exact source density
and punctured comb, local finiteness, actual growth/gap/sign/origin and pairing. -/
theorem full_actual_square_measure {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) :
    ∃ ν:LocallyFiniteSignedMeasure,
      ν.positive=volume.withDensity (fun x=>ENNReal.ofReal (‖A-h x‖^2)) ∧
      ν.negative=ENNReal.ofReal (‖A‖^2) • puncturedLattice ∧
      ν.positive.MutuallySingular ν.negative ∧
      (∃ hg:ν.HasLinearGrowth,
        (ν.positive (Ioo (-1) 1)=0 ∧ ν.negative (Ioo (-1) 1)=0) ∧
        (ν.positive {0}=0 ∧ ν.negative {0}=0) ∧
        ν.negative (Set.range (fun n:ℤ=>(n:ℝ)))ᶜ=0 ∧
        (Measure.map (fun x:ℝ=>-x) ν.positive=ν.positive ∧
          Measure.map (fun x:ℝ=>-x) ν.negative=ν.negative) ∧
        (∀ φ:𝓢(ℝ,ℂ),ν.distributionOfLinearGrowth hg φ=
          (∫ x,((‖A-h x‖^2:ℝ):ℂ)*φ x)-
            ((‖A‖^2:ℝ):ℂ)*∑' n:ℤ,if n=0 then 0 else φ n) ∧
        (∀ φ:𝓢(ℝ,ℂ),𝓕 (ν.distributionOfLinearGrowth hg) φ-
          ν.distributionOfLinearGrowth hg φ=
            ∫ x,(autocorr h x-h x*conj (h x))*φ x)) := by
  refine ⟨squareGapJordan h A hcont,rfl,rfl,(squareGapJordan h A hcont).mutuallySingular,
    squareGapJordan_growth hcont hvan A,squareGapJordan_gap hcont A hpl,
    squareGapJordan_origin hcont A,squareGapJordan_off_lattice hcont A,
    squareGapJordan_even hcont A hev,?_,?_⟩
  · intro φ
    exact squareGapJordan_pairing hcont hvan A φ
  · intro φ
    exact squareGapJordan_fourier_defect hcont hint hL2 hsd hev hvan A φ

/-- Every arbitrary true Euclidean-tempered complex measure supported on the
integer lattice is covered. The four coordinate embeddings are derived, then
the literal sum of their genuine positive-measure tempered distributions is used. -/
theorem all_actual_tempered_corrections {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) (hne : h≠0)
    (σ:LocallyFiniteComplexMeasure) [σ.totalVariation.HasTemperateGrowth]
    (hσ:σ.totalVariation (Set.range (fun n:ℤ=>(n:ℝ)))ᶜ=0) :
    ∃ (hrp:σ.rePart.positive.HasTemperateGrowth) (hrn:σ.rePart.negative.HasTemperateGrowth)
      (hip:σ.imPart.positive.HasTemperateGrowth) (hin:σ.imPart.negative.HasTemperateGrowth),
    letI := hrp; letI := hrn; letI := hip; letI := hin
    let T := (squareGapJordan h A hcont).distributionOfLinearGrowth
      (squareGapJordan_growth hcont hvan A)
    𝓕 (T+((σ.rePart.positive.toTemperedDistribution-σ.rePart.negative.toTemperedDistribution)+
      I • (σ.imPart.positive.toTemperedDistribution-σ.imPart.negative.toTemperedDistribution))) ≠
      T+((σ.rePart.positive.toTemperedDistribution-σ.rePart.negative.toTemperedDistribution)+
        I • (σ.imPart.positive.toTemperedDistribution-σ.imPart.negative.toTemperedDistribution)) := by
  let hrp := SquarePhysicalSupport.component_temperate σ _ (SquarePhysicalSupport.coordinate_domination σ).1
  let hrn := SquarePhysicalSupport.component_temperate σ _ (SquarePhysicalSupport.coordinate_domination σ).2.1
  let hip := SquarePhysicalSupport.component_temperate σ _ (SquarePhysicalSupport.coordinate_domination σ).2.2.1
  let hin := SquarePhysicalSupport.component_temperate σ _ (SquarePhysicalSupport.coordinate_domination σ).2.2.2
  refine ⟨hrp,hrn,hip,hin,?_⟩
  exact square_actual_no_tempered_measure_repair hev hcont hint hL2 hsd hvan hpl hne σ hσ

/-- The actual distribution projection, with its literal density identity and
every local positivity/gap-filling clause retained. -/
theorem full_actual_projection {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) (hne : h≠0) :
    let T := (squareGapJordan h A hcont).distributionOfLinearGrowth
      (squareGapJordan_growth hcont hvan A)
    let P := (1/2:ℂ) • (T+𝓕 T)
    𝓕 P=P ∧
    (∀ φ:𝓢(ℝ,ℂ),P φ=T φ+(1/2)*∫ x,(autocorr h x-h x*conj (h x))*φ x) ∧
    ∃ ε:ℝ,0<ε ∧ ε<1 ∧
      (∀ x∈Ioo (-ε) ε,0<(autocorr h x-h x*conj (h x)).re ∧
        (autocorr h x-h x*conj (h x)).im=0) ∧
      ∀ φ:𝓢(ℝ,ℂ),tsupport φ⊆Ioo (-ε) ε →
        P φ=∫ x,((autocorr h x-h x*conj (h x))/2)*φ x := by
  exact square_actual_projection_fills_gap hev hcont hint hL2 hsd hvan hpl hne

theorem nonzero_lattice_atom_retained :
    (squareGapJordan (fun _ : ℝ => (0:ℂ)) 1 continuous_const).negative {1}=1 := by
  simp [squareGapJordan,Measure.smul_apply,puncturedLattice_one]

theorem no_gap_without_plateau :
    (squareGapJordan (fun _ : ℝ => (0:ℂ)) 1 continuous_const).positive (Ioo (-1) 1)=2 := by
  norm_num [squareGapJordan,Real.volume_Ioo]

theorem zero_square_degenerate :
    (squareGapJordan (fun _ : ℝ => (0:ℂ)) 0 continuous_const).positive=0 ∧
      (squareGapJordan (fun _ : ℝ => (0:ℂ)) 0 continuous_const).negative=0 := by
  simp [squareGapJordan]

end Zeta23.OPICAFollowup.Validation
#print axioms Zeta23.OPICAFollowup.Validation.full_actual_square_measure
#print axioms Zeta23.OPICAFollowup.Validation.all_actual_tempered_corrections
#print axioms Zeta23.OPICAFollowup.Validation.full_actual_projection
#print axioms Zeta23.OPICAFollowup.Validation.nonzero_lattice_atom_retained
#print axioms Zeta23.OPICAFollowup.Validation.no_gap_without_plateau
#print axioms Zeta23.OPICAFollowup.Validation.zero_square_degenerate

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup.Validation
open Zeta23.OPICA

/-- Literal actual zero profile at plateau one, actual multiplicity-bounded
finite zero-jet measures, and an arbitrary Euclidean-temperate lattice measure. -/
theorem full_actual_square_jet_lattice_composition (ρ:ℂ) (hz:riemannZeta ρ=0)
    (h0:0<ρ.re) (h1:ρ.re<1) (data:List (ℂ × ℂ × ℕ))
    (hdata:∀j∈data,riemannZeta j.2.1=0 ∧ 0<j.2.1.re ∧ j.2.1.re<1 ∧
      j.2.2<zeroJetOrder j.2.1)
    (σ:LocallyFiniteComplexMeasure) [σ.totalVariation.HasTemperateGrowth]
    (hσ:σ.totalVariation (Set.range (fun n:ℤ=>(n:ℝ)))ᶜ=0) :
    let hp := zero_profile_regular_selfdual ρ hz h0 h1
    let hv : Tendsto (zeroProfile ρ) (cocompact ℝ) (𝓝 0) := by
      rw [←hp.2.2.2.2.2.1]; exact Real.zero_at_infty_fourier _
    let Tτ := (squareGapJordan (zeroProfile ρ) 1 hp.2.1).distributionOfLinearGrowth
      (squareGapJordan_growth hp.2.1 hv 1)
    let Tν := (FiniteSpan.actualZeroJetSum data).rePart.distributionOfLinearGrowth
      (FiniteSpan.zeroJetRealSpan_growth data hdata)
    𝓕 (Tτ+Tν+SquarePhysicalSupport.correctionDistribution σ) ≠
      Tτ+Tν+SquarePhysicalSupport.correctionDistribution σ := by
  exact actual_square_zero_jet_lattice_barrier ρ hz h0 h1 data hdata σ hσ

end Zeta23.OPICAFollowup.Validation
#print axioms Zeta23.OPICAFollowup.Validation.full_actual_square_jet_lattice_composition

noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap ContDiff
namespace Zeta23.OPICAFollowup.Validation
open Zeta23.OPICA

theorem expected_original_distribution_tempered_domain {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) (hne : h≠0)
    (σ : LocallyFiniteComplexMeasure) (T : TemperedDistribution ℝ ℂ)
    (hσ : σ.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ=0)
    (hT : ∀ φ : 𝓢(ℝ,ℂ), HasCompactSupport (φ : ℝ → ℂ) → T φ=σ.integral φ) :
    𝓕 ((squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+T) ≠
      (squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+T :=
  square_actual_no_distribution_tempered_measure_repair
    hev hcont hint hL2 hsd hvan hpl hne σ T hσ hT

theorem expected_existing_strong_domain_is_instance {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) (hne : h≠0)
    (σ : LocallyFiniteComplexMeasure) [σ.totalVariation.HasTemperateGrowth]
    (hσ : σ.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ=0) :
    𝓕 ((squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+SquarePhysicalSupport.correctionDistribution σ) ≠
      (squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+SquarePhysicalSupport.correctionDistribution σ := by
  exact square_actual_no_distribution_tempered_measure_repair
    hev hcont hint hL2 hsd hvan hpl hne σ (SquarePhysicalSupport.correctionDistribution σ)
    hσ (fun _ _ => rfl)

theorem expected_compact_extension_unique (σ : LocallyFiniteComplexMeasure)
    (T U : TemperedDistribution ℝ ℂ)
    (hT : ∀ φ : 𝓢(ℝ,ℂ), HasCompactSupport (φ : ℝ → ℂ) → T φ=σ.integral φ)
    (hU : ∀ φ : 𝓢(ℝ,ℂ), HasCompactSupport (φ : ℝ → ℂ) → U φ=σ.integral φ) : T=U :=
  TemperedLatticeBridge.extension_unique σ T U hT hU

theorem expected_full_domain_mixed_selfdual_barrier {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x,h (-x)=h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h=h) (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x,|x|≤1 → h x=A) (hne : h≠0)
    (S : TemperedDistribution ℝ ℂ) (hS : 𝓕 S=S)
    (σ : LocallyFiniteComplexMeasure) (T : TemperedDistribution ℝ ℂ)
    (hσ : σ.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ=0)
    (hT : ∀ φ : 𝓢(ℝ,ℂ), HasCompactSupport (φ : ℝ → ℂ) → T φ=σ.integral φ) :
    𝓕 ((squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+S+T) ≠
      (squareGapJordan h A hcont).distributionOfLinearGrowth
        (squareGapJordan_growth hcont hvan A)+S+T :=
  square_actual_no_selfdual_and_distribution_tempered_measure_repair
    hev hcont hint hL2 hsd hvan hpl hne S hS σ T hσ hT

/-- Omitting compact compatibility would be mathematically false: a free
tempered distribution can cancel the square exactly. -/
theorem compact_compatibility_cannot_be_omitted (S : TemperedDistribution ℝ ℂ) :
    ∃ T : TemperedDistribution ℝ ℂ, 𝓕 (S+T)=S+T := by
  exact ⟨-S, by simp⟩

#print axioms Zeta23.OPICAFollowup.Validation.expected_original_distribution_tempered_domain
#print axioms Zeta23.OPICAFollowup.Validation.expected_existing_strong_domain_is_instance
#print axioms Zeta23.OPICAFollowup.Validation.expected_compact_extension_unique
#print axioms Zeta23.OPICAFollowup.Validation.expected_full_domain_mixed_selfdual_barrier
#print axioms Zeta23.OPICAFollowup.Validation.compact_compatibility_cannot_be_omitted
end Zeta23.OPICAFollowup.Validation

/- Independently authored from frozen A1--A3, HT2.1--HT2.3,
CT1.1--CT1.3 and R2-H2b, before elaborating any consumer.
No producer root statement or Validation statement was consulted. -/
noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology BigOperators ENNReal FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup.Validation
open Zeta23.OPICA Zeta23.CCM FiniteSpan

theorem independent_expected_source_order_uniform_norms :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ,
      (∀ k : ℕ, k ≤ 2 → ∀ x : ℝ,
        (∫ u : ℝ, |iteratedDeriv k (sourceOrderFamily d) u|) +
          |iteratedDeriv k (sourceOrderFamily d) x| ≤
            Real.exp (C * (d + 1) * Real.log (d + 2))) ∧
      (∀ k : ℕ, k ≤ 2 →
        (eLpNorm (iteratedDeriv k (sourceOrderFamily d)) ∞ volume).toReal +
          (∫ u : ℝ, |iteratedDeriv k (sourceOrderFamily d) u|) ≤
            Real.exp (C * (d + 1) * Real.log (d + 2)) ∧
        eLpNorm (iteratedDeriv k (sourceOrderFamily d)) ∞ volume ≤
          ENNReal.ofReal (Real.exp (C * (d + 1) * Real.log (d + 2)))) ∧
      MemLp (integerDriveFamily d) 2 volume ∧
      ‖integerDriveFamilyL2 d‖ ≤ Real.exp (C * (d + 1) * Real.log (d + 2)) ∧
      (∀ t : ℝ, ∫ x : ℝ, uniform_nativeOrderLogDriveSummand d t x = 0) ∧
      sourceWeightedMoment 0 (1/2) (sourceOrderFamily d) = 0 ∧
      sourceWeightedMoment 1 (1/2) (sourceOrderFamily d) = 0 := by
  obtain ⟨C, hC, h⟩ := source_order_uniform_norms
  refine ⟨C, hC, fun d => ?_⟩
  obtain ⟨jet, lp, bound, cancellation⟩ := h d
  refine ⟨?_, ?_, lp, bound, cancellation,
    (sourceFamily_elementary_moments d 0 (by omega)).1,
    (sourceFamily_elementary_moments d 1 (by omega)).1⟩
  · intro k hk x
    simpa only [add_comm] using (jet k hk).1 x
  · intro k hk
    exact ⟨(jet k hk).2.2, (jet k hk).2.1⟩

theorem independent_expected_native_field_theta_envelope :
    ∃ C : ℝ, 0 < C ∧ ∃ A : ℕ → ℝ,
      A = nativeFieldOrderConstant ∧
      (∀ d, 0 < A d) ∧
      (∀ d, Real.log (1 + A d) ≤ C * (d + 1) * Real.log (d + 2)) ∧
      ∀ d : ℕ, ∀ t : ℝ, 0 ≤ t →
        |primeFieldFamily d t| ≤ A d * Real.exp (nativeZeroDisplacementSup * t) := by
  obtain ⟨C, hC, h⟩ := native_field_theta_envelope
  exact ⟨C, hC, nativeFieldOrderConstant, rfl,
    fun d => (h d).1, fun d => (h d).2.2, fun d => (h d).2.1⟩

theorem independent_expected_near_gap_mass_bound
    (ν : LocallyFiniteSignedMeasure) (growth : ν.HasLinearGrowth)
    (selfdual : ν.FourierSelfdual growth) (positiveOff : ν.negative integerLatticeᶜ = 0)
    (a R d : ℝ) (ha : 0 < a) (ha1 : a ≤ 1)
    (gap : ν.positive (Ioo (-a) a) = 0 ∧ ν.negative (Ioo (-a) a) = 0)
    (hR : 1 ≤ R) (hd : 0 < d) (hd2 : d ≤ 1/2) :
    ν.negative {x | |x| ≤ R ∧ d ≤ Metric.infDist x integerLattice} = 0 ∧
    ν.positive.real {x | |x| ≤ R ∧ d ≤ Metric.infDist x integerLattice} ≤
      Real.pi^2 * R^2 * (1-a) * ν.totalVariation.real (Icc (-1) 1) / (4*d^2) := by
  obtain ⟨hn, hp⟩ := near_gap_mass_bound ν growth selfdual ha ha1 gap positiveOff hR hd hd2
  refine ⟨hn, ?_⟩
  convert hp using 1 <;> first | rfl | ring

theorem independent_expected_near_gap_controlled_limit_zero
    (ν : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (common : ∀ n, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      (ν n).totalVariation.real (Icc (-R) R) ≤ C * (1+R))
    (growth : ∀ n, (ν n).HasLinearGrowth)
    (selfdual : ∀ n, (ν n).FourierSelfdual (growth n))
    (positiveOff : ∀ n, (ν n).negative integerLatticeᶜ = 0)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n ∧ a n ≤ 1)
    (gap : ∀ n, (ν n).positive (Ioo (-a n) (a n)) = 0 ∧
      (ν n).negative (Ioo (-a n) (a n)) = 0)
    (sharp : Tendsto a atTop (𝓝 1)) :
    ∀ φ : SchwartzMap ℝ ℂ,
      Tendsto (fun n => (ν n).distributionOfLinearGrowth (growth n) φ) atTop (𝓝 0) := by
  exact near_gap_controlled_limit_zero ν C common selfdual a
    (fun n => (ha n).1) (fun n => (ha n).2) gap positiveOff sharp

theorem independent_expected_dilation_near_gap_family :
    ∃ C : ℝ, 0 < C ∧ ∀ L : ℝ, 0 < L → L < Real.log 2 →
      (nearGapCombDistribution L =
        dilatedCombDistribution L + dilatedCombDistribution (-L) -
          ((2 * Real.cosh (L/2) : ℝ) : ℂ) • dilatedCombDistribution 0) ∧
      (∀ K : Set ℝ, ∀ hK : IsCompact K,
        localSignedCompactRestriction (nearGapCombFamily L) K hK =
          localSignedCompactRestriction (dilatedCombJordan L) K hK +
          localSignedCompactRestriction (dilatedCombJordan (-L)) K hK -
          (2 * Real.cosh (L/2)) • localSignedCompactRestriction (dilatedCombJordan 0) K hK) ∧
      (nearGapCombFamily L).HasLinearGrowth ∧
      nearGapCombDistribution L ≠ 0 ∧
      𝓕 (nearGapCombDistribution L) = nearGapCombDistribution L ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        nearGapCombDistribution L
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
            (LinearIsometryEquiv.neg ℝ).toContinuousLinearEquiv φ) = nearGapCombDistribution L φ) ∧
      Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).positive =
        (nearGapCombFamily L).positive ∧
      Measure.map (fun x : ℝ => -x) (nearGapCombFamily L).negative =
        (nearGapCombFamily L).negative ∧
      (nearGapCombFamily L).positive {0} = 0 ∧
      (nearGapCombFamily L).negative {0} = 0 ∧
      (nearGapCombFamily L).positive (Ioo (-Real.exp (-L)) (Real.exp (-L))) = 0 ∧
      (nearGapCombFamily L).negative (Ioo (-Real.exp (-L)) (Real.exp (-L))) = 0 ∧
      (1/2 < Real.exp (-L) ∧ Real.exp (-L) < 1) ∧
      (nearGapCombFamily L).negative integerLatticeᶜ = 0 ∧
      (nearGapCombFamily L).positive ≠ 0 ∧
      (nearGapCombFamily L).positive {Real.exp (-L)} = ENNReal.ofReal (Real.exp (-L/2)) ∧
      (nearGapCombFamily L).negative {Real.exp (-L)} = 0 ∧
      (∀ R : ℝ, 0 ≤ R → (nearGapCombFamily L).totalVariation.real (Icc (-R) R) ≤ C*(1+R)) := by
  refine ⟨18, by norm_num, fun L hL hL2 => ?_⟩
  obtain ⟨restriction, growth, common, selfdual, evenTest, gap, radius, off,
    origin, nonzero, evenJordan, edge, edgeNeg⟩ := dilation_near_gap_family L hL hL2
  have distNonzero : nearGapCombDistribution L ≠ 0 := by
    intro hz
    exact nonzero ((nearGapCombFamily L).parts_eq_zero_of_distribution_eq_zero growth hz).1
  have atom : (nearGapCombFamily L).positive {Real.exp (-L)} =
      ENNReal.ofReal (Real.exp (-L/2)) := by
    rw [← edge]
    exact (ENNReal.ofReal_toReal isCompact_singleton.measure_lt_top.ne).symm
  exact ⟨nearGapCombDistribution_eq_explicit L, restriction, growth, distNonzero, selfdual,
    evenTest, evenJordan.1, evenJordan.2, origin.1, origin.2, gap.1, gap.2,
    radius, off, nonzero, atom, edgeNeg, common.2⟩

theorem independent_expected_dilation_normalized_limit_not_measure :
    ∃ T : TemperedDistribution ℝ ℂ,
      T = ct1NormalizedLimit ∧ T ≠ 0 ∧
      Tendsto (fun L : ℝ => ((L : ℂ)^2)⁻¹ • nearGapCombDistribution L)
        (𝓝[≠] 0) (𝓝 T) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        Tendsto (fun L : ℝ => (nearGapCombDistribution L φ) / (L : ℂ)^2)
          (𝓝[≠] 0) (𝓝 (T φ))) ∧
      (∀ φ : SchwartzMap ℝ ℂ,
        T φ = ∑' n : ℤ, ((n : ℂ)^2 * deriv (deriv φ) n + 2*(n : ℂ)*deriv φ n)) ∧
      (∀ φ : SchwartzMap ℝ ℂ, HasSum (fun n : ℤ =>
        ((n : ℂ)^2 • (TemperedDistribution.derivCLM ℂ)
          ((TemperedDistribution.derivCLM ℂ) (TemperedDistribution.delta (n : ℝ))) -
          (2*(n : ℂ)) • (TemperedDistribution.derivCLM ℂ)
            (TemperedDistribution.delta (n : ℝ))) φ) (T φ)) ∧
      (∀ n : ℤ, ∀ φ : SchwartzMap ℝ ℂ,
        tsupport (φ : ℝ → ℂ) ⊆ Icc ((n : ℝ)-1/2) ((n : ℝ)+1/2) →
        T φ = (n : ℂ)^2 * deriv (deriv φ) n + 2*(n : ℂ)*deriv φ n) ∧
      (∀ n : ℤ, n ≠ 0 → ¬ ∃ C : ℝ, ∀ φ : SchwartzMap ℝ ℂ,
        tsupport (φ : ℝ → ℂ) ⊆ Icc ((n : ℝ)-1/2) ((n : ℝ)+1/2) →
        ‖T φ‖ ≤ C * SchwartzMap.seminorm ℝ 0 0 φ) ∧
      (¬ ∃ μ : LocallyFiniteSignedMeasure, ∀ φ : SchwartzMap ℝ ℂ,
        (∫ x : ℝ, φ x ∂μ.positive) - (∫ x : ℝ, φ x ∂μ.negative) = T φ) ∧
      (¬ ∃ μ : LocallyFiniteSignedMeasure, ∃ growth : μ.HasLinearGrowth,
        μ.distributionOfLinearGrowth growth = T) ∧
      Tendsto (fun L : ℝ => (nearGapCombFamily L).totalVariation.real (Icc (1/2) (3/2)) / L^2)
        (𝓝[>] 0) atTop ∧
      (∀ M : ℝ, ∀ᶠ L : ℝ in 𝓝[>] 0,
        M < (nearGapCombFamily L).totalVariation.real (Icc (-2) 2) / L^2) := by
  obtain ⟨topology, pairing, delta, localFormula, nonzero, order, measure, variation⟩ :=
    dilation_normalized_limit_not_measure
  refine ⟨ct1NormalizedLimit, rfl, nonzero, topology, ?_, ct1NormalizedLimit_apply,
    delta, localFormula, order, measure, ?_, variation, ?_⟩
  · intro φ
    simpa only [ct1NormalizedLimit_apply] using pairing φ
  · rintro ⟨μ, growth, hμ⟩
    apply measure
    refine ⟨μ, fun φ => ?_⟩
    simpa only [LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply] using
      congrArg (fun S : TemperedDistribution ℝ ℂ => S φ) hμ
  · intro M
    filter_upwards [variation.eventually (eventually_gt_atTop M)] with L hL
    apply lt_of_lt_of_le hL
    apply div_le_div_of_nonneg_right _ (sq_nonneg L)
    exact measureReal_mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])
      (h₂ := isCompact_Icc.measure_lt_top.ne)

theorem independent_expected_fixed_basis_negative_mass_budget
    {n : ℕ} (basis : Fin n → List JetDatum)
    (valid : ∀ i, ∀ j ∈ basis i, ValidJet j)
    (independent : LinearIndependent ℝ (fun i =>
      (zeroJetRealSpan (basis i)).distributionOfLinearGrowth (zeroJetRealSpan_growth _ (valid i)))) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : Fin n → ℝ,
      (c * Real.sqrt (∑ i, (a i)^2) ≤
        ∫ x : ℝ in integerLatticeᶜ, sincSquared x
          ∂(zeroJetRealSpan (realBasisCombinationData basis a)).negative) ∧
      c * Real.sqrt (∑ i, (a i)^2) ≤
        ∫ x : ℝ, sincSquared x ∂(zeroJetRealSpan (realBasisCombinationData basis a)).negative := by
  obtain ⟨c, hc, h⟩ := fixed_basis_negative_mass_budget basis valid independent
  refine ⟨c, hc, fun a => ?_⟩
  have bound := h (WithLp.toLp 2 a)
  have euclidean : ‖(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin n))‖ =
      Real.sqrt (∑ i, (a i)^2) := by
    simp only [EuclideanSpace.norm_eq, Real.norm_eq_abs, sq_abs]
  have b : c * Real.sqrt (∑ i, (a i)^2) ≤
      ∫ x : ℝ in integerLatticeᶜ, sincSquared x
        ∂(zeroJetRealSpan (realBasisCombinationData basis a)).negative := by
    simpa only [euclidean, WithLp.ofLp_toLp] using bound
  refine ⟨b, ?_⟩
  have validA := realBasisCombination_valid basis valid a
  have growthA := zeroJetRealSpan_growth _ validA
  have gapA := zeroJetRealSpan_gap (realBasisCombinationData basis a)
  rw [← sincSquared_integral_compl_lattice _
    ((zeroJetRealSpan (realBasisCombinationData basis a)).negative_hasLinearGrowth growthA)
    (singleton_zero_of_unit_gap _ gapA.2)]
  exact b

/- The original, independently authored kernel premise and the canonical
interface quantify over exactly the same actual finite real combinations. -/
theorem independent_actual_basis_independence_iff_Jordan_kernel
    {n : ℕ} (basis : Fin n → List JetDatum)
    (valid : ∀ i, ∀ j ∈ basis i, ValidJet j) :
    LinearIndependent ℝ (fun i =>
      (zeroJetRealSpan (basis i)).distributionOfLinearGrowth (zeroJetRealSpan_growth _ (valid i))) ↔
      ∀ a : Fin n → ℝ,
        (zeroJetRealSpan (realBasisCombinationData basis a)).positive = 0 →
        (zeroJetRealSpan (realBasisCombinationData basis a)).negative = 0 → a = 0 := by
  classical
  constructor
  · intro independent a hp hn
    have hz : (zeroJetRealSpan (realBasisCombinationData basis a)).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (realBasisCombination_valid basis valid a)) = 0 := by
      ext φ
      simp only [LocallyFiniteSignedMeasure.distributionOfLinearGrowth_apply, hp, hn,
        integral_zero_measure, sub_self, ContinuousLinearMap.zero_apply]
    rw [realBasisCombination_distribution basis valid a] at hz
    funext i
    exact Fintype.linearIndependent_iff.mp independent a hz i
  · intro kernel
    apply Fintype.linearIndependent_iff.mpr
    intro a hz i
    have hdist : (zeroJetRealSpan (realBasisCombinationData basis a)).distributionOfLinearGrowth
        (zeroJetRealSpan_growth _ (realBasisCombination_valid basis valid a)) = 0 := by
      rw [realBasisCombination_distribution basis valid a]
      exact hz
    have parts := (zeroJetRealSpan (realBasisCombinationData basis a)).parts_eq_zero_of_distribution_eq_zero
      (zeroJetRealSpan_growth _ (realBasisCombination_valid basis valid a)) hdist
    exact congrFun (kernel a parts.1 parts.2) i

/- Uniform tails used by the controlled-limit theorem, stated on the actual
total variation for every member of an arbitrary common-budget sequence. -/
theorem independent_expected_controlled_uniform_tails
    (ν : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (common : ∀ n, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      (ν n).totalVariation.real (Icc (-R) R) ≤ C * (1+R))
    (M R : ℝ) (hM : 0 ≤ M) (hR : 1 ≤ R)
    (f : ℝ → ℂ) (continuous : Continuous f)
    (decay : ∀ x, |x|^3 * ‖f x‖ ≤ M) :
    ∀ n, IntegrableOn f {x : ℝ | R ≤ |x|} (ν n).totalVariation ∧
      (∫ x : ℝ in {x | R ≤ |x|}, ‖f x‖ ∂(ν n).totalVariation) ≤ 4*C*M/R^2 := by
  intro n
  exact common_linear_cubic_tail _ C M R (common n) hM hR f continuous decay

#print axioms Zeta23.OPICAFollowup.Validation.independent_expected_source_order_uniform_norms
#print axioms Zeta23.OPICAFollowup.Validation.independent_expected_native_field_theta_envelope
#print axioms Zeta23.OPICAFollowup.Validation.independent_expected_near_gap_mass_bound
#print axioms Zeta23.OPICAFollowup.Validation.independent_expected_near_gap_controlled_limit_zero
#print axioms Zeta23.OPICAFollowup.Validation.independent_expected_dilation_near_gap_family
#print axioms Zeta23.OPICAFollowup.Validation.independent_expected_dilation_normalized_limit_not_measure
#print axioms Zeta23.OPICAFollowup.Validation.independent_expected_fixed_basis_negative_mass_budget
#print axioms Zeta23.OPICAFollowup.Validation.independent_actual_basis_independence_iff_Jordan_kernel
#print axioms Zeta23.OPICAFollowup.Validation.independent_expected_controlled_uniform_tails

end Zeta23.OPICAFollowup.Validation

/- Explicit intended statements written from frozen paper CT1.3 before this
consumer's first elaboration. No reflected or copied inferred theorem types. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace Zeta23.OPICAFollowup.Validation
open Zeta23.OPICA Zeta23.OPICAFollowup

theorem expected_ct13_original_pairing {L : ℝ} (hL : 0 < L) (hlog : L < Real.log 2) :
    (nearGapCombFamily L).integral sincSquared =
      2 * (Real.exp L - 1) / (Real.exp L) ^ (3 / 2 : ℝ) ∧
    (nearGapCombFamily L).integral unitTriangle =
      2 * (Real.exp L - 1) / (Real.exp L) ^ (3 / 2 : ℝ) := by
  refine ⟨CT13Support.sinc_identity_original hL hlog, ?_⟩
  exact (signed_sinc_triangle_pairing _ (nearGapCombFamily_growth L)
    (nearGapCombFamily_fourier_selfdual L)).symm.trans (CT13Support.sinc_identity_original hL hlog)

theorem expected_ct13_jordan_masses {L : ℝ} (hL : 0 < L) (hlog : L < Real.log 2) :
    (∫ x, sincSquared x ∂(nearGapCombFamily L).negative) = 0 ∧
    (∫ x, sincSquared x ∂(nearGapCombFamily L).positive) =
      2 * (Real.exp L - 1) / (Real.exp L) ^ (3 / 2 : ℝ) := by
  refine ⟨CT13Support.negative_sinc_mass_zero hL, ?_⟩
  exact (CT13Support.positive_sinc_mass hL hlog).trans
    ((CT13Support.sinc_identity hL hlog).symm.trans (CT13Support.sinc_identity_original hL hlog))

theorem expected_ct13_first_order_cost :
    Tendsto (fun L : ℝ => (∫ x, sincSquared x ∂(nearGapCombFamily L).positive) / L)
      (𝓝[>] 0) (𝓝 2) :=
  CT13Support.positive_sinc_mass_slope

theorem expected_ct13_second_order_cost :
    Tendsto (fun L : ℝ => (∫ x, sincSquared x ∂(nearGapCombFamily L).positive) / L ^ 2)
      (𝓝[>] 0) atTop :=
  CT13Support.positive_sinc_mass_normalization_cost

/-- The family is outside the exact-unit-gap domain of the zero-jet span. -/
theorem expected_ct13_not_unit_gap {L : ℝ} (hL : 0 < L) (hlog : L < Real.log 2) :
    ¬(nearGapCombFamily L).HasUnitGap := by
  intro hgap
  have hx : ({Real.exp (-L)} : Set ℝ) ⊆ Ioo (-1 : ℝ) 1 := by
    intro x hx
    have heq : x = Real.exp (-L) := hx
    subst x
    exact ⟨by linarith [Real.exp_pos (-L)], (nearGapComb_radius_bounds hL hlog).2⟩
  have hz := measure_mono_null hx hgap.1
  have hm := (nearGapCombFamily_gap_edge_atom hL hlog).1
  change ((nearGapCombFamily L).positive {Real.exp (-L)}).toReal = _ at hm
  rw [hz, ENNReal.toReal_zero] at hm
  exact Real.exp_ne_zero _ hm.symm

end Zeta23.OPICAFollowup.Validation
#print axioms Zeta23.OPICAFollowup.Validation.expected_ct13_original_pairing
#print axioms Zeta23.OPICAFollowup.Validation.expected_ct13_jordan_masses
#print axioms Zeta23.OPICAFollowup.Validation.expected_ct13_first_order_cost
#print axioms Zeta23.OPICAFollowup.Validation.expected_ct13_second_order_cost
#print axioms Zeta23.OPICAFollowup.Validation.expected_ct13_not_unit_gap

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology ENNReal FourierTransform SchwartzMap
namespace Zeta23.OPICAFollowup.Validation
open Zeta23.OPICA

/- Literal actual-measure expected statement for the missing HT2 local
continuous-test topology. No assumed compact-test convergence is an input. -/
theorem expected_full_HT2_compact_continuous_extraction
    (ν : ℕ → LocallyFiniteSignedMeasure) (C : ℝ)
    (common : ∀ n, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      (ν n).totalVariation.real (Icc (-R) R) ≤ C*(1+R))
    (growth : ∀ n, (ν n).HasLinearGrowth)
    (selfdual : ∀ n, (ν n).FourierSelfdual (growth n))
    (positiveOff : ∀ n, (ν n).negative integerLatticeᶜ = 0)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n ∧ a n ≤ 1)
    (gap : ∀ n, (ν n).positive (Ioo (-a n) (a n)) = 0 ∧
      (ν n).negative (Ioo (-a n) (a n)) = 0)
    (sharp : Tendsto a atTop (𝓝 1)) :
    (∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f →
      Tendsto (fun n => (∫ x, f x ∂(ν n).positive) - (∫ x, f x ∂(ν n).negative))
        atTop (𝓝 0)) ∧
    ∃ s : ℕ → ℕ, ∃ μ : LocallyFiniteSignedMeasure,
      StrictMono s ∧ μ.positive = 0 ∧ μ.negative = 0 ∧ μ.HasLinearGrowth ∧
      ∀ f : ℝ → ℂ, Continuous f → HasCompactSupport f →
        Tendsto (fun n => (∫ x, f x ∂(ν (s n)).positive) -
          (∫ x, f x ∂(ν (s n)).negative)) atTop
          (𝓝 ((∫ x, f x ∂μ.positive) - (∫ x, f x ∂μ.negative))) := by
  constructor
  · intro f continuous compact
    simpa only [IndependentCompactExtraction.extractedZeroMeasure, integral_zero_measure, sub_self] using
      IndependentCompactExtraction.expected_near_gap_compact_continuous_limit_zero
        ν C common growth selfdual positiveOff a ha gap sharp f continuous compact
  · exact IndependentCompactExtraction.expected_near_gap_genuine_zero_measure_extraction
      ν C common growth selfdual positiveOff a ha gap sharp

#print axioms Zeta23.OPICAFollowup.Validation.expected_full_HT2_compact_continuous_extraction
end Zeta23.OPICAFollowup.Validation



noncomputable section
open Set MeasureTheory Complex
open scoped ENNReal
open Zeta23.OPICA

namespace Zeta23.OPICAFollowup.Validation

/-- Independently packaged full complex weighted inverse contract.  The four
coordinates belong to the actual physical mixture, rather than caller-supplied
eta data.  Both complex coordinate equations and the absolute convolution
integrals are retained. -/
def independentlyIntendedComplexMobius
    (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a sigma < (∞ : ℝ≥0∞)) : Prop :=
  let physical := weightedDilationMixture sigma a ha.le hm
  let etaReP := positiveLogMeasure physical.rePart.positive
  let etaReN := positiveLogMeasure physical.rePart.negative
  let etaImP := positiveLogMeasure physical.imPart.positive
  let etaImN := positiveLogMeasure physical.imPart.negative
  let absoluteMobius := moebiusPlusComb + moebiusMinusComb
  -- eta = N * sigma, with BOTH real and imaginary coordinates.
  (etaReP + integerLogComb ∗ sigma.rePart.negative =
    etaReN + integerLogComb ∗ sigma.rePart.positive) ∧
  (etaImP + integerLogComb ∗ sigma.imPart.negative =
    etaImN + integerLogComb ∗ sigma.imPart.positive) ∧
  -- sigma = M_mu * eta, with BOTH real and imaginary coordinates.
  (sigma.rePart.positive +
      (moebiusPlusComb ∗ etaReN + moebiusMinusComb ∗ etaReP) =
    sigma.rePart.negative +
      (moebiusPlusComb ∗ etaReP + moebiusMinusComb ∗ etaReN)) ∧
  (sigma.imPart.positive +
      (moebiusPlusComb ∗ etaImN + moebiusMinusComb ∗ etaImP) =
    sigma.imPart.negative +
      (moebiusPlusComb ∗ etaImP + moebiusMinusComb ∗ etaImN)) ∧
  -- All physical input/output coordinates lie in the weighted algebra.
  (∀ i : Fin 4, weightedLogNorm a (mixingCoordinate sigma i) < (∞ : ℝ≥0∞)) ∧
  (∀ i : Fin 4, weightedLogNorm a
    (positiveLogMeasure (mixingCoordinate physical i)) < (∞ : ℝ≥0∞)) ∧
  -- Absolute weighted Fubini for every coordinate, including imaginary ones.
  (∀ i : Fin 4, weightedLogNorm a
    (absoluteMobius ∗ positiveLogMeasure (mixingCoordinate physical i)) < (∞ : ℝ≥0∞)) ∧
  (∀ i : Fin 4,
    (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (-a * (x + y)))
      ∂(positiveLogMeasure (mixingCoordinate physical i)) ∂absoluteMobius) < (∞ : ℝ≥0∞)) ∧
  -- The positive/negative physical Mobius combs form its Jordan pair.
  (moebiusPlusComb ⟂ₘ moebiusMinusComb) ∧
  -- Exact weighted variation norm, not merely an upper bound.
  weightedLogNorm a absoluteMobius = ENNReal.ofReal
    ((riemannZeta ((a + 1 / 2 : ℝ) : ℂ) /
      riemannZeta ((2 * a + 1 : ℝ) : ℂ)).re)

theorem expected_independent_complete_complex_mobius
    (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a sigma < (∞ : ℝ≥0∞)) :
    independentlyIntendedComplexMobius sigma a ha hm
    := by
  rcases weighted_mobius_inverse sigma a ha hm with
    ⟨hraw, hre, him, hunit, hinvre, hinvim, hsigma, heta, hmul, hn, hmobius⟩
  let physical := weightedDilationMixture sigma a ha.le hm
  have hetaAll (i : Fin 4) : weightedLogNorm a
      (positiveLogMeasure (mixingCoordinate physical i)) < (∞ : ℝ≥0∞) := by
    fin_cases i
    · exact heta.1
    · exact heta.2.1
    · exact heta.2.2.1
    · exact heta.2.2.2
  have habsolute : weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) < (∞ : ℝ≥0∞) := by
    rw [weightedLogNorm_add]
    exact ENNReal.add_lt_top.mpr (weightedLogNorm_moebiusComb_lt_top ha)
  have hconv (i : Fin 4) : weightedLogNorm a
      ((moebiusPlusComb + moebiusMinusComb) ∗
        positiveLogMeasure (mixingCoordinate physical i)) < (∞ : ℝ≥0∞) := by
    rw [hmul]
    exact ENNReal.mul_lt_top habsolute (hetaAll i)
  have hfubini (i : Fin 4) :
      (∫⁻ x, ∫⁻ y, ENNReal.ofReal (Real.exp (-a * (x + y)))
        ∂(positiveLogMeasure (mixingCoordinate physical i))
        ∂(moebiusPlusComb + moebiusMinusComb)) < (∞ : ℝ≥0∞) := by
    rw [← Measure.lintegral_conv (by fun_prop :
      Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (-a * z))))]
    exact hconv i
  have hexact : weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) =
      ENNReal.ofReal ((riemannZeta ((a + 1 / 2 : ℝ) : ℂ) /
        riemannZeta ((2 * a + 1 : ℝ) : ℂ)).re) := by
    rw [hmobius.2.1]
    exact congrArg ENNReal.ofReal (by simpa using congrArg Complex.re hmobius.2.2)
  exact ⟨hre, him, hinvre, hinvim, hsigma, hetaAll, hconv, hfubini, hmobius.1, hexact⟩

#print axioms Zeta23.OPICAFollowup.Validation.expected_independent_complete_complex_mobius

/-- Postseal auxiliary interface: these explicit clauses were added only after
inspection of the production root.  No blind-authorship claim is made for them.
Together with the independently sealed core they preserve every original root
interface clause, while the core also exposes finite absolute double integrals. -/
def postSealMobiusAuxiliaryInterface
    (sigma : LocallyFiniteComplexMeasure) (a : ℝ) : Prop :=
  (∀ i : Fin 4, positiveLogMeasure (positiveDilationMixture (mixingCoordinate sigma i)) =
    integerLogComb ∗ mixingCoordinate sigma i) ∧
  (moebiusPlusComb ∗ integerLogComb =
    Measure.dirac 0 + moebiusMinusComb ∗ integerLogComb) ∧
  (∀ (mu rho : Measure ℝ) [SFinite rho],
    weightedLogNorm a (mu ∗ rho) = weightedLogNorm a mu * weightedLogNorm a rho) ∧
  (weightedLogNorm a integerLogComb = ENNReal.ofReal
      (∑' n : ℕ, (n : ℝ) ^ (-(a + 1 / 2))) ∧
    ((∑' n : ℕ, (n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) =
      riemannZeta ((a + 1 / 2 : ℝ) : ℂ)) ∧
  (weightedLogNorm a (moebiusPlusComb + moebiusMinusComb) = ENNReal.ofReal
      (∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2))) ∧
    ((∑' n : ℕ, (|ArithmeticFunction.moebius n| : ℝ) * (n : ℝ) ^ (-(a + 1 / 2)) : ℝ) : ℂ) =
      riemannZeta ((a + 1 / 2 : ℝ) : ℂ) / riemannZeta ((2 * a + 1 : ℝ) : ℂ))

theorem expected_independent_complex_mobius_full_interface
    (sigma : LocallyFiniteComplexMeasure) (a : ℝ)
    (ha : 1 / 2 < a) (hm : mixingExponentialMoment a sigma < (∞ : ℝ≥0∞)) :
    independentlyIntendedComplexMobius sigma a ha hm ∧
      postSealMobiusAuxiliaryInterface sigma a := by
  rcases weighted_mobius_inverse sigma a ha hm with
    ⟨hraw, hre, him, hunit, hinvre, hinvim, hsigma, heta, hmul, hn, hmobius⟩
  refine ⟨expected_independent_complete_complex_mobius sigma a ha hm, ?_⟩
  exact ⟨hraw, hunit, hmul, hn, hmobius.2.1, hmobius.2.2⟩

#print axioms Zeta23.OPICAFollowup.Validation.expected_independent_complex_mobius_full_interface

end Zeta23.OPICAFollowup.Validation




noncomputable section
open Set MeasureTheory Filter Complex
open scoped Topology FourierTransform SchwartzMap

namespace Zeta23.OPICAFollowup.Validation

/-! This compound preserves both existing interfaces as genuine conjuncts.
Authored by the contract reviewer as an implementation leaf at the owner's
explicit request; its independent semantic review must come from the owner or
another nonauthor. It is not a new primary root or an approval artifact. -/

theorem expected_square_original_and_full_distribution_domain
    {h : ℝ → ℂ} {A : ℂ}
    (hev : ∀ x, h (-x) = h x) (hcont : Continuous h) (hint : Integrable h)
    (hL2 : MemLp h 2) (hsd : 𝓕 h = h)
    (hvan : Tendsto h (cocompact ℝ) (𝓝 0))
    (hpl : ∀ x, |x| ≤ 1 → h x = A) (hne : h ≠ 0) :
    (¬ ∃ c : ℤ → ℂ, TemperedLatticeWeights c ∧
      ∀ φ : 𝓢(ℝ, ℂ),
        squareGapMeasure h A (𝓕 φ) + latticePairing c (𝓕 φ) =
          squareGapMeasure h A φ + latticePairing c φ) ∧
    (∀ (σ : LocallyFiniteComplexMeasure) (T : TemperedDistribution ℝ ℂ),
      σ.totalVariation (Set.range (fun n : ℤ => (n : ℝ)))ᶜ = 0 →
      (∀ φ : 𝓢(ℝ, ℂ), HasCompactSupport (φ : ℝ → ℂ) →
        T φ = σ.integral φ) →
      𝓕 ((squareGapJordan h A hcont).distributionOfLinearGrowth
          (squareGapJordan_growth hcont hvan A) + T) ≠
        (squareGapJordan h A hcont).distributionOfLinearGrowth
          (squareGapJordan_growth hcont hvan A) + T) := by
  refine ⟨square_no_lattice_repair hev hcont hint hL2 hsd hvan hpl hne, ?_⟩
  intro σ T hσ hT
  exact square_actual_no_distribution_tempered_measure_repair
    hev hcont hint hL2 hsd hvan hpl hne σ T hσ hT

#print axioms Zeta23.OPICAFollowup.Validation.expected_square_original_and_full_distribution_domain

end Zeta23.OPICAFollowup.Validation
