import Zeta23.OPICARound2.CausalProbe
import Zeta23.OPICARound2.FixedFilter
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Actual finite probe geometry

All dictionary columns are the unchanged causal outputs. The finite geometry
uses their actual Hilbert inner products and never assumes Gram invertibility.
-/

noncomputable section

open Set MeasureTheory Matrix
open scoped Topology ENNReal BigOperators ComplexConjugate ComplexOrder

namespace Zeta23.OPICARound2

def probeQ0 : ℝ := ‖probeTarget‖ ^ 2

def probeGram (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.gram ℂ (fun i : Fin N => probeColumn (i.val + 1))

def probeTargetColumn (N : ℕ) (i : Fin N) : ℂ :=
  inner ℂ (probeColumn (i.val + 1)) probeTarget

def probeSynthesis (N : ℕ) : (Fin N → ℂ) →ₗ[ℂ] CausalProbeL2 :=
  Fintype.linearCombination ℂ (fun i : Fin N => probeColumn (i.val + 1))

theorem probeSynthesis_apply {N : ℕ} (x : Fin N → ℂ) :
    probeSynthesis N x = probeFiniteOutput x := rfl

def probeFiniteSpace (N : ℕ) : Submodule ℂ CausalProbeL2 :=
  LinearMap.range (probeSynthesis N)

instance probeFiniteSpace_finiteDimensional (N : ℕ) :
    FiniteDimensional ℂ (probeFiniteSpace N) :=
  LinearMap.finiteDimensional_range (probeSynthesis N)

instance probeFiniteSpace_completeSpace (N : ℕ) : CompleteSpace (probeFiniteSpace N) :=
  FiniteDimensional.complete ℂ (probeFiniteSpace N)

def probeBestOutput (N : ℕ) : CausalProbeL2 :=
  ((probeFiniteSpace N).orthogonalProjectionOnto probeTarget : CausalProbeL2)

def probeError (N : ℕ) : ℝ := ‖probeTarget - probeBestOutput N‖

theorem probeBestOutput_mem (N : ℕ) : probeBestOutput N ∈ probeFiniteSpace N :=
  ((probeFiniteSpace N).orthogonalProjectionOnto probeTarget).property

theorem probeBestOutput_exists_coefficients (N : ℕ) :
    ∃ x : Fin N → ℂ, probeFiniteOutput x = probeBestOutput N := by
  rcases probeBestOutput_mem N with ⟨x, hx⟩
  exact ⟨x, hx⟩

theorem probeFiniteSpace_le_range (N : ℕ) :
    (probeFiniteSpace N : Set CausalProbeL2) ⊆ Set.range probeOperator := by
  rintro g ⟨x, rfl⟩
  exact probeFiniteOutput_mem_range x

theorem probeBestOutput_mem_range (N : ℕ) :
    probeBestOutput N ∈ Set.range probeOperator :=
  probeFiniteSpace_le_range N (probeBestOutput_mem N)

theorem probeError_nonneg (N : ℕ) : 0 ≤ probeError N := norm_nonneg _

def probeEvaluation (z : ℂ) (hz : 0 < z.re) : CausalProbeL2 →L[ℂ] ℂ :=
  innerSL ℂ (CCM.nativeCausalExponentialWitness z hz 0)

theorem probeEvaluation_apply (z : ℂ) (hz : 0 < z.re) (f : CausalProbeL2) :
    probeEvaluation z hz f = CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) :=
  CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment z hz 0 f

theorem probeFiniteOutput_laplace (z : ℂ) (hz : 0 < z.re) {N : ℕ} (x : Fin N → ℂ) :
    CCM.nativeCausalLaplaceMoment z 0 (probeFiniteOutput x : ProbeL2) =
      ∑ i : Fin N, x i * CCM.nativeCausalLaplaceMoment z 0
        (probeColumn (i.val + 1) : ProbeL2) := by
  simp only [← probeEvaluation_apply z hz, probeFiniteOutput, map_sum, map_smul,
    smul_eq_mul]

/-- On this real half-line, nonvanishing follows from the actual one-copy
product and ordinary zeta, independently of any source support endpoint. -/
theorem probeW_laplace_real_ne_zero {x : ℝ} (hx : 1 < x) :
    probeLaplace probeW (x : ℂ) ≠ 0 := by
  have hp : 0 < (x : ℂ).re := by simpa using lt_trans zero_lt_one hx
  have hhalf : (x : ℂ) ≠ (1 / 2 : ℂ) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith
  have hR : CCM.nativeCompletionRationalMultiplier (x : ℂ) ≠ 0 := by
    unfold CCM.nativeCompletionRationalMultiplier
    apply div_ne_zero
    · intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      linarith
    · apply mul_ne_zero
      all_goals
        intro h
        have hr := congrArg Complex.re h
        norm_num at hr
        linarith
  have hpoly : ((Complex.I * (x : ℂ)) ^ 2 + 1 / 4) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [mul_pow, Complex.I_sq, ← Complex.ofReal_pow] at hr
    nlinarith
  have hQ : CCM.UniversalSinc.product probeSigma (Complex.I * (x : ℂ)) ≠ 0 := by
    apply CCM.UniversalSinc.product_ne_zero_of_im_ne_zero probeSigma_pos
    simpa using ne_of_gt (lt_trans zero_lt_one hx)
  have hJ : JPlus (x : ℂ) ≠ 0 := by
    rw [JPlus_one_copy_formula]
    exact mul_ne_zero (Complex.exp_ne_zero _) (mul_ne_zero (pow_ne_zero 2 hpoly) hQ)
  rw [probeW_laplace hp hhalf]
  exact mul_ne_zero (mul_ne_zero hR
    (riemannZeta_ne_zero_of_one_lt_re (by simpa using (show 1 < x + 1 / 2 by linarith)))) hJ

/-- The real-exponential power characters used in a finite Dirichlet uniqueness
argument. This is a family of literal characters, not a basis hypothesis. -/
def probePowerCharacter (x : ℝ) : Multiplicative ℕ →* ℂ where
  toFun k := Complex.exp (-(x : ℂ)) ^ Multiplicative.toAdd k
  map_one' := by simp
  map_mul' a b := by simp [pow_add]

theorem probePowerCharacter_injective : Function.Injective probePowerCharacter := by
  intro x y h
  have he := DFunLike.congr_fun h (Multiplicative.ofAdd 1)
  have hr := congrArg Complex.re he
  simp only [probePowerCharacter, MonoidHom.coe_mk, OneHom.coe_mk,
    toAdd_ofAdd, pow_one] at hr
  have hr' : Real.exp (-x) = Real.exp (-y) := by
    simpa only [← Complex.ofReal_neg, ← Complex.ofReal_exp, Complex.ofReal_re] using hr
  exact neg_injective (Real.exp_injective hr')

theorem probe_log_indices_injective (N : ℕ) :
    Function.Injective (fun i : Fin N => Real.log (i.val + 1 : ℕ)) := by
  intro i j h
  have hij : (i.val + 1 : ℝ) = (j.val + 1 : ℝ) :=
    Real.log_injOn_pos (show (i.val + 1 : ℝ) ∈ Ioi 0 by simp only [Set.mem_Ioi]; positivity)
      (show (j.val + 1 : ℝ) ∈ Ioi 0 by simp only [Set.mem_Ioi]; positivity)
      (by simpa only [Nat.cast_add, Nat.cast_one] using h)
  apply Fin.ext
  exact_mod_cast (by linarith : (i.val : ℝ) = j.val)

theorem probePowerCharacters_linearIndependent (N : ℕ) :
    LinearIndependent ℂ (fun i : Fin N =>
      (probePowerCharacter (Real.log (i.val + 1 : ℕ)) : Multiplicative ℕ → ℂ)) :=
  (linearIndependent_monoidHom (Multiplicative ℕ) ℂ).comp
    (fun i : Fin N => probePowerCharacter (Real.log (i.val + 1 : ℕ)))
    (probePowerCharacter_injective.comp (probe_log_indices_injective N))

theorem probeColumn_integer_laplace (k : ℕ) {n : ℕ} (hn : n ≠ 0) :
    CCM.nativeCausalLaplaceMoment ((k + 2 : ℕ) : ℂ) 0 (probeColumn n : ProbeL2) =
      ((CCM.nativeIntegerCoefficient n : ℂ) * Complex.exp (-(Real.log n : ℂ)) ^ 2) *
        Complex.exp (-(Real.log n : ℂ)) ^ k *
          probeLaplace probeW ((k + 2 : ℕ) : ℂ) := by
  rw [probeColumn_laplace _ (by norm_num; positivity) hn]
  have he : -((k + 2 : ℕ) : ℂ) * (Real.log n : ℂ) =
      ((k + 2 : ℕ) : ℂ) * (-(Real.log n : ℂ)) := by ring
  rw [he, Complex.exp_nat_mul, pow_add]
  ring

theorem probeColumns_linearIndependent (N : ℕ) :
    LinearIndependent ℂ (fun i : Fin N => probeColumn (i.val + 1)) := by
  classical
  apply Fintype.linearIndependent_iff.2
  intro x hx i
  let c : Fin N → ℂ := fun j =>
    x j * (CCM.nativeIntegerCoefficient (j.val + 1) : ℂ) *
      Complex.exp (-(Real.log (j.val + 1 : ℕ) : ℂ)) ^ 2
  have hcharacters : ∑ j : Fin N,
      c j • (probePowerCharacter (Real.log (j.val + 1 : ℕ)) : Multiplicative ℕ → ℂ) = 0 := by
    funext k
    have hkpos : 0 < (((Multiplicative.toAdd k + 2 : ℕ) : ℂ)).re := by
      simp only [Complex.natCast_re]
      exact_mod_cast (show 0 < Multiplicative.toAdd k + 2 by omega)
    have hEval := congrArg (probeEvaluation ((Multiplicative.toAdd k + 2 : ℕ) : ℂ)
      hkpos) hx
    have hcomb : CCM.nativeCausalLaplaceMoment ((Multiplicative.toAdd k + 2 : ℕ) : ℂ) 0
        (probeFiniteOutput x : ProbeL2) = 0 := by
      rw [← probeEvaluation_apply _ hkpos]
      simpa only [probeFiniteOutput, map_zero] using hEval
    rw [probeFiniteOutput_laplace _ hkpos x] at hcomb
    simp_rw [probeColumn_integer_laplace (Multiplicative.toAdd k) (Nat.succ_ne_zero _)] at hcomb
    have hW : probeLaplace probeW ((Multiplicative.toAdd k + 2 : ℕ) : ℂ) ≠ 0 := by
      exact probeW_laplace_real_ne_zero (x := (Multiplicative.toAdd k + 2 : ℕ))
        (by exact_mod_cast (show 1 < Multiplicative.toAdd k + 2 by omega))
    have hf : (∑ j : Fin N, x j *
        (((CCM.nativeIntegerCoefficient (j.val + 1) : ℂ) *
          Complex.exp (-(Real.log (j.val + 1 : ℕ) : ℂ)) ^ 2) *
          Complex.exp (-(Real.log (j.val + 1 : ℕ) : ℂ)) ^ Multiplicative.toAdd k)) *
        probeLaplace probeW ((Multiplicative.toAdd k + 2 : ℕ) : ℂ) = 0 := by
      simpa only [Finset.sum_mul, mul_assoc] using hcomb
    have hs := (mul_eq_zero.mp hf).resolve_right hW
    simpa only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      probePowerCharacter, MonoidHom.coe_mk, OneHom.coe_mk, c, mul_assoc] using hs
  have hc := Fintype.linearIndependent_iff.1 (probePowerCharacters_linearIndependent N)
    c hcharacters i
  have hn : (CCM.nativeIntegerCoefficient (i.val + 1) : ℂ) ≠ 0 := by
    apply Complex.ofReal_ne_zero.mpr
    unfold CCM.nativeIntegerCoefficient
    apply one_div_ne_zero
    exact ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have he : Complex.exp (-(Real.log (i.val + 1 : ℕ) : ℂ)) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Complex.exp_ne_zero _)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hc).resolve_right he)).resolve_right hn

theorem probe_finite_gram_positive (N : ℕ) : (probeGram N).PosDef :=
  Matrix.posDef_gram_of_linearIndependent (probeColumns_linearIndependent N)

theorem rh_of_probe_residual_limit (N : ℕ → ℕ)
    (x : ∀ k : ℕ, Fin (N k) → ℂ)
    (h : Filter.Tendsto (fun k => ‖probeResidual (x k)‖) Filter.atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply rh_of_native_probe_range
  have hconv : Filter.Tendsto (fun k => probeFiniteOutput (x k)) Filter.atTop
      (𝓝 probeTarget) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa only [probeResidual, norm_sub_rev] using h
  exact isClosed_closure.mem_of_tendsto hconv
    (Filter.Eventually.of_forall fun k => subset_closure (probeFiniteOutput_mem_range (x k)))

theorem rh_of_probe_error_subsequence_limit (N : ℕ → ℕ)
    (h : Filter.Tendsto (fun k => probeError (N k)) Filter.atTop (𝓝 0)) :
    RiemannHypothesis := by
  choose x hx using fun k => probeBestOutput_exists_coefficients (N k)
  apply rh_of_probe_residual_limit N x
  simpa only [probeResidual, hx, probeError] using h

theorem rh_of_probe_error_limit
    (h : Filter.Tendsto probeError Filter.atTop (𝓝 0)) : RiemannHypothesis :=
  rh_of_probe_error_subsequence_limit id h

theorem probeV_conj (t : ℝ) : conj (probeV t) = probeV t := by
  rw [probeV_eq_real_integral]
  exact Complex.conj_ofReal _

def probeTailRemainder (t : ℝ) : ℂ := probeV t -
  if 0 ≤ t then 2 * JPlus (-3 / 2 : ℂ) *
    Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) else 0

theorem probeTailRemainder_hasCompactSupport : HasCompactSupport probeTailRemainder := by
  apply HasCompactSupport.intro (K := Icc 0 (2 * probeSigma)) isCompact_Icc
  intro t ht
  have hcases : t < 0 ∨ 2 * probeSigma < t := by
    simpa only [mem_Icc, not_and_or, not_le] using ht
  rcases hcases with hneg | hafter
  · simp only [probeTailRemainder, if_neg (not_le.mpr hneg),
      probeV_zero_of_neg hneg, sub_zero]
  · rw [probeTailRemainder, if_pos (by linarith [probeSigma_pos]),
      probeV_tail hafter.le, sub_self]

theorem probeNativeJ_neg (z : ℂ) :
    CCM.nativeOriginalSourceLaplace (-z) = CCM.nativeOriginalSourceLaplace z := by
  rw [ExceptionalZero.nativeOriginalSourceLaplace_formula,
    ExceptionalZero.nativeOriginalSourceLaplace_formula]
  simp only [mul_neg, neg_sq, CCM.UniversalSinc.product_neg]

theorem JPlus_opposite_product (z : ℂ) :
    JPlus (-z) * JPlus z = CCM.nativeOriginalSourceLaplace z ^ 2 := by
  rw [JPlus_eq_delay, JPlus_eq_delay, probeNativeJ_neg]
  have he : Complex.exp (-(-z) * (probeSigma : ℂ)) *
      Complex.exp (-z * (probeSigma : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero using 2 <;> ring
  calc
    _ = (Complex.exp (-(-z) * (probeSigma : ℂ)) *
      Complex.exp (-z * (probeSigma : ℂ))) * CCM.nativeOriginalSourceLaplace z ^ 2 := by ring
    _ = _ := by rw [he, one_mul]

/-- This constant belongs to the v-shift correlation, not the w-dictionary Gram. -/
def probeCorrelationConstant : ℂ := CCM.nativeOriginalSourceLaplace (3 / 2 : ℂ) ^ 2 / 3

def probeCorrelation (L : ℝ) : ℂ :=
  ∫ t : ℝ, conj (probeV t) * probeV (t + L)

theorem probeCorrelation_nonneg_separation {L : ℝ} (hL : 2 * probeSigma ≤ L) :
    probeCorrelation L = probeCorrelationConstant *
      Complex.exp (-(3 / 2 : ℂ) * (L : ℂ)) := by
  have hp (t : ℝ) : conj (probeV t) * probeV (t + L) =
      (2 * JPlus (-3 / 2 : ℂ) * Complex.exp (-(3 / 2 : ℂ) * (L : ℂ))) *
        (Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) * probeV t) := by
    by_cases ht : t < 0
    · rw [probeV_zero_of_neg ht, map_zero, zero_mul, mul_zero, mul_zero]
    · rw [probeV_conj, probeV_tail (t := t + L) (by linarith [le_of_not_gt ht])]
      have he : Complex.exp (-(3 / 2 : ℂ) * ((t + L : ℝ) : ℂ)) =
          Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) *
            Complex.exp (-(3 / 2 : ℂ) * (L : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [he]
      ring
  rw [probeCorrelation, integral_congr_ae (Filter.Eventually.of_forall hp), integral_const_mul]
  change (2 * JPlus (-3 / 2 : ℂ) * Complex.exp (-(3 / 2 : ℂ) * (L : ℂ))) *
    probeLaplace probeV (3 / 2 : ℂ) = _
  rw [probeV_laplace (by norm_num)]
  have hR : CCM.nativeCompletionRationalMultiplier (3 / 2 : ℂ) = 1 / 6 := by
    norm_num [CCM.nativeCompletionRationalMultiplier]
  rw [hR]
  calc
    _ = (JPlus (-(3 / 2 : ℂ)) * JPlus (3 / 2 : ℂ) / 3) *
      Complex.exp (-(3 / 2 : ℂ) * (L : ℂ)) := by ring
    _ = _ := by rw [JPlus_opposite_product]; rfl

theorem probeCorrelation_neg (L : ℝ) : probeCorrelation (-L) = probeCorrelation L := by
  have h := integral_sub_right_eq_self
    (fun t : ℝ => conj (probeV t) * probeV (t + L)) L
    (μ := (volume : Measure ℝ))
  change _ = probeCorrelation L at h
  rw [← h]
  apply integral_congr_ae
  filter_upwards with t
  simp only [probeV_conj, sub_add_cancel]
  rw [show t + -L = t - L by ring]
  ring

theorem probeCorrelation_separated {L : ℝ} (hL : 2 * probeSigma ≤ |L|) :
    probeCorrelation L = probeCorrelationConstant *
      Complex.exp (-(3 / 2 : ℂ) * ((|L| : ℝ) : ℂ)) := by
  by_cases hpos : 0 ≤ L
  · rw [abs_of_nonneg hpos] at hL ⊢
    exact probeCorrelation_nonneg_separation hL
  · have hneg : L < 0 := lt_of_not_ge hpos
    rw [abs_of_neg hneg] at hL ⊢
    rw [← probeCorrelation_neg L]
    exact probeCorrelation_nonneg_separation hL

theorem probeTargetShift_inner (s t : ℝ) :
    inner ℂ (CCM.nativeCompletionL2Delay s (probeTarget : ProbeL2))
      (CCM.nativeCompletionL2Delay t (probeTarget : ProbeL2)) = probeCorrelation (s - t) := by
  rw [L2.inner_def]
  have hrep (a : ℝ) : CCM.nativeCompletionL2Delay a (probeTarget : ProbeL2) =ᵐ[volume]
      fun x : ℝ => probeV (x - a) := by
    have hshift := (measurePreserving_sub_right volume a).quasiMeasurePreserving.ae_eq
      probeTarget_coeFn
    filter_upwards [CCM.nativeCompletionL2Delay_coeFn a (probeTarget : ProbeL2), hshift]
      with x hx hs
    dsimp only [Function.comp_def] at hs
    rw [hx, hs]
  calc
    _ = ∫ x : ℝ, conj (probeV (x - s)) * probeV (x - t) := by
      apply integral_congr_ae
      filter_upwards [hrep s, hrep t] with x hs ht
      rw [hs, ht, RCLike.inner_apply']
    _ = ∫ x : ℝ, (fun u : ℝ => conj (probeV u) * probeV (u + (s - t))) (x - s) := by
      apply integral_congr_ae
      filter_upwards with x
      congr 2
      ring
    _ = _ := integral_sub_right_eq_self
      (fun u : ℝ => conj (probeV u) * probeV (u + (s - t))) s
      (μ := (volume : Measure ℝ))

def probeTargetShiftGram {ι : Type*} (lags : ι → ℝ) : Matrix ι ι ℂ :=
  Matrix.gram ℂ (fun i => CCM.nativeCompletionL2Delay (lags i) (probeTarget : ProbeL2))

theorem probeTargetShiftGram_separated {ι : Type*} [DecidableEq ι] (lags : ι → ℝ)
    (hsep : ∀ i j, i ≠ j → 2 * probeSigma ≤ |lags i - lags j|) (i j : ι) :
    probeTargetShiftGram lags i j = if i = j then (probeQ0 : ℂ) else
      probeCorrelationConstant * Complex.exp (-(3 / 2 : ℂ) *
        ((|lags i - lags j| : ℝ) : ℂ)) := by
  by_cases hij : i = j
  · subst j
    simp [probeTargetShiftGram, Matrix.gram_apply,
      inner_self_eq_norm_sq_to_K, CCM.nativeCompletionL2Delay_norm, probeQ0]
  · rw [if_neg hij]
    change inner ℂ (CCM.nativeCompletionL2Delay (lags i) (probeTarget : ProbeL2))
      (CCM.nativeCompletionL2Delay (lags j) (probeTarget : ProbeL2)) = _
    rw [probeTargetShift_inner]
    exact probeCorrelation_separated (hsep i j hij)

theorem probe_tail_and_correlation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (lags : ι → ℝ) (hsep : ∀ i j, i ≠ j → 2 * probeSigma ≤ |lags i - lags j|) :
    (∀ t : ℝ, 2 * probeSigma ≤ t → probeV t =
      2 * JPlus (-3 / 2 : ℂ) * Complex.exp (-(3 / 2 : ℂ) * (t : ℂ))) ∧
    HasCompactSupport probeTailRemainder ∧
    (∀ L : ℝ, 2 * probeSigma ≤ |L| → probeCorrelation L =
      probeCorrelationConstant * Complex.exp (-(3 / 2 : ℂ) * ((|L| : ℝ) : ℂ))) ∧
    (∀ i j, probeTargetShiftGram lags i j = if i = j then (probeQ0 : ℂ) else
      probeCorrelationConstant * Complex.exp (-(3 / 2 : ℂ) *
        ((|lags i - lags j| : ℝ) : ℂ))) :=
  ⟨fun _ ht => probeV_tail ht, probeTailRemainder_hasCompactSupport,
    fun _ hL => probeCorrelation_separated hL, probeTargetShiftGram_separated lags hsep⟩

theorem probeGram_det_ne_zero (N : ℕ) : (probeGram N).det ≠ 0 :=
  Matrix.det_gram_ne_zero_iff_linearIndependent.2 (probeColumns_linearIndependent N)

def probePairings (N : ℕ) (f : CausalProbeL2) (i : Fin N) : ℂ :=
  inner ℂ (probeColumn (i.val + 1)) f

def probeProjectionCoefficients (N : ℕ) (f : CausalProbeL2) : Fin N → ℂ :=
  (probeGram N)⁻¹ *ᵥ probePairings N f

theorem probeProjectionCoefficients_normal (N : ℕ) (f : CausalProbeL2) :
    probeGram N *ᵥ probeProjectionCoefficients N f = probePairings N f := by
  unfold probeProjectionCoefficients
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    (isUnit_iff_ne_zero.2 (probeGram_det_ne_zero N)), Matrix.one_mulVec]

theorem probeColumn_inner_output {N : ℕ} (i : Fin N) (x : Fin N → ℂ) :
    inner ℂ (probeColumn (i.val + 1)) (probeFiniteOutput x) =
      (probeGram N *ᵥ x) i := by
  simp only [probeFiniteOutput, inner_sum,
    inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2),
    probeGram, Matrix.gram_apply, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem probeProjectionResidual_inner_column (N : ℕ) (f : CausalProbeL2) (i : Fin N) :
    inner ℂ (probeColumn (i.val + 1))
      (f - probeFiniteOutput (probeProjectionCoefficients N f)) = 0 := by
  rw [inner_sub_right, probeColumn_inner_output]
  have hn := congrFun (probeProjectionCoefficients_normal N f) i
  change (probePairings N f) i - _ = 0
  rw [hn, sub_self]

theorem probeProjectionResidual_inner_space (N : ℕ) (f : CausalProbeL2)
    {g : CausalProbeL2} (hg : g ∈ probeFiniteSpace N) :
    inner ℂ (f - probeFiniteOutput (probeProjectionCoefficients N f)) g = 0 := by
  rcases hg with ⟨x, rfl⟩
  change inner ℂ (f - probeFiniteOutput (probeProjectionCoefficients N f))
    (∑ i : Fin N, x i • probeColumn (i.val + 1)) = 0
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2)]
  have hz : inner ℂ (f - probeFiniteOutput (probeProjectionCoefficients N f))
      (probeColumn (i.val + 1)) = 0 := by
    rw [← inner_conj_symm, probeProjectionResidual_inner_column, map_zero]
  rw [hz, mul_zero]

theorem probeProjection_eq_starProjection (N : ℕ) (f : CausalProbeL2) :
    (probeFiniteSpace N).starProjection f =
      probeFiniteOutput (probeProjectionCoefficients N f) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact ⟨probeProjectionCoefficients N f, rfl⟩
  · intro g hg
    exact probeProjectionResidual_inner_space N f hg

theorem probeBestOutput_eq_coefficients (N : ℕ) :
    probeBestOutput N = probeFiniteOutput (probeProjectionCoefficients N probeTarget) :=
  probeProjection_eq_starProjection N probeTarget

theorem probeBestResidual_inner_space (N : ℕ) {g : CausalProbeL2}
    (hg : g ∈ probeFiniteSpace N) : inner ℂ (probeTarget - probeBestOutput N) g = 0 := by
  rw [probeBestOutput_eq_coefficients]
  exact probeProjectionResidual_inner_space N probeTarget hg

theorem probe_residual_pythagoras {N : ℕ} (x : Fin N → ℂ) :
    ‖probeResidual x‖ ^ 2 = probeError N ^ 2 + ‖probeBestOutput N - probeFiniteOutput x‖ ^ 2 := by
  have hg : probeBestOutput N - probeFiniteOutput x ∈ probeFiniteSpace N :=
    (probeFiniteSpace N).sub_mem (probeBestOutput_mem N) ⟨x, rfl⟩
  have hp := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (probeTarget - probeBestOutput N) (probeBestOutput N - probeFiniteOutput x)
    (probeBestResidual_inner_space N hg)
  have he : (probeTarget - probeBestOutput N) +
      (probeBestOutput N - probeFiniteOutput x) = probeResidual x := by
    dsimp only [probeResidual]
    abel
  simpa only [he, ← pow_two, probeError] using hp

theorem probeError_le_residual {N : ℕ} (x : Fin N → ℂ) :
    probeError N ≤ ‖probeResidual x‖ := by
  have hp := probe_residual_pythagoras x
  nlinarith [sq_nonneg ‖probeBestOutput N - probeFiniteOutput x‖,
    probeError_nonneg N, norm_nonneg (probeResidual x)]

theorem probeTarget_inner_output {N : ℕ} (x : Fin N → ℂ) :
    inner ℂ probeTarget (probeFiniteOutput x) = star (probeTargetColumn N) ⬝ᵥ x := by
  simp only [probeFiniteOutput, inner_sum,
    inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2), dotProduct,
    Pi.star_apply, probeTargetColumn]
  apply Finset.sum_congr rfl
  intro i _
  rw [← inner_conj_symm]
  simp only [RCLike.star_def]
  ring

theorem probeError_sq_schur (N : ℕ) :
    ((probeError N ^ 2 : ℝ) : ℂ) = (probeQ0 : ℂ) -
      star (probeTargetColumn N) ⬝ᵥ ((probeGram N)⁻¹ *ᵥ probeTargetColumn N) := by
  have hi : inner ℂ (probeBestOutput N) probeTarget =
      inner ℂ (probeBestOutput N) (probeBestOutput N) := by
    have hz := probeBestResidual_inner_space N (probeBestOutput_mem N)
    have hz' := congrArg conj hz
    simp only [map_zero, inner_sub_left, map_sub, inner_conj_symm] at hz'
    exact sub_eq_zero.mp hz'
  have he : inner ℂ (probeTarget - probeBestOutput N)
      (probeTarget - probeBestOutput N) = inner ℂ probeTarget probeTarget -
        inner ℂ probeTarget (probeBestOutput N) := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right, hi]
    ring
  have hnorm : inner ℂ (probeTarget - probeBestOutput N)
      (probeTarget - probeBestOutput N) = ((probeError N ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    simp only [probeError, Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal]
  rw [← hnorm, he, inner_self_eq_norm_sq_to_K, probeBestOutput_eq_coefficients,
    probeTarget_inner_output]
  simp only [probeQ0, Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal, probeProjectionCoefficients,
    probePairings, probeTargetColumn] <;> rfl

def probePairingColumnMatrix (N : ℕ) : Matrix (Fin N) Unit ℂ :=
  Matrix.of fun i (_ : Unit) => probeTargetColumn N i

def probePairingRowMatrix (N : ℕ) : Matrix Unit (Fin N) ℂ :=
  Matrix.of fun (_ : Unit) i => star (probeTargetColumn N i)

def probeBorderedGram (N : ℕ) : Matrix (Fin N ⊕ Unit) (Fin N ⊕ Unit) ℂ :=
  Matrix.fromBlocks (probeGram N) (probePairingColumnMatrix N)
    (probePairingRowMatrix N)
    (Matrix.of fun (_ : Unit) (_ : Unit) => (probeQ0 : ℂ))

theorem probeBorderedGram_eq_gram (N : ℕ) : probeBorderedGram N =
    Matrix.gram ℂ (Sum.elim (fun i : Fin N => probeColumn (i.val + 1))
      (fun _ : Unit => probeTarget)) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · rfl
  · rfl
  · simp only [probeBorderedGram, Matrix.fromBlocks_apply₂₁, probePairingRowMatrix,
      Pi.star_apply, probeTargetColumn, Matrix.gram_apply, Sum.elim_inl, Sum.elim_inr]
    exact inner_conj_symm _ _
  · simp only [probeBorderedGram, Matrix.fromBlocks_apply₂₂, Matrix.of_apply,
      Matrix.gram_apply, Sum.elim_inr, probeQ0, inner_self_eq_norm_sq_to_K,
      Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal]

theorem probeBorderedGram_det (N : ℕ) :
    (probeBorderedGram N).det = (probeGram N).det *
      ((probeQ0 : ℂ) - star (probeTargetColumn N) ⬝ᵥ
        ((probeGram N)⁻¹ *ᵥ probeTargetColumn N)) := by
  letI : Invertible (probeGram N) := Matrix.invertibleOfIsUnitDet _
    (isUnit_iff_ne_zero.2 (probeGram_det_ne_zero N))
  have hcol : (probeGram N)⁻¹ * probePairingColumnMatrix N =
      Matrix.of (fun i (_ : Unit) => ((probeGram N)⁻¹ *ᵥ probeTargetColumn N) i) := by
    ext i j
    rfl
  have hrow : probePairingRowMatrix N *
      Matrix.of (fun i (_ : Unit) => ((probeGram N)⁻¹ *ᵥ probeTargetColumn N) i) =
      Matrix.of (fun (_ : Unit) (_ : Unit) =>
        star (probeTargetColumn N) ⬝ᵥ ((probeGram N)⁻¹ *ᵥ probeTargetColumn N)) := by
    ext i j
    rfl
  rw [probeBorderedGram, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv,
    Matrix.mul_assoc, hcol, hrow, Matrix.det_unique (n := Unit)]
  rfl

theorem probeError_sq_determinant_ratio (N : ℕ) :
    ((probeError N ^ 2 : ℝ) : ℂ) = (probeBorderedGram N).det / (probeGram N).det := by
  rw [probeBorderedGram_det, ← probeError_sq_schur]
  field_simp [probeGram_det_ne_zero N]

theorem probe_schur_error (N : ℕ) :
    (((probeError N ^ 2 : ℝ) : ℂ) = (probeQ0 : ℂ) -
      star (probeTargetColumn N) ⬝ᵥ ((probeGram N)⁻¹ *ᵥ probeTargetColumn N)) ∧
    (((probeError N ^ 2 : ℝ) : ℂ) = (probeBorderedGram N).det / (probeGram N).det) ∧
    (probeBestOutput N = probeFiniteOutput (probeProjectionCoefficients N probeTarget)) ∧
    (∀ x : Fin N → ℂ, probeError N ≤ ‖probeResidual x‖) :=
  ⟨probeError_sq_schur N, probeError_sq_determinant_ratio N,
    probeBestOutput_eq_coefficients N, probeError_le_residual⟩

theorem probeFiniteSpace_eq_span (N : ℕ) :
    probeFiniteSpace N = Submodule.span ℂ
      (Set.range (fun i : Fin N => probeColumn (i.val + 1))) :=
  Fintype.range_linearCombination ℂ _

theorem probeFiniteSpace_mono {N M : ℕ} (hNM : N ≤ M) :
    probeFiniteSpace N ≤ probeFiniteSpace M := by
  rw [probeFiniteSpace_eq_span, probeFiniteSpace_eq_span]
  apply Submodule.span_mono
  rintro g ⟨i, rfl⟩
  exact ⟨⟨i.val, lt_of_lt_of_le i.isLt hNM⟩, rfl⟩

theorem probeError_antitone : Antitone probeError := by
  intro N M hNM
  have hm := probeFiniteSpace_mono hNM (probeBestOutput_mem N)
  rcases hm with ⟨x, hx⟩
  have h := probeError_le_residual x
  change probeFiniteOutput x = probeBestOutput N at hx
  change probeError M ≤ ‖probeTarget - probeFiniteOutput x‖ at h
  simpa only [hx, probeError] using h

theorem probeError_sq_eq_real_schur (N : ℕ) : probeError N ^ 2 = probeQ0 -
    (star (probeTargetColumn N) ⬝ᵥ ((probeGram N)⁻¹ *ᵥ probeTargetColumn N)).re := by
  have h := congrArg Complex.re (probeError_sq_schur N)
  simpa only [Complex.ofReal_re, Complex.sub_re] using h

theorem rh_of_probe_schur_limit
    (h : Filter.Tendsto (fun N => probeQ0 -
      (star (probeTargetColumn N) ⬝ᵥ ((probeGram N)⁻¹ *ᵥ probeTargetColumn N)).re)
      Filter.atTop (𝓝 0)) : RiemannHypothesis := by
  apply rh_of_probe_error_limit
  have hsq : Filter.Tendsto (fun N => probeError N ^ 2) Filter.atTop (𝓝 0) := by
    simpa only [probeError_sq_eq_real_schur] using h
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq (probeError_nonneg _), Real.sqrt_zero] using hs

theorem probe_source_width_lt_log_two : 2 * probeSigma < Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (by norm_num : 0 < (2 : ℝ))
  rw [probeSigma_eq]
  norm_num at h ⊢
  linarith

theorem probeW_conj (t : ℝ) : conj (probeW t) = probeW t := by
  rw [probeW_eq_real_integral]
  exact Complex.conj_ofReal _

/-- The inclusive native integer history has only its first column before log 2. -/
theorem probeW_eq_probeV_first_cell {t : ℝ} (ht : t < Real.log 2) :
    probeW t = probeV t := by
  by_cases hneg : t < 0
  · rw [probeW_zero_of_neg hneg, probeV_zero_of_neg hneg]
  have ht0 : 0 ≤ t := le_of_not_gt hneg
  have he1 : 1 ≤ Real.exp t := by simpa using Real.exp_le_exp.mpr ht0
  have he2 : Real.exp t < 2 := by
    exact (Real.exp_lt_exp.mpr ht).trans_eq (Real.exp_log (by norm_num))
  have hfloor : ⌊Real.exp t⌋₊ = 1 := by
    apply (Nat.floor_eq_iff (Real.exp_pos t).le).2
    simp only [Nat.cast_one, one_add_one_eq_two]
    exact ⟨he1, he2⟩
  rw [native_probe_integer_action, hfloor]
  norm_num [Finset.sum_range_succ, CCM.nativeIntegerCoefficient]

theorem probeV_damped_integrable (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * probeV t) := by
  apply (CCM.nativeCausalLaplaceMoment_integrable z hz 0 probeTarget).congr
  filter_upwards [probeTarget_coeFn] with t ht
  simp only [pow_zero, one_mul, ht]

theorem probeW_damped_integrable (z : ℂ) (hz : 0 < z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * probeW t) := by
  apply (CCM.nativeCausalLaplaceMoment_integrable z hz 0 probeCompletedSource).congr
  filter_upwards [probeCompletedSource_coeFn] with t ht
  simp only [pow_zero, one_mul, ht]

theorem probeV_square_integrable : Integrable (fun t : ℝ => conj (probeV t) * probeV t) := by
  apply (L2.integrable_inner (𝕜 := ℂ) (probeTarget : ProbeL2) (probeTarget : ProbeL2)).congr
  filter_upwards [probeTarget_coeFn] with t ht
  rw [ht, RCLike.inner_apply']

theorem probeV_square_integral : (∫ t : ℝ, conj (probeV t) * probeV t) = (probeQ0 : ℂ) := by
  calc
    _ = inner ℂ (probeTarget : ProbeL2) (probeTarget : ProbeL2) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [probeTarget_coeFn] with t ht
      rw [ht, RCLike.inner_apply']
    _ = _ := by
      rw [inner_self_eq_norm_sq_to_K]
      simp only [probeQ0, Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal] <;> rfl

def probeMixedPairing (n : ℕ) : ℂ := inner ℂ (probeColumn n) probeTarget

theorem probeTargetColumn_eq_mixed (N : ℕ) (i : Fin N) :
    probeTargetColumn N i = probeMixedPairing (i.val + 1) := rfl

theorem probeMixedPairing_integral {n : ℕ} (hn : n ≠ 0) :
    probeMixedPairing n = (CCM.nativeIntegerCoefficient n : ℂ) *
      ∫ t : ℝ, probeW t * probeV (t + Real.log n) := by
  change inner ℂ (probeColumn n : ProbeL2) (probeTarget : ProbeL2) = _
  rw [L2.inner_def]
  calc
    _ = ∫ t : ℝ, (CCM.nativeIntegerCoefficient n : ℂ) *
        (probeW (t - Real.log n) * probeV t) := by
      apply integral_congr_ae
      filter_upwards [probeColumn_coeFn hn, probeTarget_coeFn] with t hc hv
      rw [hc, hv, RCLike.inner_apply']
      simp only [map_mul, Complex.conj_ofReal, probeW_conj]
      ring
    _ = (CCM.nativeIntegerCoefficient n : ℂ) *
        ∫ t : ℝ, probeW (t - Real.log n) * probeV t := integral_const_mul _ _
    _ = _ := by
      congr 1
      have h := integral_sub_right_eq_self
        (fun t : ℝ => probeW t * probeV (t + Real.log n)) (Real.log n)
        (μ := (volume : Measure ℝ))
      simpa only [sub_add_cancel] using h

theorem probeR_three_half : CCM.nativeCompletionRationalMultiplier (3 / 2 : ℂ) = 1 / 6 := by
  norm_num [CCM.nativeCompletionRationalMultiplier]

/-- The first mixed pairing reduces to two genuine damped integrals: the native
first-cell identity removes the compact head before the exact target tail is used. -/
theorem probeMixedPairing_one : probeMixedPairing 1 = (probeQ0 : ℂ) +
    probeCorrelationConstant * (riemannZeta (2 : ℂ) - 1) := by
  have hpair : probeMixedPairing 1 = ∫ t : ℝ, conj (probeW t) * probeV t := by
    simpa only [CCM.nativeIntegerCoefficient, Nat.cast_one, Real.sqrt_one, div_one,
      Complex.ofReal_one, one_mul, Real.log_one, add_zero, probeW_conj]
      using (probeMixedPairing_integral (n := 1) (by omega))
  have hp (t : ℝ) : conj (probeW t) * probeV t = conj (probeV t) * probeV t +
      (2 * JPlus (-3 / 2 : ℂ)) *
        (Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) * (probeW t - probeV t)) := by
    rw [probeW_conj, probeV_conj]
    by_cases ht : t < 2 * probeSigma
    · rw [probeW_eq_probeV_first_cell (ht.trans probe_source_width_lt_log_two)]
      ring
    · rw [probeV_tail (le_of_not_gt ht)]
      ring
  have hW := probeW_damped_integrable (3 / 2 : ℂ) (by norm_num)
  have hV := probeV_damped_integrable (3 / 2 : ℂ) (by norm_num)
  have hdiff : Integrable (fun t : ℝ =>
      Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) * (probeW t - probeV t)) := by
    apply (hW.sub hV).congr
    filter_upwards with t
    change Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) * probeW t -
      Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) * probeV t =
        Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) * (probeW t - probeV t)
    ring
  have hInt : (∫ t : ℝ, Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) *
      (probeW t - probeV t)) = probeLaplace probeW (3 / 2 : ℂ) -
        probeLaplace probeV (3 / 2 : ℂ) := by
    simp_rw [mul_sub]
    exact integral_sub hW hV
  rw [hpair, integral_congr_ae (Filter.Eventually.of_forall hp),
    integral_add probeV_square_integrable (hdiff.const_mul _), integral_const_mul,
    probeV_square_integral, hInt, probeW_laplace (by norm_num) (by norm_num),
    probeV_laplace (by norm_num), probeR_three_half]
  norm_num only [show (3 / 2 : ℂ) + 1 / 2 = 2 by norm_num]
  calc
    _ = (probeQ0 : ℂ) + (JPlus (-(3 / 2 : ℂ)) * JPlus (3 / 2 : ℂ) / 3) *
        (riemannZeta (2 : ℂ) - 1) := by ring
    _ = _ := by rw [JPlus_opposite_product]; rfl

theorem probe_integer_weight_tail {n : ℕ} (hn : n ≠ 0) :
    (CCM.nativeIntegerCoefficient n : ℂ) *
      Complex.exp (-(3 / 2 : ℂ) * (Real.log n : ℂ)) = 1 / (n : ℂ) ^ 2 := by
  have hnR : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hhalf : CCM.nativeIntegerCoefficient n = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    unfold CCM.nativeIntegerCoefficient
    rw [Real.sqrt_eq_rpow, one_div, Real.rpow_neg hnR.le]
  have he : Real.exp (-(3 / 2 : ℝ) * Real.log n) = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [Real.rpow_def_of_pos hnR]
    congr 1
    ring
  have hw : CCM.nativeIntegerCoefficient n * Real.exp (-(3 / 2 : ℝ) * Real.log n) =
      1 / (n : ℝ) ^ 2 := by
    rw [hhalf, he, ← Real.rpow_add hnR]
    norm_num [Real.rpow_neg hnR.le]
  have hc : Complex.exp (-(3 / 2 : ℂ) * (Real.log n : ℂ)) =
      (Real.exp (-(3 / 2 : ℝ) * Real.log n) : ℂ) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [hc, ← Complex.ofReal_mul, hw]
  push_cast <;> rfl

theorem probeMixedPairing_ge_two {n : ℕ} (hn : 2 ≤ n) :
    probeMixedPairing n = probeCorrelationConstant * riemannZeta (2 : ℂ) / (n : ℂ) ^ 2 := by
  have hn0 : n ≠ 0 := by omega
  have hlog : 2 * probeSigma ≤ Real.log n := by
    exact probe_source_width_lt_log_two.le.trans
      (Real.log_le_log (by norm_num : 0 < (2 : ℝ)) (by exact_mod_cast hn))
  have hp (t : ℝ) : probeW t * probeV (t + Real.log n) =
      (2 * JPlus (-3 / 2 : ℂ) * Complex.exp (-(3 / 2 : ℂ) * (Real.log n : ℂ))) *
        (Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) * probeW t) := by
    by_cases ht : t < 0
    · rw [probeW_zero_of_neg ht]
      ring
    · rw [probeV_tail (t := t + Real.log n) (by linarith [le_of_not_gt ht])]
      have he : Complex.exp (-(3 / 2 : ℂ) * ((t + Real.log n : ℝ) : ℂ)) =
          Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) *
            Complex.exp (-(3 / 2 : ℂ) * (Real.log n : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      rw [he]
      ring
  rw [probeMixedPairing_integral hn0,
    integral_congr_ae (Filter.Eventually.of_forall hp), integral_const_mul]
  change (CCM.nativeIntegerCoefficient n : ℂ) *
    ((2 * JPlus (-3 / 2 : ℂ) * Complex.exp (-(3 / 2 : ℂ) * (Real.log n : ℂ))) *
      probeLaplace probeW (3 / 2 : ℂ)) = _
  rw [probeW_laplace (by norm_num) (by norm_num), probeR_three_half]
  norm_num only [show (3 / 2 : ℂ) + 1 / 2 = 2 by norm_num]
  calc
    _ = ((CCM.nativeIntegerCoefficient n : ℂ) *
        Complex.exp (-(3 / 2 : ℂ) * (Real.log n : ℂ))) *
        ((JPlus (-(3 / 2 : ℂ)) * JPlus (3 / 2 : ℂ) / 3) * riemannZeta (2 : ℂ)) := by ring
    _ = _ := by
      rw [probe_integer_weight_tail hn0, JPlus_opposite_product]
      dsimp only [probeCorrelationConstant]
      ring

theorem probeOriginalDensity_zero_outside {t : ℝ} (ht : t ∉ Icc (-probeSigma) probeSigma) :
    CCM.universalSincSource probeSigma t = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  exact fun h => ht (CCM.universalSincSource_support probeSigma_pos h)

theorem probeOriginalDensity_hasCompactSupport :
    HasCompactSupport (CCM.universalSincSource probeSigma) := by
  apply HasCompactSupport.intro (K := Icc (-probeSigma) probeSigma) isCompact_Icc
  exact fun _ ht => probeOriginalDensity_zero_outside ht

theorem probeOriginalDensity_integrable : Integrable (CCM.universalSincSource probeSigma) :=
  (CCM.universalSincSource_contDiff probeSigma_pos).continuous.integrable_of_hasCompactSupport
    probeOriginalDensity_hasCompactSupport

theorem probeProbabilityExp_integrable (r : ℝ) :
    Integrable (fun t : ℝ => Real.exp (r * t) * CCM.universalSincSource probeSigma t) :=
  ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
    (CCM.universalSincSource_contDiff probeSigma_pos).continuous).integrable_of_hasCompactSupport
      probeOriginalDensity_hasCompactSupport.mul_left

def probeSymmetricQ (r : ℝ) : ℝ :=
  ∫ t : ℝ, Real.cosh (r * t) * CCM.universalSincSource probeSigma t

theorem probeProbabilityCosh_integrable (r : ℝ) :
    Integrable (fun t : ℝ => Real.cosh (r * t) * CCM.universalSincSource probeSigma t) :=
  ((Real.continuous_cosh.comp (continuous_const.mul continuous_id)).mul
    (CCM.universalSincSource_contDiff probeSigma_pos).continuous).integrable_of_hasCompactSupport
      probeOriginalDensity_hasCompactSupport.mul_left

theorem probeSymmetricQ_eq_exp (r : ℝ) : probeSymmetricQ r =
    ∫ t : ℝ, Real.exp (-r * t) * CCM.universalSincSource probeSigma t := by
  have heq : (∫ t : ℝ, Real.exp (r * t) * CCM.universalSincSource probeSigma t) =
      ∫ t : ℝ, Real.exp (-r * t) * CCM.universalSincSource probeSigma t := by
    calc
      _ = ∫ t : ℝ, (fun u : ℝ => Real.exp (-r * u) *
          CCM.universalSincSource probeSigma u) (-t) := by
        apply integral_congr_ae
        filter_upwards with t
        rw [CCM.universalSincSource_even probeSigma_pos t]
        congr 2
        ring
      _ = _ := integral_neg_eq_self
        (fun t : ℝ => Real.exp (-r * t) * CCM.universalSincSource probeSigma t)
        (volume : Measure ℝ)
  have hp (t : ℝ) : Real.cosh (r * t) * CCM.universalSincSource probeSigma t =
      (Real.exp (r * t) * CCM.universalSincSource probeSigma t +
        Real.exp (-r * t) * CCM.universalSincSource probeSigma t) / 2 := by
    simp only [Real.cosh_eq, neg_mul]
    ring
  rw [probeSymmetricQ, integral_congr_ae (Filter.Eventually.of_forall hp), integral_div,
    integral_add (probeProbabilityExp_integrable r) (probeProbabilityExp_integrable (-r)), heq]
  ring

theorem probeSymmetricQ_bounds {r : ℝ} (hr : 0 ≤ r) :
    1 ≤ probeSymmetricQ r ∧ probeSymmetricQ r ≤ Real.cosh (r * probeSigma) := by
  have hlo (t : ℝ) : CCM.universalSincSource probeSigma t ≤
      Real.cosh (r * t) * CCM.universalSincSource probeSigma t := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (Real.one_le_cosh (r * t))
      (CCM.universalSincSource_nonneg probeSigma_pos t)
  have hhi (t : ℝ) : Real.cosh (r * t) * CCM.universalSincSource probeSigma t ≤
      Real.cosh (r * probeSigma) * CCM.universalSincSource probeSigma t := by
    by_cases ht : t ∈ Icc (-probeSigma) probeSigma
    · apply mul_le_mul_of_nonneg_right _ (CCM.universalSincSource_nonneg probeSigma_pos t)
      apply Real.cosh_le_cosh.2
      rw [abs_mul, abs_of_nonneg hr, abs_of_nonneg (mul_nonneg hr probeSigma_pos.le)]
      exact mul_le_mul_of_nonneg_left (abs_le.2 ht) hr
    · rw [probeOriginalDensity_zero_outside ht, mul_zero, mul_zero]
  have hl := integral_mono probeOriginalDensity_integrable (probeProbabilityCosh_integrable r) hlo
  have hh := integral_mono (probeProbabilityCosh_integrable r)
    (probeOriginalDensity_integrable.const_mul (Real.cosh (r * probeSigma))) hhi
  rw [CCM.universalSincSource_integral_one probeSigma_pos] at hl
  rw [integral_const_mul, CCM.universalSincSource_integral_one probeSigma_pos, mul_one] at hh
  exact ⟨hl, hh⟩

theorem probeProduct_imaginary (r : ℝ) :
    CCM.UniversalSinc.product probeSigma (Complex.I * (r : ℂ)) = (probeSymmetricQ r : ℂ) := by
  have hf := congrFun (CCM.paperFT_universalSincSource probeSigma_pos) (Complex.I * (r : ℂ))
  calc
    _ = Zeta23.paperFT (fun t : ℝ => (CCM.universalSincSource probeSigma t : ℂ))
        (Complex.I * (r : ℂ)) := hf.symm
    _ = ∫ t : ℝ, ((Real.exp (-r * t) * CCM.universalSincSource probeSigma t : ℝ) : ℂ) := by
      unfold Zeta23.paperFT
      apply integral_congr_ae
      filter_upwards with t
      rw [Complex.ofReal_mul, Complex.ofReal_exp]
      have he : Complex.I * (Complex.I * (r : ℂ)) * (t : ℂ) = ((-r * t : ℝ) : ℂ) := by
        calc
          _ = (Complex.I * Complex.I) * ((r : ℂ) * (t : ℂ)) := by ring
          _ = _ := by rw [Complex.I_mul_I]; push_cast; ring
      rw [he]
      ring
    _ = ((∫ t : ℝ, Real.exp (-r * t) * CCM.universalSincSource probeSigma t : ℝ) : ℂ) :=
      _root_.integral_complex_ofReal
    _ = _ := by rw [probeSymmetricQ_eq_exp]

def probeCorrelationC : ℝ := (16 / 3) * probeSymmetricQ (3 / 2) ^ 2

theorem probeCorrelationConstant_eq_real : probeCorrelationConstant = (probeCorrelationC : ℂ) := by
  have hQ : CCM.UniversalSinc.product probeSigma (Complex.I * (3 / 2 : ℂ)) =
      (probeSymmetricQ (3 / 2) : ℂ) := by
    simpa only [Complex.ofReal_div, Complex.ofReal_ofNat] using probeProduct_imaginary (3 / 2)
  have hJ : CCM.nativeOriginalSourceLaplace (3 / 2 : ℂ) = 4 * (probeSymmetricQ (3 / 2) : ℂ) := by
    rw [ExceptionalZero.nativeOriginalSourceLaplace_formula]
    change ((Complex.I * (3 / 2 : ℂ)) ^ 2 + 1 / 4) ^ 2 *
      CCM.UniversalSinc.product probeSigma (Complex.I * (3 / 2 : ℂ)) = _
    rw [hQ]
    norm_num [mul_pow, Complex.I_sq]
  rw [probeCorrelationConstant, hJ, probeCorrelationC]
  push_cast
  ring

theorem probeCorrelationC_bounds : (16 / 3 : ℝ) ≤ probeCorrelationC ∧
    probeCorrelationC ≤ (16 / 3 : ℝ) * Real.cosh (3 * probeSigma / 2) ^ 2 := by
  rcases probeSymmetricQ_bounds (by norm_num : 0 ≤ (3 / 2 : ℝ)) with ⟨hl, hh⟩
  have he : (3 / 2 : ℝ) * probeSigma = 3 * probeSigma / 2 := by ring
  rw [he] at hh
  have hsq := pow_le_pow_left₀ (le_trans (by norm_num : (0 : ℝ) ≤ 1) hl) hh 2
  have hloSq := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hl 2
  unfold probeCorrelationC
  constructor <;> nlinarith

theorem probe_cosh_rational_upper : Real.cosh (3 * probeSigma / 2) ≤
    (134217728 / 134217719 : ℝ) := by
  let x : ℝ := 3 * probeSigma / 2
  have hy : 0 < 1 - x ^ 2 / 2 := by dsimp only [x]; rw [probeSigma_eq]; norm_num
  have hlog : x ^ 2 / 2 ≤ Real.log ((1 - x ^ 2 / 2)⁻¹) := by
    rw [Real.log_inv]
    have h := Real.log_le_sub_one_of_pos hy
    linarith
  have he : Real.exp (x ^ 2 / 2) ≤ (1 - x ^ 2 / 2)⁻¹ :=
    (Real.exp_le_exp.mpr hlog).trans_eq (Real.exp_log (inv_pos.2 hy))
  calc
    _ ≤ (1 - x ^ 2 / 2)⁻¹ := (Real.cosh_le_exp_half_sq x).trans he
    _ = _ := by dsimp only [x]; rw [probeSigma_eq]; norm_num

theorem probeCorrelationC_rational_upper : probeCorrelationC ≤
    (16 / 3 : ℝ) * (134217728 / 134217719 : ℝ) ^ 2 := by
  have h := pow_le_pow_left₀ (le_trans (by norm_num : (0 : ℝ) ≤ 1)
    (Real.one_le_cosh (3 * probeSigma / 2))) probe_cosh_rational_upper 2
  exact probeCorrelationC_bounds.2.trans (mul_le_mul_of_nonneg_left h (by norm_num))

theorem probe_target_column :
    (probeMixedPairing 1 = (probeQ0 : ℂ) +
      probeCorrelationConstant * (riemannZeta (2 : ℂ) - 1)) ∧
    (∀ n : ℕ, 2 ≤ n → probeMixedPairing n =
      probeCorrelationConstant * riemannZeta (2 : ℂ) / (n : ℂ) ^ 2) ∧
    probeCorrelationConstant = (probeCorrelationC : ℂ) ∧
    (16 / 3 : ℝ) ≤ probeCorrelationC ∧
    probeCorrelationC ≤ (16 / 3 : ℝ) * Real.cosh (3 * probeSigma / 2) ^ 2 ∧
    probeCorrelationC ≤ (16 / 3 : ℝ) * (134217728 / 134217719 : ℝ) ^ 2 :=
  ⟨probeMixedPairing_one, fun _ hn => probeMixedPairing_ge_two hn,
    probeCorrelationConstant_eq_real, probeCorrelationC_bounds.1, probeCorrelationC_bounds.2,
    probeCorrelationC_rational_upper⟩

def probeInnovation (N : ℕ) : CausalProbeL2 := probeColumn (N + 1) -
  (probeFiniteSpace N).starProjection (probeColumn (N + 1))

def probeInnovationNormSq (N : ℕ) : ℝ := ‖probeInnovation N‖ ^ 2

def probeInnovationPairing (N : ℕ) : ℂ := inner ℂ (probeInnovation N) probeTarget

def probeInnovationCoefficient (N : ℕ) : ℂ :=
  probeInnovationPairing N / (probeInnovationNormSq N : ℂ)

theorem probeColumn_not_mem_previous (N : ℕ) :
    probeColumn (N + 1) ∉ probeFiniteSpace N := by
  classical
  rintro ⟨x, hx⟩
  change probeFiniteOutput x = probeColumn (N + 1) at hx
  let y : Fin (N + 1) → ℂ := Fin.snoc x (-1)
  have hy : (∑ i : Fin (N + 1), y i • probeColumn (i.val + 1)) = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [y, Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last,
      neg_smul, one_smul]
    change probeFiniteOutput x + -probeColumn (N + 1) = 0
    rw [hx, add_neg_cancel]
  have hz := Fintype.linearIndependent_iff.1 (probeColumns_linearIndependent (N + 1)) y hy
    (Fin.last N)
  norm_num [y] at hz

theorem probeInnovation_ne_zero (N : ℕ) : probeInnovation N ≠ 0 := by
  intro h
  have he := sub_eq_zero.mp h
  apply probeColumn_not_mem_previous N
  rw [he]
  exact (probeFiniteSpace N).starProjection_apply_mem _

theorem probeInnovationNormSq_pos (N : ℕ) : 0 < probeInnovationNormSq N :=
  sq_pos_of_pos (norm_pos_iff.2 (probeInnovation_ne_zero N))

theorem probeInnovation_inner_previous (N : ℕ) {g : CausalProbeL2}
    (hg : g ∈ probeFiniteSpace N) : inner ℂ (probeInnovation N) g = 0 :=
  (probeFiniteSpace N).starProjection_inner_eq_zero (probeColumn (N + 1)) g hg

theorem probeInnovation_mem_next (N : ℕ) : probeInnovation N ∈ probeFiniteSpace (N + 1) := by
  apply (probeFiniteSpace (N + 1)).sub_mem
  · rw [probeFiniteSpace_eq_span]
    exact Submodule.subset_span ⟨Fin.last N, rfl⟩
  · exact probeFiniteSpace_mono (Nat.le_succ N)
      ((probeFiniteSpace N).starProjection_apply_mem _)

theorem probeInnovation_inner_self (N : ℕ) :
    inner ℂ (probeInnovation N) (probeInnovation N) = (probeInnovationNormSq N : ℂ) := by
  rw [inner_self_eq_norm_sq_to_K]
  simp only [probeInnovationNormSq, Complex.ofReal_pow, RCLike.ofReal_eq_complex_ofReal]

theorem probeBestOutput_innovation (N : ℕ) : probeBestOutput (N + 1) =
    probeBestOutput N + probeInnovationCoefficient N • probeInnovation N := by
  classical
  let p : CausalProbeL2 := probeBestOutput N +
    probeInnovationCoefficient N • probeInnovation N
  have hδ : (probeInnovationNormSq N : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (ne_of_gt (probeInnovationNormSq_pos N))
  have hp : p ∈ probeFiniteSpace (N + 1) := (probeFiniteSpace (N + 1)).add_mem
    (probeFiniteSpace_mono (Nat.le_succ N) (probeBestOutput_mem N))
    ((probeFiniteSpace (N + 1)).smul_mem _ (probeInnovation_mem_next N))
  have hOld (g : CausalProbeL2) (hg : g ∈ probeFiniteSpace N) :
      inner ℂ (probeTarget - p) g = 0 := by
    have he : probeTarget - p = (probeTarget - probeBestOutput N) -
        probeInnovationCoefficient N • probeInnovation N := by dsimp only [p]; abel
    rw [he, inner_sub_left, inner_smul_left (𝕜 := ℂ) (E := CausalProbeL2),
      probeBestResidual_inner_space N hg, probeInnovation_inner_previous N hg,
      mul_zero, sub_zero]
  have hU : inner ℂ (probeInnovation N) (probeTarget - p) = 0 := by
    dsimp only [p]
    rw [inner_sub_right, inner_add_right,
      inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2),
      probeInnovation_inner_previous N (probeBestOutput_mem N),
      probeInnovation_inner_self, zero_add]
    change probeInnovationPairing N -
      probeInnovationCoefficient N * (probeInnovationNormSq N : ℂ) = 0
    rw [probeInnovationCoefficient, div_mul_cancel₀ _ hδ, sub_self]
  have hCols (i : Fin (N + 1)) : inner ℂ (probeTarget - p) (probeColumn (i.val + 1)) = 0 := by
    by_cases hi : i.val < N
    · apply hOld
      rw [probeFiniteSpace_eq_span]
      exact Submodule.subset_span ⟨⟨i.val, hi⟩, rfl⟩
    · have hiN : i.val = N := by omega
      rw [hiN]
      have he : probeColumn (N + 1) =
          (probeFiniteSpace N).starProjection (probeColumn (N + 1)) + probeInnovation N := by
        dsimp only [probeInnovation]
        abel
      rw [he, inner_add_right,
        hOld _ ((probeFiniteSpace N).starProjection_apply_mem _),
        inner_eq_zero_symm.1 hU, zero_add]
  have hAll (g : CausalProbeL2) (hg : g ∈ probeFiniteSpace (N + 1)) :
      inner ℂ (probeTarget - p) g = 0 := by
    rcases hg with ⟨x, rfl⟩
    change inner ℂ (probeTarget - p) (∑ i : Fin (N + 1), x i • probeColumn (i.val + 1)) = 0
    rw [inner_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [inner_smul_right (𝕜 := ℂ) (E := CausalProbeL2), hCols, mul_zero]
  exact Submodule.eq_starProjection_of_mem_of_inner_eq_zero hp hAll

theorem probeError_sq_nested {N M : ℕ} (hNM : N ≤ M) :
    probeError N ^ 2 = probeError M ^ 2 + ‖probeBestOutput M - probeBestOutput N‖ ^ 2 := by
  rcases probeFiniteSpace_mono hNM (probeBestOutput_mem N) with ⟨x, hx⟩
  change probeFiniteOutput x = probeBestOutput N at hx
  have hp := probe_residual_pythagoras x
  simpa only [probeResidual, hx, probeError] using hp

theorem probeInnovation_update_norm (N : ℕ) :
    ‖probeInnovationCoefficient N • probeInnovation N‖ ^ 2 =
      ‖probeInnovationPairing N‖ ^ 2 / probeInnovationNormSq N := by
  have hδ := probeInnovationNormSq_pos N
  rw [norm_smul, probeInnovationCoefficient, norm_div, Complex.norm_real,
    Real.norm_of_nonneg hδ.le, mul_pow, div_pow]
  change (‖probeInnovationPairing N‖ ^ 2 / probeInnovationNormSq N ^ 2) *
    probeInnovationNormSq N = _
  field_simp [ne_of_gt hδ] <;> ring

theorem probe_innovation_decrement (N : ℕ) : probeError N ^ 2 - probeError (N + 1) ^ 2 =
    ‖probeInnovationPairing N‖ ^ 2 / probeInnovationNormSq N := by
  have h := probeError_sq_nested (Nat.le_succ N)
  rw [probeBestOutput_innovation] at h
  have he : probeBestOutput N + probeInnovationCoefficient N • probeInnovation N -
      probeBestOutput N = probeInnovationCoefficient N • probeInnovation N := by abel
  rw [he, probeInnovation_update_norm] at h
  linarith

theorem probe_monotone_innovation : (∀ N : ℕ, 0 ≤ probeError N) ∧ Antitone probeError ∧
    (∀ N : ℕ, 0 < probeInnovationNormSq N ∧
      probeError N ^ 2 - probeError (N + 1) ^ 2 =
        ‖probeInnovationPairing N‖ ^ 2 / probeInnovationNormSq N) :=
  ⟨probeError_nonneg, probeError_antitone,
    fun N => ⟨probeInnovationNormSq_pos N, probe_innovation_decrement N⟩⟩

def probeDirichletPolynomial {N : ℕ} (x : Fin N → ℂ) (s : ℂ) : ℂ :=
  ∑ i : Fin N, x i * Complex.exp (-s * (Real.log (i.val + 1 : ℕ) : ℂ))

theorem probeExp_neg_log_integer {n : ℕ} (hn : n ≠ 0) :
    Complex.exp (-(Real.log n : ℂ)) = (n : ℂ)⁻¹ := by
  have hp : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log hp]
  push_cast <;> rfl

theorem probeExp_half_integer {n : ℕ} (hn : n ≠ 0) :
    Complex.exp (-(1 / 2 : ℂ) * (Real.log n : ℂ)) = (CCM.nativeIntegerCoefficient n : ℂ) := by
  have hp : 0 < (n : ℝ) := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have he : Real.exp (-(1 / 2 : ℝ) * Real.log n) = CCM.nativeIntegerCoefficient n := by
    calc
      _ = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_def_of_pos hp]
        congr 1
        ring
      _ = ((n : ℝ) ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hp.le _
      _ = _ := by
        unfold CCM.nativeIntegerCoefficient
        rw [Real.sqrt_eq_rpow]
        exact (one_div _).symm
  have hc : -(1 / 2 : ℂ) * (Real.log n : ℂ) = ((-(1 / 2 : ℝ) * Real.log n : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hc, ← Complex.ofReal_exp, he]

theorem probeExp_split_half (z : ℂ) {n : ℕ} (hn : n ≠ 0) :
    Complex.exp (-(z + 1 / 2) * (Real.log n : ℂ)) =
      (CCM.nativeIntegerCoefficient n : ℂ) * Complex.exp (-z * (Real.log n : ℂ)) := by
  have he : -(z + 1 / 2) * (Real.log n : ℂ) =
      -z * (Real.log n : ℂ) + -(1 / 2 : ℂ) * (Real.log n : ℂ) := by ring
  rw [he, Complex.exp_add, probeExp_half_integer hn]
  ring

theorem probeDirichletPolynomial_eq_cpow {N : ℕ} (x : Fin N → ℂ) (s : ℂ) :
    probeDirichletPolynomial x s = ∑ i : Fin N, x i * ((i.val + 1 : ℕ) : ℂ) ^ (-s) := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Nat.succ_ne_zero i.val)),
    ← Complex.natCast_log]
  congr 1
  ring

theorem probeDirichletPolynomial_analyticAt {N : ℕ} (x : Fin N → ℂ) (s : ℂ) :
    AnalyticAt ℂ (probeDirichletPolynomial x) s := by
  unfold probeDirichletPolynomial
  fun_prop

theorem probeDirichletPolynomial_one {N : ℕ} (x : Fin N → ℂ) :
    probeDirichletPolynomial x 1 = ∑ i : Fin N, x i / ((i.val + 1 : ℕ) : ℂ) := by
  unfold probeDirichletPolynomial
  apply Finset.sum_congr rfl
  intro i _
  rw [show (-1 : ℂ) * (Real.log (i.val + 1 : ℕ) : ℂ) =
    -(Real.log (i.val + 1 : ℕ) : ℂ) by ring, probeExp_neg_log_integer (Nat.succ_ne_zero _)]
  rw [div_eq_mul_inv]

theorem probeDirichletPolynomial_hasDerivAt {N : ℕ} (x : Fin N → ℂ) (s : ℂ) :
    HasDerivAt (probeDirichletPolynomial x)
      (∑ i : Fin N, -x i * (Real.log (i.val + 1 : ℕ) : ℂ) *
        Complex.exp (-s * (Real.log (i.val + 1 : ℕ) : ℂ))) s := by
  unfold probeDirichletPolynomial
  apply HasDerivAt.fun_sum
  intro i _
  have hlin : HasDerivAt (fun z : ℂ => -z * (Real.log (i.val + 1 : ℕ) : ℂ))
      (-(Real.log (i.val + 1 : ℕ) : ℂ)) s := by
    simpa only [neg_mul, one_mul, Pi.neg_apply, id_eq, Function.comp_def] using!
      (hasDerivAt_id s).neg.mul_const (Real.log (i.val + 1 : ℕ) : ℂ)
  have he := ((Complex.hasDerivAt_exp _).comp s hlin).const_mul (x i)
  simpa only [neg_mul, mul_neg, mul_comm, mul_left_comm, mul_assoc, Function.comp_def] using! he

theorem probeDirichletPolynomial_deriv_one {N : ℕ} (x : Fin N → ℂ) :
    deriv (probeDirichletPolynomial x) 1 =
      -(∑ i : Fin N, x i * (Real.log (i.val + 1 : ℕ) : ℂ) / ((i.val + 1 : ℕ) : ℂ)) := by
  rw [(probeDirichletPolynomial_hasDerivAt x 1).deriv]
  simp only [neg_mul, one_mul]
  simp_rw [probeExp_neg_log_integer (Nat.succ_ne_zero _)]
  simp only [div_eq_mul_inv, Finset.sum_neg_distrib, mul_assoc, neg_mul]

theorem probeFiniteOutput_laplace_dirichlet (z : ℂ) (hz : 0 < z.re)
    {N : ℕ} (x : Fin N → ℂ) :
    CCM.nativeCausalLaplaceMoment z 0 (probeFiniteOutput x : ProbeL2) =
      probeLaplace probeW z * probeDirichletPolynomial x (z + 1 / 2) := by
  rw [probeFiniteOutput_laplace z hz x, probeDirichletPolynomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [probeColumn_laplace z hz (Nat.succ_ne_zero _), probeExp_split_half z (Nat.succ_ne_zero _)]
  ring

theorem probeResidual_laplace_dirichlet (z : ℂ) (hz : 0 < z.re)
    {N : ℕ} (x : Fin N → ℂ) :
    CCM.nativeCausalLaplaceMoment z 0 (probeResidual x : ProbeL2) =
      probeLaplace probeV z - probeLaplace probeW z * probeDirichletPolynomial x (z + 1 / 2) := by
  rw [← probeEvaluation_apply z hz, probeResidual, map_sub,
    probeEvaluation_apply z hz, probeEvaluation_apply z hz,
    probeTarget_laplace_eq_physical, probeFiniteOutput_laplace_dirichlet z hz x]

theorem JPlus_continuous : Continuous JPlus := by
  have he : JPlus = fun z : ℂ => Complex.exp (-z * (probeSigma : ℂ)) *
      (((Complex.I * z) ^ 2 + 1 / 4) ^ 2 * CCM.UniversalSinc.product probeSigma (Complex.I * z)) :=
    funext JPlus_one_copy_formula
  rw [he]
  have hq : Continuous (fun z : ℂ => CCM.UniversalSinc.product probeSigma (Complex.I * z)) :=
    (CCM.UniversalSinc.differentiable_product probeSigma_pos.le).continuous.comp
      (continuous_const.mul continuous_id)
  exact (by fun_prop : Continuous (fun z : ℂ => Complex.exp (-z * (probeSigma : ℂ)))).mul
    ((by fun_prop : Continuous (fun z : ℂ => ((Complex.I * z) ^ 2 + 1 / 4) ^ 2)).mul hq)

theorem probeW_laplace_boundary (tau : ℝ) :
    probeLaplace probeW (Complex.I * (tau : ℂ)) =
      CCM.nativeCompletionRationalMultiplier (Complex.I * (tau : ℂ)) *
        riemannZeta (Complex.I * (tau : ℂ) + 1 / 2) * JPlus (Complex.I * (tau : ℂ)) := by
  have hz := probeBoundaryParameter_tendsto tau
  have hR : Filter.Tendsto
      (fun n => CCM.nativeCompletionRationalMultiplier (probeBoundaryParameter tau n))
      Filter.atTop (𝓝 (CCM.nativeCompletionRationalMultiplier (Complex.I * (tau : ℂ)))) :=
    (CCM.nativeCompletionRationalMultiplier_analyticAt (by simp [Complex.mul_re])).continuousAt.tendsto.comp hz
  have hne : Complex.I * (tau : ℂ) + 1 / 2 ≠ (1 : ℂ) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re] at hr
  have hZ := (analyticOn_riemannZeta _ hne).continuousAt.tendsto.comp
    (hz.add_const (1 / 2 : ℂ))
  have hJ := (JPlus_continuous.tendsto _).comp hz
  have hprod := (hR.mul hZ).mul hJ
  have hWlim : Filter.Tendsto
      (fun n => probeLaplace probeW (probeBoundaryParameter tau n)) Filter.atTop
      (𝓝 (CCM.nativeCompletionRationalMultiplier (Complex.I * (tau : ℂ)) *
        riemannZeta (Complex.I * (tau : ℂ) + 1 / 2) * JPlus (Complex.I * (tau : ℂ)))) := by
    apply hprod.congr'
    exact Filter.Eventually.of_forall fun n =>
      (probeW_laplace (probeBoundaryParameter_pos tau n) (probeBoundaryParameter_ne_half tau n)).symm
  exact tendsto_nhds_unique
    (probeLaplace_boundary_tendsto probeW probeW_integrable
      (Filter.Eventually.of_forall fun _ ht => probeW_zero_of_neg ht) tau) hWlim

theorem probeColumn_integrable {n : ℕ} (hn : n ≠ 0) :
    Integrable (probeColumn n : ProbeL2) := by
  exact ((probeW_integrable.comp_sub_right (Real.log n)).const_mul
    (CCM.nativeIntegerCoefficient n : ℂ)).congr (probeColumn_coeFn hn).symm

theorem probeFiniteOutput_integrable {N : ℕ} (x : Fin N → ℂ) :
    Integrable (probeFiniteOutput x : ProbeL2) := by
  have hi : ∀ i : Fin N, Integrable (x i • (probeColumn (i.val + 1) : ProbeL2) : ProbeL2) := by
    intro i
    apply ((probeColumn_integrable (Nat.succ_ne_zero i.val)).const_mul (x i)).congr
    filter_upwards [Lp.coeFn_smul (x i) (probeColumn (i.val + 1) : ProbeL2)] with t ht
    simpa only [Pi.smul_apply, smul_eq_mul] using ht.symm
  have he : (probeFiniteOutput x : ProbeL2) =
      ∑ i : Fin N, x i • (probeColumn (i.val + 1) : ProbeL2) := by
    simp only [probeFiniteOutput, Submodule.coe_sum, Submodule.coe_smul_of_tower]
  rw [he]
  apply (integrable_finsetSum Finset.univ (fun i _ => hi i)).congr
  exact (Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : Fin N => x i • (probeColumn (i.val + 1) : ProbeL2))).symm

theorem probeResidual_integrable {N : ℕ} (x : Fin N → ℂ) :
    Integrable (probeResidual x : ProbeL2) := by
  have hv : Integrable (probeTarget : ProbeL2) :=
    probeV_integrable.congr probeTarget_coeFn.symm
  apply (hv.sub (probeFiniteOutput_integrable x)).congr
  exact (Lp.coeFn_sub (probeTarget : ProbeL2) (probeFiniteOutput x : ProbeL2)).symm

theorem probeLaplace_eq_logFourier (f : ℝ → ℂ) (tau : ℝ) :
    probeLaplace f (Complex.I * (tau : ℂ)) = OPICAFollowup.logFourier f tau := by
  unfold probeLaplace OPICAFollowup.logFourier
  congr 1
  funext t
  congr 2
  push_cast
  ring

def probeBoundaryDefect {N : ℕ} (x : Fin N → ℂ) (tau : ℝ) : ℂ :=
  1 - riemannZeta (1 / 2 + Complex.I * (tau : ℂ)) *
    probeDirichletPolynomial x (1 / 2 + Complex.I * (tau : ℂ))

theorem probeResidual_fourier {N : ℕ} (x : Fin N → ℂ) (tau : ℝ) :
    OPICAFollowup.logFourier (probeResidual x : ProbeL2) tau =
      CCM.nativeCompletionRationalMultiplier (Complex.I * (tau : ℂ)) *
        JPlus (Complex.I * (tau : ℂ)) * probeBoundaryDefect x tau := by
  have hz := probeBoundaryParameter_tendsto tau
  have hR :=
    (CCM.nativeCompletionRationalMultiplier_analyticAt
      (by simp [Complex.mul_re] : 0 ≤ (Complex.I * (tau : ℂ)).re)).continuousAt.tendsto.comp hz
  have hne : Complex.I * (tau : ℂ) + 1 / 2 ≠ (1 : ℂ) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re] at hr
  have hZ := (analyticOn_riemannZeta _ hne).continuousAt.tendsto.comp
    (hz.add_const (1 / 2 : ℂ))
  have hJ := (JPlus_continuous.tendsto _).comp hz
  have hP := (probeDirichletPolynomial_analyticAt x
    (Complex.I * (tau : ℂ) + 1 / 2)).continuousAt.tendsto.comp (hz.add_const (1 / 2 : ℂ))
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℂ)) Filter.atTop (𝓝 1) := tendsto_const_nhds
  have hprod := (hR.mul hJ).mul (hone.sub (hZ.mul hP))
  have he : ∀ n : ℕ,
      probeLaplace (probeResidual x : ProbeL2) (probeBoundaryParameter tau n) =
        CCM.nativeCompletionRationalMultiplier (probeBoundaryParameter tau n) *
          JPlus (probeBoundaryParameter tau n) *
            (1 - riemannZeta (probeBoundaryParameter tau n + 1 / 2) *
              probeDirichletPolynomial x (probeBoundaryParameter tau n + 1 / 2)) := by
    intro n
    rw [show probeLaplace (probeResidual x : ProbeL2) (probeBoundaryParameter tau n) =
      CCM.nativeCausalLaplaceMoment (probeBoundaryParameter tau n) 0
        (probeResidual x : ProbeL2) by
          simp only [probeLaplace, CCM.nativeCausalLaplaceMoment, pow_zero, one_mul],
      probeResidual_laplace_dirichlet _ (probeBoundaryParameter_pos tau n),
      probeV_laplace (probeBoundaryParameter_pos tau n).le,
      probeW_laplace (probeBoundaryParameter_pos tau n) (probeBoundaryParameter_ne_half tau n)]
    ring
  have hlim := hprod.congr' (Filter.Eventually.of_forall fun n => (he n).symm)
  have hb := probeLaplace_boundary_tendsto (probeResidual x : ProbeL2)
    (probeResidual_integrable x) (probeResidual x).property tau
  have huniq := tendsto_nhds_unique hb hlim
  rw [probeLaplace_eq_logFourier] at huniq
  simpa only [probeBoundaryDefect, add_comm (Complex.I * (tau : ℂ)) (1 / 2 : ℂ)] using huniq

theorem probeRational_boundary_norm_sq (tau : ℝ) :
    ‖CCM.nativeCompletionRationalMultiplier (Complex.I * (tau : ℂ))‖ ^ 2 =
      1 / (tau ^ 2 + 9 / 4) := by
  have hpos : 0 < tau ^ 2 + 1 / 4 := by positivity
  have hpos' : 0 < tau ^ 2 + 9 / 4 := by positivity
  have hn : ‖Complex.I * (tau : ℂ) - 1 / 2‖ ^ 2 = tau ^ 2 + 1 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.mul_re, Complex.mul_im]
    ring
  have hd : ‖Complex.I * (tau : ℂ) + 1 / 2‖ ^ 2 = tau ^ 2 + 1 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.mul_re, Complex.mul_im]
    ring
  have hd' : ‖Complex.I * (tau : ℂ) + 3 / 2‖ ^ 2 = tau ^ 2 + 9 / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [Complex.mul_re, Complex.mul_im]
    ring
  rw [CCM.nativeCompletionRationalMultiplier, norm_div, div_pow, norm_mul, mul_pow,
    hn, hd, hd']
  field_simp [ne_of_gt hpos, ne_of_gt hpos']

theorem JPlus_boundary_norm (tau : ℝ) :
    ‖JPlus (Complex.I * (tau : ℂ))‖ =
      ‖CCM.nativeOriginalSourceLaplace (Complex.I * (tau : ℂ))‖ := by
  rw [JPlus_eq_delay, norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, Complex.neg_re]

def probeOmega (tau : ℝ) : ℝ :=
  ‖CCM.nativeOriginalSourceLaplace (Complex.I * (tau : ℂ))‖ ^ 2 /
    (2 * Real.pi * (tau ^ 2 + 9 / 4))

theorem probeBoundary_energy {N : ℕ} (x : Fin N → ℂ) (tau : ℝ) :
    1 / (2 * Real.pi) * ‖OPICAFollowup.logFourier (probeResidual x : ProbeL2) tau‖ ^ 2 =
      probeOmega tau * ‖probeBoundaryDefect x tau‖ ^ 2 := by
  rw [probeResidual_fourier, norm_mul, norm_mul, mul_pow, mul_pow,
    probeRational_boundary_norm_sq, JPlus_boundary_norm, probeOmega]
  simp only [div_eq_mul_inv, _root_.mul_inv_rev]
  ring

theorem probe_dirichlet_norm {N : ℕ} (x : Fin N → ℂ) :
    Integrable (fun tau : ℝ => probeOmega tau * ‖probeBoundaryDefect x tau‖ ^ 2) ∧
      ‖probeResidual x‖ ^ 2 =
        ∫ tau : ℝ, probeOmega tau * ‖probeBoundaryDefect x tau‖ ^ 2 := by
  have hp := OPICAFollowup.logFourier_plancherel (probeResidual_integrable x)
    (Lp.memLp (probeResidual x : ProbeL2))
  constructor
  · apply (hp.1.const_mul (1 / (2 * Real.pi))).congr
    exact Filter.Eventually.of_forall fun tau => probeBoundary_energy x tau
  · calc
      ‖probeResidual x‖ ^ 2 = ∫ t : ℝ, ‖(probeResidual x : ProbeL2) t‖ ^ 2 :=
        OPICAFollowup.L2_norm_sq_eq_integral (probeResidual x : ProbeL2)
      _ = 1 / (2 * Real.pi) *
          ∫ tau : ℝ, ‖OPICAFollowup.logFourier (probeResidual x : ProbeL2) tau‖ ^ 2 := hp.2
      _ = ∫ tau : ℝ, 1 / (2 * Real.pi) *
          ‖OPICAFollowup.logFourier (probeResidual x : ProbeL2) tau‖ ^ 2 :=
        (integral_const_mul _ _).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun tau => probeBoundary_energy x tau)

/-- The moment of the unchanged delayed probability source. -/
def probeQbar : ℝ := ∫ t : ℝ, Real.exp (-t / 2) * qPlus t

theorem probeQbar_integrable : Integrable (fun t : ℝ => Real.exp (-t / 2) * qPlus t) := by
  have hc : Continuous (fun t : ℝ => Real.exp (-t / 2) * qPlus t) :=
    (by fun_prop : Continuous (fun t : ℝ => Real.exp (-t / 2))).mul qPlus_contDiff.continuous
  have hs : HasCompactSupport (fun t : ℝ => Real.exp (-t / 2) * qPlus t) := by
    apply HasCompactSupport.intro (K := Icc 0 (2 * probeSigma)) isCompact_Icc
    intro t ht
    rw [qPlus_zero_outside ht, mul_zero]
  exact hc.integrable_of_hasCompactSupport hs

theorem QPlus_half : QPlus (1 / 2 : ℂ) = (probeQbar : ℂ) := by
  rw [QPlus, probeQbar, ← _root_.integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards with t
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 2
  push_cast
  ring

theorem probeQbar_bounds : Real.exp (-probeSigma) ≤ probeQbar ∧ probeQbar ≤ 1 := by
  have hlo (t : ℝ) : Real.exp (-probeSigma) * qPlus t ≤ Real.exp (-t / 2) * qPlus t := by
    by_cases ht : t ∈ Icc 0 (2 * probeSigma)
    · exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 (by linarith [ht.2])) (qPlus_nonneg t)
    · rw [qPlus_zero_outside ht, mul_zero, mul_zero]
  have hhi (t : ℝ) : Real.exp (-t / 2) * qPlus t ≤ qPlus t := by
    by_cases ht : t ∈ Icc 0 (2 * probeSigma)
    · have he : Real.exp (-t / 2) ≤ 1 := Real.exp_le_one_iff.2 (by linarith [ht.1])
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he (qPlus_nonneg t)
    · rw [qPlus_zero_outside ht, mul_zero]
  constructor
  · have h := integral_mono (qPlus_integrable.const_mul (Real.exp (-probeSigma)))
      probeQbar_integrable hlo
    simpa only [integral_const_mul, qPlus_integral_one, mul_one, probeQbar] using h
  · have h := integral_mono probeQbar_integrable qPlus_integrable hhi
    simpa only [probeQbar, qPlus_integral_one] using h

theorem probeQbar_pos : 0 < probeQbar := (Real.exp_pos _).trans_le probeQbar_bounds.1

theorem QPlus_analyticAt (z : ℂ) : AnalyticAt ℂ QPlus z := by
  have he : QPlus = fun z : ℂ => Complex.exp (-z * (probeSigma : ℂ)) *
      CCM.UniversalSinc.product probeSigma (Complex.I * z) := funext QPlus_one_copy_formula
  rw [he]
  exact (by fun_prop : AnalyticAt ℂ (fun z : ℂ => Complex.exp (-z * (probeSigma : ℂ))) z).mul
    ((CCM.UniversalSinc.analyticAt_product probeSigma_pos.le (Complex.I * z)).comp
      (by fun_prop : AnalyticAt ℂ (fun z : ℂ => Complex.I * z) z))

def probeVLocalFactor (z : ℂ) : ℂ := (z + 1 / 2) / (z + 3 / 2) * QPlus z
def probeWLocalFactor (z : ℂ) : ℂ :=
  CCM.nativePositiveCompletionLaplace z * (z + 1 / 2) ^ 2 * QPlus z

theorem probeVLocalFactor_analytic : AnalyticAt ℂ probeVLocalFactor (1 / 2 : ℂ) := by
  exact ((analyticAt_id.add analyticAt_const).div (analyticAt_id.add analyticAt_const)
    (by norm_num : (1 / 2 : ℂ) + 3 / 2 ≠ 0)).mul (QPlus_analyticAt _)

theorem probeWLocalFactor_analytic : AnalyticAt ℂ probeWLocalFactor (1 / 2 : ℂ) := by
  exact ((CCM.nativePositiveCompletionLaplace_analyticAt
    (by norm_num : 0 < (1 / 2 : ℂ).re)).mul
      ((analyticAt_id.add analyticAt_const).pow 2)).mul (QPlus_analyticAt _)

theorem probeVLocalFactor_half : probeVLocalFactor (1 / 2 : ℂ) = (probeQbar : ℂ) / 2 := by
  rw [probeVLocalFactor, QPlus_half]
  norm_num <;> ring

theorem probeWLocalFactor_half : probeWLocalFactor (1 / 2 : ℂ) = (probeQbar : ℂ) / 2 := by
  rw [probeWLocalFactor, CCM.nativePositiveCompletion_complexLaplace_half, QPlus_half]
  norm_num <;> ring

theorem probeV_local_factorization :
    (fun z : ℂ => probeLaplace probeV z) =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun z => (z - 1 / 2) ^ 3 * probeVLocalFactor z := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by norm_num : 0 < (1 / 2 : ℂ).re)] with z hz
  rw [probeV_laplace hz.le, JPlus_eq_pole_polynomial_QPlus,
    CCM.nativeCompletionRationalMultiplier, probeVLocalFactor]
  have hd : z + 1 / 2 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    linarith
  have hd' : z + 3 / 2 ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    linarith
  have hratio : ((z - 1 / 2) * (z ^ 2 - 1 / 4) ^ 2) /
      ((z + 1 / 2) * (z + 3 / 2)) =
      ((z - 1 / 2) ^ 3 * (z + 1 / 2)) / (z + 3 / 2) := by
    apply (div_eq_div_iff (mul_ne_zero hd hd') hd').2
    ring
  calc
    _ = (((z - 1 / 2) * (z ^ 2 - 1 / 4) ^ 2) /
      ((z + 1 / 2) * (z + 3 / 2))) * QPlus z := by ring
    _ = _ := by rw [hratio]; ring

theorem probeW_local_factorization :
    (fun z : ℂ => probeLaplace probeW z) =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun z => (z - 1 / 2) ^ 2 * probeWLocalFactor z := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by norm_num : 0 < (1 / 2 : ℂ).re)] with z hz
  rw [probeW_laplace_actual hz.le, JPlus_eq_pole_polynomial_QPlus, probeWLocalFactor]
  ring

theorem probePolePower_deriv (n k : ℕ) :
    iteratedDeriv k (fun z : ℂ => (z - 1 / 2) ^ n) (1 / 2 : ℂ) =
      (n.descFactorial k : ℂ) * (0 : ℂ) ^ (n - k) := by
  have h := congrFun (iteratedDeriv_comp_sub_const k (fun z : ℂ => z ^ n) (1 / 2 : ℂ)) (1 / 2 : ℂ)
  simpa only [sub_self, iteratedDeriv_pow] using h

theorem probeV_second_half : iteratedDeriv 2 (probeLaplace probeV) (1 / 2 : ℂ) = 0 := by
  rw [probeV_local_factorization.iteratedDeriv_eq 2,
    iteratedDeriv_fun_mul (by fun_prop : ContDiffAt ℂ 2 (fun z : ℂ => (z - 1 / 2) ^ 3) (1 / 2 : ℂ))
      probeVLocalFactor_analytic.contDiffAt]
  norm_num [Finset.sum_range_succ, probePolePower_deriv]

theorem probeV_third_half : iteratedDeriv 3 (probeLaplace probeV) (1 / 2 : ℂ) =
    3 * (probeQbar : ℂ) := by
  rw [probeV_local_factorization.iteratedDeriv_eq 3,
    iteratedDeriv_fun_mul (by fun_prop : ContDiffAt ℂ 3 (fun z : ℂ => (z - 1 / 2) ^ 3) (1 / 2 : ℂ))
      probeVLocalFactor_analytic.contDiffAt]
  norm_num [Finset.sum_range_succ, probePolePower_deriv,
    iteratedDeriv_zero, probeVLocalFactor_half] <;> ring

theorem probeW_first_half : deriv (probeLaplace probeW) (1 / 2 : ℂ) = 0 := by
  rw [← iteratedDeriv_one]
  rw [probeW_local_factorization.iteratedDeriv_eq 1,
    iteratedDeriv_fun_mul (by fun_prop : ContDiffAt ℂ 1 (fun z : ℂ => (z - 1 / 2) ^ 2) (1 / 2 : ℂ))
      probeWLocalFactor_analytic.contDiffAt]
  norm_num [Finset.sum_range_succ, probePolePower_deriv]

theorem probeW_second_half : iteratedDeriv 2 (probeLaplace probeW) (1 / 2 : ℂ) = (probeQbar : ℂ) := by
  rw [probeW_local_factorization.iteratedDeriv_eq 2,
    iteratedDeriv_fun_mul (by fun_prop : ContDiffAt ℂ 2 (fun z : ℂ => (z - 1 / 2) ^ 2) (1 / 2 : ℂ))
      probeWLocalFactor_analytic.contDiffAt]
  norm_num [Finset.sum_range_succ, probePolePower_deriv,
    iteratedDeriv_zero, probeWLocalFactor_half] <;> ring

theorem probeHalfWitness_norm_sq (k : ℕ) :
    ‖CCM.nativeCausalExponentialWitness (1 / 2 : ℂ) (by norm_num) k‖ ^ 2 = ((2 * k).factorial : ℝ) := by
  change ‖CCM.nativeCausalExponentialPolynomialL2 (1 / 2 : ℂ) (by norm_num) k‖ ^ 2 = _
  have hrep := CCM.nativeCausalExponentialPolynomialL2_coeFn (1 / 2 : ℂ) (by norm_num) k
  calc
    _ = ∫ t : ℝ, ‖CCM.nativeCausalExponentialPolynomial (1 / 2 : ℂ) k t‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hrep] with t ht
      change inner ℝ (CCM.nativeCausalExponentialPolynomialL2 (1 / 2 : ℂ) (by norm_num) k t)
        (CCM.nativeCausalExponentialPolynomialL2 (1 / 2 : ℂ) (by norm_num) k t) = _
      rw [ht, real_inner_self_eq_norm_sq]
    _ = ∫ t : ℝ, (Ici (0 : ℝ)).indicator (fun t : ℝ => t ^ (2 * k) * Real.exp (-t)) t := by
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : 0 ≤ t
      · have hi : (Ici (0 : ℝ)).indicator (fun t : ℝ => t ^ (2 * k) * Real.exp (-t)) t =
            t ^ (2 * k) * Real.exp (-t) := Set.indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht) _
        rw [hi, CCM.nativeCausalExponentialPolynomial_norm_sq _ _ ht]
        norm_num
      · have hi : (Ici (0 : ℝ)).indicator (fun t : ℝ => t ^ (2 * k) * Real.exp (-t)) t = 0 :=
          Set.indicator_of_notMem (show t ∉ Ici (0 : ℝ) from ht) _
        rw [hi,
          CCM.nativeCausalExponentialPolynomial_zero_of_neg _ _ (lt_of_not_ge ht)]
        norm_num
    _ = ∫ t in Ioi (0 : ℝ), Real.exp (-t) * t ^ (2 * k) := by
      rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
      congr 1
      funext t
      ring
    _ = _ := OPICAFollowup.exp_neg_monomial_integral (2 * k)

theorem probeHalfDerivative_bound (k : ℕ) (f : CausalProbeL2) :
    ‖iteratedDeriv k (fun z : ℂ => CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2)) (1 / 2 : ℂ)‖ ≤
      Real.sqrt ((2 * k).factorial : ℝ) * ‖f‖ := by
  rw [CCM.nativeCausalLaplaceMoment_iteratedDeriv _ (by norm_num), norm_mul]
  norm_num only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
  rw [← CCM.nativeCausalExponentialWitness_inner_eq_laplaceMoment _ (by norm_num)]
  have hn : ‖CCM.nativeCausalExponentialWitness (1 / 2 : ℂ) (by norm_num) k‖ =
      Real.sqrt ((2 * k).factorial : ℝ) := by
    rw [← probeHalfWitness_norm_sq k, Real.sqrt_sq (norm_nonneg _)]
  simpa only [hn] using norm_inner_le_norm
    (CCM.nativeCausalExponentialWitness (1 / 2 : ℂ) (by norm_num) k) f

theorem probeV_transform_analytic : AnalyticAt ℂ (probeLaplace probeV) (1 / 2 : ℂ) := by
  have he : (fun z : ℂ => CCM.nativeCausalLaplaceMoment z 0 (probeTarget : ProbeL2)) =
      probeLaplace probeV := funext probeTarget_laplace_eq_physical
  rw [← he]
  exact CCM.nativeCausalLaplaceMoment_analyticAt _ (by norm_num) 0 probeTarget

theorem probeW_transform_analytic : AnalyticAt ℂ (probeLaplace probeW) (1 / 2 : ℂ) := by
  have he : (fun z : ℂ => CCM.nativeCausalLaplaceMoment z 0 (probeCompletedSource : ProbeL2)) =
      probeLaplace probeW := funext probeCompletedSource_laplace_eq_physical
  rw [← he]
  exact CCM.nativeCausalLaplaceMoment_analyticAt _ (by norm_num) 0 probeCompletedSource

theorem probeResidual_local_dirichlet {N : ℕ} (x : Fin N → ℂ) :
    (fun z : ℂ => CCM.nativeCausalLaplaceMoment z 0 (probeResidual x : ProbeL2)) =ᶠ[𝓝 (1 / 2 : ℂ)]
      fun z => probeLaplace probeV z - probeLaplace probeW z * probeDirichletPolynomial x (z + 1 / 2) := by
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (by norm_num : 0 < (1 / 2 : ℂ).re)] with z hz
  exact probeResidual_laplace_dirichlet z hz x

theorem probeResidual_second_half {N : ℕ} (x : Fin N → ℂ) :
    iteratedDeriv 2 (fun z : ℂ => CCM.nativeCausalLaplaceMoment z 0 (probeResidual x : ProbeL2))
      (1 / 2 : ℂ) = -(probeQbar : ℂ) * probeDirichletPolynomial x 1 := by
  have hp : AnalyticAt ℂ (fun z : ℂ => probeDirichletPolynomial x (z + 1 / 2)) (1 / 2 : ℂ) :=
    (probeDirichletPolynomial_analyticAt x _).comp (analyticAt_id.add analyticAt_const)
  rw [(probeResidual_local_dirichlet x).iteratedDeriv_eq 2]
  change iteratedDeriv 2 (probeLaplace probeV -
    probeLaplace probeW * (fun z : ℂ => probeDirichletPolynomial x (z + 1 / 2))) (1 / 2 : ℂ) = _
  rw [iteratedDeriv_sub probeV_transform_analytic.contDiffAt
      (probeW_transform_analytic.mul hp).contDiffAt,
    iteratedDeriv_mul probeW_transform_analytic.contDiffAt hp.contDiffAt,
    probeV_second_half]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    probeW_laplace_half, probeW_first_half, probeW_second_half]

theorem probeResidual_third_half {N : ℕ} (x : Fin N → ℂ) :
    iteratedDeriv 3 (fun z : ℂ => CCM.nativeCausalLaplaceMoment z 0 (probeResidual x : ProbeL2))
      (1 / 2 : ℂ) = 3 * (probeQbar : ℂ) * (1 - deriv (probeDirichletPolynomial x) 1) -
        iteratedDeriv 3 (probeLaplace probeW) (1 / 2 : ℂ) * probeDirichletPolynomial x 1 := by
  have hp : AnalyticAt ℂ (fun z : ℂ => probeDirichletPolynomial x (z + 1 / 2)) (1 / 2 : ℂ) :=
    (probeDirichletPolynomial_analyticAt x _).comp (analyticAt_id.add analyticAt_const)
  rw [(probeResidual_local_dirichlet x).iteratedDeriv_eq 3]
  change iteratedDeriv 3 (probeLaplace probeV -
    probeLaplace probeW * (fun z : ℂ => probeDirichletPolynomial x (z + 1 / 2))) (1 / 2 : ℂ) = _
  rw [iteratedDeriv_sub probeV_transform_analytic.contDiffAt
      (probeW_transform_analytic.mul hp).contDiffAt,
    iteratedDeriv_mul probeW_transform_analytic.contDiffAt hp.contDiffAt,
    probeV_third_half]
  norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one,
    probeW_laplace_half, probeW_first_half, probeW_second_half, deriv_comp_add_const] <;> ring

theorem probe_pole_value_bound {N : ℕ} (x : Fin N → ℂ) :
    probeQbar * ‖probeDirichletPolynomial x 1‖ ≤ Real.sqrt 24 * ‖probeResidual x‖ := by
  have hb := probeHalfDerivative_bound 2 (probeResidual x)
  rw [probeResidual_second_half, norm_mul, norm_neg, Complex.norm_real,
    Real.norm_of_nonneg probeQbar_pos.le] at hb
  norm_num at hb ⊢
  exact hb

theorem probe_pole_derivative_bound {N : ℕ} (x : Fin N → ℂ) :
    ‖3 * (probeQbar : ℂ) * (1 - deriv (probeDirichletPolynomial x) 1) -
      iteratedDeriv 3 (probeLaplace probeW) (1 / 2 : ℂ) * probeDirichletPolynomial x 1‖ ≤
        Real.sqrt 720 * ‖probeResidual x‖ := by
  have hb := probeHalfDerivative_bound 3 (probeResidual x)
  rw [probeResidual_third_half] at hb
  norm_num at hb ⊢
  exact hb

theorem probe_pole_constrained_derivative_bound {N : ℕ} (x : Fin N → ℂ)
    (hx : probeDirichletPolynomial x 1 = 0) :
    3 * probeQbar * ‖1 - deriv (probeDirichletPolynomial x) 1‖ ≤
      Real.sqrt 720 * ‖probeResidual x‖ := by
  have h := probe_pole_derivative_bound x
  rw [hx, mul_zero, sub_zero, norm_mul, norm_mul, Complex.norm_ofNat,
    Complex.norm_real, Real.norm_of_nonneg probeQbar_pos.le] at h
  exact h

theorem probe_pole_value_norm_le {N : ℕ} (x : Fin N → ℂ) :
    ‖probeDirichletPolynomial x 1‖ ≤ (Real.sqrt 24 / probeQbar) * ‖probeResidual x‖ := by
  have h : ‖probeDirichletPolynomial x 1‖ * probeQbar ≤ Real.sqrt 24 * ‖probeResidual x‖ := by
    simpa only [mul_comm] using probe_pole_value_bound x
  have hd := (le_div_iff₀ probeQbar_pos).2 h
  simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hd

theorem probe_pole_derivative_norm_le {N : ℕ} (x : Fin N → ℂ) :
    ‖1 - deriv (probeDirichletPolynomial x) 1‖ ≤
      (Real.sqrt 720 * ‖probeResidual x‖ +
        ‖iteratedDeriv 3 (probeLaplace probeW) (1 / 2 : ℂ)‖ * ‖probeDirichletPolynomial x 1‖) /
          (3 * probeQbar) := by
  apply (le_div_iff₀ (mul_pos (by norm_num) probeQbar_pos)).2
  calc
    ‖1 - deriv (probeDirichletPolynomial x) 1‖ * (3 * probeQbar) =
        ‖3 * (probeQbar : ℂ) * (1 - deriv (probeDirichletPolynomial x) 1)‖ := by
      rw [norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
        Real.norm_of_nonneg probeQbar_pos.le]
      ring
    _ ≤ ‖3 * (probeQbar : ℂ) * (1 - deriv (probeDirichletPolynomial x) 1) -
          iteratedDeriv 3 (probeLaplace probeW) (1 / 2 : ℂ) * probeDirichletPolynomial x 1‖ +
        ‖iteratedDeriv 3 (probeLaplace probeW) (1 / 2 : ℂ) * probeDirichletPolynomial x 1‖ := by
      simpa only [sub_add_cancel] using norm_add_le
        (3 * (probeQbar : ℂ) * (1 - deriv (probeDirichletPolynomial x) 1) -
          iteratedDeriv 3 (probeLaplace probeW) (1 / 2 : ℂ) * probeDirichletPolynomial x 1)
        (iteratedDeriv 3 (probeLaplace probeW) (1 / 2 : ℂ) * probeDirichletPolynomial x 1)
    _ ≤ _ := by
      rw [norm_mul]
      exact add_le_add (probe_pole_derivative_bound x) le_rfl

theorem probe_pole_moment_limits (N : ℕ → ℕ) (x : ∀ k : ℕ, Fin (N k) → ℂ)
    (h : Filter.Tendsto (fun k => ‖probeResidual (x k)‖) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun k => probeDirichletPolynomial (x k) 1) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun k => deriv (probeDirichletPolynomial (x k)) 1) Filter.atTop (𝓝 1) := by
  have hP : Filter.Tendsto (fun k => probeDirichletPolynomial (x k) 1) Filter.atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => probe_pole_value_norm_le (x k))
    simpa only [mul_zero] using (tendsto_const_nhds.mul h :
      Filter.Tendsto (fun k => (Real.sqrt 24 / probeQbar) * ‖probeResidual (x k)‖)
        Filter.atTop (𝓝 ((Real.sqrt 24 / probeQbar) * 0)))
  have hPn : Filter.Tendsto (fun k => ‖probeDirichletPolynomial (x k) 1‖)
      Filter.atTop (𝓝 0) := by simpa only [norm_zero] using hP.norm
  have hD : Filter.Tendsto (fun k => 1 - deriv (probeDirichletPolynomial (x k)) 1)
      Filter.atTop (𝓝 (0 : ℂ)) := by
    apply squeeze_zero_norm (fun k => probe_pole_derivative_norm_le (x k))
    have hlim := ((h.const_mul (Real.sqrt 720)).add
      (hPn.const_mul ‖iteratedDeriv 3 (probeLaplace probeW) (1 / 2 : ℂ)‖)).div_const (3 * probeQbar)
    simpa only [mul_zero, zero_add, zero_div] using hlim
  refine ⟨hP, ?_⟩
  have hone : Filter.Tendsto (fun _ : ℕ => (1 : ℂ)) Filter.atTop (𝓝 1) := tendsto_const_nhds
  simpa only [sub_sub_cancel, sub_zero] using hone.sub hD

theorem native_probe_pole_moment_constraints :
    0 < probeQbar ∧ QPlus (1 / 2 : ℂ) = (probeQbar : ℂ) ∧
    iteratedDeriv 2 (probeLaplace probeV) (1 / 2 : ℂ) = 0 ∧
    iteratedDeriv 3 (probeLaplace probeV) (1 / 2 : ℂ) = 3 * (probeQbar : ℂ) ∧
    probeLaplace probeW (1 / 2 : ℂ) = 0 ∧ deriv (probeLaplace probeW) (1 / 2 : ℂ) = 0 ∧
    iteratedDeriv 2 (probeLaplace probeW) (1 / 2 : ℂ) = (probeQbar : ℂ) ∧
    (∀ (N : ℕ) (x : Fin N → ℂ),
      probeQbar * ‖probeDirichletPolynomial x 1‖ ≤ Real.sqrt 24 * ‖probeResidual x‖ ∧
      ‖3 * (probeQbar : ℂ) * (1 - deriv (probeDirichletPolynomial x) 1) -
        iteratedDeriv 3 (probeLaplace probeW) (1 / 2 : ℂ) * probeDirichletPolynomial x 1‖ ≤
          Real.sqrt 720 * ‖probeResidual x‖ ∧
      (probeDirichletPolynomial x 1 = 0 →
        3 * probeQbar * ‖1 - deriv (probeDirichletPolynomial x) 1‖ ≤ Real.sqrt 720 * ‖probeResidual x‖) ∧
      deriv (probeDirichletPolynomial x) 1 =
        -(∑ i : Fin N, x i * (Real.log (i.val + 1 : ℕ) : ℂ) / ((i.val + 1 : ℕ) : ℂ))) ∧
    (∀ (N : ℕ → ℕ) (x : ∀ k : ℕ, Fin (N k) → ℂ),
      Filter.Tendsto (fun k => ‖probeResidual (x k)‖) Filter.atTop (𝓝 0) →
      Filter.Tendsto (fun k => probeDirichletPolynomial (x k) 1) Filter.atTop (𝓝 0) ∧
      Filter.Tendsto (fun k => deriv (probeDirichletPolynomial (x k)) 1) Filter.atTop (𝓝 1)) :=
  ⟨probeQbar_pos, QPlus_half, probeV_second_half, probeV_third_half, probeW_laplace_half,
    probeW_first_half, probeW_second_half,
    fun _ x => ⟨probe_pole_value_bound x, probe_pole_derivative_bound x,
      probe_pole_constrained_derivative_bound x, probeDirichletPolynomial_deriv_one x⟩,
    probe_pole_moment_limits⟩


end Zeta23.OPICARound2
