import Zeta23.CCM.OriginalSincDriveLp
import Zeta23.CCM.NativeDampedCompletionOperator
import Mathlib.Analysis.Convolution

/-!
# Independent stability of the literal completed input

The function Y is the actual full-line convolution c * U, where U is the
unchanged original integer drive and c is the signed causal correction
kernel -exp(-t/2) + 2 exp(-3t/2). Its stability follows from the already
proved source-defined U integrability, without assuming that the prime
field X belongs to L2 or that Y lies in the completion operator's range.
The separate equation a * X = c * U is not part of the definition.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Zeta23.CCM

def nativeCompletionCorrection (t : ℝ) : ℝ :=
  if 0 ≤ t then -Real.exp (-(t / 2)) + 2 * Real.exp (-(3 * t / 2)) else 0

theorem nativeCompletionCorrection_zero_of_neg {t : ℝ} (ht : t < 0) :
    nativeCompletionCorrection t = 0 := by
  simp [nativeCompletionCorrection, not_le.mpr ht]

theorem nativeCompletionCorrection_measurable : Measurable nativeCompletionCorrection := by
  unfold nativeCompletionCorrection
  apply Measurable.ite measurableSet_Ici <;> fun_prop

theorem nativeCompletionCorrection_abs_le_three (t : ℝ) :
    |nativeCompletionCorrection t| ≤ 3 := by
  by_cases ht : 0 ≤ t
  · rw [nativeCompletionCorrection, if_pos ht]
    have h1 : Real.exp (-(t / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h3 : Real.exp (-(3 * t / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc
      _ ≤ |-Real.exp (-(t / 2))| + |2 * Real.exp (-(3 * t / 2))| := abs_add_le _ _
      _ = Real.exp (-(t / 2)) + 2 * Real.exp (-(3 * t / 2)) := by
        rw [abs_neg, abs_of_pos (Real.exp_pos _), abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2),
          abs_of_pos (Real.exp_pos _)]
      _ ≤ 3 := by linarith
  · rw [nativeCompletionCorrection_zero_of_neg (lt_of_not_ge ht), abs_zero]
    norm_num

theorem nativeCompletionCorrection_integrable : Integrable nativeCompletionCorrection := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-(t / 2))) (Ioi 0) := by
    simpa only [show ∀ t : ℝ, -(1 / 2 : ℝ) * t = -(t / 2) by intro t; ring] using
      integrableOn_exp_mul_Ioi (a := -(1 / 2 : ℝ)) (by norm_num) 0
  have h3 : IntegrableOn (fun t : ℝ => Real.exp (-(3 * t / 2))) (Ioi 0) := by
    simpa only [show ∀ t : ℝ, -(3 / 2 : ℝ) * t = -(3 * t / 2) by intro t; ring] using
      integrableOn_exp_mul_Ioi (a := -(3 / 2 : ℝ)) (by norm_num) 0
  have hpos : IntegrableOn nativeCompletionCorrection (Ioi 0) :=
    (h1.neg.add (h3.const_mul 2)).congr_fun
      (fun t ht => by
        have htp : (0 : ℝ) < t := ht
        simp [nativeCompletionCorrection, htp.le]) measurableSet_Ioi
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Iio 0)).congr_fun
    (fun t ht => (nativeCompletionCorrection_zero_of_neg ht).symm) measurableSet_Iio

/-- Literal c * U, before any function-space realization or range claim. -/
def nativeCompletedInput (t : ℝ) : ℝ :=
  ∫ s : ℝ, nativeCompletionCorrection s * nativeOriginalIntegerDrive (t - s)

theorem nativeCompletedInput_integrable : Integrable nativeCompletedInput := by
  exact nativeCompletionCorrection_integrable.integrable_convolution
    (L := ContinuousLinearMap.lsmul ℝ ℝ) nativeOriginalIntegerDrive_integrable

theorem nativeCompletedInput_zero_of_neg {t : ℝ} (ht : t < 0) :
    nativeCompletedInput t = 0 := by
  unfold nativeCompletedInput
  apply integral_eq_zero_of_ae
  filter_upwards with s
  change nativeCompletionCorrection s * nativeOriginalIntegerDrive (t - s) = 0
  by_cases hs : s < 0
  · rw [nativeCompletionCorrection_zero_of_neg hs, zero_mul]
  · rw [nativeOriginalIntegerDrive_zero_of_neg (by linarith [le_of_not_gt hs]), mul_zero]

def nativeCompletedInputUniformBound : ℝ :=
  3 * ∫ t : ℝ, |nativeOriginalIntegerDrive t|

theorem nativeCompletedInputUniformBound_nonneg : 0 ≤ nativeCompletedInputUniformBound :=
  mul_nonneg (by norm_num) (integral_nonneg (fun _ => abs_nonneg _))

/-- The actual pointwise integral is uniformly bounded by the original
integer drive's paid L1 norm and the literal correction-kernel bound. -/
theorem nativeCompletedInput_abs_le_uniform (t : ℝ) :
    |nativeCompletedInput t| ≤ nativeCompletedInputUniformBound := by
  have hU : Integrable (fun s : ℝ => |nativeOriginalIntegerDrive s|) := by
    simpa only [Real.norm_eq_abs] using nativeOriginalIntegerDrive_integrable.norm
  have hshift : Integrable (fun s : ℝ => |nativeOriginalIntegerDrive (t - s)|) :=
    (integrable_comp_sub_left (fun s : ℝ => |nativeOriginalIntegerDrive s|) t).mpr hU
  calc
    _ ≤ ∫ s : ℝ, |nativeCompletionCorrection s * nativeOriginalIntegerDrive (t - s)| := by
      simpa only [nativeCompletedInput, Real.norm_eq_abs] using
        (norm_integral_le_integral_norm
          (fun s : ℝ => nativeCompletionCorrection s * nativeOriginalIntegerDrive (t - s)))
    _ ≤ ∫ s : ℝ, 3 * |nativeOriginalIntegerDrive (t - s)| := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
        (hshift.const_mul 3)
      filter_upwards with s
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (nativeCompletionCorrection_abs_le_three s) (abs_nonneg _)
    _ = _ := by
      rw [integral_const_mul]
      unfold nativeCompletedInputUniformBound
      congr 1
      exact integral_sub_left_eq_self (fun s : ℝ => |nativeOriginalIntegerDrive s|) volume t

theorem nativeCompletedInput_norm_sq_integrable :
    Integrable (fun t : ℝ => |nativeCompletedInput t| ^ 2) := by
  have hU : Integrable (fun t : ℝ => |nativeCompletedInput t|) := by
    simpa only [Real.norm_eq_abs] using nativeCompletedInput_integrable.norm
  have hae : AEStronglyMeasurable (fun t : ℝ => |nativeCompletedInput t|) := by
    simpa only [Real.norm_eq_abs] using nativeCompletedInput_integrable.aestronglyMeasurable.norm
  apply (hU.const_mul nativeCompletedInputUniformBound).mono' (hae.pow 2)
  filter_upwards with t
  change ‖|nativeCompletedInput t| ^ 2‖ ≤ nativeCompletedInputUniformBound * |nativeCompletedInput t|
  rw [Real.norm_of_nonneg (sq_nonneg _), pow_two]
  exact mul_le_mul_of_nonneg_right (nativeCompletedInput_abs_le_uniform t) (abs_nonneg _)

def nativeDampedCompletedInput (epsilon t : ℝ) : ℂ :=
  ((Real.exp (-epsilon * t) * nativeCompletedInput t : ℝ) : ℂ)

theorem nativeDampedCompletedInput_aestronglyMeasurable (epsilon : ℝ) :
    AEStronglyMeasurable (nativeDampedCompletedInput epsilon) := by
  exact Complex.continuous_ofReal.comp_aestronglyMeasurable
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable.mul
      nativeCompletedInput_integrable.aestronglyMeasurable)

theorem nativeDampedCompletedInput_zero_of_neg (epsilon : ℝ) {t : ℝ} (ht : t < 0) :
    nativeDampedCompletedInput epsilon t = 0 := by
  rw [nativeDampedCompletedInput, nativeCompletedInput_zero_of_neg ht, mul_zero, Complex.ofReal_zero]

theorem nativeDampedCompletedInput_norm_le {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) (t : ℝ) :
    ‖nativeDampedCompletedInput epsilon t‖ ≤ |nativeCompletedInput t| := by
  by_cases ht : 0 ≤ t
  · rw [nativeDampedCompletedInput, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have hE : Real.exp (-epsilon * t) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hepsilon) ht)
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hE (abs_nonneg (nativeCompletedInput t))
  · rw [nativeDampedCompletedInput_zero_of_neg epsilon (lt_of_not_ge ht),
      nativeCompletedInput_zero_of_neg (lt_of_not_ge ht), norm_zero, abs_zero]

theorem nativeDampedCompletedInput_norm_sq_integrable {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    Integrable (fun t : ℝ => ‖nativeDampedCompletedInput epsilon t‖ ^ 2) := by
  apply nativeCompletedInput_norm_sq_integrable.mono'
    ((nativeDampedCompletedInput_aestronglyMeasurable epsilon).norm.pow 2)
  filter_upwards with t
  change ‖‖nativeDampedCompletedInput epsilon t‖ ^ 2‖ ≤ |nativeCompletedInput t| ^ 2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact (sq_le_sq₀ (norm_nonneg _) (abs_nonneg _)).mpr
    (nativeDampedCompletedInput_norm_le hepsilon t)

theorem nativeCompletedInput_memLp {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    MemLp (nativeDampedCompletedInput epsilon) 2 volume :=
  (memLp_two_iff_integrable_sq_norm
    (nativeDampedCompletedInput_aestronglyMeasurable epsilon)).mpr
      (nativeDampedCompletedInput_norm_sq_integrable hepsilon)

def nativeDampedCompletedInputL2 (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) : NativeCompletionL2 :=
  (nativeCompletedInput_memLp hepsilon).toLp (nativeDampedCompletedInput epsilon)

theorem nativeDampedCompletedInputL2_coeFn (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    nativeDampedCompletedInputL2 epsilon hepsilon =ᵐ[volume] nativeDampedCompletedInput epsilon :=
  (nativeCompletedInput_memLp hepsilon).coeFn_toLp

theorem nativeDampedCompletedInputL2_causal (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    nativeDampedCompletedInputL2 epsilon hepsilon ∈ nativeCompletionCausalL2 := by
  change ∀ᵐ t : ℝ, t < 0 → nativeDampedCompletedInputL2 epsilon hepsilon t = 0
  filter_upwards [nativeDampedCompletedInputL2_coeFn epsilon hepsilon] with t ht
  intro htneg
  rw [ht]
  exact nativeDampedCompletedInput_zero_of_neg epsilon htneg

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeCompletionCorrection_integrable
#print axioms Zeta23.CCM.nativeCompletedInput_integrable
#print axioms Zeta23.CCM.nativeCompletedInput_abs_le_uniform
#print axioms Zeta23.CCM.nativeCompletedInput_memLp
#print axioms Zeta23.CCM.nativeDampedCompletedInputL2_causal
