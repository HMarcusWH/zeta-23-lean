import Zeta23.CCM.OriginalSincDriveDecay
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Integrability of the actual unchanged integer drive

The native field's continuity comes from its literal locally finite integer
histories. Its support starts strictly after zero at the frozen source scale.
The proved source-defined decay then supplies genuine L1 and L2 membership
by integrating polynomial exponential envelopes on the positive half-line.

The complex damped function and its L2 realization retain the unchanged
integer coefficients. No stability premise, prime-field membership, inverse,
range membership or completed-input equation is assumed or inferred.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace Zeta23.CCM

theorem nativeOriginalSource_scale_lt_log_two : UniversalSinc.fixedScale < Real.log 2 := by
  have hlog := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at hlog
  unfold UniversalSinc.fixedScale
  linarith

/-- Actual pre-first-prime support supplies full-line causality. -/
theorem nativeOriginalIntegerDrive_zero_of_neg {t : ℝ} (ht : t < 0) :
    nativeOriginalIntegerDrive t = 0 := by
  unfold nativeOriginalIntegerDrive
  apply nativeIntegerDriveField_zero_before_firstPrime nativeOriginalSource_supported
  linarith [nativeOriginalSource_scale_lt_log_two]

/-- This consumes the proved continuity of the literal locally finite sum. -/
theorem nativeOriginalIntegerDrive_measurable : Measurable nativeOriginalIntegerDrive :=
  nativeOriginalIntegerDrive_continuous.measurable

private theorem pow_exp_integrableOn (n : ℕ) {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-a * t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n : ℝ)) (p := (1 : ℝ)) (b := a)
    (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) ha
  simpa only [Real.rpow_natCast, Real.rpow_one] using! h

private theorem affine_exp_integrableOn {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun t : ℝ => (c + t) * Real.exp (-a * t)) (Ioi 0) := by
  have h0 : IntegrableOn (fun t : ℝ => Real.exp (-a * t)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using! pow_exp_integrableOn 0 ha
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-a * t)) (Ioi 0) := by
    simpa only [pow_one] using! pow_exp_integrableOn 1 ha
  have heq : (fun t : ℝ => (c + t) * Real.exp (-a * t)) =
      fun t => c * Real.exp (-a * t) + t * Real.exp (-a * t) := by
    funext t
    ring
  rw [heq]
  exact (h0.const_mul c).add h1

private theorem affine_exp_sq_integrableOn {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun t : ℝ => ((c + t) * Real.exp (-a * t)) ^ 2) (Ioi 0) := by
  have hdouble : 0 < 2 * a := mul_pos (by norm_num) ha
  have h0 : IntegrableOn (fun t : ℝ => Real.exp (-(2 * a) * t)) (Ioi 0) := by
    simpa only [pow_zero, one_mul] using! pow_exp_integrableOn 0 hdouble
  have h1 : IntegrableOn (fun t : ℝ => t * Real.exp (-(2 * a) * t)) (Ioi 0) := by
    simpa only [pow_one] using! pow_exp_integrableOn 1 hdouble
  have h2 := pow_exp_integrableOn 2 hdouble
  have hexp (t : ℝ) : Real.exp (-a * t) ^ 2 = Real.exp (-(2 * a) * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have heq : (fun t : ℝ => ((c + t) * Real.exp (-a * t)) ^ 2) =
      fun t => c ^ 2 * Real.exp (-(2 * a) * t) +
        (2 * c) * (t * Real.exp (-(2 * a) * t)) +
          t ^ 2 * Real.exp (-(2 * a) * t) := by
    funext t
    rw [mul_pow, hexp]
    ring
  rw [heq]
  exact ((h0.const_mul (c ^ 2)).add (h1.const_mul (2 * c))).add h2

private theorem drive_half_line_envelope_integrable :
    IntegrableOn (fun t : ℝ => nativeOriginalDriveDecayConstant *
      ((1 + UniversalSinc.fixedScale + t) * Real.exp (-(1 / 2 : ℝ) * t))) (Ioi 0) :=
  (affine_exp_integrableOn (a := (1 / 2 : ℝ)) (by norm_num)
    (1 + UniversalSinc.fixedScale)).const_mul nativeOriginalDriveDecayConstant

/-- L1 membership of the literal native integer drive, independently of
any prime-field or inverse estimate. -/
theorem nativeOriginalIntegerDrive_integrable : Integrable nativeOriginalIntegerDrive := by
  have hpos : IntegrableOn nativeOriginalIntegerDrive (Ioi 0) := by
    apply drive_half_line_envelope_integrable.mono'
      nativeOriginalIntegerDrive_continuous.aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [Real.norm_eq_abs]
    calc
      _ ≤ nativeOriginalDriveDecayConstant * (1 + t + UniversalSinc.fixedScale) *
          Real.exp (-(t / 2)) := nativeOriginalIntegerDrive_decay ht.le
      _ = _ := by
        rw [show -(t / 2) = -(1 / 2 : ℝ) * t by ring]
        ring
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Iio 0)).congr_fun
    (fun t ht => (nativeOriginalIntegerDrive_zero_of_neg ht).symm) measurableSet_Iio

theorem nativeOriginalIntegerDrive_memLp_one : MemLp nativeOriginalIntegerDrive 1 volume :=
  memLp_one_iff_integrable.mpr nativeOriginalIntegerDrive_integrable

/-- Literal complex damped integer forcing for the native complex L2
operator. This is a function before it is made an equivalence class. -/
def nativeOriginalDampedIntegerDrive (epsilon t : ℝ) : ℂ :=
  ((Real.exp (-epsilon * t) * nativeOriginalIntegerDrive t : ℝ) : ℂ)

theorem nativeOriginalDampedIntegerDrive_continuous (epsilon : ℝ) :
    Continuous (nativeOriginalDampedIntegerDrive epsilon) :=
  Complex.continuous_ofReal.comp
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul
      nativeOriginalIntegerDrive_continuous)

theorem nativeOriginalDampedIntegerDrive_measurable (epsilon : ℝ) :
    Measurable (nativeOriginalDampedIntegerDrive epsilon) :=
  (nativeOriginalDampedIntegerDrive_continuous epsilon).measurable

theorem nativeOriginalDampedIntegerDrive_zero_of_neg (epsilon : ℝ) {t : ℝ} (ht : t < 0) :
    nativeOriginalDampedIntegerDrive epsilon t = 0 := by
  rw [nativeOriginalDampedIntegerDrive, nativeOriginalIntegerDrive_zero_of_neg ht,
    mul_zero, Complex.ofReal_zero]

private theorem damped_drive_norm_bound {epsilon t : ℝ}
    (hepsilon : 0 ≤ epsilon) (ht : 0 ≤ t) :
    ‖nativeOriginalDampedIntegerDrive epsilon t‖ ≤
      nativeOriginalDriveDecayConstant *
        ((1 + UniversalSinc.fixedScale + t) * Real.exp (-(1 / 2 : ℝ) * t)) := by
  rw [nativeOriginalDampedIntegerDrive, Complex.norm_real, Real.norm_eq_abs,
    abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexp : Real.exp (-epsilon * t) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hepsilon) ht)
  calc
    _ ≤ 1 * |nativeOriginalIntegerDrive t| :=
      mul_le_mul_of_nonneg_right hexp (abs_nonneg _)
    _ = |nativeOriginalIntegerDrive t| := one_mul _
    _ ≤ nativeOriginalDriveDecayConstant * (1 + t + UniversalSinc.fixedScale) *
        Real.exp (-(t / 2)) := nativeOriginalIntegerDrive_decay ht
    _ = _ := by
      rw [show -(t / 2) = -(1 / 2 : ℝ) * t by ring]
      ring

/-- The actual complex norm square is integrable on the full line, with
the polynomial exponential majorant and negative-time zero paid explicitly. -/
theorem nativeOriginalDampedIntegerDrive_norm_sq_integrable {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) :
    Integrable (fun t : ℝ => ‖nativeOriginalDampedIntegerDrive epsilon t‖ ^ 2) := by
  have hE : IntegrableOn (fun t : ℝ =>
      (nativeOriginalDriveDecayConstant *
        ((1 + UniversalSinc.fixedScale + t) * Real.exp (-(1 / 2 : ℝ) * t))) ^ 2) (Ioi 0) := by
    simpa only [mul_pow, mul_assoc] using!
      (affine_exp_sq_integrableOn (a := (1 / 2 : ℝ)) (by norm_num)
        (1 + UniversalSinc.fixedScale)).const_mul (nativeOriginalDriveDecayConstant ^ 2)
  have hpos : IntegrableOn
      (fun t : ℝ => ‖nativeOriginalDampedIntegerDrive epsilon t‖ ^ 2) (Ioi 0) := by
    apply hE.mono' ((nativeOriginalDampedIntegerDrive_continuous epsilon).norm.pow 2).aestronglyMeasurable
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : (0 : ℝ) < t := ht
    change ‖‖nativeOriginalDampedIntegerDrive epsilon t‖ ^ 2‖ ≤
      (nativeOriginalDriveDecayConstant *
        ((1 + UniversalSinc.fixedScale + t) * Real.exp (-(1 / 2 : ℝ) * t))) ^ 2
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hC := nativeOriginalDriveDecayConstant_nonneg
    have hs := UniversalSinc.fixedScale_pos.le
    have hB : 0 ≤ nativeOriginalDriveDecayConstant *
        ((1 + UniversalSinc.fixedScale + t) * Real.exp (-(1 / 2 : ℝ) * t)) :=
      mul_nonneg hC (mul_nonneg (by linarith [htpos.le]) (Real.exp_pos _).le)
    exact (sq_le_sq₀ (norm_nonneg _) hB).mpr (damped_drive_norm_bound hepsilon htpos.le)
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, hpos⟩
  exact (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Iio 0)).congr_fun
    (fun t ht => by
      change (0 : ℝ) = ‖nativeOriginalDampedIntegerDrive epsilon t‖ ^ 2
      rw [nativeOriginalDampedIntegerDrive_zero_of_neg epsilon ht, norm_zero]
      norm_num)
    measurableSet_Iio

/-- Genuine complex L2 membership for every nonnegative damping. -/
theorem nativeOriginalDampedIntegerDrive_memLp_two {epsilon : ℝ} (hepsilon : 0 ≤ epsilon) :
    MemLp (nativeOriginalDampedIntegerDrive epsilon) 2 volume :=
  (memLp_two_iff_integrable_sq_norm
    (nativeOriginalDampedIntegerDrive_continuous epsilon).aestronglyMeasurable).mpr
      (nativeOriginalDampedIntegerDrive_norm_sq_integrable hepsilon)

def nativeOriginalDampedIntegerDriveL2 (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    Lp ℂ 2 (volume : Measure ℝ) :=
  (nativeOriginalDampedIntegerDrive_memLp_two hepsilon).toLp
    (nativeOriginalDampedIntegerDrive epsilon)

theorem nativeOriginalDampedIntegerDriveL2_coeFn (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    nativeOriginalDampedIntegerDriveL2 epsilon hepsilon =ᵐ[volume]
      nativeOriginalDampedIntegerDrive epsilon :=
  (nativeOriginalDampedIntegerDrive_memLp_two hepsilon).coeFn_toLp

theorem nativeOriginalDampedIntegerDriveL2_causal (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    ∀ᵐ t : ℝ, t < 0 → nativeOriginalDampedIntegerDriveL2 epsilon hepsilon t = 0 := by
  filter_upwards [nativeOriginalDampedIntegerDriveL2_coeFn epsilon hepsilon] with t ht
  intro htneg
  rw [ht]
  exact nativeOriginalDampedIntegerDrive_zero_of_neg epsilon htneg

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeOriginalIntegerDrive_zero_of_neg
#print axioms Zeta23.CCM.nativeOriginalIntegerDrive_integrable
#print axioms Zeta23.CCM.nativeOriginalDampedIntegerDrive_norm_sq_integrable
#print axioms Zeta23.CCM.nativeOriginalDampedIntegerDrive_memLp_two
#print axioms Zeta23.CCM.nativeOriginalDampedIntegerDriveL2_causal
