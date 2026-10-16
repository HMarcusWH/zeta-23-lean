import Zeta23.CCM.OriginalSincDriveDerivative

/-!
# Source-defined decay of the actual original integer drive

The continuum contribution has already been cancelled by the two actual
weighted elementary moments. Exponential substitution in the remaining Abel
derivative integral leaves a compact integral involving the literal source
and its derivative. Its constant is defined from those functions, rather
than accepted as a decay premise. No estimate on the prime field or stable
forward input is used.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace Zeta23.CCM

private theorem drive_source_compact : HasCompactSupport nativeOriginalSource := by
  apply HasCompactSupport.intro
    (K := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale) isCompact_Icc
  exact fun x hx => nativeOriginalSource_supported x hx

private theorem drive_source_tsupport :
    tsupport nativeOriginalSource ⊆
      Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  exact hx (nativeOriginalSource_supported x hnot)

private theorem drive_source_deriv_continuous : Continuous (deriv nativeOriginalSource) :=
  (nativeOriginalSource_contDiff.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).continuous_deriv le_rfl

private theorem log_drive_deriv_zero_below {t x : ℝ}
    (hx : x < Real.exp (t - UniversalSinc.fixedScale)) :
    deriv (nativeOriginalLogDriveSummand t) x = 0 := by
  have hzero : nativeOriginalLogDriveSummand t =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.eventually_mem hx] with y hy
    exact nativeOriginalLogDriveSummand_zero_below hy
  rw [hzero.deriv_eq, deriv_const]

private theorem sqrt_exp_half (y : ℝ) :
    Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  have hsplit : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, Real.sqrt_mul_self (Real.exp_pos _).le]

/-- The exact derivative profile after both genuine changes of variables. -/
def nativeOriginalDriveDerivativeProfile (t u : ℝ) : ℝ :=
  Real.exp (-((t - u) / 2)) *
    ((1 - (t - u) / 2) * nativeOriginalSource u -
      (t - u) * deriv nativeOriginalSource u)

private theorem abs_exp_drive_deriv (t y : ℝ) :
    Real.exp y * |deriv (nativeOriginalLogDriveSummand t) (Real.exp y)| =
      |nativeOriginalDriveDerivativeProfile t (t - y)| := by
  calc
    _ = |Real.exp y * deriv (nativeOriginalLogDriveSummand t) (Real.exp y)| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos y)]
    _ = _ := by
      rw [nativeOriginalLogDriveSummand_deriv_exp, abs_div, sqrt_exp_half,
        abs_of_pos (Real.exp_pos _), div_eq_mul_inv, ← Real.exp_neg]
      unfold nativeOriginalDriveDerivativeProfile
      rw [sub_sub_cancel, abs_mul, abs_of_pos (Real.exp_pos _)]
      ring

/-- The full absolute derivative integral is a compact original-source
integral. The zero neighborhood at x = 0 is supplied by the actual source. -/
theorem nativeOriginalLogDriveSummand_derivative_integral_eq (t : ℝ) :
    (∫ x : ℝ, |deriv (nativeOriginalLogDriveSummand t) x|) =
      ∫ u : ℝ, |nativeOriginalDriveDerivativeProfile t u| := by
  let a : ℝ := t - UniversalSinc.fixedScale - 1
  let D : ℝ → ℝ := fun x => |deriv (nativeOriginalLogDriveSummand t) x|
  let H : ℝ → ℝ := fun y => Real.exp y * D (Real.exp y)
  have hD : (∫ x : ℝ in Ioi (Real.exp a), D x) = ∫ x : ℝ, D x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hbelow : x < Real.exp (t - UniversalSinc.fixedScale) :=
      (le_of_not_gt hx).trans_lt (Real.exp_lt_exp.mpr (by dsimp [a]; linarith))
    dsimp only [D]
    rw [log_drive_deriv_zero_below hbelow, abs_zero]
  have hH : (∫ y : ℝ in Ioi a, H y) = ∫ y : ℝ, H y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hbelow : Real.exp y < Real.exp (t - UniversalSinc.fixedScale) := by
      apply Real.exp_lt_exp.mpr
      have hyle : y ≤ a := le_of_not_gt hy
      dsimp only [a] at hyle
      linarith
    dsimp only [H, D]
    rw [log_drive_deriv_zero_below hbelow, abs_zero, mul_zero]
  have hsub := integral_comp_exp_Ioi D a
  change (∫ y : ℝ in Ioi a, H y) = ∫ x : ℝ in Ioi (Real.exp a), D x at hsub
  rw [hD, hH] at hsub
  change (∫ x : ℝ, D x) = _
  rw [← hsub]
  have hreflect : (∫ y : ℝ, H y) = ∫ u : ℝ, H (t - u) :=
    (integral_sub_left_eq_self H volume t).symm
  rw [hreflect]
  apply integral_congr_ae
  filter_upwards with u
  dsimp only [H, D]
  rw [abs_exp_drive_deriv, sub_sub_cancel]

/-- A finite constant determined by the exact original source and its
derivative. The integral is genuinely integrable by compact smoothness. -/
def nativeOriginalDriveDecayConstant : ℝ :=
  Real.exp (UniversalSinc.fixedScale / 2) *
    ∫ u : ℝ, |nativeOriginalSource u| + |deriv nativeOriginalSource u|

theorem nativeOriginalDriveSourceNorm_integrable :
    Integrable (fun u : ℝ => |nativeOriginalSource u| + |deriv nativeOriginalSource u|) :=
  (nativeOriginalSource_integrable.abs).add
    ((drive_source_deriv_continuous.integrable_of_hasCompactSupport drive_source_compact.deriv).abs)

theorem nativeOriginalDriveDerivativeProfile_integrable (t : ℝ) :
    Integrable (nativeOriginalDriveDerivativeProfile t) := by
  have harg : Continuous (fun u : ℝ => t - u) := continuous_const.sub continuous_id
  have hcoef : Continuous (fun u : ℝ => 1 - (t - u) / 2) :=
    continuous_const.sub (harg.div_const 2)
  have hE : Continuous (fun u : ℝ => Real.exp (-((t - u) / 2))) := by fun_prop
  unfold nativeOriginalDriveDerivativeProfile
  exact (hE.mul ((hcoef.mul nativeOriginalSource_contDiff.continuous).sub
    (harg.mul drive_source_deriv_continuous))).integrable_of_hasCompactSupport
      ((drive_source_compact.mul_left.sub drive_source_compact.deriv.mul_left).mul_left)

theorem nativeOriginalDriveDecayConstant_nonneg : 0 ≤ nativeOriginalDriveDecayConstant := by
  apply mul_nonneg (Real.exp_pos _).le
  exact integral_nonneg (fun u => add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The source-defined constant is strictly positive, using the actual
mass 1/16 rather than a pointwise sample of the source. -/
theorem nativeOriginalDriveDecayConstant_pos : 0 < nativeOriginalDriveDecayConstant := by
  have hmass := norm_integral_le_integral_norm (μ := volume) nativeOriginalSource
  simp only [nativeOriginalSource_integral, Real.norm_eq_abs] at hmass
  norm_num at hmass
  have hsum := integral_mono nativeOriginalSource_integrable.abs
    nativeOriginalDriveSourceNorm_integrable
    (fun u => le_add_of_nonneg_right (abs_nonneg (deriv nativeOriginalSource u)))
  unfold nativeOriginalDriveDecayConstant
  exact mul_pos (Real.exp_pos _)
    ((by norm_num : (0 : ℝ) < 1 / 16).trans_le (hmass.trans hsum))

private theorem drive_profile_bound {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    |nativeOriginalDriveDerivativeProfile t u| ≤
      (Real.exp (UniversalSinc.fixedScale / 2) *
        (1 + t + UniversalSinc.fixedScale) * Real.exp (-(t / 2))) *
          (|nativeOriginalSource u| + |deriv nativeOriginalSource u|) := by
  by_cases hu : u ∈ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale
  · have hs : 0 ≤ UniversalSinc.fixedScale := UniversalSinc.fixedScale_pos.le
    have habs : |t - u| ≤ t + UniversalSinc.fixedScale := by
      apply abs_le.mpr
      constructor <;> linarith [hu.1, hu.2]
    have hcoeff : |1 - (t - u) / 2| ≤ 1 + t + UniversalSinc.fixedScale := by
      have h := abs_sub (1 : ℝ) ((t - u) / 2)
      rw [abs_one, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
      linarith
    have habs' : |t - u| ≤ 1 + t + UniversalSinc.fixedScale := by linarith
    have hC : 0 ≤ 1 + t + UniversalSinc.fixedScale := by linarith
    have hcore :
        |(1 - (t - u) / 2) * nativeOriginalSource u -
          (t - u) * deriv nativeOriginalSource u| ≤
            (1 + t + UniversalSinc.fixedScale) *
              (|nativeOriginalSource u| + |deriv nativeOriginalSource u|) := by
      calc
        _ ≤ |(1 - (t - u) / 2) * nativeOriginalSource u| +
            |(t - u) * deriv nativeOriginalSource u| := abs_sub _ _
        _ = |1 - (t - u) / 2| * |nativeOriginalSource u| +
            |t - u| * |deriv nativeOriginalSource u| := by rw [abs_mul, abs_mul]
        _ ≤ (1 + t + UniversalSinc.fixedScale) * |nativeOriginalSource u| +
            (1 + t + UniversalSinc.fixedScale) * |deriv nativeOriginalSource u| :=
          add_le_add (mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _))
            (mul_le_mul_of_nonneg_right habs' (abs_nonneg _))
        _ = _ := by ring
    have hexp : Real.exp (-((t - u) / 2)) ≤
        Real.exp (-(t / 2)) * Real.exp (UniversalSinc.fixedScale / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hu.2]
    unfold nativeOriginalDriveDerivativeProfile
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-((t - u) / 2)) *
          ((1 + t + UniversalSinc.fixedScale) *
            (|nativeOriginalSource u| + |deriv nativeOriginalSource u|)) :=
        mul_le_mul_of_nonneg_left hcore (Real.exp_pos _).le
      _ ≤ (Real.exp (-(t / 2)) * Real.exp (UniversalSinc.fixedScale / 2)) *
          ((1 + t + UniversalSinc.fixedScale) *
            (|nativeOriginalSource u| + |deriv nativeOriginalSource u|)) :=
        mul_le_mul_of_nonneg_right hexp
          (mul_nonneg hC (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      _ = _ := by ring
  · have hj := nativeOriginalSource_supported u hu
    have hj' : deriv nativeOriginalSource u = 0 :=
      deriv_of_notMem_tsupport (fun h => hu (drive_source_tsupport h))
    simp only [nativeOriginalDriveDerivativeProfile, hj, hj', mul_zero, sub_zero,
      abs_zero, zero_add, mul_zero, le_refl]

/-- The actual source-defined derivative budget, after the exact Jacobian
and all support restrictions have been paid. -/
theorem nativeOriginalLogDriveSummand_derivative_integral_le {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, |deriv (nativeOriginalLogDriveSummand t) x|) ≤
      nativeOriginalDriveDecayConstant * (1 + t + UniversalSinc.fixedScale) *
        Real.exp (-(t / 2)) := by
  rw [nativeOriginalLogDriveSummand_derivative_integral_eq]
  have h := integral_mono (nativeOriginalDriveDerivativeProfile_integrable t).abs
    (nativeOriginalDriveSourceNorm_integrable.const_mul
      (Real.exp (UniversalSinc.fixedScale / 2) *
        (1 + t + UniversalSinc.fixedScale) * Real.exp (-(t / 2))))
    (drive_profile_bound ht)
  rw [integral_const_mul] at h
  calc
    _ ≤ _ := h
    _ = _ := by unfold nativeOriginalDriveDecayConstant; ring

/-- The literal unchanged integer drive decays exponentially; neither a
decay certificate nor any prime-field bound is a caller hypothesis. -/
theorem nativeOriginalIntegerDrive_decay {t : ℝ} (ht : 0 ≤ t) :
    |nativeOriginalIntegerDrive t| ≤
      nativeOriginalDriveDecayConstant * (1 + t + UniversalSinc.fixedScale) *
        Real.exp (-(t / 2)) := by
  have hDint : Integrable (fun x : ℝ => |deriv (nativeOriginalLogDriveSummand t) x|) :=
    (((nativeOriginalLogDriveSummand_contDiff t).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).continuous_deriv le_rfl).abs
      |>.integrable_of_hasCompactSupport (nativeOriginalLogDriveSummand_hasCompactSupport t).deriv.abs
  calc
    _ ≤ ∫ x : ℝ in Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1)),
        |deriv (nativeOriginalLogDriveSummand t) x| :=
      nativeOriginalIntegerDrive_abs_le_summand_derivative t
    _ ≤ ∫ x : ℝ, |deriv (nativeOriginalLogDriveSummand t) x| :=
      setIntegral_le_integral hDint (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
    _ ≤ _ := nativeOriginalLogDriveSummand_derivative_integral_le ht

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_derivative_integral_eq
#print axioms Zeta23.CCM.nativeOriginalDriveSourceNorm_integrable
#print axioms Zeta23.CCM.nativeOriginalDriveDerivativeProfile_integrable
#print axioms Zeta23.CCM.nativeOriginalDriveDecayConstant_pos
#print axioms Zeta23.CCM.nativeOriginalLogDriveSummand_derivative_integral_le
#print axioms Zeta23.CCM.nativeOriginalIntegerDrive_decay
