import Zeta23.CCM.OriginalSincNativeSource
import Zeta23.CCM.CompactPoleConvolution

/-!
# Complex compact sources on the unchanged native lattice

A single finite cutoff works on every chosen bounded time horizon. The
finite expression is established before differentiation. None of these
local assertions assumes a global L2 norm of the native prime field.
-/

noncomputable section

open Set MeasureTheory Filter Finset
open scoped Topology

namespace Zeta23.CCM

def NativeComplexSourceSupported (s : ℝ) (f : ℝ → ℂ) : Prop :=
  tsupport f ⊆ Icc (-s) s

def nativeComplexPrimeField (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, (nativePrimeCoefficient n : ℂ) * f (t - Real.log n)

def nativeComplexIntegerDrive (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : ℕ, (nativeIntegerDriveCoefficient n : ℂ) * f (t - Real.log n)

theorem NativeComplexSourceSupported.deriv {s : ℝ} {f : ℝ → ℂ}
    (hf : NativeComplexSourceSupported s f) : NativeComplexSourceSupported s (deriv f) :=
  tsupport_deriv_subset.trans hf

theorem NativeComplexSourceSupported.hasCompactSupport {s : ℝ} {f : ℝ → ℂ}
    (hf : NativeComplexSourceSupported s f) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hf

theorem nativeComplexSourceTranslate_zero_above_history {s T t : ℝ} {f : ℝ → ℂ}
    (hf : NativeComplexSourceSupported s f) (ht : t ≤ T) {n : ℕ}
    (hn : nativeHistoryCutoff s T < n) : f (t - Real.log n) = 0 := by
  have hexp : Real.exp (T + s) < (n : ℝ) := Nat.lt_of_floor_lt hn
  have hnpos : 0 < (n : ℝ) := (Real.exp_pos _).trans hexp
  have hlog : T + s < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hexp
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hlo := (hf hmem).1
  linarith

theorem nativeComplexPrimeField_eq_history_sum {s T t : ℝ} {f : ℝ → ℂ}
    (hf : NativeComplexSourceSupported s f) (ht : t ≤ T) :
    nativeComplexPrimeField f t =
      ∑ n ∈ range (nativeHistoryCutoff s T + 1),
        (nativePrimeCoefficient n : ℂ) * f (t - Real.log n) := by
  unfold nativeComplexPrimeField
  apply tsum_eq_sum
  intro n hn
  have hcut : nativeHistoryCutoff s T < n := by
    simp only [Finset.mem_range, not_lt] at hn
    omega
  rw [nativeComplexSourceTranslate_zero_above_history hf ht hcut, mul_zero]

theorem nativeComplexIntegerDrive_eq_history_sum {s T t : ℝ} {f : ℝ → ℂ}
    (hf : NativeComplexSourceSupported s f) (ht : t ≤ T) :
    nativeComplexIntegerDrive f t =
      ∑ n ∈ range (nativeHistoryCutoff s T + 1),
        (nativeIntegerDriveCoefficient n : ℂ) * f (t - Real.log n) := by
  unfold nativeComplexIntegerDrive
  apply tsum_eq_sum
  intro n hn
  have hcut : nativeHistoryCutoff s T < n := by
    simp only [Finset.mem_range, not_lt] at hn
    omega
  rw [nativeComplexSourceTranslate_zero_above_history hf ht hcut, mul_zero]

theorem nativeComplexPrimeField_summable {s t : ℝ} {f : ℝ → ℂ}
    (hf : NativeComplexSourceSupported s f) :
    Summable (fun n : ℕ => (nativePrimeCoefficient n : ℂ) * f (t - Real.log n)) := by
  apply summable_of_ne_finset_zero (s := range (nativeHistoryCutoff s t + 1))
  intro n hn
  have hcut : nativeHistoryCutoff s t < n := by
    simp only [Finset.mem_range, not_lt] at hn
    omega
  rw [nativeComplexSourceTranslate_zero_above_history hf le_rfl hcut, mul_zero]

theorem nativeComplexPrimeField_contDiff {s : ℝ} {f : ℝ → ℂ} {m : WithTop ℕ∞}
    (hf : NativeComplexSourceSupported s f) (hfd : ContDiff ℝ m f) :
    ContDiff ℝ m (nativeComplexPrimeField f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hc : ContDiff ℝ m (fun u : ℝ =>
      ∑ n ∈ range (nativeHistoryCutoff s (t + 1) + 1),
        (nativePrimeCoefficient n : ℂ) * f (u - Real.log n)) := by fun_prop
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [eventually_le_nhds (show t < t + 1 by linarith)] with u hu
  exact nativeComplexPrimeField_eq_history_sum hf hu

theorem nativeComplexPrimeField_hasDerivAt {s : ℝ} {f : ℝ → ℂ}
    (hf : NativeComplexSourceSupported s f) (hfd : Differentiable ℝ f) (t : ℝ) :
    HasDerivAt (nativeComplexPrimeField f) (nativeComplexPrimeField (deriv f) t) t := by
  have hsum : HasDerivAt (fun u : ℝ =>
      ∑ n ∈ range (nativeHistoryCutoff s (t + 1) + 1),
        (nativePrimeCoefficient n : ℂ) * f (u - Real.log n))
      (∑ n ∈ range (nativeHistoryCutoff s (t + 1) + 1),
        (nativePrimeCoefficient n : ℂ) * deriv f (t - Real.log n)) t := by
    have hfamily : ∀ n ∈ range (nativeHistoryCutoff s (t + 1) + 1),
        HasDerivAt (fun u : ℝ => (nativePrimeCoefficient n : ℂ) * f (u - Real.log n))
          ((nativePrimeCoefficient n : ℂ) * deriv f (t - Real.log n)) t := by
      intro n hn
      have hshift : HasDerivAt (fun u : ℝ => f (u - Real.log n))
          (deriv f (t - Real.log n)) t := by
        simpa only [one_smul, Function.comp_def, id_eq] using
          ((hfd (t - Real.log n)).hasDerivAt.scomp t
          ((hasDerivAt_id t).sub_const (Real.log n)))
      exact hshift.const_mul (nativePrimeCoefficient n : ℂ)
    exact HasDerivAt.fun_sum hfamily
  rw [← nativeComplexPrimeField_eq_history_sum hf.deriv (by linarith : t ≤ t + 1)] at hsum
  apply hsum.congr_of_eventuallyEq
  filter_upwards [eventually_le_nhds (show t < t + 1 by linarith)] with u hu
  exact nativeComplexPrimeField_eq_history_sum hf hu

theorem nativeComplexIntegerDrive_contDiff {s : ℝ} {f : ℝ → ℂ} {m : WithTop ℕ∞}
    (hf : NativeComplexSourceSupported s f) (hfd : ContDiff ℝ m f) :
    ContDiff ℝ m (nativeComplexIntegerDrive f) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hc : ContDiff ℝ m (fun u : ℝ =>
      ∑ n ∈ range (nativeHistoryCutoff s (t + 1) + 1),
        (nativeIntegerDriveCoefficient n : ℂ) * f (u - Real.log n)) := by fun_prop
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [eventually_le_nhds (show t < t + 1 by linarith)] with u hu
  exact nativeComplexIntegerDrive_eq_history_sum hf hu

theorem nativeComplexPrimeField_deriv {s : ℝ} {f : ℝ → ℂ}
    (hf : NativeComplexSourceSupported s f) (hfd : Differentiable ℝ f) :
    deriv (nativeComplexPrimeField f) = nativeComplexPrimeField (deriv f) := by
  funext t
  exact (nativeComplexPrimeField_hasDerivAt hf hfd t).deriv

theorem nativeComplexPrimeField_sub_const_mul {s : ℝ} {f g : ℝ → ℂ}
    (hf : NativeComplexSourceSupported s f) (hg : NativeComplexSourceSupported s g)
    (c : ℂ) (t : ℝ) :
    nativeComplexPrimeField (fun x => f x - c * g x) t =
      nativeComplexPrimeField f t - c * nativeComplexPrimeField g t := by
  unfold nativeComplexPrimeField
  have heq : (fun n : ℕ => (nativePrimeCoefficient n : ℂ) *
      (f (t - Real.log n) - c * g (t - Real.log n))) =
      fun n : ℕ => (nativePrimeCoefficient n : ℂ) * f (t - Real.log n) -
        c * ((nativePrimeCoefficient n : ℂ) * g (t - Real.log n)) := by
    funext n
    ring
  rw [heq, (nativeComplexPrimeField_summable hf).tsum_sub
    ((nativeComplexPrimeField_summable hg).mul_left c), tsum_mul_left]

theorem nativeComplexPrimeField_poleImage {s : ℝ} {f : ℝ → ℂ}
    (hf : NativeComplexSourceSupported s f) (hfd : ContDiff ℝ 2 f) :
    universalSincDifferential (nativeComplexPrimeField f) =
      nativeComplexPrimeField (universalSincDifferential f) := by
  have hd : Differentiable ℝ f := hfd.differentiable (by norm_num)
  have hd1 : ContDiff ℝ 1 (deriv f) := hfd.deriv'
  have hdd : Differentiable ℝ (deriv f) := hd1.differentiable (by norm_num)
  funext t
  unfold universalSincDifferential
  rw [nativeComplexPrimeField_deriv hf hd, nativeComplexPrimeField_deriv hf.deriv hdd]
  exact (nativeComplexPrimeField_sub_const_mul hf.deriv.deriv hf (1 / 4) t).symm

theorem NativeComplexSourceSupported.ofReal {s : ℝ} {f : ℝ → ℝ}
    (hf : NativeSourceSupported s f) :
    NativeComplexSourceSupported s (fun t => (f t : ℂ)) := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  have hz := hf t hn
  simp [Function.mem_support, hz] at ht

theorem nativeComplexPrimeField_ofReal {s : ℝ} {f : ℝ → ℝ}
    (hf : NativeSourceSupported s f) (t : ℝ) :
    nativeComplexPrimeField (fun x => (f x : ℂ)) t = (nativePrimeField f t : ℂ) := by
  rw [nativeComplexPrimeField_eq_history_sum (NativeComplexSourceSupported.ofReal hf) (le_refl t),
    nativePrimeField_eq_history_sum hf (le_refl t)]
  push_cast
  rfl

theorem nativeComplexIntegerDrive_ofReal {s : ℝ} {f : ℝ → ℝ}
    (hf : NativeSourceSupported s f) (t : ℝ) :
    nativeComplexIntegerDrive (fun x => (f x : ℂ)) t = (nativeIntegerDriveField f t : ℂ) := by
  rw [nativeComplexIntegerDrive_eq_history_sum (NativeComplexSourceSupported.ofReal hf) (le_refl t),
    nativeIntegerDriveField_eq_history_sum hf (le_refl t)]
  push_cast
  rfl

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeComplexPrimeField_eq_history_sum
#print axioms Zeta23.CCM.nativeComplexIntegerDrive_eq_history_sum
#print axioms Zeta23.CCM.nativeComplexPrimeField_contDiff
#print axioms Zeta23.CCM.nativeComplexIntegerDrive_contDiff
#print axioms Zeta23.CCM.nativeComplexPrimeField_hasDerivAt
#print axioms Zeta23.CCM.nativeComplexPrimeField_poleImage
#print axioms Zeta23.CCM.nativeComplexPrimeField_ofReal
#print axioms Zeta23.CCM.nativeComplexIntegerDrive_ofReal
