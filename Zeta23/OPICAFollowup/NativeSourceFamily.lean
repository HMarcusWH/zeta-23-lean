import Zeta23.CCM.OriginalSincNativeSource
import Zeta23.CCM.UniversalSincInverseGevreyBounds
import Zeta23.CCM.OriginalSincWeightedPoleMoments
import Zeta23.CCM.NativeIntegerPrimeConvolution

/-! The literal differential source family and its physical lattice histories.
The source is the parent's one-copy `j`; no source data are caller premises. -/

noncomputable section
open Set MeasureTheory Filter Finset
open scoped Topology BigOperators
namespace Zeta23.OPICAFollowup
open Zeta23.CCM

def sourceDifferential (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => deriv (deriv f) x - (1/4:ℝ)*f x

def sourceOrderFamily : ℕ → ℝ → ℝ
  | 0 => nativeOriginalSource
  | d+1 => sourceDifferential (sourceOrderFamily d)

def primeFieldFamily (d : ℕ) : ℝ → ℝ := nativePrimeField (sourceOrderFamily d)

def integerDriveFamily (d : ℕ) : ℝ → ℝ := nativeIntegerDriveField (sourceOrderFamily d)

def forwardKernel (d : ℕ) : ℕ → ℝ → ℝ
  | 0 => integerDriveFamily d
  | ell+1 => nativeIntegerTranslateAction (forwardKernel d ell)

def nativeCausalGap : ℝ := Real.log 2-UniversalSinc.fixedScale

@[simp] theorem sourceFamily_succ (d : ℕ) :
    sourceOrderFamily (d+1) = sourceDifferential (sourceOrderFamily d) := rfl

theorem sourceFamily_zero_eq_original :
    sourceOrderFamily 0 = nativeOriginalSource ∧
    primeFieldFamily 0 = nativeOriginalPrimeField ∧
    integerDriveFamily 0 = nativeOriginalIntegerDrive := ⟨rfl,rfl,rfl⟩

theorem sourceFamily_contDiff (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (sourceOrderFamily d) := by
  induction d with
  | zero => exact nativeOriginalSource_contDiff
  | succ d ih =>
    have hd := (contDiff_infty_iff_deriv.mp ih).2
    exact (contDiff_infty_iff_deriv.mp hd).2.sub (contDiff_const.mul ih)

theorem supported_deriv {s : ℝ} {f : ℝ → ℝ} (hf : NativeSourceSupported s f) :
    NativeSourceSupported s (deriv f) := by
  intro x hx
  have heq : f =ᶠ[𝓝 x] fun _ : ℝ => 0 := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    exact hf y hy
  rw [heq.deriv_eq, deriv_const]

theorem sourceFamily_supported (d : ℕ) :
    NativeSourceSupported UniversalSinc.fixedScale (sourceOrderFamily d) := by
  induction d with
  | zero => exact nativeOriginalSource_supported
  | succ d ih =>
    intro x hx
    simp only [sourceOrderFamily, sourceDifferential, supported_deriv (supported_deriv ih) x hx,
      ih x hx, mul_zero, sub_zero]

theorem sourceFamily_hasCompactSupport (d : ℕ) : HasCompactSupport (sourceOrderFamily d) := by
  apply HasCompactSupport.intro (K := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale)
    isCompact_Icc
  exact sourceFamily_supported d

theorem sourceFamily_integrable (d : ℕ) : Integrable (sourceOrderFamily d) :=
  (sourceFamily_contDiff d).continuous.integrable_of_hasCompactSupport
    (sourceFamily_hasCompactSupport d)

theorem nativeCausalGap_pos : 0 < nativeCausalGap :=
  native_frozenSource_causal_gap_pos

theorem primeFieldFamily_zero_before (d : ℕ) {t : ℝ} (ht : t < nativeCausalGap) :
    primeFieldFamily d t = 0 :=
  nativePrimeField_zero_before_firstPrime (sourceFamily_supported d) ht

theorem integerDriveFamily_zero_before (d : ℕ) {t : ℝ} (ht : t < nativeCausalGap) :
    integerDriveFamily d t = 0 :=
  nativeIntegerDriveField_zero_before_firstPrime (sourceFamily_supported d) ht

theorem primeFieldFamily_history (d : ℕ) {T t : ℝ} (ht : t ≤ T) :
    primeFieldFamily d t =
      ∑ n ∈ range (nativeHistoryCutoff UniversalSinc.fixedScale T+1),
        nativePrimeCoefficient n*sourceOrderFamily d (t-Real.log n) :=
  nativePrimeField_eq_history_sum (sourceFamily_supported d) ht

theorem integerDriveFamily_history (d : ℕ) {T t : ℝ} (ht : t ≤ T) :
    integerDriveFamily d t =
      ∑ n ∈ range (nativeHistoryCutoff UniversalSinc.fixedScale T+1),
        nativeIntegerDriveCoefficient n*sourceOrderFamily d (t-Real.log n) :=
  nativeIntegerDriveField_eq_history_sum (sourceFamily_supported d) ht

theorem primeFieldFamily_contDiff (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (primeFieldFamily d) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ =>
      ∑ n ∈ range (nativeHistoryCutoff UniversalSinc.fixedScale (t+1)+1),
        nativePrimeCoefficient n*sourceOrderFamily d (u-Real.log n)) := by
    have := sourceFamily_contDiff d
    fun_prop
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [eventually_le_nhds (show t<t+1 by linarith)] with u hu
  exact primeFieldFamily_history d hu

theorem integerDriveFamily_contDiff (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (integerDriveFamily d) := by
  apply contDiff_iff_contDiffAt.mpr
  intro t
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun u : ℝ =>
      ∑ n ∈ range (nativeHistoryCutoff UniversalSinc.fixedScale (t+1)+1),
        nativeIntegerDriveCoefficient n*sourceOrderFamily d (u-Real.log n)) := by
    have := sourceFamily_contDiff d
    fun_prop
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [eventually_le_nhds (show t<t+1 by linarith)] with u hu
  exact integerDriveFamily_history d hu

theorem integerTranslate_zero_before {f : ℝ → ℝ}
    (hf : ∀ t < nativeCausalGap, f t = 0) {t : ℝ} (ht : t < nativeCausalGap) :
    nativeIntegerTranslateAction f t = 0 := by
  unfold nativeIntegerTranslateAction
  apply Eq.trans (tsum_congr ?_) (tsum_zero)
  intro n
  by_cases hn : n=0
  · subst n
    simp [nativeIntegerCoefficient]
  · have hlog : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
    rw [hf _ (by linarith), mul_zero]

theorem forwardKernel_zero_before (d ell : ℕ) {t : ℝ} (ht : t < nativeCausalGap) :
    forwardKernel d ell t = 0 := by
  induction ell generalizing t with
  | zero => exact integerDriveFamily_zero_before d ht
  | succ ell ih =>
    exact integerTranslate_zero_before (fun _ hs => ih hs) ht

/-- The actual elementary weighted moments; `k` is a polynomial degree. -/
def sourceWeightedMoment (k : ℕ) (r : ℝ) (f : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, x^k*Real.exp (r*x)*f x

theorem sourceWeightedMoment_integrable {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (k : ℕ) (r : ℝ) :
    Integrable (fun x : ℝ => x^k*Real.exp (r*x)*f x) := by
  exact ((continuous_id.pow k |>.mul (by fun_prop)).mul hf).integrable_of_hasCompactSupport hc.mul_left

theorem sourceWeightedMoment_deriv {f : ℝ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) (k : ℕ) (r : ℝ) :
    sourceWeightedMoment k r (deriv f) =
      -(k:ℝ)*sourceWeightedMoment (k-1) r f-r*sourceWeightedMoment k r f := by
  let w : ℝ → ℝ := fun x => x^k*Real.exp (r*x)
  let w' : ℝ → ℝ := fun x => (k:ℝ)*x^(k-1)*Real.exp (r*x)+r*(x^k*Real.exp (r*x))
  have hw : ∀ x, HasDerivAt w (w' x) x := by
    intro x
    have h := ((hasDerivAt_id x).pow k).mul (((hasDerivAt_id x).const_mul r).exp)
    convert h using 1 <;> first | rfl | (dsimp [w,w']; ring)
  have hwc : Continuous w := by dsimp [w]; fun_prop
  have hw'c : Continuous w' := by dsimp [w']; fun_prop
  have hD := hf.continuous_deriv le_rfl
  have key := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (u' := deriv f) (v := w) (v' := w')
    (fun x _ => (hf.differentiable (by norm_num) x).hasDerivAt) (fun x _ => hw x)
    ((hf.continuous.mul hw'c).integrable_of_hasCompactSupport hc.mul_right)
    ((hD.mul hwc).integrable_of_hasCompactSupport hc.deriv.mul_right)
    ((hf.continuous.mul hwc).integrable_of_hasCompactSupport hc.mul_right)
  have heq : (fun x : ℝ => f x*w' x) = fun x =>
      (k:ℝ)*(x^(k-1)*Real.exp (r*x)*f x)+r*(x^k*Real.exp (r*x)*f x) := by
    funext x
    dsimp [w']
    ring
  have heq' : (fun x : ℝ => deriv f x*w x) =
      fun x => x^k*Real.exp (r*x)*deriv f x := by funext x; dsimp [w]; ring
  rw [heq,heq', integral_add
    ((sourceWeightedMoment_integrable hf.continuous hc (k-1) r).const_mul _)
    ((sourceWeightedMoment_integrable hf.continuous hc k r).const_mul _),
    integral_const_mul,integral_const_mul] at key
  dsimp [sourceWeightedMoment] at *
  linarith

theorem sourceWeightedMoment_differential {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hc : HasCompactSupport f) (k : ℕ) (r : ℝ) :
    sourceWeightedMoment k r (sourceDifferential f) =
      (r^2-1/4)*sourceWeightedMoment k r f+
      2*(k:ℝ)*r*sourceWeightedMoment (k-1) r f+
      (k:ℝ)*(k-1:ℕ)*sourceWeightedMoment (k-1-1) r f := by
  have hD := hf.deriv'.continuous_deriv le_rfl
  have heq : (fun x : ℝ => x^k*Real.exp (r*x)*sourceDifferential f x) =
      fun x => x^k*Real.exp (r*x)*deriv (deriv f) x-
        (1/4:ℝ)*(x^k*Real.exp (r*x)*f x) := by
    funext x; dsimp [sourceDifferential]; ring
  unfold sourceWeightedMoment
  rw [heq,integral_sub (sourceWeightedMoment_integrable hD hc.deriv.deriv k r)
    ((sourceWeightedMoment_integrable hf.continuous hc k r).const_mul _),integral_const_mul]
  change sourceWeightedMoment k r (deriv (deriv f))-(1/4:ℝ)*sourceWeightedMoment k r f = _
  rw [sourceWeightedMoment_deriv hf.deriv' hc.deriv,
    sourceWeightedMoment_deriv (hf.of_le (by norm_num)) hc,
    sourceWeightedMoment_deriv (hf.of_le (by norm_num)) hc]
  simp only [sourceWeightedMoment]
  ring

theorem sourceFamily_elementary_moments (d k : ℕ) (hk : k<d+2) :
    sourceWeightedMoment k (1/2) (sourceOrderFamily d) = 0 ∧
    sourceWeightedMoment k (-1/2) (sourceOrderFamily d) = 0 := by
  induction d generalizing k with
  | zero =>
    have hbase := nativeOriginalSource_weighted_elementary_moments
    have h01 : k=0 ∨ k=1 := by omega
    rcases h01 with rfl | rfl
    · simpa [sourceWeightedMoment,sourceOrderFamily,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
        using And.intro hbase.1 hbase.2.1
    · simpa [sourceWeightedMoment,sourceOrderFamily,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc]
        using And.intro hbase.2.2.1 hbase.2.2.2
  | succ d ih =>
    have hlow := ih (k-1) (by omega)
    have hlow' := ih (k-1-1) (by omega)
    have hsm := (sourceFamily_contDiff d).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
    constructor
    · rw [sourceFamily_succ, sourceWeightedMoment_differential hsm (sourceFamily_hasCompactSupport d),
        hlow.1,hlow'.1]
      norm_num
    · rw [sourceFamily_succ, sourceWeightedMoment_differential hsm (sourceFamily_hasCompactSupport d),
        hlow.2,hlow'.2]
      norm_num

/-- Exact support, smoothness, causal gap and all `d+2` elementary moments. -/
theorem sourceFamily_support_smooth_moments (d : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (sourceOrderFamily d) ∧
    NativeSourceSupported UniversalSinc.fixedScale (sourceOrderFamily d) ∧
    0<nativeCausalGap ∧
    (∀ t<nativeCausalGap, primeFieldFamily d t=0 ∧ integerDriveFamily d t=0) ∧
    (∀ k<d+2, sourceWeightedMoment k (1/2) (sourceOrderFamily d)=0 ∧
      sourceWeightedMoment k (-1/2) (sourceOrderFamily d)=0) :=
  ⟨sourceFamily_contDiff d,sourceFamily_supported d,nativeCausalGap_pos,
    fun _ ht => ⟨primeFieldFamily_zero_before d ht,integerDriveFamily_zero_before d ht⟩,
    fun k hk => sourceFamily_elementary_moments d k hk⟩

end Zeta23.OPICAFollowup
