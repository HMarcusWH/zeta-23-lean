import Zeta23.OPICAFollowup.NativeExplicitFormula
import Zeta23.OPICAFollowup.SourceVerticalBounds
import Zeta23.CCM.UniversalSincInverseGevreyBounds
import Zeta23.CCM.NativeAbelDiscrepancy
import Zeta23.CCM.OriginalSincDriveLp
import Mathlib.Tactic

/-! Uniform order costs for the literal one-copy source and its physical fields. -/

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology BigOperators FourierTransform

namespace Zeta23.OPICAFollowup
open Zeta23.CCM

def nativeSourceGevreyA : ℝ :=
  4/(Real.pi*UniversalSinc.gevreyMomentScale UniversalSinc.fixedScale^2)

def nativeSourceGevreyH : ℝ :=
  max 1 (12/UniversalSinc.gevreyMomentScale UniversalSinc.fixedScale^2)

theorem nativeSourceGevreyA_pos : 0 < nativeSourceGevreyA := by
  have h := UniversalSinc.gevreyMomentScale_pos UniversalSinc.fixedScale_pos
  unfold nativeSourceGevreyA
  positivity

theorem nativeSourceGevreyH_one_le : 1 ≤ nativeSourceGevreyH := le_max_left _ _

theorem nativeSourceGevreyH_pos : 0 < nativeSourceGevreyH :=
  zero_lt_one.trans_le nativeSourceGevreyH_one_le

private theorem nativeBox_contDiff :
    ContDiff ℝ (⊤:ℕ∞) (UniversalSinc.originalDensityComplex UniversalSinc.fixedScale) := by
  rw [← UniversalSinc.inverseCandidate_eq_originalDensityComplex UniversalSinc.fixedScale_pos]
  exact UniversalSinc.contDiff_inverseCandidate UniversalSinc.fixedScale_pos

private theorem nativeP_contDiff {f : ℝ → ℂ} (hf : ContDiff ℝ (⊤:ℕ∞) f) :
    ContDiff ℝ (⊤:ℕ∞) (universalSincDifferential f) := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  exact (contDiff_infty_iff_deriv.mp hd).2.sub (contDiff_const.mul hf)

private theorem nativeBox_iterate_contDiff (n : ℕ) :
    ContDiff ℝ (⊤:ℕ∞)
      (universalSincDifferential^[n] (UniversalSinc.originalDensityComplex UniversalSinc.fixedScale)) := by
  induction n with
  | zero => exact nativeBox_contDiff
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact nativeP_contDiff ih

private theorem nativeP_iterated_jet {f : ℝ → ℂ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (r : ℕ) (x : ℝ) :
    iteratedDeriv r (universalSincDifferential f) x =
      iteratedDeriv (r+2) f x-(1/4:ℂ)*iteratedDeriv r f x := by
  have hd := (contDiff_infty_iff_deriv.mp hf).2
  have hdd := (contDiff_infty_iff_deriv.mp hd).2
  have hr := ENat.natCast_le_of_coe_top_le_withTop le_rfl r
  have hshift : iteratedDeriv (r+2) f = iteratedDeriv r (deriv (deriv f)) := by
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
  unfold universalSincDifferential
  rw [iteratedDeriv_fun_sub ((hdd.of_le hr).contDiffAt)
    (((contDiff_const.mul hf).of_le hr).contDiffAt), iteratedDeriv_const_mul_field, hshift]

/-- A factorial budget derived from the actual original inverse integral, then
propagated through literal powers of `P`; it is not a hypothesis on the source. -/
theorem nativeBox_iterate_gevrey (n r : ℕ) (x : ℝ) :
    ‖iteratedDeriv r
      (universalSincDifferential^[n] (UniversalSinc.originalDensityComplex UniversalSinc.fixedScale)) x‖ ≤
      nativeSourceGevreyA*(nativeSourceGevreyH^2+1/4)^n*nativeSourceGevreyH^r*
        ((2*n+r).factorial:ℝ)^2 := by
  have hA := nativeSourceGevreyA_pos.le
  have hH := nativeSourceGevreyH_pos.le
  induction n generalizing r with
  | zero =>
    have h := UniversalSinc.norm_iteratedDeriv_inverseCandidate_le_gevrey
      UniversalSinc.fixedScale_pos r x
    rw [UniversalSinc.inverseCandidate_eq_originalDensityComplex UniversalSinc.fixedScale_pos] at h
    simp only [Function.iterate_zero_apply, pow_zero, mul_one, Nat.mul_zero, Nat.zero_add]
    apply h.trans
    change nativeSourceGevreyA*(_)^r*(r.factorial:ℝ)^2 ≤ _
    have hbase : 12/UniversalSinc.gevreyMomentScale UniversalSinc.fixedScale^2 ≤ nativeSourceGevreyH :=
      le_max_right _ _
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hbase r) hA) (sq_nonneg _)
  | succ n ih =>
    rw [Function.iterate_succ_apply', nativeP_iterated_jet (nativeBox_iterate_contDiff n)]
    have hfac : ((2*n+r).factorial:ℝ)^2 ≤ ((2*n+(r+2)).factorial:ℝ)^2 := by
      have h : ((2*n+r).factorial:ℝ) ≤ ((2*n+(r+2)).factorial:ℝ) := by
        exact_mod_cast Nat.factorial_le (by omega : 2*n+r ≤ 2*n+(r+2))
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
    calc
      _ ≤ ‖iteratedDeriv (r+2)
          (universalSincDifferential^[n] (UniversalSinc.originalDensityComplex UniversalSinc.fixedScale)) x‖ +
          (1/4:ℝ)*‖iteratedDeriv r
          (universalSincDifferential^[n] (UniversalSinc.originalDensityComplex UniversalSinc.fixedScale)) x‖ := by
        simpa only [norm_mul, show ‖(1/4:ℂ)‖=(1/4:ℝ) by norm_num] using norm_sub_le
          (iteratedDeriv (r+2)
            (universalSincDifferential^[n] (UniversalSinc.originalDensityComplex UniversalSinc.fixedScale)) x)
          ((1/4:ℂ)*iteratedDeriv r
            (universalSincDifferential^[n] (UniversalSinc.originalDensityComplex UniversalSinc.fixedScale)) x)
      _ ≤ nativeSourceGevreyA*(nativeSourceGevreyH^2+1/4)^n*nativeSourceGevreyH^(r+2)*
            ((2*n+(r+2)).factorial:ℝ)^2 +
          (1/4:ℝ)*(nativeSourceGevreyA*(nativeSourceGevreyH^2+1/4)^n*nativeSourceGevreyH^r*
            ((2*n+r).factorial:ℝ)^2) :=
        add_le_add (ih (r+2)) (mul_le_mul_of_nonneg_left (ih r) (by norm_num))
      _ ≤ nativeSourceGevreyA*(nativeSourceGevreyH^2+1/4)^n*nativeSourceGevreyH^(r+2)*
            ((2*n+(r+2)).factorial:ℝ)^2 +
          (1/4:ℝ)*(nativeSourceGevreyA*(nativeSourceGevreyH^2+1/4)^n*nativeSourceGevreyH^r*
            ((2*n+(r+2)).factorial:ℝ)^2) := by
        gcongr
      _ = _ := by
        rw [show 2*(n+1)+r=2*n+(r+2) by omega, pow_succ, pow_add]
        ring

private theorem native_real_iteratedDeriv_complex {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤:ℕ∞) f) (r : ℕ) :
    iteratedDeriv r (fun x : ℝ => (f x:ℂ)) =
      fun x : ℝ => Complex.ofReal (iteratedDeriv r f x) := by
  induction r with
  | zero => rfl
  | succ r ih =>
    rw [iteratedDeriv_succ, ih]
    simpa only [iteratedDeriv_succ] using complexify_deriv
      (hf.differentiable_iteratedDeriv r (by
        exact_mod_cast (show (r:ℕ∞)<⊤ from WithTop.coe_lt_top r)))

/-- All derivative orders are controlled by a single source-fixed Gevrey budget. -/
theorem sourceFamily_iteratedDeriv_gevrey (d k : ℕ) (x : ℝ) :
    |iteratedDeriv k (sourceOrderFamily d) x| ≤
      nativeSourceGevreyA*(nativeSourceGevreyH^2+1/4)^(d+2)*nativeSourceGevreyH^k*
        ((2*(d+2)+k).factorial:ℝ)^2 := by
  have h := nativeBox_iterate_gevrey (d+2) k x
  rw [← sourceFamily_complex_eq_iterated_original d,
    native_real_iteratedDeriv_complex (sourceFamily_contDiff d)] at h
  simpa only [Complex.norm_real, Real.norm_eq_abs] using h

def nativeSourceRawBudget (d : ℕ) : ℝ :=
  (max 1 nativeSourceGevreyA)*nativeSourceGevreyH^2*
    (nativeSourceGevreyH^2+1/4)^(d+2)*((2*d+6).factorial:ℝ)^2

theorem nativeSourceRawBudget_one_le (d : ℕ) : 1 ≤ nativeSourceRawBudget d := by
  unfold nativeSourceRawBudget
  have hfac : (1:ℝ) ≤ ((2*d+6).factorial:ℝ) := by
    exact_mod_cast (show 1 ≤ (2*d+6).factorial from Nat.factorial_pos _)
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (one_le_pow₀ nativeSourceGevreyH_one_le))
      (one_le_pow₀ (by nlinarith [nativeSourceGevreyH_one_le, sq_nonneg nativeSourceGevreyH])))
    (one_le_pow₀ hfac)

theorem sourceFamily_jet_le_rawBudget (d k : ℕ) (hk : k ≤ 2) (x : ℝ) :
    |iteratedDeriv k (sourceOrderFamily d) x| ≤ nativeSourceRawBudget d := by
  have h := sourceFamily_iteratedDeriv_gevrey d k x
  have hpow : nativeSourceGevreyH^k ≤ nativeSourceGevreyH^2 :=
    pow_le_pow_right₀ nativeSourceGevreyH_one_le hk
  have hfac : ((2*(d+2)+k).factorial:ℝ)^2 ≤ ((2*d+6).factorial:ℝ)^2 := by
    have hfac₀ : ((2*(d+2)+k).factorial:ℝ) ≤ ((2*d+6).factorial:ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega : 2*(d+2)+k ≤ 2*d+6)
    exact pow_le_pow_left₀ (Nat.cast_nonneg _) hfac₀ 2
  apply h.trans
  unfold nativeSourceRawBudget
  have hA := nativeSourceGevreyA_pos.le
  have hH := nativeSourceGevreyH_pos.le
  calc
    _ ≤ (max 1 nativeSourceGevreyA)*(nativeSourceGevreyH^2+1/4)^(d+2)*nativeSourceGevreyH^2*
        ((2*d+6).factorial:ℝ)^2 := by gcongr; exact le_max_right _ _
    _ = _ := by ring

theorem sourceFamily_jet_supported (d k : ℕ) :
    NativeSourceSupported UniversalSinc.fixedScale (iteratedDeriv k (sourceOrderFamily d)) := by
  induction k with
  | zero => exact sourceFamily_supported d
  | succ k ih => simpa only [iteratedDeriv_succ] using supported_deriv ih

theorem sourceFamily_jet_hasCompactSupport (d k : ℕ) :
    HasCompactSupport (iteratedDeriv k (sourceOrderFamily d)) := by
  apply HasCompactSupport.intro
    (K := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale) isCompact_Icc
  exact fun x hx => sourceFamily_jet_supported d k x hx

theorem sourceFamily_jet_integrable (d k : ℕ) :
    Integrable (iteratedDeriv k (sourceOrderFamily d)) :=
  ((sourceFamily_contDiff d).continuous_iteratedDeriv k
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl k)).integrable_of_hasCompactSupport
      (sourceFamily_jet_hasCompactSupport d k)

theorem sourceFamily_jet_L1_le_rawBudget (d k : ℕ) (hk : k ≤ 2) :
    (∫ x : ℝ, |iteratedDeriv k (sourceOrderFamily d) x|) ≤
      (2*UniversalSinc.fixedScale)*nativeSourceRawBudget d := by
  have hfi := (sourceFamily_jet_integrable d k).abs
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale) (by
      intro x hx
      rw [sourceFamily_jet_supported d k x hx, abs_zero])]
  calc
    _ ≤ ∫ x : ℝ in Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale,
        nativeSourceRawBudget d := by
      apply integral_mono_ae hfi.restrict (continuous_const.integrableOn_Icc)
      filter_upwards with x
      exact sourceFamily_jet_le_rawBudget d k hk x
    _ = _ := by
      rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith [UniversalSinc.fixedScale_pos])]
      simp only [smul_eq_mul]
      ring

/-- Fixed multiplicative constants and the actual affine factorial order are
absorbed into one cost constant, independently of the future source order. -/
theorem affine_factorial_uniform_log_cost {A B : ℝ} (hA : 1 ≤ A) (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ,
      Real.log (1+A*B^(d+2)*((2*d+6).factorial:ℝ)^2) ≤
        C*((d:ℝ)+1)*Real.log ((d:ℝ)+2) := by
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hq : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let M : ℝ := Real.log (2*A)+2*Real.log B+12*Real.log 8
  have hM : 0 ≤ M := by
    dsimp [M]
    positivity [Real.log_nonneg (by nlinarith : 1 ≤ 2*A), Real.log_nonneg hB]
  refine ⟨M/Real.log 2+12, by positivity, ?_⟩
  intro d
  let n : ℝ := (d:ℝ)+1
  let l : ℝ := Real.log ((d:ℝ)+2)
  let f : ℝ := ((2*d+6).factorial:ℝ)
  have hn : 1 ≤ n := by dsimp [n]; linarith [show (0:ℝ)≤d from Nat.cast_nonneg d]
  have hl : Real.log 2 ≤ l := Real.log_le_log (by norm_num)
    (by linarith [show (0:ℝ)≤d from Nat.cast_nonneg d])
  have hl₀ : 0 ≤ l := hq.le.trans hl
  have hfpos : 0 < f := by dsimp [f]; exact_mod_cast Nat.factorial_pos _
  have hfac : Real.log f ≤ (6*n)*(Real.log 8+l) := by
    have hb : f ≤ ((2*d+6:ℕ):ℝ)^(2*d+6) := by dsimp [f]; exact_mod_cast Nat.factorial_le_pow _
    have hlog := Real.log_le_log hfpos hb
    rw [Real.log_pow] at hlog
    have harg : (((2*d+6:ℕ):ℝ)) ≤ 8*((d:ℝ)+2) := by push_cast; nlinarith
    have hlog₂ := Real.log_le_log (by positivity : (0:ℝ)<((2*d+6:ℕ):ℝ)) harg
    rw [Real.log_mul (by norm_num : (8:ℝ)≠0) (by positivity : (d:ℝ)+2≠0)] at hlog₂
    have hm : (((2*d+6:ℕ):ℝ)) ≤ 6*n := by dsimp [n]; push_cast; nlinarith
    exact hlog.trans (mul_le_mul hm hlog₂
      (Real.log_nonneg (by exact_mod_cast (show 1≤2*d+6 by omega))) (by linarith))
  have hraw₁ : 1 ≤ A*B^(d+2)*f^2 :=
    one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le hA (one_le_pow₀ hB))
      (one_le_pow₀ (by dsimp [f]; exact_mod_cast
        (show 1 ≤ (2*d+6).factorial from Nat.factorial_pos _)))
  have hlog₀ : Real.log (1+A*B^(d+2)*f^2) ≤
      Real.log (2*A)+(d+2:ℕ)*Real.log B+2*Real.log f := by
    have h := Real.log_le_log (by positivity : 0<1+A*B^(d+2)*f^2)
      (show 1+A*B^(d+2)*f^2 ≤ 2*(A*B^(d+2)*f^2) by linarith)
    convert h using 1
    rw [Real.log_mul (by norm_num : (2:ℝ)≠0) (by positivity : A*B^(d+2)*f^2≠0),
      Real.log_mul (by positivity : A*B^(d+2)≠0) (by positivity : f^2≠0),
      Real.log_mul hApos.ne' (pow_pos hBpos _).ne', Real.log_pow, Real.log_pow,
      Real.log_mul (by norm_num : (2:ℝ)≠0) hApos.ne']
    ring
  have hfixed : M ≤ (M/Real.log 2)*l := by
    have h := mul_le_mul_of_nonneg_left hl (div_nonneg hM hq.le)
    simpa only [div_mul_cancel₀ M hq.ne'] using h
  have hfixedn := mul_le_mul_of_nonneg_left hfixed (show 0≤n by linarith)
  have hlogA : 0 ≤ Real.log (2*A) := Real.log_nonneg (by nlinarith)
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  change Real.log (1+A*B^(d+2)*f^2) ≤ (M/Real.log 2+12)*n*l
  have hd : ((d+2:ℕ):ℝ) ≤ 2*n := by dsimp [n]; push_cast; linarith
  have hb := mul_le_mul_of_nonneg_right hd hlogB
  have ha := mul_le_mul_of_nonneg_right hn hlogA
  have hpre : Real.log (1+A*B^(d+2)*f^2) ≤ n*M+12*n*l := by
    dsimp [M]
    nlinarith
  nlinarith


/-- The actual negative elementary moments consumed by the continuum integral. -/
private theorem uniform_source_negative_elementary_moments (d : ℕ) :
    (∫ u : ℝ, Real.exp (-u/2)*sourceOrderFamily d u) = 0 ∧
    (∫ u : ℝ, u*Real.exp (-u/2)*sourceOrderFamily d u) = 0 := by
  constructor
  · simpa [sourceWeightedMoment,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using
      (sourceFamily_elementary_moments d 0 (by omega)).2
  · simpa [sourceWeightedMoment,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using
      (sourceFamily_elementary_moments d 1 (by omega)).2

/- The following Abel, substitution and derivative proofs specialize the same
P0 algorithms to each actual source order. Every continuum cancellation is
supplied by the independently proved actual moments above. -/


def uniform_nativeOrderLogDriveSummand (d : ℕ) (t x : ℝ) : ℝ :=
  if 0 < x then Real.log x / Real.sqrt x *
    (sourceOrderFamily d) (t - Real.log x) else 0

theorem uniform_nativeOrderLogDriveSummand_zero_below (d : ℕ) {t x : ℝ}
    (hx : x < Real.exp (t - UniversalSinc.fixedScale)) :
    uniform_nativeOrderLogDriveSummand d t x = 0 := by
  unfold uniform_nativeOrderLogDriveSummand
  split_ifs with hpos
  · have hlog : Real.log x < t - UniversalSinc.fixedScale :=
      (Real.log_lt_iff_lt_exp hpos).mpr hx
    have hj : (sourceOrderFamily d) (t - Real.log x) = 0 := by
      apply (sourceFamily_supported d)
      intro hm
      linarith [hm.2]
    rw [hj, mul_zero]
  · rfl

theorem uniform_nativeOrderLogDriveSummand_zero_above (d : ℕ) {t x : ℝ}
    (hx : Real.exp (t + UniversalSinc.fixedScale) < x) :
    uniform_nativeOrderLogDriveSummand d t x = 0 := by
  have hpos : 0 < x := (Real.exp_pos _).trans hx
  have hlog : t + UniversalSinc.fixedScale < Real.log x :=
    (Real.lt_log_iff_exp_lt hpos).mpr hx
  unfold uniform_nativeOrderLogDriveSummand
  rw [if_pos hpos]
  have hj : (sourceOrderFamily d) (t - Real.log x) = 0 := by
    apply (sourceFamily_supported d)
    intro hm
    linarith [hm.1]
  rw [hj, mul_zero]

theorem uniform_nativeOrderLogDriveSummand_contDiff (d : ℕ) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (uniform_nativeOrderLogDriveSummand d t) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : 0 < x
  · have hlog := (contDiffAt_id : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => x) x).log hx.ne'
    have hroot := (contDiffAt_id : ContDiffAt ℝ (⊤ : ℕ∞) (fun x : ℝ => x) x).sqrt hx.ne'
    have hf : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : ℝ => Real.log y / Real.sqrt y *
          (sourceOrderFamily d) (t - Real.log y)) x :=
      (hlog.div hroot (Real.sqrt_pos.mpr hx).ne').mul
        ((sourceFamily_contDiff d).contDiffAt.comp x (contDiffAt_const.sub hlog))
    apply hf.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioi.eventually_mem hx] with y hy
    exact if_pos hy
  · have hbound : x < Real.exp (t - UniversalSinc.fixedScale) :=
      lt_of_le_of_lt (le_of_not_gt hx) (Real.exp_pos _)
    apply (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [isOpen_Iio.eventually_mem hbound] with y hy
    exact uniform_nativeOrderLogDriveSummand_zero_below d hy

theorem uniform_nativeOrderLogDriveSummand_hasCompactSupport (d : ℕ) (t : ℝ) :
    HasCompactSupport (uniform_nativeOrderLogDriveSummand d t) := by
  apply HasCompactSupport.intro
    (K := Icc (Real.exp (t - UniversalSinc.fixedScale))
      (Real.exp (t + UniversalSinc.fixedScale))) isCompact_Icc
  intro x hx
  by_cases hlow : x < Real.exp (t - UniversalSinc.fixedScale)
  · exact uniform_nativeOrderLogDriveSummand_zero_below d hlow
  · apply uniform_nativeOrderLogDriveSummand_zero_above d
    exact lt_of_not_ge (fun hh => hx ⟨le_of_not_gt hlow, hh⟩)

theorem uniform_nativeOrderLogDriveSummand_at_nat (d : ℕ) (t : ℝ) (n : ℕ) :
    uniform_nativeOrderLogDriveSummand d t n =
      nativeIntegerDriveCoefficient n * (sourceOrderFamily d) (t - Real.log n) := by
  by_cases hn : n = 0
  · subst n
    simp [uniform_nativeOrderLogDriveSummand, nativeIntegerDriveCoefficient]
  · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    simp only [uniform_nativeOrderLogDriveSummand, if_pos hnpos, nativeIntegerDriveCoefficient]

/-- The inclusive integer sum in Abel's formula is the actual original U,
with a unit upper collar ensuring the upper boundary vanishes. -/
theorem uniform_nativeOrderIntegerDrive_eq_abel_sum (d : ℕ) (t : ℝ) :
    (integerDriveFamily d) t =
      ∑ n ∈ Finset.Icc 0 ⌊Real.exp (t + UniversalSinc.fixedScale + 1)⌋₊,
        uniform_nativeOrderLogDriveSummand d t n := by
  rw [integerDriveFamily_history d (T := t + 1) (by linarith)]
  have htime : t + 1 + UniversalSinc.fixedScale = t + UniversalSinc.fixedScale + 1 := by ring
  unfold nativeHistoryCutoff
  rw [htime]
  have hset (N : ℕ) : Finset.range (N + 1) = Finset.Icc 0 N := by
    ext n
    simp only [Finset.mem_range, Finset.mem_Icc, Nat.zero_le, true_and]
    omega
  rw [hset]
  apply Finset.sum_congr rfl
  intro n hn
  exact (uniform_nativeOrderLogDriveSummand_at_nat d t n).symm

theorem uniform_nativeOrderIntegerDrive_abel_discrepancy_bound (d : ℕ) (t : ℝ) :
    |(integerDriveFamily d) t -
      ∫ x : ℝ in Set.Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1)),
        uniform_nativeOrderLogDriveSummand d t x| ≤
      ∫ x : ℝ in Set.Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1)),
        |deriv (uniform_nativeOrderLogDriveSummand d t) x| := by
  rw [uniform_nativeOrderIntegerDrive_eq_abel_sum]
  apply nativeIntegerAbel_discrepancy_bound (Real.exp_pos _).le
    ((uniform_nativeOrderLogDriveSummand_contDiff d t).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1))
  apply uniform_nativeOrderLogDriveSummand_zero_above d
  exact Real.exp_lt_exp.mpr (by linarith)




private theorem uniform_actual_source_compact (d : ℕ) : HasCompactSupport (sourceOrderFamily d) := by
  apply HasCompactSupport.intro (K := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale)
    isCompact_Icc
  exact fun x hx => (sourceFamily_supported d) x hx

private theorem uniform_exp_div_sqrt_exp (y : ℝ) :
    Real.exp y / Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  have hsplit : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hroot : Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
    rw [hsplit, Real.sqrt_mul_self (Real.exp_pos _).le]
  rw [hroot, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_add]
  congr 1
  ring

private theorem uniform_actual_exp_summand (d : ℕ) (t y : ℝ) :
    Real.exp y * uniform_nativeOrderLogDriveSummand d t (Real.exp y) =
      y * Real.exp (y / 2) * (sourceOrderFamily d) (t - y) := by
  simp only [uniform_nativeOrderLogDriveSummand, if_pos (Real.exp_pos y), Real.log_exp]
  calc
    _ = y * (Real.exp y / Real.sqrt (Real.exp y)) * (sourceOrderFamily d) (t - y) := by ring
    _ = _ := by rw [uniform_exp_div_sqrt_exp]

/-- Exact exponential substitution, with the zero neighborhood at the lower
endpoint proved from the actual compact source. -/
theorem uniform_nativeOrderLogDriveSummand_integral_eq_exponential (d : ℕ) (t : ℝ) :
    (∫ x : ℝ, uniform_nativeOrderLogDriveSummand d t x) =
      ∫ y : ℝ, y * Real.exp (y / 2) * (sourceOrderFamily d) (t - y) := by
  let a : ℝ := t - UniversalSinc.fixedScale - 1
  let F : ℝ → ℝ := uniform_nativeOrderLogDriveSummand d t
  let H : ℝ → ℝ := fun y => Real.exp y * F (Real.exp y)
  have hF : (∫ x : ℝ in Ioi (Real.exp a), F x) = ∫ x : ℝ, F x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    apply uniform_nativeOrderLogDriveSummand_zero_below d
    have hxle : x ≤ Real.exp a := le_of_not_gt hx
    exact hxle.trans_lt (Real.exp_lt_exp.mpr (by dsimp [a]; linarith))
  have hH : (∫ y : ℝ in Ioi a, H y) = ∫ y : ℝ, H y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hyle : y ≤ a := le_of_not_gt hy
    have hzero : F (Real.exp y) = 0 := by
      apply uniform_nativeOrderLogDriveSummand_zero_below d
      apply Real.exp_lt_exp.mpr
      dsimp [a] at hyle
      linarith
    dsimp only [H]
    rw [hzero, mul_zero]
  have hsub := integral_comp_exp_Ioi F a
  change (∫ y : ℝ in Ioi a, H y) = ∫ x : ℝ in Ioi (Real.exp a), F x at hsub
  rw [hF, hH] at hsub
  rw [← hsub]
  apply integral_congr_ae
  filter_upwards with y
  exact uniform_actual_exp_summand d t y

/-- Both actual pole moments are needed: the first weighted moment cancels
the logarithmic coefficient that remains after the ordinary moment. -/
theorem uniform_nativeOrderLogDriveSummand_integral_zero (d : ℕ) (t : ℝ) :
    (∫ x : ℝ, uniform_nativeOrderLogDriveSummand d t x) = 0 := by
  rw [uniform_nativeOrderLogDriveSummand_integral_eq_exponential]
  let H : ℝ → ℝ := fun y => y * Real.exp (y / 2) * (sourceOrderFamily d) (t - y)
  have hchange : (∫ y : ℝ, H y) = ∫ u : ℝ, H (t - u) :=
    (integral_sub_left_eq_self H volume t).symm
  change (∫ y : ℝ, H y) = 0
  rw [hchange]
  have heq : (fun u : ℝ => H (t - u)) = fun u =>
      Real.exp (t / 2) * (t * (Real.exp (-u / 2) * (sourceOrderFamily d) u) -
        u * Real.exp (-u / 2) * (sourceOrderFamily d) u) := by
    funext u
    dsimp only [H]
    rw [sub_sub_cancel, show (t - u) / 2 = t / 2 + (-u / 2) by ring, Real.exp_add]
    ring
  have hE : Continuous (fun u : ℝ => Real.exp (-u / 2)) := by fun_prop
  have h0int : Integrable (fun u : ℝ => Real.exp (-u / 2) * (sourceOrderFamily d) u) :=
    (hE.mul (sourceFamily_contDiff d).continuous).integrable_of_hasCompactSupport
      (uniform_actual_source_compact d).mul_left
  have h1int : Integrable (fun u : ℝ => u * Real.exp (-u / 2) * (sourceOrderFamily d) u) :=
    ((continuous_id.mul hE).mul (sourceFamily_contDiff d).continuous).integrable_of_hasCompactSupport
      (uniform_actual_source_compact d).mul_left
  rw [heq, integral_const_mul, integral_sub (h0int.const_mul t) h1int, integral_const_mul]
  rw [(uniform_source_negative_elementary_moments d).1,
    (uniform_source_negative_elementary_moments d).2]
  ring

theorem uniform_nativeOrderLogDriveSummand_continuum_zero (d : ℕ) (t : ℝ) :
    (∫ x : ℝ in Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1)),
      uniform_nativeOrderLogDriveSummand d t x) = 0 := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1))) (by
      intro x hx
      by_cases hx0 : 0 < x
      · have hxhigh : Real.exp (t + UniversalSinc.fixedScale + 1) < x :=
          lt_of_not_ge (fun h => hx ⟨hx0, h⟩)
        exact uniform_nativeOrderLogDriveSummand_zero_above d
          ((Real.exp_lt_exp.mpr (by linarith)).trans hxhigh)
      · exact uniform_nativeOrderLogDriveSummand_zero_below d
          ((le_of_not_gt hx0).trans_lt (Real.exp_pos _)))]
  exact uniform_nativeOrderLogDriveSummand_integral_zero d t

/-- Actual integer-drive bound with its continuum term discharged internally. -/
theorem uniform_nativeOrderIntegerDrive_abs_le_summand_derivative (d : ℕ) (t : ℝ) :
    |(integerDriveFamily d) t| ≤
      ∫ x : ℝ in Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1)),
        |deriv (uniform_nativeOrderLogDriveSummand d t) x| := by
  have h := uniform_nativeOrderIntegerDrive_abel_discrepancy_bound d t
  rw [uniform_nativeOrderLogDriveSummand_continuum_zero, sub_zero] at h
  exact h




private theorem uniform_logarithmic_drive_derivative_algebra
    (x R z v w : ℝ) (hx : x ≠ 0) (hR : R ≠ 0) (hroot : R ^ 2 = x) :
    ((x⁻¹ * R - z * (1 / (2 * R))) / R ^ 2) * v +
      (z / R) * (w * (0 - x⁻¹)) =
      ((1 - z / 2) * v - z * w) / (x * R) := by
  subst x
  field_simp [hR]
  ring

theorem uniform_nativeOrderLogDriveSummand_hasDerivAt (d : ℕ) {t x : ℝ} (hx : 0 < x) :
    HasDerivAt (uniform_nativeOrderLogDriveSummand d t)
      (((1 - Real.log x / 2) * (sourceOrderFamily d) (t - Real.log x) -
        Real.log x * deriv (sourceOrderFamily d) (t - Real.log x)) /
        (x * Real.sqrt x)) x := by
  have hlog := Real.hasDerivAt_log hx.ne'
  have hroot := Real.hasDerivAt_sqrt hx.ne'
  have hrootne : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have harg := (hasDerivAt_const x t).sub hlog
  have hj := ((sourceFamily_contDiff d).differentiable
    (by norm_num)
    (t - Real.log x)).hasDerivAt
  have hsource := hj.comp x harg
  have hraw := (hlog.div hroot hrootne).mul hsource
  have hagree : uniform_nativeOrderLogDriveSummand d t =ᶠ[𝓝 x]
      (fun y : ℝ => Real.log y / Real.sqrt y *
        (sourceOrderFamily d) (t - Real.log y)) := by
    filter_upwards [isOpen_Ioi.eventually_mem hx] with y hy
    exact if_pos hy
  have hd := hraw.congr_of_eventuallyEq hagree
  have hvalue := uniform_logarithmic_drive_derivative_algebra x (Real.sqrt x)
    (Real.log x) ((sourceOrderFamily d) (t - Real.log x))
    (deriv (sourceOrderFamily d) (t - Real.log x)) hx.ne' hrootne
    (Real.sq_sqrt hx.le)
  simpa only [] using! hd.congr_deriv hvalue

theorem uniform_nativeOrderLogDriveSummand_deriv (d : ℕ) {t x : ℝ} (hx : 0 < x) :
    deriv (uniform_nativeOrderLogDriveSummand d t) x =
      ((1 - Real.log x / 2) * (sourceOrderFamily d) (t - Real.log x) -
        Real.log x * deriv (sourceOrderFamily d) (t - Real.log x)) /
        (x * Real.sqrt x) :=
  (uniform_nativeOrderLogDriveSummand_hasDerivAt d hx).deriv

/-- The exponential Jacobian cancels exactly the x in the derivative
denominator. The remaining square-root weight is paid explicitly. -/
theorem uniform_nativeOrderLogDriveSummand_deriv_exp (d : ℕ) (t y : ℝ) :
    Real.exp y * deriv (uniform_nativeOrderLogDriveSummand d t) (Real.exp y) =
      (((1 - y / 2) * (sourceOrderFamily d) (t - y) -
        y * deriv (sourceOrderFamily d) (t - y)) / Real.sqrt (Real.exp y)) := by
  rw [uniform_nativeOrderLogDriveSummand_deriv d (Real.exp_pos y), Real.log_exp]
  field_simp [(Real.exp_pos y).ne', (Real.sqrt_pos.mpr (Real.exp_pos y)).ne']




private theorem uniform_drive_source_compact (d : ℕ) : HasCompactSupport (sourceOrderFamily d) := by
  apply HasCompactSupport.intro
    (K := Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale) isCompact_Icc
  exact fun x hx => (sourceFamily_supported d) x hx

private theorem uniform_drive_source_tsupport (d : ℕ) :
    tsupport (sourceOrderFamily d) ⊆
      Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  by_contra hnot
  exact hx ((sourceFamily_supported d) x hnot)

private theorem uniform_drive_source_deriv_continuous (d : ℕ) : Continuous (deriv (sourceOrderFamily d)) :=
  ((sourceFamily_contDiff d).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).continuous_deriv le_rfl

private theorem uniform_log_drive_deriv_zero_below (d : ℕ) {t x : ℝ}
    (hx : x < Real.exp (t - UniversalSinc.fixedScale)) :
    deriv (uniform_nativeOrderLogDriveSummand d t) x = 0 := by
  have hzero : uniform_nativeOrderLogDriveSummand d t =ᶠ[𝓝 x] (fun _ : ℝ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.eventually_mem hx] with y hy
    exact uniform_nativeOrderLogDriveSummand_zero_below d hy
  rw [hzero.deriv_eq, deriv_const]

private theorem uniform_sqrt_exp_half (y : ℝ) :
    Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  have hsplit : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hsplit, Real.sqrt_mul_self (Real.exp_pos _).le]

/-- The exact derivative profile after both genuine changes of variables. -/
def uniform_nativeOrderDriveDerivativeProfile (d : ℕ) (t u : ℝ) : ℝ :=
  Real.exp (-((t - u) / 2)) *
    ((1 - (t - u) / 2) * (sourceOrderFamily d) u -
      (t - u) * deriv (sourceOrderFamily d) u)

private theorem uniform_abs_exp_drive_deriv (d : ℕ) (t y : ℝ) :
    Real.exp y * |deriv (uniform_nativeOrderLogDriveSummand d t) (Real.exp y)| =
      |uniform_nativeOrderDriveDerivativeProfile d t (t - y)| := by
  calc
    _ = |Real.exp y * deriv (uniform_nativeOrderLogDriveSummand d t) (Real.exp y)| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos y)]
    _ = _ := by
      rw [uniform_nativeOrderLogDriveSummand_deriv_exp, abs_div, uniform_sqrt_exp_half,
        abs_of_pos (Real.exp_pos _), div_eq_mul_inv, ← Real.exp_neg]
      unfold uniform_nativeOrderDriveDerivativeProfile
      rw [sub_sub_cancel, abs_mul, abs_of_pos (Real.exp_pos _)]
      ring

/-- The full absolute derivative integral is a compact original-source
integral. The zero neighborhood at x = 0 is supplied by the actual source. -/
theorem uniform_nativeOrderLogDriveSummand_derivative_integral_eq (d : ℕ) (t : ℝ) :
    (∫ x : ℝ, |deriv (uniform_nativeOrderLogDriveSummand d t) x|) =
      ∫ u : ℝ, |uniform_nativeOrderDriveDerivativeProfile d t u| := by
  let a : ℝ := t - UniversalSinc.fixedScale - 1
  let D : ℝ → ℝ := fun x => |deriv (uniform_nativeOrderLogDriveSummand d t) x|
  let H : ℝ → ℝ := fun y => Real.exp y * D (Real.exp y)
  have hD : (∫ x : ℝ in Ioi (Real.exp a), D x) = ∫ x : ℝ, D x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hbelow : x < Real.exp (t - UniversalSinc.fixedScale) :=
      (le_of_not_gt hx).trans_lt (Real.exp_lt_exp.mpr (by dsimp [a]; linarith))
    dsimp only [D]
    rw [uniform_log_drive_deriv_zero_below d hbelow, abs_zero]
  have hH : (∫ y : ℝ in Ioi a, H y) = ∫ y : ℝ, H y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hbelow : Real.exp y < Real.exp (t - UniversalSinc.fixedScale) := by
      apply Real.exp_lt_exp.mpr
      have hyle : y ≤ a := le_of_not_gt hy
      dsimp only [a] at hyle
      linarith
    dsimp only [H, D]
    rw [uniform_log_drive_deriv_zero_below d hbelow, abs_zero, mul_zero]
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
  rw [uniform_abs_exp_drive_deriv, sub_sub_cancel]

/-- A finite constant determined by the exact original source and its
derivative. The integral is genuinely integrable by compact smoothness. -/
def uniform_nativeOrderDriveDecayConstant (d : ℕ) : ℝ :=
  Real.exp (UniversalSinc.fixedScale / 2) *
    ∫ u : ℝ, |(sourceOrderFamily d) u| + |deriv (sourceOrderFamily d) u|

theorem uniform_nativeOrderDriveSourceNorm_integrable (d : ℕ) :
    Integrable (fun u : ℝ => |(sourceOrderFamily d) u| + |deriv (sourceOrderFamily d) u|) :=
  ((sourceFamily_integrable d).abs).add
    (((uniform_drive_source_deriv_continuous d).integrable_of_hasCompactSupport (uniform_drive_source_compact d).deriv).abs)

theorem uniform_nativeOrderDriveDerivativeProfile_integrable (d : ℕ) (t : ℝ) :
    Integrable (uniform_nativeOrderDriveDerivativeProfile d t) := by
  have harg : Continuous (fun u : ℝ => t - u) := continuous_const.sub continuous_id
  have hcoef : Continuous (fun u : ℝ => 1 - (t - u) / 2) :=
    continuous_const.sub (harg.div_const 2)
  have hE : Continuous (fun u : ℝ => Real.exp (-((t - u) / 2))) := by fun_prop
  unfold uniform_nativeOrderDriveDerivativeProfile
  exact (hE.mul ((hcoef.mul (sourceFamily_contDiff d).continuous).sub
    (harg.mul (uniform_drive_source_deriv_continuous d)))).integrable_of_hasCompactSupport
      (((uniform_drive_source_compact d).mul_left.sub (uniform_drive_source_compact d).deriv.mul_left).mul_left)

theorem uniform_nativeOrderDriveDecayConstant_nonneg (d : ℕ) : 0 ≤ uniform_nativeOrderDriveDecayConstant d := by
  apply mul_nonneg (Real.exp_pos _).le
  exact integral_nonneg (fun u => add_nonneg (abs_nonneg _) (abs_nonneg _))

private theorem uniform_drive_profile_bound (d : ℕ) {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    |uniform_nativeOrderDriveDerivativeProfile d t u| ≤
      (Real.exp (UniversalSinc.fixedScale / 2) *
        (1 + t + UniversalSinc.fixedScale) * Real.exp (-(t / 2))) *
          (|(sourceOrderFamily d) u| + |deriv (sourceOrderFamily d) u|) := by
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
        |(1 - (t - u) / 2) * (sourceOrderFamily d) u -
          (t - u) * deriv (sourceOrderFamily d) u| ≤
            (1 + t + UniversalSinc.fixedScale) *
              (|(sourceOrderFamily d) u| + |deriv (sourceOrderFamily d) u|) := by
      calc
        _ ≤ |(1 - (t - u) / 2) * (sourceOrderFamily d) u| +
            |(t - u) * deriv (sourceOrderFamily d) u| := abs_sub _ _
        _ = |1 - (t - u) / 2| * |(sourceOrderFamily d) u| +
            |t - u| * |deriv (sourceOrderFamily d) u| := by rw [abs_mul, abs_mul]
        _ ≤ (1 + t + UniversalSinc.fixedScale) * |(sourceOrderFamily d) u| +
            (1 + t + UniversalSinc.fixedScale) * |deriv (sourceOrderFamily d) u| :=
          add_le_add (mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _))
            (mul_le_mul_of_nonneg_right habs' (abs_nonneg _))
        _ = _ := by ring
    have hexp : Real.exp (-((t - u) / 2)) ≤
        Real.exp (-(t / 2)) * Real.exp (UniversalSinc.fixedScale / 2) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      linarith [hu.2]
    unfold uniform_nativeOrderDriveDerivativeProfile
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-((t - u) / 2)) *
          ((1 + t + UniversalSinc.fixedScale) *
            (|(sourceOrderFamily d) u| + |deriv (sourceOrderFamily d) u|)) :=
        mul_le_mul_of_nonneg_left hcore (Real.exp_pos _).le
      _ ≤ (Real.exp (-(t / 2)) * Real.exp (UniversalSinc.fixedScale / 2)) *
          ((1 + t + UniversalSinc.fixedScale) *
            (|(sourceOrderFamily d) u| + |deriv (sourceOrderFamily d) u|)) :=
        mul_le_mul_of_nonneg_right hexp
          (mul_nonneg hC (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      _ = _ := by ring
  · have hj := (sourceFamily_supported d) u hu
    have hj' : deriv (sourceOrderFamily d) u = 0 :=
      deriv_of_notMem_tsupport (fun h => hu (uniform_drive_source_tsupport d h))
    simp only [uniform_nativeOrderDriveDerivativeProfile, hj, hj', mul_zero, sub_zero,
      abs_zero, zero_add, mul_zero, le_refl]

/-- The actual source-defined derivative budget, after the exact Jacobian
and all support restrictions have been paid. -/
theorem uniform_nativeOrderLogDriveSummand_derivative_integral_le (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, |deriv (uniform_nativeOrderLogDriveSummand d t) x|) ≤
      uniform_nativeOrderDriveDecayConstant d * (1 + t + UniversalSinc.fixedScale) *
        Real.exp (-(t / 2)) := by
  rw [uniform_nativeOrderLogDriveSummand_derivative_integral_eq]
  have h := integral_mono (uniform_nativeOrderDriveDerivativeProfile_integrable d t).abs
    ((uniform_nativeOrderDriveSourceNorm_integrable d).const_mul
      (Real.exp (UniversalSinc.fixedScale / 2) *
        (1 + t + UniversalSinc.fixedScale) * Real.exp (-(t / 2))))
    (uniform_drive_profile_bound d ht)
  rw [integral_const_mul] at h
  calc
    _ ≤ _ := h
    _ = _ := by unfold uniform_nativeOrderDriveDecayConstant; ring

/-- The literal unchanged integer drive decays exponentially; neither a
decay certificate nor any prime-field bound is a caller hypothesis. -/
theorem uniform_nativeOrderIntegerDrive_decay (d : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    |(integerDriveFamily d) t| ≤
      uniform_nativeOrderDriveDecayConstant d * (1 + t + UniversalSinc.fixedScale) *
        Real.exp (-(t / 2)) := by
  have hDint : Integrable (fun x : ℝ => |deriv (uniform_nativeOrderLogDriveSummand d t) x|) :=
    (((uniform_nativeOrderLogDriveSummand_contDiff d t).of_le
      (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)).continuous_deriv le_rfl).abs
      |>.integrable_of_hasCompactSupport (uniform_nativeOrderLogDriveSummand_hasCompactSupport d t).deriv.abs
  calc
    _ ≤ ∫ x : ℝ in Ioc 0 (Real.exp (t + UniversalSinc.fixedScale + 1)),
        |deriv (uniform_nativeOrderLogDriveSummand d t) x| :=
      uniform_nativeOrderIntegerDrive_abs_le_summand_derivative d t
    _ ≤ ∫ x : ℝ, |deriv (uniform_nativeOrderLogDriveSummand d t) x| :=
      setIntegral_le_integral hDint (Filter.Eventually.of_forall (fun _ => abs_nonneg _))
    _ ≤ _ := uniform_nativeOrderLogDriveSummand_derivative_integral_le d ht


def nativeDriveOrderFactor : ℝ := Real.exp (UniversalSinc.fixedScale/2)*(4*UniversalSinc.fixedScale)

theorem nativeDriveOrderFactor_nonneg : 0 ≤ nativeDriveOrderFactor := by
  unfold nativeDriveOrderFactor
  positivity [UniversalSinc.fixedScale_pos]

theorem nativeOrderDriveDecayConstant_le_rawBudget (d : ℕ) :
    uniform_nativeOrderDriveDecayConstant d ≤ nativeDriveOrderFactor*nativeSourceRawBudget d := by
  unfold uniform_nativeOrderDriveDecayConstant nativeDriveOrderFactor
  rw [integral_add (sourceFamily_integrable d).abs
    (((uniform_drive_source_deriv_continuous d).integrable_of_hasCompactSupport
      (sourceFamily_hasCompactSupport d).deriv).abs)]
  have h₀ := sourceFamily_jet_L1_le_rawBudget d 0 (by omega)
  have h₁ := sourceFamily_jet_L1_le_rawBudget d 1 (by omega)
  simp only [iteratedDeriv_zero, iteratedDeriv_one] at h₀ h₁
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  nlinarith

def nativeDriveL2Envelope (t : ℝ) : ℝ :=
  (Ici (0:ℝ)).indicator (fun u => (1+u+UniversalSinc.fixedScale)*Real.exp (-(u/2))) t

theorem nativeDriveL2Envelope_nonneg (t : ℝ) : 0 ≤ nativeDriveL2Envelope t := by
  by_cases ht : 0 ≤ t
  · rw [nativeDriveL2Envelope, indicator_of_mem (show t∈Ici (0:ℝ) from ht)]
    positivity [UniversalSinc.fixedScale_pos]
  · simp [nativeDriveL2Envelope, ht]

private theorem uniform_pow_exp_integrableOn (n : ℕ) {a : ℝ} (ha : 0<a) :
    IntegrableOn (fun t : ℝ => t^n*Real.exp (-a*t)) (Ioi 0) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow
    (s := (n:ℝ)) (p := (1:ℝ)) (b := a)
    (by have hn := Nat.cast_nonneg (α := ℝ) n; linarith) (by norm_num) ha
  simpa only [Real.rpow_natCast, Real.rpow_one] using! h

theorem nativeDriveL2Envelope_sq_integrable : Integrable (fun t : ℝ => nativeDriveL2Envelope t^2) := by
  have h0 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi 0) := by
    simpa only [pow_zero, one_mul, neg_one_mul] using! uniform_pow_exp_integrableOn 0 (by norm_num : (0:ℝ)<1)
  have h1 : IntegrableOn (fun t : ℝ => t*Real.exp (-t)) (Ioi 0) := by
    simpa only [pow_one, one_mul, neg_one_mul] using! uniform_pow_exp_integrableOn 1 (by norm_num : (0:ℝ)<1)
  have h2 : IntegrableOn (fun t : ℝ => t^2*Real.exp (-t)) (Ioi 0) := by
    simpa only [one_mul, neg_one_mul] using! uniform_pow_exp_integrableOn 2 (by norm_num : (0:ℝ)<1)
  have hsq : IntegrableOn (fun t : ℝ => ((1+t+UniversalSinc.fixedScale)*Real.exp (-(t/2)))^2) (Ioi 0) := by
    have he (t : ℝ) : Real.exp (-(t/2))^2 = Real.exp (-t) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have heq : (fun t : ℝ => ((1+t+UniversalSinc.fixedScale)*Real.exp (-(t/2)))^2) =
        fun t => (1+UniversalSinc.fixedScale)^2*Real.exp (-t) +
          (2*(1+UniversalSinc.fixedScale))*(t*Real.exp (-t)) + t^2*Real.exp (-t) := by
      funext t
      rw [mul_pow, he]
      ring
    rw [heq]
    exact ((h0.const_mul _).add (h1.const_mul _)).add h2
  have hIci : IntegrableOn (fun t : ℝ => ((1+t+UniversalSinc.fixedScale)*Real.exp (-(t/2)))^2) (Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact hsq
  have heq : (fun t : ℝ => nativeDriveL2Envelope t^2) =
      (Ici (0:ℝ)).indicator (fun t => ((1+t+UniversalSinc.fixedScale)*Real.exp (-(t/2)))^2) := by
    funext t
    by_cases ht : 0 ≤ t <;> simp [nativeDriveL2Envelope, ht]
  rw [heq]
  exact hIci.integrable_indicator measurableSet_Ici

theorem integerDriveFamily_le_orderEnvelope (d : ℕ) (t : ℝ) :
    |integerDriveFamily d t| ≤ nativeDriveOrderFactor*nativeSourceRawBudget d*nativeDriveL2Envelope t := by
  by_cases ht : 0≤t
  · rw [nativeDriveL2Envelope, indicator_of_mem (show t∈Ici (0:ℝ) from ht)]
    calc
      _ ≤ uniform_nativeOrderDriveDecayConstant d*(1+t+UniversalSinc.fixedScale)*Real.exp (-(t/2)) :=
        uniform_nativeOrderIntegerDrive_decay d ht
      _ ≤ (nativeDriveOrderFactor*nativeSourceRawBudget d)*(1+t+UniversalSinc.fixedScale)*Real.exp (-(t/2)) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (nativeOrderDriveDecayConstant_le_rawBudget d)
            (by linarith [UniversalSinc.fixedScale_pos])) (Real.exp_nonneg _)
      _ = _ := by ring
  · rw [integerDriveFamily_zero_before d ((lt_of_not_ge ht).trans nativeCausalGap_pos), abs_zero]
    positivity [nativeDriveOrderFactor_nonneg, nativeSourceRawBudget_one_le d,
      nativeDriveL2Envelope_nonneg t]

theorem integerDriveFamily_sq_integrable (d : ℕ) :
    Integrable (fun t : ℝ => (integerDriveFamily d t)^2) := by
  have hmajor := nativeDriveL2Envelope_sq_integrable.const_mul
    ((nativeDriveOrderFactor*nativeSourceRawBudget d)^2)
  apply hmajor.mono' (((integerDriveFamily_contDiff d).continuous.pow 2).aestronglyMeasurable)
  filter_upwards with t
  simp only [Pi.pow_apply]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have h := pow_le_pow_left₀ (abs_nonneg (integerDriveFamily d t))
    (integerDriveFamily_le_orderEnvelope d t) 2
  simpa only [sq_abs, mul_pow] using h

theorem integerDriveFamily_memLp_two (d : ℕ) : MemLp (integerDriveFamily d) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm (integerDriveFamily_contDiff d).continuous.aestronglyMeasurable).mpr
  simpa only [Real.norm_eq_abs, sq_abs] using integerDriveFamily_sq_integrable d

def nativeDriveL2EnvelopeNorm : ℝ := Real.sqrt (∫ t : ℝ, nativeDriveL2Envelope t^2)

theorem integerDriveFamily_L2_le_rawBudget (d : ℕ) :
    Real.sqrt (∫ t : ℝ, |integerDriveFamily d t|^2) ≤
      (nativeDriveOrderFactor*nativeDriveL2EnvelopeNorm)*nativeSourceRawBudget d := by
  have hnonneg : 0 ≤ nativeDriveOrderFactor*nativeSourceRawBudget d :=
    mul_nonneg nativeDriveOrderFactor_nonneg (zero_le_one.trans (nativeSourceRawBudget_one_le d))
  have hmass : (∫ t : ℝ, |integerDriveFamily d t|^2) ≤
      (nativeDriveOrderFactor*nativeSourceRawBudget d)^2*(∫ t : ℝ, nativeDriveL2Envelope t^2) := by
    rw [← integral_const_mul]
    apply integral_mono_ae (by simpa only [sq_abs] using integerDriveFamily_sq_integrable d)
      (nativeDriveL2Envelope_sq_integrable.const_mul _)
    filter_upwards with t
    have h := pow_le_pow_left₀ (abs_nonneg (integerDriveFamily d t))
      (integerDriveFamily_le_orderEnvelope d t) 2
    simpa only [mul_pow] using h
  calc
    _ ≤ Real.sqrt ((nativeDriveOrderFactor*nativeSourceRawBudget d)^2*
        (∫ t : ℝ, nativeDriveL2Envelope t^2)) := Real.sqrt_le_sqrt hmass
    _ = _ := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hnonneg]
      unfold nativeDriveL2EnvelopeNorm
      ring

theorem nativeRawBudget_uniform_log_cost (K : ℝ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ d : ℕ,
      Real.log (1+K*nativeSourceRawBudget d) ≤ C*((d:ℝ)+1)*Real.log ((d:ℝ)+2) := by
  let A := (max 1 K)*(max 1 nativeSourceGevreyA)*nativeSourceGevreyH^2
  let B := nativeSourceGevreyH^2+1/4
  have hA : 1≤A := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (le_max_left _ _))
      (one_le_pow₀ nativeSourceGevreyH_one_le)
  have hB : 1≤B := by dsimp [B]; nlinarith [nativeSourceGevreyH_one_le, sq_nonneg nativeSourceGevreyH]
  obtain ⟨C,hC,hcost⟩ := affine_factorial_uniform_log_cost hA hB
  refine ⟨C,hC,fun d => ?_⟩
  have hbudget : K*nativeSourceRawBudget d ≤ A*B^(d+2)*((2*d+6).factorial:ℝ)^2 := by
    calc
      _ ≤ max 1 K*nativeSourceRawBudget d := mul_le_mul_of_nonneg_right (le_max_right _ _)
        (zero_le_one.trans (nativeSourceRawBudget_one_le d))
      _ = _ := by dsimp [A,B,nativeSourceRawBudget]; ring
  have hpos : 0<1+K*nativeSourceRawBudget d := by
    have hraw := zero_le_one.trans (nativeSourceRawBudget_one_le d)
    positivity
  exact (Real.log_le_log hpos (show 1+K*nativeSourceRawBudget d ≤
    1+A*B^(d+2)*((2*d+6).factorial:ℝ)^2 by linarith)).trans (hcost d)

theorem nativeRawBudget_uniform_exp_cost (K : ℝ) (hK : 0≤K) :
    ∃ C : ℝ, 0<C ∧ ∀ d : ℕ,
      K*nativeSourceRawBudget d ≤ Real.exp (C*((d:ℝ)+1)*Real.log ((d:ℝ)+2)) := by
  obtain ⟨C,hC,hcost⟩ := nativeRawBudget_uniform_log_cost K hK
  refine ⟨C,hC,fun d => ?_⟩
  have hpos : 0<1+K*nativeSourceRawBudget d := by
    have hraw := zero_le_one.trans (nativeSourceRawBudget_one_le d)
    positivity
  exact (by linarith : K*nativeSourceRawBudget d ≤ 1+K*nativeSourceRawBudget d).trans
    ((Real.log_le_iff_le_exp hpos).mp (hcost d))

/-- The actual L2 equivalence class of the literal integer drive. -/
def integerDriveFamilyL2 (d : ℕ) : Lp ℝ 2 (volume:Measure ℝ) :=
  (integerDriveFamily_memLp_two d).toLp (integerDriveFamily d)

theorem integerDriveFamilyL2_norm_eq (d : ℕ) :
    ‖integerDriveFamilyL2 d‖ = Real.sqrt (∫ t : ℝ, |integerDriveFamily d t|^2) := by
  have hae : integerDriveFamilyL2 d =ᵐ[volume] integerDriveFamily d :=
    (integerDriveFamily_memLp_two d).coeFn_toLp
  have hsq : ‖integerDriveFamilyL2 d‖^2 = ∫ t : ℝ, |integerDriveFamily d t|^2 := by
    rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hae] with t ht
    simp only [ht, real_inner_self_eq_norm_sq, Real.norm_eq_abs]
  calc
    _ = Real.sqrt (‖integerDriveFamilyL2 d‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = _ := congrArg Real.sqrt hsq

/-- Appendix B's common source-fixed order cost controls the actual L1/L∞
jets and genuine L2 integer drive. The displayed continuum cancellation is
proved from the actual two elementary moments, not assumed. -/
theorem source_order_uniform_norms :
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
  let K := 1+2*UniversalSinc.fixedScale+nativeDriveOrderFactor*nativeDriveL2EnvelopeNorm
  have hU : 0≤nativeDriveOrderFactor*nativeDriveL2EnvelopeNorm :=
    mul_nonneg nativeDriveOrderFactor_nonneg (Real.sqrt_nonneg _)
  have hK : 0≤K := by dsimp [K]; positivity [UniversalSinc.fixedScale_pos]
  have hK₁ : 1+2*UniversalSinc.fixedScale≤K := by dsimp [K]; linarith
  have hK₂ : nativeDriveOrderFactor*nativeDriveL2EnvelopeNorm≤K := by
    dsimp [K]
    linarith [UniversalSinc.fixedScale_pos]
  obtain ⟨C,hC,hcost⟩ := nativeRawBudget_uniform_exp_cost K hK
  refine ⟨C,hC,fun d => ⟨?_,integerDriveFamily_memLp_two d,?_,uniform_nativeOrderLogDriveSummand_integral_zero d⟩⟩
  · intro k hk
    have hraw := zero_le_one.trans (nativeSourceRawBudget_one_le d)
    have hsum (x : ℝ) : |iteratedDeriv k (sourceOrderFamily d) x| +
        (∫ u : ℝ, |iteratedDeriv k (sourceOrderFamily d) u|) ≤
          Real.exp (C*((d:ℝ)+1)*Real.log ((d:ℝ)+2)) := by
      have h := add_le_add (sourceFamily_jet_le_rawBudget d k hk x) (sourceFamily_jet_L1_le_rawBudget d k hk)
      have hfixed := mul_le_mul_of_nonneg_right hK₁ hraw
      exact h.trans ((by nlinarith : nativeSourceRawBudget d +
        2*UniversalSinc.fixedScale*nativeSourceRawBudget d ≤ K*nativeSourceRawBudget d).trans (hcost d))
    refine ⟨hsum, ?_, ?_⟩
    · rw [eLpNorm_exponent_top]
      apply eLpNormEssSup_le_of_ae_bound
      filter_upwards with x
      rw [Real.norm_eq_abs]
      exact (le_add_of_nonneg_right (integral_nonneg (fun u => abs_nonneg _))).trans (hsum x)
    · have hL : 0 ≤ Real.exp (C*((d:ℝ)+1)*Real.log ((d:ℝ)+2)) -
          (∫ u : ℝ, |iteratedDeriv k (sourceOrderFamily d) u|) := by
        have h := hsum 0
        linarith [abs_nonneg (iteratedDeriv k (sourceOrderFamily d) 0)]
      have hess : eLpNorm (iteratedDeriv k (sourceOrderFamily d)) (⊤:ENNReal) volume ≤
          ENNReal.ofReal (Real.exp (C*((d:ℝ)+1)*Real.log ((d:ℝ)+2)) -
            (∫ u : ℝ, |iteratedDeriv k (sourceOrderFamily d) u|)) := by
        rw [eLpNorm_exponent_top]
        apply eLpNormEssSup_le_of_ae_bound
        filter_upwards with x
        rw [Real.norm_eq_abs]
        have h := hsum x
        linarith
      have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hess
      rw [ENNReal.toReal_ofReal hL] at hreal
      linarith
  · rw [integerDriveFamilyL2_norm_eq]
    exact (integerDriveFamily_L2_le_rawBudget d).trans
      ((mul_le_mul_of_nonneg_right hK₂ (zero_le_one.trans (nativeSourceRawBudget_one_le d))).trans (hcost d))

theorem sourceFamily_paperFT_strip_bound (d : ℕ) {z : ℂ} (hz : |z.im|≤1/2) :
    ‖paperFT (fun u : ℝ => (sourceOrderFamily d u:ℂ)) z‖ ≤
      nativeDriveOrderFactor*nativeSourceRawBudget d/(1+Complex.normSq z) := by
  let f : ℝ → ℂ := fun u => (sourceOrderFamily d u:ℂ)
  have hf := sourceFamily_complex_contDiff d
  have hfi : Integrable f := hf.continuous.integrable_of_hasCompactSupport (sourceFamily_complex_hasCompactSupport d)
  have hsupp : ∀ u : ℝ, f u≠0 → |u|≤UniversalSinc.fixedScale := by
    intro u hu
    apply abs_le.mpr
    by_contra hmem
    apply hu
    rw [show f u=(sourceOrderFamily d u:ℂ) by rfl, sourceFamily_supported d u hmem, Complex.ofReal_zero]
  have h0 := norm_paperFT_le hfi hsupp z
  have h2 := norm_paperFT_mul_sq_le (hf.of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)) hsupp z
  have hL0 : (∫ u : ℝ, ‖f u‖) ≤ 2*UniversalSinc.fixedScale*nativeSourceRawBudget d := by
    simpa only [f,Complex.norm_real,Real.norm_eq_abs,iteratedDeriv_zero] using
      sourceFamily_jet_L1_le_rawBudget d 0 (by omega)
  have hL2 : (∫ u : ℝ, ‖deriv (deriv f) u‖) ≤ 2*UniversalSinc.fixedScale*nativeSourceRawBudget d := by
    have he := native_real_iteratedDeriv_complex (sourceFamily_contDiff d) 2
    simp only [iteratedDeriv_succ,iteratedDeriv_zero] at he
    change (∫ u : ℝ, ‖deriv (deriv (fun v : ℝ => (sourceOrderFamily d v:ℂ))) u‖) ≤ _
    rw [he]
    simpa only [Complex.norm_real,Real.norm_eq_abs,iteratedDeriv_succ,iteratedDeriv_zero] using
      sourceFamily_jet_L1_le_rawBudget d 2 le_rfl
  have he : Real.exp (|z.im| *UniversalSinc.fixedScale) ≤ Real.exp (UniversalSinc.fixedScale/2) :=
    Real.exp_le_exp.mpr (by nlinarith [UniversalSinc.fixedScale_pos])
  have hM : 0≤2*UniversalSinc.fixedScale*nativeSourceRawBudget d := by
    positivity [UniversalSinc.fixedScale_pos,nativeSourceRawBudget_one_le d]
  have h0' := h0.trans ((mul_le_mul_of_nonneg_left hL0 (Real.exp_nonneg _)).trans
    (mul_le_mul_of_nonneg_right he hM))
  have h2' := h2.trans ((mul_le_mul_of_nonneg_left hL2 (Real.exp_nonneg _)).trans
    (mul_le_mul_of_nonneg_right he hM))
  have hden : 0<1+Complex.normSq z := by nlinarith [Complex.normSq_nonneg z]
  apply (le_div_iff₀ hden).mpr
  rw [Complex.normSq_eq_norm_sq]
  unfold nativeDriveOrderFactor
  dsimp only [f] at h0' h2'
  nlinarith

def nativeZeroCoefficientMass : ℝ :=
  ∑' rho : zetaZeroConfig.carrier, (zetaZeroConfig.mult rho:ℝ)/(1+Complex.normSq (gammaOf rho))

theorem nativeZeroCoefficientMass_nonneg : 0≤nativeZeroCoefficientMass := by
  apply tsum_nonneg
  intro rho
  exact div_nonneg (Nat.cast_nonneg _) (by nlinarith [Complex.normSq_nonneg (gammaOf (rho:ℂ))])

theorem sourceFamilyLaplace_at_zero_bound (d : ℕ) (rho : zetaZeroConfig.carrier) :
    ‖sourceFamilyLaplace d ((rho:ℂ)-1/2)‖ ≤
      nativeDriveOrderFactor*nativeSourceRawBudget d/(1+Complex.normSq (gammaOf rho)) := by
  have hz : I*((rho:ℂ)-1/2) = -(gammaOf rho) := by
    rw [← nativeGammaOf_shift]
    calc
      I*(I*gammaOf rho) = (I*I)*gammaOf rho := by ring
      _ = _ := by rw [I_mul_I]; ring
  rw [sourceFamilyLaplace_eq_paperFT,hz]
  have him : |(-(gammaOf (rho:ℂ))).im|≤1/2 := by
    rw [Complex.neg_im,abs_neg]
    exact WeilEF.abs_gammaOf_im_le (zetaZeroConfig.strip _ rho.property)
  simpa only [Complex.normSq_neg] using sourceFamily_paperFT_strip_bound d him

theorem nativeNontrivialZeroTerm_theta_bound (d : ℕ) {t : ℝ} (ht : 0≤t)
    (rho : zetaZeroConfig.carrier) :
    ‖nativeNontrivialZeroTerm d t rho‖ ≤
      (nativeDriveOrderFactor*nativeSourceRawBudget d*Real.exp (nativeZeroDisplacementSup*t))*
        ((zetaZeroConfig.mult rho:ℝ)/(1+Complex.normSq (gammaOf rho))) := by
  have hr : (rho:ℂ).re-1/2≤nativeZeroDisplacementSup :=
    (le_max_left _ _).trans (native_zero_sup_bounds.2.2.1 rho)
  have he : Real.exp (((rho:ℂ).re-1/2)*t) ≤ Real.exp (nativeZeroDisplacementSup*t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hr ht)
  have hb := sourceFamilyLaplace_at_zero_bound d rho
  have hden : 0<1+Complex.normSq (gammaOf (rho:ℂ)) := by
    nlinarith [Complex.normSq_nonneg (gammaOf (rho:ℂ))]
  unfold nativeNontrivialZeroTerm
  simp only [norm_mul,Complex.norm_natCast,Complex.norm_exp,Complex.mul_re,
    Complex.sub_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    Complex.div_ofNat_re,Complex.one_re]
  have hmul := mul_le_mul
    (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (zetaZeroConfig.mult rho))) he
    (Real.exp_nonneg _) (by positivity [nativeDriveOrderFactor_nonneg,nativeSourceRawBudget_one_le d])
  calc
    _ ≤ (zetaZeroConfig.mult rho:ℝ)*
        (nativeDriveOrderFactor*nativeSourceRawBudget d/(1+Complex.normSq (gammaOf rho)))*
          Real.exp (nativeZeroDisplacementSup*t) := hmul
    _ = _ := by ring

theorem nativeNontrivialZeroSum_theta_bound (d : ℕ) {t : ℝ} (ht : 0≤t) :
    ‖∑' rho : zetaZeroConfig.carrier, nativeNontrivialZeroTerm d t rho‖ ≤
      (nativeDriveOrderFactor*nativeZeroCoefficientMass)*nativeSourceRawBudget d*
        Real.exp (nativeZeroDisplacementSup*t) := by
  have hs := native_zero_count_summability.1.mul_left
    (nativeDriveOrderFactor*nativeSourceRawBudget d*Real.exp (nativeZeroDisplacementSup*t))
  have hn := nativeNontrivialZeroTerm_summable_norm d t
  calc
    _ ≤ ∑' rho : zetaZeroConfig.carrier, ‖nativeNontrivialZeroTerm d t rho‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' rho : zetaZeroConfig.carrier,
        (nativeDriveOrderFactor*nativeSourceRawBudget d*Real.exp (nativeZeroDisplacementSup*t))*
          ((zetaZeroConfig.mult rho:ℝ)/(1+Complex.normSq (gammaOf rho))) :=
      Summable.tsum_le_tsum (nativeNontrivialZeroTerm_theta_bound d ht) hn hs
    _ = _ := by rw [tsum_mul_left]; unfold nativeZeroCoefficientMass; ring

def nativeTrivialTailFactor : ℝ := (2*UniversalSinc.fixedScale)/(1-Real.exp (-2))

theorem nativeTrivialTailFactor_nonneg : 0≤nativeTrivialTailFactor := by
  unfold nativeTrivialTailFactor
  have hq : Real.exp (-2)<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  positivity [UniversalSinc.fixedScale_pos]

theorem nativeTrivialZeroSum_uniform_tail_bound (d : ℕ) {t : ℝ}
    (ht : UniversalSinc.fixedScale+1≤t) :
    ‖∑' n : ℕ, nativeTrivialZeroTerm d t n‖ ≤ nativeTrivialTailFactor*nativeSourceRawBudget d := by
  let q : ℝ := Real.exp (-2)
  have hq0 : 0≤q := Real.exp_nonneg _
  have hq1 : q<1 := Real.exp_lt_one_iff.mpr (by norm_num)
  have hM : 0≤nativeSourceL1Mass d := integral_nonneg (fun _ => abs_nonneg _)
  have hL : nativeSourceL1Mass d≤2*UniversalSinc.fixedScale*nativeSourceRawBudget d := by
    simpa only [nativeSourceL1Mass,iteratedDeriv_zero] using sourceFamily_jet_L1_le_rawBudget d 0 (by omega)
  have hterm (n : ℕ) : ‖nativeTrivialZeroTerm d t n‖ ≤
      (2*UniversalSinc.fixedScale*nativeSourceRawBudget d)*q^n := by
    have ha : 0≤nativeTrivialZeroDecay n := by unfold nativeTrivialZeroDecay; positivity
    have he₁ : -nativeTrivialZeroDecay n*(t-UniversalSinc.fixedScale) ≤ -nativeTrivialZeroDecay n := by
      nlinarith
    have he₂ : -nativeTrivialZeroDecay n ≤ (-2:ℝ)*(n:ℝ) := by unfold nativeTrivialZeroDecay; linarith
    have he : Real.exp (-nativeTrivialZeroDecay n*(t-UniversalSinc.fixedScale))≤q^n := by
      calc
        _ ≤ Real.exp ((-2:ℝ)*(n:ℝ)) := Real.exp_le_exp.mpr (he₁.trans he₂)
        _ = _ := by rw [mul_comm,Real.exp_nat_mul]
    exact (nativeTrivialZeroTerm_bound d t n).trans
      (mul_le_mul hL he (Real.exp_nonneg _) (by positivity [UniversalSinc.fixedScale_pos,nativeSourceRawBudget_one_le d]))
  have hs := (summable_geometric_of_lt_one hq0 hq1).mul_left
    (2*UniversalSinc.fixedScale*nativeSourceRawBudget d)
  calc
    _ ≤ ∑' n : ℕ, ‖nativeTrivialZeroTerm d t n‖ :=
      norm_tsum_le_tsum_norm (nativeTrivialZeroTerm_summable_norm d (by linarith))
    _ ≤ ∑' n : ℕ, (2*UniversalSinc.fixedScale*nativeSourceRawBudget d)*q^n :=
      Summable.tsum_le_tsum hterm (nativeTrivialZeroTerm_summable_norm d (by linarith)) hs
    _ = _ := by
      rw [tsum_mul_left,tsum_geometric_of_norm_lt_one (by simpa [Real.norm_eq_abs,abs_of_nonneg hq0] using hq1)]
      unfold nativeTrivialTailFactor
      dsimp [q]
      ring

def nativePrimeInitialFactor : ℝ :=
  ∑ n ∈ Finset.range (nativeHistoryCutoff UniversalSinc.fixedScale (UniversalSinc.fixedScale+1)+1),
    |nativePrimeCoefficient n|

theorem nativePrimeInitialFactor_nonneg : 0≤nativePrimeInitialFactor :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem primeFieldFamily_initial_bound (d : ℕ) {t : ℝ} (ht : t≤UniversalSinc.fixedScale+1) :
    |primeFieldFamily d t| ≤ nativePrimeInitialFactor*nativeSourceRawBudget d := by
  rw [primeFieldFamily_history d ht]
  calc
    _ ≤ ∑ n ∈ Finset.range (nativeHistoryCutoff UniversalSinc.fixedScale (UniversalSinc.fixedScale+1)+1),
        |nativePrimeCoefficient n*sourceOrderFamily d (t-Real.log n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range (nativeHistoryCutoff UniversalSinc.fixedScale (UniversalSinc.fixedScale+1)+1),
        |nativePrimeCoefficient n| *nativeSourceRawBudget d := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      simpa only [iteratedDeriv_zero] using sourceFamily_jet_le_rawBudget d 0 (by omega) (t-Real.log n)
    _ = _ := by rw [← Finset.sum_mul]; rfl

def nativeFieldOrderFactor : ℝ :=
  1+nativePrimeInitialFactor+nativeDriveOrderFactor*nativeZeroCoefficientMass+nativeTrivialTailFactor

def nativeFieldOrderConstant (d : ℕ) : ℝ := nativeFieldOrderFactor*nativeSourceRawBudget d

theorem nativeFieldOrderFactor_pos : 0<nativeFieldOrderFactor := by
  have hZ := mul_nonneg nativeDriveOrderFactor_nonneg nativeZeroCoefficientMass_nonneg
  unfold nativeFieldOrderFactor
  linarith [nativePrimeInitialFactor_nonneg,nativeTrivialTailFactor_nonneg]

/-- The actual prime field has the actual zero-supremum envelope. Its coefficient
cost is source-fixed, including both absolute zero sums and the finite initial
history; no rate or coefficient identity is a caller premise. -/
theorem native_field_theta_envelope :
    ∃ C : ℝ, 0<C ∧ ∀ d : ℕ,
      0<nativeFieldOrderConstant d ∧
      (∀ t : ℝ, 0≤t → |primeFieldFamily d t| ≤
        nativeFieldOrderConstant d*Real.exp (nativeZeroDisplacementSup*t)) ∧
      Real.log (1+nativeFieldOrderConstant d) ≤ C*((d:ℝ)+1)*Real.log ((d:ℝ)+2) := by
  obtain ⟨C,hC,hcost⟩ := nativeRawBudget_uniform_log_cost nativeFieldOrderFactor nativeFieldOrderFactor_pos.le
  refine ⟨C,hC,fun d => ⟨mul_pos nativeFieldOrderFactor_pos
    (zero_lt_one.trans_le (nativeSourceRawBudget_one_le d)),?_,hcost d⟩⟩
  intro t ht
  have he : 1≤Real.exp (nativeZeroDisplacementSup*t) :=
    Real.one_le_exp (mul_nonneg native_zero_sup_bounds.1 ht)
  have hraw := zero_le_one.trans (nativeSourceRawBudget_one_le d)
  have hZ := mul_nonneg nativeDriveOrderFactor_nonneg nativeZeroCoefficientMass_nonneg
  by_cases hi : t≤UniversalSinc.fixedScale+1
  · have hfactor : nativePrimeInitialFactor≤nativeFieldOrderFactor := by
      unfold nativeFieldOrderFactor
      linarith [nativeTrivialTailFactor_nonneg]
    exact (primeFieldFamily_initial_bound d hi).trans
      ((mul_le_mul_of_nonneg_right hfactor hraw).trans
        (le_mul_of_one_le_right (mul_nonneg nativeFieldOrderFactor_pos.le hraw) he))
  · have htail := nativeTrivialZeroSum_uniform_tail_bound d (le_of_not_ge hi)
    have hzero := nativeNontrivialZeroSum_theta_bound d ht
    have hef := (native_source_explicit_formula d (by linarith : UniversalSinc.fixedScale<t)).2.2.2
    have hnorm : |primeFieldFamily d t| ≤
        ‖∑' rho : zetaZeroConfig.carrier, nativeNontrivialZeroTerm d t rho‖+
        ‖∑' n : ℕ, nativeTrivialZeroTerm d t n‖ := by
      calc
        _ = ‖(primeFieldFamily d t:ℂ)‖ := by simp
        _ ≤ _ := by
          rw [hef]
          simpa only [norm_neg] using norm_sub_le
            (-(∑' rho : zetaZeroConfig.carrier, nativeNontrivialZeroTerm d t rho))
            (∑' n : ℕ, nativeTrivialZeroTerm d t n)
    have htail' := htail.trans (le_mul_of_one_le_right
      (mul_nonneg nativeTrivialTailFactor_nonneg hraw) he)
    have hfactor : nativeDriveOrderFactor*nativeZeroCoefficientMass+nativeTrivialTailFactor≤nativeFieldOrderFactor := by
      unfold nativeFieldOrderFactor
      linarith [nativePrimeInitialFactor_nonneg]
    exact hnorm.trans ((add_le_add hzero htail').trans (by
      unfold nativeFieldOrderConstant
      have h := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hfactor hraw) (Real.exp_nonneg (nativeZeroDisplacementSup*t))
      nlinarith))

end Zeta23.OPICAFollowup
