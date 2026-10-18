import Zeta23.CCM.OriginalSincDriveDecay
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# Finite-order summation for the actual original integer drive

The normalized Bernoulli polynomials realize the bounded periodic primitive
construction. Integration by parts is performed on finitely many integer
cells, retaining and cancelling their actual endpoint values. The source
and its two weighted moment cancellations are the original fixed ones.
-/

noncomputable section

open MeasureTheory Set Filter Finset
open scoped Topology Polynomial

namespace Zeta23.CCM

private def driveEulerPolynomial (n : ℕ) (x : ℝ) : ℝ :=
  Polynomial.aeval x (Polynomial.bernoulli n) / (n.factorial : ℝ)

private theorem driveEulerPolynomial_continuous (n : ℕ) :
    Continuous (driveEulerPolynomial n) :=
  (Polynomial.bernoulli n).continuous_aeval.div_const _

private theorem driveEulerPolynomial_one (x : ℝ) :
    driveEulerPolynomial 1 x = x - 1 / 2 := by
  simp [driveEulerPolynomial, Polynomial.bernoulli_one]

private theorem driveEulerPolynomial_hasDerivAt (n : ℕ) (x : ℝ) :
    HasDerivAt (driveEulerPolynomial (n + 1)) (driveEulerPolynomial n x) x := by
  have h := ((Polynomial.bernoulli (n + 1)).hasDerivAt_aeval x).div_const
    ((n + 1).factorial : ℝ)
  have hv : Polynomial.aeval x (Polynomial.derivative (Polynomial.bernoulli (n + 1))) /
      ((n + 1).factorial : ℝ) = driveEulerPolynomial n x := by
    simp only [Polynomial.derivative_bernoulli_add_one, map_mul, map_add,
      Polynomial.aeval_natCast, map_one,
      driveEulerPolynomial, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
    field_simp
  simpa only [driveEulerPolynomial] using! h.congr_deriv hv

private theorem driveEulerPolynomial_endpoints {n : ℕ} (hn : n ≠ 1) :
    driveEulerPolynomial n 1 = driveEulerPolynomial n 0 := by
  have h0 : Polynomial.aeval (0 : ℝ) (Polynomial.bernoulli n) =
      algebraMap ℚ ℝ (_root_.bernoulli n) := by
    simpa using Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval
      (A := ℝ) (0 : ℚ) (Polynomial.bernoulli n)
  have h1 : Polynomial.aeval (1 : ℝ) (Polynomial.bernoulli n) =
      algebraMap ℚ ℝ (_root_.bernoulli' n) := by
    simpa using Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval
      (A := ℝ) (1 : ℚ) (Polynomial.bernoulli n)
  simp only [driveEulerPolynomial, h0, h1,
    _root_.bernoulli_eq_bernoulli'_of_ne_one hn]

private theorem driveEulerPolynomial_mean_zero (n : ℕ) (hn : 1 ≤ n) :
    (∫ x : ℝ in (0 : ℝ)..1, driveEulerPolynomial n x) = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => driveEulerPolynomial_hasDerivAt n x)
    ((driveEulerPolynomial_continuous n).intervalIntegrable 0 1)]
  rw [driveEulerPolynomial_endpoints (by omega), sub_self]

private theorem driveEulerPolynomial_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ Icc (0 : ℝ) 1, |driveEulerPolynomial n x| ≤ C := by
  obtain ⟨x, hx, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (s := Icc (0 : ℝ) 1) (by norm_num : (Icc (0 : ℝ) 1).Nonempty)
    (driveEulerPolynomial_continuous n).abs.continuousOn
  exact ⟨|driveEulerPolynomial n x|, abs_nonneg _, fun y hy => hmax hy⟩

private def driveEulerKernel (n : ℕ) (x : ℝ) : ℝ :=
  driveEulerPolynomial n (Int.fract x)

private theorem driveEulerKernel_periodic (n : ℕ) : Function.Periodic (driveEulerKernel n) 1 := by
  intro x
  simp only [driveEulerKernel, Int.fract_add_one]

private theorem driveEulerKernel_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |driveEulerKernel n x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := driveEulerPolynomial_bounded n
  exact ⟨C, hC, fun x => hbound (Int.fract x)
    ⟨Int.fract_nonneg x, (Int.fract_lt_one x).le⟩⟩

private theorem smooth_iterated_continuous {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) : Continuous (iteratedDeriv n f) :=
  hf.continuous_iteratedDeriv n
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl n)

private theorem smooth_iterated_hasDerivAt {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x := by
  have hfn : ContDiff ℝ (n + 1) f :=
    hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl (n + 1))
  simpa only [iteratedDeriv_succ] using! (hfn.differentiable_iteratedDeriv' n x).hasDerivAt

private def driveEulerCellSum (f : ℝ → ℝ) (n M : ℕ) : ℝ :=
  ∑ k ∈ Finset.range M, ∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ),
    driveEulerPolynomial n (x - k) * iteratedDeriv n f x

private theorem driveEulerCell_step {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n k : ℕ) :
    (∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ),
      driveEulerPolynomial n (x - k) * iteratedDeriv n f x) =
      driveEulerPolynomial (n + 1) 1 * iteratedDeriv n f (k + 1 : ℕ) -
        driveEulerPolynomial (n + 1) 0 * iteratedDeriv n f k -
          ∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ),
            driveEulerPolynomial (n + 1) (x - k) * iteratedDeriv (n + 1) f x := by
  have hP (x : ℝ) : HasDerivAt (fun y : ℝ => driveEulerPolynomial (n + 1) (y - k))
      (driveEulerPolynomial n (x - k)) x := by
    simpa using! (driveEulerPolynomial_hasDerivAt n (x - k)).comp x
      ((hasDerivAt_id x).sub_const (k : ℝ))
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (k : ℝ)) (b := (k + 1 : ℕ))
    (fun x _ => smooth_iterated_hasDerivAt hf n x) (fun x _ => hP x)
    ((smooth_iterated_continuous hf (n + 1)).intervalIntegrable _ _)
    (((driveEulerPolynomial_continuous n).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _)
  simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_left, sub_self, mul_comm] using! h

private theorem driveEulerCellSum_step {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {n : ℕ} (hn : 1 ≤ n) (M : ℕ)
    (h0 : iteratedDeriv n f 0 = 0) (hM : iteratedDeriv n f M = 0) :
    driveEulerCellSum f n M = -driveEulerCellSum f (n + 1) M := by
  have hcell (k : ℕ) :
      (∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ),
        driveEulerPolynomial n (x - k) * iteratedDeriv n f x) =
      driveEulerPolynomial (n + 1) 0 *
          (iteratedDeriv n f (k + 1 : ℕ) - iteratedDeriv n f k) -
        ∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ),
          driveEulerPolynomial (n + 1) (x - k) * iteratedDeriv (n + 1) f x := by
    rw [driveEulerCell_step hf n k, driveEulerPolynomial_endpoints (by omega)]
    ring
  unfold driveEulerCellSum
  simp_rw [hcell]
  have htel : (∑ i ∈ Finset.range M,
      (iteratedDeriv n f (i + 1 : ℕ) - iteratedDeriv n f i)) =
        iteratedDeriv n f M - iteratedDeriv n f 0 := by
    simpa using! Finset.sum_range_sub (fun k : ℕ => iteratedDeriv n f k) M
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, htel]
  simp only [h0, hM, sub_self, mul_zero, zero_sub]

private theorem driveEulerCellSum_abs_eq {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (M : ℕ)
    (hends : ∀ n : ℕ, iteratedDeriv n f 0 = 0 ∧ iteratedDeriv n f M = 0) (n : ℕ) :
    |driveEulerCellSum f (n + 1) M| = |driveEulerCellSum f 1 M| := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h := congrArg abs (driveEulerCellSum_step hf (by omega : 1 ≤ n + 1)
      M (hends (n + 1)).1 (hends (n + 1)).2)
    rw [abs_neg] at h
    exact h.symm.trans ih

private theorem driveEulerCell_one {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (k : ℕ) :
    (∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ),
      driveEulerPolynomial 1 (x - k) * iteratedDeriv 1 f x) =
      f (k + 1 : ℕ) / 2 + f k / 2 - ∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ), f x := by
  have hP (x : ℝ) : HasDerivAt (fun y : ℝ => driveEulerPolynomial 1 (y - k)) 1 x := by
    simpa only [driveEulerPolynomial_one] using!
      ((hasDerivAt_id x).sub_const (k : ℝ)).sub_const (1 / 2)
  have hfn : ContDiff ℝ 1 f :=
    hf.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 1)
  have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := (k : ℝ)) (b := (k + 1 : ℕ))
    (fun x _ => hP x) (fun x _ => (hfn.differentiable (by norm_num) x).hasDerivAt)
    intervalIntegrable_const ((hfn.continuous_deriv le_rfl).intervalIntegrable _ _)
  have he1 : driveEulerPolynomial 1 ((k + 1 : ℕ) - (k : ℝ)) = 1 / 2 := by
    rw [driveEulerPolynomial_one]
    push_cast
    ring
  have he0 : driveEulerPolynomial 1 ((k : ℝ) - k) = -(1 / 2) := by
    rw [sub_self, driveEulerPolynomial_one]
    ring
  simp only [he1, he0, one_mul] at h
  simpa [iteratedDeriv_one, div_eq_mul_inv, mul_comm] using! h

private theorem driveEulerCellSum_one {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (M : ℕ) :
    driveEulerCellSum f 1 M = (∑ k ∈ Finset.range M, f k) +
      (f M - f 0) / 2 - ∫ x : ℝ in (0 : ℝ)..M, f x := by
  have hsum : (∑ k ∈ Finset.range M,
      ∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ), f x) = ∫ x : ℝ in (0 : ℝ)..M, f x := by
    simpa only [Nat.cast_zero] using intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ)) (n := M)
      (fun k _ => hf.continuous.intervalIntegrable _ _)
  have hshift : (∑ k ∈ Finset.range M, f (k + 1 : ℕ)) -
      (∑ k ∈ Finset.range M, f k) = f M - f 0 := by
    rw [← Finset.sum_sub_distrib]
    simpa using! Finset.sum_range_sub (fun k : ℕ => f k) M
  unfold driveEulerCellSum
  simp_rw [driveEulerCell_one hf]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_div,
    ← Finset.sum_div, hsum]
  linarith

private theorem driveEulerCellSum_bound {f : ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (n M : ℕ) {C : ℝ}
    (hC : ∀ x ∈ Icc (0 : ℝ) 1, |driveEulerPolynomial n x| ≤ C) :
    |driveEulerCellSum f n M| ≤
      C * ∫ x : ℝ in (0 : ℝ)..M, |iteratedDeriv n f x| := by
  have hcell (k : ℕ) :
      |∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ),
        driveEulerPolynomial n (x - k) * iteratedDeriv n f x| ≤
        C * ∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ), |iteratedDeriv n f x| := by
    have hle : (k : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.le_succ k
    have hp : Continuous (fun x : ℝ => driveEulerPolynomial n (x - k)) :=
      (driveEulerPolynomial_continuous n).comp (continuous_id.sub continuous_const)
    calc
      _ ≤ ∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ),
          |driveEulerPolynomial n (x - k) * iteratedDeriv n f x| :=
        intervalIntegral.abs_integral_le_integral_abs hle
      _ ≤ ∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ), C * |iteratedDeriv n f x| := by
        apply intervalIntegral.integral_mono_on hle
          ((hp.mul (smooth_iterated_continuous hf n)).abs.intervalIntegrable _ _)
          (((smooth_iterated_continuous hf n).abs.const_mul C).intervalIntegrable _ _)
        intro x hx
        change |driveEulerPolynomial n (x - k) * iteratedDeriv n f x| ≤
          C * |iteratedDeriv n f x|
        rw [abs_mul]
        apply mul_le_mul_of_nonneg_right (hC (x - k) ?_) (abs_nonneg _)
        constructor
        · linarith [hx.1]
        · have hupper := hx.2
          push_cast at hupper
          linarith
      _ = _ := intervalIntegral.integral_const_mul _ _
  have hsum : (∑ k ∈ Finset.range M,
      ∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ), |iteratedDeriv n f x|) =
        ∫ x : ℝ in (0 : ℝ)..M, |iteratedDeriv n f x| := by
    simpa only [Nat.cast_zero] using intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ => (k : ℝ)) (n := M)
      (fun k _ => (smooth_iterated_continuous hf n).abs.intervalIntegrable _ _)
  unfold driveEulerCellSum
  calc
    _ ≤ ∑ k ∈ Finset.range M,
        |∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ),
          driveEulerPolynomial n (x - k) * iteratedDeriv n f x| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range M,
        C * ∫ x : ℝ in (k : ℝ)..(k + 1 : ℕ), |iteratedDeriv n f x| :=
      Finset.sum_le_sum (fun k _ => hcell k)
    _ = _ := by rw [← Finset.mul_sum, hsum]

private theorem driveFiniteOrderSummationBound (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) f →
      ∀ M : ℕ, (∀ j : ℕ, iteratedDeriv j f 0 = 0 ∧ iteratedDeriv j f M = 0) →
      |(∑ k ∈ Finset.range M, f k) - ∫ x : ℝ in (0 : ℝ)..M, f x| ≤
        C * ∫ x : ℝ in (0 : ℝ)..M, |iteratedDeriv n f x| := by
  obtain ⟨C, hCnonneg, hC⟩ := driveEulerPolynomial_bounded n
  refine ⟨C, hCnonneg, ?_⟩
  intro f hf M hends
  have hbase := driveEulerCellSum_one hf M
  have hz := hends 0
  simp only [iteratedDeriv_zero] at hz
  rw [hz.1, hz.2, sub_self, zero_div, add_zero] at hbase
  have hn' : n - 1 + 1 = n := by omega
  have habs := driveEulerCellSum_abs_eq hf M hends (n - 1)
  rw [hn', hbase] at habs
  rw [← habs]
  exact driveEulerCellSum_bound hf n M hC

private def driveA : ℕ → ℝ → ℝ
  | 0 => nativeOriginalSource
  | n + 1 => fun u => -((n : ℝ) + 1 / 2) * driveA n u - deriv (driveA n) u

private def driveB : ℕ → ℝ → ℝ
  | 0 => fun _ => 0
  | n + 1 => fun u => driveA n u - ((n : ℝ) + 1 / 2) * driveB n u - deriv (driveB n) u

private theorem driveA_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (driveA n) := by
  induction n with
  | zero => exact nativeOriginalSource_contDiff
  | succ n ih =>
    exact (contDiff_const.mul ih).sub (contDiff_infty_iff_deriv.mp ih).2

private theorem driveB_smooth (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (driveB n) := by
  induction n with
  | zero => exact contDiff_const
  | succ n ih =>
    exact ((driveA_smooth n).sub (contDiff_const.mul ih)).sub
      (contDiff_infty_iff_deriv.mp ih).2

private theorem drive_supported_deriv {f : ℝ → ℝ}
    (hf : ∀ x ∉ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale, f x = 0) :
    ∀ x ∉ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale, deriv f x = 0 := by
  intro x hx
  have heq : f =ᶠ[𝓝 x] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [isClosed_Icc.isOpen_compl.mem_nhds hx] with y hy
    exact hf y hy
  rw [heq.deriv_eq, deriv_const]

private theorem driveAB_supported (n : ℕ) :
    (∀ x ∉ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale, driveA n x = 0) ∧
    (∀ x ∉ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale, driveB n x = 0) := by
  induction n with
  | zero => exact ⟨nativeOriginalSource_supported, fun _ _ => rfl⟩
  | succ n ih =>
    constructor
    · intro x hx
      simp only [driveA, ih.1 x hx, drive_supported_deriv ih.1 x hx, mul_zero, sub_zero]
    · intro x hx
      simp only [driveB, ih.1 x hx, ih.2 x hx, drive_supported_deriv ih.2 x hx,
        mul_zero, sub_zero]

private def driveOrderProfile (n : ℕ) (t x : ℝ) : ℝ :=
  Real.exp (-((n : ℝ) + 1 / 2) * Real.log x) *
    (Real.log x * driveA n (t - Real.log x) + driveB n (t - Real.log x))

private theorem driveOrderProfile_hasDerivAt (n : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (driveOrderProfile n t) (driveOrderProfile (n + 1) t x) x := by
  have hlog := Real.hasDerivAt_log hx.ne'
  have harg := (hasDerivAt_const x t).sub hlog
  have hA := ((driveA_smooth n).differentiable (by norm_num)
    (t - Real.log x)).hasDerivAt.comp x harg
  have hB := ((driveB_smooth n).differentiable (by norm_num)
    (t - Real.log x)).hasDerivAt.comp x harg
  have hE := (hlog.const_mul (-((n : ℝ) + 1 / 2))).exp
  have hraw := hE.mul ((hlog.mul hA).add hB)
  have hexp : Real.exp (-(((n + 1 : ℕ) : ℝ) + 1 / 2) * Real.log x) =
      Real.exp (-((n : ℝ) + 1 / 2) * Real.log x) * x⁻¹ := by
    calc
      _ = Real.exp (-((n : ℝ) + 1 / 2) * Real.log x + -Real.log x) := by
        congr 1
        push_cast
        ring
      _ = _ := by rw [Real.exp_add, Real.exp_neg, Real.exp_log hx]
  convert! hraw using 1
  dsimp only [driveOrderProfile, Function.comp_apply, Pi.mul_apply, Pi.add_apply, Pi.sub_apply]
  rw [hexp]
  simp only [driveA, driveB]
  ring

private theorem drive_sqrt_exp_half (y : ℝ) :
    Real.sqrt (Real.exp y) = Real.exp (y / 2) := by
  have h : Real.exp y = Real.exp (y / 2) * Real.exp (y / 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [h, Real.sqrt_mul_self (Real.exp_pos _).le]

private theorem driveSummand_iteratedDeriv (n : ℕ) (t : ℝ) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv n (nativeOriginalLogDriveSummand t) x = driveOrderProfile n t x := by
  induction n generalizing x with
  | zero =>
    have hs : Real.sqrt x = Real.exp (Real.log x / 2) := by
      simpa only [Real.exp_log hx] using drive_sqrt_exp_half (Real.log x)
    simp only [iteratedDeriv_zero, nativeOriginalLogDriveSummand, if_pos hx,
      driveOrderProfile, driveA, driveB, Nat.cast_zero, zero_add, add_zero]
    rw [hs, div_eq_mul_inv, ← Real.exp_neg]
    have he : -(Real.log x / 2) = -(1 / 2 : ℝ) * Real.log x := by ring
    rw [he]
    ring
  | succ n ih =>
    have heq : iteratedDeriv n (nativeOriginalLogDriveSummand t) =ᶠ[𝓝 x]
        driveOrderProfile n t := by
      filter_upwards [isOpen_Ioi.eventually_mem hx] with y hy
      exact ih hy
    rw [iteratedDeriv_succ, heq.deriv_eq]
    exact (driveOrderProfile_hasDerivAt n t hx).deriv

private theorem driveSummand_iterated_zero_below (n : ℕ) {t x : ℝ}
    (hx : x < Real.exp (t - UniversalSinc.fixedScale)) :
    iteratedDeriv n (nativeOriginalLogDriveSummand t) x = 0 := by
  have heq : nativeOriginalLogDriveSummand t =ᶠ[𝓝 x] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.eventually_mem hx] with y hy
    exact nativeOriginalLogDriveSummand_zero_below hy
  simpa using heq.iteratedDeriv_eq n

private theorem driveSummand_iterated_zero_above (n : ℕ) {t x : ℝ}
    (hx : Real.exp (t + UniversalSinc.fixedScale) < x) :
    iteratedDeriv n (nativeOriginalLogDriveSummand t) x = 0 := by
  have heq : nativeOriginalLogDriveSummand t =ᶠ[𝓝 x] fun _ : ℝ => (0 : ℝ) := by
    filter_upwards [isOpen_Ioi.eventually_mem hx] with y hy
    exact nativeOriginalLogDriveSummand_zero_above hy
  simpa using heq.iteratedDeriv_eq n

private theorem driveSummand_iterated_compact (n : ℕ) (t : ℝ) :
    HasCompactSupport (iteratedDeriv n (nativeOriginalLogDriveSummand t)) := by
  induction n with
  | zero => exact nativeOriginalLogDriveSummand_hasCompactSupport t
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv

private theorem driveFiniteOrderSummation_actual (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ,
      |nativeOriginalIntegerDrive t| ≤
        C * ∫ x : ℝ, |iteratedDeriv n (nativeOriginalLogDriveSummand t) x| := by
  obtain ⟨C, hC, hbound⟩ := driveFiniteOrderSummationBound n hn
  refine ⟨C, hC, ?_⟩
  intro t
  let M : ℕ := ⌊Real.exp (t + UniversalSinc.fixedScale)⌋₊ + 1
  have hM : Real.exp (t + UniversalSinc.fixedScale) < (M : ℝ) :=
    by simpa only [M, Nat.cast_add, Nat.cast_one] using!
      Nat.lt_floor_add_one (Real.exp (t + UniversalSinc.fixedScale))
  have hMnonneg : (0 : ℝ) ≤ M := by positivity
  have hends : ∀ j : ℕ, iteratedDeriv j (nativeOriginalLogDriveSummand t) 0 = 0 ∧
      iteratedDeriv j (nativeOriginalLogDriveSummand t) M = 0 := fun j =>
    ⟨driveSummand_iterated_zero_below j (Real.exp_pos _),
      driveSummand_iterated_zero_above j hM⟩
  have hsum : (∑ k ∈ Finset.range M, nativeOriginalLogDriveSummand t k) =
      nativeOriginalIntegerDrive t := by
    rw [nativeOriginalIntegerDrive_eq_history_sum (T := t) le_rfl]
    apply Finset.sum_congr rfl
    intro k hk
    exact nativeOriginalLogDriveSummand_at_nat t k
  have hint : (∫ x : ℝ in (0 : ℝ)..M, nativeOriginalLogDriveSummand t x) = 0 := by
    rw [intervalIntegral.integral_of_le hMnonneg,
      setIntegral_eq_integral_of_forall_compl_eq_zero (by
        intro x hx
        by_cases hpos : 0 < x
        · have hhigh : (M : ℝ) < x := lt_of_not_ge (fun h => hx ⟨hpos, h⟩)
          exact nativeOriginalLogDriveSummand_zero_above (hM.trans hhigh)
        · exact nativeOriginalLogDriveSummand_zero_below
            ((le_of_not_gt hpos).trans_lt (Real.exp_pos _))),
      nativeOriginalLogDriveSummand_integral_zero]
  have h := hbound (nativeOriginalLogDriveSummand t)
    (nativeOriginalLogDriveSummand_contDiff t) M hends
  rw [hsum, hint, sub_zero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hC
  rw [intervalIntegral.integral_of_le hMnonneg]
  exact setIntegral_le_integral
    ((smooth_iterated_continuous (nativeOriginalLogDriveSummand_contDiff t) n).abs
      |>.integrable_of_hasCompactSupport (driveSummand_iterated_compact n t).abs)
    (Filter.Eventually.of_forall fun x => abs_nonneg _)

private def driveExponentialProfile (n : ℕ) (t u : ℝ) : ℝ :=
  Real.exp (-(((n : ℝ) - 1 / 2) * (t - u))) *
    ((t - u) * driveA n u + driveB n u)

private theorem driveSummand_iterated_exp (n : ℕ) (t y : ℝ) :
    Real.exp y * iteratedDeriv n (nativeOriginalLogDriveSummand t) (Real.exp y) =
      driveExponentialProfile n t (t - y) := by
  rw [driveSummand_iteratedDeriv n t (Real.exp_pos y)]
  unfold driveOrderProfile driveExponentialProfile
  rw [Real.log_exp, sub_sub_cancel]
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  ring

private theorem driveSummand_iterated_integral_eq (n : ℕ) (t : ℝ) :
    (∫ x : ℝ, |iteratedDeriv n (nativeOriginalLogDriveSummand t) x|) =
      ∫ u : ℝ, |driveExponentialProfile n t u| := by
  let a : ℝ := t - UniversalSinc.fixedScale - 1
  let D : ℝ → ℝ := fun x => |iteratedDeriv n (nativeOriginalLogDriveSummand t) x|
  let H : ℝ → ℝ := fun y => Real.exp y * D (Real.exp y)
  have hD : (∫ x : ℝ in Ioi (Real.exp a), D x) = ∫ x : ℝ, D x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hxlow : x < Real.exp (t - UniversalSinc.fixedScale) :=
      (le_of_not_gt hx).trans_lt (Real.exp_lt_exp.mpr (by dsimp [a]; linarith))
    dsimp only [D]
    rw [driveSummand_iterated_zero_below n hxlow, abs_zero]
  have hH : (∫ y : ℝ in Ioi a, H y) = ∫ y : ℝ, H y := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hxlow : Real.exp y < Real.exp (t - UniversalSinc.fixedScale) := by
      apply Real.exp_lt_exp.mpr
      have hyle : y ≤ a := le_of_not_gt hy
      dsimp only [a] at hyle
      linarith
    dsimp only [H, D]
    rw [driveSummand_iterated_zero_below n hxlow, abs_zero, mul_zero]
  have hsub := integral_comp_exp_Ioi D a
  change (∫ y : ℝ in Ioi a, H y) = ∫ x : ℝ in Ioi (Real.exp a), D x at hsub
  rw [hD, hH] at hsub
  change (∫ x : ℝ, D x) = _
  rw [← hsub, ← integral_sub_left_eq_self H volume t]
  apply integral_congr_ae
  filter_upwards with u
  dsimp only [H, D]
  calc
    _ = |Real.exp (t - u) *
        iteratedDeriv n (nativeOriginalLogDriveSummand t) (Real.exp (t - u))| := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    _ = _ := by rw [driveSummand_iterated_exp, sub_sub_cancel]

private theorem drive_compact_of_supported {f : ℝ → ℝ}
    (hf : ∀ x ∉ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale, f x = 0) :
    HasCompactSupport f :=
  HasCompactSupport.intro isCompact_Icc hf

private theorem driveAB_norm_integrable (n : ℕ) :
    Integrable (fun u : ℝ => |driveA n u| + |driveB n u|) :=
  (((driveA_smooth n).continuous.integrable_of_hasCompactSupport
    (drive_compact_of_supported (driveAB_supported n).1)).abs).add
      (((driveB_smooth n).continuous.integrable_of_hasCompactSupport
        (drive_compact_of_supported (driveAB_supported n).2)).abs)

private theorem driveExponentialProfile_integrable (n : ℕ) (t : ℝ) :
    Integrable (driveExponentialProfile n t) := by
  have hE : Continuous (fun u : ℝ => Real.exp (-(((n : ℝ) - 1 / 2) * (t - u)))) := by
    fun_prop
  unfold driveExponentialProfile
  exact (hE.mul (((continuous_const.sub continuous_id).mul (driveA_smooth n).continuous).add
    (driveB_smooth n).continuous)).integrable_of_hasCompactSupport
      (((drive_compact_of_supported (driveAB_supported n).1).mul_left.add
        (drive_compact_of_supported (driveAB_supported n).2)).mul_left)

private def driveOrderDecayConstant (n : ℕ) : ℝ :=
  Real.exp (((n : ℝ) - 1 / 2) * UniversalSinc.fixedScale) *
    ∫ u : ℝ, |driveA n u| + |driveB n u|

private theorem driveOrderDecayConstant_nonneg (n : ℕ) :
    0 ≤ driveOrderDecayConstant n := by
  apply mul_nonneg (Real.exp_pos _).le
  exact integral_nonneg fun u => add_nonneg (abs_nonneg _) (abs_nonneg _)

private theorem driveExponentialProfile_bound {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) (u : ℝ) :
    |driveExponentialProfile n t u| ≤
      (Real.exp (((n : ℝ) - 1 / 2) * UniversalSinc.fixedScale) *
        (1 + t + UniversalSinc.fixedScale) * Real.exp (-((n : ℝ) - 1 / 2) * t)) *
          (|driveA n u| + |driveB n u|) := by
  by_cases hu : u ∈ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale
  · have hs : 0 ≤ UniversalSinc.fixedScale := UniversalSinc.fixedScale_pos.le
    have halpha : 0 ≤ (n : ℝ) - 1 / 2 := by
      have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have habs : |t - u| ≤ t + UniversalSinc.fixedScale := by
      apply abs_le.mpr
      constructor <;> linarith [hu.1, hu.2]
    have hcoeff : |t - u| ≤ 1 + t + UniversalSinc.fixedScale := by linarith
    have hC : 0 ≤ 1 + t + UniversalSinc.fixedScale := by linarith
    have hone : 1 ≤ 1 + t + UniversalSinc.fixedScale := by linarith
    have hcore : |(t - u) * driveA n u + driveB n u| ≤
        (1 + t + UniversalSinc.fixedScale) * (|driveA n u| + |driveB n u|) := by
      calc
        _ ≤ |(t - u) * driveA n u| + |driveB n u| := abs_add_le _ _
        _ = |t - u| * |driveA n u| + 1 * |driveB n u| := by rw [abs_mul, one_mul]
        _ ≤ (1 + t + UniversalSinc.fixedScale) * |driveA n u| +
            (1 + t + UniversalSinc.fixedScale) * |driveB n u| :=
          add_le_add (mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _))
            (mul_le_mul_of_nonneg_right hone (abs_nonneg _))
        _ = _ := by ring
    have hexp : Real.exp (-(((n : ℝ) - 1 / 2) * (t - u))) ≤
        Real.exp (-((n : ℝ) - 1 / 2) * t) *
          Real.exp (((n : ℝ) - 1 / 2) * UniversalSinc.fixedScale) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_left hu.2 halpha]
    unfold driveExponentialProfile
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(((n : ℝ) - 1 / 2) * (t - u))) *
          ((1 + t + UniversalSinc.fixedScale) * (|driveA n u| + |driveB n u|)) :=
        mul_le_mul_of_nonneg_left hcore (Real.exp_pos _).le
      _ ≤ (Real.exp (-((n : ℝ) - 1 / 2) * t) *
          Real.exp (((n : ℝ) - 1 / 2) * UniversalSinc.fixedScale)) *
            ((1 + t + UniversalSinc.fixedScale) * (|driveA n u| + |driveB n u|)) :=
        mul_le_mul_of_nonneg_right hexp
          (mul_nonneg hC (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      _ = _ := by ring
  · simp only [driveExponentialProfile, (driveAB_supported n).1 u hu,
      (driveAB_supported n).2 u hu, mul_zero, zero_add, abs_zero, le_refl]

private theorem driveSummand_iterated_integral_bound {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ x : ℝ, |iteratedDeriv n (nativeOriginalLogDriveSummand t) x|) ≤
      driveOrderDecayConstant n * (1 + t + UniversalSinc.fixedScale) *
        Real.exp (-((n : ℝ) - 1 / 2) * t) := by
  rw [driveSummand_iterated_integral_eq]
  have h := integral_mono (driveExponentialProfile_integrable n t).abs
    ((driveAB_norm_integrable n).const_mul
      (Real.exp (((n : ℝ) - 1 / 2) * UniversalSinc.fixedScale) *
        (1 + t + UniversalSinc.fixedScale) * Real.exp (-((n : ℝ) - 1 / 2) * t)))
    (driveExponentialProfile_bound hn ht)
  rw [integral_const_mul] at h
  calc
    _ ≤ _ := h
    _ = _ := by unfold driveOrderDecayConstant; ring

/-- Every finite derivative order supplies its genuine source-only rate.
The two actual weighted source moments cancel the continuum term internally. -/
theorem nativeOriginalIntegerDrive_finiteOrder_bound (n : ℕ) (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 0 ≤ t →
      |nativeOriginalIntegerDrive t| ≤
        C * (1 + t + UniversalSinc.fixedScale) * Real.exp (-((n : ℝ) - 1 / 2) * t) := by
  obtain ⟨C, hC, hbound⟩ := driveFiniteOrderSummation_actual n hn
  refine ⟨C * driveOrderDecayConstant n,
    mul_nonneg hC (driveOrderDecayConstant_nonneg n), ?_⟩
  intro t ht
  calc
    _ ≤ C * ∫ x : ℝ, |iteratedDeriv n (nativeOriginalLogDriveSummand t) x| := hbound t
    _ ≤ C * (driveOrderDecayConstant n * (1 + t + UniversalSinc.fixedScale) *
        Real.exp (-((n : ℝ) - 1 / 2) * t)) :=
      mul_le_mul_of_nonneg_left (driveSummand_iterated_integral_bound hn ht) hC
    _ = _ := by ring

/-- The original literal integer drive decays at every prescribed fixed
exponential rate. Constants depend only on that rate and the fixed source.
This does not assert the optional optimized Gevrey double-exponential rate. -/
theorem nativeOriginalIntegerDrive_rapid_bound (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ T : ℝ, 0 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      |nativeOriginalIntegerDrive t| ≤ C * Real.exp (-A * t) := by
  let n : ℕ := ⌈A + 2⌉₊
  have hceil : A + 2 ≤ (n : ℝ) := Nat.le_ceil _
  have hn : 1 ≤ n := by
    have hn' : (1 : ℝ) ≤ n := by linarith
    exact_mod_cast hn'
  let d : ℝ := (n : ℝ) - 1 / 2 - A
  have hd : 0 < d := by dsimp [d]; linarith
  have hs0 : 0 ≤ UniversalSinc.fixedScale := UniversalSinc.fixedScale_pos.le
  obtain ⟨C, hC, hbound⟩ := nativeOriginalIntegerDrive_finiteOrder_bound n hn
  have hfactor : 0 ≤ 1 + UniversalSinc.fixedScale + 1 / d := by
    positivity
  refine ⟨C * (1 + UniversalSinc.fixedScale + 1 / d) + 1,
    by positivity, max UniversalSinc.fixedScale 0, le_max_right _ _, ?_⟩
  intro t ht
  have ht0 : 0 ≤ t := (le_max_right _ _).trans ht
  have he : Real.exp (-d * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le) ht0
  have hte : t * Real.exp (-d * t) ≤ 1 / d := by
    apply (le_div_iff₀ hd).mpr
    calc
      _ = (d * t) * Real.exp (-(d * t)) := by ring
      _ ≤ Real.exp (-1) := Real.mul_exp_neg_le_exp_neg_one _
      _ ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hpoly : (1 + t + UniversalSinc.fixedScale) * Real.exp (-d * t) ≤
      1 + UniversalSinc.fixedScale + 1 / d := by
    have hs : 0 ≤ 1 + UniversalSinc.fixedScale := by positivity
    have h := mul_le_mul_of_nonneg_left he hs
    nlinarith
  have hexp : Real.exp (-((n : ℝ) - 1 / 2) * t) =
      Real.exp (-A * t) * Real.exp (-d * t) := by
    rw [← Real.exp_add]
    congr 1
    dsimp [d]
    ring
  calc
    _ ≤ C * (1 + t + UniversalSinc.fixedScale) *
        Real.exp (-((n : ℝ) - 1 / 2) * t) := hbound t ht0
    _ = (C * ((1 + t + UniversalSinc.fixedScale) * Real.exp (-d * t))) *
        Real.exp (-A * t) := by rw [hexp]; ring
    _ ≤ (C * (1 + UniversalSinc.fixedScale + 1 / d)) * Real.exp (-A * t) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hC) (Real.exp_pos _).le
    _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeOriginalIntegerDrive_finiteOrder_bound
#print axioms Zeta23.CCM.nativeOriginalIntegerDrive_rapid_bound
