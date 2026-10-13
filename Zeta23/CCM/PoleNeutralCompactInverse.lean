import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# An explicit compact inverse precursor for the elementary pole operator

For a compact source with both actual elementary exponential moments zero,
the finite-primitive construction below has the same compact support and
solves u''-u/4=f when f is continuous. Its derivative is constructed too.
This is a supporting construction. General compact L2/Sobolev membership,
trace bounds and the required norm estimate remain separate obligations.
No inverse, range condition, or differential equation is accepted as a
premise about the constructed potential.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Zeta23.CCM

def nativePoleExponential (r x : ℝ) : ℂ := (Real.exp (r * x) : ℂ)

def nativePolePrimitive (s r : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∫ y : ℝ in (-s)..x, nativePoleExponential r y * f y

def nativePoleCompactInverse (s : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  nativePoleExponential (1 / 2) x * nativePolePrimitive s (-1 / 2) f x -
    nativePoleExponential (-1 / 2) x * nativePolePrimitive s (1 / 2) f x

def nativePoleCompactInverseDerivative (s : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (1 / 2 : ℂ) *
    (nativePoleExponential (1 / 2) x * nativePolePrimitive s (-1 / 2) f x +
      nativePoleExponential (-1 / 2) x * nativePolePrimitive s (1 / 2) f x)

private theorem nativePoleExponential_half_product (x : ℝ) :
    nativePoleExponential (1 / 2) x * nativePoleExponential (-1 / 2) x = 1 := by
  unfold nativePoleExponential
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  have heq : (1 / 2 : ℝ) * x + (-1 / 2 : ℝ) * x = 0 := by ring
  rw [heq, Real.exp_zero, Complex.ofReal_one]

private theorem continuous_nativePoleExponential (r : ℝ) :
    Continuous (nativePoleExponential r) :=
  Complex.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul continuous_id))

theorem hasDerivAt_nativePoleExponential (r x : ℝ) :
    HasDerivAt (nativePoleExponential r)
      ((r : ℂ) * nativePoleExponential r x) x := by
  have h := (((hasDerivAt_id x).const_mul r).exp).ofReal_comp
  change HasDerivAt (fun y : ℝ => (Real.exp (r * y) : ℂ))
    ((r : ℂ) * (Real.exp (r * x) : ℂ)) x
  simpa only [id_eq, mul_one, Complex.ofReal_mul, mul_comm] using! h

private theorem hasDerivAt_nativePolePrimitive (s r : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (x : ℝ) :
    HasDerivAt (nativePolePrimitive s r f) (nativePoleExponential r x * f x) x :=
  ((continuous_nativePoleExponential r).mul hf).integral_hasStrictDerivAt (-s) x |>.hasDerivAt

/-- The first derivative is the explicit primitive expression; the two
direct forcing terms cancel with their actual signs. -/
theorem nativePoleCompactInverse_hasDerivAt (s : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (x : ℝ) :
    HasDerivAt (nativePoleCompactInverse s f)
      (nativePoleCompactInverseDerivative s f x) x := by
  have hp := hasDerivAt_nativePoleExponential (1 / 2) x
  have hm := hasDerivAt_nativePoleExponential (-1 / 2) x
  have hA := hasDerivAt_nativePolePrimitive s (-1 / 2) hf x
  have hB := hasDerivAt_nativePolePrimitive s (1 / 2) hf x
  have h := (hp.mul hA).sub (hm.mul hB)
  convert! h using 1 <;> first
    | rfl
    | (simp only [nativePoleCompactInverse, nativePoleCompactInverseDerivative,
        Pi.mul_apply, Pi.sub_apply]
       push_cast
       ring)

/-- The derivative's derivative contains the original source with
coefficient exactly one. -/
theorem nativePoleCompactInverseDerivative_hasDerivAt (s : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (x : ℝ) :
    HasDerivAt (nativePoleCompactInverseDerivative s f)
      ((1 / 4 : ℂ) * nativePoleCompactInverse s f x + f x) x := by
  have hp := hasDerivAt_nativePoleExponential (1 / 2) x
  have hm := hasDerivAt_nativePoleExponential (-1 / 2) x
  have hA := hasDerivAt_nativePolePrimitive s (-1 / 2) hf x
  have hB := hasDerivAt_nativePolePrimitive s (1 / 2) hf x
  have h := ((hp.mul hA).add (hm.mul hB)).const_mul (1 / 2 : ℂ)
  convert! h using 1 <;> first
    | rfl
    | (simp only [nativePoleCompactInverse, nativePoleCompactInverseDerivative,
        Pi.mul_apply, Pi.add_apply]
       have he := nativePoleExponential_half_product x
       push_cast
       linear_combination -f x * he)

/-- The literal potential solves the elementary-pole equation. -/
theorem nativePoleCompactInverse_pole_equation (s : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (x : ℝ) :
    deriv (deriv (nativePoleCompactInverse s f)) x -
      (1 / 4 : ℂ) * nativePoleCompactInverse s f x = f x := by
  have hfirst : deriv (nativePoleCompactInverse s f) = nativePoleCompactInverseDerivative s f := by
    funext y
    exact (nativePoleCompactInverse_hasDerivAt s hf y).deriv
  rw [hfirst, (nativePoleCompactInverseDerivative_hasDerivAt s hf x).deriv]
  ring

theorem nativePoleCompactInverse_continuous (s : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous (nativePoleCompactInverse s f) := by
  have hdiff : Differentiable ℝ (nativePoleCompactInverse s f) :=
    fun x => (nativePoleCompactInverse_hasDerivAt s hf x).differentiableAt
  exact hdiff.continuous

theorem nativePoleCompactInverseDerivative_continuous (s : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) : Continuous (nativePoleCompactInverseDerivative s f) := by
  have hdiff : Differentiable ℝ (nativePoleCompactInverseDerivative s f) :=
    fun x => (nativePoleCompactInverseDerivative_hasDerivAt s hf x).differentiableAt
  exact hdiff.continuous

/-- Continuous sources give an actual twice continuously differentiable potential. -/
theorem nativePoleCompactInverse_contDiff_two (s : ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) : ContDiff ℝ 2 (nativePoleCompactInverse s f) := by
  have hfirst : deriv (nativePoleCompactInverse s f) = nativePoleCompactInverseDerivative s f := by
    funext x
    exact (nativePoleCompactInverse_hasDerivAt s hf x).deriv
  have hsecond : deriv (nativePoleCompactInverseDerivative s f) =
      fun x => (1 / 4 : ℂ) * nativePoleCompactInverse s f x + f x := by
    funext x
    exact (nativePoleCompactInverseDerivative_hasDerivAt s hf x).deriv
  have hD1 : ContDiff ℝ 1 (nativePoleCompactInverseDerivative s f) := by
    rw [contDiff_one_iff_deriv, hsecond]
    exact ⟨fun x => (nativePoleCompactInverseDerivative_hasDerivAt s hf x).differentiableAt,
      (continuous_const.mul (nativePoleCompactInverse_continuous s hf)).add hf⟩
  rw [show (2 : ℕ∞ω) = 1 + 1 by rfl, contDiff_succ_iff_deriv, hfirst]
  exact ⟨fun x => (nativePoleCompactInverse_hasDerivAt s hf x).differentiableAt,
    by simp, hD1⟩

private theorem nativePolePrimitive_zero_of_lt_left {s r x : ℝ} {f : ℝ → ℂ}
    (hsupport : ∀ y : ℝ, y ∉ Icc (-s) s → f y = 0) (hx : x < -s) :
    nativePolePrimitive s r f x = 0 := by
  unfold nativePolePrimitive
  rw [intervalIntegral.integral_symm]
  have hz :
      (∫ y : ℝ in x..(-s), nativePoleExponential r y * f y) =
        ∫ y : ℝ in x..(-s), (0 : ℂ) := by
    apply intervalIntegral.integral_congr_Ioo_of_le hx.le
    intro y hy
    change nativePoleExponential r y * f y = 0
    rw [hsupport y (fun hmem => (not_le_of_gt hy.2) hmem.1), mul_zero]
  rw [hz]
  simp

private theorem nativePolePrimitive_zero_of_gt_right {s r x : ℝ} {f : ℝ → ℂ}
    (hs : 0 ≤ s) (hsupport : ∀ y : ℝ, y ∉ Icc (-s) s → f y = 0)
    (hmoment : (∫ y : ℝ, nativePoleExponential r y * f y) = 0) (hx : s < x) :
    nativePolePrimitive s r f x = 0 := by
  unfold nativePolePrimitive
  rw [intervalIntegral.integral_of_le (by linarith : -s ≤ x),
    ← integral_Icc_eq_integral_Ioc]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · exact hmoment
  · intro y hy
    rw [hsupport y (fun hmem => hy ⟨hmem.1, hmem.2.trans hx.le⟩), mul_zero]

/-- Exact compact support follows from both actual elementary moments. -/
theorem nativePoleCompactInverse_zero_outside {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hsupport : ∀ y : ℝ, y ∉ Icc (-s) s → f y = 0)
    (hplus : (∫ y : ℝ, nativePoleExponential (1 / 2) y * f y) = 0)
    (hminus : (∫ y : ℝ, nativePoleExponential (-1 / 2) y * f y) = 0)
    {x : ℝ} (hx : x ∉ Icc (-s) s) :
    nativePoleCompactInverse s f x = 0 := by
  have hsplit : x < -s ∨ s < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hx
  rcases hsplit with hleft | hright
  · simp only [nativePoleCompactInverse,
      nativePolePrimitive_zero_of_lt_left hsupport hleft, mul_zero, sub_zero]
  · simp only [nativePoleCompactInverse,
      nativePolePrimitive_zero_of_gt_right hs hsupport hplus hright,
      nativePolePrimitive_zero_of_gt_right hs hsupport hminus hright, mul_zero, sub_zero]

theorem nativePoleCompactInverseDerivative_zero_outside {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hsupport : ∀ y : ℝ, y ∉ Icc (-s) s → f y = 0)
    (hplus : (∫ y : ℝ, nativePoleExponential (1 / 2) y * f y) = 0)
    (hminus : (∫ y : ℝ, nativePoleExponential (-1 / 2) y * f y) = 0)
    {x : ℝ} (hx : x ∉ Icc (-s) s) :
    nativePoleCompactInverseDerivative s f x = 0 := by
  have hsplit : x < -s ∨ s < x := by
    simpa only [mem_Icc, not_and_or, not_le] using hx
  rcases hsplit with hleft | hright
  · simp only [nativePoleCompactInverseDerivative,
      nativePolePrimitive_zero_of_lt_left hsupport hleft, mul_zero, add_zero]
  · simp only [nativePoleCompactInverseDerivative,
      nativePolePrimitive_zero_of_gt_right hs hsupport hplus hright,
      nativePolePrimitive_zero_of_gt_right hs hsupport hminus hright, mul_zero, add_zero]

theorem nativePoleCompactInverse_hasCompactSupport {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hsupport : ∀ y : ℝ, y ∉ Icc (-s) s → f y = 0)
    (hplus : (∫ y : ℝ, nativePoleExponential (1 / 2) y * f y) = 0)
    (hminus : (∫ y : ℝ, nativePoleExponential (-1 / 2) y * f y) = 0) :
    HasCompactSupport (nativePoleCompactInverse s f) := by
  apply HasCompactSupport.intro (K := Icc (-s) s) isCompact_Icc
  intro x hx
  exact nativePoleCompactInverse_zero_outside hs hsupport hplus hminus hx

theorem nativePoleCompactInverseDerivative_hasCompactSupport {s : ℝ} (hs : 0 ≤ s)
    {f : ℝ → ℂ} (hsupport : ∀ y : ℝ, y ∉ Icc (-s) s → f y = 0)
    (hplus : (∫ y : ℝ, nativePoleExponential (1 / 2) y * f y) = 0)
    (hminus : (∫ y : ℝ, nativePoleExponential (-1 / 2) y * f y) = 0) :
    HasCompactSupport (nativePoleCompactInverseDerivative s f) := by
  apply HasCompactSupport.intro (K := Icc (-s) s) isCompact_Icc
  intro x hx
  exact nativePoleCompactInverseDerivative_zero_outside hs hsupport hplus hminus hx

private theorem continuous_interval_support_traces {s : ℝ} {h : ℝ → ℂ}
    (hh : Continuous h) (hsupport : ∀ x : ℝ, x ∉ Icc (-s) s → h x = 0) :
    h (-s) = 0 ∧ h s = 0 := by
  have hclosed : IsClosed {x : ℝ | h x = 0} := isClosed_eq hh continuous_const
  constructor
  · have hleft : Iio (-s) ⊆ {x : ℝ | h x = 0} := by
      intro x hx
      exact hsupport x (fun hmem => (not_le_of_gt hx) hmem.1)
    have hclosure := hclosed.closure_subset_iff.mpr hleft
    have hend : -s ∈ closure (Iio (-s)) := by
      rw [closure_Iio, mem_Iic]
      exact (le_rfl : -s ≤ -s)
    exact hclosure hend
  · have hright : Ioi s ⊆ {x : ℝ | h x = 0} := by
      intro x hx
      exact hsupport x (fun hmem => (not_le_of_gt hx) hmem.2)
    have hclosure := hclosed.closure_subset_iff.mpr hright
    have hend : s ∈ closure (Ioi s) := by
      rw [closure_Ioi, mem_Ici]
      exact (le_rfl : s ≤ s)
    exact hclosure hend

/-- Both endpoint value and first-derivative traces are filled by the actual
constructed potential's compact support and continuity. -/
theorem nativePoleCompactInverse_clamped_traces {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : Continuous f) (hsupport : ∀ y : ℝ, y ∉ Icc (-s) s → f y = 0)
    (hplus : (∫ y : ℝ, nativePoleExponential (1 / 2) y * f y) = 0)
    (hminus : (∫ y : ℝ, nativePoleExponential (-1 / 2) y * f y) = 0) :
    nativePoleCompactInverse s f (-s) = 0 ∧ nativePoleCompactInverse s f s = 0 ∧
      deriv (nativePoleCompactInverse s f) (-s) = 0 ∧
      deriv (nativePoleCompactInverse s f) s = 0 := by
  have hv := continuous_interval_support_traces (nativePoleCompactInverse_continuous s hf)
    (fun x hx => nativePoleCompactInverse_zero_outside hs hsupport hplus hminus hx)
  have hd := continuous_interval_support_traces
    (nativePoleCompactInverseDerivative_continuous s hf)
    (fun x hx => nativePoleCompactInverseDerivative_zero_outside hs hsupport hplus hminus hx)
  refine ⟨hv.1, hv.2, ?_, ?_⟩
  · rw [(nativePoleCompactInverse_hasDerivAt s hf (-s)).deriv]
    exact hd.1
  · rw [(nativePoleCompactInverse_hasDerivAt s hf s).deriv]
    exact hd.2

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePoleCompactInverse_hasDerivAt
#print axioms Zeta23.CCM.nativePoleCompactInverseDerivative_hasDerivAt
#print axioms Zeta23.CCM.nativePoleCompactInverse_pole_equation
#print axioms Zeta23.CCM.nativePoleCompactInverse_contDiff_two
#print axioms Zeta23.CCM.nativePoleCompactInverse_zero_outside
#print axioms Zeta23.CCM.nativePoleCompactInverseDerivative_zero_outside
#print axioms Zeta23.CCM.nativePoleCompactInverse_hasCompactSupport
#print axioms Zeta23.CCM.nativePoleCompactInverse_clamped_traces
