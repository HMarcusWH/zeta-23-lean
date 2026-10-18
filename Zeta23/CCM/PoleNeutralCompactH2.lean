import Zeta23.CCM.PoleNeutralCompactL2Energy
import Mathlib.Analysis.Calculus.Deriv.Support

/-!
# A concrete compact H2 solution for general pole-neutral L2 input

The weak derivative interface uses actual global integral identities against
compact C1 tests. Values, first jets, clamped traces, support, L2 membership,
absolute continuity and both a.e. equations are all constructed from the
finite primitives, rather than supplied inverse or Sobolev assumptions.
-/

noncomputable section

open Set MeasureTheory
open scoped Topology

namespace Zeta23.CCM

private theorem supported_intervalIntegral {s : ℝ} (hs : 0 ≤ s)
    {v : ℝ → ℂ} (hv : ∀ x, x ∉ Icc (-s) s → v x = 0) :
    (∫ x in (-s)..s, v x) = ∫ x : ℝ, v x := by
  rw [intervalIntegral.integral_of_le (by linarith : -s ≤ s), ← integral_Icc_eq_integral_Ioc]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hv

/-- Concrete one-dimensional H2 data, including weak derivatives and
continuous clamped representatives. This contains no inverse estimate or
uniqueness assertion as a field. -/
structure NativeCompactPoleH2 (s : ℝ) (f : ℝ → ℂ) where
  value : ℝ → ℂ
  first : ℝ → ℂ
  value_continuous : Continuous value
  first_continuous : Continuous first
  value_ac : AbsolutelyContinuousOnInterval value (-s) s
  first_ac : AbsolutelyContinuousOnInterval first (-s) s
  value_l2 : MemLp value 2 volume
  first_l2 : MemLp first 2 volume
  second_l2 : MemLp (fun x => (1 / 4 : ℂ) * value x + f x) 2 volume
  value_support : ∀ x, x ∉ Icc (-s) s → value x = 0
  first_support : ∀ x, x ∉ Icc (-s) s → first x = 0
  value_clamped : value (-s) = 0 ∧ value s = 0
  first_clamped : first (-s) = 0 ∧ first s = 0
  value_derivative : ∀ᵐ x : ℝ, HasDerivAt value (first x) x
  first_derivative : ∀ᵐ x : ℝ, HasDerivAt first ((1 / 4 : ℂ) * value x + f x) x

def nativePoleCompactH2 {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ} (hf : MemLp f 2 volume)
    (hsupport : ∀ x : ℝ, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    NativeCompactPoleH2 s f where
  value := nativePoleCompactInverse s f
  first := nativePoleCompactInverseDerivative s f
  value_continuous := nativePoleCompactInverse_continuous_of_memLp s hf
  first_continuous := nativePoleCompactInverseDerivative_continuous_of_memLp s hf
  value_ac := (nativePoleCompactInverse_jet_absolutelyContinuous s hf).1
  first_ac := (nativePoleCompactInverse_jet_absolutelyContinuous s hf).2
  value_l2 := (nativePoleCompactInverse_memLp_jet_representatives hs hf hsupport hplus hminus).1
  first_l2 := (nativePoleCompactInverse_memLp_jet_representatives hs hf hsupport hplus hminus).2.1
  second_l2 := (nativePoleCompactInverse_memLp_jet_representatives hs hf hsupport hplus hminus).2.2
  value_support := fun _ hx => nativePoleCompactInverse_zero_outside hs hsupport hplus hminus hx
  first_support := fun _ hx => nativePoleCompactInverseDerivative_zero_outside hs hsupport hplus hminus hx
  value_clamped := (nativePoleCompactInverse_memLp_clamped_values hs hf hsupport hplus hminus).imp
    id (fun h => h.1)
  first_clamped := (nativePoleCompactInverse_memLp_clamped_values hs hf hsupport hplus hminus).2.2
  value_derivative := nativePoleCompactInverse_ae_hasDerivAt s hf
  first_derivative := nativePoleCompactInverseDerivative_ae_hasDerivAt s hf

private theorem weakDerivative_of_clamped_ac {s : ℝ} (hs : 0 ≤ s)
    {u d : ℝ → ℂ} (hu : MemLp u 2 volume) (hd : MemLp d 2 volume)
    (huAC : AbsolutelyContinuousOnInterval u (-s) s)
    (hsupport : ∀ x, x ∉ Icc (-s) s → u x = 0)
    (hdsupport : ∀ x, x ∉ Icc (-s) s → d x = 0)
    (hclamp : u (-s) = 0 ∧ u s = 0)
    (hderiv : ∀ᵐ x : ℝ, HasDerivAt u (d x) x)
    {φ : ℝ → ℂ} (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ) :
    (∫ x : ℝ, u x * deriv φ x) = -(∫ x : ℝ, d x * φ x) := by
  have hφl : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hφs
  have hφdl : MemLp (deriv φ) 2 volume :=
    hφ.continuous_deriv_one.memLp_of_hasCompactSupport hφs.deriv
  have h1 : Integrable (fun x : ℝ => d x * φ x) := hd.integrable_mul hφl
  have h2 : Integrable (fun x : ℝ => u x * deriv φ x) := hu.integrable_mul hφdl
  have hAC : AbsolutelyContinuousOnInterval (fun x : ℝ => u x * φ x) (-s) s := by
    simpa only [Pi.smul_apply, smul_eq_mul] using!
      huAC.smul hφ.contDiffOn.absolutelyContinuousOnInterval
  have hAE : ∀ᵐ x : ℝ, x ∈ uIcc (-s) s →
      HasDerivAt (fun x : ℝ => u x * φ x) (d x * φ x + u x * deriv φ x) x := by
    filter_upwards [hderiv] with x hx _
    exact hx.mul ((hφ.differentiable (by norm_num) x).hasDerivAt)
  have hFTC := complex_integral_eq_sub_of_ac_ae hAC (h1.add h2).intervalIntegrable hAE
  simp only [hclamp.1, hclamp.2, zero_mul, sub_self] at hFTC
  change (∫ x in (-s)..s, d x * φ x + u x * deriv φ x) = 0 at hFTC
  rw [intervalIntegral.integral_add h1.intervalIntegrable h2.intervalIntegrable,
    supported_intervalIntegral hs (v := fun x => d x * φ x)
      (fun x hx => by rw [hdsupport x hx, zero_mul]),
    supported_intervalIntegral hs (v := fun x => u x * deriv φ x)
      (fun x hx => by rw [hsupport x hx, zero_mul])] at hFTC
  linear_combination hFTC

theorem NativeCompactPoleH2.weak_first {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (u : NativeCompactPoleH2 s f) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ) :
    (∫ x : ℝ, u.value x * deriv φ x) = -(∫ x : ℝ, u.first x * φ x) :=
  weakDerivative_of_clamped_ac hs u.value_l2 u.first_l2 u.value_ac
    u.value_support u.first_support u.value_clamped u.value_derivative hφ hφs

theorem NativeCompactPoleH2.weak_second {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hfSupport : ∀ x, x ∉ Icc (-s) s → f x = 0)
    (u : NativeCompactPoleH2 s f) {φ : ℝ → ℂ}
    (hφ : ContDiff ℝ 1 φ) (hφs : HasCompactSupport φ) :
    (∫ x : ℝ, u.first x * deriv φ x) =
      -(∫ x : ℝ, ((1 / 4 : ℂ) * u.value x + f x) * φ x) := by
  apply weakDerivative_of_clamped_ac hs u.first_l2 u.second_l2 u.first_ac
    u.first_support (fun x hx => ?_) u.first_clamped u.first_derivative hφ hφs
  rw [u.value_support x hx, hfSupport x hx, mul_zero, add_zero]

/-- The constructed H2 solution carries the genuine sharp L2 estimate. -/
theorem nativePoleCompactH2_norm_bound {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℂ}
    (hf : MemLp f 2 volume) (hsupport : ∀ x, x ∉ Icc (-s) s → f x = 0)
    (hplus : (∫ x : ℝ, nativePoleExponential (1 / 2) x * f x) = 0)
    (hminus : (∫ x : ℝ, nativePoleExponential (-1 / 2) x * f x) = 0) :
    (eLpNorm (nativePoleCompactH2 hs hf hsupport hplus hminus).value 2 volume).toReal ≤
      4 * (eLpNorm f 2 volume).toReal :=
  nativePoleCompactInverse_l2_norm_le_four_of_memLp hs hf hsupport hplus hminus

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePoleCompactH2
#print axioms Zeta23.CCM.NativeCompactPoleH2.weak_first
#print axioms Zeta23.CCM.NativeCompactPoleH2.weak_second
#print axioms Zeta23.CCM.nativePoleCompactH2_norm_bound
