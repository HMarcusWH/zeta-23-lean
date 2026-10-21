import Zeta23.CCM.NativeCausalLaplaceDerivatives
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Topology.Connected.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Actual weighted L2 data and its half-plane Laplace integral

The weighted membership is an ordinary `MemLp` premise on the actual source.
No pole exclusion, derivative estimate, or rate is included in the data.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace Zeta23.OPICA

open Zeta23.CCM

def weightedCausalProfile (epsilon : ℝ) (f : ℝ → ℂ) : ℝ → ℂ :=
  (Ici (0 : ℝ)).indicator (fun t => Complex.exp (-(epsilon : ℂ) * (t : ℂ)) * f t)

structure WeightedL2Data where
  source : ℝ → ℂ
  epsilon : ℝ
  weighted_memLp : MemLp (weightedCausalProfile epsilon source) 2 volume

def WeightedL2Data.causalVector (f : WeightedL2Data) : nativeCompletionCausalL2 :=
  ⟨f.weighted_memLp.toLp (weightedCausalProfile f.epsilon f.source), by
    filter_upwards [f.weighted_memLp.coeFn_toLp] with t ht
    intro htneg
    rw [ht]
    exact indicator_of_notMem (not_le.mpr htneg) _⟩

def weightedLaplace (f : WeightedL2Data) (z : ℂ) : ℂ :=
  ∫ t : ℝ in Ici (0 : ℝ), Complex.exp (-z * (t : ℂ)) * f.source t

theorem weightedLaplace_eq_causalMoment (f : WeightedL2Data) (z : ℂ) :
    weightedLaplace f z = nativeCausalLaplaceMoment (z - (f.epsilon : ℂ)) 0
      (f.causalVector : NativeCompletionL2) := by
  unfold weightedLaplace nativeCausalLaplaceMoment
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards [f.weighted_memLp.coeFn_toLp] with t ht
  change _ = (t : ℂ) ^ 0 * Complex.exp (-(z - (f.epsilon : ℂ)) * (t : ℂ)) *
    f.weighted_memLp.toLp (weightedCausalProfile f.epsilon f.source) t
  rw [ht, pow_zero, one_mul]
  by_cases hpos : t ∈ Ici (0 : ℝ)
  · simp only [weightedCausalProfile, indicator_of_mem hpos]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  · simp only [weightedCausalProfile, indicator_of_notMem hpos, mul_zero]

theorem laplace_holomorphic_of_weighted_L2 (f : WeightedL2Data) (z : ℂ)
    (hz : f.epsilon < z.re) : AnalyticAt ℂ (weightedLaplace f) z := by
  have hw : 0 < (z - (f.epsilon : ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  have ha := nativeCausalLaplaceMoment_analyticAt (z - (f.epsilon : ℂ)) hw 0 f.causalVector
  have htrans : AnalyticAt ℂ (fun q : ℂ => q - (f.epsilon : ℂ)) z :=
    analyticAt_id.sub analyticAt_const
  have hc := ha.comp (f := fun q : ℂ => q - (f.epsilon : ℂ)) (x := z) htrans
  have heq : weightedLaplace f = fun q => nativeCausalLaplaceMoment
      (q - (f.epsilon : ℂ)) 0 (f.causalVector : NativeCompletionL2) := by
    funext q
    exact weightedLaplace_eq_causalMoment f q
  rw [heq]
  exact hc

theorem weightedLaplace_iteratedDeriv (f : WeightedL2Data) (z : ℂ)
    (hz : f.epsilon < z.re) (j : ℕ) :
    iteratedDeriv j (weightedLaplace f) z = (-1 : ℂ)^j *
      nativeCausalLaplaceMoment (z - (f.epsilon : ℂ)) j
        (f.causalVector : NativeCompletionL2) := by
  have heq : weightedLaplace f = fun q => nativeCausalLaplaceMoment
      (q - (f.epsilon : ℂ)) 0 (f.causalVector : NativeCompletionL2) := by
    funext q
    exact weightedLaplace_eq_causalMoment f q
  rw [heq, iteratedDeriv_comp_sub_const (f := fun w =>
    nativeCausalLaplaceMoment w 0 (f.causalVector : NativeCompletionL2))
    (s := (f.epsilon : ℂ))]
  apply nativeCausalLaplaceMoment_iteratedDeriv
  simp only [Complex.sub_re, Complex.ofReal_re]
  linarith

theorem exponentialPolynomial_L2_norm (w : ℂ) (hw : 0 < w.re) (j : ℕ) :
    ‖nativeCausalExponentialWitness w hw j‖ =
      Real.sqrt ((2*j).factorial / (2*w.re)^(2*j+1)) := by
  let v := nativeCausalExponentialPolynomialL2 w hw j
  have hnorm : ‖v‖^2 = ∫ t : ℝ, ‖nativeCausalExponentialPolynomial w j t‖^2 := by
    calc
      ‖v‖^2 = inner ℝ v v := (real_inner_self_eq_norm_sq v).symm
      _ = ∫ t : ℝ, inner ℝ (v t) (v t) := L2.inner_def v v
      _ = ∫ t : ℝ, ‖nativeCausalExponentialPolynomial w j t‖^2 := by
        apply integral_congr_ae
        filter_upwards [nativeCausalExponentialPolynomialL2_coeFn w hw j] with t ht
        change inner ℝ (nativeCausalExponentialPolynomialL2 w hw j t)
          (nativeCausalExponentialPolynomialL2 w hw j t) = _
        rw [ht, real_inner_self_eq_norm_sq]
  have hpoint : (fun t : ℝ => ‖nativeCausalExponentialPolynomial w j t‖^2) =
      (Ici (0 : ℝ)).indicator (fun t => t^(2*j) * Real.exp (-(2*w.re)*t)) := by
    funext t
    by_cases ht : t ∈ Ici (0 : ℝ)
    · rw [indicator_of_mem ht]
      exact nativeCausalExponentialPolynomial_norm_sq w j ht
    · rw [indicator_of_notMem ht, nativeCausalExponentialPolynomial_zero_of_neg w j
        (lt_of_not_ge ht), norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
  rw [hpoint, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi] at hnorm
  have hgamma := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := (2*j : ℕ) + 1) (r := 2*w.re) (by positivity) (by positivity)
  have hintegral : (∫ t : ℝ in Ioi (0 : ℝ), t^(2*j) * Real.exp (-(2*w.re)*t)) =
      (2*j).factorial / (2*w.re)^(2*j+1) := by
    convert hgamma using 1
    · simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Real.rpow_natCast]
      congr 1
      funext t
      congr 2
      ring
    · rw [Real.Gamma_nat_eq_factorial]
      have hcast : (↑(2*j) : ℝ) + 1 = ((2*j+1 : ℕ) : ℝ) := by push_cast; rfl
      rw [hcast, Real.rpow_natCast, div_pow, one_pow]
      ring
  rw [hintegral] at hnorm
  have hsqrt := congrArg Real.sqrt hnorm
  change ‖v‖ = _
  simpa only [Real.sqrt_sq_eq_abs, abs_norm] using hsqrt

/-- Exact Cauchy-Schwarz factorial constant. The square-root form is
sqrt((2j)!)/(2(Re z-epsilon))^(j+1/2), with its positive domain retained. -/
theorem laplace_iteratedDeriv_bound_of_weighted_L2 (f : WeightedL2Data) (z : ℂ)
    (hz : f.epsilon < z.re) (j : ℕ) :
    ‖iteratedDeriv j (weightedLaplace f) z‖ ≤ ‖f.causalVector‖ *
      Real.sqrt ((2*j).factorial / (2*(z.re-f.epsilon))^(2*j+1)) := by
  have hw : 0 < (z - (f.epsilon : ℂ)).re := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    linarith
  rw [weightedLaplace_iteratedDeriv f z hz j, norm_mul, norm_pow, norm_neg,
    norm_one, one_pow, one_mul,
    ← nativeCausalExponentialWitness_inner_eq_laplaceMoment _ hw j f.causalVector]
  calc
    _ ≤ ‖nativeCausalExponentialWitness (z - (f.epsilon : ℂ)) hw j‖ * ‖f.causalVector‖ :=
      norm_inner_le_norm _ _
    _ = _ := by
      rw [exponentialPolynomial_L2_norm]
      simp only [Complex.sub_re, Complex.ofReal_re]
      ring

/-- Meromorphic continuation equality is a punctured-germ statement; arbitrary
totalized values at isolated poles do not become pointwise identities. -/
theorem meromorphic_eq_punctured_of_preconnected
    {g h : ℂ → ℂ} {D : Set ℂ} (hD : IsPreconnected D)
    (hg : MeromorphicOn g D) (hh : MeromorphicOn h D)
    {a : ℂ} (ha : a ∈ D) (heq : g =ᶠ[𝓝 a] h) :
    ∀ z ∈ D, g =ᶠ[𝓝[≠] z] h := by
  let S : Set ℂ := {z | ∀ᶠ q in 𝓝[≠] z, g q - h q = 0}
  let N : Set ℂ := {z | ∀ᶠ q in 𝓝[≠] z, g q - h q ≠ 0}
  have hS : IsOpen S := isOpen_setOfPred_eventually_nhdsWithin
  have hN : IsOpen N := isOpen_setOfPred_eventually_nhdsWithin
  have hdisjoint : Disjoint S N := by
    apply disjoint_left.mpr
    intro z hzS hzN
    dsimp [S] at hzS
    dsimp [N] at hzN
    obtain ⟨q, hq0, hqne⟩ := (hzS.and hzN).exists
    exact hqne hq0
  have hcover : D ⊆ S ∪ N := by
    intro z hz
    exact ((hg z hz).sub (hh z hz)).eventually_eq_zero_or_eventually_ne_zero
  have haS : a ∈ S := by
    filter_upwards [heq.filter_mono nhdsWithin_le_nhds] with q hq
    exact sub_eq_zero.mpr hq
  have hsubset := hD.subset_left_of_subset_union hS hN hdisjoint hcover ⟨a, ha, haS⟩
  intro z hz
  filter_upwards [hsubset hz] with q hq
  exact sub_eq_zero.mp hq

/-- An actual weighted L2 transform cannot continue to any negative-order pole
inside its strict half-plane. The initial open source identity and the common
connected continuation domain are explicit hypotheses. -/
theorem no_visible_pole_of_weighted_L2 (f : WeightedL2Data) (M : ℂ → ℂ)
    (D O : Set ℂ) (hD : IsPreconnected D) (hM : MeromorphicOn M D)
    (hhalf : ∀ z ∈ D, f.epsilon < z.re) (hO : IsOpen O) (hOD : O ⊆ D)
    (hOnonempty : O.Nonempty) (hsource : EqOn M (weightedLaplace f) O) :
    ∀ z ∈ D, 0 ≤ meromorphicOrderAt M z := by
  obtain ⟨a, ha⟩ := hOnonempty
  have hL : MeromorphicOn (weightedLaplace f) D := fun z hz =>
    (laplace_holomorphic_of_weighted_L2 f z (hhalf z hz)).meromorphicAt
  have heq : M =ᶠ[𝓝 a] weightedLaplace f := by
    filter_upwards [hO.mem_nhds ha] with z hz
    exact hsource hz
  have hall := meromorphic_eq_punctured_of_preconnected hD hM hL (hOD ha) heq
  intro z hz
  rw [meromorphicOrderAt_congr (hall z hz)]
  exact (laplace_holomorphic_of_weighted_L2 f z (hhalf z hz)).meromorphicOrderAt_nonneg

end Zeta23.OPICA
