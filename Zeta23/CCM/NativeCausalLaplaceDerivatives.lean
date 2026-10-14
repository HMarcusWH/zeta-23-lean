import Zeta23.CCM.NativeCausalLaplaceMoments
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order

/-!
# Differentiating the literal causal L2 Laplace moments

The half-plane Re w > 0 supplies an integrable neighborhood bound using
the actual L2 exponential-polynomial test vectors. The derivative is the
negative of the next moment. This sign is retained explicitly before
connecting moment vanishing to analytic zero multiplicity.
-/

noncomputable section

open Set MeasureTheory Filter
open scoped Topology

namespace Zeta23.CCM

theorem nativeCausalLaplaceMoment_hasDerivAt (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (f : nativeCompletionCausalL2) :
    HasDerivAt (fun z : ℂ => nativeCausalLaplaceMoment z k (f : NativeCompletionL2))
      (-nativeCausalLaplaceMoment w (k + 1) (f : NativeCompletionL2)) w := by
  let F : ℂ → ℝ → ℂ := fun z t =>
    (t : ℂ) ^ k * Complex.exp (-z * (t : ℂ)) * (f : NativeCompletionL2) t
  let G : ℂ → ℝ → ℂ := fun z t =>
    -(t : ℂ) ^ (k + 1) * Complex.exp (-z * (t : ℂ)) * (f : NativeCompletionL2) t
  let B : ℝ → ℝ := fun t =>
    ‖(t : ℂ) ^ (k + 1) * Complex.exp (-((w.re / 2 : ℝ) : ℂ) * (t : ℂ)) *
      (f : NativeCompletionL2) t‖
  let S : Set ℂ := {z | w.re / 2 < z.re}
  have hhalf : 0 < (((w.re / 2 : ℝ) : ℂ)).re := by
    simp only [Complex.ofReal_re]
    linarith
  have hB : Integrable B :=
    (nativeCausalLaplaceMoment_integrable ((w.re / 2 : ℝ) : ℂ) hhalf (k + 1) f).norm
  have hS : S ∈ 𝓝 w := by
    apply (isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    change w.re / 2 < w.re
    linarith
  have hFm : ∀ z : ℂ, AEStronglyMeasurable (F z) := by
    intro z
    have hc : Continuous (fun t : ℝ => (t : ℂ) ^ k * Complex.exp (-z * (t : ℂ))) := by
      fun_prop
    exact hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable (f : NativeCompletionL2))
  have hGm : AEStronglyMeasurable (G w) := by
    have hc : Continuous (fun t : ℝ => -(t : ℂ) ^ (k + 1) * Complex.exp (-w * (t : ℂ))) := by
      fun_prop
    exact hc.aestronglyMeasurable.mul (Lp.aestronglyMeasurable (f : NativeCompletionL2))
  have hbound : ∀ᵐ t : ℝ, ∀ z ∈ S, ‖G z t‖ ≤ B t := by
    filter_upwards [f.property] with t hft
    intro z hz
    by_cases ht : 0 ≤ t
    · dsimp only [G, B]
      simp only [norm_mul, norm_neg, norm_pow, Complex.norm_exp]
      have hre (v : ℂ) : (-v * (t : ℂ)).re = -v.re * t := by
        simp only [Complex.mul_re, Complex.neg_re, Complex.ofReal_re, Complex.ofReal_im,
          mul_zero, sub_zero]
      rw [hre z, hre ((w.re / 2 : ℝ) : ℂ), Complex.ofReal_re]
      gcongr
      have hzre : w.re / 2 < z.re := hz
      exact hzre.le
    · dsimp only [G, B]
      rw [hft (lt_of_not_ge ht)]
      simp only [mul_zero, norm_zero, le_refl]
  have hdiff : ∀ᵐ t : ℝ, ∀ z ∈ S, HasDerivAt (F · t) (G z t) z := by
    filter_upwards with t
    intro z _
    have hlin := (hasDerivAt_id z).neg.mul_const (t : ℂ)
    have hd := (hlin.cexp.const_mul ((t : ℂ) ^ k)).mul_const ((f : NativeCompletionL2) t)
    convert! hd using 1 <;> simp only [F, G, pow_succ, Pi.neg_apply, id_eq] <;> ring
  have h := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := (volume : Measure ℝ)) (F := F) (F' := G) (bound := B) hS
    (Filter.Eventually.of_forall hFm) (nativeCausalLaplaceMoment_integrable w hw k f)
    hGm hbound hB hdiff).2
  have hGint : (∫ t : ℝ, G w t) =
      -nativeCausalLaplaceMoment w (k + 1) (f : NativeCompletionL2) := by
    unfold nativeCausalLaplaceMoment
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with t
    dsimp only [G]
    ring
  change HasDerivAt (fun z : ℂ => nativeCausalLaplaceMoment z k (f : NativeCompletionL2))
    (∫ t : ℝ, G w t) w at h
  rw [hGint] at h
  exact h

theorem nativeCausalLaplaceMoment_analyticAt (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (f : nativeCompletionCausalL2) :
    AnalyticAt ℂ (fun z : ℂ => nativeCausalLaplaceMoment z k (f : NativeCompletionL2)) w := by
  apply DifferentiableOn.analyticAt (s := {z : ℂ | 0 < z.re})
  · intro z hz
    exact (nativeCausalLaplaceMoment_hasDerivAt z hz k f).differentiableAt.differentiableWithinAt
  · exact (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw

/-- The exact phase of every derivative of the literal transform. -/
theorem nativeCausalLaplaceMoment_iteratedDeriv (w : ℂ) (hw : 0 < w.re) (k : ℕ)
    (f : nativeCompletionCausalL2) :
    iteratedDeriv k (fun z : ℂ => nativeCausalLaplaceMoment z 0 (f : NativeCompletionL2)) w =
      (-1 : ℂ) ^ k * nativeCausalLaplaceMoment w k (f : NativeCompletionL2) := by
  induction k generalizing w with
  | zero => simp only [iteratedDeriv_zero, pow_zero, one_mul]
  | succ k ih =>
    have heq : iteratedDeriv k (fun z : ℂ =>
        nativeCausalLaplaceMoment z 0 (f : NativeCompletionL2)) =ᶠ[𝓝 w]
        fun z => (-1 : ℂ) ^ k * nativeCausalLaplaceMoment z k (f : NativeCompletionL2) := by
      filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hw] with z hz
      exact ih z hz
    rw [iteratedDeriv_succ, heq.deriv_eq]
    rw [((nativeCausalLaplaceMoment_hasDerivAt w hw k f).const_mul ((-1 : ℂ) ^ k)).deriv]
    rw [pow_succ]
    ring

theorem nativeCausalLaplaceMoment_vanishes_iff_iteratedDeriv
    (w : ℂ) (hw : 0 < w.re) (k : ℕ) (f : nativeCompletionCausalL2) :
    nativeCausalLaplaceMoment w k (f : NativeCompletionL2) = 0 ↔
      iteratedDeriv k (fun z : ℂ => nativeCausalLaplaceMoment z 0 (f : NativeCompletionL2)) w = 0 := by
  rw [nativeCausalLaplaceMoment_iteratedDeriv w hw k f]
  exact (mul_eq_zero_iff_left (pow_ne_zero k (neg_ne_zero.mpr (one_ne_zero : (1 : ℂ) ≠ 0)))).symm

theorem nativeCausalLaplaceMoment_vanishes_below_analyticOrder
    (w : ℂ) (hw : 0 < w.re) (n : ℕ) (f : nativeCompletionCausalL2)
    (horder : (n : ℕ∞) ≤ analyticOrderAt
      (fun z : ℂ => nativeCausalLaplaceMoment z 0 (f : NativeCompletionL2)) w) :
    ∀ k < n, nativeCausalLaplaceMoment w k (f : NativeCompletionL2) = 0 := by
  have h := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
    (nativeCausalLaplaceMoment_analyticAt w hw 0 f)).mp horder
  intro k hk
  exact (nativeCausalLaplaceMoment_vanishes_iff_iteratedDeriv w hw k f).mpr (h k hk)

theorem nativeCausalLaplaceMoment_ne_zero_at_analyticOrder
    (w : ℂ) (hw : 0 < w.re) (n : ℕ) (f : nativeCompletionCausalL2)
    (horder : analyticOrderAt
      (fun z : ℂ => nativeCausalLaplaceMoment z 0 (f : NativeCompletionL2)) w = n) :
    nativeCausalLaplaceMoment w n (f : NativeCompletionL2) ≠ 0 := by
  have h := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    (nativeCausalLaplaceMoment_analyticAt w hw 0 f)).mp horder
  intro hz
  exact h.2 ((nativeCausalLaplaceMoment_vanishes_iff_iteratedDeriv w hw n f).mp hz)

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeCausalLaplaceMoment_hasDerivAt
#print axioms Zeta23.CCM.nativeCausalLaplaceMoment_analyticAt
#print axioms Zeta23.CCM.nativeCausalLaplaceMoment_iteratedDeriv
#print axioms Zeta23.CCM.nativeCausalLaplaceMoment_vanishes_below_analyticOrder
#print axioms Zeta23.CCM.nativeCausalLaplaceMoment_ne_zero_at_analyticOrder
