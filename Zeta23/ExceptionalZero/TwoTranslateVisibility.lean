import Zeta23.ExceptionalZero.WeilFilter
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Complex.RealDeriv

noncomputable section

namespace Zeta23.ExceptionalZero

open Complex MeasureTheory ContinuousLinearMap
open scoped Convolution

/-!
# X1: real-even target-adaptive visibility

The existing exceptional-zero stack already contains the pole-killing operator
`poleKilled` and its exact Fourier multiplier. X1 therefore produces, for an
arbitrary complex spectral target, a real-even smooth compactly supported bump
whose paper Fourier transform is nonzero at that target, and then applies the
existing pole killer.

The seed construction uses a normalized bump as an approximate identity. A
sufficiently small real-even bump has Fourier response close to `1` at the fixed
target, hence cannot vanish there. No zero location is hard-coded into the test
family.
-/

/-- Every complex spectral target is visible to a real-even `C⁴` compactly supported test. -/
theorem exists_realEven_contDiff_visible_test (w : ℂ) :
    ∃ q : ℝ → ℂ,
      ContDiff ℝ 4 q ∧ HasCompactSupport q ∧ Function.Even q ∧
        (∀ x : ℝ, (q x).im = 0) ∧ paperFT q w ≠ 0 := by
  let g : ℝ → ℝ := fun x => (Complex.exp (-(I * w * (x : ℂ)))).re
  have hg : Continuous g := by
    fun_prop
  have hg0 : ContinuousAt g 0 := hg.continuousAt
  obtain ⟨δ, hδ, hclose⟩ :=
    (Metric.continuousAt_iff.1 hg0) (1 / 2 : ℝ) (by norm_num)
  let φ : ContDiffBump (0 : ℝ) :=
    ⟨δ / 2, δ, by positivity, by linarith⟩
  have hconv :
      dist
          ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) 0)
          (g 0) ≤ (1 / 2 : ℝ) := by
    apply φ.dist_normed_convolution_le hg.aestronglyMeasurable
    intro x hx
    exact le_of_lt (hclose (by simpa [φ] using hx))
  have hconv_ne : ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) 0) ≠ 0 := by
    intro hzero
    rw [hzero] at hconv
    norm_num [g] at hconv
  let q : ℝ → ℂ := fun x => ((φ.normed volume x : ℝ) : ℂ)
  have hq4 : ContDiff ℝ 4 q := by
    exact Complex.ofRealCLM.contDiff.comp φ.contDiff_normed
  have hqc : HasCompactSupport q := by
    exact (φ.hasCompactSupport_normed (μ := volume)).comp_left
      (g := Complex.ofReal) Complex.ofReal_zero
  have hqeven : Function.Even q := by
    intro x
    change ((φ.normed volume (-x) : ℝ) : ℂ) = ((φ.normed volume x : ℝ) : ℂ)
    rw [φ.normed_neg]
  have hqreal : ∀ x : ℝ, (q x).im = 0 := by
    intro x
    simp [q]
  have hint : Integrable (fun x : ℝ => q x * Complex.exp (I * w * (x : ℂ))) := by
    have hce : Continuous (fun x : ℝ => Complex.exp (I * w * (x : ℂ))) := by
      fun_prop
    exact (hq4.continuous.mul hce).integrable_of_hasCompactSupport hqc.mul_right
  have hconv_re :
      ((φ.normed volume ⋆[lsmul ℝ ℝ, volume] g) 0) = (paperFT q w).re := by
    unfold MeasureTheory.convolution paperFT
    calc
      (∫ t : ℝ, ((lsmul ℝ ℝ) (φ.normed volume t)) (g (0 - t))) =
          ∫ u : ℝ, (q u * Complex.exp (I * w * (u : ℂ))).re := by
        apply integral_congr_ae
        filter_upwards with x
        simp [q, g, lsmul_apply, Complex.mul_re]
      _ = (∫ u : ℝ, q u * Complex.exp (I * w * (u : ℂ))).re := by
        exact integral_re hint
  have hqvis_re : (paperFT q w).re ≠ 0 := by
    intro hzero
    apply hconv_ne
    rw [hconv_re, hzero]
  have hqvis : paperFT q w ≠ 0 := by
    intro hzero
    apply hqvis_re
    rw [hzero]
    simp
  exact ⟨q, hq4, hqc, hqeven, hqreal, hqvis⟩

/-- The first derivative of an even function is odd. This statement is purely algebraic because
`deriv` is totalized in Mathlib. -/
theorem deriv_odd_of_even {q : ℝ → ℂ} (hq : Function.Even q) :
    Function.Odd (deriv q) := by
  have hfun : (fun y : ℝ => q (-y)) = q := by
    funext y
    exact hq y
  intro x
  have h := congrArg (fun f : ℝ → ℂ => deriv f x) hfun
  rw [deriv_comp_neg] at h
  exact neg_eq_iff_eq_neg.mp h

/-- Two derivatives preserve evenness. -/
theorem deriv_deriv_even_of_even {q : ℝ → ℂ} (hq : Function.Even q) :
    Function.Even (deriv (deriv q)) := by
  have hodd : Function.Odd (deriv q) := deriv_odd_of_even hq
  have hfun : (fun y : ℝ => deriv q (-y)) = -deriv q := by
    funext y
    exact hodd y
  intro x
  have h := congrArg (fun f : ℝ → ℂ => deriv f x) hfun
  rw [deriv_comp_neg, deriv.neg] at h
  exact neg_injective h

/-- A differentiable complex-valued function that is pointwise real has a pointwise real derivative. -/
theorem deriv_im_eq_zero_of_real {q : ℝ → ℂ}
    (hq : Differentiable ℝ q) (hreal : ∀ x : ℝ, (q x).im = 0) (x : ℝ) :
    (deriv q x).im = 0 := by
  have hqAt : HasDerivAt q (deriv q x) x := (hq x).hasDerivAt
  have hconjDeriv :
      deriv (Complex.conjCLE ∘ q) x =
        Complex.conjCLE (deriv q x) := by
    exact (Complex.conjCLE.hasFDerivAt.comp_hasDerivAt x hqAt).deriv
  have hfun : (Complex.conjCLE ∘ q) = q := by
    funext y
    change Complex.conjCLE (q y) = q y
    rw [Complex.conjCLE_apply]
    apply Complex.ext
    · simp
    · simp [hreal y]
  have hderiv := congrArg (fun f : ℝ → ℂ => deriv f x) hfun
  rw [hconjDeriv] at hderiv
  have him : -(deriv q x).im = (deriv q x).im := by
    simpa only [Complex.conjCLE_apply, Complex.conj_im] using
      congrArg Complex.im hderiv
  linarith

/-- The pole-killing operator preserves evenness. -/
theorem poleKilled_even {q : ℝ → ℂ} (hq : Function.Even q) :
    Function.Even (poleKilled q) := by
  have hdd : Function.Even (deriv (deriv q)) := deriv_deriv_even_of_even hq
  intro x
  unfold poleKilled
  rw [hdd x, hq x]

/-- On a `C⁴` real-valued seed, the pole-killing operator remains real-valued. -/
theorem poleKilled_im_eq_zero {q : ℝ → ℂ}
    (hq4 : ContDiff ℝ 4 q) (hreal : ∀ x : ℝ, (q x).im = 0) :
    ∀ x : ℝ, (poleKilled q x).im = 0 := by
  have hqdiff : Differentiable ℝ q := hq4.differentiable (by norm_num)
  have hdreal : ∀ x : ℝ, (deriv q x).im = 0 :=
    fun x => deriv_im_eq_zero_of_real hqdiff hreal x
  have hd3 : ContDiff ℝ 3 (deriv q) := hq4.deriv'
  have hddiff : Differentiable ℝ (deriv q) := hd3.differentiable (by norm_num)
  have hddreal : ∀ x : ℝ, (deriv (deriv q) x).im = 0 :=
    fun x => deriv_im_eq_zero_of_real hddiff hdreal x
  intro x
  simp [poleKilled, hddreal x, hreal x]

/-- **X1 endpoint.** Every nontrivial zeta zero is visible to an admissible real-even
pole-neutral Weil test. The test is target-adaptive but uses no assumption that the zero is
off the critical line. -/
theorem exists_realEven_poleKilled_visible_test
    (ρ₀ : zetaZeroConfig.carrier) :
    ∃ k : ℝ → ℂ,
      ContDiff ℝ 2 k ∧ HasCompactSupport k ∧ Function.Even k ∧
        (∀ x : ℝ, (k x).im = 0) ∧
        paperFT k (I / 2) = 0 ∧ paperFT k (-I / 2) = 0 ∧
        paperFT k (gammaOf (ρ₀ : ℂ)) ≠ 0 := by
  obtain ⟨q, hq4, hqc, hqeven, hqreal, hqvis⟩ :=
    exists_realEven_contDiff_visible_test (gammaOf (ρ₀ : ℂ))
  have hq2 : ContDiff ℝ 2 q := hq4.of_le (by norm_num)
  refine ⟨poleKilled q,
    contDiff_poleKilled hq4,
    hasCompactSupport_poleKilled hqc,
    poleKilled_even hqeven,
    poleKilled_im_eq_zero hq4 hqreal,
    paperFT_poleKilled_I_half hq2 hqc,
    paperFT_poleKilled_neg_I_half hq2 hqc,
    ?_⟩
  exact paperFT_poleKilled_ne_zero_at_zero hq2 hqc ρ₀ hqvis

/-- X1/R001 handoff: a hypothetical right-half zero admits a real-even, pole-neutral test whose
translated arithmetic explicit-formula side violates every subexponential bound. -/
theorem exists_realEven_poleKilled_test_not_subexponential_of_right_zero
    (ρ₀ : zetaZeroConfig.carrier) (hright : 1 / 2 < (ρ₀ : ℂ).re) :
    ∃ k : ℝ → ℂ,
      ContDiff ℝ 2 k ∧ HasCompactSupport k ∧ Function.Even k ∧
        (∀ x : ℝ, (k x).im = 0) ∧
        paperFT k (I / 2) = 0 ∧ paperFT k (-I / 2) = 0 ∧
        ¬ Subexponential
          (fun a => ‖Zeta23.EF.literatureRHS (translateRight k (2 * a))‖) := by
  obtain ⟨k, hk2, hkc, hkeven, hkreal, hkp, hkn, hkvis⟩ :=
    exists_realEven_poleKilled_visible_test ρ₀
  refine ⟨k, hk2, hkc, hkeven, hkreal, hkp, hkn, ?_⟩
  exact not_subexponential_weilLiteratureRHS_of_right_zero hk2 hkc ρ₀ hright hkvis

#print axioms Zeta23.ExceptionalZero.exists_realEven_contDiff_visible_test
#print axioms Zeta23.ExceptionalZero.exists_realEven_poleKilled_visible_test
#print axioms Zeta23.ExceptionalZero.exists_realEven_poleKilled_test_not_subexponential_of_right_zero

end Zeta23.ExceptionalZero
