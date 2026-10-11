import Zeta23.CCM.DictionaryAnalysis
import Zeta23.CCM.SourceMatrix
import Zeta23.CCM.ConstrainedParity
import Zeta23.CCM.FiniteDictionary
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

noncomputable section

/-!
# M03: rank-two Laplace transform of the source matrix

For `L > 0`, `a = 4π/L`, `u_n = 1/(1 + a² n²)` and `v_n = n/(1 + a² n²)`,

```text
∫₀^∞ e^{-t/2} S_{nm}(t/L) dt = (8/L) (u_n u_m - a² v_n v_m),
```

for the diagonal (`2ω cos 2πnω`) and off-diagonal
(`(sin 2πnω - sin 2πmω)/(π(n - m))`) source entries alike.  The proof writes
`e^{-t/2} sin(βt)` and `e^{-t/2} t cos(βt)` as imaginary and real parts of
`e^{ct}` and `t e^{ct}` with `c = -1/2 + iβ`, and uses
`∫₀^∞ e^{ct} = -1/c`, `∫₀^∞ t e^{ct} = 1/c²` (`Re c < 0`).

For complex coefficients `x` the Laplace-weighted source energy is
`(8/L)(|∑ u_i x_i|² - a² |∑ v_i x_i|²)`.  Since `u` is even and `v` is odd in
the centered index, reversal-even vectors give the rank-one square
`(8/L)|∑ u_i x_i|² ≥ 0` and reversal-odd vectors give
`-(8/L) a² |∑ v_i x_i|² ≤ 0`.

These are semidefinite rank-one restrictions of a model transform, not
definiteness and not the full canonical energy.  Nothing here concerns zeta
zeros or RH.
-/

namespace Zeta23.CCM

open MeasureTheory Set Filter Topology Complex

/-- `t e^{ct}` is integrable on `(0, ∞)` when `Re c < 0`. -/
theorem integrableOn_mul_cexp_Ioi {c : ℂ} (hc : c.re < 0) :
    IntegrableOn (fun t : ℝ => (t : ℂ) * Complex.exp (c * t)) (Ioi 0) := by
  have hr := integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (b := -c.re)
    (by norm_num) one_pos (by linarith)
  refine (integrable_norm_iff ?_).mp ?_
  · exact (by fun_prop : Continuous fun t : ℝ => (t : ℂ) * Complex.exp (c * t)).aestronglyMeasurable
  refine hr.congr_fun (fun t ht => ?_) measurableSet_Ioi
  simp only [Real.rpow_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (mem_Ioi.mp ht),
    Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring_nf

/-- `∫₀^∞ e^{ct} dt = -1/c` for `Re c < 0`. -/
theorem integral_cexp_Ioi_zero {c : ℂ} (hc : c.re < 0) :
    ∫ t : ℝ in Ioi 0, Complex.exp (c * t) = -1 / c := by
  rw [integral_exp_mul_complex_Ioi hc 0]
  simp

/-- `∫₀^∞ t e^{ct} dt = 1/c²` for `Re c < 0`. -/
theorem integral_mul_cexp_Ioi_zero {c : ℂ} (hc : c.re < 0) :
    ∫ t : ℝ in Ioi 0, (t : ℂ) * Complex.exp (c * t) = 1 / c ^ 2 := by
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  set F : ℝ → ℂ := fun t => ((t : ℂ) / c - 1 / c ^ 2) * Complex.exp (c * t)
  have hderiv : ∀ x ∈ Ici (0 : ℝ), HasDerivAt F ((x : ℂ) * Complex.exp (c * x)) x := by
    intro x _
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) / c - 1 / c ^ 2) (1 / c) x := by
      have := ((hasDerivAt_id x).ofReal_comp).div_const c
      simpa using this.sub_const (1 / c ^ 2)
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp (c * t)) (c * Complex.exp (c * x)) x := by
      have hl : HasDerivAt (fun t : ℝ => c * (t : ℂ)) c x := by
        simpa using ((hasDerivAt_id x).ofReal_comp).const_mul c
      have := (Complex.hasDerivAt_exp (c * x)).comp x hl
      rw [mul_comm c]
      exact this
    refine (h1.mul h2).congr_deriv ?_
    field_simp
    ring
  have hlim : Tendsto F atTop (𝓝 0) := by
    -- ‖F t‖ ≤ (t/|c| + 1/|c|²) e^{Re c · t} → 0
    have hdecay : Tendsto (fun t : ℝ => (t / ‖c‖ + 1 / ‖c‖ ^ 2) * Real.exp (c.re * t)) atTop (𝓝 0) := by
      have hb : 0 < -c.re := by linarith
      have h1 : Tendsto (fun t : ℝ => t * Real.exp (c.re * t)) atTop (𝓝 0) := by
        have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
          (tendsto_id.const_mul_atTop hb)
        have h' : Tendsto (fun t : ℝ => (1 / -c.re) * ((-c.re * t) ^ 1 * Real.exp (-(-c.re * t))))
            atTop (𝓝 ((1 / -c.re) * 0)) := this.const_mul _
        rw [mul_zero] at h'
        refine h'.congr fun t => ?_
        simp only [pow_one, neg_mul, neg_neg]
        field_simp
        have hne : c.re ≠ 0 := by linarith
        field_simp
      have h2 : Tendsto (fun t : ℝ => Real.exp (c.re * t)) atTop (𝓝 0) := by
        have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg hc)
        exact this
      have := (h1.div_const ‖c‖).add (h2.const_mul (1 / ‖c‖ ^ 2))
      simp only [zero_div, mul_zero, add_zero] at this
      refine this.congr fun t => ?_
      ring
    refine squeeze_zero_norm' ?_ hdecay
    filter_upwards [eventually_ge_atTop 0] with t ht
    simp only [F, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero]
    gcongr
    calc ‖(t : ℂ) / c - 1 / c ^ 2‖ ≤ ‖(t : ℂ) / c‖ + ‖1 / c ^ 2‖ := norm_sub_le _ _
      _ = t / ‖c‖ + 1 / ‖c‖ ^ 2 := by
        rw [norm_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht, norm_one,
          norm_pow]
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_mul_cexp_Ioi hc) hlim
  rw [h]
  simp [F]

/-- Rate `c = -1/2 + iβ`. -/
private def halfRate (β : ℝ) : ℂ := ⟨-1 / 2, β⟩

private theorem halfRate_re (β : ℝ) : (halfRate β).re < 0 := by
  simp [halfRate]; norm_num

private theorem normSq_halfRate (β : ℝ) : Complex.normSq (halfRate β) = 1 / 4 + β ^ 2 := by
  simp [halfRate, Complex.normSq_apply]; ring

private theorem exp_halfRate_mul (β t : ℝ) :
    Complex.exp (halfRate β * t) =
      ((Real.exp (-t / 2) * Real.cos (β * t) : ℝ) : ℂ) +
        ((Real.exp (-t / 2) * Real.sin (β * t) : ℝ) : ℂ) * Complex.I := by
  have hre : (halfRate β * t).re = -t / 2 := by simp [halfRate, Complex.mul_re]; ring
  have him : (halfRate β * t).im = β * t := by simp [halfRate, Complex.mul_im]
  apply Complex.ext
  · rw [Complex.exp_re, hre, him]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  · rw [Complex.exp_im, hre, him]
    simp only [Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring

/-- `∫₀^∞ e^{-t/2} sin(βt) dt = β/(1/4 + β²)`. -/
theorem integral_exp_neg_half_mul_sin_Ioi (β : ℝ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t / 2) * Real.sin (β * t) = β / (1 / 4 + β ^ 2) := by
  have hint := integrableOn_exp_mul_complex_Ioi (halfRate_re β) 0
  have him := integral_im hint
  have hval := integral_cexp_Ioi_zero (halfRate_re β)
  simp only [RCLike.im_to_complex] at him
  rw [hval] at him
  have hpt : (fun t : ℝ => (Complex.exp (halfRate β * t)).im) =
      fun t => Real.exp (-t / 2) * Real.sin (β * t) := by
    funext t
    rw [exp_halfRate_mul]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im]
    ring
  rw [hpt] at him
  rw [him, Complex.div_im, normSq_halfRate]
  simp [halfRate]
  ring

/-- `∫₀^∞ e^{-t/2} t cos(βt) dt = (1/4 - β²)/(1/4 + β²)²`. -/
theorem integral_exp_neg_half_mul_mul_cos_Ioi (β : ℝ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t / 2) * (t * Real.cos (β * t)) =
      (1 / 4 - β ^ 2) / (1 / 4 + β ^ 2) ^ 2 := by
  have hint := integrableOn_mul_cexp_Ioi (halfRate_re β)
  have hre := integral_re hint
  have hval := integral_mul_cexp_Ioi_zero (halfRate_re β)
  simp only [RCLike.re_to_complex] at hre
  rw [hval] at hre
  have hpt : (fun t : ℝ => ((t : ℂ) * Complex.exp (halfRate β * t)).re) =
      fun t => Real.exp (-t / 2) * (t * Real.cos (β * t)) := by
    funext t
    rw [exp_halfRate_mul, Complex.re_ofReal_mul]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    ring
  rw [hpt] at hre
  rw [hre, one_div, Complex.inv_re, map_pow, normSq_halfRate]
  have : (halfRate β ^ 2).re = 1 / 4 - β ^ 2 := by simp [halfRate, sq]; ring
  rw [this]

/-- `e^{-t/2} sin(βt)` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_half_mul_sin (β : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t / 2) * Real.sin (β * t)) (Ioi 0) := by
  have h := (integrableOn_exp_mul_complex_Ioi (halfRate_re β) 0).im
  refine Integrable.congr h (Filter.Eventually.of_forall fun t => ?_)
  simp only [RCLike.im_to_complex]
  rw [exp_halfRate_mul]
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im]
  ring

/-- `e^{-t/2} t cos(βt)` is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_half_mul_mul_cos (β : ℝ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t / 2) * (t * Real.cos (β * t))) (Ioi 0) := by
  have h := (integrableOn_mul_cexp_Ioi (halfRate_re β)).re
  refine Integrable.congr h (Filter.Eventually.of_forall fun t => ?_)
  simp only [RCLike.re_to_complex]
  rw [exp_halfRate_mul, Complex.re_ofReal_mul]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im]
  ring

/-- Laplace scale `a = 4π/L`. -/
def sourceLaplaceScale (L : ℝ) : ℝ := 4 * Real.pi / L

/-- Even Laplace profile `u_n = 1/(1 + a² n²)`. -/
def sourceLaplaceU (L : ℝ) (n : ℤ) : ℝ := 1 / (1 + sourceLaplaceScale L ^ 2 * (n : ℝ) ^ 2)

/-- Odd Laplace profile `v_n = n/(1 + a² n²)`. -/
def sourceLaplaceV (L : ℝ) (n : ℤ) : ℝ := (n : ℝ) / (1 + sourceLaplaceScale L ^ 2 * (n : ℝ) ^ 2)

/-- **M03, rank-two Laplace transform (entrywise).**  For `L > 0`,
`∫₀^∞ e^{-t/2} S_{nm}(t/L) dt = (8/L)(u_n u_m - a² v_n v_m)` with `a = 4π/L`. -/
theorem integral_exp_neg_half_mul_sourceEntryReal {L : ℝ} (hL : 0 < L) (n m : ℤ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t / 2) * sourceEntryReal (t / L) n m =
      8 / L * (sourceLaplaceU L n * sourceLaplaceU L m -
        sourceLaplaceScale L ^ 2 * sourceLaplaceV L n * sourceLaplaceV L m) := by
  have hL0 : L ≠ 0 := hL.ne'
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hden : ∀ k : ℤ, 1 + (4 * Real.pi / L) ^ 2 * (k : ℝ) ^ 2 ≠ 0 := fun k => by positivity
  have hden' : ∀ k : ℤ, 1 / 4 + (2 * Real.pi * k / L) ^ 2 ≠ 0 := fun k => by positivity
  by_cases hnm : n = m
  · subst hnm
    have hpt : (fun t : ℝ => Real.exp (-t / 2) * sourceEntryReal (t / L) n n) =
        fun t => (2 / L) * (Real.exp (-t / 2) * (t * Real.cos (2 * Real.pi * n / L * t))) := by
      funext t
      simp only [sourceEntryReal, if_true, sourceDiagonalReal]
      have : 2 * Real.pi * (n : ℝ) * (t / L) = 2 * Real.pi * n / L * t := by ring
      rw [this]
      ring
    rw [hpt, integral_const_mul, integral_exp_neg_half_mul_mul_cos_Ioi]
    unfold sourceLaplaceU sourceLaplaceV sourceLaplaceScale
    have h1 := hden n
    have h2 := hden' n
    field_simp
    ring
  · have hnm' : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hnm
    have hpt : (fun t : ℝ => Real.exp (-t / 2) * sourceEntryReal (t / L) n m) =
        fun t => (1 / (Real.pi * ((n - m : ℤ) : ℝ))) *
          (Real.exp (-t / 2) * Real.sin (2 * Real.pi * n / L * t) -
            Real.exp (-t / 2) * Real.sin (2 * Real.pi * m / L * t)) := by
      funext t
      simp only [sourceEntryReal, hnm, if_false, sourcePotentialReal]
      have e1 : 2 * Real.pi * (n : ℝ) * (t / L) = 2 * Real.pi * n / L * t := by ring
      have e2 : 2 * Real.pi * (m : ℝ) * (t / L) = 2 * Real.pi * m / L * t := by ring
      rw [e1, e2]
      field_simp
    rw [hpt, integral_const_mul, integral_sub (integrableOn_exp_neg_half_mul_sin _)
      (integrableOn_exp_neg_half_mul_sin _), integral_exp_neg_half_mul_sin_Ioi,
      integral_exp_neg_half_mul_sin_Ioi]
    unfold sourceLaplaceU sourceLaplaceV sourceLaplaceScale
    have h1 := hden n
    have h2 := hden m
    have h3 := hden' n
    have h4 := hden' m
    push_cast at hnm' ⊢
    have hnm'' : (n : ℝ) - m ≠ 0 := hnm'
    field_simp
    ring

/-- Each Laplace-weighted source entry is integrable on `(0, ∞)`. -/
theorem integrableOn_exp_neg_half_mul_sourceEntryReal (L : ℝ) (n m : ℤ) :
    IntegrableOn (fun t : ℝ => Real.exp (-t / 2) * sourceEntryReal (t / L) n m) (Ioi 0) := by
  by_cases hnm : n = m
  · subst hnm
    refine ((integrableOn_exp_neg_half_mul_mul_cos (2 * Real.pi * n / L)).const_mul (2 / L)).congr
      (Filter.Eventually.of_forall fun t => ?_)
    simp only [sourceEntryReal, if_true, sourceDiagonalReal]
    have : 2 * Real.pi * (n : ℝ) * (t / L) = 2 * Real.pi * n / L * t := by ring
    rw [this]
    ring
  · refine (((integrableOn_exp_neg_half_mul_sin (2 * Real.pi * n / L)).sub
      (integrableOn_exp_neg_half_mul_sin (2 * Real.pi * m / L))).const_mul
        (1 / (Real.pi * ((n - m : ℤ) : ℝ)))).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [sourceEntryReal, hnm, if_false, sourcePotentialReal, Pi.sub_apply]
    have e1 : 2 * Real.pi * (n : ℝ) * (t / L) = 2 * Real.pi * n / L * t := by ring
    have e2 : 2 * Real.pi * (m : ℝ) * (t / L) = 2 * Real.pi * m / L * t := by ring
    rw [e1, e2]
    have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
    have hnm' : ((n - m : ℤ) : ℝ) ≠ 0 := by exact_mod_cast sub_ne_zero.mpr hnm
    field_simp

private theorem normSq_eq_re_conj_mul (z : ℂ) : Complex.normSq z = ((starRingEnd ℂ) z * z).re := by
  simp [Complex.normSq_apply, Complex.mul_re]

private theorem normSq_sum_real_mul {ι : Type*} [Fintype ι] (w : ι → ℝ) (x : ι → ℂ) :
    Complex.normSq (∑ i, (w i : ℂ) * x i) =
      ∑ i, ∑ j, w i * w j * ((starRingEnd ℂ) (x i) * x j).re := by
  rw [normSq_eq_re_conj_mul, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [map_mul, Complex.conj_ofReal]
  rw [show (w i : ℂ) * (starRingEnd ℂ) (x i) * ((w j : ℂ) * x j) =
      ((w i * w j : ℝ) : ℂ) * ((starRingEnd ℂ) (x i) * x j) by push_cast; ring,
    Complex.re_ofReal_mul]

/-- **M03, rank-two Laplace transform (energy form).**  For `L > 0` and any
complex coefficients `x`,
`∫₀^∞ e^{-t/2} e_x(t/L) dt = (8/L)(|∑ u_i x_i|² - a² |∑ v_i x_i|²)`. -/
theorem integral_exp_neg_half_mul_sourceEnergy {L : ℝ} (hL : 0 < L) (K : ℕ)
    (x : Fin (2 * K + 1) → ℂ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t / 2) * (quadraticForm (sourceMatrix (t / L) K) x).re =
      8 / L * (Complex.normSq (∑ i, (sourceLaplaceU L (centeredIndex K i) : ℂ) * x i) -
        sourceLaplaceScale L ^ 2 *
          Complex.normSq (∑ i, (sourceLaplaceV L (centeredIndex K i) : ℂ) * x i)) := by
  set c := centeredIndex K
  have hpt : (fun t : ℝ => Real.exp (-t / 2) * (quadraticForm (sourceMatrix (t / L) K) x).re) =
      fun t => ∑ i, ∑ j, ((starRingEnd ℂ) (x i) * x j).re *
        (Real.exp (-t / 2) * sourceEntryReal (t / L) (c i) (c j)) := by
    funext t
    unfold quadraticForm
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.re_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [sourceMatrix_apply, sourceEntry_eq_ofReal,
      show (starRingEnd ℂ) (x i) * (sourceEntryReal (t / L) (c i) (c j) : ℂ) * x j =
        ((sourceEntryReal (t / L) (c i) (c j) : ℝ) : ℂ) * ((starRingEnd ℂ) (x i) * x j) by ring,
      Complex.re_ofReal_mul]
    ring
  rw [hpt, integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (integrableOn_exp_neg_half_mul_sourceEntryReal L (c i) (c j)).const_mul _]
  simp_rw [integral_finsetSum _ fun j _ =>
    (integrableOn_exp_neg_half_mul_sourceEntryReal L _ _).const_mul _, integral_const_mul,
    integral_exp_neg_half_mul_sourceEntryReal hL]
  rw [normSq_sum_real_mul, normSq_sum_real_mul]
  calc _ = ∑ i, ∑ j, (8 / L * (sourceLaplaceU L (c i) * sourceLaplaceU L (c j) *
          ((starRingEnd ℂ) (x i) * x j).re) -
        8 / L * sourceLaplaceScale L ^ 2 * (sourceLaplaceV L (c i) * sourceLaplaceV L (c j) *
          ((starRingEnd ℂ) (x i) * x j).re)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = _ := by
        simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
        ring

theorem sourceLaplaceU_neg (L : ℝ) (n : ℤ) : sourceLaplaceU L (-n) = sourceLaplaceU L n := by
  simp [sourceLaplaceU]

theorem sourceLaplaceV_neg (L : ℝ) (n : ℤ) : sourceLaplaceV L (-n) = -sourceLaplaceV L n := by
  simp [sourceLaplaceV, neg_div]

/-- A reversal-even vector has zero odd Laplace moment. -/
theorem sum_sourceLaplaceV_mul_eq_zero_of_even (L : ℝ) (K : ℕ) {x : Fin (2 * K + 1) → ℂ}
    (hx : ∀ i : Fin (2 * K + 1), x i.rev = x i) :
    ∑ i, (sourceLaplaceV L (centeredIndex K i) : ℂ) * x i = 0 := by
  set S := ∑ i, (sourceLaplaceV L (centeredIndex K i) : ℂ) * x i
  have hrev : S = ∑ i : Fin (2 * K + 1), (sourceLaplaceV L (centeredIndex K i.rev) : ℂ) * x i.rev :=
    (Equiv.sum_comp Fin.revPerm (fun i => (sourceLaplaceV L (centeredIndex K i) : ℂ) * x i)).symm
  have hneg : S = -S := by
    conv_lhs => rw [hrev]
    simp only [centeredIndex_rev, sourceLaplaceV_neg, hx, Complex.ofReal_neg, neg_mul,
      Finset.sum_neg_distrib, S]
  have h2 : (2 : ℂ) * S = 0 := by linear_combination hneg
  simpa using h2

/-- A reversal-odd vector has zero even Laplace moment. -/
theorem sum_sourceLaplaceU_mul_eq_zero_of_odd (L : ℝ) (K : ℕ) {x : Fin (2 * K + 1) → ℂ}
    (hx : ∀ i : Fin (2 * K + 1), x i.rev = -x i) :
    ∑ i, (sourceLaplaceU L (centeredIndex K i) : ℂ) * x i = 0 := by
  set S := ∑ i, (sourceLaplaceU L (centeredIndex K i) : ℂ) * x i
  have hrev : S = ∑ i : Fin (2 * K + 1), (sourceLaplaceU L (centeredIndex K i.rev) : ℂ) * x i.rev :=
    (Equiv.sum_comp Fin.revPerm (fun i => (sourceLaplaceU L (centeredIndex K i) : ℂ) * x i)).symm
  have hneg : S = -S := by
    conv_lhs => rw [hrev]
    simp only [centeredIndex_rev, sourceLaplaceU_neg, hx, mul_neg, Finset.sum_neg_distrib, S]
  have h2 : (2 : ℂ) * S = 0 := by linear_combination hneg
  simpa using h2

/-- On reversal-even vectors the Laplace-weighted source energy is the rank-one
square `(8/L)|∑ u_i x_i|² ≥ 0` (semidefinite, not definite). -/
theorem integral_exp_neg_half_mul_sourceEnergy_of_even {L : ℝ} (hL : 0 < L) (K : ℕ)
    {x : Fin (2 * K + 1) → ℂ} (hx : ∀ i : Fin (2 * K + 1), x i.rev = x i) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t / 2) * (quadraticForm (sourceMatrix (t / L) K) x).re =
      8 / L * Complex.normSq (∑ i, (sourceLaplaceU L (centeredIndex K i) : ℂ) * x i) := by
  rw [integral_exp_neg_half_mul_sourceEnergy hL, sum_sourceLaplaceV_mul_eq_zero_of_even L K hx]
  simp

/-- On reversal-odd vectors it is `-(8/L) a² |∑ v_i x_i|² ≤ 0`. -/
theorem integral_exp_neg_half_mul_sourceEnergy_of_odd {L : ℝ} (hL : 0 < L) (K : ℕ)
    {x : Fin (2 * K + 1) → ℂ} (hx : ∀ i : Fin (2 * K + 1), x i.rev = -x i) :
    ∫ t in Ioi (0 : ℝ), Real.exp (-t / 2) * (quadraticForm (sourceMatrix (t / L) K) x).re =
      -(8 / L * sourceLaplaceScale L ^ 2 *
        Complex.normSq (∑ i, (sourceLaplaceV L (centeredIndex K i) : ℂ) * x i)) := by
  rw [integral_exp_neg_half_mul_sourceEnergy hL, sum_sourceLaplaceU_mul_eq_zero_of_odd L K hx]
  simp
  ring

end Zeta23.CCM

#print axioms Zeta23.CCM.integrableOn_mul_cexp_Ioi
#print axioms Zeta23.CCM.integral_cexp_Ioi_zero
#print axioms Zeta23.CCM.integral_mul_cexp_Ioi_zero
#print axioms Zeta23.CCM.integral_exp_neg_half_mul_sin_Ioi
#print axioms Zeta23.CCM.integral_exp_neg_half_mul_mul_cos_Ioi
#print axioms Zeta23.CCM.integrableOn_exp_neg_half_mul_sin
#print axioms Zeta23.CCM.integrableOn_exp_neg_half_mul_mul_cos
#print axioms Zeta23.CCM.integral_exp_neg_half_mul_sourceEntryReal
#print axioms Zeta23.CCM.integrableOn_exp_neg_half_mul_sourceEntryReal
#print axioms Zeta23.CCM.integral_exp_neg_half_mul_sourceEnergy
#print axioms Zeta23.CCM.sourceLaplaceU_neg
#print axioms Zeta23.CCM.sourceLaplaceV_neg
#print axioms Zeta23.CCM.sum_sourceLaplaceV_mul_eq_zero_of_even
#print axioms Zeta23.CCM.sum_sourceLaplaceU_mul_eq_zero_of_odd
#print axioms Zeta23.CCM.integral_exp_neg_half_mul_sourceEnergy_of_even
#print axioms Zeta23.CCM.integral_exp_neg_half_mul_sourceEnergy_of_odd
