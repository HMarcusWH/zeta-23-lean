import Zeta23.OPICARound2.CausalProbe
import Zeta23.OPICAFollowup.LogFourierSobolev
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# The physical positive-half-line logarithmic adapter

The literal logarithmic unitary is constructed on actual L2 equivalence
classes, with its actual inverse and surjectivity. The literal compact source
has one-sided C1 regularity, its actual Mellin formula and mean zero. Its
mean-subtracted integer adapter gives the unchanged native completion and
all original dictionary dilations.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency.types false
open Set MeasureTheory
open scoped Topology ENNReal Convolution

namespace Zeta23.OPICARound2

/-- The prescribed reversal of the positive-half-line logarithmic unitary. -/
def reversedLogUnitary (f : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-t / 2) : ℂ) * f (Real.exp (-t))

theorem reversedLogUnitary_norm_sq (f : ℝ → ℂ) (t : ℝ) :
    ‖reversedLogUnitary f t‖ ^ 2 =
      Real.exp (-t) * ‖f (Real.exp (-t))‖ ^ 2 := by
  rw [reversedLogUnitary, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (Real.exp_nonneg _), mul_pow]
  congr 1
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- Exact whole-line energy conversion; no source derivative premise is needed. -/
theorem reversedLogUnitary_integral_norm_sq (f : ℝ → ℂ) :
    (∫ t : ℝ, ‖reversedLogUnitary f t‖ ^ 2) =
      ∫ x : ℝ in Ioi 0, ‖f x‖ ^ 2 := by
  simp_rw [reversedLogUnitary_norm_sq]
  calc
    (∫ t : ℝ, Real.exp (-t) * ‖f (Real.exp (-t))‖ ^ 2) =
        ∫ t : ℝ, Real.exp t * ‖f (Real.exp t)‖ ^ 2 :=
      integral_neg_eq_self (fun t : ℝ => Real.exp t * ‖f (Real.exp t)‖ ^ 2)
        volume
    _ = _ := by
      simpa only [smul_eq_mul] using
        OPICAFollowup.integral_exp_smul_comp (fun x : ℝ => ‖f x‖ ^ 2)

theorem reversedLogUnitary_integrable_norm_sq_iff (f : ℝ → ℂ) :
    Integrable (fun t : ℝ => ‖reversedLogUnitary f t‖ ^ 2) ↔
      IntegrableOn (fun x : ℝ => ‖f x‖ ^ 2) (Ioi 0) := by
  simp_rw [reversedLogUnitary_norm_sq]
  have hn : Integrable (fun t : ℝ => Real.exp (-t) * ‖f (Real.exp (-t))‖ ^ 2) ↔
      Integrable (fun t : ℝ => Real.exp t * ‖f (Real.exp t)‖ ^ 2) := by
    constructor
    · intro h; simpa using h.comp_neg
    · intro h; exact h.comp_neg
  exact hn.trans
      (by simpa only [smul_eq_mul] using
        OPICAFollowup.integrable_exp_smul_comp_iff (fun x : ℝ => ‖f x‖ ^ 2))

/-- The literal inverse on the positive half-line. Its value at zero does not
enter either L2 space. -/
def reversedLogInverse (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  if 0 < x then (Real.exp (-Real.log x / 2) : ℂ) * g (-Real.log x) else 0

theorem reversedLogUnitary_inverse (g : ℝ → ℂ) :
    reversedLogUnitary (reversedLogInverse g) = g := by
  ext t
  simp only [reversedLogUnitary, reversedLogInverse, Real.exp_pos, if_pos,
    Real.log_exp, neg_neg]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  rw [show -t / 2 + t / 2 = (0 : ℝ) by ring, Real.exp_zero]
  simp

theorem reversedLogInverse_unitary (f : ℝ → ℂ) {x : ℝ} (hx : 0 < x) :
    reversedLogInverse (reversedLogUnitary f) x = f x := by
  rw [reversedLogInverse, if_pos hx, reversedLogUnitary]
  simp only [neg_neg, Real.exp_log hx]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  rw [show -Real.log x / 2 + Real.log x / 2 = (0 : ℝ) by ring, Real.exp_zero]
  simp

theorem reversedLogInverse_integral_norm_sq (g : ℝ → ℂ) :
    (∫ x : ℝ in Ioi 0, ‖reversedLogInverse g x‖ ^ 2) =
      ∫ t : ℝ, ‖g t‖ ^ 2 := by
  rw [← reversedLogUnitary_integral_norm_sq, reversedLogUnitary_inverse]

theorem reversedLogInverse_integrable_norm_sq_iff (g : ℝ → ℂ) :
    IntegrableOn (fun x : ℝ => ‖reversedLogInverse g x‖ ^ 2) (Ioi 0) ↔
      Integrable (fun t : ℝ => ‖g t‖ ^ 2) := by
  rw [← reversedLogUnitary_integrable_norm_sq_iff, reversedLogUnitary_inverse]

theorem reversedLogUnitary_congr_ae {f g : ℝ → ℂ}
    (hfg : f =ᵐ[volume.restrict (Ioi 0)] g) :
    reversedLogUnitary f =ᵐ[volume] reversedLogUnitary g := by
  have hz : (fun x : ℝ => ‖f x - g x‖ ^ 2) =ᵐ[volume.restrict (Ioi 0)] 0 :=
    hfg.mono fun x hx => by simp [hx]
  have hi : IntegrableOn (fun x : ℝ => ‖f x - g x‖ ^ 2) (Ioi 0) :=
    (integrable_zero ℝ ℝ (volume.restrict (Ioi (0 : ℝ)))).congr hz.symm
  have hmi := (reversedLogUnitary_integrable_norm_sq_iff (fun x => f x - g x)).mpr hi
  have hmzero : (∫ t : ℝ, ‖reversedLogUnitary (fun x => f x - g x) t‖ ^ 2) = 0 := by
    rw [reversedLogUnitary_integral_norm_sq]
    exact integral_eq_zero_of_ae hz
  have hae := (integral_eq_zero_iff_of_nonneg (fun _ => sq_nonneg _) hmi).mp hmzero
  filter_upwards [hae] with t ht
  have hval : reversedLogUnitary (fun x => f x - g x) t = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp ht)
  unfold reversedLogUnitary at hval ⊢
  rw [mul_sub, sub_eq_zero] at hval
  exact hval

abbrev PositiveProbeL2 := Lp ℂ 2 (volume.restrict (Ioi (0 : ℝ)))

theorem reversedLogUnitary_memLp (f : PositiveProbeL2) :
    MemLp (reversedLogUnitary f) 2 volume := by
  have hm : Measurable (reversedLogUnitary f) := by
    unfold reversedLogUnitary
    exact (by fun_prop : Measurable (fun t : ℝ => (Real.exp (-t / 2) : ℂ))).mul
      ((Lp.stronglyMeasurable f).measurable.comp (by fun_prop))
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  exact (reversedLogUnitary_integrable_norm_sq_iff f).mpr
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp f).1).mp (Lp.memLp f))

def reversedLogL2Value (f : PositiveProbeL2) : ProbeL2 :=
  (reversedLogUnitary_memLp f).toLp (reversedLogUnitary f)

theorem reversedLogL2Value_coeFn (f : PositiveProbeL2) :
    reversedLogL2Value f =ᵐ[volume] reversedLogUnitary f :=
  (reversedLogUnitary_memLp f).coeFn_toLp

private theorem positiveProbeL2_norm_sq (f : PositiveProbeL2) :
    ‖f‖ ^ 2 = ∫ x : ℝ in Ioi 0, ‖f x‖ ^ 2 := by
  have h1 : (‖f‖ ^ 2 : ℂ) = inner ℂ f f := (inner_self_eq_norm_sq_to_K f).symm
  rw [MeasureTheory.L2.inner_def] at h1
  have h2 : (∫ x : ℝ in Ioi 0, inner ℂ (f x) (f x)) =
      ((∫ x : ℝ in Ioi 0, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1
    ext x
    rw [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [h2] at h1
  exact_mod_cast h1

theorem reversedLogL2Value_norm (f : PositiveProbeL2) : ‖reversedLogL2Value f‖ = ‖f‖ := by
  have hs : ‖reversedLogL2Value f‖ ^ 2 = ‖f‖ ^ 2 := by
    rw [OPICAFollowup.L2_norm_sq_eq_integral, positiveProbeL2_norm_sq]
    rw [← reversedLogUnitary_integral_norm_sq]
    exact integral_congr_ae ((reversedLogL2Value_coeFn f).mono fun t ht => by dsimp only; rw [ht])
  nlinarith [norm_nonneg (reversedLogL2Value f), norm_nonneg f]

def reversedLogL2 : PositiveProbeL2 →ₗᵢ[ℂ] ProbeL2 where
  toFun := reversedLogL2Value
  map_add' f g := by
    apply Lp.ext
    have hinput := reversedLogUnitary_congr_ae (Lp.coeFn_add f g)
    filter_upwards [reversedLogL2Value_coeFn (f + g), reversedLogL2Value_coeFn f,
      reversedLogL2Value_coeFn g, Lp.coeFn_add (reversedLogL2Value f) (reversedLogL2Value g),
      hinput] with t hsum hf hg hout hin
    have hout' : ((reversedLogL2Value f + reversedLogL2Value g : ProbeL2) : ℝ → ℂ) t =
        reversedLogL2Value f t + reversedLogL2Value g t := by
      simpa only [Pi.add_apply] using hout
    rw [hsum, hout', hf, hg, hin]
    unfold reversedLogUnitary
    simp only [Pi.add_apply, mul_add]
  map_smul' c f := by
    change reversedLogL2Value (c • f) = c • reversedLogL2Value f
    apply Lp.ext
    have hinput := reversedLogUnitary_congr_ae (Lp.coeFn_smul c f)
    filter_upwards [reversedLogL2Value_coeFn (c • f), reversedLogL2Value_coeFn f,
      Lp.coeFn_smul c (reversedLogL2Value f), hinput] with t hsum hf hout hin
    have hout' : ((c • reversedLogL2Value f : ProbeL2) : ℝ → ℂ) t =
        c * reversedLogL2Value f t := by simpa only [Pi.smul_apply, smul_eq_mul] using hout
    rw [hsum, hout', hf, hin]
    unfold reversedLogUnitary
    simp only [Pi.smul_apply, smul_eq_mul, mul_left_comm]
  norm_map' := reversedLogL2Value_norm

theorem reversedLogInverse_memLp (g : ProbeL2) :
    MemLp (reversedLogInverse g) 2 (volume.restrict (Ioi 0)) := by
  have hm : Measurable (reversedLogInverse g) := by
    unfold reversedLogInverse
    apply Measurable.ite measurableSet_Ioi
    · exact (by fun_prop : Measurable (fun x : ℝ => (Real.exp (-Real.log x / 2) : ℂ))).mul
        ((Lp.stronglyMeasurable g).measurable.comp (by fun_prop))
    · exact measurable_const
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  exact (reversedLogInverse_integrable_norm_sq_iff g).mpr
    ((memLp_two_iff_integrable_sq_norm (Lp.memLp g).1).mp (Lp.memLp g))

theorem reversedLogL2_surjective : Function.Surjective reversedLogL2 := by
  intro g
  let f : PositiveProbeL2 := (reversedLogInverse_memLp g).toLp (reversedLogInverse g)
  refine ⟨f, ?_⟩
  apply Lp.ext
  have hf := reversedLogUnitary_congr_ae (reversedLogInverse_memLp g).coeFn_toLp
  apply (reversedLogL2Value_coeFn f).trans
  apply hf.trans
  exact Filter.Eventually.of_forall fun t => congrFun (reversedLogUnitary_inverse g) t

/-- The actual positive-half-line L2 space and full-line L2 space are unitarily
identified by the prescribed physical logarithmic formula. -/
def reversedLogL2Equiv : PositiveProbeL2 ≃ₗᵢ[ℂ] ProbeL2 :=
  LinearIsometryEquiv.ofSurjective reversedLogL2 reversedLogL2_surjective

/-! The following actual-source tail lemmas are moved verbatim from the
checked ProbeGram origin recorded in the build evidence. -/

theorem jPlusDamping_integrable (z : ℂ) :
    Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (jPlus t : ℂ)) := by
  have hc : HasCompactSupport
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (jPlus t : ℂ)) := by
    apply HasCompactSupport.intro (K := Icc 0 (2 * probeSigma)) isCompact_Icc
    intro t ht
    rw [jPlus_zero_outside ht, Complex.ofReal_zero, mul_zero]
  have hcont : Continuous
      (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (jPlus t : ℂ)) := by
    exact (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal)).mul
      (Complex.continuous_ofReal.comp jPlus_contDiff.continuous)
  exact hcont.integrable_of_hasCompactSupport hc

theorem probeV_source_first (t : ℝ) :
    probeV t = ∫ s : ℝ, (probeC (t - s) : ℂ) * (jPlus s : ℂ) := by
  have h := integral_sub_left_eq_self
    (fun s : ℝ => (probeC s : ℂ) * (jPlus (t - s) : ℂ)) t
    (μ := (volume : Measure ℝ))
  simpa only [sub_sub_cancel, probeV] using h.symm

theorem probeV_tail {t : ℝ} (ht : 2 * probeSigma ≤ t) :
    probeV t = 2 * JPlus (-3 / 2 : ℂ) * Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) := by
  have hp (s : ℝ) : (probeC (t - s) : ℂ) * (jPlus s : ℂ) =
      (-Complex.exp (-(1 / 2 : ℂ) * (t : ℂ))) *
        (Complex.exp (-(-1 / 2 : ℂ) * (s : ℂ)) * (jPlus s : ℂ)) +
      (2 * Complex.exp (-(3 / 2 : ℂ) * (t : ℂ))) *
        (Complex.exp (-(-3 / 2 : ℂ) * (s : ℂ)) * (jPlus s : ℂ)) := by
    by_cases hs : s ∈ Icc 0 (2 * probeSigma)
    · have hts : 0 ≤ t - s := by linarith [hs.2]
      simp only [probeC, CCM.nativeCompletionCorrection, if_pos hts,
        Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_mul,
        Complex.ofReal_exp, Complex.ofReal_ofNat]
      have he1 : Complex.exp (((-((t - s) / 2) : ℝ) : ℂ)) =
          Complex.exp (-(1 / 2 : ℂ) * (t : ℂ)) *
            Complex.exp (-(-1 / 2 : ℂ) * (s : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      have he3 : Complex.exp (((-(3 * (t - s) / 2) : ℝ) : ℂ)) =
          Complex.exp (-(3 / 2 : ℂ) * (t : ℂ)) *
            Complex.exp (-(-3 / 2 : ℂ) * (s : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp only [Complex.ofReal_neg] at he1 he3
      rw [he1, he3]
      ring
    · rw [jPlus_zero_outside hs, Complex.ofReal_zero]
      ring
  rw [probeV_source_first, integral_congr_ae (Filter.Eventually.of_forall hp),
    integral_add ((jPlusDamping_integrable (-1 / 2)).const_mul _)
      ((jPlusDamping_integrable (-3 / 2)).const_mul _), integral_const_mul,
    integral_const_mul]
  change -Complex.exp (-(1 / 2 : ℂ) * (t : ℂ)) * JPlus (-1 / 2) +
    (2 * Complex.exp (-(3 / 2 : ℂ) * (t : ℂ))) * JPlus (-3 / 2) = _
  rw [JPlus_neg_half, mul_zero, zero_add]
  ring

def probeBoundaryEpsilon (n : ℕ) : ℝ := 1 / ((n : ℝ) + 3)

theorem probeBoundaryEpsilon_pos (n : ℕ) : 0 < probeBoundaryEpsilon n := by
  unfold probeBoundaryEpsilon
  positivity

theorem probeBoundaryEpsilon_lt_half (n : ℕ) : probeBoundaryEpsilon n < 1 / 2 := by
  unfold probeBoundaryEpsilon
  apply (div_lt_iff₀ (by positivity : 0 < (n : ℝ) + 3)).2
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

theorem probeBoundaryEpsilon_tendsto :
    Filter.Tendsto probeBoundaryEpsilon Filter.atTop (𝓝 0) := by
  change Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 3)) Filter.atTop (𝓝 0)
  have h := (Filter.tendsto_add_atTop_iff_nat 2).2
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  simpa only [Nat.cast_add, Nat.cast_ofNat, add_assoc,
    show (2 : ℝ) + 1 = 3 by norm_num] using h

def probeBoundaryParameter (tau : ℝ) (n : ℕ) : ℂ :=
  (probeBoundaryEpsilon n : ℂ) + Complex.I * (tau : ℂ)

theorem probeBoundaryParameter_re (tau : ℝ) (n : ℕ) :
    (probeBoundaryParameter tau n).re = probeBoundaryEpsilon n := by
  simp [probeBoundaryParameter, Complex.mul_re]

theorem probeBoundaryParameter_pos (tau : ℝ) (n : ℕ) :
    0 < (probeBoundaryParameter tau n).re := by
  rw [probeBoundaryParameter_re]
  exact probeBoundaryEpsilon_pos n

theorem probeBoundaryParameter_ne_half (tau : ℝ) (n : ℕ) :
    probeBoundaryParameter tau n ≠ (1 / 2 : ℂ) := by
  intro h
  have hr := congrArg Complex.re h
  rw [probeBoundaryParameter_re] at hr
  norm_num at hr
  linarith [probeBoundaryEpsilon_lt_half n]

theorem probeBoundaryParameter_tendsto (tau : ℝ) :
    Filter.Tendsto (probeBoundaryParameter tau) Filter.atTop (𝓝 (Complex.I * (tau : ℂ))) := by
  change Filter.Tendsto (fun n : ℕ => (probeBoundaryEpsilon n : ℂ) + Complex.I * (tau : ℂ))
    Filter.atTop (𝓝 (Complex.I * (tau : ℂ)))
  have h := ((Complex.continuous_ofReal.tendsto 0).comp probeBoundaryEpsilon_tendsto).add_const
    (Complex.I * (tau : ℂ))
  simpa only [Function.comp_def, Complex.ofReal_zero, zero_add] using h

/-- Genuine dominated convergence from the right half-plane. The function may
be any actual causal L1 representative; no boundary transform is a premise. -/
theorem probeLaplace_boundary_tendsto (f : ℝ → ℂ) (hf : Integrable f)
    (hf0 : ∀ᵐ t : ℝ, t < 0 → f t = 0) (tau : ℝ) :
    Filter.Tendsto (fun n : ℕ => probeLaplace f (probeBoundaryParameter tau n))
      Filter.atTop (𝓝 (probeLaplace f (Complex.I * (tau : ℂ)))) := by
  unfold probeLaplace
  apply tendsto_integral_of_dominated_convergence (fun t : ℝ => ‖f t‖)
  · intro n
    have hc : Continuous (fun t : ℝ =>
        Complex.exp (-probeBoundaryParameter tau n * (t : ℂ))) := by fun_prop
    exact hc.aestronglyMeasurable.mul hf.aestronglyMeasurable
  · exact hf.norm
  · intro n
    filter_upwards [hf0] with t ht
    by_cases hneg : t < 0
    · simp only [ht hneg, mul_zero, norm_zero, le_refl]
    · have ht0 : 0 ≤ t := le_of_not_gt hneg
      have hr : (-probeBoundaryParameter tau n * (t : ℂ)).re =
          -probeBoundaryEpsilon n * t := by
        simp only [Complex.mul_re, Complex.neg_re, probeBoundaryParameter_re,
          Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      rw [norm_mul, Complex.norm_exp, hr]
      have he : Real.exp (-probeBoundaryEpsilon n * t) ≤ 1 :=
        Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg (probeBoundaryEpsilon_pos n).le ht0])
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg (f t))
  · filter_upwards with t
    exact ((Complex.continuous_exp.tendsto _).comp
      ((probeBoundaryParameter_tendsto tau).neg.mul_const (t : ℂ))).mul_const (f t)


theorem nativeCompletionLaplace_boundary (tau : ℝ) :
    CCM.nativePositiveCompletionLaplace (Complex.I * (tau : ℂ)) =
      CCM.nativeCompletionRationalMultiplier (Complex.I * (tau : ℂ)) *
        riemannZeta (Complex.I * (tau : ℂ) + 1 / 2) := by
  have hz := probeBoundaryParameter_tendsto tau
  have hR :=
    (CCM.nativeCompletionRationalMultiplier_analyticAt
      (by simp [Complex.mul_re] : 0 ≤ (Complex.I * (tau : ℂ)).re)).continuousAt.tendsto.comp hz
  have hne : Complex.I * (tau : ℂ) + 1 / 2 ≠ (1 : ℂ) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [Complex.mul_re] at hr
  have hZ := (analyticOn_riemannZeta _ hne).continuousAt.tendsto.comp
    (hz.add_const (1 / 2 : ℂ))
  have hprod := hR.mul hZ
  have hA : Filter.Tendsto
      (fun n => probeLaplace (fun t : ℝ => (CCM.nativePositiveCompletion t : ℂ))
        (probeBoundaryParameter tau n)) Filter.atTop
      (𝓝 (CCM.nativeCompletionRationalMultiplier (Complex.I * (tau : ℂ)) *
        riemannZeta (Complex.I * (tau : ℂ) + 1 / 2))) := by
    apply hprod.congr'
    exact Filter.Eventually.of_forall fun n =>
      (CCM.nativePositiveCompletion_complexLaplace (probeBoundaryParameter_pos tau n)
        (probeBoundaryParameter_ne_half tau n)).symm
  exact tendsto_nhds_unique
    (probeLaplace_boundary_tendsto _ CCM.nativePositiveCompletion_integrable.ofReal
      (Filter.Eventually.of_forall fun _ ht => by
        rw [CCM.nativePositiveCompletion_eq_zero_of_neg ht]
        rfl) tau) hA



/-- Fourier testing is injective on actual L1 intersection L2 representatives.
This is a direct consequence of the pinned Plancherel theorem. -/
theorem probeL1L2Fourier_zero_ae (f : ℝ → ℂ) (hf1 : Integrable f)
    (hf2 : MemLp f 2 volume)
    (hF : ∀ tau : ℝ, OPICAFollowup.logFourier f tau = 0) : f =ᵐ[volume] 0 := by
  have hp := OPICAFollowup.logFourier_plancherel hf1 hf2
  have he : (∫ t : ℝ, ‖f t‖ ^ 2) = 0 := by
    rw [hp.2]
    simp_rw [hF]
    simp
  have hi := (memLp_two_iff_integrable_sq_norm hf2.1).mp hf2
  have hae := (integral_eq_zero_iff_of_nonneg (fun t : ℝ => sq_nonneg ‖f t‖) hi).mp he
  filter_upwards [hae] with t ht
  apply norm_eq_zero.mp
  have hn := norm_nonneg (f t)
  change ‖f t‖ ^ 2 = 0 at ht
  nlinarith

/-- Causal L2 Laplace uniqueness, proved through one strictly positive damping
and the actual L1/L2 Fourier theorem. No range density or zeta hypothesis enters. -/
theorem probeCausalLaplace_injective (f : CausalProbeL2)
    (h : ∀ z : ℂ, 0 < z.re → CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) = 0) : f = 0 := by
  let g : ℝ → ℂ := fun t => Complex.exp (-(t : ℂ)) * (f : ProbeL2) t
  have hg1 : Integrable g := by
    simpa only [pow_zero, one_mul, Complex.one_re, neg_mul, one_mul] using
      CCM.nativeCausalLaplaceMoment_integrable (1 : ℂ) (by norm_num) 0 f
  have hgm : AEStronglyMeasurable g volume :=
    (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-(t : ℂ)))).aestronglyMeasurable.mul
      (Lp.stronglyMeasurable (f : ProbeL2)).aestronglyMeasurable
  have hg2 : MemLp g 2 volume := by
    apply (Lp.memLp (f : ProbeL2)).mono hgm
    filter_upwards [f.property] with t ht
    by_cases hneg : t < 0
    · simp [g, ht hneg]
    · have ht0 : 0 ≤ t := le_of_not_gt hneg
      change ‖Complex.exp (-(t : ℂ)) * (f : ProbeL2) t‖ ≤ _
      rw [norm_mul, Complex.norm_exp]
      have he : Real.exp (-(t : ℂ)).re ≤ 1 :=
        Real.exp_le_one_iff.mpr (by simpa using neg_nonpos.mpr ht0)
      simpa only [one_mul] using mul_le_mul_of_nonneg_right he (norm_nonneg ((f : ProbeL2) t))
  have hFg (tau : ℝ) : OPICAFollowup.logFourier g tau = 0 := by
    have hh := h (1 + Complex.I * (tau : ℂ)) (by simp [Complex.mul_re])
    rw [OPICAFollowup.logFourier]
    unfold CCM.nativeCausalLaplaceMoment at hh
    rw [← hh]
    apply integral_congr_ae
    filter_upwards with t
    simp only [g, pow_zero, one_mul]
    rw [← mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    ring
  have hg0 := probeL1L2Fourier_zero_ae g hg1 hg2 hFg
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [hg0, Lp.coeFn_zero (α := ℝ) (E := ℂ) (p := 2) (μ := volume)] with t ht hz
  change (f : ProbeL2) t = (0 : ProbeL2) t
  rw [hz]
  change Complex.exp (-(t : ℂ)) * (f : ProbeL2) t = 0 at ht
  exact (mul_eq_zero.mp ht).resolve_left (Complex.exp_ne_zero _)

/-- Equality follows from equality of all actual causal Laplace evaluations. -/
theorem probeCausalLaplace_ext (f g : CausalProbeL2)
    (h : ∀ z : ℂ, 0 < z.re →
      CCM.nativeCausalLaplaceMoment z 0 (f : ProbeL2) =
        CCM.nativeCausalLaplaceMoment z 0 (g : ProbeL2)) : f = g := by
  apply sub_eq_zero.mp
  apply probeCausalLaplace_injective (f - g)
  intro z hz
  unfold CCM.nativeCausalLaplaceMoment
  have heq : (fun t : ℝ => (t : ℂ)^0 * Complex.exp (-z * (t : ℂ)) *
      ((f - g : CausalProbeL2) : ProbeL2) t) =ᵐ[volume]
      fun t : ℝ => (t : ℂ)^0 * Complex.exp (-z * (t : ℂ)) * (f : ProbeL2) t -
        (t : ℂ)^0 * Complex.exp (-z * (t : ℂ)) * (g : ProbeL2) t := by
    filter_upwards [Lp.coeFn_sub (f : ProbeL2) (g : ProbeL2)] with t ht
    change _ * _ * ((f : ProbeL2) - (g : ProbeL2)) t = _
    rw [ht]
    change _ * _ * ((f : ProbeL2) t - (g : ProbeL2) t) = _
    ring
  rw [integral_congr_ae heq,
    integral_sub (CCM.nativeCausalLaplaceMoment_integrable z hz 0 f)
      (CCM.nativeCausalLaplaceMoment_integrable z hz 0 g)]
  exact sub_eq_zero.mpr (h z hz)

theorem probeFourierDamping_integrable {f : ℝ → ℂ} (hf : Integrable f) (tau : ℝ) :
    Integrable (fun t : ℝ => Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I) * f t) := by
  have hm : AEStronglyMeasurable
      (fun t : ℝ => Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I) * f t) volume :=
    (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-((tau * t : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable.mul
      hf.aestronglyMeasurable
  apply hf.norm.mono' hm
  filter_upwards with t
  rw [norm_mul, Complex.norm_exp]
  simp

theorem probeL1L2Fourier_ext (f g : ℝ → ℂ) (hf1 : Integrable f) (hg1 : Integrable g)
    (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume)
    (hF : ∀ tau : ℝ, OPICAFollowup.logFourier f tau = OPICAFollowup.logFourier g tau) :
    f =ᵐ[volume] g := by
  have hzero : ∀ tau : ℝ, OPICAFollowup.logFourier (f - g) tau = 0 := by
    intro tau
    unfold OPICAFollowup.logFourier
    simp only [Pi.sub_apply, mul_sub]
    rw [integral_sub (probeFourierDamping_integrable hf1 tau)
      (probeFourierDamping_integrable hg1 tau)]
    exact sub_eq_zero.mpr (hF tau)
  have hz := probeL1L2Fourier_zero_ae (f - g) (hf1.sub hg1) (hf2.sub hg2) hzero
  filter_upwards [hz] with t ht
  exact sub_eq_zero.mp ht


/-- The compact source is the literal inverse logarithmic transform of V.
The value at the endpoint zero is prescribed rather than inferred by division. -/
def nativeMuntzKernel (x : ℝ) : ℂ := reversedLogInverse probeV x

theorem nativeMuntzKernel_zero : nativeMuntzKernel 0 = 0 := by
  simp [nativeMuntzKernel, reversedLogInverse]

theorem nativeMuntzKernel_of_pos {x : ℝ} (hx : 0 < x) :
    nativeMuntzKernel x = ((Real.sqrt x)⁻¹ : ℂ) * probeV (-Real.log x) := by
  have hs : Real.sqrt x = Real.exp (Real.log x / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hx]
    congr 1
    ring
  rw [nativeMuntzKernel, reversedLogInverse, if_pos hx, hs]
  have he : (Real.exp (-Real.log x / 2) : ℂ) = (Real.exp (Real.log x / 2) : ℂ)⁻¹ := by
    rw [← Complex.ofReal_inv, ← Real.exp_neg]
    congr 1
    congr 1
    ring
  rw [he]

theorem probeV_contDiff : ContDiff ℝ (⊤ : ℕ∞) probeV := by
  have hj : HasCompactSupport (fun t : ℝ => (jPlus t : ℂ)) :=
    jPlus_hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (jPlus t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp jPlus_contDiff
  exact hj.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    probeC_integrable.ofReal.locallyIntegrable hc

theorem nativeMuntzKernel_zero_outside {x : ℝ} (hx : x ∉ Icc (0 : ℝ) 1) :
    nativeMuntzKernel x = 0 := by
  by_cases hp : 0 < x
  · have hx1 : 1 < x := by
      by_contra hn
      exact hx ⟨hp.le, le_of_not_gt hn⟩
    have ht : -Real.log x < 0 := by linarith [Real.log_pos hx1]
    rw [nativeMuntzKernel, reversedLogInverse, if_pos hp, probeV_zero_of_neg ht, mul_zero]
  · simp [nativeMuntzKernel, reversedLogInverse, hp]

theorem nativeMuntzKernel_hasCompactSupport : HasCompactSupport nativeMuntzKernel :=
  HasCompactSupport.intro isCompact_Icc (fun _ hx => nativeMuntzKernel_zero_outside hx)

theorem nativeMuntzKernel_linear_near_zero {x : ℝ} (hx : 0 ≤ x)
    (hsmall : x ≤ Real.exp (-2 * probeSigma)) :
    nativeMuntzKernel x = (2 * JPlus (-3 / 2 : ℂ)) * (x : ℂ) := by
  rcases eq_or_lt_of_le hx with hx0 | hxp
  · subst x
    simp [nativeMuntzKernel_zero]
  · have hlog : Real.log x ≤ -2 * probeSigma := by
      have h := Real.log_le_log hxp hsmall
      rwa [Real.log_exp] at h
    have ht : 2 * probeSigma ≤ -Real.log x := by linarith
    rw [nativeMuntzKernel, reversedLogInverse, if_pos hxp, probeV_tail ht]
    have he : (Real.exp (-Real.log x / 2) : ℂ) *
        Complex.exp (-(3 / 2 : ℂ) * ((-Real.log x : ℝ) : ℂ)) = (x : ℂ) := by
      rw [Complex.ofReal_exp, ← Complex.exp_add]
      have hh : ((-Real.log x / 2 : ℝ) : ℂ) +
          -(3 / 2 : ℂ) * ((-Real.log x : ℝ) : ℂ) = (Real.log x : ℂ) := by
        push_cast
        ring
      rw [hh, ← Complex.ofReal_exp, Real.exp_log hxp]
    calc
      _ = (2 * JPlus (-3 / 2 : ℂ)) * ((Real.exp (-Real.log x / 2) : ℂ) *
        Complex.exp (-(3 / 2 : ℂ) * ((-Real.log x : ℝ) : ℂ))) := by ring
      _ = _ := by rw [he]

theorem JPlus_neg_three_half_ne_zero : JPlus (-3 / 2 : ℂ) ≠ 0 := by
  rw [JPlus_one_copy_formula]
  apply mul_ne_zero (Complex.exp_ne_zero _)
  apply mul_ne_zero
  · norm_num [mul_pow, Complex.I_sq]
  · exact CCM.UniversalSinc.product_ne_zero_of_im_ne_zero probeSigma_pos (by norm_num)

theorem nativeMuntzKernel_right_slope_ne_zero : (2 * JPlus (-3 / 2 : ℂ)) ≠ 0 :=
  mul_ne_zero (by norm_num) JPlus_neg_three_half_ne_zero

theorem nativeMuntzKernel_contDiffAt {x : ℝ} (hx : 0 < x) :
    ContDiffAt ℝ (⊤ : ℕ∞) nativeMuntzKernel x := by
  have hl : ContDiffAt ℝ (⊤ : ℕ∞) Real.log x := Real.contDiffAt_log.mpr hx.ne'
  have hg : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun y : ℝ => (Real.exp (-Real.log y / 2) : ℂ) * probeV (-Real.log y)) x := by
    exact (Complex.ofRealCLM.contDiff.contDiffAt.comp x
      (Real.contDiff_exp.contDiffAt.comp x (hl.neg.div_const 2))).mul
        (probeV_contDiff.contDiffAt.comp x hl.neg)
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact if_pos hy

theorem nativeMuntzKernel_contDiffOn_halfline :
    ContDiffOn ℝ 1 nativeMuntzKernel (Ici (0 : ℝ)) := by
  intro x hx
  change 0 ≤ x at hx
  rcases eq_or_lt_of_le hx with hx0 | hxp
  · subst x
    have hlin : nativeMuntzKernel =ᶠ[𝓝[Ici (0 : ℝ)] 0]
        fun y : ℝ => (2 * JPlus (-3 / 2 : ℂ)) * (y : ℂ) := by
      filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Iio_mem_nhds (Real.exp_pos (-2 * probeSigma)))] with y hy hs
      exact nativeMuntzKernel_linear_near_zero (show 0 ≤ y from hy)
        (show y < Real.exp (-2 * probeSigma) from hs).le
    have hg : ContDiffWithinAt ℝ 1
        (fun y : ℝ => (2 * JPlus (-3 / 2 : ℂ)) * (y : ℂ)) (Ici (0 : ℝ)) 0 := by
      have hc : ContDiff ℝ 1 (fun y : ℝ => (2 * JPlus (-3 / 2 : ℂ)) * (y : ℂ)) :=
        contDiff_const.mul Complex.ofRealCLM.contDiff
      exact hc.contDiffAt.contDiffWithinAt
    apply hg.congr_of_eventuallyEq_of_mem hlin
    exact mem_Ici.mpr le_rfl
  · exact (nativeMuntzKernel_contDiffAt hxp).of_le (by norm_num) |>.contDiffWithinAt

theorem nativeMuntzKernel_logarithmic_identity :
    reversedLogUnitary nativeMuntzKernel = probeV := reversedLogUnitary_inverse probeV


theorem probeC_damped_integrable {z : ℂ} (hz : -1 / 2 < z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (probeC t : ℂ)) := by
  have ho := CCM.nativeRationalCausalKernel_complexDamped_integrableOn hz
  rw [← probeC_eq_nativeRationalKernel] at ho
  have hc : IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * (probeC t : ℂ))
      (Ici (0 : ℝ)) := (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr ho
  apply hc.integrable_indicator measurableSet_Ici |>.congr
  filter_upwards with t
  by_cases ht : 0 ≤ t
  · simp [indicator_of_mem (show t ∈ Ici (0 : ℝ) from ht)]
  · simp [indicator_of_notMem (show t ∉ Ici (0 : ℝ) from ht), probeC_zero_of_neg t (lt_of_not_ge ht)]

theorem probeV_damped_integrable_extended {z : ℂ} (hz : -1 / 2 < z.re) :
    Integrable (fun t : ℝ => Complex.exp (-z * (t : ℂ)) * probeV t) :=
  (OPICAFollowup.dampedConvolution_integrable_laplace
    (fun t : ℝ => (probeC t : ℂ)) (fun t : ℝ => (jPlus t : ℂ)) z
      (probeC_damped_integrable hz) (jPlusDamping_integrable z)).1

theorem probeV_laplace_extended {z : ℂ} (hz : -1 / 2 < z.re) :
    probeLaplace probeV z = CCM.nativeCompletionRationalMultiplier z * JPlus z := by
  have h := (OPICAFollowup.dampedConvolution_integrable_laplace
    (fun t : ℝ => (probeC t : ℂ)) (fun t : ℝ => (jPlus t : ℂ)) z
      (probeC_damped_integrable hz) (jPlusDamping_integrable z)).2
  change probeLaplace probeV z =
    (∫ t : ℝ, Complex.exp (-z * (t : ℂ)) * (CCM.nativeCompletionCorrection t : ℂ)) * JPlus z at h
  rw [CCM.nativeCompletionCorrection_complexLaplace hz] at h
  exact h

theorem positiveIntegral_eq_reversedLogJacobian (F : ℝ → ℂ) :
    (∫ x : ℝ in Ioi 0, F x) =
      ∫ t : ℝ, (Real.exp (-t) : ℂ) * F (Real.exp (-t)) := by
  calc
    _ = ∫ t : ℝ, Real.exp t • F (Real.exp t) :=
      (OPICAFollowup.integral_exp_smul_comp F).symm
    _ = ∫ t : ℝ, Real.exp (-t) • F (Real.exp (-t)) :=
      (integral_neg_eq_self (fun t : ℝ => Real.exp t • F (Real.exp t)) volume).symm
    _ = _ := rfl

theorem positiveIntegrable_iff_reversedLogJacobian (F : ℝ → ℂ) :
    IntegrableOn F (Ioi 0) ↔
      Integrable (fun t : ℝ => (Real.exp (-t) : ℂ) * F (Real.exp (-t))) := by
  rw [← OPICAFollowup.integrable_exp_smul_comp_iff]
  constructor
  · intro h
    simpa only [Complex.real_smul] using! h.comp_neg
  · intro h
    simpa only [Complex.real_smul, neg_neg] using! h.comp_neg

def nativeMuntzMellin (s : ℂ) : ℂ :=
  ∫ x : ℝ in Ioi 0, Complex.exp ((s - 1) * (Real.log x : ℂ)) * nativeMuntzKernel x

theorem nativeMuntzMellin_jacobian (s : ℂ) (t : ℝ) :
    (Real.exp (-t) : ℂ) * (Complex.exp ((s - 1) * (Real.log (Real.exp (-t)) : ℂ)) *
      nativeMuntzKernel (Real.exp (-t))) =
        Complex.exp (-(s - 1 / 2) * (t : ℂ)) * probeV t := by
  simp only [nativeMuntzKernel, reversedLogInverse, Real.exp_pos, if_pos, Real.log_exp,
    neg_neg]
  simp_rw [Complex.ofReal_exp]
  calc
    _ = (Complex.exp (-t : ℝ) * Complex.exp ((s - 1) * ((-t : ℝ) : ℂ)) *
      Complex.exp ((t / 2 : ℝ) : ℂ)) * probeV t := by ring
    _ = _ := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 2
      push_cast
      ring

theorem nativeMuntzMellin_eq_laplace (s : ℂ) :
    nativeMuntzMellin s = probeLaplace probeV (s - 1 / 2) := by
  rw [nativeMuntzMellin, positiveIntegral_eq_reversedLogJacobian]
  exact integral_congr_ae (Filter.Eventually.of_forall (nativeMuntzMellin_jacobian s))

theorem nativeMuntzMellin_integrable {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => Complex.exp ((s - 1) * (Real.log x : ℂ)) * nativeMuntzKernel x)
      (Ioi 0) := by
  apply (positiveIntegrable_iff_reversedLogJacobian _).mpr
  have hz : -1 / 2 < (s - 1 / 2).re := by simp only [Complex.sub_re]; norm_num; linarith
  exact (probeV_damped_integrable_extended hz).congr
    (Filter.Eventually.of_forall fun t => (nativeMuntzMellin_jacobian s t).symm)

theorem nativeMuntzMellin_formula {s : ℂ} (hs : 0 < s.re) :
    nativeMuntzMellin s = ((s - 1) / (s * (s + 1))) * JPlus (s - 1 / 2) := by
  rw [nativeMuntzMellin_eq_laplace, probeV_laplace_extended]
  · unfold CCM.nativeCompletionRationalMultiplier
    rw [show (s - 1 / 2) - 1 / 2 = s - 1 by ring,
      show (s - 1 / 2) + 1 / 2 = s by ring,
      show (s - 1 / 2) + 3 / 2 = s + 1 by ring]
  · simp only [Complex.sub_re]
    norm_num
    linarith

theorem nativeMuntzKernel_integrableOn : IntegrableOn nativeMuntzKernel (Ioi (0 : ℝ)) := by
  have h := nativeMuntzMellin_integrable (s := 1) (by norm_num)
  simpa using h

theorem nativeMuntzKernel_integrable : Integrable nativeMuntzKernel := by
  apply nativeMuntzKernel_integrableOn.integrable_indicator measurableSet_Ioi |>.congr
  filter_upwards with x
  by_cases hx : 0 < x
  · exact indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx) nativeMuntzKernel
  · simp [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx),
      nativeMuntzKernel, reversedLogInverse, hx]

theorem nativeMuntzKernel_integralOn_zero : (∫ x : ℝ in Ioi 0, nativeMuntzKernel x) = 0 := by
  have h := nativeMuntzMellin_formula (s := 1) (by norm_num)
  simpa [nativeMuntzMellin] using h

theorem nativeMuntzKernel_integral_zero : (∫ x : ℝ, nativeMuntzKernel x) = 0 := by
  have he : (∫ x : ℝ in Ioi 0, nativeMuntzKernel x) = ∫ x : ℝ, nativeMuntzKernel x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hn : ¬0 < x := hx
    simp [nativeMuntzKernel, reversedLogInverse, hn]
  rw [← he]
  exact nativeMuntzKernel_integralOn_zero


/-- The full mean subtraction is retained in the defining expression. -/
def nativeMuntzPf (x : ℝ) : ℂ := if 0 < x then
    (∑ n ∈ Finset.range (⌊x⁻¹⌋₊ + 1), nativeMuntzKernel ((n : ℝ) * x)) -
      (x : ℂ)⁻¹ * (∫ y : ℝ, nativeMuntzKernel y)
  else 0

theorem reversedLogUnitary_natural_dilation (f : ℝ → ℂ) {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    reversedLogUnitary (fun x : ℝ => f ((n : ℝ) * x)) t =
      (CCM.nativeIntegerCoefficient n : ℂ) * reversedLogUnitary f (t - Real.log n) := by
  have hnreal : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hroot : Real.sqrt (n : ℝ) = Real.exp (Real.log n / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hnreal]
    congr 1
    ring
  have harg : (n : ℝ) * Real.exp (-t) = Real.exp (-(t - Real.log n)) := by
    rw [show -(t - Real.log n) = Real.log n - t by ring,
      Real.exp_sub, Real.exp_log hnreal, Real.exp_neg]
    rfl
  have he : CCM.nativeIntegerCoefficient n * Real.exp (-(t - Real.log n) / 2) =
      Real.exp (-t / 2) := by
    unfold CCM.nativeIntegerCoefficient
    rw [hroot, one_div, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  unfold reversedLogUnitary
  dsimp only
  have hce : (CCM.nativeIntegerCoefficient n : ℂ) *
      (Real.exp (-(t - Real.log n) / 2) : ℂ) = (Real.exp (-t / 2) : ℂ) := by exact_mod_cast he
  rw [harg, ← mul_assoc, hce]

theorem nativeMuntzPf_logarithmic_identity (t : ℝ) :
    reversedLogUnitary nativeMuntzPf t = probeW t := by
  have hfloor : ⌊(Real.exp (-t))⁻¹⌋₊ = ⌊Real.exp t⌋₊ := by
    rw [← Real.exp_neg, neg_neg]
  unfold reversedLogUnitary nativeMuntzPf
  rw [if_pos (Real.exp_pos _), nativeMuntzKernel_integral_zero, mul_zero, sub_zero,
    hfloor, Finset.mul_sum]
  rw [native_probe_integer_action]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hn0 : n = 0
  · subst n
    simp [nativeMuntzKernel_zero, CCM.nativeIntegerCoefficient]
  · have h := reversedLogUnitary_natural_dilation nativeMuntzKernel hn0 t
    rw [nativeMuntzKernel_logarithmic_identity] at h
    exact h

theorem nativeMuntzPf_eq_inverse : nativeMuntzPf = reversedLogInverse probeW := by
  ext x
  by_cases hx : 0 < x
  · have h := reversedLogInverse_unitary nativeMuntzPf hx
    rw [show reversedLogUnitary nativeMuntzPf = probeW from funext nativeMuntzPf_logarithmic_identity] at h
    exact h.symm
  · simp [nativeMuntzPf, reversedLogInverse, hx]

theorem probeW_contDiff : ContDiff ℝ (⊤ : ℕ∞) probeW := by
  have hj : HasCompactSupport (fun t : ℝ => (jPlus t : ℂ)) :=
    jPlus_hasCompactSupport.comp_left (g := Complex.ofReal) Complex.ofReal_zero
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (jPlus t : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp jPlus_contDiff
  exact hj.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℂ)
    CCM.nativePositiveCompletion_integrable.ofReal.locallyIntegrable hc

theorem reversedLogInverse_measurable {f : ℝ → ℂ} (hf : Measurable f) :
    Measurable (reversedLogInverse f) := by
  unfold reversedLogInverse
  apply Measurable.ite measurableSet_Ioi
  · exact (by fun_prop : Measurable (fun x : ℝ => (Real.exp (-Real.log x / 2) : ℂ))).mul
      (hf.comp (by fun_prop))
  · exact measurable_const

theorem nativeMuntzKernel_memLp : MemLp nativeMuntzKernel 2 (volume.restrict (Ioi (0 : ℝ))) := by
  apply (memLp_two_iff_integrable_sq_norm
    (reversedLogInverse_measurable probeV_contDiff.continuous.measurable).aestronglyMeasurable).mpr
  exact (reversedLogInverse_integrable_norm_sq_iff probeV).mpr
    ((memLp_two_iff_integrable_sq_norm probeV_memLp.1).mp probeV_memLp)

theorem nativeMuntzPf_memLp : MemLp nativeMuntzPf 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [nativeMuntzPf_eq_inverse]
  apply (memLp_two_iff_integrable_sq_norm
    (reversedLogInverse_measurable probeW_contDiff.continuous.measurable).aestronglyMeasurable).mpr
  exact (reversedLogInverse_integrable_norm_sq_iff probeW).mpr
    ((memLp_two_iff_integrable_sq_norm probeW_memLp.1).mp probeW_memLp)

def nativeMuntzKernelL2 : PositiveProbeL2 := nativeMuntzKernel_memLp.toLp nativeMuntzKernel

def nativeMuntzPfL2 : PositiveProbeL2 := nativeMuntzPf_memLp.toLp nativeMuntzPf

theorem nativeMuntzKernel_L2_logarithmic_identity :
    reversedLogL2 nativeMuntzKernelL2 = (probeTarget : ProbeL2) := by
  apply Lp.ext
  exact (reversedLogL2Value_coeFn nativeMuntzKernelL2).trans
    ((reversedLogUnitary_congr_ae nativeMuntzKernel_memLp.coeFn_toLp).trans
      ((show reversedLogUnitary nativeMuntzKernel =ᵐ[volume] probeV from
        Filter.Eventually.of_forall fun t => congrFun nativeMuntzKernel_logarithmic_identity t).trans
        probeTarget_coeFn.symm))

theorem nativeMuntzPf_L2_logarithmic_identity :
    reversedLogL2 nativeMuntzPfL2 = (probeCompletedSource : ProbeL2) := by
  apply Lp.ext
  exact (reversedLogL2Value_coeFn nativeMuntzPfL2).trans
    ((reversedLogUnitary_congr_ae nativeMuntzPf_memLp.coeFn_toLp).trans
      ((show reversedLogUnitary nativeMuntzPf =ᵐ[volume] probeW from
        Filter.Eventually.of_forall nativeMuntzPf_logarithmic_identity).trans
        probeCompletedSource_coeFn.symm))

theorem nativeMuntzPf_dilation_logarithmic_identity {n : ℕ} (hn : n ≠ 0) (t : ℝ) :
    reversedLogUnitary (fun x : ℝ => nativeMuntzPf ((n : ℝ) * x)) t =
      (CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n) := by
  rw [reversedLogUnitary_natural_dilation nativeMuntzPf hn t,
    nativeMuntzPf_logarithmic_identity]

theorem nativeMuntzPf_dilation_memLp {n : ℕ} (hn : n ≠ 0) :
    MemLp (fun x : ℝ => nativeMuntzPf ((n : ℝ) * x)) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  have hm : Measurable (fun x : ℝ => nativeMuntzPf ((n : ℝ) * x)) := by
    rw [nativeMuntzPf_eq_inverse]
    exact (reversedLogInverse_measurable probeW_contDiff.continuous.measurable).comp
      (measurable_const.mul measurable_id)
  apply (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mpr
  apply (reversedLogUnitary_integrable_norm_sq_iff _).mp
  have hd := probeW_memLp.comp_measurePreserving (measurePreserving_sub_right volume (Real.log n))
  have hr : MemLp (fun t : ℝ => (CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n))
      2 volume := by
    simpa only [Function.comp_def, Pi.smul_apply, smul_eq_mul] using!
      hd.const_smul (CCM.nativeIntegerCoefficient n : ℂ)
  have hM : MemLp (reversedLogUnitary (fun x : ℝ => nativeMuntzPf ((n : ℝ) * x))) 2 volume :=
    hr.ae_eq (Filter.Eventually.of_forall fun t => (nativeMuntzPf_dilation_logarithmic_identity hn t).symm)
  exact (memLp_two_iff_integrable_sq_norm hM.1).mp hM

def nativeMuntzPfDilationL2 (n : ℕ) (hn : n ≠ 0) : PositiveProbeL2 :=
  (nativeMuntzPf_dilation_memLp hn).toLp (fun x : ℝ => nativeMuntzPf ((n : ℝ) * x))

theorem nativeMuntzPf_dilation_L2_identity {n : ℕ} (hn : n ≠ 0) :
    reversedLogL2 (nativeMuntzPfDilationL2 n hn) = (probeColumn n : ProbeL2) := by
  apply Lp.ext
  exact (reversedLogL2Value_coeFn (nativeMuntzPfDilationL2 n hn)).trans
    ((reversedLogUnitary_congr_ae (nativeMuntzPf_dilation_memLp hn).coeFn_toLp).trans
      ((show reversedLogUnitary (fun x : ℝ => nativeMuntzPf ((n : ℝ) * x)) =ᵐ[volume]
        (fun t : ℝ => (CCM.nativeIntegerCoefficient n : ℂ) * probeW (t - Real.log n)) from
        Filter.Eventually.of_forall (nativeMuntzPf_dilation_logarithmic_identity hn)).trans
        (probeColumn_coeFn hn).symm))


theorem nativeMuntzKernel_right_derivative :
    HasDerivWithinAt nativeMuntzKernel (2 * JPlus (-3 / 2 : ℂ)) (Ici (0 : ℝ)) 0 := by
  have hg : HasDerivAt (fun y : ℝ => (2 * JPlus (-3 / 2 : ℂ)) * (y : ℂ))
      (2 * JPlus (-3 / 2 : ℂ)) 0 := by
    simpa only [Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one] using!
      (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul (2 * JPlus (-3 / 2 : ℂ))
  apply hg.hasDerivWithinAt.congr_of_eventuallyEq_of_mem
  · filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (Real.exp_pos (-2 * probeSigma)))] with y hy hs
    exact nativeMuntzKernel_linear_near_zero (show 0 ≤ y from hy)
      (show y < Real.exp (-2 * probeSigma) from hs).le
  · exact mem_Ici.mpr le_rfl

theorem nativeMuntzKernel_not_differentiable_zero :
    ¬DifferentiableAt ℝ nativeMuntzKernel 0 := by
  intro hd
  have hl : HasDerivWithinAt nativeMuntzKernel 0 (Iic (0 : ℝ)) 0 := by
    apply (hasDerivAt_const (0 : ℝ) (0 : ℂ)).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin] with y hy
      have hn : ¬0 < y := not_lt.mpr (show y ≤ 0 from hy)
      simp [nativeMuntzKernel, reversedLogInverse, hn]
    · exact mem_Iic.mpr le_rfl
  have hright := UniqueDiffWithinAt.eq_deriv (Ici (0 : ℝ)) (uniqueDiffWithinAt_Ici (0 : ℝ))
    nativeMuntzKernel_right_derivative hd.hasDerivAt.hasDerivWithinAt
  have hleft := hl.deriv_eq_zero (uniqueDiffWithinAt_Iic (0 : ℝ))
  exact nativeMuntzKernel_right_slope_ne_zero (hright.trans hleft)

theorem nativeMuntzKernel_one : nativeMuntzKernel 1 = 0 := by
  have hc := (nativeMuntzKernel_contDiffAt (x := 1) (by norm_num)).continuousAt.continuousWithinAt
    (s := Ioi (1 : ℝ))
  have hz : nativeMuntzKernel =ᶠ[𝓝[>] (1 : ℝ)] fun _ : ℝ => (0 : ℂ) := by
    filter_upwards [self_mem_nhdsWithin] with y hy
    apply nativeMuntzKernel_zero_outside
    intro h
    exact (not_lt_of_ge h.2) hy
  have ht : Filter.Tendsto nativeMuntzKernel (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ)) :=
    (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ => (0 : ℂ)) (𝓝[>] (1 : ℝ)) (𝓝 (0 : ℂ))).congr' hz.symm
  exact tendsto_nhds_unique hc ht

theorem nativeMuntzKernel_flat_at_one : HasDerivAt nativeMuntzKernel 0 1 := by
  have hd : DifferentiableAt ℝ nativeMuntzKernel 1 :=
    (nativeMuntzKernel_contDiffAt (x := 1) (by norm_num)).differentiableAt (by simp)
  have hz : HasDerivWithinAt nativeMuntzKernel 0 (Ici (1 : ℝ)) 1 := by
    apply (hasDerivAt_const (1 : ℝ) (0 : ℂ)).hasDerivWithinAt.congr_of_eventuallyEq_of_mem
    · filter_upwards [self_mem_nhdsWithin] with y hy
      by_cases he : y = 1
      · simpa only [he] using nativeMuntzKernel_one
      · apply nativeMuntzKernel_zero_outside
        intro h
        have : y = 1 := le_antisymm h.2 hy
        exact he this
    · exact mem_Ici.mpr le_rfl
  have he := hz.deriv_eq_zero (uniqueDiffWithinAt_Ici (1 : ℝ))
  simpa only [he] using hd.hasDerivAt

/-- The complete native compact good-kernel adapter. The regularity domain is
explicitly the closed positive half-line, and the original mean subtraction
and physical dictionary are retained. -/
theorem native_compact_muntz_adapter :
    nativeMuntzKernel 0 = 0 ∧
    (∀ x : ℝ, x ∉ Icc (0 : ℝ) 1 → nativeMuntzKernel x = 0) ∧
    HasCompactSupport nativeMuntzKernel ∧
    ContDiffOn ℝ 1 nativeMuntzKernel (Ici (0 : ℝ)) ∧
    nativeMuntzKernel 1 = 0 ∧ HasDerivAt nativeMuntzKernel 0 1 ∧
    HasDerivWithinAt nativeMuntzKernel (2 * JPlus (-3 / 2 : ℂ)) (Ici (0 : ℝ)) 0 ∧
    (2 * JPlus (-3 / 2 : ℂ)) ≠ 0 ∧
    Integrable nativeMuntzKernel ∧ (∫ x : ℝ, nativeMuntzKernel x) = 0 ∧
    (∀ s : ℂ, 0 < s.re →
      IntegrableOn (fun x : ℝ => Complex.exp ((s - 1) * (Real.log x : ℂ)) * nativeMuntzKernel x) (Ioi 0) ∧
      nativeMuntzMellin s = ((s - 1) / (s * (s + 1))) * JPlus (s - 1 / 2)) ∧
    reversedLogL2 nativeMuntzKernelL2 = (probeTarget : ProbeL2) ∧
    reversedLogL2 nativeMuntzPfL2 = (probeCompletedSource : ProbeL2) ∧
    (∀ n : ℕ, ∀ hn : n ≠ 0,
      reversedLogL2 (nativeMuntzPfDilationL2 n hn) = (probeColumn n : ProbeL2)) := by
  exact ⟨nativeMuntzKernel_zero, fun _ hx => nativeMuntzKernel_zero_outside hx,
    nativeMuntzKernel_hasCompactSupport, nativeMuntzKernel_contDiffOn_halfline,
    nativeMuntzKernel_one, nativeMuntzKernel_flat_at_one, nativeMuntzKernel_right_derivative,
    nativeMuntzKernel_right_slope_ne_zero, nativeMuntzKernel_integrable, nativeMuntzKernel_integral_zero,
    fun _ hs => ⟨nativeMuntzMellin_integrable hs, nativeMuntzMellin_formula hs⟩,
    nativeMuntzKernel_L2_logarithmic_identity, nativeMuntzPf_L2_logarithmic_identity,
    fun _ hn => nativeMuntzPf_dilation_L2_identity hn⟩

end Zeta23.OPICARound2
