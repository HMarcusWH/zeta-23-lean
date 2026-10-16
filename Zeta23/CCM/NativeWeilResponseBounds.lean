import Zeta23.CCM.NativeWeilResponse
import Mathlib.MeasureTheory.Function.L2Space

/-!+# Physical H1 estimates in the literal paper Fourier convention

The compact C2 class is retained.  Parseval for its first derivative is
obtained by inversion of the continuous compact autocorrelation, rather
than by assuming that the first derivative is itself C2.
-/

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Topology FourierTransform Convolution ComplexConjugate

namespace Zeta23.CCM

private theorem nativeIntegral_ofReal (f : ℝ → ℝ) :
    (∫ x : ℝ, (f x : ℂ)) = ((∫ x : ℝ, f x : ℝ) : ℂ) := integral_ofReal

private theorem integrable_fourier_of_paperFT {f : ℝ → ℂ}
    (hf : Integrable (fun ξ : ℝ => paperFT f (ξ : ℂ))) : Integrable (𝓕 f) := by
  have heq : (fun ξ : ℝ => paperFT f (ξ : ℂ)) =
      fun ξ : ℝ => (𝓕 f) ((-(1 / (2 * Real.pi))) * ξ) := by
    funext ξ
    rw [EF.paperFT_ofReal_eq_fourier]
    congr 1
    ring
  rw [heq] at hf
  exact (integrable_comp_mul_left_iff (𝓕 f) (neg_ne_zero.mpr (by positivity))).mp hf

/-- Compact autocorrelation gives Parseval with the exact `+i` and `2π`
normalization.  The Fourier-square integrability is an internal analytic
condition discharged below for the source and its first derivative. -/
theorem nativePaperFT_parseval_of_integrable_sq {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hF : Integrable (fun ξ : ℝ => ‖paperFT f (ξ : ℂ)‖ ^ 2)) :
    (∫ ξ : ℝ, ‖paperFT f (ξ : ℂ)‖ ^ 2) =
      2 * Real.pi * ∫ x : ℝ, ‖f x‖ ^ 2 := by
  let k : ℝ → ℂ := EF.weilTest f f
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  have hk : Continuous k := by
    exact (EF.hasCompactSupport_tilde hfc).continuous_convolution_right
      (ContinuousLinearMap.mul ℝ ℂ) hf.locallyIntegrable (EF.continuous_tilde hf)
  have hFk (ξ : ℝ) : paperFT k (ξ : ℂ) = (‖paperFT f (ξ : ℂ)‖ ^ 2 : ℝ) := by
    dsimp [k]
    rw [EF.paperFT_weilTest hf hf hfc hfc, Complex.conj_ofReal,
      Complex.mul_conj', Complex.ofReal_pow]
  have hFki : Integrable (fun ξ : ℝ => paperFT k (ξ : ℂ)) := by
    exact (hF.ofReal).congr (Eventually.of_forall fun ξ => (hFk ξ).symm)
  have hi := EF.paper_inversion hk (hk.integrable_of_hasCompactSupport hkc)
    (integrable_fourier_of_paperFT hFki) 0
  have hk0 : k 0 = ((∫ x : ℝ, ‖f x‖ ^ 2 : ℝ) : ℂ) := by
    dsimp [k, EF.weilTest, EF.tilde]
    simp only [convolution_def, ContinuousLinearMap.mul_apply', zero_sub, EF.tilde, neg_neg]
    change (∫ x : ℝ, f x * conj (f x)) = _
    simp_rw [Complex.mul_conj', ← Complex.ofReal_pow]
    exact nativeIntegral_ofReal _
  rw [hk0] at hi
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at hi
  simp_rw [hFk] at hi
  rw [nativeIntegral_ofReal] at hi
  have hp : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  rw [one_div_mul_eq_div] at hi
  have hic := (eq_div_iff hp).mp hi
  have hre := congrArg Complex.re hic
  norm_num [Complex.mul_re, Complex.mul_im] at hre
  linarith only [hre]

/-- The exact C2 decay estimate implies the weighted Fourier-square is
integrable; no regularity above C2 is used. -/
theorem nativePaperFT_weighted_sq_integrable {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun ξ : ℝ => (1 + ξ ^ 2) * ‖paperFT f (ξ : ℂ)‖ ^ 2) := by
  obtain ⟨Λ, hΛ⟩ := EF.exists_abs_le_of_hasCompactSupport hfc
  let B : ℝ := (∫ x : ℝ, ‖f x‖) + ∫ x : ℝ, ‖deriv (deriv f) x‖
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hFi : Integrable (fun ξ : ℝ => paperFT f (ξ : ℂ)) :=
    EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hf hfc)
  have hm : AEStronglyMeasurable
      (fun ξ : ℝ => (1 + ξ ^ 2) * ‖paperFT f (ξ : ℂ)‖ ^ 2) :=
    (by fun_prop : Continuous (fun ξ : ℝ => 1 + ξ ^ 2)).aestronglyMeasurable.mul
      (hFi.aestronglyMeasurable.norm.pow 2)
  refine (integrable_inv_one_add_sq.const_mul (B ^ 2)).mono' hm
    (Eventually.of_forall fun ξ => ?_)
  have hb := EF.norm_paperFT_mul_one_add_sq_le hf hΛ ξ
  change ‖paperFT f (ξ : ℂ)‖ * (1 + ξ ^ 2) ≤ B at hb
  rw [Real.norm_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _)),
    ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hs := pow_le_pow_left₀
    (mul_nonneg (norm_nonneg (paperFT f (ξ : ℂ))) (by positivity : 0 ≤ 1 + ξ ^ 2)) hb 2
  nlinarith only [hs]

theorem nativePaperFT_sq_integrable {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun ξ : ℝ => ‖paperFT f (ξ : ℂ)‖ ^ 2) := by
  have hFi := EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hf hfc)
  refine (nativePaperFT_weighted_sq_integrable hf hfc).mono'
    (hFi.aestronglyMeasurable.norm.pow 2) (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [mul_nonneg (sq_nonneg ξ) (sq_nonneg ‖paperFT f (ξ : ℂ)‖)]

theorem nativePaperFT_deriv_sq_integrable {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun ξ : ℝ => ‖paperFT (deriv f) (ξ : ℂ)‖ ^ 2) := by
  have hd (ξ : ℝ) : ‖paperFT (deriv f) (ξ : ℂ)‖ ^ 2 =
      ξ ^ 2 * ‖paperFT f (ξ : ℂ)‖ ^ 2 := by
    rw [Zeta23.paperFT_deriv (hf.of_le (by norm_num)) hfc, norm_mul, norm_neg,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs]
  have hmeas : AEStronglyMeasurable
      (fun ξ : ℝ => ‖paperFT (deriv f) (ξ : ℂ)‖ ^ 2) := by
    have hdint : Integrable (deriv f) :=
      (hf.continuous_deriv (by norm_num)).integrable_of_hasCompactSupport hfc.deriv
    have hc := EF.continuous_fourier_of_integrable hdint
    have heq : (fun ξ : ℝ => paperFT (deriv f) (ξ : ℂ)) =
        fun ξ : ℝ => (𝓕 (deriv f)) (-ξ / (2 * Real.pi)) :=
      funext (EF.paperFT_ofReal_eq_fourier (deriv f))
    change AEStronglyMeasurable
      (fun ξ : ℝ => ‖(fun ξ : ℝ => paperFT (deriv f) (ξ : ℂ)) ξ‖ ^ 2)
    rw [heq]
    exact (hc.comp (by fun_prop)).aestronglyMeasurable.norm.pow 2
  refine (nativePaperFT_weighted_sq_integrable hf hfc).mono' hmeas
    (Eventually.of_forall fun ξ => ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), hd]
  nlinarith [sq_nonneg ‖paperFT f (ξ : ℂ)‖]

/-- Exact physical H1 Parseval, with the same norm used by finite-image
approximation and with only the actual compact C2 assumptions. -/
theorem nativePaperFT_H1_energy {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ ξ : ℝ, (1 + ξ ^ 2) * ‖paperFT f (ξ : ℂ)‖ ^ 2) =
      2 * Real.pi * nativePhysicalH1Norm f ^ 2 := by
  have h0 := nativePaperFT_parseval_of_integrable_sq hf.continuous hfc
    (nativePaperFT_sq_integrable hf hfc)
  have h1 := nativePaperFT_parseval_of_integrable_sq
    (hf.continuous_deriv (by norm_num)) hfc.deriv
    (nativePaperFT_deriv_sq_integrable hf hfc)
  have hd (ξ : ℝ) : ‖paperFT (deriv f) (ξ : ℂ)‖ ^ 2 =
      ξ ^ 2 * ‖paperFT f (ξ : ℂ)‖ ^ 2 := by
    rw [Zeta23.paperFT_deriv (hf.of_le (by norm_num)) hfc, norm_mul, norm_neg,
      norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      mul_pow, sq_abs]
  have hdi : Integrable (fun ξ : ℝ => ξ ^ 2 * ‖paperFT f (ξ : ℂ)‖ ^ 2) := by
    simpa only [hd] using nativePaperFT_deriv_sq_integrable hf hfc
  have hsum : (∫ ξ : ℝ, (1 + ξ ^ 2) * ‖paperFT f (ξ : ℂ)‖ ^ 2) =
      (∫ ξ : ℝ, ‖paperFT f (ξ : ℂ)‖ ^ 2) +
      ∫ ξ : ℝ, ‖paperFT (deriv f) (ξ : ℂ)‖ ^ 2 := by
    rw [← integral_add (nativePaperFT_sq_integrable hf hfc)
      (nativePaperFT_deriv_sq_integrable hf hfc)]
    apply integral_congr_ae
    filter_upwards with ξ
    rw [hd]
    ring
  rw [hsum, h0, h1]
  unfold nativePhysicalH1Norm originalDetectorPhysicalH1Error
  simp only [Pi.zero_apply, sub_zero]
  rw [Real.sq_sqrt (by positivity)]
  ring

theorem nativePhysicalH1Norm_nonneg (f : ℝ → ℂ) :
    0 ≤ nativePhysicalH1Norm f := Real.sqrt_nonneg _

private theorem integral_mul_le_sqrt_sq {g h : ℝ → ℝ}
    (hg : AEStronglyMeasurable g) (hh : AEStronglyMeasurable h)
    (hg0 : ∀ x, 0 ≤ g x) (hh0 : ∀ x, 0 ≤ h x)
    (hg2 : Integrable (fun x => g x ^ 2)) (hh2 : Integrable (fun x => h x ^ 2)) :
    (∫ x, g x * h x) ≤ Real.sqrt (∫ x, g x ^ 2) * Real.sqrt (∫ x, h x ^ 2) := by
  have hglp : MemLp g 2 := (memLp_two_iff_integrable_sq hg).mpr hg2
  have hhlp : MemLp h 2 := (memLp_two_iff_integrable_sq hh).mpr hh2
  have hi := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Eventually.of_forall hg0) (Eventually.of_forall hh0)
    (by simpa using hglp) (by simpa using hhlp)
  simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hi

theorem nativePaperFT_H1_mixed_bound {f v : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hv : ContDiff ℝ 2 v)
    (hfc : HasCompactSupport f) (hvc : HasCompactSupport v) :
    Integrable (fun ξ : ℝ => (1 + ξ ^ 2) * ‖paperFT f (ξ : ℂ)‖ *
      ‖paperFT v (ξ : ℂ)‖) ∧
    (∫ ξ : ℝ, (1 + ξ ^ 2) * ‖paperFT f (ξ : ℂ)‖ * ‖paperFT v (ξ : ℂ)‖) ≤
      2 * Real.pi * nativePhysicalH1Norm f * nativePhysicalH1Norm v := by
  let g : ℝ → ℝ := fun ξ => Real.sqrt (1 + ξ ^ 2) * ‖paperFT f (ξ : ℂ)‖
  let h : ℝ → ℝ := fun ξ => Real.sqrt (1 + ξ ^ 2) * ‖paperFT v (ξ : ℂ)‖
  have hff : AEStronglyMeasurable (fun ξ : ℝ => paperFT f (ξ : ℂ)) :=
    (EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hf hfc)).aestronglyMeasurable
  have hvf : AEStronglyMeasurable (fun ξ : ℝ => paperFT v (ξ : ℂ)) :=
    (EF.integrable_paperFT_ofReal (EF.integrable_fourier_of_contDiff_two hv hvc)).aestronglyMeasurable
  have hroot : Continuous (fun ξ : ℝ => Real.sqrt (1 + ξ ^ 2)) := by fun_prop
  have hg : AEStronglyMeasurable g := hroot.aestronglyMeasurable.mul hff.norm
  have hh : AEStronglyMeasurable h := hroot.aestronglyMeasurable.mul hvf.norm
  have hgs (ξ : ℝ) : g ξ ^ 2 = (1 + ξ ^ 2) * ‖paperFT f (ξ : ℂ)‖ ^ 2 := by
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hhs (ξ : ℝ) : h ξ ^ 2 = (1 + ξ ^ 2) * ‖paperFT v (ξ : ℂ)‖ ^ 2 := by
    dsimp [h]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hg2 : Integrable (fun ξ => g ξ ^ 2) := by
    simpa only [hgs] using nativePaperFT_weighted_sq_integrable hf hfc
  have hh2 : Integrable (fun ξ => h ξ ^ 2) := by
    simpa only [hhs] using nativePaperFT_weighted_sq_integrable hv hvc
  have heq (ξ : ℝ) : g ξ * h ξ =
      (1 + ξ ^ 2) * ‖paperFT f (ξ : ℂ)‖ * ‖paperFT v (ξ : ℂ)‖ := by
    dsimp [g, h]
    calc
      _ = Real.sqrt (1 + ξ ^ 2) ^ 2 * ‖paperFT f (ξ : ℂ)‖ *
          ‖paperFT v (ξ : ℂ)‖ := by ring
      _ = _ := by rw [Real.sq_sqrt (by positivity)]
  have hmul : Integrable (fun ξ => g ξ * h ξ) := by
    have hm : MemLp (fun ξ => g ξ * h ξ) 1 :=
      ((memLp_two_iff_integrable_sq hh).mpr hh2).mul'
        ((memLp_two_iff_integrable_sq hg).mpr hg2)
    exact memLp_one_iff_integrable.mp hm
  refine ⟨by simpa only [heq] using hmul, ?_⟩
  have hc := integral_mul_le_sqrt_sq hg hh
    (fun ξ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))
    (fun ξ => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) hg2 hh2
  simp only [heq, hgs, hhs, nativePaperFT_H1_energy hf hfc,
    nativePaperFT_H1_energy hv hvc] at hc
  have hsf : Real.sqrt (2 * Real.pi * nativePhysicalH1Norm f ^ 2) =
      Real.sqrt (2 * Real.pi) * nativePhysicalH1Norm f := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (nativePhysicalH1Norm_nonneg f)]
  have hsv : Real.sqrt (2 * Real.pi * nativePhysicalH1Norm v ^ 2) =
      Real.sqrt (2 * Real.pi) * nativePhysicalH1Norm v := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (nativePhysicalH1Norm_nonneg v)]
  rw [hsf, hsv] at hc
  calc
    _ ≤ (Real.sqrt (2 * Real.pi) * nativePhysicalH1Norm f) *
        (Real.sqrt (2 * Real.pi) * nativePhysicalH1Norm v) := hc
    _ = _ := by
      calc
        _ = Real.sqrt (2 * Real.pi) ^ 2 * nativePhysicalH1Norm f *
            nativePhysicalH1Norm v := by ring
        _ = _ := by rw [Real.sq_sqrt (by positivity)]

/-- The exact native arithmetic mass has a source-independent explicit
majorant.  This finite estimate makes no subexponential claim. -/
theorem native_sum_inv_sqrt_succ_le (N : ℕ) :
    (∑ n ∈ Finset.range N, 1 / Real.sqrt (n + 1 : ℝ)) ≤ 2 * Real.sqrt N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hn : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    have hs : 0 < Real.sqrt (N + 1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
    have hn2 := Real.sq_sqrt hn
    have hs2 := Real.sq_sqrt (by positivity : 0 ≤ (N + 1 : ℝ))
    have hstep : 1 / Real.sqrt (N + 1 : ℝ) ≤
        2 * (Real.sqrt (N + 1 : ℝ) - Real.sqrt N) := by
      rw [div_le_iff₀ hs]
      nlinarith [sq_nonneg (Real.sqrt (N + 1 : ℝ) - Real.sqrt N)]
    push_cast
    linarith

theorem nativePrimeMass_finite_bound {L : ℝ} (hL : 0 ≤ L) :
    (∑ n ∈ Finset.range ⌊Real.exp L⌋₊, nativePrimeCoefficient (n + 1)) ≤
      2 * (1 + L) * Real.exp (L / 2) := by
  let N : ℕ := ⌊Real.exp L⌋₊
  have hterm (n : ℕ) (hn : n ∈ Finset.range N) :
      nativePrimeCoefficient (n + 1) ≤ L * (1 / Real.sqrt (n + 1 : ℝ)) := by
    have hnN : n + 1 ≤ N := Nat.succ_le_iff.mpr (Finset.mem_range.mp hn)
    have hnNreal : (n + 1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hnN
    have hnE : (n + 1 : ℝ) ≤ Real.exp L :=
      hnNreal.trans (Nat.floor_le (Real.exp_pos L).le)
    have hlog : Real.log (n + 1 : ℝ) ≤ L :=
      (Real.log_le_iff_le_exp (by positivity)).mpr hnE
    dsimp [nativePrimeCoefficient]
    push_cast
    calc
      ArithmeticFunction.vonMangoldt (n + 1) / Real.sqrt (n + 1 : ℝ) ≤
          Real.log (n + 1 : ℝ) / Real.sqrt (n + 1 : ℝ) := by
        gcongr
        exact_mod_cast ArithmeticFunction.vonMangoldt_le_log (n := n + 1)
      _ ≤ L / Real.sqrt (n + 1 : ℝ) := by gcongr
      _ = _ := by ring
  have hN : Real.sqrt N ≤ Real.exp (L / 2) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨(Real.exp_pos _).le, ?_⟩
    have he : Real.exp (L / 2) ^ 2 = Real.exp L := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    rw [he]
    exact Nat.floor_le (Real.exp_pos L).le
  calc
    _ ≤ ∑ n ∈ Finset.range N, L * (1 / Real.sqrt (n + 1 : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = L * ∑ n ∈ Finset.range N, 1 / Real.sqrt (n + 1 : ℝ) := by
      rw [Finset.mul_sum]
    _ ≤ L * (2 * Real.sqrt N) := mul_le_mul_of_nonneg_left
      (native_sum_inv_sqrt_succ_le N) hL
    _ ≤ L * (2 * Real.exp (L / 2)) := by gcongr
    _ ≤ _ := by nlinarith [Real.exp_pos (L / 2)]

/-- A single constant, constructed from the proved native gamma growth,
bounds the actual mixed Archimedean response by the physical H1 norms. -/
theorem nativeWeilArchResponse_bilinear_bound :
    ∃ C_A : ℝ, 0 < C_A ∧ ∀ (f v : ℝ → ℂ),
      ContDiff ℝ 2 f → ContDiff ℝ 2 v → HasCompactSupport f → HasCompactSupport v →
      ‖∫ x : ℝ, nativeWeilArchResponse f x * conj (v x)‖ ≤
        C_A * nativePhysicalH1Norm f * nativePhysicalH1Norm v := by
  obtain ⟨C_A, hCA, hgamma⟩ := nativeGammaBracket_quadratic_bound
  refine ⟨C_A, hCA, ?_⟩
  intro f v hf hv hfc hvc
  obtain ⟨hcrossi, hcross⟩ := nativePaperFT_H1_mixed_bound hf hv hfc hvc
  let cross : ℝ → ℝ := fun ξ =>
    (1 + ξ ^ 2) * ‖paperFT f (ξ : ℂ)‖ * ‖paperFT v (ξ : ℂ)‖
  let F : ℝ → ℂ := fun ξ =>
    paperFT f (ξ : ℂ) * conj (paperFT v (ξ : ℂ)) * (EF.gammaBracket ξ : ℂ)
  have hμ : Continuous (fun ξ : ℝ => (Zeta23.mu ξ : ℂ)) :=
    Complex.continuous_ofReal.comp Zeta23.gammaFacts.smooth.continuous
  have hgam (ξ : ℝ) : (EF.gammaBracket ξ : ℂ) =
      ((2 * Real.pi : ℝ) : ℂ) * (Zeta23.mu ξ : ℂ) := by
    unfold EF.gammaBracket Zeta23.mu
    push_cast
    field_simp <;> ring
  have hgammaMeas : AEStronglyMeasurable (fun ξ : ℝ => (EF.gammaBracket ξ : ℂ)) := by
    have heq : (fun ξ : ℝ => (EF.gammaBracket ξ : ℂ)) =
        fun ξ => ((2 * Real.pi : ℝ) : ℂ) * (Zeta23.mu ξ : ℂ) := funext hgam
    rw [heq]
    exact (continuous_const.mul hμ).aestronglyMeasurable
  have hff := (EF.integrable_paperFT_ofReal
    (EF.integrable_fourier_of_contDiff_two hf hfc)).aestronglyMeasurable
  have hvf := (EF.integrable_paperFT_ofReal
    (EF.integrable_fourier_of_contDiff_two hv hvc)).aestronglyMeasurable
  have hFm : AEStronglyMeasurable F :=
    (hff.mul (Complex.continuous_conj.comp_aestronglyMeasurable hvf)).mul hgammaMeas
  have hpoint (ξ : ℝ) : ‖F ξ‖ ≤ C_A * cross ξ := by
    dsimp [F, cross]
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ ‖paperFT f (ξ : ℂ)‖ * ‖paperFT v (ξ : ℂ)‖ * (C_A * (1 + ξ ^ 2)) := by
        gcongr
        exact hgamma ξ
      _ = _ := by ring
  have hFi : Integrable F := (hcrossi.const_mul C_A).mono' hFm
    (Eventually.of_forall hpoint)
  have hint : ‖∫ ξ : ℝ, F ξ‖ ≤ C_A *
      (2 * Real.pi * nativePhysicalH1Norm f * nativePhysicalH1Norm v) := by
    calc
      _ ≤ ∫ ξ : ℝ, ‖F ξ‖ := norm_integral_le_integral_norm F
      _ ≤ ∫ ξ : ℝ, C_A * cross ξ :=
        integral_mono_ae hFi.norm (hcrossi.const_mul C_A) (Eventually.of_forall hpoint)
      _ = C_A * ∫ ξ : ℝ, cross ξ := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hcross hCA.le
  rw [nativeWeilArchResponse_pairing hf hfc hv.continuous hvc, norm_mul]
  change ‖(1 / (2 * Real.pi) : ℂ)‖ * ‖∫ ξ : ℝ, F ξ‖ ≤ _
  have hc : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, norm_mul]
    norm_num [Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hc]
  calc
    _ ≤ (1 / (2 * Real.pi)) *
        (C_A * (2 * Real.pi * nativePhysicalH1Norm f * nativePhysicalH1Norm v)) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = _ := by field_simp <;> ring

def nativePhysicalL2Norm (f : ℝ → ℂ) : ℝ := Real.sqrt (∫ x : ℝ, ‖f x‖ ^ 2)

theorem nativePhysicalL2Norm_nonneg (f : ℝ → ℂ) :
    0 ≤ nativePhysicalL2Norm f := Real.sqrt_nonneg _

theorem nativePhysicalL2Norm_le_H1 (f : ℝ → ℂ) :
    nativePhysicalL2Norm f ≤ nativePhysicalH1Norm f := by
  unfold nativePhysicalL2Norm nativePhysicalH1Norm originalDetectorPhysicalH1Error
  simp only [Pi.zero_apply, sub_zero]
  exact Real.sqrt_le_sqrt (le_add_of_nonneg_right (integral_nonneg fun _ => sq_nonneg _))

private theorem physical_sq_integrable {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Integrable (fun x : ℝ => ‖f x‖ ^ 2) := by
  have hmem : MemLp f 2 := hf.memLp_of_hasCompactSupport hfc
  exact (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hmem

theorem nativePhysicalL1_le_sqrt_length_L2 {f : ℝ → ℂ} {L : ℝ}
    (hL : 0 ≤ L) (hf : Continuous f) (hfs : tsupport f ⊆ Icc (0 : ℝ) L) :
    (∫ x : ℝ, ‖f x‖) ≤ Real.sqrt L * nativePhysicalL2Norm f := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  let h : ℝ → ℝ := (Icc (0 : ℝ) L).indicator (fun _ => 1)
  have hm : AEStronglyMeasurable h := aestronglyMeasurable_const.indicator measurableSet_Icc
  have hh0 (x : ℝ) : 0 ≤ h x := by
    by_cases hx : x ∈ Icc (0 : ℝ) L <;> simp [h, hx]
  have hhs (x : ℝ) : h x ^ 2 = h x := by
    by_cases hx : x ∈ Icc (0 : ℝ) L <;> simp [h, hx]
  have hhi : Integrable h := (integrableOn_const (C := (1 : ℝ))
    (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hh2 : Integrable (fun x => h x ^ 2) := by simpa only [hhs] using hhi
  have hmass : (∫ x : ℝ, h x ^ 2) = L := by
    simp only [hhs]
    change (∫ x : ℝ, (Icc (0 : ℝ) L).indicator (fun _ : ℝ => (1 : ℝ)) x) = L
    calc
      _ = volume.real (Icc (0 : ℝ) L) * (1 : ℝ) := by
        simpa only [smul_eq_mul] using integral_indicator_const (1 : ℝ) measurableSet_Icc
      _ = L := by rw [Real.volume_real_Icc_of_le hL]; ring
  have hp (x : ℝ) : ‖f x‖ * h x = ‖f x‖ := by
    by_cases hx : x ∈ Icc (0 : ℝ) L
    · simp [h, hx]
    · have hf0 : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hm => hx (hfs hm))
      simp [hf0]
  have hc := integral_mul_le_sqrt_sq hf.norm.aestronglyMeasurable hm
    (fun _ => norm_nonneg _) hh0 (physical_sq_integrable hf hfc) hh2
  simp only [hp, hmass] at hc
  simpa only [nativePhysicalL2Norm, mul_comm] using hc

theorem nativePhysicalL1_le_sqrt_length_H1 {f : ℝ → ℂ} {L : ℝ}
    (hL : 0 ≤ L) (hf : Continuous f) (hfs : tsupport f ⊆ Icc (0 : ℝ) L) :
    (∫ x : ℝ, ‖f x‖) ≤ Real.sqrt L * nativePhysicalH1Norm f :=
  (nativePhysicalL1_le_sqrt_length_L2 hL hf hfs).trans
    (mul_le_mul_of_nonneg_left (nativePhysicalL2Norm_le_H1 f) (Real.sqrt_nonneg L))

/-- Every physical correlation value is bounded by the two actual L2
norms. This bound covers both prime shifts without a test-grid premise. -/
theorem nativeWeilTest_norm_le_L2 {f v : ℝ → ℂ}
    (hf : Continuous f) (hv : Continuous v)
    (hfc : HasCompactSupport f) (hvc : HasCompactSupport v) (y : ℝ) :
    ‖EF.weilTest f v y‖ ≤ nativePhysicalL2Norm f * nativePhysicalL2Norm v := by
  have hfi := physical_sq_integrable hf hfc
  have hvi := physical_sq_integrable hv hvc
  have heq : EF.weilTest f v y = ∫ t : ℝ, f t * conj (v (t - y)) := by
    simp only [EF.weilTest, convolution_def, ContinuousLinearMap.mul_apply', EF.tilde]
    congr 1
    funext t
    rw [neg_sub]
  have hc := integral_mul_le_sqrt_sq hf.norm.aestronglyMeasurable
    ((hv.comp (by fun_prop : Continuous (fun t : ℝ => t - y))).norm.aestronglyMeasurable)
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) hfi (hvi.comp_sub_right y)
  simp only [Function.comp_apply] at hc
  have hshift : (∫ x : ℝ, ‖v (x - y)‖ ^ 2) = ∫ x : ℝ, ‖v x‖ ^ 2 :=
    integral_sub_right_eq_self (fun x : ℝ => ‖v x‖ ^ 2) y
  rw [hshift] at hc
  rw [heq]
  calc
    _ ≤ ∫ t : ℝ, ‖f t * conj (v (t - y))‖ := norm_integral_le_integral_norm _
    _ = ∫ t : ℝ, ‖f t‖ * ‖v (t - y)‖ := by simp only [norm_mul, Complex.norm_conj]
    _ ≤ _ := hc

theorem nativeWeilTest_norm_le_H1 {f v : ℝ → ℂ}
    (hf : Continuous f) (hv : Continuous v)
    (hfc : HasCompactSupport f) (hvc : HasCompactSupport v) (y : ℝ) :
    ‖EF.weilTest f v y‖ ≤ nativePhysicalH1Norm f * nativePhysicalH1Norm v := by
  apply (nativeWeilTest_norm_le_L2 hf hv hfc hvc y).trans
  exact mul_le_mul (nativePhysicalL2Norm_le_H1 f) (nativePhysicalL2Norm_le_H1 v)
    (nativePhysicalL2Norm_nonneg v) (nativePhysicalH1Norm_nonneg f)

private theorem nativePaperFT_imaginary_norm_le {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) (a B : ℝ)
    (hb : ∀ x : ℝ, f x ≠ 0 → Real.exp (-a * x) ≤ B) :
    ‖paperFT f ((a : ℂ) * Complex.I)‖ ≤ B * ∫ x : ℝ, ‖f x‖ := by
  rw [nativePaperFT_imaginary]
  have hcont : Continuous (fun x : ℝ => (Real.exp (-a * x) : ℂ) * f x) := by fun_prop
  have hfi : Integrable (fun x : ℝ => (Real.exp (-a * x) : ℂ) * f x) :=
    hcont.integrable_of_hasCompactSupport hfc.mul_left
  calc
    _ ≤ ∫ x : ℝ, ‖(Real.exp (-a * x) : ℂ) * f x‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x : ℝ, B * ‖f x‖ := by
      apply integral_mono_ae hfi.norm ((hf.integrable_of_hasCompactSupport hfc).norm.const_mul B)
      filter_upwards with x
      by_cases hx : f x = 0
      · simp [hx]
      · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        exact mul_le_mul_of_nonneg_right (hb x hx) (norm_nonneg _)
    _ = _ := integral_const_mul _ _

theorem nativeWeilPoleResponse_bilinear_bound {f v : ℝ → ℂ} {L : ℝ}
    (hL : 0 ≤ L) (hf : Continuous f) (hv : Continuous v)
    (hfs : tsupport f ⊆ Icc (0 : ℝ) L) (hvs : tsupport v ⊆ Icc (0 : ℝ) L) :
    ‖∫ x : ℝ, nativeWeilPoleResponse f x * conj (v x)‖ ≤
      2 * L * Real.exp (L / 2) * nativePhysicalH1Norm f * nativePhysicalH1Norm v := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hvc : HasCompactSupport v :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport v) hvs
  have hplus {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
      (hgs : tsupport g ⊆ Icc (0 : ℝ) L) :
      ‖paperFT g (Complex.I / 2)‖ ≤ ∫ x : ℝ, ‖g x‖ := by
    have hh := nativePaperFT_imaginary_norm_le hg hgc (1 / 2) 1 (fun x hx => by
      have hs := hgs (subset_tsupport g hx)
      apply Real.exp_le_one_iff.mpr
      linarith [hs.1])
    have ha : (((1 / 2 : ℝ) : ℂ) * Complex.I) = Complex.I / 2 := by push_cast; ring
    simpa only [ha, one_mul] using hh
  have hminus {g : ℝ → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g)
      (hgs : tsupport g ⊆ Icc (0 : ℝ) L) :
      ‖paperFT g (-Complex.I / 2)‖ ≤ Real.exp (L / 2) * ∫ x : ℝ, ‖g x‖ := by
    have hh := nativePaperFT_imaginary_norm_le hg hgc (-1 / 2) (Real.exp (L / 2))
      (fun x hx => by
        have hs := hgs (subset_tsupport g hx)
        apply Real.exp_le_exp.mpr
        linarith [hs.2])
    have ha : (((-1 / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I / 2 := by push_cast; ring
    simpa only [ha] using hh
  rw [nativeWeilPoleResponse_pairing hv hvc]
  calc
    _ ≤ ‖paperFT f (Complex.I / 2) * conj (paperFT v (-Complex.I / 2))‖ +
        ‖paperFT f (-Complex.I / 2) * conj (paperFT v (Complex.I / 2))‖ := norm_add_le _ _
    _ ≤ (∫ x : ℝ, ‖f x‖) * (Real.exp (L / 2) * ∫ x : ℝ, ‖v x‖) +
        (Real.exp (L / 2) * ∫ x : ℝ, ‖f x‖) * (∫ x : ℝ, ‖v x‖) := by
      simp only [norm_mul, Complex.norm_conj]
      gcongr
      · exact hplus hf hfc hfs
      · exact hminus hv hvc hvs
      · exact hminus hf hfc hfs
      · exact hplus hv hvc hvs
    _ = 2 * Real.exp (L / 2) * ((∫ x : ℝ, ‖f x‖) * (∫ x : ℝ, ‖v x‖)) := by ring
    _ ≤ 2 * Real.exp (L / 2) * ((Real.sqrt L * nativePhysicalH1Norm f) *
        (Real.sqrt L * nativePhysicalH1Norm v)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul (nativePhysicalL1_le_sqrt_length_H1 hL hf hfs)
        (nativePhysicalL1_le_sqrt_length_H1 hL hv hvs)
        (integral_nonneg fun _ => norm_nonneg _)
        (mul_nonneg (Real.sqrt_nonneg L) (nativePhysicalH1Norm_nonneg f))
    _ = _ := by
      calc
        _ = 2 * Real.sqrt L ^ 2 * Real.exp (L / 2) * nativePhysicalH1Norm f *
            nativePhysicalH1Norm v := by ring
        _ = _ := by rw [Real.sq_sqrt hL]

/-- A common physical support of length L gives precisely the difference
support needed by the native finite prime cutoff. -/
theorem nativeWeilTest_common_support {f v : ℝ → ℂ} {L : ℝ}
    (hfs : tsupport f ⊆ Icc (0 : ℝ) L) (hvs : tsupport v ⊆ Icc (0 : ℝ) L) :
    tsupport (EF.weilTest f v) ⊆ Icc (-L) L := by
  refine closure_minimal ?_ isClosed_Icc
  refine (support_convolution_subset (ContinuousLinearMap.mul ℝ ℂ)).trans ?_
  rintro x ⟨a, ha, b, hb, rfl⟩
  have ha' := hfs (subset_tsupport f ha)
  have hb0 : v (-b) ≠ 0 := by
    simpa only [Function.mem_support, EF.tilde, ne_eq, map_eq_zero] using hb
  have hb' := hvs (subset_tsupport v hb0)
  constructor <;> linarith [ha'.1, ha'.2, hb'.1, hb'.2]

private theorem nativePrimeMass_Ioc_eq (N : ℕ) :
    (∑ n ∈ Finset.Ioc 0 N, nativePrimeCoefficient n) =
      ∑ n ∈ Finset.range N, nativePrimeCoefficient (n + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le N), Finset.sum_range_succ, ih]

theorem nativeWeilPrimeCorrelation_bilinear_bound {f v : ℝ → ℂ} {L : ℝ}
    (hL : 0 ≤ L) (hf : Continuous f) (hv : Continuous v)
    (hfs : tsupport f ⊆ Icc (0 : ℝ) L) (hvs : tsupport v ⊆ Icc (0 : ℝ) L) :
    ‖∑' n : ℕ, (nativePrimeCoefficient n : ℂ) *
      (EF.weilTest f v (Real.log n) + EF.weilTest f v (-Real.log n))‖ ≤
      4 * (1 + L) * Real.exp (L / 2) * nativePhysicalH1Norm f * nativePhysicalH1Norm v := by
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hvc : HasCompactSupport v :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport v) hvs
  have hks := nativeWeilTest_common_support hfs hvs
  have hz (n : ℕ) (hn : n ∉ Finset.Ioc 0 ⌊Real.exp L⌋₊) :
      (nativePrimeCoefficient n : ℂ) *
        (EF.weilTest f v (Real.log n) + EF.weilTest f v (-Real.log n)) = 0 := by
    simpa only [nativePrimeCoefficient] using EF.prime_summand_eq_zero hks hn
  rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊Real.exp L⌋₊) hz]
  have hterm (n : ℕ) :
      ‖(nativePrimeCoefficient n : ℂ) *
        (EF.weilTest f v (Real.log n) + EF.weilTest f v (-Real.log n))‖ ≤
      nativePrimeCoefficient n * (2 * nativePhysicalH1Norm f * nativePhysicalH1Norm v) := by
    have hc : 0 ≤ nativePrimeCoefficient n := by unfold nativePrimeCoefficient; positivity
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
    apply mul_le_mul_of_nonneg_left _ hc
    calc
      _ ≤ ‖EF.weilTest f v (Real.log n)‖ + ‖EF.weilTest f v (-Real.log n)‖ := norm_add_le _ _
      _ ≤ nativePhysicalH1Norm f * nativePhysicalH1Norm v +
          nativePhysicalH1Norm f * nativePhysicalH1Norm v :=
        add_le_add (nativeWeilTest_norm_le_H1 hf hv hfc hvc _)
          (nativeWeilTest_norm_le_H1 hf hv hfc hvc _)
      _ = _ := by ring
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊,
        ‖(nativePrimeCoefficient n : ℂ) *
          (EF.weilTest f v (Real.log n) + EF.weilTest f v (-Real.log n))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊,
        nativePrimeCoefficient n * (2 * nativePhysicalH1Norm f * nativePhysicalH1Norm v) :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = (∑ n ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊, nativePrimeCoefficient n) *
        (2 * nativePhysicalH1Norm f * nativePhysicalH1Norm v) := by rw [Finset.sum_mul]
    _ ≤ (2 * (1 + L) * Real.exp (L / 2)) *
        (2 * nativePhysicalH1Norm f * nativePhysicalH1Norm v) := by
      apply mul_le_mul_of_nonneg_right _ (by
        exact mul_nonneg (mul_nonneg (by norm_num) (nativePhysicalH1Norm_nonneg f))
          (nativePhysicalH1Norm_nonneg v))
      rw [nativePrimeMass_Ioc_eq]
      exact nativePrimeMass_finite_bound hL
    _ = _ := by ring

private theorem nativeBoundPair_integrable {R v : ℝ → ℂ}
    (hR : Continuous R) (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (fun x : ℝ => R x * conj (v x)) :=
  (hR.mul (Complex.continuous_conj.comp hv)).integrable_of_hasCompactSupport
    ((hvc.comp_left (g := fun z : ℂ => conj z) (map_zero _)).mul_left)

/-- The complete native finite-aperture H1 estimate. Its constant is
constructed from the native Archimedean constant plus the six explicit
pole/prime units; it is independent of L, f, v and any zero. -/
theorem nativeWeilResponse_bilinear_bound :
    ∃ C_Q : ℝ, 0 < C_Q ∧ ∀ (L : ℝ) (f v : ℝ → ℂ),
      0 ≤ L → ContDiff ℝ 2 f → ContDiff ℝ 2 v →
      tsupport f ⊆ Icc (0 : ℝ) L → tsupport v ⊆ Icc (0 : ℝ) L →
      ‖zetaZeroConfig.W f v‖ ≤ C_Q * (1 + L) * Real.exp (L / 2) *
        nativePhysicalH1Norm f * nativePhysicalH1Norm v := by
  obtain ⟨C_A, hCA, harch⟩ := nativeWeilArchResponse_bilinear_bound
  refine ⟨C_A + 6, by linarith, ?_⟩
  intro L f v hL hf hv hfs hvs
  have hfc : HasCompactSupport f :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport f) hfs
  have hvc : HasCompactSupport v :=
    IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport v) hvs
  have hAi := nativeBoundPair_integrable
    (nativeWeilArchResponse_continuous hf hfc) hv.continuous hvc
  have hPi := nativeBoundPair_integrable
    (nativeWeilPoleResponse_continuous f) hv.continuous hvc
  have hNi := nativeBoundPair_integrable
    (nativeWeilPrimeResponse_continuous hf.continuous hfc) hv.continuous hvc
  have hAP : Integrable (fun x : ℝ => nativeWeilArchResponse f x * conj (v x) +
      nativeWeilPoleResponse f x * conj (v x)) := hAi.add hPi
  have heq : zetaZeroConfig.W f v =
      (∫ x : ℝ, nativeWeilArchResponse f x * conj (v x)) +
      (∫ x : ℝ, nativeWeilPoleResponse f x * conj (v x)) -
      (∫ x : ℝ, nativeWeilPrimeResponse f x * conj (v x)) := by
    rw [nativeWeilResponse_pairing hf hfc hv.continuous hvc]
    simp only [nativeWeilResponse, sub_mul, add_mul]
    rw [integral_sub hAP hNi, integral_add hAi hPi]
  have hA := harch f v hf hv hfc hvc
  have hP := nativeWeilPoleResponse_bilinear_bound hL hf.continuous hv.continuous hfs hvs
  have hN : ‖∫ x : ℝ, nativeWeilPrimeResponse f x * conj (v x)‖ ≤
      4 * (1 + L) * Real.exp (L / 2) * nativePhysicalH1Norm f * nativePhysicalH1Norm v := by
    rw [nativeWeilPrimeResponse_pairing hf.continuous hfc hv.continuous hvc]
    exact nativeWeilPrimeCorrelation_bilinear_bound hL hf.continuous hv.continuous hfs hvs
  have hnf := nativePhysicalH1Norm_nonneg f
  have hnv := nativePhysicalH1Norm_nonneg v
  have he : 1 ≤ Real.exp (L / 2) := Real.one_le_exp_iff.mpr (by linarith)
  have hscale : 1 ≤ (1 + L) * Real.exp (L / 2) := by
    nlinarith [mul_nonneg hL (Real.exp_pos (L / 2)).le]
  rw [heq]
  calc
    _ ≤ ‖∫ x : ℝ, nativeWeilArchResponse f x * conj (v x)‖ +
        ‖∫ x : ℝ, nativeWeilPoleResponse f x * conj (v x)‖ +
        ‖∫ x : ℝ, nativeWeilPrimeResponse f x * conj (v x)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ C_A * nativePhysicalH1Norm f * nativePhysicalH1Norm v +
        2 * L * Real.exp (L / 2) * nativePhysicalH1Norm f * nativePhysicalH1Norm v +
        4 * (1 + L) * Real.exp (L / 2) * nativePhysicalH1Norm f * nativePhysicalH1Norm v :=
      add_le_add (add_le_add hA hP) hN
    _ ≤ C_A * (1 + L) * Real.exp (L / 2) * nativePhysicalH1Norm f * nativePhysicalH1Norm v +
        2 * (1 + L) * Real.exp (L / 2) * nativePhysicalH1Norm f * nativePhysicalH1Norm v +
        4 * (1 + L) * Real.exp (L / 2) * nativePhysicalH1Norm f * nativePhysicalH1Norm v := by
      refine add_le_add (add_le_add ?_ ?_) le_rfl
      · have hh := mul_le_mul_of_nonneg_left hscale hCA.le
        have hh' := mul_le_mul_of_nonneg_right hh (mul_nonneg hnf hnv)
        simpa only [mul_one, mul_assoc] using hh'
      · gcongr
        linarith
    _ = _ := by ring

end Zeta23.CCM

#print axioms Zeta23.CCM.nativePaperFT_parseval_of_integrable_sq
#print axioms Zeta23.CCM.nativePaperFT_weighted_sq_integrable
#print axioms Zeta23.CCM.nativePaperFT_H1_energy
#print axioms Zeta23.CCM.nativePaperFT_H1_mixed_bound
#print axioms Zeta23.CCM.nativePrimeMass_finite_bound
#print axioms Zeta23.CCM.nativeWeilArchResponse_bilinear_bound
#print axioms Zeta23.CCM.nativePhysicalL1_le_sqrt_length_L2
#print axioms Zeta23.CCM.nativeWeilTest_norm_le_H1
#print axioms Zeta23.CCM.nativeWeilPoleResponse_bilinear_bound
#print axioms Zeta23.CCM.nativeWeilTest_common_support
#print axioms Zeta23.CCM.nativeWeilPrimeCorrelation_bilinear_bound
#print axioms Zeta23.CCM.nativeWeilResponse_bilinear_bound
#print axioms Zeta23.CCM.nativePaperFT_sq_integrable
#print axioms Zeta23.CCM.nativePaperFT_deriv_sq_integrable
#print axioms Zeta23.CCM.nativePhysicalH1Norm_nonneg
#print axioms Zeta23.CCM.native_sum_inv_sqrt_succ_le
#print axioms Zeta23.CCM.nativePhysicalL2Norm
#print axioms Zeta23.CCM.nativePhysicalL2Norm_nonneg
#print axioms Zeta23.CCM.nativePhysicalL2Norm_le_H1
#print axioms Zeta23.CCM.nativePhysicalL1_le_sqrt_length_H1
#print axioms Zeta23.CCM.nativeWeilTest_norm_le_L2
