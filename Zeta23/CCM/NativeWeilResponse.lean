import Zeta23.ExceptionalZero.WeilLiteratureBridge
import Zeta23.CCM.UniversalSincPhysicalBounds
import Zeta23.CCM.NativeIntegerPrimeField
import Zeta23.CCM.OriginalDetectorPaddedFiniteH1Rate
import Zeta23.WeilEF.VerticalLine
import Zeta23.ExplicitFormula.Bridge
import Zeta23.GammaFacts.Complete
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Fourier.LpSpace

/-!
# The literal native physical Weil response

The paper Fourier convention is +i. The response keeps both prime
translations and the two elementary poles. Its mixed pairing is linear
in the source and conjugate-linear in the compact test.
-/

noncomputable section

open MeasureTheory Complex Set Filter
open scoped Topology ComplexConjugate FourierTransform

namespace Zeta23.CCM

def nativeWeilArchResponse (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ,
    paperFT f (ξ : ℂ) * (EF.gammaBracket ξ : ℂ) *
      Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))

def nativeWeilPoleResponse (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (Real.exp (x / 2) : ℂ) * (∫ t : ℝ, (Real.exp (-t / 2) : ℂ) * f t) +
    (Real.exp (-x / 2) : ℂ) * (∫ t : ℝ, (Real.exp (t / 2) : ℂ) * f t)

def nativeWeilPrimeResponse (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, (nativePrimeCoefficient n : ℂ) *
    (f (x - Real.log n) + f (x + Real.log n))

def nativeWeilResponse (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  nativeWeilArchResponse f x + nativeWeilPoleResponse f x - nativeWeilPrimeResponse f x

def nativePhysicalH1Norm (f : ℝ → ℂ) : ℝ :=
  originalDetectorPhysicalH1Error f 0

theorem nativeWeilResponse_decomposition (f : ℝ → ℂ) (x : ℝ) :
    nativeWeilResponse f x = nativeWeilArchResponse f x + nativeWeilPoleResponse f x -
      nativeWeilPrimeResponse f x := rfl

/-- A constructed polynomial majorant of the actual gamma bracket. -/
theorem nativeGammaBracket_quadratic_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ ξ : ℝ, |EF.gammaBracket ξ| ≤ C * (1 + ξ ^ 2) := by
  obtain ⟨Cψ, hCψ, hψ⟩ := Zeta23.WeilEF.digamma_growth_strip
  refine ⟨8 * Cψ + |Real.log Real.pi| + 1, by positivity, ?_⟩
  intro ξ
  have harg : (1 / 4 : ℂ) + Complex.I * (ξ : ℂ) / 2 = ⟨1 / 4, ξ / 2⟩ := by
    apply Complex.ext <;> simp <;> ring
  have hψξ := hψ (⟨1 / 4, ξ / 2⟩ : ℂ) (by norm_num) (by norm_num)
  have hlog : Real.log (2 + |ξ / 2|) ≤ 2 + |ξ| / 2 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < 2 + |ξ / 2|)
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h
    linarith
  have hreal : |(Complex.digamma (⟨1 / 4, ξ / 2⟩ : ℂ)).re| ≤
      Cψ * (2 + |ξ| / 2) :=
    (Complex.abs_re_le_norm _).trans (hψξ.trans (mul_le_mul_of_nonneg_left hlog hCψ.le))
  have hgamma : |EF.gammaBracket ξ| ≤ Cψ * (2 + |ξ| / 2) + |Real.log Real.pi| := by
    unfold EF.gammaBracket
    rw [harg]
    exact (abs_sub _ _).trans (add_le_add hreal le_rfl)
  have hξ : |ξ| ≤ 1 + ξ ^ 2 := by
    nlinarith [sq_nonneg (|ξ| - 1 / 2), sq_abs ξ]
  have hC : 0 ≤ |Real.log Real.pi| := abs_nonneg _
  calc
    |EF.gammaBracket ξ| ≤ Cψ * (2 + |ξ| / 2) + |Real.log Real.pi| := hgamma
    _ ≤ (8 * Cψ + |Real.log Real.pi| + 1) * (1 + ξ ^ 2) := by
      nlinarith [sq_nonneg ξ, mul_nonneg hC (sq_nonneg ξ),
        mul_nonneg hCψ.le (sq_nonneg ξ)]

/-- Actual gamma-weighted Fourier integrability, with the proved gamma
facts instantiated rather than passed as an explicit-formula premise. -/
theorem nativeWeilArch_fourier_integrable {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Integrable (fun ξ : ℝ => paperFT f (ξ : ℂ) * (EF.gammaBracket ξ : ℂ)) := by
  have hμ := EF.integrable_paperFT_mul_mu hf hfc Zeta23.gammaFacts
  have heq : (fun ξ : ℝ => paperFT f (ξ : ℂ) * (EF.gammaBracket ξ : ℂ)) =
      fun ξ : ℝ => ((2 * Real.pi : ℝ) : ℂ) *
        (paperFT f (ξ : ℂ) * (Zeta23.mu ξ : ℂ)) := by
    funext ξ
    unfold EF.gammaBracket Zeta23.mu
    push_cast
    field_simp <;> ring
  rw [heq]
  exact hμ.const_mul _

private theorem conjugate_paperFT_real (v : ℝ → ℂ) (ξ : ℝ) :
    conj (paperFT v (ξ : ℂ)) =
      ∫ x : ℝ, Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)) * conj (v x) := by
  rw [paperFT, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul, ← Complex.exp_conj, map_mul, Complex.conj_I,
    Complex.conj_ofReal]
  ring

/-- Correct mixed orientation of the physical Archimedean response. -/
theorem nativeWeilArchResponse_pairing {f v : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    (∫ x : ℝ, nativeWeilArchResponse f x * conj (v x)) =
      (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ,
        paperFT f (ξ : ℂ) * conj (paperFT v (ξ : ℂ)) * (EF.gammaBracket ξ : ℂ) := by
  let k : ℝ → ℂ := fun ξ => paperFT f (ξ : ℂ) * (EF.gammaBracket ξ : ℂ)
  have hk : Integrable k := nativeWeilArch_fourier_integrable hf hfc
  have hvint : Integrable (fun x => conj (v x)) :=
    (Complex.continuous_conj.comp hv).integrable_of_hasCompactSupport
      (hvc.comp_left (g := fun z : ℂ => conj z) (map_zero _))
  have hbase : Integrable (fun p : ℝ × ℝ => k p.1 * conj (v p.2))
      (volume.prod volume) := hk.mul_prod hvint
  have hi : Integrable (fun p : ℝ × ℝ =>
      k p.1 * Complex.exp (-Complex.I * (p.1 : ℂ) * (p.2 : ℂ)) * conj (v p.2))
        (volume.prod volume) := by
    have hh := hbase.mul_bdd (c := 1)
      ((by fun_prop : Continuous (fun p : ℝ × ℝ =>
        Complex.exp (-Complex.I * (p.1 : ℂ) * (p.2 : ℂ)))).aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun p : ℝ × ℝ => by
        rw [Complex.norm_exp]
        simp))
    apply hh.congr
    filter_upwards with p
    ring
  calc
    (∫ x : ℝ, nativeWeilArchResponse f x * conj (v x)) =
        (1 / (2 * Real.pi) : ℂ) * ∫ x : ℝ, ∫ ξ : ℝ,
          k ξ * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)) * conj (v x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      rw [integral_mul_const]
      dsimp [nativeWeilArchResponse, k]
      ring
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ, ∫ x : ℝ,
          k ξ * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)) * conj (v x) := by
      exact congrArg (fun z : ℂ => (1 / (2 * Real.pi) : ℂ) * z)
        (MeasureTheory.integral_integral_swap
          (f := fun ξ (x : ℝ) => k ξ *
            Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)) * conj (v x)) hi).symm
    _ = (1 / (2 * Real.pi) : ℂ) * ∫ ξ : ℝ,
        paperFT f (ξ : ℂ) * conj (paperFT v (ξ : ℂ)) * (EF.gammaBracket ξ : ℂ) := by
      congr 1
      apply integral_congr_ae
      filter_upwards with ξ
      rw [conjugate_paperFT_real]
      calc
        (∫ x : ℝ, k ξ * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)) * conj (v x)) =
            k ξ * (∫ x : ℝ, Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)) * conj (v x)) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with x
          ring
        _ = _ := by dsimp [k]; ring

theorem nativePaperFT_imaginary (f : ℝ → ℂ) (a : ℝ) :
    paperFT f ((a : ℂ) * Complex.I) =
      ∫ x : ℝ, (Real.exp (-a * x) : ℂ) * f x := by
  unfold paperFT
  apply integral_congr_ae
  filter_upwards with x
  have he : Complex.I * ((a : ℂ) * Complex.I) * (x : ℂ) = ((-a * x : ℝ) : ℂ) := by
    push_cast
    calc
      _ = (Complex.I * Complex.I) * (a : ℂ) * (x : ℂ) := by ring
      _ = _ := by rw [Complex.I_mul_I]; ring
  rw [he, ← Complex.ofReal_exp]
  ring

private theorem native_conjugate_weighted_integral (v : ℝ → ℂ) (a : ℝ) :
    (∫ x : ℝ, (Real.exp (-a * x) : ℂ) * conj (v x)) =
      conj (paperFT v ((a : ℂ) * Complex.I)) := by
  rw [nativePaperFT_imaginary, ← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp only [map_mul, Complex.conj_ofReal]

theorem nativeWeilPoleResponse_pairing {f v : ℝ → ℂ}
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    (∫ x : ℝ, nativeWeilPoleResponse f x * conj (v x)) =
      paperFT f (Complex.I / 2) * conj (paperFT v (-Complex.I / 2)) +
        paperFT f (-Complex.I / 2) * conj (paperFT v (Complex.I / 2)) := by
  have hplus : Integrable (fun x : ℝ => (Real.exp (x / 2) : ℂ) * conj (v x)) :=
    (by fun_prop : Continuous (fun x : ℝ => (Real.exp (x / 2) : ℂ) * conj (v x))).integrable_of_hasCompactSupport
      ((hvc.comp_left (g := fun z : ℂ => conj z) (map_zero _)).mul_left)
  have hminus : Integrable (fun x : ℝ => (Real.exp (-x / 2) : ℂ) * conj (v x)) :=
    (by fun_prop : Continuous (fun x : ℝ => (Real.exp (-x / 2) : ℂ) * conj (v x))).integrable_of_hasCompactSupport
      ((hvc.comp_left (g := fun z : ℂ => conj z) (map_zero _)).mul_left)
  have heq : (fun x => nativeWeilPoleResponse f x * conj (v x)) =
      fun x => (∫ t : ℝ, (Real.exp (-t / 2) : ℂ) * f t) *
          ((Real.exp (x / 2) : ℂ) * conj (v x)) +
        (∫ t : ℝ, (Real.exp (t / 2) : ℂ) * f t) *
          ((Real.exp (-x / 2) : ℂ) * conj (v x)) := by
    funext x
    dsimp [nativeWeilPoleResponse]
    ring
  rw [heq, integral_add (hplus.const_mul _) (hminus.const_mul _),
    integral_const_mul, integral_const_mul]
  have hargplus : (((1 / 2 : ℝ) : ℂ) * Complex.I) = Complex.I / 2 := by push_cast; ring
  have hargminus : (((-1 / 2 : ℝ) : ℂ) * Complex.I) = -Complex.I / 2 := by push_cast; ring
  have hfp := nativePaperFT_imaginary f (1 / 2)
  have hfm := nativePaperFT_imaginary f (-1 / 2)
  have hvp := native_conjugate_weighted_integral v (1 / 2)
  have hvm := native_conjugate_weighted_integral v (-1 / 2)
  simp only [hargplus, hargminus] at hfp hfm hvp hvm
  have ep (x : ℝ) : -(1 / 2 : ℝ) * x = -x / 2 := by ring
  have em (x : ℝ) : -(-1 / 2 : ℝ) * x = x / 2 := by ring
  simp only [ep, em] at hfp hfm hvp hvm
  rw [← hfp, ← hfm, hvp, hvm]

private theorem nativePrimeTranslate_zero_above_history {f : ℝ → ℂ} {R T x : ℝ}
    (hR : ∀ y, f y ≠ 0 → |y| ≤ R) (hx : |x| ≤ T) {n : ℕ}
    (hn : nativeHistoryCutoff R T < n) :
    f (x - Real.log n) = 0 ∧ f (x + Real.log n) = 0 := by
  have hexp : Real.exp (T + R) < (n : ℝ) := Nat.lt_of_floor_lt hn
  have hnpos : 0 < (n : ℝ) := (Real.exp_pos _).trans hexp
  have hlog : T + R < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hexp
  constructor
  · by_contra hne
    have hb := (abs_le.mp (hR _ hne)).1
    linarith [(abs_le.mp hx).2]
  · by_contra hne
    have hb := (abs_le.mp (hR _ hne)).2
    linarith [(abs_le.mp hx).1]

/-- One cutoff works for both translations at every point of the chosen
compact observation interval. -/
theorem nativeWeilPrimeResponse_eq_history_sum {f : ℝ → ℂ} {R T x : ℝ}
    (hR : ∀ y, f y ≠ 0 → |y| ≤ R) (hx : |x| ≤ T) :
    nativeWeilPrimeResponse f x =
      ∑ n ∈ Finset.range (nativeHistoryCutoff R T + 1),
        (nativePrimeCoefficient n : ℂ) * (f (x - Real.log n) + f (x + Real.log n)) := by
  unfold nativeWeilPrimeResponse
  apply tsum_eq_sum
  intro n hn
  have hcut : nativeHistoryCutoff R T < n := by
    simp only [Finset.mem_range, not_lt] at hn
    omega
  have hz := nativePrimeTranslate_zero_above_history hR hx hcut
  rw [hz.1, hz.2, zero_add, mul_zero]

theorem nativeWeilPrimeResponse_continuous {f : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (nativeWeilPrimeResponse f) := by
  obtain ⟨R, hR⟩ := EF.exists_abs_le_of_hasCompactSupport hfc
  apply continuous_iff_continuousAt.mpr
  intro x
  let T : ℝ := |x| + 1
  have hsum : Continuous (fun y : ℝ =>
      ∑ n ∈ Finset.range (nativeHistoryCutoff R T + 1),
        (nativePrimeCoefficient n : ℂ) * (f (y - Real.log n) + f (y + Real.log n))) := by
    fun_prop
  apply hsum.continuousAt.congr_of_eventuallyEq
  have hneighborhood : ∀ᶠ y in 𝓝 x, |y| < T :=
    (isOpen_lt continuous_abs continuous_const).mem_nhds (by dsimp [T]; linarith)
  filter_upwards [hneighborhood] with y hy
  exact nativeWeilPrimeResponse_eq_history_sum hR hy.le

theorem nativeWeilPoleResponse_continuous (f : ℝ → ℂ) :
    Continuous (nativeWeilPoleResponse f) := by
  unfold nativeWeilPoleResponse
  fun_prop

private theorem nativeWeilTest_eq_translation_pairing (f v : ℝ → ℂ) (a : ℝ) :
    EF.weilTest f v a = ∫ x : ℝ, f (x + a) * conj (v x) := by
  unfold EF.weilTest
  simp only [convolution_def, ContinuousLinearMap.mul_apply', EF.tilde, neg_sub]
  have h := integral_sub_right_eq_self (μ := volume) (fun x : ℝ => f (x + a) * conj (v x)) a
  simpa only [sub_add_cancel] using h

private theorem nativePrimeTranslate_pairing {f v : ℝ → ℂ}
    (hf : Continuous f) (hv : Continuous v) (hvc : HasCompactSupport v) (n : ℕ) :
    (∫ x : ℝ, ((nativePrimeCoefficient n : ℂ) *
        (f (x - Real.log n) + f (x + Real.log n))) * conj (v x)) =
      (nativePrimeCoefficient n : ℂ) *
        (EF.weilTest f v (Real.log n) + EF.weilTest f v (-Real.log n)) := by
  have hcv : Continuous (fun x : ℝ => conj (v x)) := Complex.continuous_conj.comp hv
  have hcc : HasCompactSupport (fun x : ℝ => conj (v x)) :=
    hvc.comp_left (g := fun z : ℂ => conj z) (map_zero _)
  have hm : Integrable (fun x : ℝ => f (x - Real.log n) * conj (v x)) :=
    ((hf.comp (continuous_id.sub continuous_const)).mul hcv).integrable_of_hasCompactSupport hcc.mul_left
  have hp : Integrable (fun x : ℝ => f (x + Real.log n) * conj (v x)) :=
    ((hf.comp (continuous_id.add continuous_const)).mul hcv).integrable_of_hasCompactSupport hcc.mul_left
  calc
    _ = (nativePrimeCoefficient n : ℂ) * ∫ x : ℝ,
        (f (x - Real.log n) * conj (v x) + f (x + Real.log n) * conj (v x)) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = (nativePrimeCoefficient n : ℂ) *
        ((∫ x : ℝ, f (x + (-Real.log n)) * conj (v x)) +
          ∫ x : ℝ, f (x + Real.log n) * conj (v x)) := by
      rw [integral_add hm hp]
      simp only [sub_eq_add_neg]
    _ = _ := by
      rw [← nativeWeilTest_eq_translation_pairing, ← nativeWeilTest_eq_translation_pairing]
      ring

/-- Literal prime mixed pairing, with both histories and a single compact
cutoff chosen before exchanging the finite sum and integral. -/
theorem nativeWeilPrimeResponse_pairing {f v : ℝ → ℂ}
    (hf : Continuous f) (hfc : HasCompactSupport f)
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    (∫ x : ℝ, nativeWeilPrimeResponse f x * conj (v x)) =
      ∑' n : ℕ, (nativePrimeCoefficient n : ℂ) *
        (EF.weilTest f v (Real.log n) + EF.weilTest f v (-Real.log n)) := by
  obtain ⟨R, hR⟩ := EF.exists_abs_le_of_hasCompactSupport hfc
  obtain ⟨T, hT⟩ := EF.exists_abs_le_of_hasCompactSupport hvc
  let S : Finset ℕ := Finset.range (nativeHistoryCutoff R T + 1)
  have hprod : (fun x : ℝ => nativeWeilPrimeResponse f x * conj (v x)) = fun x =>
      ∑ n ∈ S, ((nativePrimeCoefficient n : ℂ) *
        (f (x - Real.log n) + f (x + Real.log n))) * conj (v x) := by
    funext x
    rw [← Finset.sum_mul]
    by_cases hx : v x = 0
    · simp only [hx, map_zero, mul_zero]
    · rw [nativeWeilPrimeResponse_eq_history_sum hR (hT x hx)]
  have hzero (n : ℕ) (hn : n ∉ S) :
      (nativePrimeCoefficient n : ℂ) *
        (EF.weilTest f v (Real.log n) + EF.weilTest f v (-Real.log n)) = 0 := by
    rw [← nativePrimeTranslate_pairing hf hv hvc n]
    apply integral_eq_zero_of_ae
    filter_upwards with x
    change ((nativePrimeCoefficient n : ℂ) *
      (f (x - Real.log n) + f (x + Real.log n))) * conj (v x) = (0 : ℂ)
    by_cases hx : v x = 0
    · simp [hx]
    · have hcut : nativeHistoryCutoff R T < n := by
        simp only [S, Finset.mem_range, not_lt] at hn
        omega
      have hz := nativePrimeTranslate_zero_above_history hR (hT x hx) hcut
      rw [hz.1, hz.2, zero_add, mul_zero, zero_mul]
  have hint (n : ℕ) : Integrable (fun x : ℝ =>
      ((nativePrimeCoefficient n : ℂ) *
        (f (x - Real.log n) + f (x + Real.log n))) * conj (v x)) := by
    have hc : Continuous (fun x : ℝ =>
        ((nativePrimeCoefficient n : ℂ) *
          (f (x - Real.log n) + f (x + Real.log n))) * conj (v x)) := by fun_prop
    exact hc.integrable_of_hasCompactSupport
      ((hvc.comp_left (g := fun z : ℂ => conj z) (map_zero _)).mul_left)
  rw [hprod, integral_finsetSum S (fun n _ => hint n), tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro n hn
  exact nativePrimeTranslate_pairing hf hv hvc n

theorem nativeWeilArchResponse_continuous {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (nativeWeilArchResponse f) := by
  let k : ℝ → ℂ := fun ξ => paperFT f (ξ : ℂ) * (EF.gammaBracket ξ : ℂ)
  have hk : Integrable k := nativeWeilArch_fourier_integrable hf hfc
  have hmeas (x : ℝ) : AEStronglyMeasurable (fun ξ : ℝ =>
      k ξ * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) volume :=
    hk.aestronglyMeasurable.mul (by fun_prop : Continuous (fun ξ : ℝ =>
      Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ)))).aestronglyMeasurable
  have hbound (x : ℝ) : ∀ᵐ ξ : ℝ, ‖k ξ *
      Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))‖ ≤ ‖k ξ‖ := by
    filter_upwards with ξ
    rw [norm_mul, Complex.norm_exp]
    simp
  have hc : Continuous (fun x : ℝ => ∫ ξ : ℝ,
      k ξ * Complex.exp (-Complex.I * (ξ : ℂ) * (x : ℂ))) :=
    continuous_of_dominated hmeas hbound hk.norm
      (Filter.Eventually.of_forall fun ξ : ℝ => by fun_prop)
  exact continuous_const.mul hc

theorem nativeWeilResponse_continuous {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Continuous (nativeWeilResponse f) :=
  ((nativeWeilArchResponse_continuous hf hfc).add (nativeWeilPoleResponse_continuous f)).sub
    (nativeWeilPrimeResponse_continuous hf.continuous hfc)

/-- The total physical response has actual L2 membership on every finite
interval. This makes no global exterior-L2 assertion. -/
theorem nativeWeilResponse_memLp_two_on_interval {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (a b : ℝ) :
    MemLp (nativeWeilResponse f) 2 (volume.restrict (Icc a b)) := by
  have hc := nativeWeilResponse_continuous hf hfc
  exact (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
    (hc.norm.pow 2).continuousOn.integrableOn_Icc

theorem nativeWeilResponse_indicator_memLp_two {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (a b : ℝ) :
    MemLp ((Icc a b).indicator (nativeWeilResponse f)) 2 volume :=
  (memLp_indicator_iff_restrict measurableSet_Icc).mpr
    (nativeWeilResponse_memLp_two_on_interval hf hfc a b)

private theorem nativeResponsePair_integrable {r v : ℝ → ℂ}
    (hr : Continuous r) (hv : Continuous v) (hvc : HasCompactSupport v) :
    Integrable (fun x : ℝ => r x * conj (v x)) :=
  (hr.mul (Complex.continuous_conj.comp hv)).integrable_of_hasCompactSupport
    ((hvc.comp_left (g := fun z : ℂ => conj z) (map_zero _)).mul_left)

/-- The actual mixed Weil form equals the literal total physical response,
with the source in the linear slot and the compact test conjugated. -/
theorem nativeWeilResponse_pairing {f v : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hv : Continuous v) (hvc : HasCompactSupport v) :
    zetaZeroConfig.W f v = ∫ x : ℝ, nativeWeilResponse f x * conj (v x) := by
  have hA := nativeResponsePair_integrable (nativeWeilArchResponse_continuous hf hfc) hv hvc
  have hP := nativeResponsePair_integrable (nativeWeilPoleResponse_continuous f) hv hvc
  have hN := nativeResponsePair_integrable (nativeWeilPrimeResponse_continuous hf.continuous hfc) hv hvc
  have hAP : Integrable (fun x : ℝ => nativeWeilArchResponse f x * conj (v x) +
      nativeWeilPoleResponse f x * conj (v x)) := hA.add hP
  have heq : (fun x : ℝ => nativeWeilResponse f x * conj (v x)) =
      fun x => (nativeWeilArchResponse f x * conj (v x) +
        nativeWeilPoleResponse f x * conj (v x)) - nativeWeilPrimeResponse f x * conj (v x) := by
    funext x
    unfold nativeWeilResponse
    ring
  rw [heq, integral_sub hAP hN, integral_add hA hP,
    nativeWeilArchResponse_pairing hf hfc hv hvc, nativeWeilPoleResponse_pairing hv hvc,
    nativeWeilPrimeResponse_pairing hf.continuous hfc hv hvc,
    ExceptionalZero.zeta_W_eq_literatureRHS_weilTest hf hv hfc hvc]
  have hfac := EF.paperFT_weilTest hf.continuous hv hfc hvc
  have hp := hfac (Complex.I / 2)
  have hm := hfac (-Complex.I / 2)
  have htwo : conj (2 : ℂ) = 2 := by
    convert! (Complex.conj_ofReal (2 : ℝ)) using 1 <;> norm_num
  have hconjp : conj (Complex.I / 2) = -Complex.I / 2 := by rw [map_div₀, Complex.conj_I, htwo]
  have hconjm : conj (-Complex.I / 2) = Complex.I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, htwo]
  rw [hconjp] at hp
  rw [hconjm] at hm
  have harch : (fun ξ : ℝ => paperFT (EF.weilTest f v) (ξ : ℂ) * (EF.gammaBracket ξ : ℂ)) =
      fun ξ : ℝ => paperFT f (ξ : ℂ) * conj (paperFT v (ξ : ℂ)) * (EF.gammaBracket ξ : ℂ) := by
    funext ξ
    rw [hfac, Complex.conj_ofReal]
  unfold EF.literatureRHS
  rw [hp, hm, harch]
  unfold nativePrimeCoefficient
  ring

/-- The actual gamma-weighted Fourier multiplier is L2 as well as L1.
Its uniform bound comes from the proved quadratic gamma majorant and
actual compact-C2 Fourier decay. -/
theorem nativeWeilArch_fourier_memLp_two {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    MemLp (fun ξ : ℝ => paperFT f (ξ : ℂ) * (EF.gammaBracket ξ : ℂ)) 2 volume := by
  let k : ℝ → ℂ := fun ξ => paperFT f (ξ : ℂ) * (EF.gammaBracket ξ : ℂ)
  have hk : Integrable k := nativeWeilArch_fourier_integrable hf hfc
  obtain ⟨R, hR⟩ := EF.exists_abs_le_of_hasCompactSupport hfc
  obtain ⟨C, hC, hgamma⟩ := nativeGammaBracket_quadratic_bound
  let K : ℝ := (∫ x : ℝ, ‖f x‖) + ∫ x : ℝ, ‖deriv (deriv f) x‖
  have hbound (ξ : ℝ) : ‖k ξ‖ ≤ C * K := by
    have hF := EF.norm_paperFT_mul_one_add_sq_le hf hR ξ
    dsimp only [k]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc
      _ ≤ ‖paperFT f (ξ : ℂ)‖ * (C * (1 + ξ ^ 2)) :=
        mul_le_mul_of_nonneg_left (hgamma ξ) (norm_nonneg _)
      _ = C * (‖paperFT f (ξ : ℂ)‖ * (1 + ξ ^ 2)) := by ring
      _ ≤ C * K := mul_le_mul_of_nonneg_left hF hC.le
  apply (memLp_two_iff_integrable_sq_norm hk.aestronglyMeasurable).mpr
  apply (hk.norm.const_mul (C * K)).mono' (hk.aestronglyMeasurable.norm.pow 2)
  filter_upwards with ξ
  change ‖‖k ξ‖ ^ 2‖ ≤ C * K * ‖k ξ‖
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  nlinarith [mul_le_mul_of_nonneg_right (hbound ξ) (norm_nonneg (k ξ))]

private theorem nativeFourier_memLp_two_of_integrable {k : ℝ → ℂ}
    (hk : Integrable k) (hk2 : MemLp k 2 volume) : MemLp (𝓕 k) 2 volume := by
  let v : Lp ℂ 2 (volume : Measure ℝ) := hk2.toLp k
  let V : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 v
  have hae : (𝓕 k) =ᵐ[volume] V := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (EF.continuous_fourier_of_integrable hk).locallyIntegrable
      ((Lp.memLp V).locallyIntegrable (by norm_num))
    intro g hg hgc
    let gC : ℝ → ℂ := fun x => (g x : ℂ)
    have hgC : ContDiff ℝ (⊤ : ℕ∞) gC :=
      Complex.ofRealCLM.contDiff.comp hg
    have hgcC : HasCompactSupport gC := hgc.comp_left (g := fun r : ℝ => (r : ℂ)) rfl
    let phi : SchwartzMap ℝ ℂ := hgcC.toSchwartzMap hgC
    have hp := congrArg (fun T : TemperedDistribution ℝ ℂ => T phi)
      (Lp.fourier_toTemperedDistribution_eq v)
    simp only [TemperedDistribution.fourier_apply, Lp.toTemperedDistribution_apply,
      smul_eq_mul] at hp
    change (∫ x : ℝ, (𝓕 phi) x * v x) = ∫ x : ℝ, phi x * V x at hp
    have hreplace : (∫ x : ℝ, (𝓕 phi) x * v x) = ∫ x : ℝ, (𝓕 phi) x * k x := by
      apply integral_congr_ae
      filter_upwards [hk2.coeFn_toLp] with x hx
      rw [hx]
    have hdual : (∫ x : ℝ, (𝓕 phi) x * k x) = ∫ x : ℝ, phi x * (𝓕 k) x := by
      simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
        (ContinuousLinearMap.mul ℂ ℂ) (L := innerₗ ℝ)
        Real.continuous_fourierChar (by exact continuous_inner) phi.integrable hk
    have hpair := hdual.symm.trans (hreplace.symm.trans hp)
    simpa [phi, gC, Complex.real_smul] using! hpair
  exact MemLp.ae_eq hae.symm (Lp.memLp V)

/-- The literal full-line Archimedean response itself belongs to L2.
The pointwise Fourier integral is identified with the actual L2 transform,
rather than transferring membership from its multiplier by terminology. -/
theorem nativeWeilArchResponse_memLp_two {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    MemLp (nativeWeilArchResponse f) 2 volume := by
  let k : ℝ → ℂ := fun ξ => paperFT f (ξ : ℂ) * (EF.gammaBracket ξ : ℂ)
  have hk : Integrable k := nativeWeilArch_fourier_integrable hf hfc
  have hk2 : MemLp k 2 volume := nativeWeilArch_fourier_memLp_two hf hfc
  have hF2 : MemLp (𝓕 k) 2 volume := nativeFourier_memLp_two_of_integrable hk hk2
  have hFc : Continuous (𝓕 k) := EF.continuous_fourier_of_integrable hk
  have hsq : Integrable (fun x : ℝ => ‖(𝓕 k) x‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hFc.aestronglyMeasurable).mp hF2
  have hsquare : Integrable (fun x : ℝ => ‖(𝓕 k) ((1 / (2 * Real.pi)) * x)‖ ^ 2) :=
    hsq.comp_mul_left' (by positivity : (1 / (2 * Real.pi) : ℝ) ≠ 0)
  have hscaled : MemLp (fun x : ℝ => (𝓕 k) ((1 / (2 * Real.pi)) * x)) 2 volume :=
    (memLp_two_iff_integrable_sq_norm
      (hFc.comp (continuous_const.mul continuous_id)).aestronglyMeasurable).mpr hsquare
  have heq : nativeWeilArchResponse f = fun x : ℝ =>
      (1 / (2 * Real.pi) : ℂ) * (𝓕 k) ((1 / (2 * Real.pi)) * x) := by
    funext x
    unfold nativeWeilArchResponse
    rw [Real.fourier_real_eq_integral_exp_smul]
    congr 1
    apply integral_congr_ae
    filter_upwards with ξ
    rw [smul_eq_mul]
    have hphase : (((-2 * Real.pi * ξ * ((1 / (2 * Real.pi)) * x) : ℝ) : ℂ) *
        Complex.I) = -Complex.I * (ξ : ℂ) * (x : ℂ) := by
      push_cast
      field_simp
    rw [hphase]
    dsimp only [k]
    ring
  rw [heq]
  exact hscaled.const_mul _

end Zeta23.CCM

#print axioms Zeta23.CCM.nativeWeilResponse_decomposition
#print axioms Zeta23.CCM.nativeGammaBracket_quadratic_bound
#print axioms Zeta23.CCM.nativeWeilArch_fourier_integrable
#print axioms Zeta23.CCM.nativeWeilArchResponse_pairing
#print axioms Zeta23.CCM.nativePaperFT_imaginary
#print axioms Zeta23.CCM.nativeWeilPoleResponse_pairing
#print axioms Zeta23.CCM.nativeWeilPrimeResponse_eq_history_sum
#print axioms Zeta23.CCM.nativeWeilPrimeResponse_continuous
#print axioms Zeta23.CCM.nativeWeilPoleResponse_continuous
#print axioms Zeta23.CCM.nativeWeilPrimeResponse_pairing
#print axioms Zeta23.CCM.nativeWeilArchResponse_continuous
#print axioms Zeta23.CCM.nativeWeilResponse_continuous
#print axioms Zeta23.CCM.nativeWeilResponse_memLp_two_on_interval
#print axioms Zeta23.CCM.nativeWeilResponse_indicator_memLp_two
#print axioms Zeta23.CCM.nativeWeilResponse_pairing
#print axioms Zeta23.CCM.nativeWeilArch_fourier_memLp_two
#print axioms Zeta23.CCM.nativeWeilArchResponse_memLp_two
