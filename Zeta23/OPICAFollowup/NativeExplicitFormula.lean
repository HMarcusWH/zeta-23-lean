import Zeta23.RvM.LocalCount
import Zeta23.WeilEF.Main
import Zeta23.OPICAFollowup.NativeSourceTransforms
import Zeta23.CCM.DictionaryArchSourceBridge
import Zeta23.GammaFacts.Complete
import Mathlib.Tactic

/-!
# The actual zeta zero configuration and native source formula

The carrier is the genuine nontrivial zero set of Mathlib's zeta function,
and its multiplicity is analytic order.  Both imaginary signs are retained.
The displacement supremum includes zero explicitly, so no nonempty zero set,
maximal zero, simplicity, or positive minimum displacement is assumed.
-/

noncomputable section
open Set Filter MeasureTheory Complex
open scoped Topology BigOperators FourierTransform

namespace Zeta23.OPICAFollowup

open Zeta23.CCM

/-- Actual analytic multiplicities on the entire zeta zero carrier.  The second
weight is in the actual ordinate, and neither series restricts its imaginary sign. -/
theorem native_zero_count_summability :
    Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ))) ∧
    Summable (fun ρ : zetaZeroConfig.carrier =>
      (zetaZeroConfig.mult ρ : ℝ) / (1 + ((ρ : ℂ).im) ^ 2)) := by
  obtain ⟨A, hA, hcount⟩ := RvM.zetaZeroConfig_local_count
  have hbase := WeilEF.zero_sum_inv_sq_gen zetaZeroConfig hA hcount
  refine ⟨hbase, Summable.of_nonneg_of_le (fun ρ => by positivity) ?_ (hbase.mul_left 2)⟩
  intro ρ
  have hstrip := zetaZeroConfig.strip (ρ : ℂ) ρ.property
  have hden : 1 + Complex.normSq (gammaOf (ρ : ℂ)) ≤ 2 * (1 + ((ρ : ℂ).im)^2) := by
    rw [Complex.normSq_apply, WeilEF.gammaOf_re, WeilEF.gammaOf_im]
    nlinarith [mul_nonneg hstrip.1 (sub_nonneg.mpr hstrip.2), sq_nonneg ((ρ : ℂ).im)]
  have hm : (0 : ℝ) ≤ zetaZeroConfig.mult ρ := Nat.cast_nonneg _
  have hd₁ : 0 < 1 + ((ρ : ℂ).im)^2 := by positivity
  have hd₂ : 0 < 1 + Complex.normSq (gammaOf (ρ : ℂ)) := by
    nlinarith [Complex.normSq_nonneg (gammaOf (ρ : ℂ))]
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hd₁ hd₂).mpr
  nlinarith [mul_le_mul_of_nonneg_left hden hm]

/-- Actual positive right displacements, together with zero. -/
def nativeZeroDisplacementSet : Set ℝ :=
  insert 0 (Set.range (fun ρ : zetaZeroConfig.carrier => max ((ρ : ℂ).re - 1/2) 0))

/-- The actual zero-displacement supremum; it need not be attained. -/
def nativeZeroDisplacementSup : ℝ := sSup nativeZeroDisplacementSet

private theorem native_zero_displacement_set_nonempty : nativeZeroDisplacementSet.Nonempty :=
  ⟨0, Set.mem_insert _ _⟩

private theorem native_zero_displacement_set_bounded : BddAbove nativeZeroDisplacementSet := by
  refine ⟨1/2, ?_⟩
  intro x hx
  rcases Set.mem_insert_iff.mp hx with hx | hx
  · rw [hx]; norm_num
  · obtain ⟨ρ, rfl⟩ := hx
    have hstrip := zetaZeroConfig.strip (ρ : ℂ) ρ.property
    exact max_le (by linarith [hstrip.2]) (by norm_num)

/-- Bounds and strict supremum selection for the actual nontrivial zeros.
Only an approximating zero is selected; there is no attaining-zero premise. -/
theorem native_zero_sup_bounds :
    0 ≤ nativeZeroDisplacementSup ∧ nativeZeroDisplacementSup ≤ 1/2 ∧
    (∀ ρ : zetaZeroConfig.carrier,
      max ((ρ : ℂ).re - 1/2) 0 ≤ nativeZeroDisplacementSup) ∧
    (∀ b : ℝ, 0 ≤ b → b < nativeZeroDisplacementSup →
      ∃ ρ : zetaZeroConfig.carrier, b < (ρ : ℂ).re - 1/2) := by
  have hzero : 0 ≤ nativeZeroDisplacementSup :=
    le_csSup native_zero_displacement_set_bounded (Set.mem_insert _ _)
  have hupper : nativeZeroDisplacementSup ≤ 1/2 := by
    apply csSup_le native_zero_displacement_set_nonempty
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx]; norm_num
    · obtain ⟨ρ, rfl⟩ := hx
      have hstrip := zetaZeroConfig.strip (ρ : ℂ) ρ.property
      exact max_le (by linarith [hstrip.2]) (by norm_num)
  refine ⟨hzero, hupper, ?_, ?_⟩
  · intro ρ
    apply le_csSup native_zero_displacement_set_bounded
    exact Set.mem_insert_of_mem _ ⟨ρ, rfl⟩
  · intro b hb hblt
    obtain ⟨x, hx, hbx⟩ := exists_lt_of_lt_csSup native_zero_displacement_set_nonempty hblt
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · rw [hx] at hbx
      linarith
    · obtain ⟨ρ, rfl⟩ := hx
      rcases lt_max_iff.mp hbx with h | h
      · exact ⟨ρ, h⟩
      · linarith

/-- The actual translated compact source used in the literal zeta explicit formula. -/
def translatedNativeSourceTest (d : ℕ) (t u : ℝ) : ℂ :=
  (sourceOrderFamily d (t-u) : ℂ)

theorem translatedNativeSourceTest_contDiff (d : ℕ) (t : ℝ) :
    ContDiff ℝ 2 (translatedNativeSourceTest d t) := by
  exact ((sourceFamily_complex_contDiff d).of_le
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)).comp (contDiff_const.sub contDiff_id)

theorem translatedNativeSourceTest_hasCompactSupport (d : ℕ) (t : ℝ) :
    HasCompactSupport (translatedNativeSourceTest d t) := by
  apply HasCompactSupport.intro
    (K := Icc (t-UniversalSinc.fixedScale) (t+UniversalSinc.fixedScale)) isCompact_Icc
  intro u hu
  unfold translatedNativeSourceTest
  rw [sourceFamily_supported d (t-u) ?_, Complex.ofReal_zero]
  intro hmem
  apply hu
  exact ⟨by linarith [hmem.2], by linarith [hmem.1]⟩

/-- Translation and reversal retain the exact source shift and Laplace sign. -/
theorem translatedNativeSourceTest_paperFT (d : ℕ) (t : ℝ) (z : ℂ) :
    paperFT (translatedNativeSourceTest d t) z =
      Complex.exp (I*z*(t : ℂ)) * sourceFamilyLaplace d (I*z) := by
  calc
    _ = ∫ u : ℝ, (sourceOrderFamily d u : ℂ) * Complex.exp (I*z*((t-u : ℝ) : ℂ)) := by
      have h := integral_sub_left_eq_self
        (fun u : ℝ => (sourceOrderFamily d u : ℂ) * Complex.exp (I*z*((t-u : ℝ) : ℂ))) volume t
      simpa [paperFT, translatedNativeSourceTest] using h
    _ = _ := by
      unfold sourceFamilyLaplace
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with u
      have he : I*z*((t-u : ℝ) : ℂ) = I*z*(t : ℂ) + -(I*z)*(u : ℂ) := by
        push_cast
        ring
      rw [he, Complex.exp_add]
      ring

theorem nativeGammaOf_shift (ρ : ℂ) : I * gammaOf ρ = ρ - 1/2 := by
  unfold gammaOf
  field_simp

/-- The actual source coefficient and actual analytic zero multiplicity. -/
def nativeNontrivialZeroTerm (d : ℕ) (t : ℝ) (ρ : zetaZeroConfig.carrier) : ℂ :=
  (zetaZeroConfig.mult ρ : ℂ) * sourceFamilyLaplace d ((ρ : ℂ)-1/2) *
    Complex.exp (((ρ : ℂ)-1/2)*(t : ℂ))

theorem nativeNontrivialZeroTerm_eq_translated_test (d : ℕ) (t : ℝ)
    (ρ : zetaZeroConfig.carrier) :
    nativeNontrivialZeroTerm d t ρ =
      (zetaZeroConfig.mult ρ : ℂ) * paperFT (translatedNativeSourceTest d t) (gammaOf ρ) := by
  rw [translatedNativeSourceTest_paperFT, nativeGammaOf_shift]
  unfold nativeNontrivialZeroTerm
  ring

/-- Absolute convergence of the actual nontrivial zero series, before any rearrangement. -/
theorem nativeNontrivialZeroTerm_summable_norm (d : ℕ) (t : ℝ) :
    Summable (fun ρ : zetaZeroConfig.carrier => ‖nativeNontrivialZeroTerm d t ρ‖) := by
  have h := (WeilEF.EF_lit_zetaZeroConfig (translatedNativeSourceTest d t)
    (translatedNativeSourceTest_contDiff d t) (translatedNativeSourceTest_hasCompactSupport d t)).1
  apply summable_norm_iff.mpr
  exact h.congr (fun ρ => (nativeNontrivialZeroTerm_eq_translated_test d t ρ).symm)

/-- Both elementary poles are killed by the actual source, including derivative order zero. -/
theorem nativeSourceLaplace_elementary_cancellation (d : ℕ) :
    sourceFamilyLaplace d (1/2) = 0 ∧ sourceFamilyLaplace d (-1/2) = 0 := by
  constructor <;>
    rw [sourceFamilyLaplace_factor, ExceptionalZero.nativeOriginalSourceLaplace_formula] <;>
    norm_num [mul_pow, Complex.I_sq]

theorem translatedNativeSourceTest_elementary_cancellation (d : ℕ) (t : ℝ) :
    paperFT (translatedNativeSourceTest d t) (I/2) +
      paperFT (translatedNativeSourceTest d t) (-I/2) = 0 := by
  have h₁ : I * (I/2) = (-1/2 : ℂ) := by rw [← mul_div_assoc, I_mul_I]
  have h₂ : I * (-I/2) = (1/2 : ℂ) := by rw [← mul_div_assoc, mul_neg, I_mul_I]; ring
  rw [translatedNativeSourceTest_paperFT, translatedNativeSourceTest_paperFT, h₁, h₂,
    (nativeSourceLaplace_elementary_cancellation d).1,
    (nativeSourceLaplace_elementary_cancellation d).2]
  simp

theorem translatedNativeSourceTest_negative_log_zero (d : ℕ) {t : ℝ}
    (ht : UniversalSinc.fixedScale < t) (n : ℕ) :
    translatedNativeSourceTest d t (-Real.log n) = 0 := by
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    by_cases hn : n=0
    · simp [hn]
    · exact Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn)
  unfold translatedNativeSourceTest
  rw [sourceFamily_supported d (t- -Real.log n) ?_, Complex.ofReal_zero]
  intro hmem
  linarith [hmem.2]

theorem translatedNativeSourceTest_nonpositive_zero (d : ℕ) {t : ℝ}
    (ht : UniversalSinc.fixedScale < t) {u : ℝ} (hu : u ≤ 0) :
    translatedNativeSourceTest d t u = 0 := by
  unfold translatedNativeSourceTest
  rw [sourceFamily_supported d (t-u) ?_, Complex.ofReal_zero]
  intro hmem
  linarith [hmem.2]

/-- The prime side is the literal physical field, including the square-root weight. -/
theorem translatedNativeSourceTest_prime_side (d : ℕ) {t : ℝ}
    (ht : UniversalSinc.fixedScale < t) :
    (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      (translatedNativeSourceTest d t (Real.log n) +
        translatedNativeSourceTest d t (-Real.log n))) = (primeFieldFamily d t : ℂ) := by
  rw [primeFieldFamily, nativePrimeField, Complex.ofReal_tsum]
  apply tsum_congr
  intro n
  rw [translatedNativeSourceTest_negative_log_zero d ht n, add_zero]
  simp [translatedNativeSourceTest, nativePrimeCoefficient]

/-- Exact source-specialized literal EF, with the elementary cancellation and
both prime-side source shifts discharged.  The archimedean integral still has
to be evaluated as the trivial-zero series; this helper does not rename that
remaining analytic obligation as a completed native explicit-formula root. -/
theorem native_source_literal_ef_archimedean (d : ℕ) {t : ℝ}
    (ht : UniversalSinc.fixedScale < t) :
    (∑' ρ : zetaZeroConfig.carrier, nativeNontrivialZeroTerm d t ρ) =
      -(primeFieldFamily d t : ℂ) + (1 / (2 * Real.pi) : ℂ) *
        ∫ r : ℝ, paperFT (translatedNativeSourceTest d t) r * (EF.gammaBracket r : ℂ) := by
  have h := (WeilEF.EF_lit_zetaZeroConfig (translatedNativeSourceTest d t)
    (translatedNativeSourceTest_contDiff d t) (translatedNativeSourceTest_hasCompactSupport d t)).2
  calc
    _ = ∑' ρ : zetaZeroConfig.carrier,
        (zetaZeroConfig.mult ρ : ℂ) * paperFT (translatedNativeSourceTest d t) (gammaOf ρ) :=
      tsum_congr (nativeNontrivialZeroTerm_eq_translated_test d t)
    _ = EF.literatureRHS (translatedNativeSourceTest d t) := h
    _ = _ := by
      rw [EF.literatureRHS, translatedNativeSourceTest_elementary_cancellation,
        translatedNativeSourceTest_prime_side d ht]
      ring

/-- Evaluate the genuine literature gamma integral on the actual positive translated source.
The parent density/Fubini spine is used without an evenness assumption on that source. -/
theorem native_source_archimedean_density (d : ℕ) {t : ℝ}
    (ht : UniversalSinc.fixedScale < t) :
    dictionaryArchRHS (translatedNativeSourceTest d t) =
      -(∫ x : ℝ in Ioi 0,
        translatedNativeSourceTest d t x * (archDensity x : ℂ)) := by
  let k := translatedNativeSourceTest d t
  have hk : ContDiff ℝ 2 k := translatedNativeSourceTest_contDiff d t
  have hkc : HasCompactSupport k := translatedNativeSourceTest_hasCompactSupport d t
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  have hFk : Integrable (𝓕 k) := EF.integrable_fourier_of_contDiff_two hk hkc
  have hpaper := EF.integrable_paperFT_ofReal hFk
  have hmu : Integrable (fun r : ℝ => paperFT k r * (mu r : ℂ)) :=
    EF.integrable_paperFT_mul_mu hk hkc gammaFacts
  have hconst : Integrable (fun r : ℝ => paperFT k r * (mu 0 : ℂ)) := hpaper.mul_const _
  have hdiff : Integrable (fun r : ℝ => paperFT k r * ((mu r-mu 0 : ℝ) : ℂ)) := by
    apply (hmu.sub hconst).congr
    filter_upwards with r
    change paperFT k r * (mu r : ℂ) - paperFT k r * (mu 0 : ℂ) = _
    push_cast
    ring
  have hprod := integrable_archDensityFubiniIntegrand hFk hdiff
  have hswap : (∫ r : ℝ, ∫ x : ℝ in Ioi 0, archDensityFubiniIntegrand k (r,x)) =
      ∫ x : ℝ in Ioi 0, ∫ r : ℝ, archDensityFubiniIntegrand k (r,x) :=
    integral_integral_swap hprod
  have hkzero : k 0 = 0 := translatedNativeSourceTest_nonpositive_zero d ht le_rfl
  have hpaperzero : (∫ r : ℝ, paperFT k r) = 0 := by
    rw [integral_paperFT_eq_two_pi_mul hk.continuous hki hFk, hkzero, mul_zero]
  have hconstzero : (∫ r : ℝ, paperFT k r * (mu 0 : ℂ)) = 0 := by
    rw [integral_mul_const, hpaperzero, zero_mul]
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hinner (x : ℝ) (hx : 0 < x) :
      (∫ r : ℝ, archDensityFubiniIntegrand k (r,x)) =
        -(Real.pi : ℂ) * (k x * (archDensity x : ℂ)) := by
    have hkneg : k (-x) = 0 := translatedNativeSourceTest_nonpositive_zero d ht (by linarith)
    have hcos₀ : k x = (1 / Real.pi : ℂ) *
        ∫ r : ℝ, paperFT k r * (Real.cos (r*x) : ℂ) := by
      have h := EF.k_add_k_neg hk.continuous hki hFk x
      simpa only [hkneg, add_zero, mul_comm x] using h
    have hcos : (∫ r : ℝ, paperFT k r * (Real.cos (r*x) : ℂ)) = (Real.pi : ℂ)*k x := by
      calc
        _ = ((Real.pi : ℂ)*(1/Real.pi))*
            ∫ r : ℝ, paperFT k r * (Real.cos (r*x) : ℂ) := by simp [hpi]
        _ = (Real.pi : ℂ)*((1/Real.pi)*
            ∫ r : ℝ, paperFT k r * (Real.cos (r*x) : ℂ)) := by ring
        _ = _ := by rw [← hcos₀]
    have hsub : (∫ r : ℝ, paperFT k r * ((1-Real.cos (r*x) : ℝ) : ℂ)) =
        -(Real.pi : ℂ)*k x := by
      calc
        _ = ∫ r : ℝ, paperFT k r - paperFT k r * (Real.cos (r*x) : ℂ) := by
          apply integral_congr_ae
          filter_upwards with r
          push_cast
          ring
        _ = (∫ r : ℝ, paperFT k r) - ∫ r : ℝ, paperFT k r * (Real.cos (r*x) : ℂ) :=
          integral_sub hpaper (EF.integrable_paperFT_mul_cos hFk x)
        _ = _ := by rw [hpaperzero, hcos]; ring
    calc
      _ = (archDensity x : ℂ) *
          ∫ r : ℝ, paperFT k r * ((1-Real.cos (r*x) : ℝ) : ℂ) := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with r
        unfold archDensityFubiniIntegrand
        push_cast
        ring
      _ = _ := by rw [hsub]; ring
  change dictionaryArchRHS k = _
  calc
    _ = ∫ r : ℝ, paperFT k r * (mu r : ℂ) := dictionaryArchRHS_eq_integral_mu k
    _ = ∫ r : ℝ, paperFT k r * ((mu r-mu 0 : ℝ) : ℂ) := by
      have heq : (fun r : ℝ => paperFT k r * (mu r : ℂ)) =
          fun r : ℝ => paperFT k r * ((mu r-mu 0 : ℝ) : ℂ) + paperFT k r * (mu 0 : ℂ) := by
        funext r
        push_cast
        ring
      rw [heq, integral_add hdiff hconst, hconstzero, add_zero]
    _ = (1/Real.pi : ℂ) * ∫ r : ℝ, ∫ x : ℝ in Ioi 0,
        archDensityFubiniIntegrand k (r,x) := by
      simp_rw [paperFT_mul_mu_sub_mu_zero_eq_density_slice]
      rw [integral_const_mul]
    _ = (1/Real.pi : ℂ) * ∫ x : ℝ in Ioi 0, ∫ r : ℝ,
        archDensityFubiniIntegrand k (r,x) := by rw [hswap]
    _ = (1/Real.pi : ℂ) * ∫ x : ℝ in Ioi 0,
        -(Real.pi : ℂ) * (k x * (archDensity x : ℂ)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact hinner x hx
    _ = _ := by
      rw [integral_const_mul]
      field_simp [hpi]
      rfl

def nativeSourceL1Mass (d : ℕ) : ℝ := ∫ u : ℝ, |sourceOrderFamily d u|

/-- The full compact-source exponential budget on the negative real Laplace axis. -/
theorem nativeSourceLaplace_negative_real_bound (d : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    ‖sourceFamilyLaplace d (-(a : ℂ))‖ ≤
      Real.exp (a*UniversalSinc.fixedScale) * nativeSourceL1Mass d := by
  rw [sourceFamilyLaplace_eq_paperFT]
  have hfi : Integrable (fun u : ℝ => (sourceOrderFamily d u : ℂ)) :=
    (sourceFamily_complex_contDiff d).continuous.integrable_of_hasCompactSupport
      (sourceFamily_complex_hasCompactSupport d)
  have hsupp : ∀ u : ℝ, (sourceOrderFamily d u : ℂ) ≠ 0 → |u| ≤ UniversalSinc.fixedScale := by
    intro u hu
    apply abs_le.mpr
    by_contra hmem
    apply hu
    rw [sourceFamily_supported d u hmem, Complex.ofReal_zero]
  have hb := norm_paperFT_le hfi hsupp (I * -(a : ℂ))
  simpa [nativeSourceL1Mass, Complex.mul_im, abs_of_nonneg ha] using hb

/-- Actual negative even zeta zeros, indexed from the first one `-2`. -/
def nativeTrivialZeroDecay (n : ℕ) : ℝ := 2*((n : ℝ)+1)+1/2

theorem nativeTrivialZeroDecay_zeta_zero (n : ℕ) :
    riemannZeta (1/2-(nativeTrivialZeroDecay n : ℂ)) = 0 := by
  have he : (1/2:ℂ)-(nativeTrivialZeroDecay n : ℂ) = -2*((n:ℂ)+1) := by
    unfold nativeTrivialZeroDecay
    push_cast
    ring
  rw [he]
  exact riemannZeta_neg_two_mul_nat_add_one n

def nativeTrivialZeroTerm (d : ℕ) (t : ℝ) (n : ℕ) : ℂ :=
  sourceFamilyLaplace d (-(nativeTrivialZeroDecay n : ℂ)) *
    Complex.exp (-(nativeTrivialZeroDecay n : ℂ)*(t : ℂ))

theorem nativeTrivialZeroTerm_bound (d : ℕ) (t : ℝ) (n : ℕ) :
    ‖nativeTrivialZeroTerm d t n‖ ≤ nativeSourceL1Mass d *
      Real.exp (-nativeTrivialZeroDecay n*(t-UniversalSinc.fixedScale)) := by
  have ha : 0 ≤ nativeTrivialZeroDecay n := by unfold nativeTrivialZeroDecay; positivity
  calc
    ‖nativeTrivialZeroTerm d t n‖ =
        ‖sourceFamilyLaplace d (-(nativeTrivialZeroDecay n : ℂ))‖ *
          Real.exp (-nativeTrivialZeroDecay n*t) := by
      simp [nativeTrivialZeroTerm, Complex.norm_exp, Complex.mul_re]
    _ ≤ (Real.exp (nativeTrivialZeroDecay n*UniversalSinc.fixedScale) * nativeSourceL1Mass d) *
        Real.exp (-nativeTrivialZeroDecay n*t) :=
      mul_le_mul_of_nonneg_right (nativeSourceLaplace_negative_real_bound d _ ha) (Real.exp_nonneg _)
    _ = _ := by
      rw [mul_comm (Real.exp _) (nativeSourceL1Mass d), mul_assoc, ← Real.exp_add]
      congr 2
      ring

/-- Absolute trivial-zero convergence uses the strict physical threshold `t>s0`. -/
theorem nativeTrivialZeroTerm_summable_norm (d : ℕ) {t : ℝ}
    (ht : UniversalSinc.fixedScale < t) : Summable (fun n : ℕ => ‖nativeTrivialZeroTerm d t n‖) := by
  let h : ℝ := t-UniversalSinc.fixedScale
  let q : ℝ := Real.exp (-2*h)
  have hh : 0 < h := by dsimp [h]; linarith
  have hq₀ : 0 ≤ q := Real.exp_nonneg _
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hs := (summable_geometric_of_lt_one hq₀ hq₁).mul_left
    (nativeSourceL1Mass d * Real.exp (-(5/2:ℝ)*h))
  apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) ?_ hs
  intro n
  have he : Real.exp (-nativeTrivialZeroDecay n*h) = Real.exp (-(5/2:ℝ)*h)*q^n := by
    dsimp [q]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    unfold nativeTrivialZeroDecay
    ring
  have hb := nativeTrivialZeroTerm_bound d t n
  change ‖nativeTrivialZeroTerm d t n‖ ≤ nativeSourceL1Mass d * Real.exp (-nativeTrivialZeroDecay n*h) at hb
  rw [he] at hb
  simpa only [mul_assoc] using hb

theorem translatedNativeSourceTest_norm_integral (d : ℕ) (t : ℝ) :
    (∫ x : ℝ, ‖translatedNativeSourceTest d t x‖) = nativeSourceL1Mass d := by
  simpa [translatedNativeSourceTest, nativeSourceL1Mass] using
    integral_sub_left_eq_self (fun u : ℝ => |sourceOrderFamily d u|) volume t

/-- The existing certified gamma density is exactly the full exponential series. -/
theorem native_arch_density_weight_series {x : ℝ} (hx : 0 < x) :
    (∑' m : ℕ, archSeriesWeight m x) = (archDensity x : ℂ) := by
  have hphase : (Real.pi/x)*x = Real.pi := div_mul_cancel₀ _ hx.ne'
  have h := tsum_archPhysicalSeriesTerm_eq_archDensity (Real.pi/x) hx
  have hs : (∑' m : ℕ, (4:ℝ)*Real.exp (-(2*((m:ℝ)+1/4))*x)) = 4*archDensity x := by
    convert h using 1
    · apply tsum_congr
      intro m
      unfold archPhysicalSeriesTerm
      rw [hphase, Real.cos_pi]
      ring
    · rw [hphase, Real.cos_pi]
      ring
  rw [tsum_mul_left] at hs
  have hr : (∑' m : ℕ, Real.exp (-(2*((m:ℝ)+1/4))*x)) = archDensity x := by linarith
  simp only [archSeriesWeight, archExpWeight, archSeriesAbscissa, abs_of_pos hx]
  rw [← Complex.ofReal_tsum, hr]

theorem native_arch_weight_integral (d : ℕ) {t : ℝ}
    (ht : UniversalSinc.fixedScale < t) (m : ℕ) :
    (∫ x : ℝ, translatedNativeSourceTest d t x * archSeriesWeight m x) =
      sourceFamilyLaplace d (-((2*archSeriesAbscissa m : ℝ) : ℂ)) *
        Complex.exp (-((2*archSeriesAbscissa m : ℝ) : ℂ)*(t : ℂ)) := by
  let a : ℝ := 2*archSeriesAbscissa m
  have harg : I*(I*(a : ℂ)) = -(a : ℂ) := by rw [← mul_assoc, I_mul_I]; ring
  calc
    _ = paperFT (translatedNativeSourceTest d t) (I*(a : ℂ)) := by
      unfold paperFT
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 < x
      · have he : (Real.exp (-a*x) : ℂ) = Complex.exp (-(a : ℂ)*(x : ℂ)) := by
          rw [Complex.ofReal_exp]
          congr 1
          push_cast
          ring
        change translatedNativeSourceTest d t x * (Real.exp (-a*|x|) : ℂ) = _
        rw [abs_of_pos hx, he, harg]
      · rw [translatedNativeSourceTest_nonpositive_zero d ht (le_of_not_gt hx)]
        simp
    _ = _ := by
      rw [translatedNativeSourceTest_paperFT, harg]
      change _ = sourceFamilyLaplace d (-(a : ℂ)) * Complex.exp (-(a : ℂ)*(t : ℂ))
      ring

/-- Absolute integral-norm summability is proved before exchanging the gamma weights
with the physical integral.  Compact support stays a positive distance from zero. -/
theorem native_arch_weight_integral_norm_summability (d : ℕ) {t : ℝ}
    (ht : UniversalSinc.fixedScale < t) :
    (∀ m : ℕ, Integrable (fun x : ℝ =>
      translatedNativeSourceTest d t x * archSeriesWeight m x)) ∧
    Summable (fun m : ℕ => ∫ x : ℝ,
      ‖translatedNativeSourceTest d t x * archSeriesWeight m x‖) := by
  let k := translatedNativeSourceTest d t
  let h := t-UniversalSinc.fixedScale
  have hh : 0 < h := by dsimp [h]; linarith
  have hk := translatedNativeSourceTest_contDiff d t
  have hkc := translatedNativeSourceTest_hasCompactSupport d t
  have hki : Integrable k := hk.continuous.integrable_of_hasCompactSupport hkc
  have hterm (m : ℕ) : Integrable (fun x : ℝ => k x * archSeriesWeight m x) := by
    have hw : Continuous (archSeriesWeight m) := by
      unfold archSeriesWeight archExpWeight
      fun_prop
    exact (hk.continuous.mul hw).integrable_of_hasCompactSupport hkc.mul_right
  have hbound (m : ℕ) : (∫ x : ℝ, ‖k x * archSeriesWeight m x‖) ≤
      Real.exp (-(2*archSeriesAbscissa m)*h) * nativeSourceL1Mass d := by
    have ha : 0 < 2*archSeriesAbscissa m := by positivity [archSeriesAbscissa_pos m]
    have hmajor : Integrable (fun x : ℝ => Real.exp (-(2*archSeriesAbscissa m)*h)*‖k x‖) :=
      hki.norm.const_mul _
    calc
      _ ≤ ∫ x : ℝ, Real.exp (-(2*archSeriesAbscissa m)*h)*‖k x‖ := by
        apply integral_mono_ae (hterm m).norm hmajor
        filter_upwards with x
        by_cases hx : k x=0
        · simp [hx]
        · have hmem : t-x ∈ Icc (-UniversalSinc.fixedScale) UniversalSinc.fixedScale := by
            by_contra hmem
            apply hx
            change (sourceOrderFamily d (t-x) : ℂ) = 0
            rw [sourceFamily_supported d (t-x) hmem, Complex.ofReal_zero]
          have hxl : h ≤ x := by dsimp [h]; linarith [hmem.2]
          have hxpos : 0 < x := hh.trans_le hxl
          have he : Real.exp (-(2*archSeriesAbscissa m)*|x|) ≤
              Real.exp (-(2*archSeriesAbscissa m)*h) := by
            rw [abs_of_pos hxpos]
            exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hxl (by linarith))
          simp only [norm_mul, archSeriesWeight, archExpWeight, Complex.norm_real,
            Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          exact (mul_le_mul_of_nonneg_left he (norm_nonneg _)).trans_eq (mul_comm _ _)
      _ = _ := by rw [integral_const_mul, translatedNativeSourceTest_norm_integral]
  let q := Real.exp (-2*h)
  have hq₀ : 0 ≤ q := Real.exp_nonneg _
  have hq₁ : q < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have hs := (summable_geometric_of_lt_one hq₀ hq₁).mul_left
    (Real.exp (-h/2)*nativeSourceL1Mass d)
  refine ⟨hterm, Summable.of_nonneg_of_le (fun m => integral_nonneg (fun _ => norm_nonneg _)) ?_ hs⟩
  intro m
  have he : Real.exp (-(2*archSeriesAbscissa m)*h) = Real.exp (-h/2)*q^m := by
    dsimp [q]
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    unfold archSeriesAbscissa
    ring
  exact (hbound m).trans_eq (by rw [he]; ring)

theorem native_source_arch_density_trivial_series (d : ℕ) {t : ℝ}
    (ht : UniversalSinc.fixedScale < t) :
    (∫ x : ℝ in Ioi 0, translatedNativeSourceTest d t x * (archDensity x : ℂ)) =
      ∑' n : ℕ, nativeTrivialZeroTerm d t n := by
  have hterms := native_arch_weight_integral_norm_summability d ht
  have hsum := hasSum_integral_of_summable_integral_norm hterms.1 hterms.2
  let f : ℕ → ℂ := fun m =>
    sourceFamilyLaplace d (-((2*archSeriesAbscissa m : ℝ) : ℂ)) *
      Complex.exp (-((2*archSeriesAbscissa m : ℝ) : ℂ)*(t : ℂ))
  have hf : Summable f := hsum.summable.congr (native_arch_weight_integral d ht)
  have hzero : f 0 = 0 := by
    have ha : ((2*archSeriesAbscissa 0 : ℝ) : ℂ) = (1/2:ℂ) := by
      norm_num [archSeriesAbscissa]
    have hc : sourceFamilyLaplace d (-(1/2:ℂ)) = 0 := by
      rw [show -(1/2:ℂ) = (-1/2:ℂ) by ring]
      exact (nativeSourceLaplace_elementary_cancellation d).2
    dsimp only [f]
    rw [ha, hc, zero_mul]
  have hsucc (n : ℕ) : f (n+1) = nativeTrivialZeroTerm d t n := by
    have ha : 2*archSeriesAbscissa (n+1) = nativeTrivialZeroDecay n := by
      unfold archSeriesAbscissa nativeTrivialZeroDecay
      push_cast
      ring
    simp only [f, ha, nativeTrivialZeroTerm]
  calc
    _ = ∫ x : ℝ, ∑' m : ℕ,
        translatedNativeSourceTest d t x * archSeriesWeight m x := by
      rw [← integral_indicator measurableSet_Ioi]
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 < x
      · rw [indicator_of_mem (show x ∈ Ioi (0:ℝ) from hx),
          tsum_mul_left, native_arch_density_weight_series hx]
      · rw [indicator_of_notMem (show x ∉ Ioi (0:ℝ) from hx),
          translatedNativeSourceTest_nonpositive_zero d ht (le_of_not_gt hx)]
        simp
    _ = ∑' m : ℕ, ∫ x : ℝ,
        translatedNativeSourceTest d t x * archSeriesWeight m x := hsum.tsum_eq.symm
    _ = ∑' m : ℕ, f m := tsum_congr (native_arch_weight_integral d ht)
    _ = ∑' n : ℕ, nativeTrivialZeroTerm d t n := by
      rw [hf.tsum_eq_zero_add, hzero, zero_add]
      exact tsum_congr hsucc

/-- Actual native source explicit formula, retaining analytic multiplicities,
both imaginary signs, the canceled elementary term, and absolute convergence
of both zero sums.  No explicit-formula identity is a caller premise. -/
theorem native_source_explicit_formula (d : ℕ) {t : ℝ}
    (ht : UniversalSinc.fixedScale < t) :
    (paperFT (translatedNativeSourceTest d t) (I/2) +
      paperFT (translatedNativeSourceTest d t) (-I/2) = 0) ∧
    Summable (fun ρ : zetaZeroConfig.carrier => ‖nativeNontrivialZeroTerm d t ρ‖) ∧
    Summable (fun n : ℕ => ‖nativeTrivialZeroTerm d t n‖) ∧
    (primeFieldFamily d t : ℂ) =
      -(∑' ρ : zetaZeroConfig.carrier, nativeNontrivialZeroTerm d t ρ) -
      (∑' n : ℕ, nativeTrivialZeroTerm d t n) := by
  refine ⟨translatedNativeSourceTest_elementary_cancellation d t,
    nativeNontrivialZeroTerm_summable_norm d t, nativeTrivialZeroTerm_summable_norm d ht, ?_⟩
  have h := native_source_literal_ef_archimedean d ht
  change (∑' ρ : zetaZeroConfig.carrier, nativeNontrivialZeroTerm d t ρ) =
    -(primeFieldFamily d t : ℂ) + dictionaryArchRHS (translatedNativeSourceTest d t) at h
  rw [native_source_archimedean_density d ht, native_source_arch_density_trivial_series d ht] at h
  linear_combination h

end Zeta23.OPICAFollowup
